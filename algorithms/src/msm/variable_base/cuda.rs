// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use snarkvm_curves::{
    bls12_377::{Fq, Fr, G1Affine, G1Projective},
    traits::{AffineCurve, ProjectiveCurve},
};
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_utilities::BitIteratorBE;

use rust_gpu_tools::{cuda, program_closures, Device, GPUError, Program};

use std::{any::TypeId, path::Path, process::Command};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub struct CudaRequest {
    bases: Vec<G1Affine>,
    scalars: Vec<Fr>,
    response: crossbeam_channel::Sender<Result<G1Projective, GPUError>>,
}

struct CudaContext {
    num_groups: u32,
    pixel_func_name: String,
    row_func_name: String,
    program: Program,
}

const SCALAR_BITS: usize = 253;
const BIT_WIDTH: usize = 1;
const LIMB_COUNT: usize = 6;
const WINDOW_SIZE: u32 = 128; // must match in cuda source

#[derive(Clone, Debug)]
#[allow(dead_code)]
#[repr(C)]
struct CudaAffine {
    x: Fq,
    y: Fq,
}

/// Generates the cuda msm binary.
fn generate_cuda_binary<P: AsRef<Path>>(file_path: P, debug: bool) -> Result<(), GPUError> {
    // Find the latest compute code values.
    let nvcc_help = Command::new("nvcc").arg("-h").output()?.stdout;
    let nvcc_output =
        std::str::from_utf8(&nvcc_help).map_err(|_| GPUError::Generic("Missing nvcc command".to_string()))?;

    // Generate the parent directory.
    let mut resource_path = aleo_std::aleo_dir();
    resource_path.push("resources/cuda/");
    std::fs::create_dir_all(resource_path)?;

    // TODO (raychu86): Fix this approach to generating files. Should just read all files in the `blst_377_cuda` directory.
    // Store the `.cu` and `.h` files temporarily for fatbin generation
    let mut asm_cuda_path = aleo_std::aleo_dir();
    let mut asm_cuda_h_path = aleo_std::aleo_dir();
    asm_cuda_path.push("resources/cuda/asm_cuda.cu");
    asm_cuda_h_path.push("resources/cuda/asm_cuda.h");

    let mut blst_377_ops_path = aleo_std::aleo_dir();
    let mut blst_377_ops_h_path = aleo_std::aleo_dir();
    blst_377_ops_path.push("resources/cuda/blst_377_ops.cu");
    blst_377_ops_h_path.push("resources/cuda/blst_377_ops.h");

    let mut msm_path = aleo_std::aleo_dir();
    msm_path.push("resources/cuda/msm.cu");

    let mut types_path = aleo_std::aleo_dir();
    types_path.push("resources/cuda/types.h");

    let mut tests_path = aleo_std::aleo_dir();
    tests_path.push("resources/cuda/tests.cu");

    // Write all the files to the relative path.
    {
        let asm_cuda = include_bytes!("./blst_377_cuda/asm_cuda.cu");
        let asm_cuda_h = include_bytes!("./blst_377_cuda/asm_cuda.h");
        std::fs::write(&asm_cuda_path, asm_cuda)?;
        std::fs::write(&asm_cuda_h_path, asm_cuda_h)?;

        let blst_377_ops = include_bytes!("./blst_377_cuda/blst_377_ops.cu");
        let blst_377_ops_h = include_bytes!("./blst_377_cuda/blst_377_ops.h");
        std::fs::write(&blst_377_ops_path, blst_377_ops)?;
        std::fs::write(&blst_377_ops_h_path, blst_377_ops_h)?;

        let msm = include_bytes!("./blst_377_cuda/msm.cu");
        std::fs::write(&msm_path, msm)?;

        let types = include_bytes!("./blst_377_cuda/types.h");
        std::fs::write(&types_path, types)?;
    }

    // Generate the cuda fatbin.
    let mut command = Command::new("nvcc");
    command.arg(asm_cuda_path.as_os_str()).arg(blst_377_ops_path.as_os_str()).arg(msm_path.as_os_str());

    // Add the debug feature for tests.
    if debug {
        let tests = include_bytes!("./blst_377_cuda/tests.cu");
        std::fs::write(&tests_path, tests)?;

        command.arg(tests_path.as_os_str()).arg("--device-debug");
    }

    // Add supported gencodes
    command
        .arg("--generate-code=arch=compute_60,code=sm_60")
        .arg("--generate-code=arch=compute_70,code=sm_70")
        .arg("--generate-code=arch=compute_75,code=sm_75");

    if nvcc_output.contains("compute_80") {
        command.arg("--generate-code=arch=compute_80,code=sm_80");
    }

    if nvcc_output.contains("compute_86") {
        command.arg("--generate-code=arch=compute_86,code=sm_86");
    }

    command.arg("-fatbin").arg("-dlink").arg("-o").arg(file_path.as_ref().as_os_str());

    eprintln!("\nRunning command: {:?}", command);

    let status = command.status()?;

    // Delete all the temporary .cu and .h files.
    {
        let _ = std::fs::remove_file(asm_cuda_path);
        let _ = std::fs::remove_file(asm_cuda_h_path);
        let _ = std::fs::remove_file(blst_377_ops_path);
        let _ = std::fs::remove_file(blst_377_ops_h_path);
        let _ = std::fs::remove_file(msm_path);
        let _ = std::fs::remove_file(types_path);
        let _ = std::fs::remove_file(tests_path);
    }

    // Execute the command.
    if !status.success() {
        return Err(GPUError::KernelNotFound("Could not generate a new msm kernel".to_string()));
    }

    Ok(())
}

/// Loads the msm.fatbin into an executable CUDA program.
fn load_cuda_program() -> Result<Program, GPUError> {
    let devices: Vec<_> = Device::all();
    let device = match devices.first() {
        Some(device) => device,
        None => return Err(GPUError::DeviceNotFound),
    };

    // Find the path to the msm fatbin kernel
    let mut file_path = aleo_std::aleo_dir();
    file_path.push("resources/cuda/msm.fatbin");

    // If the file does not exist, regenerate the fatbin.
    if !file_path.exists() {
        generate_cuda_binary(&file_path, false)?;
    }

    let cuda_device = match device.cuda_device() {
        Some(device) => device,
        None => return Err(GPUError::DeviceNotFound),
    };

    eprintln!("\nUsing '{}' as CUDA device with {} bytes of memory", device.name(), device.memory());

    let cuda_kernel = std::fs::read(file_path.clone())?;

    // Load the cuda program from the kernel bytes.
    let cuda_program = match cuda::Program::from_bytes(cuda_device, &cuda_kernel) {
        Ok(program) => program,
        Err(err) => {
            // Delete the failing cuda kernel.
            std::fs::remove_file(file_path)?;
            return Err(err);
        }
    };

    Ok(Program::Cuda(cuda_program))
}

/// Run the CUDA MSM operation for a given request.
fn handle_cuda_request(context: &mut CudaContext, request: &CudaRequest) -> Result<G1Projective, GPUError> {
    let mapped_bases: Vec<_> =
        crate::cfg_iter!(request.bases).map(|affine| CudaAffine { x: affine.x, y: affine.y }).collect();

    let mut window_lengths =
        (0..(request.scalars.len() as u32 / WINDOW_SIZE)).into_iter().map(|_| WINDOW_SIZE).collect::<Vec<u32>>();
    let overflow_size = request.scalars.len() as u32 - window_lengths.len() as u32 * WINDOW_SIZE;
    if overflow_size > 0 {
        window_lengths.push(overflow_size);
    }

    let closures = program_closures!(|program, _arg| -> Result<Vec<u8>, GPUError> {
        let window_lengths_buffer = program.create_buffer_from_slice(&window_lengths)?;
        let base_buffer = program.create_buffer_from_slice(&mapped_bases)?;
        let scalars_buffer = program.create_buffer_from_slice(&request.scalars)?;

        let buckets_buffer = program.create_buffer_from_slice(&vec![
            0u8;
            context.num_groups as usize
                * window_lengths.len() as usize
                * 8
                * LIMB_COUNT as usize
                * 3
        ])?;
        let result_buffer =
            program.create_buffer_from_slice(&vec![0u8; LIMB_COUNT as usize * 8 * context.num_groups as usize * 3])?;

        // // The global work size follows CUDA's definition and is the number of
        // // `LOCAL_WORK_SIZE` sized thread groups.
        // const LOCAL_WORK_SIZE: usize = 256;
        // let global_work_size =
        //     (window_lengths.len() * context.num_groups as usize + LOCAL_WORK_SIZE - 1) / LOCAL_WORK_SIZE;

        let kernel_1 =
            program.create_kernel(&context.pixel_func_name, window_lengths.len(), context.num_groups as usize)?;

        kernel_1
            .arg(&buckets_buffer)
            .arg(&base_buffer)
            .arg(&scalars_buffer)
            .arg(&window_lengths_buffer)
            .arg(&(window_lengths.len() as u32))
            .run()?;

        let kernel_2 = program.create_kernel(&context.row_func_name, 1, context.num_groups as usize)?;

        kernel_2.arg(&result_buffer).arg(&buckets_buffer).arg(&(window_lengths.len() as u32)).run()?;

        let mut results = vec![0u8; LIMB_COUNT as usize * 8 * context.num_groups as usize * 3];
        program.read_into_buffer(&result_buffer, &mut results)?;

        Ok(results)
    });

    let mut out = context.program.run(closures, ())?;

    let base_size = std::mem::size_of::<<<G1Affine as AffineCurve>::BaseField as PrimeField>::BigInteger>();

    let windows = unsafe {
        Vec::from_raw_parts(
            out.as_mut_ptr() as *mut G1Projective,
            out.len() / base_size / 3,
            out.capacity() / base_size / 3,
        )
    };
    std::mem::forget(out);

    let lowest = windows.first().unwrap();

    // We're traversing windows from high to low.
    let final_result = windows[1..].iter().rev().fold(G1Projective::zero(), |mut total, sum_i| {
        total += sum_i;
        for _ in 0..BIT_WIDTH {
            total.double_in_place();
        }
        total
    }) + lowest;
    Ok(final_result)
}

/// Initialize the cuda request handler.
fn initialize_cuda_request_handler(input: crossbeam_channel::Receiver<CudaRequest>) {
    match load_cuda_program() {
        Ok(program) => {
            let num_groups = (SCALAR_BITS + BIT_WIDTH - 1) / BIT_WIDTH;

            let mut context = CudaContext {
                num_groups: num_groups as u32,
                pixel_func_name: "msm6_pixel".to_string(),
                row_func_name: "msm6_collapse_rows".to_string(),
                program,
            };

            // Handle each cuda request received from the channel.
            while let Ok(request) = input.recv() {
                let out = handle_cuda_request(&mut context, &request);

                request.response.send(out).ok();
            }
        }
        Err(err) => {
            eprintln!("Error loading cuda program: {:?}", err);
            // If the cuda program fails to load, notify the cuda request dispatcher.
            while let Ok(request) = input.recv() {
                request.response.send(Err(GPUError::DeviceNotFound)).ok();
            }
        }
    }
}

lazy_static::lazy_static! {
    static ref CUDA_DISPATCH: crossbeam_channel::Sender<CudaRequest> = {
        let (sender, receiver) = crossbeam_channel::bounded(4096);
        std::thread::spawn(move || initialize_cuda_request_handler(receiver));
        sender
    };
}

#[allow(clippy::transmute_undefined_repr)]
pub(super) fn msm_cuda<G: AffineCurve>(
    mut bases: &[G],
    mut scalars: &[<G::ScalarField as PrimeField>::BigInteger],
) -> Result<G::Projective, GPUError> {
    if TypeId::of::<G>() != TypeId::of::<G1Affine>() {
        unimplemented!("trying to use cuda for unsupported curve");
    }

    match bases.len() < scalars.len() {
        true => scalars = &scalars[..bases.len()],
        false => bases = &bases[..scalars.len()],
    }

    if scalars.len() < 4 {
        let mut acc = G::Projective::zero();

        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            acc += &base.mul_bits(BitIteratorBE::new(*scalar))
        }
        return Ok(acc);
    }

    let (sender, receiver) = crossbeam_channel::bounded(1);
    CUDA_DISPATCH
        .send(CudaRequest {
            bases: unsafe { std::mem::transmute(bases.to_vec()) },
            scalars: unsafe { std::mem::transmute(scalars.to_vec()) },
            response: sender,
        })
        .map_err(|_| GPUError::DeviceNotFound)?;
    match receiver.recv() {
        Ok(x) => unsafe { std::mem::transmute_copy(&x) },
        Err(_) => Err(GPUError::DeviceNotFound),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::{bls12_377::Fq, ProjectiveCurve};
    use snarkvm_fields::{Field, One, PrimeField};
    use snarkvm_utilities::rand::{test_rng, Uniform};

    use serial_test::serial;

    #[repr(C)]
    struct ProjectiveAffine {
        projective: G1Projective,
        affine: CudaAffine,
    }

    fn run_roundtrip<T, Y: Clone>(name: &str, inputs: &[Vec<T>]) -> Vec<Y> {
        let out_size = std::mem::size_of::<Y>();

        let closures = program_closures!(|program, _arg| -> Result<Vec<Y>, GPUError> {
            let mut out = vec![];

            let first_len = inputs.first().unwrap().len();
            assert!(inputs.iter().all(|x| x.len() == first_len));

            for input in inputs {
                let output_buf = program.create_buffer_from_slice(&vec![0u8; out_size]).unwrap();

                let input_buf = program.create_buffer_from_slice(input).unwrap();

                let kernel = program.create_kernel(name, 1, 1).unwrap();
                kernel.arg(&output_buf).arg(&input_buf).run().unwrap();

                let mut output = vec![0u8; out_size];

                program.read_into_buffer(&output_buf, &mut output).unwrap();

                let output_value = unsafe { (output.as_ptr() as *const Y).as_ref() }.unwrap();

                out.push(output_value.clone());
            }

            Ok(out)
        });

        // Find the path to the msm test fatbin kernel
        let mut file_path = aleo_std::aleo_dir();
        file_path.push("resources/cuda/msm_test.fatbin");

        // If the file does not exist, regenerate the fatbin.
        if !file_path.exists() {
            generate_cuda_binary(&file_path, true).unwrap();
        }

        let cuda_kernel = std::fs::read(file_path.clone()).unwrap();
        let cuda_device = Device::all().first().unwrap().cuda_device().unwrap();

        let cuda_program = match cuda::Program::from_bytes(cuda_device, &cuda_kernel) {
            Ok(program) => program,
            Err(_err) => {
                // Delete the failing cuda kernel.
                std::fs::remove_file(file_path).unwrap();
                panic!("Failed to load cuda program");
            }
        };

        let program = Program::Cuda(cuda_program);

        program.run(closures, ()).unwrap()
    }

    fn make_tests(count: usize, cardinality: usize) -> Vec<Vec<Fq>> {
        let mut rng = test_rng();
        let mut inputs = vec![];
        for _ in 0..count {
            let mut out = vec![];
            for _ in 0..cardinality {
                out.push(Fq::rand(&mut rng));
            }
            inputs.push(out);
        }
        inputs
    }

    fn make_projective_tests(count: usize, cardinality: usize) -> Vec<Vec<G1Projective>> {
        let mut rng = test_rng();
        let mut inputs = vec![];
        for _ in 0..count {
            let mut out = vec![];
            for _ in 0..cardinality {
                out.push(G1Projective::rand(&mut rng));
            }
            inputs.push(out);
        }
        inputs
    }

    fn make_affine_tests(count: usize, cardinality: usize) -> Vec<Vec<CudaAffine>> {
        let mut rng = test_rng();
        let mut inputs = vec![];
        for _ in 0..count {
            let mut out = vec![];
            for _ in 0..cardinality {
                let point = G1Projective::rand(&mut rng).to_affine();
                out.push(CudaAffine { x: point.x, y: point.y });
            }
            inputs.push(out);
        }
        inputs
    }

    #[test]
    #[serial]
    fn test_cuda_mul() {
        let inputs = make_tests(1000, 2);

        let output: Vec<Fq> = run_roundtrip("mul_test", &inputs[..]);
        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0] * input[1];
            let output = output.to_repr_unchecked();
            let rust_out = rust_out.to_repr_unchecked();

            if rust_out != output {
                eprintln!("test failed: {:?} != {:?}", rust_out.as_ref(), output.as_ref());
                eprintln!(
                    "inputs {:?}, {:?}",
                    input[0].to_repr_unchecked().as_ref(),
                    input[1].to_repr_unchecked().as_ref()
                );
                assert_eq!(rust_out.as_ref(), output.as_ref());
            }
        }
    }

    #[test]
    #[serial]
    fn test_cuda_square() {
        let inputs = make_tests(1000, 1);

        let output: Vec<Fq> = run_roundtrip("sqr_test", &inputs[..]);
        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0].square();
            let output = output.to_repr_unchecked();
            let rust_out = rust_out.to_repr_unchecked();

            if rust_out != output {
                eprintln!("test failed: {:?} != {:?}", rust_out.as_ref(), output.as_ref());
                eprintln!("inputs {:?}", input[0].to_repr_unchecked().as_ref());
                assert_eq!(rust_out.as_ref(), output.as_ref());
            }
        }
    }

    #[test]
    #[serial]
    fn test_cuda_add() {
        let inputs = make_tests(1000, 2);

        let output: Vec<Fq> = run_roundtrip("add_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0] + input[1];
            let output = output.to_repr_unchecked();
            let rust_out = rust_out.to_repr_unchecked();

            if rust_out != output {
                eprintln!("test failed: {:?} != {:?}", rust_out.as_ref(), output.as_ref());
                eprintln!(
                    "inputs {:?}, {:?}",
                    input[0].to_repr_unchecked().as_ref(),
                    input[1].to_repr_unchecked().as_ref()
                );
                assert_eq!(rust_out.as_ref(), output.as_ref());
            }
        }
    }

    #[test]
    #[serial]
    fn test_cuda_projective_add() {
        let inputs = make_projective_tests(1000, 2);

        let output: Vec<G1Projective> = run_roundtrip("add_projective_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0] + input[1];

            assert_eq!(&rust_out, output);
        }
    }

    #[test]
    #[serial]
    fn test_cuda_projective_double() {
        let inputs = make_projective_tests(1000, 1);

        let output: Vec<G1Projective> = run_roundtrip("double_projective_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0].double();

            assert_eq!(&rust_out, output);
        }
    }

    #[test]
    #[serial]
    fn test_cuda_affine_round_trip() {
        let inputs = make_affine_tests(1000, 1);

        let output: Vec<CudaAffine> = run_roundtrip("affine_round_trip_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let a = G1Affine::new(input[0].x, input[0].y, false);
            let out = G1Affine::new(output.x, output.y, false);
            assert_eq!(a, out);
        }
    }

    #[test]
    #[serial]
    fn test_cuda_affine_add() {
        let inputs = make_affine_tests(1000, 2);

        let output: Vec<G1Projective> = run_roundtrip("add_affine_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let a = G1Affine::new(input[0].x, input[0].y, false);
            let b = G1Affine::new(input[1].x, input[1].y, false);
            let rust_out: G1Projective = a.to_projective() + b.to_projective();
            assert_eq!(&rust_out, output);
        }
    }

    #[test]
    #[serial]
    fn test_cuda_projective_affine_add() {
        let affine_inputs = make_affine_tests(1000, 1);
        let projective_inputs = make_projective_tests(1000, 1);

        let inputs = projective_inputs
            .into_iter()
            .zip(affine_inputs.into_iter())
            .map(|(mut projective, mut affine)| {
                vec![ProjectiveAffine { projective: projective.remove(0), affine: affine.remove(0) }]
            })
            .collect::<Vec<_>>();

        let output: Vec<G1Projective> = run_roundtrip("add_projective_affine_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let b = G1Affine::new(input[0].affine.x, input[0].affine.y, false);
            let mut rust_out = input[0].projective;
            rust_out.add_assign_mixed(&b);
            assert_eq!(&rust_out, output);
        }
    }

    #[test]
    #[serial]
    fn test_cuda_sub() {
        let inputs = make_tests(1000, 2);

        let output: Vec<Fq> = run_roundtrip("sub_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0] - input[1];
            let output = output.to_repr_unchecked();
            let rust_out = rust_out.to_repr_unchecked();
            if rust_out != output {
                eprintln!("test failed: {:?} != {:?}", rust_out.as_ref(), output.as_ref());
                eprintln!(
                    "inputs {:?}, {:?}",
                    input[0].to_repr_unchecked().as_ref(),
                    input[1].to_repr_unchecked().as_ref()
                );
                assert_eq!(rust_out.as_ref(), output.as_ref());
            }
        }
    }

    #[test]
    #[serial]
    fn test_cuda_affine_add_infinity() {
        let infinite = G1Affine::new(Fq::zero(), Fq::one(), true);
        let cuda_infinite = CudaAffine { x: Fq::zero(), y: Fq::one() };

        let inputs = vec![vec![cuda_infinite.clone(), cuda_infinite]];
        let output: Vec<G1Projective> = run_roundtrip("add_affine_test", &inputs[..]);

        let rust_out: G1Projective = infinite.to_projective() + infinite.to_projective();
        assert_eq!(rust_out, output[0]);
    }

    #[test]
    #[serial]
    fn test_cuda_projective_affine_add_infinity() {
        let mut projective = G1Projective::zero();

        let cuda_infinite = CudaAffine { x: Fq::zero(), y: Fq::one() };

        let inputs = vec![vec![ProjectiveAffine { projective, affine: cuda_infinite }]];

        let output: Vec<G1Projective> = run_roundtrip("add_projective_affine_test", &inputs[..]);

        projective.add_assign_mixed(&G1Affine::new(Fq::zero(), Fq::one(), true));
        assert_eq!(projective, output[0]);
    }
}
