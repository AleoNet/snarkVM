// Copyright (C) 2019-2021 Aleo Systems Inc.
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
    traits::{AffineCurve, Group},
};
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_utilities::BitIteratorBE;

use cuda_oxide::*;
use std::{any::TypeId, rc::Rc};

pub struct CudaRequest {
    bases: Vec<G1Affine>,
    scalars: Vec<Fr>,
    response: crossbeam_channel::Sender<Result<G1Projective, ErrorCode>>,
}

struct CudaContext<'a, 'b, 'c> {
    handle: &'b Rc<Handle<'a>>,
    stream: &'b mut Stream<'a>,
    num_groups: u32,
    output_buf: DeviceBox<'a>,
    pixel_func: Function<'a, 'c>,
    row_func: Function<'a, 'c>,
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

fn handle_cuda_request(context: &mut CudaContext, request: &CudaRequest) -> Result<G1Projective, ErrorCode> {
    let mapped_bases: Vec<_> = request
        .bases
        .iter()
        .map(|affine| CudaAffine {
            x: affine.x,
            y: affine.y,
        })
        .collect();

    let mut window_lengths = (0..(request.scalars.len() as u32 / WINDOW_SIZE))
        .into_iter()
        .map(|_| WINDOW_SIZE)
        .collect::<Vec<u32>>();
    let overflow_size = request.scalars.len() as u32 - window_lengths.len() as u32 * WINDOW_SIZE;
    if overflow_size > 0 {
        window_lengths.push(overflow_size);
    }

    let window_lengths_buf = DeviceBox::new_ffi(context.handle, &window_lengths[..])?;
    let bases_in_buf = DeviceBox::new_ffi(context.handle, &mapped_bases[..])?;
    let scalars_in_buf = DeviceBox::new_ffi(context.handle, &request.scalars[..])?;
    context.output_buf.memset_d32_stream(0, context.stream)?;

    let buckets = DeviceBox::alloc(
        context.handle,
        context.num_groups as u64 * window_lengths.len() as u64 * 8 * LIMB_COUNT as u64 * 3,
    )?;

    // let start = Instant::now();

    context.stream.launch(
        &context.pixel_func,
        window_lengths.len() as u32,
        context.num_groups,
        0,
        (
            &buckets,
            &bases_in_buf,
            &scalars_in_buf,
            &window_lengths_buf,
            window_lengths.len() as u32,
        ),
    )?;

    context.stream.sync()?;

    // let time = (start.elapsed().as_micros() as f64) / 1000.0;
    // println!("msm-pixel took {} ms", time);

    context.stream.launch(
        &context.row_func,
        1,
        context.num_groups,
        0,
        (&context.output_buf, &buckets, window_lengths.len() as u32),
    )?;

    context.stream.sync()?;

    // let time = (start.elapsed().as_micros() as f64) / 1000.0;
    // println!("msm-row took {} ms", time);

    let mut out = context.output_buf.load()?;

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
    let out = windows[1..]
        .iter()
        .rev()
        .fold(G1Projective::zero(), |mut total, sum_i| {
            total += sum_i;
            for _ in 0..BIT_WIDTH {
                total.double_in_place();
            }
            total
        })
        + lowest;
    Ok(out)
}

fn cuda_thread(input: crossbeam_channel::Receiver<CudaRequest>) {
    let num_groups = (SCALAR_BITS + BIT_WIDTH - 1) / BIT_WIDTH;
    Cuda::init().unwrap();

    let mut devices = Cuda::list_devices().unwrap();
    if devices.is_empty() {
        eprintln!("CUDA enabled but no CUDA devices were found");
        return;
    }
    let device = devices.remove(0);
    let compute_capability = device.compute_capability().unwrap();
    eprintln!(
        "Using '{}' as CUDA device with compute capability {}",
        device.name().unwrap(),
        compute_capability
    );
    let mut ctx = Context::new(&device).unwrap();
    #[cfg(debug_assertions)]
    ctx.set_limit(LimitType::PrintfFifoSize, 1024 * 1024 * 16).unwrap();
    let handle = ctx.enter().unwrap();
    let linker = Linker::new(&handle, compute_capability, LinkerOptions::default())
        .unwrap()
        .add(
            "asm_cuda.release.ptx",
            LinkerInputType::Ptx,
            include_bytes!("./blst_377_cuda/asm_cuda.release.ptx"),
        )
        .unwrap()
        .add(
            "blst_377_ops.release.ptx",
            LinkerInputType::Ptx,
            include_bytes!("./blst_377_cuda/blst_377_ops.release.ptx"),
        )
        .unwrap()
        .add(
            "msm.release.ptx",
            LinkerInputType::Ptx,
            include_bytes!("./blst_377_cuda/msm.release.ptx"),
        )
        .unwrap();
    let module = linker.build_module().unwrap();
    let pixel_func = module.get_function("msm6_pixel").unwrap();
    let row_func = module.get_function("msm6_collapse_rows").unwrap();
    let mut stream = Stream::new(&handle).unwrap();

    let output_buf = DeviceBox::alloc(&handle, LIMB_COUNT as u64 * 8 * num_groups as u64 * 3).unwrap();

    let mut context = CudaContext {
        handle: &handle,
        stream: &mut stream,
        num_groups: num_groups as u32,
        output_buf,
        pixel_func,
        row_func,
    };

    while let Ok(request) = input.recv() {
        let out = handle_cuda_request(&mut context, &request);

        request.response.send(out).ok();
    }
}

lazy_static::lazy_static! {
    static ref CUDA_DISPATCH: crossbeam_channel::Sender<CudaRequest> = {
        let (sender, receiver) = crossbeam_channel::bounded(16);
        std::thread::spawn(move || cuda_thread(receiver));
        sender
    };
}

pub(super) fn msm_cuda<G: AffineCurve>(
    mut bases: &[G],
    mut scalars: &[<G::ScalarField as PrimeField>::BigInteger],
) -> Result<G::Projective, ErrorCode> {
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
        .map_err(|_| ErrorCode::NoDevice)?;
    match receiver.recv() {
        Ok(x) => unsafe { std::mem::transmute_copy(&x) },
        Err(_) => Err(ErrorCode::NoDevice),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::{bls12_377::Fq, ProjectiveCurve};
    use snarkvm_fields::{Field, One, PrimeField};
    use snarkvm_utilities::{FromBytes, UniformRand};

    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[repr(C)]
    struct ProjectiveAffine {
        projective: G1Projective,
        affine: CudaAffine,
    }

    fn run_roundtrip<T, Y: Clone>(name: &str, inputs: &[Vec<T>]) -> Vec<Y> {
        Cuda::init().unwrap();
        let device = Cuda::list_devices().unwrap().remove(0);
        let mut ctx = Context::new(&device).unwrap();
        ctx.set_limit(LimitType::PrintfFifoSize, 1024 * 1024 * 16).unwrap();
        let handle = ctx.enter().unwrap();
        let linker = Linker::new(&handle, device.compute_capability().unwrap(), LinkerOptions::default())
            .unwrap()
            .add(
                "asm_cuda.debug.ptx",
                LinkerInputType::Ptx,
                include_bytes!("./blst_377_cuda/asm_cuda.debug.ptx"),
            )
            .unwrap()
            .add(
                "blst_377_ops.debug.ptx",
                LinkerInputType::Ptx,
                include_bytes!("./blst_377_cuda/blst_377_ops.debug.ptx"),
            )
            .unwrap()
            .add(
                "msm.debug.ptx",
                LinkerInputType::Ptx,
                include_bytes!("./blst_377_cuda/msm.debug.ptx"),
            )
            .unwrap()
            .add(
                "tests.debug.ptx",
                LinkerInputType::Ptx,
                include_bytes!("./blst_377_cuda/tests.debug.ptx"),
            )
            .unwrap();
        let module = linker.build_module().unwrap();
        let func = module.get_function(name).unwrap();
        let mut stream = Stream::new(&handle).unwrap();

        let out_size = std::mem::size_of::<Y>();
        let mut out = vec![];

        let first_len = inputs.first().unwrap().len();
        assert!(inputs.iter().all(|x| x.len() == first_len));

        for input in inputs {
            let output_buf = DeviceBox::alloc(&handle, out_size as u64).unwrap();
            output_buf.memset_d32(0).unwrap();

            let input_buf = DeviceBox::new_ffi(&handle, &input[..]).unwrap();

            stream.launch(&func, 1, 1, 0, (&output_buf, &input_buf)).unwrap();

            stream.sync().unwrap();

            let output = output_buf.load().unwrap();
            let output = unsafe { (output.as_ptr() as *const Y).as_ref() }.unwrap();
            out.push(output.clone());
        }

        out
    }

    fn make_tests(count: usize, cardinality: usize) -> Vec<Vec<Fq>> {
        let mut rng = XorShiftRng::seed_from_u64(234832847u64);
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
        let mut rng = XorShiftRng::seed_from_u64(234832847u64);
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
        let mut rng = XorShiftRng::seed_from_u64(23483281023u64);
        let mut inputs = vec![];
        for _ in 0..count {
            let mut out = vec![];
            for _ in 0..cardinality {
                let point = G1Projective::rand(&mut rng).into_affine();
                out.push(CudaAffine { x: point.x, y: point.y });
            }
            inputs.push(out);
        }
        inputs
    }

    #[test]
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
    fn test_cuda_projective_add() {
        let inputs = make_projective_tests(1000, 2);

        let output = run_roundtrip("add_projective_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0] + input[1];

            assert_eq!(&rust_out, output);
        }
    }

    #[test]
    fn test_cuda_projective_double() {
        let inputs = make_projective_tests(1000, 1);

        let output = run_roundtrip("double_projective_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let rust_out = input[0].double();

            assert_eq!(&rust_out, output);
        }
    }

    #[test]
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
    fn test_cuda_affine_add() {
        let inputs = make_affine_tests(1000, 2);

        let output: Vec<G1Projective> = run_roundtrip("add_affine_test", &inputs[..]);

        for (input, output) in inputs.iter().zip(output.iter()) {
            let a = G1Affine::new(input[0].x, input[0].y, false);
            let b = G1Affine::new(input[1].x, input[1].y, false);
            let rust_out: G1Projective = a.into_projective() + b.into_projective();
            assert_eq!(&rust_out, output);
        }
    }

    #[test]
    fn test_cuda_projective_affine_add() {
        let affine_inputs = make_affine_tests(1000, 1);
        let projective_inputs = make_projective_tests(1000, 1);

        let inputs = projective_inputs
            .into_iter()
            .zip(affine_inputs.into_iter())
            .map(|(mut projective, mut affine)| {
                vec![ProjectiveAffine {
                    projective: projective.remove(0),
                    affine: affine.remove(0),
                }]
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
    fn test_cuda_affine_add_infinity() {
        let infinite = G1Affine::new(Fq::zero(), Fq::one(), true);
        let cuda_infinite = CudaAffine {
            x: Fq::zero(),
            y: Fq::one(),
        };

        let inputs = vec![vec![cuda_infinite.clone(), cuda_infinite.clone()]];
        let output: Vec<G1Projective> = run_roundtrip("add_affine_test", &inputs[..]);

        let rust_out: G1Projective = infinite.into_projective() + &infinite.into_projective();
        assert_eq!(rust_out, output[0]);
    }

    #[test]
    fn test_cuda_projective_affine_add_infinity() {
        let mut projective = G1Projective::zero();

        let cuda_infinite = CudaAffine {
            x: Fq::zero(),
            y: Fq::one(),
        };

        let inputs = vec![vec![ProjectiveAffine {
            projective: projective.clone(),
            affine: cuda_infinite,
        }]];

        let output: Vec<G1Projective> = run_roundtrip("add_projective_affine_test", &inputs[..]);

        projective.add_assign_mixed(&G1Affine::new(Fq::zero(), Fq::one(), true));
        assert_eq!(projective, output[0]);
    }
}
