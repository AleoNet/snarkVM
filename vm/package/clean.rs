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

use super::*;

impl<N: Network> Package<N> {
    /// Removes the build directory for the package.
    pub fn clean(directory: &Path) -> Result<()> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: {}", directory.display());
        // Ensure the manifest file exists.
        ensure!(
            Manifest::<N>::exists_at(directory),
            "Missing '{}' at '{}'",
            Manifest::<N>::file_name(),
            directory.display()
        );
        // Ensure the main program file exists.
        ensure!(
            AleoFile::<N>::main_exists_at(directory),
            "Missing '{}' at '{}'",
            AleoFile::<N>::main_file_name(),
            directory.display()
        );

        // Prepare the build directory.
        let build_directory = directory.join("build");
        // Remove the build directory if it exists.
        if build_directory.exists() {
            std::fs::remove_dir_all(&build_directory)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type CurrentNetwork = snarkvm_console::network::Testnet3;
    type CurrentAleo = snarkvm_circuit::network::AleoV0;

    #[test]
    fn test_clean() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_package();

        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());
        // Clean the package.
        Package::<CurrentNetwork>::clean(&directory).unwrap();
        // Ensure the build directory still does *not* exist.
        assert!(!package.build_directory().exists());

        // Build the package.
        package.build::<CurrentAleo>(None).unwrap();

        // Ensure the build directory exists.
        assert!(package.build_directory().exists());
        // Clean the package.
        Package::<CurrentNetwork>::clean(&directory).unwrap();
        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn test_clean_with_import() {
        // Samples a new package at a temporary directory.
        let (directory, package) = crate::package::test_helpers::sample_package_with_import();

        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());
        // Clean the package.
        Package::<CurrentNetwork>::clean(&directory).unwrap();
        // Ensure the build directory still does *not* exist.
        assert!(!package.build_directory().exists());

        // Build the package.
        package.build::<CurrentAleo>(None).unwrap();

        // Ensure the build directory exists.
        assert!(package.build_directory().exists());
        // Clean the package.
        Package::<CurrentNetwork>::clean(&directory).unwrap();
        // Ensure the build directory does *not* exist.
        assert!(!package.build_directory().exists());

        // Proactively remove the temporary directory (to conserve space).
        std::fs::remove_dir_all(directory).unwrap();
    }
}
