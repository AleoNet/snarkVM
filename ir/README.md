# How to Regenerate IR Tests

1. set the `EMIT_IR` environment variable to 1
2. run the `compiler_tests` function in `leo/compiler/src/tests.rs`. a folder will be generated that contains IR tests for snarkvm
3. replace the current snarkvm IR tests with the ones generated in step 2
