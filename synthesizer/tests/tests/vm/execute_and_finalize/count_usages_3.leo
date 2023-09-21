
program basic_math.aleo {

    mapping add_uses: address => u64;
    mapping sub_uses: address => u64;

    function add_and_count(a: i64, b: i64) -> (i64, Future) {
        let finalize: Future = async |caller: address| {
             let count: u64 = add_uses.get_or_use(caller, 0u64);
             add_uses.set(caller, count + 1u64);
         };
        return (
            (a + b),
            finalize(self.caller)
        );
    }

    function sub_and_count(a: i64, b: i64) -> (i64, Future) {
        return (
            (a - b),
            async |caller: address| {
                let count: u64 = sub_uses.get_or_use(caller, 0u64);
                sub_uses.set(caller, count + 1u64);
            }
        );
    }
}


//////

import basic_math.aleo;

program count_usages.aleo {

    function add_and_subtract(a: i64, b: i64) -> (i64, Future) {
        let (result, add_future): (i64, Future) = basic_math.aleo/add_and_count(a, b);
        let (result_2, sub_future): (i64, Future) = basic_math.aleo/sub_and_count(result, b);
        assert_eq(a, result);
        assert_eq(add_future.caller, sub_future.caller);
        let future: Future = async || {
            await add_future();
            await sub_future();
        };
// TODO: Solve nested futures
//         let future2: Future = async || {
//             await future();
//         };
        return (a, future);
    }
}
