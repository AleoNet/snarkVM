
program basic_math.leo {

    mapping add_uses: address => u64;
    mapping sub_uses: address => u64;

    function add_and_count(a: i64, b: i64) -> i64 {
        return (a + b) then finalize(self.caller);
    }

    finalize add_and_count(caller: address) {
        let count: u64 = add_uses.get_or_use(caller, 0u64);
        add_uses.set(caller, count + 1u64);
    }

    function sub_and_count(a: i64, b: i64) -> i64 {
        return (a - b) then finalize(self.caller);
    }

    finalize sub_and_count(caller: address) {
        let count: u64 = sub_uses.get_or_use(caller, 0u64);
        sub_uses.set(caller, count + 1u64);
    }
}


//////

import basic_math.aleo;

program count_usages.aleo {

    function add_and_subtract(a: i64, b: i64) -> i64 {
        let result: i64 = basic_math.aleo/add_and_count(a, b) then c;
        result = basic_math.aleo/sub_and_count(result, b) then d;
        assert_eq(a, result);
        return then finalize(a);
    }

    finalize add_and_subtract(public i: i64) {
        basic_math.aleo/add_uses.get_or_use(c);
        basic_math.aleo/sub_uses.get_or_use(d);
        assert_eq(c, d)
    }


    function add_and_subtract(a: i64, b: i64) -> i64 {
            let result: i64 = basic_math.aleo/add_and_count(a, b) then c;
            result = basic_math.aleo/sub_and_count(result, b) then d;
            assert_eq(a, result);
            return then finalize(|| {
                basic_math.aleo/add_uses.get_or_use(c);
                basic_math.aleo/sub_uses.get_or_use(d);
                assert_eq(c, d)
            })

    }

//     finalize add_and_subtract() {
//         basic_math.aleo/sub_uses.get_or_use(self.caller, 0u64);
//         assert_eq(, 1u64);
//     }
}


