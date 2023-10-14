program backwards_branch.aleo;

function compute:
    async compute into r0;
    output r0 as backwards_branch.aleo/compute.future;

finalize compute:
    position foo;
    branch.eq true true to foo;
