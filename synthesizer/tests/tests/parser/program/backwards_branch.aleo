program backwards_branch.aleo;

function compute:
    finalize;

finalize compute:
    position foo;
    branch.eq true true to foo;
