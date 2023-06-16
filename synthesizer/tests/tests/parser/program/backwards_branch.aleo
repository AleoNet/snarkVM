program duplicate_position.aleo;

function compute:
    finalize;

finalize compute:
    position foo;
    branch.eq true true to foo;
