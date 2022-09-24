program token_with_cast.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    cast r0.owner r0.gates r0.token_amount into r1 as token.record;
    output r1 as token.record;