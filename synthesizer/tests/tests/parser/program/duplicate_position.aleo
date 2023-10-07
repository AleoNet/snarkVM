program duplicate_position.aleo;

function compute:
    async compute into r0;
    output r0 as duplicate_position.aleo/compute.future;

finalize compute:
    position foo;
    position foo;
