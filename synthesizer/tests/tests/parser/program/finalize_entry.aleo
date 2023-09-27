// The 'finalize_entry.aleo' program.
program finalize_entry.aleo;

struct entry:
    count as u8;
    data as u8;

mapping entries:
    key as address.public;
    value as entry.public;

function compute:
    input r0 as u8.public;
    input r1 as u8.public;
    cast r0 r1 into r2 as entry;
    async compute self.caller r2 into r3;
    output r3 as finalize_entry.aleo/compute.future;

finalize compute:
    input r0 as address.public;
    input r1 as entry.public;
    get.or_use entries[r0] r1 into r2;
    add r1.count r2.count into r3;
    add r1.data r2.data into r4;
    cast r3 r4 into r5 as entry;
    set r5 into entries[r0];
    get entries[r0] into r6;
    add r6.count r1.count into r7;
    add r6.data r1.data into r8;
    cast r7 r8 into r9 as entry;
    set r9 into entries[r0];
