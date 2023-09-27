/*
randomness: 45791624
cases:
  - program: child.aleo
    function: foo
    inputs: []
  - program: parent.aleo
    function: foo
    inputs: []
*/

program child.aleo;

function foo:
    assert.eq self.parent self.caller;
    output self.parent as address.public;
    output self.caller as address.public;

/////////////////////////////////////////////////

import child.aleo;

program parent.aleo;

function foo:
    call child.aleo/foo into r0 r1;
    output r0 as address.public;
    output r1 as address.public;
    output self.parent as address.public;
    output self.caller as address.public;

