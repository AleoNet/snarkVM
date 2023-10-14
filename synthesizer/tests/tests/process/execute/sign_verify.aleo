/*
randomness: 810372
cases:
  - program: sign_verify.aleo
    function: verify
    inputs: [
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      aleo1c5xskmnp5sfq9h2aje6avntnmlkha9xwlefduhwahdxch04w8spshzdxny,
      0field
    ]
  - program: sign_verify.aleo
    function: verify_constant_signature
    inputs: [
      aleo1c5xskmnp5sfq9h2aje6avntnmlkha9xwlefduhwahdxch04w8spshzdxny,
      0field
    ]
  - program: sign_verify.aleo
    function: verify
    inputs: [
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      aleo1c5xskmnp5sfq9h2aje6avntnmlkha9xwlefduhwahdxch04w8spshzdxny,
      1field
    ]
  - program: sign_verify.aleo
    function: verify
    inputs: [
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      aleo1c3a0lw4ng87nn7h0srpcu4gxs8k3fhw3kn32wu5z9amkn25llvrse4y6yn,
      0field
    ]
  - program: sign_verify.aleo
    function: literal_ops_on_signatures
    inputs: [
      false,
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      sign1jwctd5pcnqwl5e0srptwu726yahjg83nsncyjz0w34nzgtaqxqpuy2wja6c5u0t69f4v64nx6l84f9zd6yu5thxvtqvwvknd8p0uqqgxxmnhttyyys9n466enf9e9jpy8nccuqeqsj7xvjzjyeafkmaaplqg5y7n3cwnxmm0zk9a59hkcgghgr0zkjjq85jr5d4dpmermxc3z9kqr43
    ]
  - program: sign_verify.aleo
    function: literal_ops_on_signatures
    inputs: [
      false,
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd
    ]
  - program: sign_verify.aleo
    function: literal_ops_on_signatures
    inputs: [
      true,
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      sign1jwctd5pcnqwl5e0srptwu726yahjg83nsncyjz0w34nzgtaqxqpuy2wja6c5u0t69f4v64nx6l84f9zd6yu5thxvtqvwvknd8p0uqqgxxmnhttyyys9n466enf9e9jpy8nccuqeqsj7xvjzjyeafkmaaplqg5y7n3cwnxmm0zk9a59hkcgghgr0zkjjq85jr5d4dpmermxc3z9kqr43
    ]
*/

program sign_verify.aleo;

function verify:
    input r0 as signature.private;
    input r1 as address.private;
    input r2 as field.private;
    sign.verify r0 r1 r2 into r3;
    output r3 as boolean.private;

function verify_constant_signature:
    input r0 as address.private;
    input r1 as field.private;
    sign.verify sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd r0 r1 into r2;
    output r2 as boolean.private;

function literal_ops_on_signatures:
    input r0 as boolean.private;
    input r1 as signature.private;
    input r2 as signature.private;
    assert.eq r1 r1;
    assert.eq r2 r2;
    is.eq r1 r2 into r3;
    is.neq r1 r2 into r4;
    ternary r0 r1 r2 into r5;
    output r3 as boolean.private;
    output r4 as boolean.private;
    output r5 as signature.private;



