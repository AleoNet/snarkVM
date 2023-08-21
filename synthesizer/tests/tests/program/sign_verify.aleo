/*
randomness: 810372
cases:
  - function: verify
    inputs: [
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      aleo1c5xskmnp5sfq9h2aje6avntnmlkha9xwlefduhwahdxch04w8spshzdxny,
      0field
    ]
  - function: verify_constant_signature
    inputs: [
      aleo1c5xskmnp5sfq9h2aje6avntnmlkha9xwlefduhwahdxch04w8spshzdxny,
      0field
    ]
  - function: verify
    inputs: [
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      aleo1c5xskmnp5sfq9h2aje6avntnmlkha9xwlefduhwahdxch04w8spshzdxny,
      1field
    ]
  - function: verify
    inputs: [
      sign169ju4e8s66unu25celqycvsv3k9chdyz4n4sy62tx6wxj0u25vqp58hgu9hwyqc63qzxvjwesf2wz0krcvvw9kd9x0rsk4lwqn2acqhp9v0pdkhx6gvkanuuwratqmxa3du7l43c05253hhed9eg6ppzzfnjt06fpzp6msekdjxd36smjltndmxjndvv9x2uecsgngcwsc2qkns4afd,
      aleo1c3a0lw4ng87nn7h0srpcu4gxs8k3fhw3kn32wu5z9amkn25llvrse4y6yn,
      0field
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
