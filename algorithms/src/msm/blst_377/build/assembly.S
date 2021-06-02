#if defined(__x86_64) || defined(__x86_64__)
# if defined(__ELF__)
#  include "elf/add_mod_384-x86_64.s"
#  define __add_mod_384     __add_mont_384
#  define __sub_mod_384     __sub_mont_384
// #  if defined(__ADX__) && !defined(__BLST_PORTABLE__)
#   include "elf/mulx_mont_384-x86_64.s"
// #  else
// #   include "elf/mulq_mont_384-x86_64.s"
// #  endif
# endif
#else
# error "unsupported platform"
#endif
