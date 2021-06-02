
../target/release/build/snarkvm-algorithms-17af85ed5ea73b7f/out/src/msm/blst_377/build/assembly.o:     file format elf64-x86-64


Disassembly of section .text:

0000000000000000 <add_mod_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	55                   	push   rbp
   5:	53                   	push   rbx
   6:	41 54                	push   r12
   8:	41 55                	push   r13
   a:	41 56                	push   r14
   c:	41 57                	push   r15
   e:	48 83 ec 08          	sub    rsp,0x8
  12:	e8 29 00 00 00       	call   40 <__add_mod_384>
  17:	4c 8b 7c 24 08       	mov    r15,QWORD PTR [rsp+0x8]
  1c:	4c 8b 74 24 10       	mov    r14,QWORD PTR [rsp+0x10]
  21:	4c 8b 6c 24 18       	mov    r13,QWORD PTR [rsp+0x18]
  26:	4c 8b 64 24 20       	mov    r12,QWORD PTR [rsp+0x20]
  2b:	48 8b 5c 24 28       	mov    rbx,QWORD PTR [rsp+0x28]
  30:	48 8b 6c 24 30       	mov    rbp,QWORD PTR [rsp+0x30]
  35:	48 8d 64 24 38       	lea    rsp,[rsp+0x38]
  3a:	f3 c3                	repz ret 
  3c:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

0000000000000040 <__add_mod_384>:
  40:	f3 0f 1e fa          	endbr64 
  44:	4c 8b 06             	mov    r8,QWORD PTR [rsi]
  47:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
  4b:	4c 8b 56 10          	mov    r10,QWORD PTR [rsi+0x10]
  4f:	4c 8b 5e 18          	mov    r11,QWORD PTR [rsi+0x18]
  53:	4c 8b 66 20          	mov    r12,QWORD PTR [rsi+0x20]
  57:	4c 8b 6e 28          	mov    r13,QWORD PTR [rsi+0x28]

000000000000005b <__add_mod_384_a_is_loaded>:
  5b:	4c 03 02             	add    r8,QWORD PTR [rdx]
  5e:	4c 13 4a 08          	adc    r9,QWORD PTR [rdx+0x8]
  62:	4c 13 52 10          	adc    r10,QWORD PTR [rdx+0x10]
  66:	4d 89 c6             	mov    r14,r8
  69:	4c 13 5a 18          	adc    r11,QWORD PTR [rdx+0x18]
  6d:	4d 89 cf             	mov    r15,r9
  70:	4c 13 62 20          	adc    r12,QWORD PTR [rdx+0x20]
  74:	4c 89 d0             	mov    rax,r10
  77:	4c 13 6a 28          	adc    r13,QWORD PTR [rdx+0x28]
  7b:	4c 89 db             	mov    rbx,r11
  7e:	48 19 d2             	sbb    rdx,rdx
  81:	4c 2b 01             	sub    r8,QWORD PTR [rcx]
  84:	4c 1b 49 08          	sbb    r9,QWORD PTR [rcx+0x8]
  88:	4c 89 e5             	mov    rbp,r12
  8b:	4c 1b 51 10          	sbb    r10,QWORD PTR [rcx+0x10]
  8f:	4c 1b 59 18          	sbb    r11,QWORD PTR [rcx+0x18]
  93:	4c 1b 61 20          	sbb    r12,QWORD PTR [rcx+0x20]
  97:	4c 89 ee             	mov    rsi,r13
  9a:	4c 1b 69 28          	sbb    r13,QWORD PTR [rcx+0x28]
  9e:	48 83 da 00          	sbb    rdx,0x0
  a2:	4d 0f 42 c6          	cmovb  r8,r14
  a6:	4d 0f 42 cf          	cmovb  r9,r15
  aa:	4c 0f 42 d0          	cmovb  r10,rax
  ae:	4c 89 07             	mov    QWORD PTR [rdi],r8
  b1:	4c 0f 42 db          	cmovb  r11,rbx
  b5:	4c 89 4f 08          	mov    QWORD PTR [rdi+0x8],r9
  b9:	4c 0f 42 e5          	cmovb  r12,rbp
  bd:	4c 89 57 10          	mov    QWORD PTR [rdi+0x10],r10
  c1:	4c 0f 42 ee          	cmovb  r13,rsi
  c5:	4c 89 5f 18          	mov    QWORD PTR [rdi+0x18],r11
  c9:	4c 89 67 20          	mov    QWORD PTR [rdi+0x20],r12
  cd:	4c 89 6f 28          	mov    QWORD PTR [rdi+0x28],r13
  d1:	f3 c3                	repz ret 
  d3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
  de:	66 90                	xchg   ax,ax

00000000000000e0 <__lshift_mod_384>:
  e0:	f3 0f 1e fa          	endbr64 
  e4:	4d 01 c0             	add    r8,r8
  e7:	4d 11 c9             	adc    r9,r9
  ea:	4d 11 d2             	adc    r10,r10
  ed:	4d 89 c6             	mov    r14,r8
  f0:	4d 11 db             	adc    r11,r11
  f3:	4d 89 cf             	mov    r15,r9
  f6:	4d 11 e4             	adc    r12,r12
  f9:	4c 89 d0             	mov    rax,r10
  fc:	4d 11 ed             	adc    r13,r13
  ff:	4c 89 db             	mov    rbx,r11
 102:	48 19 d2             	sbb    rdx,rdx
 105:	4c 2b 01             	sub    r8,QWORD PTR [rcx]
 108:	4c 1b 49 08          	sbb    r9,QWORD PTR [rcx+0x8]
 10c:	4c 89 e5             	mov    rbp,r12
 10f:	4c 1b 51 10          	sbb    r10,QWORD PTR [rcx+0x10]
 113:	4c 1b 59 18          	sbb    r11,QWORD PTR [rcx+0x18]
 117:	4c 1b 61 20          	sbb    r12,QWORD PTR [rcx+0x20]
 11b:	4c 89 ee             	mov    rsi,r13
 11e:	4c 1b 69 28          	sbb    r13,QWORD PTR [rcx+0x28]
 122:	48 83 da 00          	sbb    rdx,0x0
 126:	4d 0f 42 c6          	cmovb  r8,r14
 12a:	4d 0f 42 cf          	cmovb  r9,r15
 12e:	4c 0f 42 d0          	cmovb  r10,rax
 132:	4c 0f 42 db          	cmovb  r11,rbx
 136:	4c 0f 42 e5          	cmovb  r12,rbp
 13a:	4c 0f 42 ee          	cmovb  r13,rsi
 13e:	f3 c3                	repz ret 

0000000000000140 <mul_by_3_mod_384>:
 140:	f3 0f 1e fa          	endbr64 
 144:	55                   	push   rbp
 145:	53                   	push   rbx
 146:	41 54                	push   r12
 148:	41 55                	push   r13
 14a:	41 56                	push   r14
 14c:	41 57                	push   r15
 14e:	56                   	push   rsi
 14f:	4c 8b 06             	mov    r8,QWORD PTR [rsi]
 152:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
 156:	4c 8b 56 10          	mov    r10,QWORD PTR [rsi+0x10]
 15a:	4c 8b 5e 18          	mov    r11,QWORD PTR [rsi+0x18]
 15e:	4c 8b 66 20          	mov    r12,QWORD PTR [rsi+0x20]
 162:	4c 8b 6e 28          	mov    r13,QWORD PTR [rsi+0x28]
 166:	48 89 d1             	mov    rcx,rdx
 169:	e8 72 ff ff ff       	call   e0 <__lshift_mod_384>
 16e:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 172:	e8 e4 fe ff ff       	call   5b <__add_mod_384_a_is_loaded>
 177:	4c 8b 7c 24 08       	mov    r15,QWORD PTR [rsp+0x8]
 17c:	4c 8b 74 24 10       	mov    r14,QWORD PTR [rsp+0x10]
 181:	4c 8b 6c 24 18       	mov    r13,QWORD PTR [rsp+0x18]
 186:	4c 8b 64 24 20       	mov    r12,QWORD PTR [rsp+0x20]
 18b:	48 8b 5c 24 28       	mov    rbx,QWORD PTR [rsp+0x28]
 190:	48 8b 6c 24 30       	mov    rbp,QWORD PTR [rsp+0x30]
 195:	48 8d 64 24 38       	lea    rsp,[rsp+0x38]
 19a:	f3 c3                	repz ret 
 19c:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

00000000000001a0 <mul_by_8_mod_384>:
 1a0:	f3 0f 1e fa          	endbr64 
 1a4:	55                   	push   rbp
 1a5:	53                   	push   rbx
 1a6:	41 54                	push   r12
 1a8:	41 55                	push   r13
 1aa:	41 56                	push   r14
 1ac:	41 57                	push   r15
 1ae:	48 83 ec 08          	sub    rsp,0x8
 1b2:	4c 8b 06             	mov    r8,QWORD PTR [rsi]
 1b5:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
 1b9:	4c 8b 56 10          	mov    r10,QWORD PTR [rsi+0x10]
 1bd:	4c 8b 5e 18          	mov    r11,QWORD PTR [rsi+0x18]
 1c1:	4c 8b 66 20          	mov    r12,QWORD PTR [rsi+0x20]
 1c5:	4c 8b 6e 28          	mov    r13,QWORD PTR [rsi+0x28]
 1c9:	48 89 d1             	mov    rcx,rdx
 1cc:	e8 0f ff ff ff       	call   e0 <__lshift_mod_384>
 1d1:	e8 0a ff ff ff       	call   e0 <__lshift_mod_384>
 1d6:	e8 05 ff ff ff       	call   e0 <__lshift_mod_384>
 1db:	4c 89 07             	mov    QWORD PTR [rdi],r8
 1de:	4c 89 4f 08          	mov    QWORD PTR [rdi+0x8],r9
 1e2:	4c 89 57 10          	mov    QWORD PTR [rdi+0x10],r10
 1e6:	4c 89 5f 18          	mov    QWORD PTR [rdi+0x18],r11
 1ea:	4c 89 67 20          	mov    QWORD PTR [rdi+0x20],r12
 1ee:	4c 89 6f 28          	mov    QWORD PTR [rdi+0x28],r13
 1f2:	4c 8b 7c 24 08       	mov    r15,QWORD PTR [rsp+0x8]
 1f7:	4c 8b 74 24 10       	mov    r14,QWORD PTR [rsp+0x10]
 1fc:	4c 8b 6c 24 18       	mov    r13,QWORD PTR [rsp+0x18]
 201:	4c 8b 64 24 20       	mov    r12,QWORD PTR [rsp+0x20]
 206:	48 8b 5c 24 28       	mov    rbx,QWORD PTR [rsp+0x28]
 20b:	48 8b 6c 24 30       	mov    rbp,QWORD PTR [rsp+0x30]
 210:	48 8d 64 24 38       	lea    rsp,[rsp+0x38]
 215:	f3 c3                	repz ret 
 217:	66 0f 1f 84 00 00 00 00 00 	nop    WORD PTR [rax+rax*1+0x0]

0000000000000220 <cneg_mod_384>:
 220:	f3 0f 1e fa          	endbr64 
 224:	55                   	push   rbp
 225:	53                   	push   rbx
 226:	41 54                	push   r12
 228:	41 55                	push   r13
 22a:	41 56                	push   r14
 22c:	41 57                	push   r15
 22e:	52                   	push   rdx
 22f:	48 8b 16             	mov    rdx,QWORD PTR [rsi]
 232:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
 236:	4c 8b 56 10          	mov    r10,QWORD PTR [rsi+0x10]
 23a:	49 89 d0             	mov    r8,rdx
 23d:	4c 8b 5e 18          	mov    r11,QWORD PTR [rsi+0x18]
 241:	4c 09 ca             	or     rdx,r9
 244:	4c 8b 66 20          	mov    r12,QWORD PTR [rsi+0x20]
 248:	4c 09 d2             	or     rdx,r10
 24b:	4c 8b 6e 28          	mov    r13,QWORD PTR [rsi+0x28]
 24f:	4c 09 da             	or     rdx,r11
 252:	48 c7 c6 ff ff ff ff 	mov    rsi,0xffffffffffffffff
 259:	4c 09 e2             	or     rdx,r12
 25c:	4c 09 ea             	or     rdx,r13
 25f:	4c 8b 31             	mov    r14,QWORD PTR [rcx]
 262:	48 0f 45 d6          	cmovne rdx,rsi
 266:	4c 8b 79 08          	mov    r15,QWORD PTR [rcx+0x8]
 26a:	48 8b 41 10          	mov    rax,QWORD PTR [rcx+0x10]
 26e:	49 21 d6             	and    r14,rdx
 271:	48 8b 59 18          	mov    rbx,QWORD PTR [rcx+0x18]
 275:	49 21 d7             	and    r15,rdx
 278:	48 8b 69 20          	mov    rbp,QWORD PTR [rcx+0x20]
 27c:	48 21 d0             	and    rax,rdx
 27f:	48 8b 71 28          	mov    rsi,QWORD PTR [rcx+0x28]
 283:	48 21 d3             	and    rbx,rdx
 286:	48 8b 0c 24          	mov    rcx,QWORD PTR [rsp]
 28a:	48 21 d5             	and    rbp,rdx
 28d:	48 21 d6             	and    rsi,rdx
 290:	4d 29 c6             	sub    r14,r8
 293:	4d 19 cf             	sbb    r15,r9
 296:	4c 19 d0             	sbb    rax,r10
 299:	4c 19 db             	sbb    rbx,r11
 29c:	4c 19 e5             	sbb    rbp,r12
 29f:	4c 19 ee             	sbb    rsi,r13
 2a2:	48 09 c9             	or     rcx,rcx
 2a5:	4d 0f 44 f0          	cmove  r14,r8
 2a9:	4d 0f 44 f9          	cmove  r15,r9
 2ad:	49 0f 44 c2          	cmove  rax,r10
 2b1:	4c 89 37             	mov    QWORD PTR [rdi],r14
 2b4:	49 0f 44 db          	cmove  rbx,r11
 2b8:	4c 89 7f 08          	mov    QWORD PTR [rdi+0x8],r15
 2bc:	49 0f 44 ec          	cmove  rbp,r12
 2c0:	48 89 47 10          	mov    QWORD PTR [rdi+0x10],rax
 2c4:	49 0f 44 f5          	cmove  rsi,r13
 2c8:	48 89 5f 18          	mov    QWORD PTR [rdi+0x18],rbx
 2cc:	48 89 6f 20          	mov    QWORD PTR [rdi+0x20],rbp
 2d0:	48 89 77 28          	mov    QWORD PTR [rdi+0x28],rsi
 2d4:	4c 8b 7c 24 08       	mov    r15,QWORD PTR [rsp+0x8]
 2d9:	4c 8b 74 24 10       	mov    r14,QWORD PTR [rsp+0x10]
 2de:	4c 8b 6c 24 18       	mov    r13,QWORD PTR [rsp+0x18]
 2e3:	4c 8b 64 24 20       	mov    r12,QWORD PTR [rsp+0x20]
 2e8:	48 8b 5c 24 28       	mov    rbx,QWORD PTR [rsp+0x28]
 2ed:	48 8b 6c 24 30       	mov    rbp,QWORD PTR [rsp+0x30]
 2f2:	48 8d 64 24 38       	lea    rsp,[rsp+0x38]
 2f7:	f3 c3                	repz ret 
 2f9:	0f 1f 80 00 00 00 00 	nop    DWORD PTR [rax+0x0]

0000000000000300 <sub_mod_384>:
 300:	f3 0f 1e fa          	endbr64 
 304:	55                   	push   rbp
 305:	53                   	push   rbx
 306:	41 54                	push   r12
 308:	41 55                	push   r13
 30a:	41 56                	push   r14
 30c:	41 57                	push   r15
 30e:	48 83 ec 08          	sub    rsp,0x8
 312:	e8 29 00 00 00       	call   340 <__sub_mod_384>
 317:	4c 8b 7c 24 08       	mov    r15,QWORD PTR [rsp+0x8]
 31c:	4c 8b 74 24 10       	mov    r14,QWORD PTR [rsp+0x10]
 321:	4c 8b 6c 24 18       	mov    r13,QWORD PTR [rsp+0x18]
 326:	4c 8b 64 24 20       	mov    r12,QWORD PTR [rsp+0x20]
 32b:	48 8b 5c 24 28       	mov    rbx,QWORD PTR [rsp+0x28]
 330:	48 8b 6c 24 30       	mov    rbp,QWORD PTR [rsp+0x30]
 335:	48 8d 64 24 38       	lea    rsp,[rsp+0x38]
 33a:	f3 c3                	repz ret 
 33c:	0f 1f 40 00          	nop    DWORD PTR [rax+0x0]

0000000000000340 <__sub_mod_384>:
 340:	f3 0f 1e fa          	endbr64 
 344:	4c 8b 06             	mov    r8,QWORD PTR [rsi]
 347:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
 34b:	4c 8b 56 10          	mov    r10,QWORD PTR [rsi+0x10]
 34f:	4c 8b 5e 18          	mov    r11,QWORD PTR [rsi+0x18]
 353:	4c 8b 66 20          	mov    r12,QWORD PTR [rsi+0x20]
 357:	4c 8b 6e 28          	mov    r13,QWORD PTR [rsi+0x28]
 35b:	4c 2b 02             	sub    r8,QWORD PTR [rdx]
 35e:	4c 8b 31             	mov    r14,QWORD PTR [rcx]
 361:	4c 1b 4a 08          	sbb    r9,QWORD PTR [rdx+0x8]
 365:	4c 8b 79 08          	mov    r15,QWORD PTR [rcx+0x8]
 369:	4c 1b 52 10          	sbb    r10,QWORD PTR [rdx+0x10]
 36d:	48 8b 41 10          	mov    rax,QWORD PTR [rcx+0x10]
 371:	4c 1b 5a 18          	sbb    r11,QWORD PTR [rdx+0x18]
 375:	48 8b 59 18          	mov    rbx,QWORD PTR [rcx+0x18]
 379:	4c 1b 62 20          	sbb    r12,QWORD PTR [rdx+0x20]
 37d:	48 8b 69 20          	mov    rbp,QWORD PTR [rcx+0x20]
 381:	4c 1b 6a 28          	sbb    r13,QWORD PTR [rdx+0x28]
 385:	48 8b 71 28          	mov    rsi,QWORD PTR [rcx+0x28]
 389:	48 19 d2             	sbb    rdx,rdx
 38c:	49 21 d6             	and    r14,rdx
 38f:	49 21 d7             	and    r15,rdx
 392:	48 21 d0             	and    rax,rdx
 395:	48 21 d3             	and    rbx,rdx
 398:	48 21 d5             	and    rbp,rdx
 39b:	48 21 d6             	and    rsi,rdx
 39e:	4d 01 f0             	add    r8,r14
 3a1:	4d 11 f9             	adc    r9,r15
 3a4:	4c 89 07             	mov    QWORD PTR [rdi],r8
 3a7:	49 11 c2             	adc    r10,rax
 3aa:	4c 89 4f 08          	mov    QWORD PTR [rdi+0x8],r9
 3ae:	49 11 db             	adc    r11,rbx
 3b1:	4c 89 57 10          	mov    QWORD PTR [rdi+0x10],r10
 3b5:	49 11 ec             	adc    r12,rbp
 3b8:	4c 89 5f 18          	mov    QWORD PTR [rdi+0x18],r11
 3bc:	49 11 f5             	adc    r13,rsi
 3bf:	4c 89 67 20          	mov    QWORD PTR [rdi+0x20],r12
 3c3:	4c 89 6f 28          	mov    QWORD PTR [rdi+0x28],r13
 3c7:	f3 c3                	repz ret 
 3c9:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
 3d4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
 3df:	90                   	nop

00000000000003e0 <__add_mont_384>:
 3e0:	f3 0f 1e fa          	endbr64 
 3e4:	4c 8b 06             	mov    r8,QWORD PTR [rsi]
 3e7:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
 3eb:	4c 8b 56 10          	mov    r10,QWORD PTR [rsi+0x10]
 3ef:	4c 8b 5e 18          	mov    r11,QWORD PTR [rsi+0x18]
 3f3:	4c 8b 66 20          	mov    r12,QWORD PTR [rsi+0x20]
 3f7:	4c 8b 6e 28          	mov    r13,QWORD PTR [rsi+0x28]
 3fb:	4c 03 02             	add    r8,QWORD PTR [rdx]
 3fe:	4c 13 4a 08          	adc    r9,QWORD PTR [rdx+0x8]
 402:	4c 13 52 10          	adc    r10,QWORD PTR [rdx+0x10]
 406:	4d 89 c6             	mov    r14,r8
 409:	4c 13 5a 18          	adc    r11,QWORD PTR [rdx+0x18]
 40d:	4d 89 cf             	mov    r15,r9
 410:	4c 13 62 20          	adc    r12,QWORD PTR [rdx+0x20]
 414:	4c 89 d0             	mov    rax,r10
 417:	4c 13 6a 28          	adc    r13,QWORD PTR [rdx+0x28]
 41b:	4c 89 db             	mov    rbx,r11
 41e:	48 19 d2             	sbb    rdx,rdx
 421:	4c 2b 01             	sub    r8,QWORD PTR [rcx]
 424:	4c 1b 49 08          	sbb    r9,QWORD PTR [rcx+0x8]
 428:	4c 89 e5             	mov    rbp,r12
 42b:	4c 1b 51 10          	sbb    r10,QWORD PTR [rcx+0x10]
 42f:	4c 1b 59 18          	sbb    r11,QWORD PTR [rcx+0x18]
 433:	4c 1b 61 20          	sbb    r12,QWORD PTR [rcx+0x20]
 437:	4c 89 ee             	mov    rsi,r13
 43a:	4c 1b 69 28          	sbb    r13,QWORD PTR [rcx+0x28]
 43e:	48 83 da 00          	sbb    rdx,0x0
 442:	4d 0f 42 c6          	cmovb  r8,r14
 446:	4d 0f 42 cf          	cmovb  r9,r15
 44a:	4c 0f 42 d0          	cmovb  r10,rax
 44e:	4c 89 07             	mov    QWORD PTR [rdi],r8
 451:	4c 0f 42 db          	cmovb  r11,rbx
 455:	4c 89 4f 08          	mov    QWORD PTR [rdi+0x8],r9
 459:	4c 0f 42 e5          	cmovb  r12,rbp
 45d:	4c 89 57 10          	mov    QWORD PTR [rdi+0x10],r10
 461:	4c 0f 42 ee          	cmovb  r13,rsi
 465:	4c 89 5f 18          	mov    QWORD PTR [rdi+0x18],r11
 469:	4c 89 67 20          	mov    QWORD PTR [rdi+0x20],r12
 46d:	4c 89 6f 28          	mov    QWORD PTR [rdi+0x28],r13
 471:	f3 c3                	repz ret 
 473:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
 47e:	66 90                	xchg   ax,ax

0000000000000480 <__sub_mont_384>:
 480:	f3 0f 1e fa          	endbr64 
 484:	4c 8b 06             	mov    r8,QWORD PTR [rsi]
 487:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
 48b:	4c 8b 56 10          	mov    r10,QWORD PTR [rsi+0x10]
 48f:	4c 8b 5e 18          	mov    r11,QWORD PTR [rsi+0x18]
 493:	4c 8b 66 20          	mov    r12,QWORD PTR [rsi+0x20]
 497:	4c 8b 6e 28          	mov    r13,QWORD PTR [rsi+0x28]

000000000000049b <__sub_mod_384_a_is_loaded>:
 49b:	4c 2b 02             	sub    r8,QWORD PTR [rdx]
 49e:	4c 8b 31             	mov    r14,QWORD PTR [rcx]
 4a1:	4c 1b 4a 08          	sbb    r9,QWORD PTR [rdx+0x8]
 4a5:	4c 8b 79 08          	mov    r15,QWORD PTR [rcx+0x8]
 4a9:	4c 1b 52 10          	sbb    r10,QWORD PTR [rdx+0x10]
 4ad:	48 8b 41 10          	mov    rax,QWORD PTR [rcx+0x10]
 4b1:	4c 1b 5a 18          	sbb    r11,QWORD PTR [rdx+0x18]
 4b5:	48 8b 59 18          	mov    rbx,QWORD PTR [rcx+0x18]
 4b9:	4c 1b 62 20          	sbb    r12,QWORD PTR [rdx+0x20]
 4bd:	48 8b 69 20          	mov    rbp,QWORD PTR [rcx+0x20]
 4c1:	4c 1b 6a 28          	sbb    r13,QWORD PTR [rdx+0x28]
 4c5:	48 8b 71 28          	mov    rsi,QWORD PTR [rcx+0x28]
 4c9:	48 19 d2             	sbb    rdx,rdx
 4cc:	49 21 d6             	and    r14,rdx
 4cf:	49 21 d7             	and    r15,rdx
 4d2:	48 21 d0             	and    rax,rdx
 4d5:	48 21 d3             	and    rbx,rdx
 4d8:	48 21 d5             	and    rbp,rdx
 4db:	48 21 d6             	and    rsi,rdx
 4de:	4d 01 f0             	add    r8,r14
 4e1:	4d 11 f9             	adc    r9,r15
 4e4:	4c 89 07             	mov    QWORD PTR [rdi],r8
 4e7:	49 11 c2             	adc    r10,rax
 4ea:	4c 89 4f 08          	mov    QWORD PTR [rdi+0x8],r9
 4ee:	49 11 db             	adc    r11,rbx
 4f1:	4c 89 57 10          	mov    QWORD PTR [rdi+0x10],r10
 4f5:	49 11 ec             	adc    r12,rbp
 4f8:	4c 89 5f 18          	mov    QWORD PTR [rdi+0x18],r11
 4fc:	49 11 f5             	adc    r13,rsi
 4ff:	4c 89 67 20          	mov    QWORD PTR [rdi+0x20],r12
 503:	4c 89 6f 28          	mov    QWORD PTR [rdi+0x28],r13
 507:	f3 c3                	repz ret 
 509:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
 514:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
 51f:	90                   	nop

0000000000000520 <mulx_mont_384>:
 520:	f3 0f 1e fa          	endbr64 
 524:	55                   	push   rbp
 525:	53                   	push   rbx
 526:	41 54                	push   r12
 528:	41 55                	push   r13
 52a:	41 56                	push   r14
 52c:	41 57                	push   r15
 52e:	48 8d 64 24 e8       	lea    rsp,[rsp-0x18]
 533:	48 89 d3             	mov    rbx,rdx
 536:	48 8b 12             	mov    rdx,QWORD PTR [rdx]
 539:	4c 8b 36             	mov    r14,QWORD PTR [rsi]
 53c:	4c 8b 7e 08          	mov    r15,QWORD PTR [rsi+0x8]
 540:	48 8b 46 10          	mov    rax,QWORD PTR [rsi+0x10]
 544:	4c 8b 66 18          	mov    r12,QWORD PTR [rsi+0x18]
 548:	48 89 7c 24 10       	mov    QWORD PTR [rsp+0x10],rdi
 54d:	48 8b 7e 20          	mov    rdi,QWORD PTR [rsi+0x20]
 551:	48 8b 6e 28          	mov    rbp,QWORD PTR [rsi+0x28]
 555:	48 8d 76 80          	lea    rsi,[rsi-0x80]
 559:	48 8d 49 80          	lea    rcx,[rcx-0x80]
 55d:	4c 89 04 24          	mov    QWORD PTR [rsp],r8
 561:	c4 42 bb f6 ce       	mulx   r9,r8,r14
 566:	e8 35 00 00 00       	call   5a0 <__mulx_mont_384>
 56b:	4c 8b 7c 24 18       	mov    r15,QWORD PTR [rsp+0x18]
 570:	4c 8b 74 24 20       	mov    r14,QWORD PTR [rsp+0x20]
 575:	4c 8b 6c 24 28       	mov    r13,QWORD PTR [rsp+0x28]
 57a:	4c 8b 64 24 30       	mov    r12,QWORD PTR [rsp+0x30]
 57f:	48 8b 5c 24 38       	mov    rbx,QWORD PTR [rsp+0x38]
 584:	48 8b 6c 24 40       	mov    rbp,QWORD PTR [rsp+0x40]
 589:	48 8d 64 24 48       	lea    rsp,[rsp+0x48]
 58e:	f3 c3                	repz ret 
 590:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 nop WORD PTR cs:[rax+rax*1+0x0]
 59b:	0f 1f 44 00 00       	nop    DWORD PTR [rax+rax*1+0x0]

00000000000005a0 <__mulx_mont_384>:
 5a0:	f3 0f 1e fa          	endbr64 
 5a4:	c4 42 8b f6 d7       	mulx   r10,r14,r15
 5a9:	c4 62 83 f6 d8       	mulx   r11,r15,rax
 5ae:	4d 01 f1             	add    r9,r14
 5b1:	c4 42 fb f6 e4       	mulx   r12,rax,r12
 5b6:	4d 11 fa             	adc    r10,r15
 5b9:	c4 62 c3 f6 ef       	mulx   r13,rdi,rdi
 5be:	49 11 c3             	adc    r11,rax
 5c1:	c4 62 d3 f6 f5       	mulx   r14,rbp,rbp
 5c6:	48 8b 53 08          	mov    rdx,QWORD PTR [rbx+0x8]
 5ca:	49 11 fc             	adc    r12,rdi
 5cd:	49 11 ed             	adc    r13,rbp
 5d0:	49 83 d6 00          	adc    r14,0x0
 5d4:	4d 31 ff             	xor    r15,r15
 5d7:	4c 89 44 24 10       	mov    QWORD PTR [rsp+0x10],r8
 5dc:	4c 0f af 44 24 08    	imul   r8,QWORD PTR [rsp+0x8]
 5e2:	48 31 c0             	xor    rax,rax
 5e5:	c4 e2 c3 f6 ae 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x80]
 5ee:	f3 4c 0f 38 f6 cf    	adox   r9,rdi
 5f4:	66 4c 0f 38 f6 d5    	adcx   r10,rbp
 5fa:	c4 e2 c3 f6 ae 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x88]
 603:	f3 4c 0f 38 f6 d7    	adox   r10,rdi
 609:	66 4c 0f 38 f6 dd    	adcx   r11,rbp
 60f:	c4 e2 c3 f6 ae 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x90]
 618:	f3 4c 0f 38 f6 df    	adox   r11,rdi
 61e:	66 4c 0f 38 f6 e5    	adcx   r12,rbp
 624:	c4 e2 c3 f6 ae 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x98]
 62d:	f3 4c 0f 38 f6 e7    	adox   r12,rdi
 633:	66 4c 0f 38 f6 ed    	adcx   r13,rbp
 639:	c4 e2 c3 f6 ae a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa0]
 642:	f3 4c 0f 38 f6 ef    	adox   r13,rdi
 648:	66 4c 0f 38 f6 f5    	adcx   r14,rbp
 64e:	c4 e2 c3 f6 ae a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa8]
 657:	4c 89 c2             	mov    rdx,r8
 65a:	f3 4c 0f 38 f6 f7    	adox   r14,rdi
 660:	66 4c 0f 38 f6 fd    	adcx   r15,rbp
 666:	f3 4c 0f 38 f6 f8    	adox   r15,rax
 66c:	f3 48 0f 38 f6 c0    	adox   rax,rax
 672:	4d 31 c0             	xor    r8,r8
 675:	c4 e2 c3 f6 a9 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x80]
 67e:	66 48 0f 38 f6 7c 24 10 	adcx   rdi,QWORD PTR [rsp+0x10]
 686:	f3 4c 0f 38 f6 cd    	adox   r9,rbp
 68c:	c4 e2 c3 f6 a9 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x88]
 695:	66 4c 0f 38 f6 cf    	adcx   r9,rdi
 69b:	f3 4c 0f 38 f6 d5    	adox   r10,rbp
 6a1:	c4 e2 c3 f6 a9 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x90]
 6aa:	66 4c 0f 38 f6 d7    	adcx   r10,rdi
 6b0:	f3 4c 0f 38 f6 dd    	adox   r11,rbp
 6b6:	c4 e2 c3 f6 a9 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x98]
 6bf:	66 4c 0f 38 f6 df    	adcx   r11,rdi
 6c5:	f3 4c 0f 38 f6 e5    	adox   r12,rbp
 6cb:	c4 e2 c3 f6 a9 a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa0]
 6d4:	66 4c 0f 38 f6 e7    	adcx   r12,rdi
 6da:	f3 4c 0f 38 f6 ed    	adox   r13,rbp
 6e0:	c4 e2 c3 f6 a9 a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa8]
 6e9:	48 8b 53 10          	mov    rdx,QWORD PTR [rbx+0x10]
 6ed:	66 4c 0f 38 f6 ef    	adcx   r13,rdi
 6f3:	f3 4c 0f 38 f6 f5    	adox   r14,rbp
 6f9:	66 4d 0f 38 f6 f0    	adcx   r14,r8
 6ff:	f3 4d 0f 38 f6 f8    	adox   r15,r8
 705:	66 4d 0f 38 f6 f8    	adcx   r15,r8
 70b:	f3 49 0f 38 f6 c0    	adox   rax,r8
 711:	66 49 0f 38 f6 c0    	adcx   rax,r8
 717:	4c 89 4c 24 10       	mov    QWORD PTR [rsp+0x10],r9
 71c:	4c 0f af 4c 24 08    	imul   r9,QWORD PTR [rsp+0x8]
 722:	4d 31 c0             	xor    r8,r8
 725:	c4 e2 c3 f6 ae 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x80]
 72e:	f3 4c 0f 38 f6 d7    	adox   r10,rdi
 734:	66 4c 0f 38 f6 dd    	adcx   r11,rbp
 73a:	c4 e2 c3 f6 ae 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x88]
 743:	f3 4c 0f 38 f6 df    	adox   r11,rdi
 749:	66 4c 0f 38 f6 e5    	adcx   r12,rbp
 74f:	c4 e2 c3 f6 ae 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x90]
 758:	f3 4c 0f 38 f6 e7    	adox   r12,rdi
 75e:	66 4c 0f 38 f6 ed    	adcx   r13,rbp
 764:	c4 e2 c3 f6 ae 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x98]
 76d:	f3 4c 0f 38 f6 ef    	adox   r13,rdi
 773:	66 4c 0f 38 f6 f5    	adcx   r14,rbp
 779:	c4 e2 c3 f6 ae a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa0]
 782:	f3 4c 0f 38 f6 f7    	adox   r14,rdi
 788:	66 4c 0f 38 f6 fd    	adcx   r15,rbp
 78e:	c4 e2 c3 f6 ae a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa8]
 797:	4c 89 ca             	mov    rdx,r9
 79a:	f3 4c 0f 38 f6 ff    	adox   r15,rdi
 7a0:	66 48 0f 38 f6 c5    	adcx   rax,rbp
 7a6:	f3 49 0f 38 f6 c0    	adox   rax,r8
 7ac:	f3 4d 0f 38 f6 c0    	adox   r8,r8
 7b2:	4d 31 c9             	xor    r9,r9
 7b5:	c4 e2 c3 f6 a9 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x80]
 7be:	66 48 0f 38 f6 7c 24 10 	adcx   rdi,QWORD PTR [rsp+0x10]
 7c6:	f3 4c 0f 38 f6 d5    	adox   r10,rbp
 7cc:	c4 e2 c3 f6 a9 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x88]
 7d5:	66 4c 0f 38 f6 d7    	adcx   r10,rdi
 7db:	f3 4c 0f 38 f6 dd    	adox   r11,rbp
 7e1:	c4 e2 c3 f6 a9 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x90]
 7ea:	66 4c 0f 38 f6 df    	adcx   r11,rdi
 7f0:	f3 4c 0f 38 f6 e5    	adox   r12,rbp
 7f6:	c4 e2 c3 f6 a9 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x98]
 7ff:	66 4c 0f 38 f6 e7    	adcx   r12,rdi
 805:	f3 4c 0f 38 f6 ed    	adox   r13,rbp
 80b:	c4 e2 c3 f6 a9 a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa0]
 814:	66 4c 0f 38 f6 ef    	adcx   r13,rdi
 81a:	f3 4c 0f 38 f6 f5    	adox   r14,rbp
 820:	c4 e2 c3 f6 a9 a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa8]
 829:	48 8b 53 18          	mov    rdx,QWORD PTR [rbx+0x18]
 82d:	66 4c 0f 38 f6 f7    	adcx   r14,rdi
 833:	f3 4c 0f 38 f6 fd    	adox   r15,rbp
 839:	66 4d 0f 38 f6 f9    	adcx   r15,r9
 83f:	f3 49 0f 38 f6 c1    	adox   rax,r9
 845:	66 49 0f 38 f6 c1    	adcx   rax,r9
 84b:	f3 4d 0f 38 f6 c1    	adox   r8,r9
 851:	66 4d 0f 38 f6 c1    	adcx   r8,r9
 857:	4c 89 54 24 10       	mov    QWORD PTR [rsp+0x10],r10
 85c:	4c 0f af 54 24 08    	imul   r10,QWORD PTR [rsp+0x8]
 862:	4d 31 c9             	xor    r9,r9
 865:	c4 e2 c3 f6 ae 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x80]
 86e:	f3 4c 0f 38 f6 df    	adox   r11,rdi
 874:	66 4c 0f 38 f6 e5    	adcx   r12,rbp
 87a:	c4 e2 c3 f6 ae 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x88]
 883:	f3 4c 0f 38 f6 e7    	adox   r12,rdi
 889:	66 4c 0f 38 f6 ed    	adcx   r13,rbp
 88f:	c4 e2 c3 f6 ae 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x90]
 898:	f3 4c 0f 38 f6 ef    	adox   r13,rdi
 89e:	66 4c 0f 38 f6 f5    	adcx   r14,rbp
 8a4:	c4 e2 c3 f6 ae 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x98]
 8ad:	f3 4c 0f 38 f6 f7    	adox   r14,rdi
 8b3:	66 4c 0f 38 f6 fd    	adcx   r15,rbp
 8b9:	c4 e2 c3 f6 ae a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa0]
 8c2:	f3 4c 0f 38 f6 ff    	adox   r15,rdi
 8c8:	66 48 0f 38 f6 c5    	adcx   rax,rbp
 8ce:	c4 e2 c3 f6 ae a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa8]
 8d7:	4c 89 d2             	mov    rdx,r10
 8da:	f3 48 0f 38 f6 c7    	adox   rax,rdi
 8e0:	66 4c 0f 38 f6 c5    	adcx   r8,rbp
 8e6:	f3 4d 0f 38 f6 c1    	adox   r8,r9
 8ec:	f3 4d 0f 38 f6 c9    	adox   r9,r9
 8f2:	4d 31 d2             	xor    r10,r10
 8f5:	c4 e2 c3 f6 a9 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x80]
 8fe:	66 48 0f 38 f6 7c 24 10 	adcx   rdi,QWORD PTR [rsp+0x10]
 906:	f3 4c 0f 38 f6 dd    	adox   r11,rbp
 90c:	c4 e2 c3 f6 a9 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x88]
 915:	66 4c 0f 38 f6 df    	adcx   r11,rdi
 91b:	f3 4c 0f 38 f6 e5    	adox   r12,rbp
 921:	c4 e2 c3 f6 a9 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x90]
 92a:	66 4c 0f 38 f6 e7    	adcx   r12,rdi
 930:	f3 4c 0f 38 f6 ed    	adox   r13,rbp
 936:	c4 e2 c3 f6 a9 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x98]
 93f:	66 4c 0f 38 f6 ef    	adcx   r13,rdi
 945:	f3 4c 0f 38 f6 f5    	adox   r14,rbp
 94b:	c4 e2 c3 f6 a9 a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa0]
 954:	66 4c 0f 38 f6 f7    	adcx   r14,rdi
 95a:	f3 4c 0f 38 f6 fd    	adox   r15,rbp
 960:	c4 e2 c3 f6 a9 a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa8]
 969:	48 8b 53 20          	mov    rdx,QWORD PTR [rbx+0x20]
 96d:	66 4c 0f 38 f6 ff    	adcx   r15,rdi
 973:	f3 48 0f 38 f6 c5    	adox   rax,rbp
 979:	66 49 0f 38 f6 c2    	adcx   rax,r10
 97f:	f3 4d 0f 38 f6 c2    	adox   r8,r10
 985:	66 4d 0f 38 f6 c2    	adcx   r8,r10
 98b:	f3 4d 0f 38 f6 ca    	adox   r9,r10
 991:	66 4d 0f 38 f6 ca    	adcx   r9,r10
 997:	4c 89 5c 24 10       	mov    QWORD PTR [rsp+0x10],r11
 99c:	4c 0f af 5c 24 08    	imul   r11,QWORD PTR [rsp+0x8]
 9a2:	4d 31 d2             	xor    r10,r10
 9a5:	c4 e2 c3 f6 ae 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x80]
 9ae:	f3 4c 0f 38 f6 e7    	adox   r12,rdi
 9b4:	66 4c 0f 38 f6 ed    	adcx   r13,rbp
 9ba:	c4 e2 c3 f6 ae 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x88]
 9c3:	f3 4c 0f 38 f6 ef    	adox   r13,rdi
 9c9:	66 4c 0f 38 f6 f5    	adcx   r14,rbp
 9cf:	c4 e2 c3 f6 ae 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x90]
 9d8:	f3 4c 0f 38 f6 f7    	adox   r14,rdi
 9de:	66 4c 0f 38 f6 fd    	adcx   r15,rbp
 9e4:	c4 e2 c3 f6 ae 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x98]
 9ed:	f3 4c 0f 38 f6 ff    	adox   r15,rdi
 9f3:	66 48 0f 38 f6 c5    	adcx   rax,rbp
 9f9:	c4 e2 c3 f6 ae a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa0]
 a02:	f3 48 0f 38 f6 c7    	adox   rax,rdi
 a08:	66 4c 0f 38 f6 c5    	adcx   r8,rbp
 a0e:	c4 e2 c3 f6 ae a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa8]
 a17:	4c 89 da             	mov    rdx,r11
 a1a:	f3 4c 0f 38 f6 c7    	adox   r8,rdi
 a20:	66 4c 0f 38 f6 cd    	adcx   r9,rbp
 a26:	f3 4d 0f 38 f6 ca    	adox   r9,r10
 a2c:	f3 4d 0f 38 f6 d2    	adox   r10,r10
 a32:	4d 31 db             	xor    r11,r11
 a35:	c4 e2 c3 f6 a9 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x80]
 a3e:	66 48 0f 38 f6 7c 24 10 	adcx   rdi,QWORD PTR [rsp+0x10]
 a46:	f3 4c 0f 38 f6 e5    	adox   r12,rbp
 a4c:	c4 e2 c3 f6 a9 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x88]
 a55:	66 4c 0f 38 f6 e7    	adcx   r12,rdi
 a5b:	f3 4c 0f 38 f6 ed    	adox   r13,rbp
 a61:	c4 e2 c3 f6 a9 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x90]
 a6a:	66 4c 0f 38 f6 ef    	adcx   r13,rdi
 a70:	f3 4c 0f 38 f6 f5    	adox   r14,rbp
 a76:	c4 e2 c3 f6 a9 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x98]
 a7f:	66 4c 0f 38 f6 f7    	adcx   r14,rdi
 a85:	f3 4c 0f 38 f6 fd    	adox   r15,rbp
 a8b:	c4 e2 c3 f6 a9 a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa0]
 a94:	66 4c 0f 38 f6 ff    	adcx   r15,rdi
 a9a:	f3 48 0f 38 f6 c5    	adox   rax,rbp
 aa0:	c4 e2 c3 f6 a9 a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa8]
 aa9:	48 8b 53 28          	mov    rdx,QWORD PTR [rbx+0x28]
 aad:	66 48 0f 38 f6 c7    	adcx   rax,rdi
 ab3:	f3 4c 0f 38 f6 c5    	adox   r8,rbp
 ab9:	66 4d 0f 38 f6 c3    	adcx   r8,r11
 abf:	f3 4d 0f 38 f6 cb    	adox   r9,r11
 ac5:	66 4d 0f 38 f6 cb    	adcx   r9,r11
 acb:	f3 4d 0f 38 f6 d3    	adox   r10,r11
 ad1:	66 4d 0f 38 f6 d3    	adcx   r10,r11
 ad7:	4c 89 64 24 10       	mov    QWORD PTR [rsp+0x10],r12
 adc:	4c 0f af 64 24 08    	imul   r12,QWORD PTR [rsp+0x8]
 ae2:	4d 31 db             	xor    r11,r11
 ae5:	c4 e2 c3 f6 ae 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x80]
 aee:	f3 4c 0f 38 f6 ef    	adox   r13,rdi
 af4:	66 4c 0f 38 f6 f5    	adcx   r14,rbp
 afa:	c4 e2 c3 f6 ae 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x88]
 b03:	f3 4c 0f 38 f6 f7    	adox   r14,rdi
 b09:	66 4c 0f 38 f6 fd    	adcx   r15,rbp
 b0f:	c4 e2 c3 f6 ae 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x90]
 b18:	f3 4c 0f 38 f6 ff    	adox   r15,rdi
 b1e:	66 48 0f 38 f6 c5    	adcx   rax,rbp
 b24:	c4 e2 c3 f6 ae 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0x98]
 b2d:	f3 48 0f 38 f6 c7    	adox   rax,rdi
 b33:	66 4c 0f 38 f6 c5    	adcx   r8,rbp
 b39:	c4 e2 c3 f6 ae a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa0]
 b42:	f3 4c 0f 38 f6 c7    	adox   r8,rdi
 b48:	66 4c 0f 38 f6 cd    	adcx   r9,rbp
 b4e:	c4 e2 c3 f6 ae a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rsi+0xa8]
 b57:	4c 89 e2             	mov    rdx,r12
 b5a:	f3 4c 0f 38 f6 cf    	adox   r9,rdi
 b60:	66 4c 0f 38 f6 d5    	adcx   r10,rbp
 b66:	f3 4d 0f 38 f6 d3    	adox   r10,r11
 b6c:	f3 4d 0f 38 f6 db    	adox   r11,r11
 b72:	4d 31 e4             	xor    r12,r12
 b75:	c4 e2 c3 f6 a9 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x80]
 b7e:	66 48 0f 38 f6 7c 24 10 	adcx   rdi,QWORD PTR [rsp+0x10]
 b86:	f3 4c 0f 38 f6 ed    	adox   r13,rbp
 b8c:	c4 e2 c3 f6 a9 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x88]
 b95:	66 4c 0f 38 f6 ef    	adcx   r13,rdi
 b9b:	f3 4c 0f 38 f6 f5    	adox   r14,rbp
 ba1:	c4 e2 c3 f6 a9 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x90]
 baa:	66 4c 0f 38 f6 f7    	adcx   r14,rdi
 bb0:	f3 4c 0f 38 f6 fd    	adox   r15,rbp
 bb6:	c4 e2 c3 f6 a9 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x98]
 bbf:	66 4c 0f 38 f6 ff    	adcx   r15,rdi
 bc5:	f3 48 0f 38 f6 c5    	adox   rax,rbp
 bcb:	c4 e2 c3 f6 a9 a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa0]
 bd4:	66 48 0f 38 f6 c7    	adcx   rax,rdi
 bda:	f3 4c 0f 38 f6 c5    	adox   r8,rbp
 be0:	c4 e2 c3 f6 a9 a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa8]
 be9:	4c 89 ea             	mov    rdx,r13
 bec:	66 4c 0f 38 f6 c7    	adcx   r8,rdi
 bf2:	f3 4c 0f 38 f6 cd    	adox   r9,rbp
 bf8:	66 4d 0f 38 f6 cc    	adcx   r9,r12
 bfe:	f3 4d 0f 38 f6 d4    	adox   r10,r12
 c04:	66 4d 0f 38 f6 d4    	adcx   r10,r12
 c0a:	f3 4d 0f 38 f6 dc    	adox   r11,r12
 c10:	66 4d 0f 38 f6 dc    	adcx   r11,r12
 c16:	48 0f af 54 24 08    	imul   rdx,QWORD PTR [rsp+0x8]
 c1c:	48 8b 5c 24 18       	mov    rbx,QWORD PTR [rsp+0x18]
 c21:	4d 31 e4             	xor    r12,r12
 c24:	c4 e2 c3 f6 a9 80 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x80]
 c2d:	66 4c 0f 38 f6 ef    	adcx   r13,rdi
 c33:	f3 4c 0f 38 f6 f5    	adox   r14,rbp
 c39:	c4 e2 c3 f6 a9 88 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x88]
 c42:	66 4c 0f 38 f6 f7    	adcx   r14,rdi
 c48:	f3 4c 0f 38 f6 fd    	adox   r15,rbp
 c4e:	c4 e2 c3 f6 a9 90 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x90]
 c57:	66 4c 0f 38 f6 ff    	adcx   r15,rdi
 c5d:	f3 48 0f 38 f6 c5    	adox   rax,rbp
 c63:	c4 e2 c3 f6 a9 98 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0x98]
 c6c:	66 48 0f 38 f6 c7    	adcx   rax,rdi
 c72:	f3 4c 0f 38 f6 c5    	adox   r8,rbp
 c78:	4d 89 fd             	mov    r13,r15
 c7b:	c4 e2 c3 f6 a9 a0 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa0]
 c84:	66 4c 0f 38 f6 c7    	adcx   r8,rdi
 c8a:	f3 4c 0f 38 f6 cd    	adox   r9,rbp
 c90:	48 89 c6             	mov    rsi,rax
 c93:	c4 e2 c3 f6 a9 a8 00 00 00 	mulx   rbp,rdi,QWORD PTR [rcx+0xa8]
 c9c:	66 4c 0f 38 f6 cf    	adcx   r9,rdi
 ca2:	f3 4c 0f 38 f6 d5    	adox   r10,rbp
 ca8:	4c 89 f2             	mov    rdx,r14
 cab:	66 4d 0f 38 f6 d4    	adcx   r10,r12
 cb1:	f3 4d 0f 38 f6 dc    	adox   r11,r12
 cb7:	48 8d 89 80 00 00 00 	lea    rcx,[rcx+0x80]
 cbe:	4d 89 c4             	mov    r12,r8
 cc1:	49 83 d3 00          	adc    r11,0x0
 cc5:	4c 2b 31             	sub    r14,QWORD PTR [rcx]
 cc8:	4c 1b 79 08          	sbb    r15,QWORD PTR [rcx+0x8]
 ccc:	4c 89 cf             	mov    rdi,r9
 ccf:	48 1b 41 10          	sbb    rax,QWORD PTR [rcx+0x10]
 cd3:	4c 1b 41 18          	sbb    r8,QWORD PTR [rcx+0x18]
 cd7:	4c 1b 49 20          	sbb    r9,QWORD PTR [rcx+0x20]
 cdb:	4c 89 d5             	mov    rbp,r10
 cde:	4c 1b 51 28          	sbb    r10,QWORD PTR [rcx+0x28]
 ce2:	49 83 db 00          	sbb    r11,0x0
 ce6:	49 0f 43 d6          	cmovae rdx,r14
 cea:	4d 0f 42 fd          	cmovb  r15,r13
 cee:	48 0f 42 c6          	cmovb  rax,rsi
 cf2:	4d 0f 43 e0          	cmovae r12,r8
 cf6:	48 89 13             	mov    QWORD PTR [rbx],rdx
 cf9:	49 0f 43 f9          	cmovae rdi,r9
 cfd:	4c 89 7b 08          	mov    QWORD PTR [rbx+0x8],r15
 d01:	49 0f 43 ea          	cmovae rbp,r10
 d05:	48 89 43 10          	mov    QWORD PTR [rbx+0x10],rax
 d09:	4c 89 63 18          	mov    QWORD PTR [rbx+0x18],r12
 d0d:	48 89 7b 20          	mov    QWORD PTR [rbx+0x20],rdi
 d11:	48 89 6b 28          	mov    QWORD PTR [rbx+0x28],rbp
 d15:	f3 c3                	repz ret 
 d17:	66 0f 1f 84 00 00 00 00 00 	nop    WORD PTR [rax+rax*1+0x0]

0000000000000d20 <sqrx_mont_384>:
 d20:	f3 0f 1e fa          	endbr64 
 d24:	55                   	push   rbp
 d25:	53                   	push   rbx
 d26:	41 54                	push   r12
 d28:	41 55                	push   r13
 d2a:	41 56                	push   r14
 d2c:	41 57                	push   r15
 d2e:	48 8d 64 24 e8       	lea    rsp,[rsp-0x18]
 d33:	49 89 c8             	mov    r8,rcx
 d36:	48 8d 4a 80          	lea    rcx,[rdx-0x80]
 d3a:	48 8b 16             	mov    rdx,QWORD PTR [rsi]
 d3d:	4c 8b 7e 08          	mov    r15,QWORD PTR [rsi+0x8]
 d41:	48 8b 46 10          	mov    rax,QWORD PTR [rsi+0x10]
 d45:	4c 8b 66 18          	mov    r12,QWORD PTR [rsi+0x18]
 d49:	48 89 7c 24 10       	mov    QWORD PTR [rsp+0x10],rdi
 d4e:	48 8b 7e 20          	mov    rdi,QWORD PTR [rsi+0x20]
 d52:	48 8b 6e 28          	mov    rbp,QWORD PTR [rsi+0x28]
 d56:	48 8d 1e             	lea    rbx,[rsi]
 d59:	4c 89 04 24          	mov    QWORD PTR [rsp],r8
 d5d:	48 8d 76 80          	lea    rsi,[rsi-0x80]
 d61:	c4 62 bb f6 ca       	mulx   r9,r8,rdx
 d66:	e8 35 f8 ff ff       	call   5a0 <__mulx_mont_384>
 d6b:	4c 8b 7c 24 18       	mov    r15,QWORD PTR [rsp+0x18]
 d70:	4c 8b 74 24 20       	mov    r14,QWORD PTR [rsp+0x20]
 d75:	4c 8b 6c 24 28       	mov    r13,QWORD PTR [rsp+0x28]
 d7a:	4c 8b 64 24 30       	mov    r12,QWORD PTR [rsp+0x30]
 d7f:	48 8b 5c 24 38       	mov    rbx,QWORD PTR [rsp+0x38]
 d84:	48 8b 6c 24 40       	mov    rbp,QWORD PTR [rsp+0x40]
 d89:	48 8d 64 24 48       	lea    rsp,[rsp+0x48]
 d8e:	f3 c3                	repz ret 
