
../target/release/build/snarkvm-algorithms-17af85ed5ea73b7f/out/src/msm/blst_377/asm.o:     file format elf64-x86-64


Disassembly of section .text._Z8mont_384PyS_PKyy:

0000000000000000 <mont_384(unsigned long long*, unsigned long long*, unsigned long long const*, unsigned long long)>:
   0:	f3 0f 1e fa          	endbr64 
   4:	41 57                	push   r15
   6:	41 56                	push   r14
   8:	49 89 cf             	mov    r15,rcx
   b:	41 55                	push   r13
   d:	41 54                	push   r12
   f:	49 89 fd             	mov    r13,rdi
  12:	48 89 cf             	mov    rdi,rcx
  15:	55                   	push   rbp
  16:	53                   	push   rbx
  17:	48 89 d5             	mov    rbp,rdx
  1a:	48 81 ec a8 00 00 00 	sub    rsp,0xa8
  21:	64 48 8b 04 25 28 00 00 00 	mov    rax,QWORD PTR fs:0x28
  2a:	48 89 84 24 98 00 00 00 	mov    QWORD PTR [rsp+0x98],rax
  32:	48 8b 06             	mov    rax,QWORD PTR [rsi]
  35:	48 0f af f8          	imul   rdi,rax
  39:	48 83 c0 00          	add    rax,0x0
  3d:	48 89 fa             	mov    rdx,rdi
  40:	4c 89 ff             	mov    rdi,r15
  43:	c4 62 b3 f6 55 00    	mulx   r10,r9,QWORD PTR [rbp+0x0]
  49:	4c 01 c8             	add    rax,r9
  4c:	4d 89 d0             	mov    r8,r10
  4f:	c4 62 b3 f6 55 08    	mulx   r10,r9,QWORD PTR [rbp+0x8]
  55:	49 83 d0 00          	adc    r8,0x0
  59:	4c 03 46 08          	add    r8,QWORD PTR [rsi+0x8]
  5d:	0f 92 c0             	setb   al
  60:	4d 01 c8             	add    r8,r9
  63:	44 0f b6 f0          	movzx  r14d,al
  67:	4c 89 46 08          	mov    QWORD PTR [rsi+0x8],r8
  6b:	4d 11 d6             	adc    r14,r10
  6e:	4c 03 76 10          	add    r14,QWORD PTR [rsi+0x10]
  72:	c4 e2 f3 f6 5d 10    	mulx   rbx,rcx,QWORD PTR [rbp+0x10]
  78:	0f 92 c0             	setb   al
  7b:	49 01 ce             	add    r14,rcx
  7e:	44 0f b6 e0          	movzx  r12d,al
  82:	4c 89 76 10          	mov    QWORD PTR [rsi+0x10],r14
  86:	49 11 dc             	adc    r12,rbx
  89:	4c 03 66 18          	add    r12,QWORD PTR [rsi+0x18]
  8d:	c4 e2 f3 f6 5d 18    	mulx   rbx,rcx,QWORD PTR [rbp+0x18]
  93:	0f 92 c0             	setb   al
  96:	49 01 cc             	add    r12,rcx
  99:	48 89 d9             	mov    rcx,rbx
  9c:	0f b6 d8             	movzx  ebx,al
  9f:	4c 89 66 18          	mov    QWORD PTR [rsi+0x18],r12
  a3:	48 11 cb             	adc    rbx,rcx
  a6:	48 03 5e 20          	add    rbx,QWORD PTR [rsi+0x20]
  aa:	c4 62 ab f6 5d 20    	mulx   r11,r10,QWORD PTR [rbp+0x20]
  b0:	0f 92 c1             	setb   cl
  b3:	4c 01 d3             	add    rbx,r10
  b6:	0f b6 c1             	movzx  eax,cl
  b9:	48 89 5e 20          	mov    QWORD PTR [rsi+0x20],rbx
  bd:	4c 11 d8             	adc    rax,r11
  c0:	48 03 46 28          	add    rax,QWORD PTR [rsi+0x28]
  c4:	c4 62 ab f6 5d 28    	mulx   r11,r10,QWORD PTR [rbp+0x28]
  ca:	4c 89 7c 24 10       	mov    QWORD PTR [rsp+0x10],r15
  cf:	48 89 2c 24          	mov    QWORD PTR [rsp],rbp
  d3:	41 0f 92 c1          	setb   r9b
  d7:	4c 01 d0             	add    rax,r10
  da:	41 0f b6 c9          	movzx  ecx,r9b
  de:	48 89 46 28          	mov    QWORD PTR [rsi+0x28],rax
  e2:	4c 11 d9             	adc    rcx,r11
  e5:	48 03 4e 30          	add    rcx,QWORD PTR [rsi+0x30]
  e9:	4d 89 c3             	mov    r11,r8
  ec:	41 0f 92 c2          	setb   r10b
  f0:	49 0f af f8          	imul   rdi,r8
  f4:	48 89 4e 30          	mov    QWORD PTR [rsi+0x30],rcx
  f8:	49 83 c3 00          	add    r11,0x0
  fc:	48 89 fa             	mov    rdx,rdi
  ff:	c4 62 bb f6 4d 00    	mulx   r9,r8,QWORD PTR [rbp+0x0]
 105:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
 10a:	4d 01 d8             	add    r8,r11
 10d:	4c 8b 5c 24 08       	mov    r11,QWORD PTR [rsp+0x8]
 112:	c4 62 bb f6 4d 08    	mulx   r9,r8,QWORD PTR [rbp+0x8]
 118:	4c 89 4c 24 28       	mov    QWORD PTR [rsp+0x28],r9
 11d:	4c 89 44 24 20       	mov    QWORD PTR [rsp+0x20],r8
 122:	49 83 d3 00          	adc    r11,0x0
 126:	4d 01 f3             	add    r11,r14
 129:	41 0f 92 c7          	setb   r15b
 12d:	4d 01 c3             	add    r11,r8
 130:	4c 8b 44 24 28       	mov    r8,QWORD PTR [rsp+0x28]
 135:	41 0f b6 ef          	movzx  ebp,r15b
 139:	4c 8b 3c 24          	mov    r15,QWORD PTR [rsp]
 13d:	4c 89 5e 10          	mov    QWORD PTR [rsi+0x10],r11
 141:	4c 11 c5             	adc    rbp,r8
 144:	4c 01 e5             	add    rbp,r12
 147:	c4 42 bb f6 4f 10    	mulx   r9,r8,QWORD PTR [r15+0x10]
 14d:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
 152:	41 0f 92 c6          	setb   r14b
 156:	4c 01 c5             	add    rbp,r8
 159:	4c 8b 44 24 08       	mov    r8,QWORD PTR [rsp+0x8]
 15e:	45 0f b6 f6          	movzx  r14d,r14b
 162:	48 89 6e 18          	mov    QWORD PTR [rsi+0x18],rbp
 166:	4d 89 f9             	mov    r9,r15
 169:	4d 11 c6             	adc    r14,r8
 16c:	4c 01 f3             	add    rbx,r14
 16f:	c4 42 8b f6 7f 18    	mulx   r15,r14,QWORD PTR [r15+0x18]
 175:	41 0f 92 c4          	setb   r12b
 179:	4c 01 f3             	add    rbx,r14
 17c:	45 0f b6 e4          	movzx  r12d,r12b
 180:	48 89 5e 20          	mov    QWORD PTR [rsi+0x20],rbx
 184:	4d 11 fc             	adc    r12,r15
 187:	c4 42 8b f6 79 20    	mulx   r15,r14,QWORD PTR [r9+0x20]
 18d:	4c 01 e0             	add    rax,r12
 190:	41 0f 92 c4          	setb   r12b
 194:	4c 01 f0             	add    rax,r14
 197:	45 0f b6 e4          	movzx  r12d,r12b
 19b:	48 89 46 28          	mov    QWORD PTR [rsi+0x28],rax
 19f:	4c 89 0c 24          	mov    QWORD PTR [rsp],r9
 1a3:	4d 11 fc             	adc    r12,r15
 1a6:	c4 42 8b f6 79 28    	mulx   r15,r14,QWORD PTR [r9+0x28]
 1ac:	4c 01 e1             	add    rcx,r12
 1af:	41 0f 92 c4          	setb   r12b
 1b3:	4c 01 f1             	add    rcx,r14
 1b6:	41 0f 92 c0          	setb   r8b
 1ba:	41 83 e2 01          	and    r10d,0x1
 1be:	4c 03 56 38          	add    r10,QWORD PTR [rsi+0x38]
 1c2:	45 0f b6 e4          	movzx  r12d,r12b
 1c6:	41 0f b6 f8          	movzx  edi,r8b
 1ca:	48 89 4e 30          	mov    QWORD PTR [rsi+0x30],rcx
 1ce:	0f 92 44 24 20       	setb   BYTE PTR [rsp+0x20]
 1d3:	4c 01 e7             	add    rdi,r12
 1d6:	4c 01 ff             	add    rdi,r15
 1d9:	4c 8b 3c 24          	mov    r15,QWORD PTR [rsp]
 1dd:	49 01 fa             	add    r10,rdi
 1e0:	48 8b 7c 24 10       	mov    rdi,QWORD PTR [rsp+0x10]
 1e5:	41 0f 92 c6          	setb   r14b
 1e9:	4c 89 56 38          	mov    QWORD PTR [rsi+0x38],r10
 1ed:	4c 89 3c 24          	mov    QWORD PTR [rsp],r15
 1f1:	49 0f af fb          	imul   rdi,r11
 1f5:	49 83 c3 00          	add    r11,0x0
 1f9:	48 89 fa             	mov    rdx,rdi
 1fc:	48 8b 3c 24          	mov    rdi,QWORD PTR [rsp]
 200:	c4 42 bb f6 0f       	mulx   r9,r8,QWORD PTR [r15]
 205:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
 20a:	4d 01 c3             	add    r11,r8
 20d:	4c 8b 44 24 08       	mov    r8,QWORD PTR [rsp+0x8]
 212:	49 83 d0 00          	adc    r8,0x0
 216:	4c 01 c5             	add    rbp,r8
 219:	c4 42 bb f6 4f 08    	mulx   r9,r8,QWORD PTR [r15+0x8]
 21f:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
 224:	41 0f 92 c3          	setb   r11b
 228:	4c 01 c5             	add    rbp,r8
 22b:	4c 8b 44 24 08       	mov    r8,QWORD PTR [rsp+0x8]
 230:	45 0f b6 db          	movzx  r11d,r11b
 234:	48 89 6e 18          	mov    QWORD PTR [rsi+0x18],rbp
 238:	4d 11 c3             	adc    r11,r8
 23b:	c4 42 bb f6 4f 10    	mulx   r9,r8,QWORD PTR [r15+0x10]
 241:	4c 01 db             	add    rbx,r11
 244:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
 249:	41 0f 92 c3          	setb   r11b
 24d:	4c 01 c3             	add    rbx,r8
 250:	4c 8b 44 24 08       	mov    r8,QWORD PTR [rsp+0x8]
 255:	45 0f b6 db          	movzx  r11d,r11b
 259:	48 89 5e 20          	mov    QWORD PTR [rsi+0x20],rbx
 25d:	4d 11 c3             	adc    r11,r8
 260:	c4 42 bb f6 4f 18    	mulx   r9,r8,QWORD PTR [r15+0x18]
 266:	4c 01 d8             	add    rax,r11
 269:	41 0f 92 c3          	setb   r11b
 26d:	4c 01 c0             	add    rax,r8
 270:	45 0f b6 db          	movzx  r11d,r11b
 274:	48 89 46 28          	mov    QWORD PTR [rsi+0x28],rax
 278:	4d 11 cb             	adc    r11,r9
 27b:	c4 42 bb f6 4f 20    	mulx   r9,r8,QWORD PTR [r15+0x20]
 281:	4c 01 d9             	add    rcx,r11
 284:	41 0f 92 c4          	setb   r12b
 288:	4c 01 c1             	add    rcx,r8
 28b:	48 89 4e 30          	mov    QWORD PTR [rsi+0x30],rcx
 28f:	45 0f b6 dc          	movzx  r11d,r12b
 293:	4d 11 cb             	adc    r11,r9
 296:	c4 62 bb f6 4f 28    	mulx   r9,r8,QWORD PTR [rdi+0x28]
 29c:	0f b6 54 24 20       	movzx  edx,BYTE PTR [rsp+0x20]
 2a1:	4d 01 da             	add    r10,r11
 2a4:	4d 89 c3             	mov    r11,r8
 2a7:	41 0f 92 c7          	setb   r15b
 2ab:	4d 01 d3             	add    r11,r10
 2ae:	4c 8b 54 24 10       	mov    r10,QWORD PTR [rsp+0x10]
 2b3:	40 0f 92 c7          	setb   dil
 2b7:	45 0f b6 ff          	movzx  r15d,r15b
 2bb:	4c 89 5e 38          	mov    QWORD PTR [rsi+0x38],r11
 2bf:	4d 8d 24 16          	lea    r12,[r14+rdx*1]
 2c3:	40 0f b6 ff          	movzx  edi,dil
 2c7:	41 83 e4 03          	and    r12d,0x3
 2cb:	4c 03 66 40          	add    r12,QWORD PTR [rsi+0x40]
 2cf:	0f 92 44 24 20       	setb   BYTE PTR [rsp+0x20]
 2d4:	4c 01 ff             	add    rdi,r15
 2d7:	4c 8b 3c 24          	mov    r15,QWORD PTR [rsp]
 2db:	4c 01 cf             	add    rdi,r9
 2de:	49 01 fc             	add    r12,rdi
 2e1:	0f 92 44 24 3f       	setb   BYTE PTR [rsp+0x3f]
 2e6:	4c 0f af d5          	imul   r10,rbp
 2ea:	4c 89 66 40          	mov    QWORD PTR [rsi+0x40],r12
 2ee:	48 83 c5 00          	add    rbp,0x0
 2f2:	4c 89 d2             	mov    rdx,r10
 2f5:	c4 42 bb f6 0f       	mulx   r9,r8,QWORD PTR [r15]
 2fa:	4c 01 c5             	add    rbp,r8
 2fd:	4c 89 cf             	mov    rdi,r9
 300:	4c 89 fd             	mov    rbp,r15
 303:	c4 42 8b f6 7f 08    	mulx   r15,r14,QWORD PTR [r15+0x8]
 309:	48 83 d7 00          	adc    rdi,0x0
 30d:	48 01 fb             	add    rbx,rdi
 310:	40 0f 92 c7          	setb   dil
 314:	4c 01 f3             	add    rbx,r14
 317:	44 0f b6 cf          	movzx  r9d,dil
 31b:	48 89 5e 20          	mov    QWORD PTR [rsi+0x20],rbx
 31f:	4d 11 f9             	adc    r9,r15
 322:	c4 62 8b f6 7d 10    	mulx   r15,r14,QWORD PTR [rbp+0x10]
 328:	4c 01 c8             	add    rax,r9
 32b:	4d 89 f1             	mov    r9,r14
 32e:	40 0f 92 c7          	setb   dil
 332:	49 01 c1             	add    r9,rax
 335:	40 0f b6 ff          	movzx  edi,dil
 339:	4c 89 4e 28          	mov    QWORD PTR [rsi+0x28],r9
 33d:	4c 11 ff             	adc    rdi,r15
 340:	c4 62 8b f6 7d 18    	mulx   r15,r14,QWORD PTR [rbp+0x18]
 346:	48 01 f9             	add    rcx,rdi
 349:	0f 92 c0             	setb   al
 34c:	4c 01 f1             	add    rcx,r14
 34f:	49 89 ee             	mov    r14,rbp
 352:	0f b6 f8             	movzx  edi,al
 355:	48 89 4e 30          	mov    QWORD PTR [rsi+0x30],rcx
 359:	4c 11 ff             	adc    rdi,r15
 35c:	c4 e2 fb f6 55 20    	mulx   rdx,rax,QWORD PTR [rbp+0x20]
 362:	44 0f b6 7c 24 3f    	movzx  r15d,BYTE PTR [rsp+0x3f]
 368:	4c 01 df             	add    rdi,r11
 36b:	41 0f 92 c0          	setb   r8b
 36f:	48 01 c7             	add    rdi,rax
 372:	41 0f b6 c0          	movzx  eax,r8b
 376:	48 89 7e 38          	mov    QWORD PTR [rsi+0x38],rdi
 37a:	48 11 d0             	adc    rax,rdx
 37d:	4c 89 d2             	mov    rdx,r10
 380:	4c 01 e0             	add    rax,r12
 383:	c4 62 a3 f6 65 28    	mulx   r12,r11,QWORD PTR [rbp+0x28]
 389:	0f b6 54 24 20       	movzx  edx,BYTE PTR [rsp+0x20]
 38e:	41 0f 92 c0          	setb   r8b
 392:	4c 01 d8             	add    rax,r11
 395:	41 0f 92 c2          	setb   r10b
 399:	45 0f b6 c0          	movzx  r8d,r8b
 39d:	48 89 46 40          	mov    QWORD PTR [rsi+0x40],rax
 3a1:	45 0f b6 d2          	movzx  r10d,r10b
 3a5:	49 8d 2c 17          	lea    rbp,[r15+rdx*1]
 3a9:	83 e5 03             	and    ebp,0x3
 3ac:	48 03 6e 48          	add    rbp,QWORD PTR [rsi+0x48]
 3b0:	0f 92 44 24 20       	setb   BYTE PTR [rsp+0x20]
 3b5:	4d 01 d0             	add    r8,r10
 3b8:	48 89 ea             	mov    rdx,rbp
 3bb:	4d 01 e0             	add    r8,r12
 3be:	4c 01 c2             	add    rdx,r8
 3c1:	0f 92 44 24 3f       	setb   BYTE PTR [rsp+0x3f]
 3c6:	4c 8b 44 24 10       	mov    r8,QWORD PTR [rsp+0x10]
 3cb:	48 89 56 48          	mov    QWORD PTR [rsi+0x48],rdx
 3cf:	48 89 14 24          	mov    QWORD PTR [rsp],rdx
 3d3:	4c 0f af c3          	imul   r8,rbx
 3d7:	48 83 c3 00          	add    rbx,0x0
 3db:	4c 89 c2             	mov    rdx,r8
 3de:	c4 42 a3 f6 26       	mulx   r12,r11,QWORD PTR [r14]
 3e3:	4c 01 db             	add    rbx,r11
 3e6:	c4 42 ab f6 5e 08    	mulx   r11,r10,QWORD PTR [r14+0x8]
 3ec:	49 83 d4 00          	adc    r12,0x0
 3f0:	4d 01 cc             	add    r12,r9
 3f3:	40 0f 92 c5          	setb   bpl
 3f7:	4d 01 d4             	add    r12,r10
 3fa:	44 0f b6 fd          	movzx  r15d,bpl
 3fe:	4c 89 66 28          	mov    QWORD PTR [rsi+0x28],r12
 402:	4c 89 f5             	mov    rbp,r14
 405:	4d 11 df             	adc    r15,r11
 408:	c4 42 ab f6 5e 10    	mulx   r11,r10,QWORD PTR [r14+0x10]
 40e:	48 89 eb             	mov    rbx,rbp
 411:	49 01 cf             	add    r15,rcx
 414:	41 0f 92 c1          	setb   r9b
 418:	4d 01 d7             	add    r15,r10
 41b:	45 0f b6 f1          	movzx  r14d,r9b
 41f:	4c 89 7e 30          	mov    QWORD PTR [rsi+0x30],r15
 423:	4d 11 de             	adc    r14,r11
 426:	c4 62 ab f6 5d 18    	mulx   r11,r10,QWORD PTR [rbp+0x18]
 42c:	49 01 fe             	add    r14,rdi
 42f:	41 0f 92 c1          	setb   r9b
 433:	4d 01 d6             	add    r14,r10
 436:	49 89 da             	mov    r10,rbx
 439:	41 0f b6 e9          	movzx  ebp,r9b
 43d:	4c 89 76 38          	mov    QWORD PTR [rsi+0x38],r14
 441:	4c 11 dd             	adc    rbp,r11
 444:	c4 e2 f3 f6 5b 20    	mulx   rbx,rcx,QWORD PTR [rbx+0x20]
 44a:	48 01 c5             	add    rbp,rax
 44d:	40 0f 92 c7          	setb   dil
 451:	48 01 cd             	add    rbp,rcx
 454:	48 89 6e 40          	mov    QWORD PTR [rsi+0x40],rbp
 458:	40 0f b6 c7          	movzx  eax,dil
 45c:	48 11 d8             	adc    rax,rbx
 45f:	c4 c2 f3 f6 5a 28    	mulx   rbx,rcx,QWORD PTR [r10+0x28]
 465:	48 03 04 24          	add    rax,QWORD PTR [rsp]
 469:	4c 89 14 24          	mov    QWORD PTR [rsp],r10
 46d:	0f b6 54 24 20       	movzx  edx,BYTE PTR [rsp+0x20]
 472:	48 89 5c 24 48       	mov    QWORD PTR [rsp+0x48],rbx
 477:	48 89 4c 24 40       	mov    QWORD PTR [rsp+0x40],rcx
 47c:	0f b6 5c 24 3f       	movzx  ebx,BYTE PTR [rsp+0x3f]
 481:	4c 8b 4c 24 48       	mov    r9,QWORD PTR [rsp+0x48]
 486:	40 0f 92 c7          	setb   dil
 48a:	48 01 c8             	add    rax,rcx
 48d:	41 0f 92 c0          	setb   r8b
 491:	40 0f b6 ff          	movzx  edi,dil
 495:	48 89 46 48          	mov    QWORD PTR [rsi+0x48],rax
 499:	48 8d 0c 13          	lea    rcx,[rbx+rdx*1]
 49d:	45 0f b6 c0          	movzx  r8d,r8b
 4a1:	83 e1 03             	and    ecx,0x3
 4a4:	48 03 4e 50          	add    rcx,QWORD PTR [rsi+0x50]
 4a8:	41 0f 92 c2          	setb   r10b
 4ac:	4c 01 c7             	add    rdi,r8
 4af:	4c 01 cf             	add    rdi,r9
 4b2:	48 01 f9             	add    rcx,rdi
 4b5:	48 8b 7c 24 10       	mov    rdi,QWORD PTR [rsp+0x10]
 4ba:	41 0f 92 c3          	setb   r11b
 4be:	48 89 4e 50          	mov    QWORD PTR [rsi+0x50],rcx
 4c2:	4c 8b 0c 24          	mov    r9,QWORD PTR [rsp]
 4c6:	49 0f af fc          	imul   rdi,r12
 4ca:	49 83 c4 00          	add    r12,0x0
 4ce:	48 89 fa             	mov    rdx,rdi
 4d1:	c4 42 bb f6 09       	mulx   r9,r8,QWORD PTR [r9]
 4d6:	4c 89 4c 24 18       	mov    QWORD PTR [rsp+0x18],r9
 4db:	48 8b 5c 24 18       	mov    rbx,QWORD PTR [rsp+0x18]
 4e0:	4c 8b 0c 24          	mov    r9,QWORD PTR [rsp]
 4e4:	4d 01 c4             	add    r12,r8
 4e7:	48 83 d3 00          	adc    rbx,0x0
 4eb:	c4 42 bb f6 49 08    	mulx   r9,r8,QWORD PTR [r9+0x8]
 4f1:	4c 01 fb             	add    rbx,r15
 4f4:	4c 89 4c 24 18       	mov    QWORD PTR [rsp+0x18],r9
 4f9:	41 0f 92 c7          	setb   r15b
 4fd:	4c 01 c3             	add    rbx,r8
 500:	4c 8b 44 24 18       	mov    r8,QWORD PTR [rsp+0x18]
 505:	45 0f b6 e7          	movzx  r12d,r15b
 509:	48 89 5e 30          	mov    QWORD PTR [rsi+0x30],rbx
 50d:	4d 11 c4             	adc    r12,r8
 510:	4d 01 f4             	add    r12,r14
 513:	4c 8b 34 24          	mov    r14,QWORD PTR [rsp]
 517:	41 0f 92 c7          	setb   r15b
 51b:	c4 42 bb f6 4e 10    	mulx   r9,r8,QWORD PTR [r14+0x10]
 521:	4c 89 4c 24 18       	mov    QWORD PTR [rsp+0x18],r9
 526:	4c 8b 4c 24 18       	mov    r9,QWORD PTR [rsp+0x18]
 52b:	4d 01 c4             	add    r12,r8
 52e:	4c 89 44 24 10       	mov    QWORD PTR [rsp+0x10],r8
 533:	45 0f b6 c7          	movzx  r8d,r15b
 537:	4c 89 66 38          	mov    QWORD PTR [rsi+0x38],r12
 53b:	4c 8b 3c 24          	mov    r15,QWORD PTR [rsp]
 53f:	4d 11 c8             	adc    r8,r9
 542:	4c 01 c5             	add    rbp,r8
 545:	c4 42 bb f6 4f 18    	mulx   r9,r8,QWORD PTR [r15+0x18]
 54b:	41 0f 92 c6          	setb   r14b
 54f:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
 554:	4c 8b 4c 24 08       	mov    r9,QWORD PTR [rsp+0x8]
 559:	4c 01 c5             	add    rbp,r8
 55c:	45 0f b6 c6          	movzx  r8d,r14b
 560:	48 89 6e 40          	mov    QWORD PTR [rsi+0x40],rbp
 564:	4d 11 c8             	adc    r8,r9
 567:	4c 01 c0             	add    rax,r8
 56a:	c4 42 bb f6 4f 20    	mulx   r9,r8,QWORD PTR [r15+0x20]
 570:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
 575:	4c 8b 4c 24 08       	mov    r9,QWORD PTR [rsp+0x8]
 57a:	41 0f 92 c6          	setb   r14b
 57e:	4c 89 04 24          	mov    QWORD PTR [rsp],r8
 582:	4c 01 c0             	add    rax,r8
 585:	45 0f b6 c6          	movzx  r8d,r14b
 589:	48 89 46 48          	mov    QWORD PTR [rsi+0x48],rax
 58d:	4d 11 c8             	adc    r8,r9
 590:	4c 01 c1             	add    rcx,r8
 593:	48 89 4c 24 50       	mov    QWORD PTR [rsp+0x50],rcx
 598:	41 0f 92 c6          	setb   r14b
 59c:	c4 42 bb f6 4f 28    	mulx   r9,r8,QWORD PTR [r15+0x28]
 5a2:	4b 8d 14 13          	lea    rdx,[r11+r10*1]
 5a6:	45 0f b6 f6          	movzx  r14d,r14b
 5aa:	4c 01 c1             	add    rcx,r8
 5ad:	40 0f 92 c7          	setb   dil
 5b1:	83 e2 03             	and    edx,0x3
 5b4:	48 03 56 58          	add    rdx,QWORD PTR [rsi+0x58]
 5b8:	48 89 4e 50          	mov    QWORD PTR [rsi+0x50],rcx
 5bc:	40 0f b6 ff          	movzx  edi,dil
 5c0:	4c 01 f7             	add    rdi,r14
 5c3:	4c 01 cf             	add    rdi,r9
 5c6:	48 01 fa             	add    rdx,rdi
 5c9:	48 89 56 58          	mov    QWORD PTR [rsi+0x58],rdx
 5cd:	49 8b 7d 00          	mov    rdi,QWORD PTR [r13+0x0]
 5d1:	48 89 54 24 58       	mov    QWORD PTR [rsp+0x58],rdx
 5d6:	48 29 df             	sub    rdi,rbx
 5d9:	48 89 7c 24 60       	mov    QWORD PTR [rsp+0x60],rdi
 5de:	49 8b 7d 08          	mov    rdi,QWORD PTR [r13+0x8]
 5e2:	41 0f 92 c0          	setb   r8b
 5e6:	41 80 c0 ff          	add    r8b,0xff
 5ea:	4c 19 e7             	sbb    rdi,r12
 5ed:	48 89 7c 24 68       	mov    QWORD PTR [rsp+0x68],rdi
 5f2:	49 8b 7d 10          	mov    rdi,QWORD PTR [r13+0x10]
 5f6:	41 0f 92 c0          	setb   r8b
 5fa:	41 80 c0 ff          	add    r8b,0xff
 5fe:	48 19 ef             	sbb    rdi,rbp
 601:	48 89 7c 24 70       	mov    QWORD PTR [rsp+0x70],rdi
 606:	49 8b 7d 18          	mov    rdi,QWORD PTR [r13+0x18]
 60a:	41 0f 92 c0          	setb   r8b
 60e:	41 80 c0 ff          	add    r8b,0xff
 612:	48 19 c7             	sbb    rdi,rax
 615:	49 8b 45 20          	mov    rax,QWORD PTR [r13+0x20]
 619:	41 0f 92 c0          	setb   r8b
 61d:	48 89 7c 24 78       	mov    QWORD PTR [rsp+0x78],rdi
 622:	41 80 c0 ff          	add    r8b,0xff
 626:	48 19 c8             	sbb    rax,rcx
 629:	48 89 84 24 80 00 00 00 	mov    QWORD PTR [rsp+0x80],rax
 631:	49 8b 45 28          	mov    rax,QWORD PTR [r13+0x28]
 635:	0f 92 c1             	setb   cl
 638:	80 c1 ff             	add    cl,0xff
 63b:	48 19 d0             	sbb    rax,rdx
 63e:	48 89 84 24 88 00 00 00 	mov    QWORD PTR [rsp+0x88],rax
 646:	31 c0                	xor    eax,eax
 648:	48 8b 5c 06 58       	mov    rbx,QWORD PTR [rsi+rax*1+0x58]
 64d:	49 39 5c 05 28       	cmp    QWORD PTR [r13+rax*1+0x28],rbx
 652:	72 31                	jb     685 <mont_384(unsigned long long*, unsigned long long*, unsigned long long const*, unsigned long long)+0x685>
 654:	48 83 e8 08          	sub    rax,0x8
 658:	48 83 f8 d0          	cmp    rax,0xffffffffffffffd0
 65c:	75 ea                	jne    648 <mont_384(unsigned long long*, unsigned long long*, unsigned long long const*, unsigned long long)+0x648>
 65e:	c5 f9 6f 44 24 60    	vmovdqa xmm0,XMMWORD PTR [rsp+0x60]
 664:	c5 f9 6f 4c 24 70    	vmovdqa xmm1,XMMWORD PTR [rsp+0x70]
 66a:	c5 f9 6f 94 24 80 00 00 00 	vmovdqa xmm2,XMMWORD PTR [rsp+0x80]
 673:	c4 c1 7a 7f 45 00    	vmovdqu XMMWORD PTR [r13+0x0],xmm0
 679:	c4 c1 7a 7f 4d 10    	vmovdqu XMMWORD PTR [r13+0x10],xmm1
 67f:	c4 c1 7a 7f 55 20    	vmovdqu XMMWORD PTR [r13+0x20],xmm2
 685:	48 8b 84 24 98 00 00 00 	mov    rax,QWORD PTR [rsp+0x98]
 68d:	64 48 2b 04 25 28 00 00 00 	sub    rax,QWORD PTR fs:0x28
 696:	75 12                	jne    6aa <mont_384(unsigned long long*, unsigned long long*, unsigned long long const*, unsigned long long)+0x6aa>
 698:	48 81 c4 a8 00 00 00 	add    rsp,0xa8
 69f:	5b                   	pop    rbx
 6a0:	5d                   	pop    rbp
 6a1:	41 5c                	pop    r12
 6a3:	41 5d                	pop    r13
 6a5:	41 5e                	pop    r14
 6a7:	41 5f                	pop    r15
 6a9:	c3                   	ret    
 6aa:	e8 00 00 00 00       	call   6af <mont_384(unsigned long long*, unsigned long long*, unsigned long long const*, unsigned long long)+0x6af>	6ab: R_X86_64_PLT32	__stack_chk_fail-0x4

Disassembly of section .text.mulx_mont_384:

0000000000000000 <mulx_mont_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	41 57                	push   r15
   6:	41 56                	push   r14
   8:	49 89 f1             	mov    r9,rsi
   b:	48 89 d6             	mov    rsi,rdx
   e:	41 55                	push   r13
  10:	41 54                	push   r12
  12:	55                   	push   rbp
  13:	53                   	push   rbx
  14:	48 81 ec d8 00 00 00 	sub    rsp,0xd8
  1b:	48 8b 5e 08          	mov    rbx,QWORD PTR [rsi+0x8]
  1f:	48 89 7c 24 38       	mov    QWORD PTR [rsp+0x38],rdi
  24:	48 89 4c 24 40       	mov    QWORD PTR [rsp+0x40],rcx
  29:	4c 89 44 24 48       	mov    QWORD PTR [rsp+0x48],r8
  2e:	64 48 8b 04 25 28 00 00 00 	mov    rax,QWORD PTR fs:0x28
  37:	48 89 84 24 c8 00 00 00 	mov    QWORD PTR [rsp+0xc8],rax
  3f:	48 8b 02             	mov    rax,QWORD PTR [rdx]
  42:	48 89 5c 24 08       	mov    QWORD PTR [rsp+0x8],rbx
  47:	48 89 c2             	mov    rdx,rax
  4a:	48 89 04 24          	mov    QWORD PTR [rsp],rax
  4e:	31 c0                	xor    eax,eax
  50:	c4 42 a3 f6 21       	mulx   r12,r11,QWORD PTR [r9]
  55:	48 89 da             	mov    rdx,rbx
  58:	4c 89 d9             	mov    rcx,r11
  5b:	4c 8b 5e 10          	mov    r11,QWORD PTR [rsi+0x10]
  5f:	c4 42 8b f6 39       	mulx   r15,r14,QWORD PTR [r9]
  64:	4d 89 e0             	mov    r8,r12
  67:	48 01 c1             	add    rcx,rax
  6a:	4d 01 f0             	add    r8,r14
  6d:	41 0f 92 c5          	setb   r13b
  71:	48 89 4c 24 60       	mov    QWORD PTR [rsp+0x60],rcx
  76:	4c 89 da             	mov    rdx,r11
  79:	4c 89 5c 24 10       	mov    QWORD PTR [rsp+0x10],r11
  7e:	c4 42 ab f6 19       	mulx   r11,r10,QWORD PTR [r9]
  83:	41 0f b6 d5          	movzx  edx,r13b
  87:	4e 8d 2c 3a          	lea    r13,[rdx+r15*1]
  8b:	4c 8b 7e 18          	mov    r15,QWORD PTR [rsi+0x18]
  8f:	4d 01 d5             	add    r13,r10
  92:	41 0f 92 c6          	setb   r14b
  96:	4c 89 fa             	mov    rdx,r15
  99:	4c 89 7c 24 18       	mov    QWORD PTR [rsp+0x18],r15
  9e:	c4 c2 eb f6 09       	mulx   rcx,rdx,QWORD PTR [r9]
  a3:	48 89 4c 24 28       	mov    QWORD PTR [rsp+0x28],rcx
  a8:	48 89 d1             	mov    rcx,rdx
  ab:	41 0f b6 d6          	movzx  edx,r14b
  af:	4c 8b 76 20          	mov    r14,QWORD PTR [rsi+0x20]
  b3:	4e 8d 3c 1a          	lea    r15,[rdx+r11*1]
  b7:	49 01 cf             	add    r15,rcx
  ba:	0f 92 c1             	setb   cl
  bd:	4c 89 f2             	mov    rdx,r14
  c0:	4c 89 74 24 30       	mov    QWORD PTR [rsp+0x30],r14
  c5:	0f b6 c9             	movzx  ecx,cl
  c8:	c4 42 ab f6 19       	mulx   r11,r10,QWORD PTR [r9]
  cd:	48 8b 54 24 28       	mov    rdx,QWORD PTR [rsp+0x28]
  d2:	48 8b 5e 28          	mov    rbx,QWORD PTR [rsi+0x28]
  d6:	48 8d 2c 11          	lea    rbp,[rcx+rdx*1]
  da:	4c 01 d5             	add    rbp,r10
  dd:	48 89 da             	mov    rdx,rbx
  e0:	41 0f 92 c4          	setb   r12b
  e4:	c4 c2 cb f6 39       	mulx   rdi,rsi,QWORD PTR [r9]
  e9:	41 0f b6 d4          	movzx  edx,r12b
  ed:	48 89 7c 24 28       	mov    QWORD PTR [rsp+0x28],rdi
  f2:	48 8b 4c 24 28       	mov    rcx,QWORD PTR [rsp+0x28]
  f7:	4e 8d 24 1a          	lea    r12,[rdx+r11*1]
  fb:	4d 8b 59 08          	mov    r11,QWORD PTR [r9+0x8]
  ff:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 103:	49 01 f4             	add    r12,rsi
 106:	48 83 d1 00          	adc    rcx,0x0
 10a:	49 01 c0             	add    r8,rax
 10d:	c4 c2 cb f6 fb       	mulx   rdi,rsi,r11
 112:	49 01 f0             	add    r8,rsi
 115:	48 89 fa             	mov    rdx,rdi
 118:	48 83 d2 00          	adc    rdx,0x0
 11c:	4c 89 44 24 68       	mov    QWORD PTR [rsp+0x68],r8
 121:	49 01 d5             	add    r13,rdx
 124:	48 8b 54 24 08       	mov    rdx,QWORD PTR [rsp+0x8]
 129:	41 0f 92 c2          	setb   r10b
 12d:	45 0f b6 f2          	movzx  r14d,r10b
 131:	c4 c2 cb f6 fb       	mulx   rdi,rsi,r11
 136:	48 8b 54 24 10       	mov    rdx,QWORD PTR [rsp+0x10]
 13b:	49 01 f5             	add    r13,rsi
 13e:	48 89 7c 24 28       	mov    QWORD PTR [rsp+0x28],rdi
 143:	48 8b 74 24 28       	mov    rsi,QWORD PTR [rsp+0x28]
 148:	49 11 f6             	adc    r14,rsi
 14b:	c4 c2 cb f6 fb       	mulx   rdi,rsi,r11
 150:	4d 01 fe             	add    r14,r15
 153:	41 0f 92 c0          	setb   r8b
 157:	49 01 f6             	add    r14,rsi
 15a:	41 0f b6 d0          	movzx  edx,r8b
 15e:	48 11 fa             	adc    rdx,rdi
 161:	49 89 d2             	mov    r10,rdx
 164:	48 8b 54 24 18       	mov    rdx,QWORD PTR [rsp+0x18]
 169:	49 01 ea             	add    r10,rbp
 16c:	41 0f 92 c0          	setb   r8b
 170:	c4 c2 c3 f6 eb       	mulx   rbp,rdi,r11
 175:	48 8b 54 24 30       	mov    rdx,QWORD PTR [rsp+0x30]
 17a:	49 01 fa             	add    r10,rdi
 17d:	4c 89 54 24 20       	mov    QWORD PTR [rsp+0x20],r10
 182:	45 0f b6 d0          	movzx  r10d,r8b
 186:	49 11 ea             	adc    r10,rbp
 189:	4d 01 e2             	add    r10,r12
 18c:	c4 c2 cb f6 fb       	mulx   rdi,rsi,r11
 191:	48 89 da             	mov    rdx,rbx
 194:	40 0f 92 c5          	setb   bpl
 198:	49 01 f2             	add    r10,rsi
 19b:	44 0f b6 c5          	movzx  r8d,bpl
 19f:	49 11 f8             	adc    r8,rdi
 1a2:	c4 c2 cb f6 fb       	mulx   rdi,rsi,r11
 1a7:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 1ab:	49 01 c8             	add    r8,rcx
 1ae:	41 0f 92 c4          	setb   r12b
 1b2:	49 01 f0             	add    r8,rsi
 1b5:	41 0f b6 cc          	movzx  ecx,r12b
 1b9:	4d 8b 61 10          	mov    r12,QWORD PTR [r9+0x10]
 1bd:	48 11 f9             	adc    rcx,rdi
 1c0:	49 01 c5             	add    r13,rax
 1c3:	c4 c2 c3 f6 ec       	mulx   rbp,rdi,r12
 1c8:	48 8b 54 24 08       	mov    rdx,QWORD PTR [rsp+0x8]
 1cd:	49 01 fd             	add    r13,rdi
 1d0:	48 89 ee             	mov    rsi,rbp
 1d3:	48 83 d6 00          	adc    rsi,0x0
 1d7:	4c 89 6c 24 70       	mov    QWORD PTR [rsp+0x70],r13
 1dc:	4c 8b 6c 24 20       	mov    r13,QWORD PTR [rsp+0x20]
 1e1:	49 01 f6             	add    r14,rsi
 1e4:	c4 c2 c3 f6 ec       	mulx   rbp,rdi,r12
 1e9:	41 0f 92 c3          	setb   r11b
 1ed:	48 8b 54 24 10       	mov    rdx,QWORD PTR [rsp+0x10]
 1f2:	49 01 fe             	add    r14,rdi
 1f5:	45 0f b6 db          	movzx  r11d,r11b
 1f9:	49 11 eb             	adc    r11,rbp
 1fc:	4d 01 dd             	add    r13,r11
 1ff:	c4 c2 c3 f6 ec       	mulx   rbp,rdi,r12
 204:	41 0f 92 c3          	setb   r11b
 208:	48 8b 54 24 18       	mov    rdx,QWORD PTR [rsp+0x18]
 20d:	49 01 fd             	add    r13,rdi
 210:	45 0f b6 fb          	movzx  r15d,r11b
 214:	49 11 ef             	adc    r15,rbp
 217:	4c 89 6c 24 20       	mov    QWORD PTR [rsp+0x20],r13
 21c:	4d 01 d7             	add    r15,r10
 21f:	40 0f 92 c6          	setb   sil
 223:	c4 42 ab f6 dc       	mulx   r11,r10,r12
 228:	48 8b 54 24 30       	mov    rdx,QWORD PTR [rsp+0x30]
 22d:	4d 01 d7             	add    r15,r10
 230:	40 0f b6 ee          	movzx  ebp,sil
 234:	4c 11 dd             	adc    rbp,r11
 237:	4c 01 c5             	add    rbp,r8
 23a:	c4 42 ab f6 dc       	mulx   r11,r10,r12
 23f:	41 0f 92 c5          	setb   r13b
 243:	48 89 da             	mov    rdx,rbx
 246:	4c 01 d5             	add    rbp,r10
 249:	4c 89 df             	mov    rdi,r11
 24c:	4d 8b 51 18          	mov    r10,QWORD PTR [r9+0x18]
 250:	45 0f b6 dd          	movzx  r11d,r13b
 254:	c4 42 9b f6 ec       	mulx   r13,r12,r12
 259:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 25d:	49 11 fb             	adc    r11,rdi
 260:	49 01 cb             	add    r11,rcx
 263:	40 0f 92 c7          	setb   dil
 267:	4d 01 e3             	add    r11,r12
 26a:	4c 8b 64 24 20       	mov    r12,QWORD PTR [rsp+0x20]
 26f:	44 0f b6 c7          	movzx  r8d,dil
 273:	c4 c2 cb f6 fa       	mulx   rdi,rsi,r10
 278:	48 8b 54 24 08       	mov    rdx,QWORD PTR [rsp+0x8]
 27d:	4d 11 e8             	adc    r8,r13
 280:	49 01 c6             	add    r14,rax
 283:	49 01 f6             	add    r14,rsi
 286:	48 89 f9             	mov    rcx,rdi
 289:	48 83 d1 00          	adc    rcx,0x0
 28d:	4c 89 74 24 78       	mov    QWORD PTR [rsp+0x78],r14
 292:	49 01 cc             	add    r12,rcx
 295:	c4 42 93 f6 f2       	mulx   r14,r13,r10
 29a:	0f 92 c1             	setb   cl
 29d:	4d 01 ec             	add    r12,r13
 2a0:	4c 89 64 24 20       	mov    QWORD PTR [rsp+0x20],r12
 2a5:	48 8b 54 24 10       	mov    rdx,QWORD PTR [rsp+0x10]
 2aa:	44 0f b6 e1          	movzx  r12d,cl
 2ae:	4d 11 f4             	adc    r12,r14
 2b1:	4d 01 fc             	add    r12,r15
 2b4:	0f 92 c1             	setb   cl
 2b7:	c4 42 8b f6 fa       	mulx   r15,r14,r10
 2bc:	48 8b 54 24 18       	mov    rdx,QWORD PTR [rsp+0x18]
 2c1:	0f b6 f9             	movzx  edi,cl
 2c4:	4d 01 f4             	add    r12,r14
 2c7:	4c 11 ff             	adc    rdi,r15
 2ca:	48 01 ef             	add    rdi,rbp
 2cd:	c4 42 8b f6 fa       	mulx   r15,r14,r10
 2d2:	0f 92 c1             	setb   cl
 2d5:	48 8b 54 24 30       	mov    rdx,QWORD PTR [rsp+0x30]
 2da:	4c 01 f7             	add    rdi,r14
 2dd:	0f b6 f1             	movzx  esi,cl
 2e0:	4c 11 fe             	adc    rsi,r15
 2e3:	4c 01 de             	add    rsi,r11
 2e6:	c4 42 8b f6 fa       	mulx   r15,r14,r10
 2eb:	40 0f 92 c5          	setb   bpl
 2ef:	48 89 da             	mov    rdx,rbx
 2f2:	4c 01 f6             	add    rsi,r14
 2f5:	40 0f b6 cd          	movzx  ecx,bpl
 2f9:	c4 42 ab f6 da       	mulx   r11,r10,r10
 2fe:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 302:	4c 11 f9             	adc    rcx,r15
 305:	4c 01 c1             	add    rcx,r8
 308:	4d 8b 41 20          	mov    r8,QWORD PTR [r9+0x20]
 30c:	41 0f 92 c5          	setb   r13b
 310:	4c 01 d1             	add    rcx,r10
 313:	41 0f b6 ed          	movzx  ebp,r13b
 317:	4c 11 dd             	adc    rbp,r11
 31a:	4c 8b 5c 24 20       	mov    r11,QWORD PTR [rsp+0x20]
 31f:	c4 42 93 f6 f0       	mulx   r14,r13,r8
 324:	4c 89 f2             	mov    rdx,r14
 327:	49 01 c3             	add    r11,rax
 32a:	4d 01 eb             	add    r11,r13
 32d:	48 83 d2 00          	adc    rdx,0x0
 331:	4c 89 9c 24 80 00 00 00 	mov    QWORD PTR [rsp+0x80],r11
 339:	49 01 d4             	add    r12,rdx
 33c:	48 8b 54 24 08       	mov    rdx,QWORD PTR [rsp+0x8]
 341:	41 0f 92 c3          	setb   r11b
 345:	c4 42 93 f6 f0       	mulx   r14,r13,r8
 34a:	41 0f b6 d3          	movzx  edx,r11b
 34e:	4d 01 ec             	add    r12,r13
 351:	4c 11 f2             	adc    rdx,r14
 354:	48 01 d7             	add    rdi,rdx
 357:	48 8b 54 24 10       	mov    rdx,QWORD PTR [rsp+0x10]
 35c:	41 0f 92 c7          	setb   r15b
 360:	c4 42 93 f6 f0       	mulx   r14,r13,r8
 365:	41 0f b6 d7          	movzx  edx,r15b
 369:	4c 01 ef             	add    rdi,r13
 36c:	4c 11 f2             	adc    rdx,r14
 36f:	48 01 d6             	add    rsi,rdx
 372:	48 8b 54 24 18       	mov    rdx,QWORD PTR [rsp+0x18]
 377:	41 0f 92 c3          	setb   r11b
 37b:	c4 42 93 f6 f0       	mulx   r14,r13,r8
 380:	41 0f b6 d3          	movzx  edx,r11b
 384:	4c 01 ee             	add    rsi,r13
 387:	4c 11 f2             	adc    rdx,r14
 38a:	48 01 d1             	add    rcx,rdx
 38d:	48 8b 54 24 30       	mov    rdx,QWORD PTR [rsp+0x30]
 392:	41 0f 92 c3          	setb   r11b
 396:	c4 42 93 f6 f0       	mulx   r14,r13,r8
 39b:	41 0f b6 d3          	movzx  edx,r11b
 39f:	4c 01 e9             	add    rcx,r13
 3a2:	4c 11 f2             	adc    rdx,r14
 3a5:	48 01 d5             	add    rbp,rdx
 3a8:	48 89 da             	mov    rdx,rbx
 3ab:	41 0f 92 c5          	setb   r13b
 3af:	c4 42 ab f6 d8       	mulx   r11,r10,r8
 3b4:	41 0f b6 d5          	movzx  edx,r13b
 3b8:	4c 01 d5             	add    rbp,r10
 3bb:	4d 8b 51 28          	mov    r10,QWORD PTR [r9+0x28]
 3bf:	49 89 d7             	mov    r15,rdx
 3c2:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 3c6:	4d 11 df             	adc    r15,r11
 3c9:	49 01 c4             	add    r12,rax
 3cc:	c4 42 bb f6 ca       	mulx   r9,r8,r10
 3d1:	48 8b 54 24 08       	mov    rdx,QWORD PTR [rsp+0x8]
 3d6:	4d 01 c4             	add    r12,r8
 3d9:	4c 89 c8             	mov    rax,r9
 3dc:	48 83 d0 00          	adc    rax,0x0
 3e0:	4c 89 a4 24 88 00 00 00 	mov    QWORD PTR [rsp+0x88],r12
 3e8:	48 01 c7             	add    rdi,rax
 3eb:	c4 42 9b f6 ea       	mulx   r13,r12,r10
 3f0:	0f 92 c0             	setb   al
 3f3:	48 8b 54 24 10       	mov    rdx,QWORD PTR [rsp+0x10]
 3f8:	4c 01 e7             	add    rdi,r12
 3fb:	0f b6 c0             	movzx  eax,al
 3fe:	4c 11 e8             	adc    rax,r13
 401:	48 89 bc 24 90 00 00 00 	mov    QWORD PTR [rsp+0x90],rdi
 409:	48 01 c6             	add    rsi,rax
 40c:	c4 42 bb f6 ca       	mulx   r9,r8,r10
 411:	40 0f 92 c7          	setb   dil
 415:	48 8b 54 24 18       	mov    rdx,QWORD PTR [rsp+0x18]
 41a:	4c 01 c6             	add    rsi,r8
 41d:	40 0f b6 c7          	movzx  eax,dil
 421:	4c 11 c8             	adc    rax,r9
 424:	48 89 b4 24 98 00 00 00 	mov    QWORD PTR [rsp+0x98],rsi
 42c:	48 01 c1             	add    rcx,rax
 42f:	c4 c2 cb f6 fa       	mulx   rdi,rsi,r10
 434:	41 0f 92 c0          	setb   r8b
 438:	48 8b 54 24 30       	mov    rdx,QWORD PTR [rsp+0x30]
 43d:	48 01 f1             	add    rcx,rsi
 440:	41 0f b6 c0          	movzx  eax,r8b
 444:	48 11 f8             	adc    rax,rdi
 447:	48 89 8c 24 a0 00 00 00 	mov    QWORD PTR [rsp+0xa0],rcx
 44f:	48 01 c5             	add    rbp,rax
 452:	c4 c2 cb f6 fa       	mulx   rdi,rsi,r10
 457:	0f 92 c1             	setb   cl
 45a:	48 89 da             	mov    rdx,rbx
 45d:	48 01 f5             	add    rbp,rsi
 460:	0f b6 c1             	movzx  eax,cl
 463:	4c 89 fe             	mov    rsi,r15
 466:	c4 42 ab f6 da       	mulx   r11,r10,r10
 46b:	48 11 f8             	adc    rax,rdi
 46e:	48 8b 4c 24 48       	mov    rcx,QWORD PTR [rsp+0x48]
 473:	48 8b 54 24 40       	mov    rdx,QWORD PTR [rsp+0x40]
 478:	48 89 ac 24 a8 00 00 00 	mov    QWORD PTR [rsp+0xa8],rbp
 480:	48 01 c6             	add    rsi,rax
 483:	48 8b 7c 24 38       	mov    rdi,QWORD PTR [rsp+0x38]
 488:	0f 92 c0             	setb   al
 48b:	48 89 74 24 50       	mov    QWORD PTR [rsp+0x50],rsi
 490:	4c 01 d6             	add    rsi,r10
 493:	0f b6 c0             	movzx  eax,al
 496:	48 89 74 24 58       	mov    QWORD PTR [rsp+0x58],rsi
 49b:	48 89 b4 24 b0 00 00 00 	mov    QWORD PTR [rsp+0xb0],rsi
 4a3:	48 8d 74 24 60       	lea    rsi,[rsp+0x60]
 4a8:	4c 11 d8             	adc    rax,r11
 4ab:	48 89 84 24 b8 00 00 00 	mov    QWORD PTR [rsp+0xb8],rax
 4b3:	e8 00 00 00 00       	call   4b8 <mulx_mont_384+0x4b8>	4b4: R_X86_64_PLT32	mont_384(unsigned long long*, unsigned long long*, unsigned long long const*, unsigned long long)-0x4
 4b8:	48 8b 84 24 c8 00 00 00 	mov    rax,QWORD PTR [rsp+0xc8]
 4c0:	64 48 2b 04 25 28 00 00 00 	sub    rax,QWORD PTR fs:0x28
 4c9:	75 12                	jne    4dd <mulx_mont_384+0x4dd>
 4cb:	48 81 c4 d8 00 00 00 	add    rsp,0xd8
 4d2:	5b                   	pop    rbx
 4d3:	5d                   	pop    rbp
 4d4:	41 5c                	pop    r12
 4d6:	41 5d                	pop    r13
 4d8:	41 5e                	pop    r14
 4da:	41 5f                	pop    r15
 4dc:	c3                   	ret    
 4dd:	e8 00 00 00 00       	call   4e2 <mulx_mont_384+0x4e2>	4de: R_X86_64_PLT32	__stack_chk_fail-0x4

Disassembly of section .text.sqrx_mont_384:

0000000000000000 <sqrx_mont_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	41 57                	push   r15
   6:	41 56                	push   r14
   8:	41 55                	push   r13
   a:	41 54                	push   r12
   c:	55                   	push   rbp
   d:	53                   	push   rbx
   e:	48 81 ec f8 00 00 00 	sub    rsp,0xf8
  15:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
  19:	4c 8b 46 10          	mov    r8,QWORD PTR [rsi+0x10]
  1d:	48 89 54 24 38       	mov    QWORD PTR [rsp+0x38],rdx
  22:	48 89 7c 24 30       	mov    QWORD PTR [rsp+0x30],rdi
  27:	48 8b 7e 18          	mov    rdi,QWORD PTR [rsi+0x18]
  2b:	48 8b 5e 28          	mov    rbx,QWORD PTR [rsi+0x28]
  2f:	48 89 4c 24 40       	mov    QWORD PTR [rsp+0x40],rcx
  34:	48 8b 4e 20          	mov    rcx,QWORD PTR [rsi+0x20]
  38:	4c 89 ca             	mov    rdx,r9
  3b:	c4 62 a3 f6 26       	mulx   r12,r11,QWORD PTR [rsi]
  40:	4c 89 c2             	mov    rdx,r8
  43:	64 48 8b 04 25 28 00 00 00 	mov    rax,QWORD PTR fs:0x28
  4c:	48 89 84 24 e8 00 00 00 	mov    QWORD PTR [rsp+0xe8],rax
  54:	31 c0                	xor    eax,eax
  56:	c4 e2 fb f6 16       	mulx   rdx,rax,QWORD PTR [rsi]
  5b:	4d 89 e6             	mov    r14,r12
  5e:	4c 89 5c 24 18       	mov    QWORD PTR [rsp+0x18],r11
  63:	48 89 1c 24          	mov    QWORD PTR [rsp],rbx
  67:	48 89 54 24 08       	mov    QWORD PTR [rsp+0x8],rdx
  6c:	49 01 c6             	add    r14,rax
  6f:	48 89 fa             	mov    rdx,rdi
  72:	4c 8b 54 24 08       	mov    r10,QWORD PTR [rsp+0x8]
  77:	40 0f 92 c5          	setb   bpl
  7b:	4c 89 74 24 48       	mov    QWORD PTR [rsp+0x48],r14
  80:	c4 62 8b f6 3e       	mulx   r15,r14,QWORD PTR [rsi]
  85:	40 0f b6 c5          	movzx  eax,bpl
  89:	48 89 ca             	mov    rdx,rcx
  8c:	c4 62 9b f6 2e       	mulx   r13,r12,QWORD PTR [rsi]
  91:	48 89 da             	mov    rdx,rbx
  94:	4a 8d 2c 10          	lea    rbp,[rax+r10*1]
  98:	c4 62 ab f6 1e       	mulx   r11,r10,QWORD PTR [rsi]
  9d:	4c 89 c2             	mov    rdx,r8
  a0:	4c 01 f5             	add    rbp,r14
  a3:	4c 89 5c 24 28       	mov    QWORD PTR [rsp+0x28],r11
  a8:	0f 92 c0             	setb   al
  ab:	0f b6 c0             	movzx  eax,al
  ae:	4e 8d 34 38          	lea    r14,[rax+r15*1]
  b2:	4d 01 e6             	add    r14,r12
  b5:	0f 92 c0             	setb   al
  b8:	0f b6 c0             	movzx  eax,al
  bb:	4e 8d 24 28          	lea    r12,[rax+r13*1]
  bf:	4c 8b 6c 24 28       	mov    r13,QWORD PTR [rsp+0x28]
  c4:	4d 01 d4             	add    r12,r10
  c7:	c4 42 ab f6 d9       	mulx   r11,r10,r9
  cc:	48 89 fa             	mov    rdx,rdi
  cf:	49 83 d5 00          	adc    r13,0x0
  d3:	48 83 c5 00          	add    rbp,0x0
  d7:	4c 01 d5             	add    rbp,r10
  da:	48 89 6c 24 20       	mov    QWORD PTR [rsp+0x20],rbp
  df:	4c 89 dd             	mov    rbp,r11
  e2:	c4 42 ab f6 d9       	mulx   r11,r10,r9
  e7:	48 89 ca             	mov    rdx,rcx
  ea:	48 83 d5 00          	adc    rbp,0x0
  ee:	4c 01 f5             	add    rbp,r14
  f1:	0f 92 c0             	setb   al
  f4:	4c 01 d5             	add    rbp,r10
  f7:	0f b6 d8             	movzx  ebx,al
  fa:	48 89 6c 24 50       	mov    QWORD PTR [rsp+0x50],rbp
  ff:	4c 11 db             	adc    rbx,r11
 102:	c4 42 ab f6 d9       	mulx   r11,r10,r9
 107:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 10b:	49 01 dc             	add    r12,rbx
 10e:	4c 89 d3             	mov    rbx,r10
 111:	40 0f 92 c5          	setb   bpl
 115:	4c 01 e3             	add    rbx,r12
 118:	40 0f b6 ed          	movzx  ebp,bpl
 11c:	4c 11 dd             	adc    rbp,r11
 11f:	c4 42 ab f6 d9       	mulx   r11,r10,r9
 124:	48 89 fa             	mov    rdx,rdi
 127:	49 01 ed             	add    r13,rbp
 12a:	41 0f 92 c6          	setb   r14b
 12e:	4d 01 d5             	add    r13,r10
 131:	41 0f b6 ee          	movzx  ebp,r14b
 135:	c4 42 8b f6 f8       	mulx   r15,r14,r8
 13a:	48 89 ca             	mov    rdx,rcx
 13d:	4c 11 dd             	adc    rbp,r11
 140:	48 83 c3 00          	add    rbx,0x0
 144:	4c 89 f8             	mov    rax,r15
 147:	c4 42 ab f6 d8       	mulx   r11,r10,r8
 14c:	4c 01 f3             	add    rbx,r14
 14f:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 153:	48 83 d0 00          	adc    rax,0x0
 157:	49 01 c5             	add    r13,rax
 15a:	4c 89 d0             	mov    rax,r10
 15d:	41 0f 92 c6          	setb   r14b
 161:	4c 01 e8             	add    rax,r13
 164:	45 0f b6 f6          	movzx  r14d,r14b
 168:	4d 11 de             	adc    r14,r11
 16b:	c4 42 ab f6 d8       	mulx   r11,r10,r8
 170:	48 89 ca             	mov    rdx,rcx
 173:	4c 01 f5             	add    rbp,r14
 176:	4d 89 d4             	mov    r12,r10
 179:	41 0f 92 c6          	setb   r14b
 17d:	49 01 ec             	add    r12,rbp
 180:	41 0f b6 ee          	movzx  ebp,r14b
 184:	c4 62 8b f6 ff       	mulx   r15,r14,rdi
 189:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 18d:	49 89 ed             	mov    r13,rbp
 190:	4c 89 fd             	mov    rbp,r15
 193:	4d 11 dd             	adc    r13,r11
 196:	49 83 c4 00          	add    r12,0x0
 19a:	4d 01 f4             	add    r12,r14
 19d:	48 83 d5 00          	adc    rbp,0x0
 1a1:	c4 62 8b f6 ff       	mulx   r15,r14,rdi
 1a6:	4c 01 ed             	add    rbp,r13
 1a9:	41 0f 92 c5          	setb   r13b
 1ad:	4c 01 f5             	add    rbp,r14
 1b0:	45 0f b6 ed          	movzx  r13d,r13b
 1b4:	4d 11 fd             	adc    r13,r15
 1b7:	c4 62 8b f6 f9       	mulx   r15,r14,rcx
 1bc:	4d 89 f2             	mov    r10,r14
 1bf:	4d 89 fb             	mov    r11,r15
 1c2:	4c 8b 7c 24 50       	mov    r15,QWORD PTR [rsp+0x50]
 1c7:	4c 8b 74 24 48       	mov    r14,QWORD PTR [rsp+0x48]
 1cc:	4d 01 ea             	add    r10,r13
 1cf:	49 83 d3 00          	adc    r11,0x0
 1d3:	4d 89 dd             	mov    r13,r11
 1d6:	4d 01 db             	add    r11,r11
 1d9:	49 c1 ed 3f          	shr    r13,0x3f
 1dd:	4d 01 f6             	add    r14,r14
 1e0:	4c 89 6c 24 58       	mov    QWORD PTR [rsp+0x58],r13
 1e5:	4d 89 d5             	mov    r13,r10
 1e8:	4d 01 d2             	add    r10,r10
 1eb:	49 c1 ed 3f          	shr    r13,0x3f
 1ef:	4d 09 eb             	or     r11,r13
 1f2:	4c 89 5c 24 60       	mov    QWORD PTR [rsp+0x60],r11
 1f7:	49 89 eb             	mov    r11,rbp
 1fa:	49 c1 eb 3f          	shr    r11,0x3f
 1fe:	4d 09 da             	or     r10,r11
 201:	4c 8d 5c 2d 00       	lea    r11,[rbp+rbp*1+0x0]
 206:	48 89 c5             	mov    rbp,rax
 209:	48 01 c0             	add    rax,rax
 20c:	4c 89 54 24 68       	mov    QWORD PTR [rsp+0x68],r10
 211:	4d 89 e2             	mov    r10,r12
 214:	48 c1 ed 3f          	shr    rbp,0x3f
 218:	49 c1 ea 3f          	shr    r10,0x3f
 21c:	4d 09 d3             	or     r11,r10
 21f:	4f 8d 14 24          	lea    r10,[r12+r12*1]
 223:	4c 8b 64 24 20       	mov    r12,QWORD PTR [rsp+0x20]
 228:	49 09 ea             	or     r10,rbp
 22b:	48 89 dd             	mov    rbp,rbx
 22e:	48 01 db             	add    rbx,rbx
 231:	48 c1 ed 3f          	shr    rbp,0x3f
 235:	48 09 e8             	or     rax,rbp
 238:	4c 89 fd             	mov    rbp,r15
 23b:	48 c1 ed 3f          	shr    rbp,0x3f
 23f:	49 c1 ec 3f          	shr    r12,0x3f
 243:	48 09 eb             	or     rbx,rbp
 246:	4b 8d 2c 3f          	lea    rbp,[r15+r15*1]
 24a:	4c 8b 7c 24 18       	mov    r15,QWORD PTR [rsp+0x18]
 24f:	4c 09 e5             	or     rbp,r12
 252:	4d 89 fc             	mov    r12,r15
 255:	4d 01 ff             	add    r15,r15
 258:	49 c1 ec 3f          	shr    r12,0x3f
 25c:	4d 09 e6             	or     r14,r12
 25f:	4c 8b 26             	mov    r12,QWORD PTR [rsi]
 262:	4c 89 e2             	mov    rdx,r12
 265:	c4 42 9b f6 ec       	mulx   r13,r12,r12
 26a:	4c 89 ca             	mov    rdx,r9
 26d:	4c 89 e6             	mov    rsi,r12
 270:	48 83 c6 00          	add    rsi,0x0
 274:	48 89 b4 24 80 00 00 00 	mov    QWORD PTR [rsp+0x80],rsi
 27c:	4c 89 ee             	mov    rsi,r13
 27f:	4c 01 fe             	add    rsi,r15
 282:	41 0f 92 c4          	setb   r12b
 286:	48 89 b4 24 88 00 00 00 	mov    QWORD PTR [rsp+0x88],rsi
 28e:	45 0f b6 e4          	movzx  r12d,r12b
 292:	4d 01 e6             	add    r14,r12
 295:	c4 42 9b f6 e9       	mulx   r13,r12,r9
 29a:	4c 89 c2             	mov    rdx,r8
 29d:	41 0f 92 c7          	setb   r15b
 2a1:	4d 89 e1             	mov    r9,r12
 2a4:	4d 01 f1             	add    r9,r14
 2a7:	45 0f b6 ff          	movzx  r15d,r15b
 2ab:	4d 11 ef             	adc    r15,r13
 2ae:	4c 89 8c 24 90 00 00 00 	mov    QWORD PTR [rsp+0x90],r9
 2b6:	49 01 f7             	add    r15,rsi
 2b9:	40 0f 92 c6          	setb   sil
 2bd:	4c 89 bc 24 98 00 00 00 	mov    QWORD PTR [rsp+0x98],r15
 2c5:	c4 42 8b f6 f8       	mulx   r15,r14,r8
 2ca:	48 89 fa             	mov    rdx,rdi
 2cd:	40 0f b6 f6          	movzx  esi,sil
 2d1:	c4 62 bb f6 cf       	mulx   r9,r8,rdi
 2d6:	48 89 ca             	mov    rdx,rcx
 2d9:	48 01 f5             	add    rbp,rsi
 2dc:	40 0f 92 c6          	setb   sil
 2e0:	4c 01 f5             	add    rbp,r14
 2e3:	40 0f b6 f6          	movzx  esi,sil
 2e7:	48 89 ac 24 a0 00 00 00 	mov    QWORD PTR [rsp+0xa0],rbp
 2ef:	4c 11 fe             	adc    rsi,r15
 2f2:	48 01 f3             	add    rbx,rsi
 2f5:	40 0f 92 c6          	setb   sil
 2f9:	48 89 9c 24 a8 00 00 00 	mov    QWORD PTR [rsp+0xa8],rbx
 301:	c4 e2 f3 f6 d9       	mulx   rbx,rcx,rcx
 306:	48 8b 14 24          	mov    rdx,QWORD PTR [rsp]
 30a:	40 0f b6 f6          	movzx  esi,sil
 30e:	48 01 f0             	add    rax,rsi
 311:	40 0f 92 c6          	setb   sil
 315:	4c 01 c0             	add    rax,r8
 318:	48 89 84 24 b0 00 00 00 	mov    QWORD PTR [rsp+0xb0],rax
 320:	40 0f b6 c6          	movzx  eax,sil
 324:	4c 11 c8             	adc    rax,r9
 327:	4c 01 d0             	add    rax,r10
 32a:	48 89 84 24 b8 00 00 00 	mov    QWORD PTR [rsp+0xb8],rax
 332:	0f 92 c0             	setb   al
 335:	0f b6 c0             	movzx  eax,al
 338:	49 01 c3             	add    r11,rax
 33b:	40 0f 92 c6          	setb   sil
 33f:	49 01 cb             	add    r11,rcx
 342:	40 0f b6 c6          	movzx  eax,sil
 346:	c4 e2 cb f6 fa       	mulx   rdi,rsi,rdx
 34b:	4c 89 9c 24 c0 00 00 00 	mov    QWORD PTR [rsp+0xc0],r11
 353:	48 11 d8             	adc    rax,rbx
 356:	48 03 44 24 68       	add    rax,QWORD PTR [rsp+0x68]
 35b:	48 89 84 24 c8 00 00 00 	mov    QWORD PTR [rsp+0xc8],rax
 363:	0f 92 c0             	setb   al
 366:	0f b6 c0             	movzx  eax,al
 369:	48 03 44 24 60       	add    rax,QWORD PTR [rsp+0x60]
 36e:	0f 92 c1             	setb   cl
 371:	48 89 44 24 70       	mov    QWORD PTR [rsp+0x70],rax
 376:	48 01 f0             	add    rax,rsi
 379:	48 8d b4 24 80 00 00 00 	lea    rsi,[rsp+0x80]
 381:	48 89 84 24 d0 00 00 00 	mov    QWORD PTR [rsp+0xd0],rax
 389:	0f b6 c1             	movzx  eax,cl
 38c:	48 11 f8             	adc    rax,rdi
 38f:	48 03 44 24 58       	add    rax,QWORD PTR [rsp+0x58]
 394:	48 8b 4c 24 40       	mov    rcx,QWORD PTR [rsp+0x40]
 399:	48 8b 54 24 38       	mov    rdx,QWORD PTR [rsp+0x38]
 39e:	48 8b 7c 24 30       	mov    rdi,QWORD PTR [rsp+0x30]
 3a3:	48 89 44 24 78       	mov    QWORD PTR [rsp+0x78],rax
 3a8:	48 89 84 24 d8 00 00 00 	mov    QWORD PTR [rsp+0xd8],rax
 3b0:	e8 00 00 00 00       	call   3b5 <sqrx_mont_384+0x3b5>	3b1: R_X86_64_PLT32	mont_384(unsigned long long*, unsigned long long*, unsigned long long const*, unsigned long long)-0x4
 3b5:	48 8b 84 24 e8 00 00 00 	mov    rax,QWORD PTR [rsp+0xe8]
 3bd:	64 48 2b 04 25 28 00 00 00 	sub    rax,QWORD PTR fs:0x28
 3c6:	75 12                	jne    3da <sqrx_mont_384+0x3da>
 3c8:	48 81 c4 f8 00 00 00 	add    rsp,0xf8
 3cf:	5b                   	pop    rbx
 3d0:	5d                   	pop    rbp
 3d1:	41 5c                	pop    r12
 3d3:	41 5d                	pop    r13
 3d5:	41 5e                	pop    r14
 3d7:	41 5f                	pop    r15
 3d9:	c3                   	ret    
 3da:	e8 00 00 00 00       	call   3df <sqrx_mont_384+0x3df>	3db: R_X86_64_PLT32	__stack_chk_fail-0x4

Disassembly of section .text.add_mod_384:

0000000000000000 <add_mod_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	53                   	push   rbx
   5:	49 89 d3             	mov    r11,rdx
   8:	48 83 ec 40          	sub    rsp,0x40
   c:	4c 8b 12             	mov    r10,QWORD PTR [rdx]
   f:	64 48 8b 04 25 28 00 00 00 	mov    rax,QWORD PTR fs:0x28
  18:	48 89 44 24 38       	mov    QWORD PTR [rsp+0x38],rax
  1d:	31 c0                	xor    eax,eax
  1f:	4c 03 16             	add    r10,QWORD PTR [rsi]
  22:	0f 92 c0             	setb   al
  25:	4c 89 17             	mov    QWORD PTR [rdi],r10
  28:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
  2c:	04 ff                	add    al,0xff
  2e:	4c 13 4a 08          	adc    r9,QWORD PTR [rdx+0x8]
  32:	0f 92 c0             	setb   al
  35:	4c 89 4f 08          	mov    QWORD PTR [rdi+0x8],r9
  39:	4c 8b 46 10          	mov    r8,QWORD PTR [rsi+0x10]
  3d:	04 ff                	add    al,0xff
  3f:	4c 13 42 10          	adc    r8,QWORD PTR [rdx+0x10]
  43:	0f 92 c0             	setb   al
  46:	4c 89 47 10          	mov    QWORD PTR [rdi+0x10],r8
  4a:	48 8b 56 18          	mov    rdx,QWORD PTR [rsi+0x18]
  4e:	04 ff                	add    al,0xff
  50:	49 13 53 18          	adc    rdx,QWORD PTR [r11+0x18]
  54:	0f 92 c0             	setb   al
  57:	48 89 57 18          	mov    QWORD PTR [rdi+0x18],rdx
  5b:	04 ff                	add    al,0xff
  5d:	48 8b 46 20          	mov    rax,QWORD PTR [rsi+0x20]
  61:	49 13 43 20          	adc    rax,QWORD PTR [r11+0x20]
  65:	0f 92 c3             	setb   bl
  68:	48 89 47 20          	mov    QWORD PTR [rdi+0x20],rax
  6c:	4d 8b 5b 28          	mov    r11,QWORD PTR [r11+0x28]
  70:	80 c3 ff             	add    bl,0xff
  73:	4c 13 5e 28          	adc    r11,QWORD PTR [rsi+0x28]
  77:	4c 89 5f 28          	mov    QWORD PTR [rdi+0x28],r11
  7b:	4c 2b 11             	sub    r10,QWORD PTR [rcx]
  7e:	4c 89 de             	mov    rsi,r11
  81:	41 0f 92 c3          	setb   r11b
  85:	4c 89 14 24          	mov    QWORD PTR [rsp],r10
  89:	41 80 c3 ff          	add    r11b,0xff
  8d:	4c 1b 49 08          	sbb    r9,QWORD PTR [rcx+0x8]
  91:	41 0f 92 c2          	setb   r10b
  95:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
  9a:	41 80 c2 ff          	add    r10b,0xff
  9e:	4c 1b 41 10          	sbb    r8,QWORD PTR [rcx+0x10]
  a2:	41 0f 92 c1          	setb   r9b
  a6:	4c 89 44 24 10       	mov    QWORD PTR [rsp+0x10],r8
  ab:	41 80 c1 ff          	add    r9b,0xff
  af:	48 1b 51 18          	sbb    rdx,QWORD PTR [rcx+0x18]
  b3:	41 0f 92 c0          	setb   r8b
  b7:	48 89 54 24 18       	mov    QWORD PTR [rsp+0x18],rdx
  bc:	41 80 c0 ff          	add    r8b,0xff
  c0:	48 1b 41 20          	sbb    rax,QWORD PTR [rcx+0x20]
  c4:	0f 92 c2             	setb   dl
  c7:	48 89 44 24 20       	mov    QWORD PTR [rsp+0x20],rax
  cc:	b8 28 00 00 00       	mov    eax,0x28
  d1:	80 c2 ff             	add    dl,0xff
  d4:	48 1b 71 28          	sbb    rsi,QWORD PTR [rcx+0x28]
  d8:	48 89 74 24 28       	mov    QWORD PTR [rsp+0x28],rsi
  dd:	48 8b 1c 01          	mov    rbx,QWORD PTR [rcx+rax*1]
  e1:	48 39 1c 07          	cmp    QWORD PTR [rdi+rax*1],rbx
  e5:	72 29                	jb     110 <add_mod_384+0x110>
  e7:	48 83 e8 08          	sub    rax,0x8
  eb:	48 83 f8 f8          	cmp    rax,0xfffffffffffffff8
  ef:	75 ec                	jne    dd <add_mod_384+0xdd>
  f1:	c5 fa 6f 04 24       	vmovdqu xmm0,XMMWORD PTR [rsp]
  f6:	c5 fa 6f 4c 24 10    	vmovdqu xmm1,XMMWORD PTR [rsp+0x10]
  fc:	c5 fa 6f 54 24 20    	vmovdqu xmm2,XMMWORD PTR [rsp+0x20]
 102:	c5 fa 7f 07          	vmovdqu XMMWORD PTR [rdi],xmm0
 106:	c5 fa 7f 4f 10       	vmovdqu XMMWORD PTR [rdi+0x10],xmm1
 10b:	c5 fa 7f 57 20       	vmovdqu XMMWORD PTR [rdi+0x20],xmm2
 110:	48 8b 44 24 38       	mov    rax,QWORD PTR [rsp+0x38]
 115:	64 48 2b 04 25 28 00 00 00 	sub    rax,QWORD PTR fs:0x28
 11e:	75 06                	jne    126 <add_mod_384+0x126>
 120:	48 83 c4 40          	add    rsp,0x40
 124:	5b                   	pop    rbx
 125:	c3                   	ret    
 126:	e8 00 00 00 00       	call   12b <add_mod_384+0x12b>	127: R_X86_64_PLT32	__stack_chk_fail-0x4

Disassembly of section .text.sub_mod_384:

0000000000000000 <sub_mod_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	53                   	push   rbx
   5:	49 89 f3             	mov    r11,rsi
   8:	48 83 ec 40          	sub    rsp,0x40
   c:	4c 8b 16             	mov    r10,QWORD PTR [rsi]
   f:	64 48 8b 04 25 28 00 00 00 	mov    rax,QWORD PTR fs:0x28
  18:	48 89 44 24 38       	mov    QWORD PTR [rsp+0x38],rax
  1d:	31 c0                	xor    eax,eax
  1f:	4c 2b 12             	sub    r10,QWORD PTR [rdx]
  22:	0f 92 c0             	setb   al
  25:	4c 89 17             	mov    QWORD PTR [rdi],r10
  28:	4c 8b 4e 08          	mov    r9,QWORD PTR [rsi+0x8]
  2c:	04 ff                	add    al,0xff
  2e:	4c 1b 4a 08          	sbb    r9,QWORD PTR [rdx+0x8]
  32:	0f 92 c0             	setb   al
  35:	4c 89 4f 08          	mov    QWORD PTR [rdi+0x8],r9
  39:	4c 8b 46 10          	mov    r8,QWORD PTR [rsi+0x10]
  3d:	04 ff                	add    al,0xff
  3f:	4c 1b 42 10          	sbb    r8,QWORD PTR [rdx+0x10]
  43:	0f 92 c0             	setb   al
  46:	4c 89 47 10          	mov    QWORD PTR [rdi+0x10],r8
  4a:	48 8b 76 18          	mov    rsi,QWORD PTR [rsi+0x18]
  4e:	04 ff                	add    al,0xff
  50:	48 1b 72 18          	sbb    rsi,QWORD PTR [rdx+0x18]
  54:	0f 92 c3             	setb   bl
  57:	48 89 77 18          	mov    QWORD PTR [rdi+0x18],rsi
  5b:	49 8b 43 20          	mov    rax,QWORD PTR [r11+0x20]
  5f:	80 c3 ff             	add    bl,0xff
  62:	48 1b 42 20          	sbb    rax,QWORD PTR [rdx+0x20]
  66:	0f 92 c3             	setb   bl
  69:	48 89 47 20          	mov    QWORD PTR [rdi+0x20],rax
  6d:	4d 8b 5b 28          	mov    r11,QWORD PTR [r11+0x28]
  71:	80 c3 ff             	add    bl,0xff
  74:	4c 1b 5a 28          	sbb    r11,QWORD PTR [rdx+0x28]
  78:	4c 89 5f 28          	mov    QWORD PTR [rdi+0x28],r11
  7c:	4c 2b 11             	sub    r10,QWORD PTR [rcx]
  7f:	4c 89 da             	mov    rdx,r11
  82:	41 0f 92 c3          	setb   r11b
  86:	4c 89 14 24          	mov    QWORD PTR [rsp],r10
  8a:	41 80 c3 ff          	add    r11b,0xff
  8e:	4c 1b 49 08          	sbb    r9,QWORD PTR [rcx+0x8]
  92:	41 0f 92 c2          	setb   r10b
  96:	4c 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],r9
  9b:	41 80 c2 ff          	add    r10b,0xff
  9f:	4c 1b 41 10          	sbb    r8,QWORD PTR [rcx+0x10]
  a3:	41 0f 92 c1          	setb   r9b
  a7:	4c 89 44 24 10       	mov    QWORD PTR [rsp+0x10],r8
  ac:	41 80 c1 ff          	add    r9b,0xff
  b0:	48 1b 71 18          	sbb    rsi,QWORD PTR [rcx+0x18]
  b4:	41 0f 92 c0          	setb   r8b
  b8:	48 89 74 24 18       	mov    QWORD PTR [rsp+0x18],rsi
  bd:	41 80 c0 ff          	add    r8b,0xff
  c1:	48 1b 41 20          	sbb    rax,QWORD PTR [rcx+0x20]
  c5:	40 0f 92 c6          	setb   sil
  c9:	48 89 44 24 20       	mov    QWORD PTR [rsp+0x20],rax
  ce:	b8 28 00 00 00       	mov    eax,0x28
  d3:	40 80 c6 ff          	add    sil,0xff
  d7:	48 1b 51 28          	sbb    rdx,QWORD PTR [rcx+0x28]
  db:	48 89 54 24 28       	mov    QWORD PTR [rsp+0x28],rdx
  e0:	48 8b 1c 01          	mov    rbx,QWORD PTR [rcx+rax*1]
  e4:	48 39 1c 07          	cmp    QWORD PTR [rdi+rax*1],rbx
  e8:	72 29                	jb     113 <sub_mod_384+0x113>
  ea:	48 83 e8 08          	sub    rax,0x8
  ee:	48 83 f8 f8          	cmp    rax,0xfffffffffffffff8
  f2:	75 ec                	jne    e0 <sub_mod_384+0xe0>
  f4:	c5 fa 6f 04 24       	vmovdqu xmm0,XMMWORD PTR [rsp]
  f9:	c5 fa 6f 4c 24 10    	vmovdqu xmm1,XMMWORD PTR [rsp+0x10]
  ff:	c5 fa 6f 54 24 20    	vmovdqu xmm2,XMMWORD PTR [rsp+0x20]
 105:	c5 fa 7f 07          	vmovdqu XMMWORD PTR [rdi],xmm0
 109:	c5 fa 7f 4f 10       	vmovdqu XMMWORD PTR [rdi+0x10],xmm1
 10e:	c5 fa 7f 57 20       	vmovdqu XMMWORD PTR [rdi+0x20],xmm2
 113:	48 8b 44 24 38       	mov    rax,QWORD PTR [rsp+0x38]
 118:	64 48 2b 04 25 28 00 00 00 	sub    rax,QWORD PTR fs:0x28
 121:	75 06                	jne    129 <sub_mod_384+0x129>
 123:	48 83 c4 40          	add    rsp,0x40
 127:	5b                   	pop    rbx
 128:	c3                   	ret    
 129:	e8 00 00 00 00       	call   12e <sub_mod_384+0x12e>	12a: R_X86_64_PLT32	__stack_chk_fail-0x4

Disassembly of section .text._Z11_lshift_384PyPKyS1_:

0000000000000000 <_lshift_384(unsigned long long*, unsigned long long const*, unsigned long long const*)>:
   0:	f3 0f 1e fa          	endbr64 
   4:	48 8b 06             	mov    rax,QWORD PTR [rsi]
   7:	48 01 c0             	add    rax,rax
   a:	48 89 07             	mov    QWORD PTR [rdi],rax
   d:	48 8b 46 08          	mov    rax,QWORD PTR [rsi+0x8]
  11:	0f 92 c2             	setb   dl
  14:	80 c2 ff             	add    dl,0xff
  17:	48 11 c0             	adc    rax,rax
  1a:	48 89 47 08          	mov    QWORD PTR [rdi+0x8],rax
  1e:	48 8b 46 10          	mov    rax,QWORD PTR [rsi+0x10]
  22:	0f 92 c2             	setb   dl
  25:	80 c2 ff             	add    dl,0xff
  28:	48 11 c0             	adc    rax,rax
  2b:	48 89 47 10          	mov    QWORD PTR [rdi+0x10],rax
  2f:	48 8b 46 18          	mov    rax,QWORD PTR [rsi+0x18]
  33:	0f 92 c2             	setb   dl
  36:	80 c2 ff             	add    dl,0xff
  39:	48 11 c0             	adc    rax,rax
  3c:	48 89 47 18          	mov    QWORD PTR [rdi+0x18],rax
  40:	48 8b 46 20          	mov    rax,QWORD PTR [rsi+0x20]
  44:	0f 92 c2             	setb   dl
  47:	80 c2 ff             	add    dl,0xff
  4a:	48 11 c0             	adc    rax,rax
  4d:	48 89 47 20          	mov    QWORD PTR [rdi+0x20],rax
  51:	48 8b 46 28          	mov    rax,QWORD PTR [rsi+0x28]
  55:	0f 92 c2             	setb   dl
  58:	80 c2 ff             	add    dl,0xff
  5b:	48 11 c0             	adc    rax,rax
  5e:	48 89 47 28          	mov    QWORD PTR [rdi+0x28],rax
  62:	c3                   	ret    

Disassembly of section .text.mul_by_3_mod_384:

0000000000000000 <mul_by_3_mod_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	41 55                	push   r13
   6:	49 89 d5             	mov    r13,rdx
   9:	41 54                	push   r12
   b:	49 89 f4             	mov    r12,rsi
   e:	55                   	push   rbp
   f:	48 89 fd             	mov    rbp,rdi
  12:	e8 00 00 00 00       	call   17 <mul_by_3_mod_384+0x17>	13: R_X86_64_PLT32	_lshift_384(unsigned long long*, unsigned long long const*, unsigned long long const*)-0x4
  17:	4c 89 e9             	mov    rcx,r13
  1a:	4c 89 e2             	mov    rdx,r12
  1d:	48 89 ee             	mov    rsi,rbp
  20:	48 89 ef             	mov    rdi,rbp
  23:	5d                   	pop    rbp
  24:	41 5c                	pop    r12
  26:	41 5d                	pop    r13
  28:	e9 00 00 00 00       	jmp    2d <mul_by_3_mod_384+0x2d>	29: R_X86_64_PLT32	add_mod_384-0x4

Disassembly of section .text.mul_by_8_mod_384:

0000000000000000 <mul_by_8_mod_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	41 54                	push   r12
   6:	55                   	push   rbp
   7:	49 89 f4             	mov    r12,rsi
   a:	48 89 fd             	mov    rbp,rdi
   d:	53                   	push   rbx
   e:	48 89 d3             	mov    rbx,rdx
  11:	48 83 ec 40          	sub    rsp,0x40
  15:	64 48 8b 04 25 28 00 00 00 	mov    rax,QWORD PTR fs:0x28
  1e:	48 89 44 24 38       	mov    QWORD PTR [rsp+0x38],rax
  23:	31 c0                	xor    eax,eax
  25:	e8 00 00 00 00       	call   2a <mul_by_8_mod_384+0x2a>	26: R_X86_64_PLT32	_lshift_384(unsigned long long*, unsigned long long const*, unsigned long long const*)-0x4
  2a:	48 89 da             	mov    rdx,rbx
  2d:	4c 89 e6             	mov    rsi,r12
  30:	48 89 ef             	mov    rdi,rbp
  33:	e8 00 00 00 00       	call   38 <mul_by_8_mod_384+0x38>	34: R_X86_64_PLT32	_lshift_384(unsigned long long*, unsigned long long const*, unsigned long long const*)-0x4
  38:	48 89 da             	mov    rdx,rbx
  3b:	4c 89 e6             	mov    rsi,r12
  3e:	48 89 ef             	mov    rdi,rbp
  41:	e8 00 00 00 00       	call   46 <mul_by_8_mod_384+0x46>	42: R_X86_64_PLT32	_lshift_384(unsigned long long*, unsigned long long const*, unsigned long long const*)-0x4
  46:	48 8b 45 00          	mov    rax,QWORD PTR [rbp+0x0]
  4a:	48 2b 03             	sub    rax,QWORD PTR [rbx]
  4d:	0f 92 c2             	setb   dl
  50:	48 89 04 24          	mov    QWORD PTR [rsp],rax
  54:	48 8b 45 08          	mov    rax,QWORD PTR [rbp+0x8]
  58:	80 c2 ff             	add    dl,0xff
  5b:	48 1b 43 08          	sbb    rax,QWORD PTR [rbx+0x8]
  5f:	0f 92 c2             	setb   dl
  62:	48 89 44 24 08       	mov    QWORD PTR [rsp+0x8],rax
  67:	48 8b 45 10          	mov    rax,QWORD PTR [rbp+0x10]
  6b:	80 c2 ff             	add    dl,0xff
  6e:	48 1b 43 10          	sbb    rax,QWORD PTR [rbx+0x10]
  72:	0f 92 c2             	setb   dl
  75:	48 89 44 24 10       	mov    QWORD PTR [rsp+0x10],rax
  7a:	48 8b 45 18          	mov    rax,QWORD PTR [rbp+0x18]
  7e:	80 c2 ff             	add    dl,0xff
  81:	48 1b 43 18          	sbb    rax,QWORD PTR [rbx+0x18]
  85:	0f 92 c2             	setb   dl
  88:	48 89 44 24 18       	mov    QWORD PTR [rsp+0x18],rax
  8d:	48 8b 45 20          	mov    rax,QWORD PTR [rbp+0x20]
  91:	80 c2 ff             	add    dl,0xff
  94:	48 1b 43 20          	sbb    rax,QWORD PTR [rbx+0x20]
  98:	0f 92 c2             	setb   dl
  9b:	48 89 44 24 20       	mov    QWORD PTR [rsp+0x20],rax
  a0:	48 8b 45 28          	mov    rax,QWORD PTR [rbp+0x28]
  a4:	80 c2 ff             	add    dl,0xff
  a7:	48 1b 43 28          	sbb    rax,QWORD PTR [rbx+0x28]
  ab:	48 89 44 24 28       	mov    QWORD PTR [rsp+0x28],rax
  b0:	b8 28 00 00 00       	mov    eax,0x28
  b5:	48 8b 0c 03          	mov    rcx,QWORD PTR [rbx+rax*1]
  b9:	48 39 4c 05 00       	cmp    QWORD PTR [rbp+rax*1+0x0],rcx
  be:	72 2a                	jb     ea <mul_by_8_mod_384+0xea>
  c0:	48 83 e8 08          	sub    rax,0x8
  c4:	48 83 f8 f8          	cmp    rax,0xfffffffffffffff8
  c8:	75 eb                	jne    b5 <mul_by_8_mod_384+0xb5>
  ca:	c5 fa 6f 04 24       	vmovdqu xmm0,XMMWORD PTR [rsp]
  cf:	c5 fa 6f 4c 24 10    	vmovdqu xmm1,XMMWORD PTR [rsp+0x10]
  d5:	c5 fa 6f 54 24 20    	vmovdqu xmm2,XMMWORD PTR [rsp+0x20]
  db:	c5 fa 7f 45 00       	vmovdqu XMMWORD PTR [rbp+0x0],xmm0
  e0:	c5 fa 7f 4d 10       	vmovdqu XMMWORD PTR [rbp+0x10],xmm1
  e5:	c5 fa 7f 55 20       	vmovdqu XMMWORD PTR [rbp+0x20],xmm2
  ea:	48 8b 44 24 38       	mov    rax,QWORD PTR [rsp+0x38]
  ef:	64 48 2b 04 25 28 00 00 00 	sub    rax,QWORD PTR fs:0x28
  f8:	75 09                	jne    103 <mul_by_8_mod_384+0x103>
  fa:	48 83 c4 40          	add    rsp,0x40
  fe:	5b                   	pop    rbx
  ff:	5d                   	pop    rbp
 100:	41 5c                	pop    r12
 102:	c3                   	ret    
 103:	e8 00 00 00 00       	call   108 <mul_by_8_mod_384+0x108>	104: R_X86_64_PLT32	__stack_chk_fail-0x4

Disassembly of section .text.cneg_mod_384:

0000000000000000 <cneg_mod_384>:
   0:	f3 0f 1e fa          	endbr64 
   4:	49 89 f0             	mov    r8,rsi
   7:	48 89 ce             	mov    rsi,rcx
   a:	84 d2                	test   dl,dl
   c:	74 12                	je     20 <cneg_mod_384+0x20>
   e:	4c 89 c2             	mov    rdx,r8
  11:	e9 00 00 00 00       	jmp    16 <cneg_mod_384+0x16>	12: R_X86_64_PLT32	sub_mod_384-0x4
  16:	66 2e 0f 1f 84 00 00 00 00 00 	nop    WORD PTR cs:[rax+rax*1+0x0]
  20:	c4 c1 7a 6f 00       	vmovdqu xmm0,XMMWORD PTR [r8]
  25:	c5 fa 7f 07          	vmovdqu XMMWORD PTR [rdi],xmm0
  29:	c4 c1 7a 6f 48 10    	vmovdqu xmm1,XMMWORD PTR [r8+0x10]
  2f:	c5 fa 7f 4f 10       	vmovdqu XMMWORD PTR [rdi+0x10],xmm1
  34:	c4 c1 7a 6f 50 20    	vmovdqu xmm2,XMMWORD PTR [r8+0x20]
  3a:	c5 fa 7f 57 20       	vmovdqu XMMWORD PTR [rdi+0x20],xmm2
  3f:	c3                   	ret    
