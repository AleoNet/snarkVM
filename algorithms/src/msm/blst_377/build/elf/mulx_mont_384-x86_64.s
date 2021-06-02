.text	

.globl	mulx_mont_384
.hidden	mulx_mont_384
.type	mulx_mont_384,@function
.align	32
mulx_mont_384:
.cfi_startproc
	.byte	0xf3,0x0f,0x1e,0xfa


	pushq	%rbp
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbp,-16
	pushq	%rbx
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbx,-24
	pushq	%r12
.cfi_adjust_cfa_offset	8
.cfi_offset	%r12,-32
	pushq	%r13
.cfi_adjust_cfa_offset	8
.cfi_offset	%r13,-40
	pushq	%r14
.cfi_adjust_cfa_offset	8
.cfi_offset	%r14,-48
	pushq	%r15
.cfi_adjust_cfa_offset	8
.cfi_offset	%r15,-56
	leaq	-24(%rsp),%rsp
.cfi_adjust_cfa_offset	8*3


	movq	%rdx,%rbx
	movq	0(%rdx),%rdx
	movq	0(%rsi),%r14
	movq	8(%rsi),%r15
	movq	16(%rsi),%rax
	movq	24(%rsi),%r12
	movq	%rdi,16(%rsp)
	movq	32(%rsi),%rdi
	movq	40(%rsi),%rbp
	leaq	-128(%rsi),%rsi
	leaq	-128(%rcx),%rcx
	movq	%r8,(%rsp)

	mulxq	%r14,%r8,%r9
	call	__mulx_mont_384

	movq	24(%rsp),%r15
.cfi_restore	%r15
	movq	32(%rsp),%r14
.cfi_restore	%r14
	movq	40(%rsp),%r13
.cfi_restore	%r13
	movq	48(%rsp),%r12
.cfi_restore	%r12
	movq	56(%rsp),%rbx
.cfi_restore	%rbx
	movq	64(%rsp),%rbp
.cfi_restore	%rbp
	leaq	72(%rsp),%rsp
.cfi_adjust_cfa_offset	-8*9

	.byte	0xf3,0xc3
.cfi_endproc	
.size	mulx_mont_384,.-mulx_mont_384
.type	__mulx_mont_384,@function
.align	32
__mulx_mont_384:
.cfi_startproc
	.byte	0xf3,0x0f,0x1e,0xfa


	mulxq	%r15,%r14,%r10
	mulxq	%rax,%r15,%r11
	addq	%r14,%r9
	mulxq	%r12,%rax,%r12
	adcq	%r15,%r10
	mulxq	%rdi,%rdi,%r13
	adcq	%rax,%r11
	mulxq	%rbp,%rbp,%r14
	movq	8(%rbx),%rdx
	adcq	%rdi,%r12
	adcq	%rbp,%r13
	adcq	$0,%r14
	xorq	%r15,%r15

	movq	%r8,16(%rsp)
	imulq	8(%rsp),%r8


	xorq	%rax,%rax
	mulxq	0+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r9
	adcxq	%rbp,%r10

	mulxq	8+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r10
	adcxq	%rbp,%r11

	mulxq	16+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r11
	adcxq	%rbp,%r12

	mulxq	24+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r12
	adcxq	%rbp,%r13

	mulxq	32+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r13
	adcxq	%rbp,%r14

	mulxq	40+128(%rsi),%rdi,%rbp
	movq	%r8,%rdx
	adoxq	%rdi,%r14
	adcxq	%rbp,%r15
	adoxq	%rax,%r15
	adoxq	%rax,%rax


	xorq	%r8,%r8
	mulxq	0+128(%rcx),%rdi,%rbp
	adcxq	16(%rsp),%rdi
	adoxq	%rbp,%r9

	mulxq	8+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r9
	adoxq	%rbp,%r10

	mulxq	16+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r10
	adoxq	%rbp,%r11

	mulxq	24+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r11
	adoxq	%rbp,%r12

	mulxq	32+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r12
	adoxq	%rbp,%r13

	mulxq	40+128(%rcx),%rdi,%rbp
	movq	16(%rbx),%rdx
	adcxq	%rdi,%r13
	adoxq	%rbp,%r14
	adcxq	%r8,%r14
	adoxq	%r8,%r15
	adcxq	%r8,%r15
	adoxq	%r8,%rax
	adcxq	%r8,%rax
	movq	%r9,16(%rsp)
	imulq	8(%rsp),%r9


	xorq	%r8,%r8
	mulxq	0+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r10
	adcxq	%rbp,%r11

	mulxq	8+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r11
	adcxq	%rbp,%r12

	mulxq	16+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r12
	adcxq	%rbp,%r13

	mulxq	24+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r13
	adcxq	%rbp,%r14

	mulxq	32+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r14
	adcxq	%rbp,%r15

	mulxq	40+128(%rsi),%rdi,%rbp
	movq	%r9,%rdx
	adoxq	%rdi,%r15
	adcxq	%rbp,%rax
	adoxq	%r8,%rax
	adoxq	%r8,%r8


	xorq	%r9,%r9
	mulxq	0+128(%rcx),%rdi,%rbp
	adcxq	16(%rsp),%rdi
	adoxq	%rbp,%r10

	mulxq	8+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r10
	adoxq	%rbp,%r11

	mulxq	16+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r11
	adoxq	%rbp,%r12

	mulxq	24+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r12
	adoxq	%rbp,%r13

	mulxq	32+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r13
	adoxq	%rbp,%r14

	mulxq	40+128(%rcx),%rdi,%rbp
	movq	24(%rbx),%rdx
	adcxq	%rdi,%r14
	adoxq	%rbp,%r15
	adcxq	%r9,%r15
	adoxq	%r9,%rax
	adcxq	%r9,%rax
	adoxq	%r9,%r8
	adcxq	%r9,%r8
	movq	%r10,16(%rsp)
	imulq	8(%rsp),%r10


	xorq	%r9,%r9
	mulxq	0+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r11
	adcxq	%rbp,%r12

	mulxq	8+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r12
	adcxq	%rbp,%r13

	mulxq	16+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r13
	adcxq	%rbp,%r14

	mulxq	24+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r14
	adcxq	%rbp,%r15

	mulxq	32+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r15
	adcxq	%rbp,%rax

	mulxq	40+128(%rsi),%rdi,%rbp
	movq	%r10,%rdx
	adoxq	%rdi,%rax
	adcxq	%rbp,%r8
	adoxq	%r9,%r8
	adoxq	%r9,%r9


	xorq	%r10,%r10
	mulxq	0+128(%rcx),%rdi,%rbp
	adcxq	16(%rsp),%rdi
	adoxq	%rbp,%r11

	mulxq	8+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r11
	adoxq	%rbp,%r12

	mulxq	16+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r12
	adoxq	%rbp,%r13

	mulxq	24+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r13
	adoxq	%rbp,%r14

	mulxq	32+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r14
	adoxq	%rbp,%r15

	mulxq	40+128(%rcx),%rdi,%rbp
	movq	32(%rbx),%rdx
	adcxq	%rdi,%r15
	adoxq	%rbp,%rax
	adcxq	%r10,%rax
	adoxq	%r10,%r8
	adcxq	%r10,%r8
	adoxq	%r10,%r9
	adcxq	%r10,%r9
	movq	%r11,16(%rsp)
	imulq	8(%rsp),%r11


	xorq	%r10,%r10
	mulxq	0+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r12
	adcxq	%rbp,%r13

	mulxq	8+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r13
	adcxq	%rbp,%r14

	mulxq	16+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r14
	adcxq	%rbp,%r15

	mulxq	24+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r15
	adcxq	%rbp,%rax

	mulxq	32+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%rax
	adcxq	%rbp,%r8

	mulxq	40+128(%rsi),%rdi,%rbp
	movq	%r11,%rdx
	adoxq	%rdi,%r8
	adcxq	%rbp,%r9
	adoxq	%r10,%r9
	adoxq	%r10,%r10


	xorq	%r11,%r11
	mulxq	0+128(%rcx),%rdi,%rbp
	adcxq	16(%rsp),%rdi
	adoxq	%rbp,%r12

	mulxq	8+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r12
	adoxq	%rbp,%r13

	mulxq	16+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r13
	adoxq	%rbp,%r14

	mulxq	24+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r14
	adoxq	%rbp,%r15

	mulxq	32+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r15
	adoxq	%rbp,%rax

	mulxq	40+128(%rcx),%rdi,%rbp
	movq	40(%rbx),%rdx
	adcxq	%rdi,%rax
	adoxq	%rbp,%r8
	adcxq	%r11,%r8
	adoxq	%r11,%r9
	adcxq	%r11,%r9
	adoxq	%r11,%r10
	adcxq	%r11,%r10
	movq	%r12,16(%rsp)
	imulq	8(%rsp),%r12


	xorq	%r11,%r11
	mulxq	0+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r13
	adcxq	%rbp,%r14

	mulxq	8+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r14
	adcxq	%rbp,%r15

	mulxq	16+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r15
	adcxq	%rbp,%rax

	mulxq	24+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%rax
	adcxq	%rbp,%r8

	mulxq	32+128(%rsi),%rdi,%rbp
	adoxq	%rdi,%r8
	adcxq	%rbp,%r9

	mulxq	40+128(%rsi),%rdi,%rbp
	movq	%r12,%rdx
	adoxq	%rdi,%r9
	adcxq	%rbp,%r10
	adoxq	%r11,%r10
	adoxq	%r11,%r11


	xorq	%r12,%r12
	mulxq	0+128(%rcx),%rdi,%rbp
	adcxq	16(%rsp),%rdi
	adoxq	%rbp,%r13

	mulxq	8+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r13
	adoxq	%rbp,%r14

	mulxq	16+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r14
	adoxq	%rbp,%r15

	mulxq	24+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r15
	adoxq	%rbp,%rax

	mulxq	32+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%rax
	adoxq	%rbp,%r8

	mulxq	40+128(%rcx),%rdi,%rbp
	movq	%r13,%rdx
	adcxq	%rdi,%r8
	adoxq	%rbp,%r9
	adcxq	%r12,%r9
	adoxq	%r12,%r10
	adcxq	%r12,%r10
	adoxq	%r12,%r11
	adcxq	%r12,%r11
	imulq	8(%rsp),%rdx
	movq	24(%rsp),%rbx


	xorq	%r12,%r12
	mulxq	0+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r13
	adoxq	%rbp,%r14

	mulxq	8+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r14
	adoxq	%rbp,%r15

	mulxq	16+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r15
	adoxq	%rbp,%rax

	mulxq	24+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%rax
	adoxq	%rbp,%r8
	movq	%r15,%r13

	mulxq	32+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r8
	adoxq	%rbp,%r9
	movq	%rax,%rsi

	mulxq	40+128(%rcx),%rdi,%rbp
	adcxq	%rdi,%r9
	adoxq	%rbp,%r10
	movq	%r14,%rdx
	adcxq	%r12,%r10
	adoxq	%r12,%r11
	leaq	128(%rcx),%rcx
	movq	%r8,%r12
	adcq	$0,%r11




	subq	0(%rcx),%r14
	sbbq	8(%rcx),%r15
	movq	%r9,%rdi
	sbbq	16(%rcx),%rax
	sbbq	24(%rcx),%r8
	sbbq	32(%rcx),%r9
	movq	%r10,%rbp
	sbbq	40(%rcx),%r10
	sbbq	$0,%r11

	cmovncq	%r14,%rdx
	cmovcq	%r13,%r15
	cmovcq	%rsi,%rax
	cmovncq	%r8,%r12
	movq	%rdx,0(%rbx)
	cmovncq	%r9,%rdi
	movq	%r15,8(%rbx)
	cmovncq	%r10,%rbp
	movq	%rax,16(%rbx)
	movq	%r12,24(%rbx)
	movq	%rdi,32(%rbx)
	movq	%rbp,40(%rbx)

	.byte	0xf3,0xc3
.cfi_endproc	
.size	__mulx_mont_384,.-__mulx_mont_384
.globl	sqrx_mont_384
.hidden	sqrx_mont_384
.type	sqrx_mont_384,@function
.align	32
sqrx_mont_384:
.cfi_startproc
	.byte	0xf3,0x0f,0x1e,0xfa


	pushq	%rbp
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbp,-16
	pushq	%rbx
.cfi_adjust_cfa_offset	8
.cfi_offset	%rbx,-24
	pushq	%r12
.cfi_adjust_cfa_offset	8
.cfi_offset	%r12,-32
	pushq	%r13
.cfi_adjust_cfa_offset	8
.cfi_offset	%r13,-40
	pushq	%r14
.cfi_adjust_cfa_offset	8
.cfi_offset	%r14,-48
	pushq	%r15
.cfi_adjust_cfa_offset	8
.cfi_offset	%r15,-56
	leaq	-24(%rsp),%rsp
.cfi_adjust_cfa_offset	8*3


	movq	%rcx,%r8
	leaq	-128(%rdx),%rcx
	movq	0(%rsi),%rdx
	movq	8(%rsi),%r15
	movq	16(%rsi),%rax
	movq	24(%rsi),%r12
	movq	%rdi,16(%rsp)
	movq	32(%rsi),%rdi
	movq	40(%rsi),%rbp

	leaq	(%rsi),%rbx
	movq	%r8,(%rsp)
	leaq	-128(%rsi),%rsi

	mulxq	%rdx,%r8,%r9
	call	__mulx_mont_384

	movq	24(%rsp),%r15
.cfi_restore	%r15
	movq	32(%rsp),%r14
.cfi_restore	%r14
	movq	40(%rsp),%r13
.cfi_restore	%r13
	movq	48(%rsp),%r12
.cfi_restore	%r12
	movq	56(%rsp),%rbx
.cfi_restore	%rbx
	movq	64(%rsp),%rbp
.cfi_restore	%rbp
	leaq	72(%rsp),%rsp
.cfi_adjust_cfa_offset	-8*9

	.byte	0xf3,0xc3
.cfi_endproc	
.size	sqrx_mont_384,.-sqrx_mont_384

.section	.note.GNU-stack,"",@progbits
.section	.note.gnu.property,"a",@note
	.long	4,2f-1f,5
	.byte	0x47,0x4E,0x55,0
1:	.long	0xc0000002,4,3
.align	8
2:
