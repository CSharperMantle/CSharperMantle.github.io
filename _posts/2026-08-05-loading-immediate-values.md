---
layout: post
title: Loading immediate values
date: 2026-08-05T17:24:40+08:00
lang: en
description: >-
    Maybe not so "immediate".
tags: topic:dev architecture x86 risc-v loongarch
---

Loading an immediate value into a register is so easy! All three assembly snippets below load two constant integers into two different registers.

```asm
# x86-64, Intel syntax
mov rax, 1
mov rcx, 0x1234567890abcdef
```

```asm
# RISC-V rv64g
li a0, 1
li a1, 0x1234567890abcdef
```

```asm
# LoongArch loongarch64
li.d $a0, 1
li.d $a1, 0x1234567890abcdef
```

However, when assembled, only the x86-64 snippet retains its familiar shape. The other two are both expanded into >2 instructions. Why?

```asm
# x86-64, Intel syntax
mov rax, 0x1
mov rcx, 0x1234567890abcdef
```

```asm
# RISC-V rv64g
li a0, 1
lui a1, 0x247
addiw a1, a1, -1875
slli a1, a1, 0xf
addi a1, a1, -1903
slli a1, a1, 0xc
addi a1, a1, -1347
slli a1, a1, 0xc
addi a1, a1, -529
```

```asm
# LoongArch loongarch64
li.w $a0, 0x1
lu12i.w $a1, -456004
ori $a1, $a1, 0xdef
lu32i.d $a1, 284280
lu52i.d $a1, $a1, 291
```

This is because x86-64 instructions can be longer than the machine word, and long enough to fully encode the immediate inside one instruction.

```plain-text
mov rax, 1
|  48  |  C7  |  C0  |  01 00 00 00  |
 REX.W  Opcode ModR/M    Immediate

mov rcx, 0x1234567890abcdef
|  48  |  B9  |  EF CD AB 90 78 56 34 12  |
 REX.W  Opcode          Immediate

<- LSB                               MSB ->
```

RISC-V and LoongArch (as well as AArch64) don't have this capability. Each of their instructions can only encode a subset of the immediate space. If the immediate-to-load falls outside this subset, they need to break it up into fragments and concatenate them in-place.

```plain-text
# RISC-V rv64g
addi a0, zero, 1
   00      10           05                13
|  000000000001  |  00000  |  000  |  01010  |  0010011  |
    imm[11:0]        rs1    funct3     rd       opcode

<- MSB                                              LSB ->
```

Generally, there are two topologies of the immediate loading strategy, which are based on the level of abstraction and amount of information available:

1. A *linear* approach builds the immediate within the destination register itself. The general approach is to insert the lower bits via addition, then shift them to the <abbr title="Most Significant Bit">MSB</abbr> side. Assemblers usually take this approach, since they don't know how other registers are used locally.
2. A *convergent* approach builds fragments in many registers, then adds them together and stores the result in the destination register. Compilers have enough information about register liveliness to take this approach to (hopefully) reduce a few shifts. Recursively, each fragment can have its own strategy for building.

(This is a bit similar to [organic synthesis](https://en.wikipedia.org/wiki/Convergent_synthesis).)

For example, the following two snippets are the results of translating the same instruction, `li a0, 0x1234567812345678`, using different tools:

```asm
# GNU assembler (GNU Binutils) 2.44
lui  a0, 0x247
addiw  a0, a0, -1875
slli  a0, a0, 0xe
addi  a0, a0, -1015
slli  a0, a0, 0xd
addi  a0, a0, 837
slli  a0, a0, 0xc
addi  a0, a0, 1656
```

```asm
# gcc (GCC) 15.1.0
lui  a5, 0x12345
addi  a5, a5, 1656
slli  a0, a5, 0x20
add  a0, a0, a5
```

The compiler's version uses fewer instructions at the cost of one extra temporary register. Compilers like [LLVM](https://github.com/PacktPublishing/LLVM-Code-Generation-by-example/blob/f83b02408a8d2445f1dc287fa5b3075711326213/llvm/lib/Target/RISCV/MCTargetDesc/RISCVMatInt.cpp) and <abbr title="Just-In-Time">JIT</abbr> engines like [SpiderMonkey](https://searchfox.org/firefox-main/source/js/src/jit/riscv64/AssemblerMatInt.cpp) choose the suitable strategy for each fragment via a cost model.

But why would assemblers and compilers take so much time selecting different sequences for different immediates? Why not just consider unused fragments zero, and use a single, fixed sequence for every immediate?

One major benefit is code size. Modern <abbr title="Central Processing Unit">CPU</abbr>s have sophisticated mechanisms to boost program performance. One mechanism is by exploiting the principle of [locality](https://en.wikipedia.org/wiki/Locality_of_reference) via *caching*. Hot data is loaded into a small, fast chunk of memory called cache for quick retrieval. The smaller the code is, the easier it fits in faster caches, and the fewer cycles it will take to load it from the cache.

Modern <abbr title="Central Processing Unit">CPU</abbr>s can also recognize *idioms* used by programmers to speed up execution. A famous example is the x86 `xor  eax, eax` trick that zeroes `eax`. These well-known idioms are special-cased so that little actual work is spent. For example, the <abbr title="Central Processing Unit">CPU</abbr> doesn't have to wait for a prior write to `eax` to finish.[^0] This pattern recognition ability also extends to immediate materialization, because they are so common in programs. The <abbr title="Central Processing Unit">CPU</abbr> can *fuse* the whole sequence into a single internal load operation, as long as the sequence fits its fusion window, and thus observable to the processor. Clearly, shorter sequences are more likely to meet the length requirement of fusion. This is especially true when the sequence does not appear exactly at the start of the window.

Consider the following two LoongArch snippets that both load the immediate 1 into `$t0`:

```asm
# Snippet A
addi.w  $t0, $zero, 1
```

```asm
# Snippet B
lu12i.w  $t0, 0
ori  $t0, $t0, 1
lu32i.d  $t0, 0
lu52i.d  $t0, $t0, 0
```

How do they perform in terms of throughput, i.e., the number of cycles needed to load an immediate? A naive estimation will yield 1 for Snippet A and 4 for Snippet B. This is not very accurate on modern processors. Let's measure it on [Loongson 3B6000/12](https://loongfans.cn/en/chips/cpu/3b6000/3b6000-12), a 2.2GHz, 12-core, 24-thread <abbr title="Out-of-Order">OoO</abbr> LoongArch64 processor.

Kernels under test are generated via the following snippet. Each generated function takes the iteration number as an argument in `$a0`, and should return 1 in the same register. Each kernel puts the snippet of interest at a different offset to measure the effect of window placement. The labels `a_a0_hot`, `a_a4_hot`, etc. are for assertions that the snippet is correctly aligned.

```asm
.macro A reg
    addi.w  \reg, $zero, 1
.endm

.macro B reg
    lu12i.w \reg, 0
    ori     \reg, \reg, 1
    lu32i.d \reg, 0
    lu52i.d \reg, \reg, 0
.endm

.macro BENCH name, op, off
    .globl  \name
    .type   \name, @function
\name:
    b       .Lhot_\name
    .p2align 5
.if \off
    .space  \off
.endif
    .globl  \name\()_hot
\name\()_hot:
.Lhot_\name:
    \op     $t1
    addi.d  $a0, $a0, -1
    bnez    $a0, .Lhot_\name
    or      $a0, $t1, $zero
    ret
    .size   \name, .-\name
.endm

BENCH a_a0,  A, 0
BENCH a_a4,  A, 4
BENCH a_a8,  A, 8
BENCH a_a12, A, 12
BENCH a_a16, A, 16
BENCH a_a20, A, 20
BENCH a_a24, A, 24
BENCH a_a28, A, 28

BENCH b_a0,  B, 0
BENCH b_a4,  B, 4
BENCH b_a8,  B, 8
BENCH b_a12, B, 12
BENCH b_a16, B, 16
BENCH b_a20, B, 20
BENCH b_a24, B, 24
BENCH b_a28, B, 28
```

The measurement contains 30 rounds for each kernel. In each round, we warm up the kernel by 1,000,000 iterations and run it for 10,000,000 iterations. We use [perf_event_open(2)](https://www.man7.org/linux/man-pages/man2/perf_event_open.2.html) to measure the cycles elapsed. We calculate the median of 30 rounds, then take `1 / (median / iterations)` to calculate the throughput. The result is shown below.

| Offset | Snippet A | Snippet B |
| -----: | --------: | --------: |
|      0 |    1.0000 |    1.3245 |
|      4 |    1.0001 |    1.3187 |
|      8 |    1.0002 |    1.3454 |
|     12 |    1.0001 |    2.0004 |
|     16 |    1.0001 |    2.0002 |
|     20 |    1.0000 |    2.0001 |
|     24 |    2.0003 |    2.0005 |
|     28 |    2.0001 |    2.0001 |

From the results, it’s clear that Snippets A and B actually perform quite similarly at low offset, with Snippet B taking ~0.3 cycles more. At somewhat larger offsets, Snippet B takes 2 cycles to finish while Snippet A remains 1 cycle. At even larger offsets, the two snippets both take 2 cycles to finish. Idiom recognition is certainly helping us at lower offsets, while at larger offsets the sequence probably goes beyond the recognition window. I have not carried out this test on RISC-V processors with longer sequences yet, and I believe the results would be more interesting.

Loading an immediate value into a register is not so easy and "immediate", after all. Yet, it is certainly a fascinating topic in computer architecture and micro-architecture research.

[^0]: This is usually done by [*register renaming*](https://en.wikipedia.org/wiki/Register_renaming). At this stage, a small number of *architectural registers* (like `eax`) are dynamically mapped to a larger number of *physical registers*. Then, two unrelated computations writing to the same architectural register can be transformed to use different physical registers, allowing them to be run in parallel.

