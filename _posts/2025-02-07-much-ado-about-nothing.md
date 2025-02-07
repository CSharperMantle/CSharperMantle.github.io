---
layout: post
title: "Much ado about nothing"
date: 2025-02-07T09:45:05+08:00
lang: en
description: >-
    There's quite a lot to say about doing nothing.
tags: topic:dev os architecture ee assembly x86 risc-v
---

We apply sophisticated techniques to slack off. In the world of computers, the term "idle" and "slack off" have their special meanings as well, with variations in both definition and handling between each system. As our discussion shifts from systems, OSes to hardware, the meaning of "idle" and things to do when idling drastically changes.

## Idleness in systems

Some of the most simple (but far from easy!) computer systems are bare-metal real-time systems that are commonly found in embedded applications. These systems are designed to react to external events quickly, usually on a small cost and energy (and, sometimes, size) budget. Generally, we have two ways to keep track of external events:

* *Polling.* We check periodically whether an event has happened. If so, handle it.
* *Interrupts.* When the event occurs, we receive a special message. On receiving it, we divert to handle the event and then pick up the previous job afterward.

Here, a system is "idle" if no event occurs at a given moment. In the polling approach, our system periodically checks for events even if there are no pending ones. Of course, can either let the system *sleep* between every two checks, possibly reducing power consumption. The drawback is the reaction time would increase if it sleeps for too long. Or, we can just let the system wander about during this period, running a special task that represents "no tasks". It could be as simple as a tight loop.

```c
for (unsigned i = 0; i < 10000; i++) {
    ;
}
```

The same idea extends to more complex, familiar systems. Consumer operating systems run many tasks at the same time, sharing the hardware resources among them. Each task takes turns to run for a short period, then it is suspended to give other tasks a chance. *Schedulers* orchestrate this time-sharing behavior at a high speed, so in a user's view, all tasks run simultaneously. A task may be *blocked*, waiting for some non-CPU resources to be available. It may also voluntarily *sleep* for a while. Under these circumstances, the scheduler happily assigns the processor resources to other *ready* tasks, only waking up the blocked task after its requested resources become ready.

Still, a scheduler could run out of ready tasks. The simple approach is to add a special "idle" task that does few to no jobs. In Linux, [an always-ready `idle` task](https://www.kernel.org/doc/html/v5.0/admin-guide/pm/cpuidle.html#the-idle-loop) is assigned when no other ready tasks are available. Each logical CPU has its own `idle` task. This task puts the running CPU into an *idle state* with parameters calculated by sophisticated *governors*. The CPU's idle state is a hardware state, not an OS abstraction, so it differs among each architecture and CPU model and will be covered [later in this post](#sleep-electronically).

Windows uses a different set of terminology[^1] to describe its ~~scheduling~~ *dispatching* behavior. Each CPU has an *idle thread*[^2], which runs when the CPU is idle. All idle threads belong to an *idle process*, the one you see as a "System Idle Process" in Task Manager.

## Nops in ISAs

In many architectures, there are instructions (or sequences of instructions) doing nothing. The geek's word for them is *nop*, which means "no operations". Here, "nothing" means no visible changes in architectural states, except for the program counter of course.

Consider this x86-64 assembly:

```asm
xchg eax, eax
```

It exchanges `eax`'s value with itself, which obviously does nothing on `eax`. Some instructions modify `eflags` based on their calculated results, but `xchg` is not one of them[^3]. So, this instruction has no visible effect from the perspective of running code. In x86, these pairs of instructions encode exactly the same bytes, both `0x90`:

```asm
; in x86
nop
xchg eax, eax

; in x86-64
nop
xchg rax, rax
```

I guess most of us would the first line of each pair.

Curiously, x86-64 has a CPUID flag for "multi-byte NOPs", extending `nop` with stride-index-base memory access encoding[^4]. Thus, all of these are valid:

```asm
nop
nop qword ptr [rbx]
nop qword ptr [rbx+rcx]
nop qword ptr [rbx+0x12340000]
nop qword ptr [rbx+rcx*8+0x12340000]
```

It's really an extended family thanks to the CISC architecture!

Some other architectures have special registers that can be utilized to perform a nop. One example is the `x0` register in RISC-V RV32/64, whose ABI name is `zero`. [It is hardwired to unsigned 0, and all writes to it are ignored.](https://riscv-software-src.github.io/riscv-unified-db/manual/html/isa/isa_20240411/chapters/rv32.html#_programmers_model_for_base_integer_isa) This feature leads to an intuitive implementation of nop: writing `x0` to `x0`. In RV32 assembly, it is written as:

```asm
mv x0, x0
```

But `mv rd, rs` itself is an alias to `addi rd, rs, 0`, so our nop implementation is in fact:

```asm
addi x0, x0, 0
```

... which is exactly [the definition of `nop` in the ISA manual](https://riscv-software-src.github.io/riscv-unified-db/manual/html/isa/isa_20240411/chapters/rv32.html#_nop_instruction).

Despite being a RISC architecture, the design of RV32 leaves room for other encodings of `nop`. It's not hard to see that `mv`-ing any register to `x0` would result in no effect. And since flags and comparison results are not encoded in RV32 ISA states but represented by conditional branches (e.g. `beq x1, zero, $imm`), almost all arithmetic instructions could be nop, as long as its destination register is `zero`.

Conditional branches can also be nops. Unsatisfiable conditions, and an always-taken jump to its static successor. Namely, the two following instructions are all nops:

```asm
bne zero, zero, $imm
beq zero, zero, 4
```

But some instructions can never be considered nops. See the following exercise for an example.

**Exercise.** In RV32, load instructions read data from a memory location into a destination register. For example, the following instruction reads a word (4 bytes) from memory location `x1 + 4` into `zero`:

```asm
lw zero, 4(x1)
```

Why is it **not** considered a nop, even though its destination is `zero`?

## A microscopic view

Each processor provides an implementation of an ISA via its *micro-architecture*. The same ISA could be implemented by many different micro-archs. Though nops have no architectural effects, different nops in the same ISA may have drastically different micro-architectural execution paths.

Modern high-performance processors try to make maximum use of their hardware components. They use many techniques to run statistically many instructions in each cycle, instead of running instructions one by one, waiting for each of them to finish. Typical techniques include:

* *Pipelining.* Just like making products in a factory, an instruction's execution can be divided into many *stages*. It has to be fetched from memory, decoded, result calculated, and then persisted into memory or registers. When the previous instruction finishes decoding, the next instructions don't have to wait until it finishes. Instead, the next one can start decoding immediately.
* *Reordering.* Some instructions may have dependencies among each other. For example, one instruction's source operand is the preceding one's destination. It can not be calculated before the result of the preceding instruction is persisted. Modern processors select unrelated instructions to the pipeline to minimize these hazards.
* *Multiple issuing.* A hardware core may have more than one arithmetic logic units (ALUs) that do the actual calculation. In this case, many arithmetic instructions may run simultaneously.
* *Speculation.* Instead of waiting for a branch's result to be calculated, a high-performance processor may guess its jump destination, and start to run instructions there. If the prediction is correct, much time can be saved. Contrarily, if predicted incorrectly, all wrong instructions must be discarded.
* ... And many more.

However, these implementation details may differentiate some instructions having no differences on the ISA level.

Consider a simple pipelined RV32 processor having these stages: Fetching, Decoding, Execution, Memory Access, and Register Update. The following two sequences behave the same on the ISA level, but the latter one would be significantly slower if the processor is implemented poorly:

```asm
; Sequence 1
...
addi x1, x2, 4
addi zero, zero, 0
...
```

```asm
; Sequence 2
...
addi x1, x2, 4
addi zero, x1, 0
...
```

In each sequence, the second instruction is a nop. However, in plain sight, the one in Sequence 2 has a source operand `x1` depending on the destination of `addi x1, x2, 4`, while that in Sequence 1 doesn't. When `addi zero, x1, 0` goes into the Execution unit, the source register hasn't been updated by `addi x1, x2, 4`, now in the Memory Access unit. Thus, `addi zero, x1, 0` has to be paused until `addi x1, x2, 4` has finished its update, despite that no one will use its result.

Let's see another example. Consider a speculative RV32 processor that guesses all conditional branches as *backward taken and forward not taken* (BTFNT), a common pattern seen in loops. Running the following two instruction sequences on such a processor has no ISA differences, but one of them (guess which one!) may have a large performance penalty:

```asm
; Sequence 1
...
addi zero, zero, 0
...
```

```asm
; Sequence 2
...
bne zero, zero, -0x40
...
```

Here, Sequence 2 contains a branch never taken since `zero` always equals `zero`. However, the processor will predict it as taken since it jumps backward. It will have started running instructions at `-0x40` before it calculates that the branch is not taken. It will then have to discard all instructions fetched from `-0x40`, and start all over again at the correct place.

From these examples, we can see that even if both you and your coworker are doing nothing, the price you pay for slacking off is still probably different.

## Sleep electronically

Many factors may affect the processor's power consumption. Frequency, active silicon components, and (rarely) output signal levels are some common factors. Almost all sorts of processors and controllers have different *power states* since it's a common practice to put the chip to sleep when it's idle. Generally speaking, when a processor or controller enters a low-power state or "sleep state", most of its peripherals are switched off (or "stopping the clock" in engineers' jargon). Its execution is paused, and can only be woken up by interrupts. In consumer embedded applications, user interaction is usually infrequent, so putting the device to sleep can greatly extend its battery life. Your TV remote is likely sleeping for the majority of its lifespan.

Timing-critical applications, like the airplane's inertial nav and your self-driving car's route planners, don't have such stringent energy budgets in most cases, so these controllers have to squeeze out energy consumption margins.

PCs and laptops have to balance energy and performance. The Advanced Configuration and Power Specification (ACPI) [defines many "processor power states" (C-states)](https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/08_Processor_Configuration_and_Control/processor-power-states.html). We briefly list some important ones informally below:

* C0 state is the running state. The processor runs normally, and its clock is optionally throttled by an ACPI-defined mechanism.
* C1 state is entered by executing `hlt` in x86. No instructions are executed, but caches are preserved.
* C2 state is meant for multiprocessor architectures. Cache coherency is maintained across multiprocessors.
* C3 state's entry may flush and invalidate caches, thus the OS is responsible for maintaining cache coherency.
* ... Additional power states.

The power consumption decreases as the power state transits from C0 to Cn, while the entry/exit latency increases.

Some processor uses advanced architectures to support dynamic power adjustment. Intel Turbo Boost[^5] throttles or boosts clock frequency according to many factors. When under light load, some cores will "park"[^6], saving energy for these cores.

## End of journey

In this post, we have explored only the surface of doing nothing at all. So, next time when you plan to slack off, think it over. Sometimes it is just an innocuous rest, while sometimes you'd better be prepared for some unforeseen consequences[^7].

------

### Footnotes

[^1]: It's similar to many other Microsoft products.
[^2]: P. Yosifovich, A. Ionescu, M. E. Russinovich, D. A. Solomon. *Windows Internals*, Seventh Edition. Part 1, Chapter 4, "Thread scheduling", "Idle threads". pp 260-263.
[^3]: Intel Corporation. *Intel&reg; 64 and IA-32 Architectures Software Developer's Manual*, March 2023, Order Number: 334569-079US. Volume 2D: "Instruction Set Reference, W-Z". Chapter 6.1 "Instructions (W-Z)", "XCHG--Exchange Register/Memory With Register". pp 6-28.
[^4]: Intel Corporation. *Intel&reg; 64 and IA-32 Architectures Software Developer's Manual*, March 2023, Order Number: 253667-079US. Volume 2B: "Instruction Set Reference, M-U". Chapter 4.3 "Instructions (M-U)", "NOP--No Operation". pp 4-165.
[^5]: Intel Corporation. *Intel&reg; Turbo Boost Technology in Intel&reg; Core&trade; Microarchitecture (Nehalem) Based Processors*, November 2008.
[^6]: Yet Another Windowspeak&trade;
[^7]: Thanks, G-Man!
