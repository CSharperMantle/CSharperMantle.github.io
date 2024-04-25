---
layout: post
title: "简短的问候"
date: 2024-04-24 17:36:45 +0800
lang: zh-Hans
description: >-
    本文介绍了一种在x86-64下构造尽量小的输出一个常量字符串ELF程序的案例. 本文中的最好结果为152 bytes.
categories: misc
---

## 1. 问题描述

在x86-64 Linux平台下, 构造一个文件字节数最小的静态ELF可执行文件, 实现以下伪代码的功能:

```python
print("Hello!\n")
exit(0)
```

## 2. 解决方案

本文中实现的最小ELF文件落盘大小为152字节.

### 2.1. 888KB

编写一个C代码并静态编译能够给出最naive的结果.

```c
#include <stdio.h>

int main(void) {
    puts("Hello!");
    return 0;
}
```

```text
$ clang -std=c17 -Oz -static -o hello.c.elf hello.c
$ size ./hello.c.elf
   text    data     bss     dec     hex filename
 790033   23240   23016  836289   cc2c1 ./hello.c.elf
$ ls -Fsh ./hello.c.elf
888K ./hello.c.elf*
```

### 2.2. 888KB

绕过标准库, 使用POSIX标准提供的`write`函数. 这可以剩下一些包装函数的空间.

```c
#include <unistd.h>

int main(void) {
    write(0, "Hello!\n", 7);
    return 0;
}
```

```text
$ clang -std=c17 -Oz -static -o hello.c.elf hello.c
$ size ./hello.c.elf
   text    data     bss     dec     hex filename
 789451   23240   23016  835707   cc07b ./hello.c.elf
$ ls -Fsh ./hello.c.elf
888K ./hello.c.elf*
```

### 2.3. 8.3KB

手动调用POSIX syscall完成功能. 这样可以省去`main`函数和大部分包装函数的空间. 使用`strace`等工具可以观察到关键的系统调用.

```python
S_HELLO = "Hello!\n"
syscall(0x1, 0, S_HELLO, len(S_HELLO))  # write(stdout, S_HELLO, len(S_HELLO))
syscall(0x3C, 0)  # exit(0)
```

可以方便地将其转换为NASM汇编. 注意这里并不需要任何栈空间.

```asm
[bits 64]

global _start

section .text

_start:
    mov rax, 0x1
    mov rdi, 0
    mov rsi, s_hello
    mov rdx, len_s_hello
    syscall

    mov rax, 0x3c
    mov rdx, 0
    syscall

L_HLT:
    hlt
    jmp L_HLT

section .rdata
    align 2

s_hello:
    db 'Hello!', 0x0a, 0x00
len_s_hello: equ $ - s_hello
```

```text
$ nasm -f elf64 -o hello.naive.S.reloc.elf hello.naive.S
$ ld -static -o hello.naive.S.elf hello.naive.S.reloc.elf
$ strip --strip-all ./hello.naive.S.elf
$ size ./hello.naive.S.elf
   text    data     bss     dec     hex filename
     50       0       0      50      32 ./hello.naive.S.elf
$ ll ./hello.naive.S.elf
-rwxr-xr-x 1 mantlebao mantlebao 8.3K Apr 24 19:03 ./hello.naive.S.elf*
$ ./hello.naive.S.elf
Hello!
```

### 2.4. 4.3KB

重新选择指令并合并两个syscall基本块中重叠的部分. 这样可以省下一些字节. 将字符串放入`.text`段能够省下一些ELF元数据的空间.

```asm
[bits 64]

global _start

section .text

_start:
    xor rax, rax
    inc al
    xor rdi, rdi
    mov rsi, s_hello
    xor rdx, rdx
    mov dl, len_s_hello
L_NEXT:
    syscall
    mov al, 0x3c
    xor dx, dx
    jmp L_NEXT

s_hello:
    db 'Hello!', 0x0a
len_s_hello: equ $ - s_hello
```

```text
$ nasm -f elf64 -o hello.short.S.reloc.elf hello.short.S
$ ld -static -o hello.short.S.elf hello.short.S.reloc.elf
$ strip --strip-all ./hello.short.S.elf
$ size ./hello.short.S.elf
   text    data     bss     dec     hex filename
     39       0       0      39      27 ./hello.short.S.elf
$ ll ./hello.short.S.elf
-rwxr-xr-x 1 mantlebao mantlebao 4.3K Apr 24 19:09 ./hello.short.S.elf*
$ ./hello.short.S.elf
Hello!
```

### 2.5. 152B

手动构造ELF文件, 并将字符串放入ELF header的padding区内.

```asm
[bits 64]

C_VA_LOAD: equ 0x400000

_ELF_HDR:
    db 0x7f, 'E', 'L', 'F'
    db 2
    db 1
    db 1
    db 0
    db 0
L_S_HELLO:
    db 'Hello!', 0x0A
C_LEN_S_HELLO: equ $ - L_S_HELLO
    dw 2
    dw 0x3e
    dd 1
    dq C_VA_LOAD + _start
    dq _PROG_HDR
    dq 0
    dd 0
    dw 64
    dw 0x38
    dw 1
    dw 0x40
    dw 0
    dw 0

_PROG_HDR:
    dd 1
    dd 5
    dq 0
    dq C_VA_LOAD
    dq C_VA_LOAD
    dq _END
    dq _END
    dq 0x200000

_start:
    xor rax, rax
    inc al
    xor rdi, rdi
    mov rsi, C_VA_LOAD + L_S_HELLO
    xor rdx, rdx
    mov dl, C_LEN_S_HELLO
L_NEXT:
    syscall
    mov al, 0x3c
    xor dx, dx
    jmp L_NEXT

_CODE_END:

_END:
```

```text
$ nasm -f bin hello.S -o hello && chmod +x ./hello
$ size hello
   text    data     bss     dec     hex filename
      0       0       0       0       0 hello
$ objdump -x hello

hello:     file format elf64-x86-64
hello
architecture: i386:x86-64, flags 0x00000102:
EXEC_P, D_PAGED
start address 0x0000000000400078

Program Header:
    LOAD off    0x0000000000000000 vaddr 0x0000000000400000 paddr 0x0000000000400000 align 2**21
         filesz 0x0000000000000098 memsz 0x0000000000000098 flags r-x

Sections:
Idx Name          Size      VMA               LMA               File off  Algn
SYMBOL TABLE:
no symbols


$ ll ./hello
-rwxr-xr-x 1 mantlebao mantlebao 152 Apr 24 17:56 ./hello*
$ ./hello
Hello!
```

## 3. 结论与讨论

通过手动触发syscall, 手动优化重叠代码段, 并利用加载至内存的ELF header的空闲padding区域, 能够将最终ELF文件压缩至152字节. 如果使用更激进的压缩方式, 蔽日搜索已加载共享库区段中的可用gadget等方法, 可能达到进一步压缩代码字节数的效果.
