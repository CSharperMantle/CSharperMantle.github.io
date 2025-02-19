---
layout: post
title: "You can't eliminate useless stack allocations in Rust"
date: 2025-02-1908:14:26+08:00
lang: en
description: >-
    The shiny "language of the year" lacks such an important and widely-used feature.
tags: topic:dev programming-language rust
---

We write programs that manage large data structures quite often. On occasions, said data structures are just large, plain `struct`s spanning tens of MiBs. The stack space on most OSes is quite constrained, so putting such large objects onto the stack will almost certainly make it overflow, forcing the app to exit. Unluckily, Rust does not have a "safe" solution that avoids constructing the object on the stack first. All present workarounds are error-prone for deeply cascaded structures with non-trivial constructors.

This is exactly what happened during my recent simulation project. The data structure I used is largely depicted in the following pseudo-Rust:

```rust
struct SubSub1 {
    t: u32,
    c: i8,
    u: u8,
}

struct SubSub2<const N: usize> {
    table: [i8; N],
}

struct Sub1<const N0: usize, const N: usize, const C: usize> {
    t_0: SubSub2<N0>,
    tables: [[SubSub1; C]; N],
    bitarr: Box<[bool]>,
    l: [usize; N],
    ctr: usize,
    dir: bool,
}

struct Sub2<const L: usize, const N: usize, const M: usize> {
    w: [[[i8; L]; N]; M],
    w_0: [i8; M],
    bitarr: [bool; L],
    table: [u32; L],
}

struct Selector<const N: usize> {
    table: [i8; N],
}

struct Top<...> {
    sub_1: Sub1<N10, N1, C1>,
    sub_2: Sub2<L2, N2, M2>,
    selector: Selector<N_SEL>,
}
```

In reality, all of these objects have non-trivial initialization behavior. These `struct`s are so heavily parametrized that their exact behavior can be customized via zero-sized function objects.

But the main idea is: Although the object is quite large and may vary in behavior, *its size is known at compile time*. So let's use the following structure to represent this family of objects:

```rust
struct VeryLargeButStaticallySizedObject {
    data: [u8; {2 * 1024 * 1024}],
}

type MyObject = VeryLargeButStaticallySizedObject;
```

So initially I just constructed one `MyObject` on the stack and let it run.

```rust
fn main() {
    let top = MyObject::new(...);
    ...
}
```

It inevitably failed with stack overflow on my Windows.

```plain-text
PS D:\Workspace\project> cargo run            
   Compiling project v0.1.0 (D:\Workspace\project)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 2.55s
     Running `target\debug\project.exe`

thread 'main' has overflowed its stack
error: process didn't exit successfully: `target\debug\project.exe` (exit code: 0xc00000fd, STATUS_STACK_OVERFLOW)
```

So the solution is clear:

1. Increase the stack size.
2. Construct the object on the heap, not the stack.

Solution 1 is generally unfavorable since the way to adjust stack size varies from compiler to compiler, and from OS to OS. I would have to force my coworkers to type in a long command line to achieve this. Solution 2 would be much better. In languages like C++, this is as simple as one line:

```cpp
#include <memory>

auto my_obj = std::make_unique<MyObject>(...);
```

This call forwards all parameters to `MyObject`'s constructor, then initializes internal bookkeeping to automatically deallocate (in this case, calling [`std::default_delete`](https://en.cppreference.com/w/cpp/memory/default_delete) on) the object. No stack allocation is needed.

A more historical technique known as [placement new](https://en.cppreference.com/w/cpp/language/new#Placement_new) is also there to help in C++. It allows users to view arbitrary memory as the object's storage, and then run the constructor on it. But that kind of low-level operation is generally considered "unsafe" by Rust pros, so we don't talk about them.

So I tried to replicate `std::make_unique` in safe Rust. This is what I wrote at first:

```rust
fn main() {
    let top = Box::new(MyObject::new(...));
    ...
}
```

Running it with the "debug" profile, it failed once more. Looking at the generated assembly ([Godbolt link](https://godbolt.org/#g:!((g:!((g:!((h:codeEditor,i:(filename:'1',fontScale:14,fontUsePx:'0',j:1,lang:rust,selection:(endColumn:1,endLineNumber:17,positionColumn:1,positionLineNumber:17,selectionStartColumn:1,selectionStartLineNumber:17,startColumn:1,startLineNumber:17),source:'struct+VeryLargeButStaticallySizedObject+%7B%0A++++data:+%5Bu8%3B+2+*+1024+*+1024%5D,%0A%7D%0A%0Aimpl+MyObject+%7B%0A++++pub+fn+new()+-%3E+Self+%7B%0A++++++++Self+%7B+data:+%5B0%3B+2+*+1024+*+1024%5D+%7D%0A++++%7D%0A%7D%0A%0Atype+MyObject+%3D+VeryLargeButStaticallySizedObject%3B%0A%0A%23%5Bno_mangle%5D%0Apub+fn+fun()+-%3E+Box%3CMyObject%3E+%7B%0A++++Box::new(MyObject::new())%0A%7D%0A'),l:'5',n:'0',o:'Rust+source+%231',t:'0')),k:33.333333333333336,l:'4',n:'0',o:'',s:0,t:'0'),(g:!((h:compiler,i:(compiler:r1840,filters:(b:'0',binary:'1',binaryObject:'1',commentOnly:'0',debugCalls:'1',demangle:'0',directives:'0',execute:'1',intel:'0',libraryCode:'0',trim:'1',verboseDemangling:'0'),flagsViewOpen:'1',fontScale:14,fontUsePx:'0',j:1,lang:rust,libs:!(),options:'-C+opt-level%3D0+-g',overrides:!((name:stdver,value:c17)),selection:(endColumn:1,endLineNumber:1,positionColumn:1,positionLineNumber:1,selectionStartColumn:1,selectionStartLineNumber:1,startColumn:1,startLineNumber:1),source:1),l:'5',n:'0',o:'+rustc+1.84.0+(Editor+%231)',t:'0')),k:33.333333333333336,l:'4',n:'0',o:'',s:0,t:'0'),(g:!((h:output,i:(compilerName:'x86-64+gcc+14.2',editorid:1,fontScale:14,fontUsePx:'0',j:1,wrap:'1'),l:'5',n:'0',o:'Output+of+rustc+1.84.0+(Compiler+%231)',t:'0')),k:33.33333333333333,l:'4',n:'0',o:'',s:0,t:'0')),l:'2',n:'0',o:'',t:'0')),version:4)), I found the following code:

```asm
fun:
        mov     r11, rsp
        sub     r11, 2097152
.LBB8_3:
        sub     rsp, 4096
        mov     qword ptr [rsp], 0
        cmp     rsp, r11
        jne     .LBB8_3
        sub     rsp, 24
        lea     rdi, [rsp + 8]
        call    example::VeryLargeButStaticallySizedObject::new::h94705197ed0c48cf
        mov     edi, 2097152
        mov     esi, 1
        call    alloc::alloc::exchange_malloc::hed5e7d0e2c1c5709
        mov     qword ptr [rsp], rax
        jmp     .LBB8_2
        mov     rcx, rax
        mov     eax, edx
        mov     qword ptr [rsp + 2097160], rcx
        mov     dword ptr [rsp + 2097168], eax
        mov     rdi, qword ptr [rsp + 2097160]
        call    _Unwind_Resume@PLT
.LBB8_2:
        mov     rdi, qword ptr [rsp]
        lea     rsi, [rsp + 8]
        mov     edx, 2097152
        call    memcpy@PLT
        mov     rax, qword ptr [rsp]
        add     rsp, 2097176
        ret
```

`MyObject` is first constructed on the stack, before being moved into the `Box`! `Box`-ing the object does not eliminate the stack allocation.

But when I turn on optimizations with release profile, the stack allocation magically disappeared ([Godbolt link](https://godbolt.org/#g:!((g:!((g:!((h:codeEditor,i:(filename:'1',fontScale:14,fontUsePx:'0',j:1,lang:rust,selection:(endColumn:1,endLineNumber:17,positionColumn:1,positionLineNumber:17,selectionStartColumn:1,selectionStartLineNumber:17,startColumn:1,startLineNumber:17),source:'struct+VeryLargeButStaticallySizedObject+%7B%0A++++data:+%5Bu8%3B+2+*+1024+*+1024%5D,%0A%7D%0A%0Aimpl+MyObject+%7B%0A++++pub+fn+new()+-%3E+Self+%7B%0A++++++++Self+%7B+data:+%5B0%3B+2+*+1024+*+1024%5D+%7D%0A++++%7D%0A%7D%0A%0Atype+MyObject+%3D+VeryLargeButStaticallySizedObject%3B%0A%0A%23%5Bno_mangle%5D%0Apub+fn+fun()+-%3E+Box%3CMyObject%3E+%7B%0A++++Box::new(MyObject::new())%0A%7D%0A'),l:'5',n:'0',o:'Rust+source+%231',t:'0')),k:33.333333333333336,l:'4',n:'0',o:'',s:0,t:'0'),(g:!((h:compiler,i:(compiler:r1840,filters:(b:'0',binary:'1',binaryObject:'1',commentOnly:'0',debugCalls:'1',demangle:'0',directives:'0',execute:'1',intel:'0',libraryCode:'0',trim:'1',verboseDemangling:'0'),flagsViewOpen:'1',fontScale:14,fontUsePx:'0',j:1,lang:rust,libs:!(),options:'-C+opt-level%3D2+-g',overrides:!((name:stdver,value:c17)),selection:(endColumn:95,endLineNumber:18,positionColumn:95,positionLineNumber:18,selectionStartColumn:95,selectionStartLineNumber:18,startColumn:95,startLineNumber:18),source:1),l:'5',n:'0',o:'+rustc+1.84.0+(Editor+%231)',t:'0')),k:33.333333333333336,l:'4',n:'0',o:'',s:0,t:'0'),(g:!((h:output,i:(compilerName:'x86-64+gcc+14.2',editorid:1,fontScale:14,fontUsePx:'0',j:1,wrap:'1'),l:'5',n:'0',o:'Output+of+rustc+1.84.0+(Compiler+%231)',t:'0')),k:33.33333333333333,l:'4',n:'0',o:'',s:0,t:'0')),l:'2',n:'0',o:'',t:'0')),version:4)):

```asm
fun:
        push    rax
        mov     rax, qword ptr [rip + __rust_no_alloc_shim_is_unstable@GOTPCREL]
        movzx   eax, byte ptr [rax]
        mov     edi, 2097152
        mov     esi, 1
        call    qword ptr [rip + __rust_alloc@GOTPCREL]
        test    rax, rax
        je      .LBB0_1
        mov     edx, 2097152
        mov     rdi, rax
        xor     esi, esi
        pop     rax
        jmp     qword ptr [rip + memset@GOTPCREL]
.LBB0_1:
        mov     edi, 1
        mov     esi, 2097152
        call    qword ptr [rip + alloc::alloc::handle_alloc_error::ha0547c441587f574@GOTPCREL]
```

And this is the intended behavior.

Is there a way to permanently enable this "move elision"? Unfortunately, no. There are many discussions already on Rust forums:

* ["How to create large objects directly in heap"](https://users.rust-lang.org/t/how-to-create-large-objects-directly-in-heap/26405): Same problem in this 2019 post. The provided solution is basically "alloc, then do every field construction manually by filling in raw `u8`s." This is `unsafe`. Also, although it might be feasible for shallow objects, it will be a nightmare for deeper ones like those in my project.
* ["How to boxed struct with large size without stack-overflow?"](https://users.rust-lang.org/t/how-to-boxed-struct-with-large-size-without-stack-overflow/94961): Same question in this 2023 post. The solution given is basically the same as above.

Very interestingly, in the latter thread, one guy replied [the following reply](https://users.rust-lang.org/t/how-to-boxed-struct-with-large-size-without-stack-overflow/94961/14):

> "khimru" wrote in Jun 2023:
> 
> Is this practical question or an attempt to find an excuse to not use Rust?
> 
> Guaranteed copy elision is an interesting property, but it's C++17 property which means most C++ codebases don't use it.
> 
> Similarly the ability to create object on heap without unsafe code is something that is nice in theory but quite problematic in practice. But we may hope that in year 2034, when Rust would be as old as C++17, that would be a solved problem. We are not there yet, though.

Later, in reply to a user named "kpreid", "khimru" wrote [these](https://users.rust-lang.org/t/how-to-boxed-struct-with-large-size-without-stack-overflow/94961/16):

> "khimru" wrote in Jun 2023:
>
> That's why I asked if that's an attempt to show that Rust is not yet "done" (is there any language which is actually 100% done?) or some kind of practical issue.

Well, here I give you a practical case as you have requested. *This does happen from time to time, and Rust is surely not yet "done".*

In the end, I gave up and told all my users to adjust stack space as needed.

```plain-text
RUSTFLAGS="-C link-args=/STACK:4194304" cargo run
```
