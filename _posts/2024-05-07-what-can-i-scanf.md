---
layout: post
title: "What can I scanf? Buffer out"
date: 2024-05-07 20:12:34 +0800
lang: en
description: >-
    In this short blog, we discuss the specs-defined, yet largely-ignored buffer behavior of C
    standard library function `scanf` when it fails to match.
author: Rong "Mantle" Bao
categories: misc
---

## 1. Description of problem

Explain the behavior of the following program under given inputs:

```c
// scanf_test.c

#include <stdio.h>

int main(void) {
    int ret;
    int x;
    while ((ret = scanf("%d", &x)) != EOF) {
        printf("ret=%d; x=%d\n", ret, x);
    }
    return 0;
}
```

Possible inputs:

```plain
1234
-1234
  6789
123example
example123
-
```

Compilation command:

```bash
$ gcc -std=c17 -Wall -Wextra -Wpedantic -O2 -g -fsanitize=address,undefined -o scanf_test ./scanf_test.c
```

## 2. Results

We analyze inputs group by group.

### 2.1. Input group 1

```plain
1234
-1234
  6789
```

As expected, the program stores the input value in `x` and waits for next line of input.

```bash
$ ./scanf_test
1234
ret=1; x=1234
^C
$ ./scanf_test
-1234
ret=1; x=-1234
^C
$ ./scanf_test
  6789
ret=1; x=6789
^C
$
```

### 2.2. Input group 2

```plain
123example
example123
```

Initially, when `123example\n` is input, the program starts to loop infinitely. We truncate the output to first 10 lines here.

```bash
$ echo "123example" | ./scanf_test | head -n 10
ret=1; x=123
ret=0; x=123
ret=0; x=123
ret=0; x=123
ret=0; x=123
ret=0; x=123
ret=0; x=123
ret=0; x=123
ret=0; x=123
ret=0; x=123
$ echo "example123" | ./scanf_test | head -n 10
ret=0; x=0
ret=0; x=0
ret=0; x=0
ret=0; x=0
ret=0; x=0
ret=0; x=0
ret=0; x=0
ret=0; x=0
ret=0; x=0
ret=0; x=0
$
```

In the first input, only once did `scanf` succeed in matching a `%d` and storing it into `x`. After consuming `"123"`, the leftover `"example"`cannot be matched by `%d` anymore. As expected, `scanf` does not modify the input buffer, causing all subsequent calls to fail (since `"example"` always fails to match and is left unconsumed). Thus, `scanf` will never encounter a buffer underflow, so it will never ask for user input, causing the infinite loop.

The second input is essentially the same as the first one.

### 2.3. Input group 3

```plain
-
```

This input is more interesting. At first glance it is obviously not a decimal, so intuitively it should not be matched by `%d` (which is indeed what happened). But this time, no infinite loops occur, and the program will (surprisingly) wait for next user input.

```bash
$ ./scanf_test
-
ret=0; x=0
9876
ret=1; x=9876
-
ret=0; x=9876
-9876
ret=1; x=-9876
-
ret=0; x=-9876
^C
$
```

The cause of this behavior is that `-` may signify a start of a negative decimal. Without consuming its next character, it is not possible to know whether it is a negative sign or an ordinary hyphen. Once consumed, `"-"` will not be pushed back to the stream. Thus, though the match always fails when reading `"-"`, the buffer will still underflow on the next call to `scanf` (since `"-"` is already consumed).

## 3. Discussion

Input buffers and input functions are fundamental to I/O, though some edge cases may be easily ignored. [Ju Hong Kim](https://zakuarbor.github.io/portfolio/) wrote in their blog post (<https://zakuarbor.github.io/blog/a-look-at-input-buffer-using-scanf/>) about the behavior described in [Section 2.1](#21-input-group-1) and [Section 2.2](#22-input-group-2). Even the glibc authors (or rather the Standards Committee) had made mistakes implementing their `scanf`s (see [glibc bug 1765](https://sourceware.org/bugzilla/show_bug.cgi?id=1765) and [glibc bug 12701](https://sourceware.org/bugzilla/show_bug.cgi?id=12701)).

I have not noticed the behavior in [Section 2.3](#23-input-group-3) until a recent introductory CTF game named Mini-L CTF 2024 (*link to be added*). The critical part of a Pwn challenge named "Ottoshop♿" is like this:

```c
long x;  // `x` is at the bottom of the stack

int n = ...;  // `n` is controlled by the attacker
for (int i = 0; i < n; i++) {
    scanf("%ld", &x + i)
}
```

Stack canary is enabled in this binary.

```plain
$ checksec --file /mnt/d/Workspace/rev/mini-l-2024/ottoshop/ottoshop
[*] '/mnt/d/Workspace/rev/mini-l-2024/ottoshop/ottoshop'
    Arch:     amd64-64-little
    RELRO:    Full RELRO
    Stack:    Canary found
    NX:       NX enabled
    PIE:      No PIE (0x400000)
```

We cannot find any ways to leak the canary, heaps are not initialized, and no `libc` leaks could be found. Thus, to hijack the return address, we must avoid destroying stack canary. In the above loop, the only way to solve this is to make the second write (to the canary) and the third write (to saved `rbp`) no-ops. Applying the techniques in [Section 2.3](#23-input-group-3), we can send the following input (in Python) to perform the attack:

```python
f"{0xdeadbeef}".encode("ascii")  # x; don't care
b"-\n"  # canary
b"-\n"  # saved `rbp`
f"{vaddr_gadget}".encode("ascii")  # return address
```
