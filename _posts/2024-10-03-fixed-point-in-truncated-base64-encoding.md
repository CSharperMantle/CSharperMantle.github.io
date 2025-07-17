---
layout: post
title: "Fixed point in truncated Base64 encoding: analysis and proof with Z3"
date: 2024-10-03T16:05:08+08:00
lang: en
tags: topic:research encoding
use_mathjax: true
---

> 中文版本[见此]({% link _posts/2024-10-10-fixed-point-in-truncated-base64-encoding-zh.md %}).

## 1. Introduction

Base64 ([Wikipedia](https://en.wikipedia.org/wiki/Base64), [RFC 4648](https://datatracker.ietf.org/doc/html/rfc4648)) is a well-known encoding for turing arbitrary binary data into an alphanumeric ASCII string. It's basic idea is to reinterpret original data as characters in a $2^6 = 64$-membered alphabet. Due to the input characters being 6-bits and output ones being 8-bits (ASCII characters), the length of encoded data will be different from that of the original one. If we consider only the common part of input and output, it is possible to construct a $N$-membered string $S$ whose Base64-encoding $\mathrm{Base64}(S)$ has $S$ as its prefix, i.e. $\mathrm{Base64}(S)[0..N] = S$. We call such $S$'es "$N$-truncated fixed points" for Base64 in this blog post.

For a continuous transformation $T(\cdot): X \to X$, it is natural that if a recursive sequence $x_n = T(x_{n-1})$ converges to some value $x_\infty$, an *attracting fixed point* is located at that value. This is called the *fixed point iteration*. For $\mathrm{Base64}(\cdot)$, however, its domain (in bytes, $\mathbb{B}^N$) is very different from its codomain ($\mathbb{B}^{4\lceil N/3 \rceil}$), thus we cannot directly apply the fixed point concept above to it. If we only care about the first $N$ bytes of its output (*truncation*), we could reduce said problem to a normal fixed-point finding on a $N$-membered string space.

Drawing the conclusion from [Section 2](#2-experimental-analysis), one 72-truncated fixed point is 

```plain-text
Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBeFYy
```

The first 72 bytes of its encoding result is identical to itself. This can be verified manually; such an example using [CyberChef](https://github.com/gchq/CyberChef/) is given by [this snippet](https://gchq.github.io/CyberChef/#recipe=To_Base64('A-Za-z0-9%2B/%3D')Drop_bytes(72,64,true)&input=Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBeFYySkVUbGhoTVVwVVZtcEJlRll5).

<!-- seo-excerpt-separator -->

A few others do notice this phenomena when iterating $\mathrm{Base64}(\cdot)$. One of such examples is the one discovered by [@V1ll4n](https://github.com/VillanCh) in his guest post at [a paid knowledge base](https://t.zsxq.com/EhZSb). He described utilizing such fixed point as a probe in a vulnerability discovery context, where one can reliably spot controlled Base64 output without prior knowledge of original $S$, given enough encoding iterations. A [post](https://codegolf.stackexchange.com/questions/257680/base64-fixed-point) on StackExchange Code Golf challenges to find the most efficient way to calculate the $n$th character in this fixed point. Still, analysis of this fixed point phenomenon is limited in both quantity and depth.

## 2. Experimental analysis

We try to solve for such a fixed point after truncation with [Z3 Theorem Prover](https://github.com/Z3Prover/z3/wiki).

Firstly, we need to implement Base64 lookup table with Boolean logic. In that way, we can easily describe constraints in terms of Boolean equations, without the use of array selection, which are both hard to write and hard to solve.

We generate a truth table for this lookup process with Python. Then we use [espresso](https://en.wikipedia.org/wiki/Espresso_heuristic_logic_minimizer) minimizer to produce the minimal SOP expression for each output bit.

```python
TEMPLATE = """.i 6
.o 8
.ilb I5 I4 I3 I2 I1 I0
.ob  O7 O6 O5 O4 O3 O2 O1 O0
{table}
.e
"""

B64_LOOKUP = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

entries = [f"{i:06b} {B64_LOOKUP[i]:08b}" for i in range(2**6)]
table = TEMPLATE.format(table="\n".join(entries))
print(table)

with open("tt.espresso.in", "wt") as f:
    f.write(table)
```

The resulting truth table and SOP expressions are as follows.

```plain-text
.i 6
.o 8
.ilb I5 I4 I3 I2 I1 I0
.ob  O7 O6 O5 O4 O3 O2 O1 O0
000000 01000001
000001 01000010
000010 01000011
000011 01000100
000100 01000101
000101 01000110
000110 01000111
000111 01001000
001000 01001001
001001 01001010
001010 01001011
001011 01001100
001100 01001101
001101 01001110
001110 01001111
001111 01010000
010000 01010001
010001 01010010
010010 01010011
010011 01010100
010100 01010101
010101 01010110
010110 01010111
010111 01011000
011000 01011001
011001 01011010
011010 01100001
011011 01100010
011100 01100011
011101 01100100
011110 01100101
011111 01100110
100000 01100111
100001 01101000
100010 01101001
100011 01101010
100100 01101011
100101 01101100
100110 01101101
100111 01101110
101000 01101111
101001 01110000
101010 01110001
101011 01110010
101100 01110011
101101 01110100
101110 01110101
101111 01110110
110000 01110111
110001 01111000
110010 01111001
110011 01111010
110100 00110000
110101 00110001
110110 00110010
110111 00110011
111000 00110100
111001 00110101
111010 00110110
111011 00110111
111100 00111000
111101 00111001
111110 00101011
111111 00101111
.e
```

```plain-text
# espresso -s -o eqntott .\tt.espresso.in
# UC Berkeley, Espresso Version #2.3, Release date 01/31/88
# PLA is .\tt.espresso.in with 6 inputs and 8 outputs
# ON-set cost is  c=64(64) in=384 out=242 tot=626
# OFF-set cost is c=68(68) in=270 out=99 tot=369
# DC-set cost is  c=0(0) in=0 out=0 tot=0
# ESPRESSO      Time was 0.00 sec, cost is c=41(0) in=174 out=71 tot=245
O7 = ;

O6 = (!I5&!I4&I3&!I2&I1&I0) | (!I5&!I3&!I2&I1&I0) | (!I5&!I3&I2&I1&I0) | (
    I5&!I3&!I2&I1&!I0) | (!I4&I3&I2&I1&I0) | (!I5&I4&I3&!I2&I0) | (I5&!I3
    &!I2&!I1&!I0) | (!I5&!I4&I3&!I1&I0) | (I5&!I4&I3&I1&!I0) | (!I5&!I3
    &!I1&I0) | (I5&!I3&!I2&I0) | (I5&!I4&!I3&I2) | (!I5&I4&I3&I2) | (I5
    &!I4&!I1&!I0) | (I5&!I4&I3&I0) | (!I5&!I0);

O5 = (!I5&I4&I3&I2) | (I4&I3&I1) | (I5);

O4 = (!I5&I4&I3&!I2&!I1) | (I5&!I4&I3&I2) | (I5&I4&I3&I2&!I1) | (!I4&I3
    &I2&I1&I0) | (I5&!I4&I3&I1&!I0) | (I5&I4&I3&!I2) | (I5&!I4&I3&I0) | (
    I4&!I3);

O3 = (I5&!I4&I3&!I2&!I1&!I0) | (!I5&I4&I3&!I2&!I1) | (!I5&!I4&I3&!I2&I1
    &I0) | (!I5&!I3&I2&I1&I0) | (I5&I4&I3&I2&!I1) | (I5&!I3&!I2&I1&!I0) | (
    I5&I4&I3&I2&I1) | (!I5&!I4&I3&!I1&I0) | (!I5&!I4&I3&!I0) | (I5&!I3&!I2
    &I0) | (I5&!I4&!I3&I2);

O2 = (I5&!I4&I3&!I2&!I1&!I0) | (!I5&!I4&I3&!I2&I1&I0) | (!I5&!I4&I2&!I0) | (
    !I5&!I3&!I2&I1&I0) | (!I5&I4&I3&I2&I1) | (!I4&I2&I1&!I0) | (I4&I3&I2
    &I1&I0) | (!I5&!I3&I2&!I0) | (!I5&I2&!I1&I0) | (I5&!I3&!I2&!I1&!I0) | (
    I5&!I4&I2&I0) | (I5&I4&I3&!I2);

O1 = (!I5&I4&I3&I2&!I1&!I0) | (!I5&!I4&I1&!I0) | (I5&I4&I3&I1) | (!I5&I4
    &I3&!I2&I0) | (I4&I3&I2&I1&I0) | (!I5&!I3&I1&!I0) | (I5&!I3&!I2&!I1
    &!I0) | (!I5&!I4&I3&!I1&I0) | (!I5&!I3&!I1&I0) | (I5&I4&I2&I1) | (I5
    &!I4&!I1&!I0) | (I5&I1&I0);

O0 = (I5&I4&I3&I0) | (!I4&I2&I1&!I0) | (I5&!I3&!I2&I1&!I0) | (I5&I4&I3&I2
    &I1) | (I5&!I3&!I2&!I1&!I0) | (I5&I4&I2&I0) | (I5&!I4&I3&I1&!I0) | (
    I5&!I4&!I1&!I0) | (!I5&!I0);
```

We create symbolic constraints in Python and feed them to Z3. In the following code, we try to solve for a fixed point with $N = 72$. In fact, we can successfully find a fixed point for every $N$.

The solving script is given below.

```python
import typing as ty

import more_itertools as mit
import z3
from pwn import error, success


def base64_table(input: z3.BitVecRef) -> z3.BitVecRef:
    I0: z3.BitVecRef = z3.Extract(0, 0, input)
    I1: z3.BitVecRef = z3.Extract(1, 1, input)
    I2: z3.BitVecRef = z3.Extract(2, 2, input)
    I3: z3.BitVecRef = z3.Extract(3, 3, input)
    I4: z3.BitVecRef = z3.Extract(4, 4, input)
    I5: z3.BitVecRef = z3.Extract(5, 5, input)
    O7 = z3.BitVecVal(0, 1)
    O6 = (
        (~I5 & ~I4 & I3 & ~I2 & I1 & I0)
        | (~I5 & ~I3 & ~I2 & I1 & I0)
        | (~I5 & ~I3 & I2 & I1 & I0)
        | (I5 & ~I3 & ~I2 & I1 & ~I0)
        | (~I4 & I3 & I2 & I1 & I0)
        | (~I5 & I4 & I3 & ~I2 & I0)
        | (I5 & ~I3 & ~I2 & ~I1 & ~I0)
        | (~I5 & ~I4 & I3 & ~I1 & I0)
        | (I5 & ~I4 & I3 & I1 & ~I0)
        | (~I5 & ~I3 & ~I1 & I0)
        | (I5 & ~I3 & ~I2 & I0)
        | (I5 & ~I4 & ~I3 & I2)
        | (~I5 & I4 & I3 & I2)
        | (I5 & ~I4 & ~I1 & ~I0)
        | (I5 & ~I4 & I3 & I0)
        | (~I5 & ~I0)
    )
    O5 = (~I5 & I4 & I3 & I2) | (I4 & I3 & I1) | (I5)
    O4 = (
        (~I5 & I4 & I3 & ~I2 & ~I1)
        | (I5 & ~I4 & I3 & I2)
        | (I5 & I4 & I3 & I2 & ~I1)
        | (~I4 & I3 & I2 & I1 & I0)
        | (I5 & ~I4 & I3 & I1 & ~I0)
        | (I5 & I4 & I3 & ~I2)
        | (I5 & ~I4 & I3 & I0)
        | (I4 & ~I3)
    )
    O3 = (
        (I5 & ~I4 & I3 & ~I2 & ~I1 & ~I0)
        | (~I5 & I4 & I3 & ~I2 & ~I1)
        | (~I5 & ~I4 & I3 & ~I2 & I1 & I0)
        | (~I5 & ~I3 & I2 & I1 & I0)
        | (I5 & I4 & I3 & I2 & ~I1)
        | (I5 & ~I3 & ~I2 & I1 & ~I0)
        | (I5 & I4 & I3 & I2 & I1)
        | (~I5 & ~I4 & I3 & ~I1 & I0)
        | (~I5 & ~I4 & I3 & ~I0)
        | (I5 & ~I3 & ~I2 & I0)
        | (I5 & ~I4 & ~I3 & I2)
    )
    O2 = (
        (I5 & ~I4 & I3 & ~I2 & ~I1 & ~I0)
        | (~I5 & ~I4 & I3 & ~I2 & I1 & I0)
        | (~I5 & ~I4 & I2 & ~I0)
        | (~I5 & ~I3 & ~I2 & I1 & I0)
        | (~I5 & I4 & I3 & I2 & I1)
        | (~I4 & I2 & I1 & ~I0)
        | (I4 & I3 & I2 & I1 & I0)
        | (~I5 & ~I3 & I2 & ~I0)
        | (~I5 & I2 & ~I1 & I0)
        | (I5 & ~I3 & ~I2 & ~I1 & ~I0)
        | (I5 & ~I4 & I2 & I0)
        | (I5 & I4 & I3 & ~I2)
    )
    O1 = (
        (~I5 & I4 & I3 & I2 & ~I1 & ~I0)
        | (~I5 & ~I4 & I1 & ~I0)
        | (I5 & I4 & I3 & I1)
        | (~I5 & I4 & I3 & ~I2 & I0)
        | (I4 & I3 & I2 & I1 & I0)
        | (~I5 & ~I3 & I1 & ~I0)
        | (I5 & ~I3 & ~I2 & ~I1 & ~I0)
        | (~I5 & ~I4 & I3 & ~I1 & I0)
        | (~I5 & ~I3 & ~I1 & I0)
        | (I5 & I4 & I2 & I1)
        | (I5 & ~I4 & ~I1 & ~I0)
        | (I5 & I1 & I0)
    )
    O0 = (
        (I5 & I4 & I3 & I0)
        | (~I4 & I2 & I1 & ~I0)
        | (I5 & ~I3 & ~I2 & I1 & ~I0)
        | (I5 & I4 & I3 & I2 & I1)
        | (I5 & ~I3 & ~I2 & ~I1 & ~I0)
        | (I5 & I4 & I2 & I0)
        | (I5 & ~I4 & I3 & I1 & ~I0)
        | (I5 & ~I4 & ~I1 & ~I0)
        | (~I5 & ~I0)
    )
    return z3.Concat(O7, O6, O5, O4, O3, O2, O1, O0)


def base64_encode(x: ty.Sequence[z3.BitVecRef]) -> list[z3.BitVecRef]:
    def kernel(input: ty.Sequence[z3.BitVecRef]) -> list[z3.BitVecRef]:
        assert len(input) == 3
        input = input[0:3]
        I: tuple[z3.BitVecRef, ...] = (
            z3.Extract(7, 2, input[0]),
            z3.Concat(z3.Extract(1, 0, input[0]), z3.Extract(7, 4, input[1])),
            z3.Concat(z3.Extract(3, 0, input[1]), z3.Extract(7, 6, input[2])),
            z3.Extract(5, 0, input[2]),
        )
        O = [base64_table(i) for i in I]
        return O

    y = []
    for chunk in mit.chunked(x, 3, strict=False):
        yp = kernel(chunk + [z3.BitVecVal(0, 8)] * (3 - len(chunk)))
        if len(chunk) == 3:
            y.extend(yp)
        elif len(chunk) == 2:
            y.extend(yp[0:2] + [z3.BitVecVal(ord("="), 8)])
        else:
            y.extend(yp[0:1] + [z3.BitVecVal(ord("="), 8)] * 2)
    return y


N_TOTAL_LEN = 72

solver = z3.Solver()

x = [z3.BitVec(f"x_{i}", 8) for i in range(N_TOTAL_LEN)]
y = base64_encode(x)
for i in range(N_TOTAL_LEN):
    solver.add(y[i] == x[i])

if solver.check() != z3.sat:
    error("Unsat")
    exit(1)

result: list[ty.Any] = [0] * N_TOTAL_LEN
m = solver.model()
for d in m.decls():
    result[int(d.name()[2:])] = m[d].as_long()  # type: ignore

success(bytes(result).decode("ascii"))
```

We will now list all $N$-truncated fixed points for $N$ values between 1 and 72.

```plain-text
 1 V
 2 Vm
 3 Vm0
 4 Vm0w
 5 Vm0wd
 6 Vm0wd2
 7 Vm0wd2Q
 8 Vm0wd2Qy
 9 Vm0wd2QyU
10 Vm0wd2QyUX
11 Vm0wd2QyUXl
12 Vm0wd2QyUXlV
13 Vm0wd2QyUXlVW
14 Vm0wd2QyUXlVWG
15 Vm0wd2QyUXlVWGx
16 Vm0wd2QyUXlVWGxW
17 Vm0wd2QyUXlVWGxWV
18 Vm0wd2QyUXlVWGxWV0
19 Vm0wd2QyUXlVWGxWV0d
20 Vm0wd2QyUXlVWGxWV0d4
21 Vm0wd2QyUXlVWGxWV0d4V
22 Vm0wd2QyUXlVWGxWV0d4V1
23 Vm0wd2QyUXlVWGxWV0d4V1Y
24 Vm0wd2QyUXlVWGxWV0d4V1Yw
25 Vm0wd2QyUXlVWGxWV0d4V1YwZ
26 Vm0wd2QyUXlVWGxWV0d4V1YwZD
27 Vm0wd2QyUXlVWGxWV0d4V1YwZDR
28 Vm0wd2QyUXlVWGxWV0d4V1YwZDRW
29 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWM
30 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMV
31 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl
32 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3
33 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3W
34 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3Wk
35 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkR
36 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRS
37 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV
38 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV0
39 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01
40 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01W
41 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01Wb
42 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbD
43 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDN
44 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNX
45 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa
46 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1
47 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1J
48 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JT
49 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTV
50 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVj
51 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjA
52 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAx
53 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV
54 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2
55 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2J
56 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JE
57 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JET
58 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETl
59 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlh
60 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhh
61 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhM
62 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMU
63 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUp
64 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpU
65 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUV
66 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVm
67 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmp
68 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpB
69 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBe
70 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBeF
71 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBeFY
72 Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBeFYy
```

## 3. Theoretical analysis

If we consider all $N$-truncated fixed points as prefixes of a fixed point with an infinite length, we will be able to discuss the existence and uniqueness of this "prime" fixed point, shedding some lights on the structure of Base64 transformation.

**Existence.** From a view of functions, the alphabet lookup process of Base64 $f(\cdot): \\\{0, 1\\\}^6 \to \mathbb{A} \subset \mathbb{B}$ is a bijection, thus invertible, which means every component in its input can be expressed as some Boolean expression of its output. By writing out these expressions we can solve them as any other Boolean equations, which is exactly what we have done in [Section 2](#2-experimental-analysis).

**Uniqueness.** The uniqueness of this fixed point can be proved in an inductive approach.

For every integer $i \in [0, N)$, we try to state the uniquess of the solution to

$$\mathrm{Base64}(S)[i] = S[i].$$

Recall that the reinterpretation process is (rewriting group number $m = \lfloor i/4 \rfloor$, and symbol $\mathbin\Vert$ stands for bit-string concatenation):

$$
\mathrm{Base64}(S)[i] = \begin{cases}
    f\left(S\left[3m\right]\left(7,2\right)\right) & \text{if}\ i \equiv 0 \pmod{4}\\
    f\left(S\left[3m\right]\left(1,0\right) \mathbin\Vert S\left[3m+1\right]\left(7,4\right)\right) & \text{if}\ i \equiv 1 \pmod{4}\\
    f\left(S\left[3m+1\right]\left(3,0\right) \mathbin\Vert S\left[3m+2\right]\left(7,6\right)\right) & \text{if}\ i \equiv 2 \pmod{4}\\
    f\left(S\left[3m+2\right]\left(5,0\right)\right) & \text{if}\ i \equiv 3 \pmod{4}
\end{cases}
$$

It is not difficult to discover that $\mathrm{Base64}(S)[i]$ only depends on $S[j]$ for some $j \le i$. In this fixed point analysis, this is also equal to $\mathrm{Base64}(S)[j]$. If the Base64 sequence prior to $i$ is uniquely determined, then $\mathrm{Base64}(S)[i]$ will also be uniquely determined.

We now continue to prove that $\mathrm{Base64}(S)[0] = S[0]$ has a unique solution by contradiction.

```python
def base64_encode(...):
    # Same as Section 2.
    ...

solver = z3.Solver()

x = [z3.BitVec(f"x_{i}", 8) for i in range(3)]
y = base64_encode(x)

solver.add(x[0] == y[0])
assert solver.check() == z3.sat
m = solver.model()
x_0 = m[m.decls()[0]]

# Introducing contradiction
solver.add(x[0] != x_0)
assert solver.check() == z3.unsat, "Not unique"
```

Therefore, the first character of the fixed point is unique, and so are all subsequent characters in the fixed point.

## 4. Conclusion

In this blog post, we elaborate the existence and uniqueness of a fixed point in truncated Base64 encoding. We also provide a working proof-of-concept for finding $N$-truncated fixed point with arbitrary $N$. This fixed point of truncated Base64 has already seen application in some areas, such as serving as a blind probe in application vulnerability analysis. Nevertheless, this interesting phenomenon's full potential is yet to be exploited, and we would leave this task to future works.
