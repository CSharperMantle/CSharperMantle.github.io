---
layout: post
title: "截断Base64编码的不动点: 借助Z3的分析与证明"
date: 2024-10-10T08:07:54+08:00
lang: zh
categories: misc
use_mathjax: true
---

> An English version is available [here](/misc/2024/10/03/fixed-point-in-truncated-base64-encoding.html).

## 1. 导语

Base64 ([Wikipedia](https://en.wikipedia.org/wiki/Base64), [RFC 4648](https://datatracker.ietf.org/doc/html/rfc4648)) 是相当常见的编码格式, 可以将任意二进制数据至一个 ASCII 码子集, 其原理为将原始数据中的位视为 $2^6 = 64$ 元字母表中的元素下标. 显然, 由于输入为6位元素而输出为8位元素 (ASCII 字符), 数据在编码后会比原来更长. 若只考虑相同长度的部分 (前缀), 我们能够构造一个 $N$ 元串 $S$ 使得它的 Base64 编码结果 $\mathrm{Base64}(S)$ 以 $S$ 为前缀, 即 $\mathrm{Base64}(S)[0..N] = S$. 我们称此种 $S$ 为 Base64 编码的 "$N$ 截断不动点".

对于一个连续变换 $T(\cdot): X \to X$, 如果数列 $x_n = T(x_{n-1})$ 收敛于值 $x_\infty$, 我们能够自然地说该变换存在一个*吸引不动点*. 上述过程也被称为*不动点迭代*. 但是, 变换 $\mathrm{Base64}(\cdot)$ 的值域 ($\mathbb{B}^N$, 以字节计) 和它的陪域 ($\mathbb{B}^{4\lceil N/3 \rceil}$) 并不相同, 因此我们不能直接将分析中不动点的概念借用过来. 但如果我们只关心输出的前 $N$ 字节 (*截断*), 我们能够将上述问题转化为在 $N$ 元串空间上求一个变换的不动点的常规问题.

提前引用[第 2 节](#2-实验分析)的结论, 72 截断的不动点为

```plain-text
Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBeFYy
```

上述串经编码后的前 72 字节与它本身相同. 读者可亲自验证该结论; 我们也提供了使用 [CyberChef](https://github.com/gchq/CyberChef/) 的[验证示例](https://gchq.github.io/CyberChef/#recipe=To_Base64('A-Za-z0-9%2B/%3D')Drop_bytes(72,64,true)&input=Vm0wd2QyUXlVWGxWV0d4V1YwZDRWMVl3WkRSV01WbDNXa1JTVjAxV2JETlhhMUpUVmpBeFYySkVUbGhoTVVwVVZtcEJlRll5).

目前已有在迭代 $\mathrm{Base64}(\cdot)$ 时对该现象的报道. 其中一个例子是 [@V1ll4n](https://github.com/VillanCh) 在[一个付费知识星球](https://t.zsxq.com/EhZSb)的嘉宾帖中提到的现象. 该帖中展示, 在漏洞发现过程中可以利用此不动点作为探针, 能够在不知道待编码 $S$ 原始内容的前提下可靠地发现攻击者可控的 Base64 输出. StackExchange Code Golf 网站上的一个[帖子](https://codegolf.stackexchange.com/questions/257680/base64-fixed-point)尝试找出高效计算该不动点中第 $n$ 个字符的算法. 遗憾的是, 对该现象的分析总体而言在数量和深度上均有待提升.

## 2. 实验分析

我们首先尝试使用 [Z3 定理证明器](https://github.com/Z3Prover/z3/wiki)求解该不动点.

我们的第一步操作是用布尔逻辑实现 Base64 的查表过程, 这样我们就可以直接用布尔表达式描述待求解的约束, 不需要引入既难以编写又难以求解的数组元素选择语法.

我们首先使用 Python 生成查表过程的真值表, 然后使用 [espresso](https://en.wikipedia.org/wiki/Espresso_heuristic_logic_minimizer) 逻辑化简器来产生每个输出位的最简与或式.

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

该脚本输出的真值表与化简后的最简与或式如下.

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

我们在 Python 中构造符号约束, 将其导入 Z3. 下列代码中我们求解 $N = 72$ 时的不动点. 实际上, 我们将在[第 3 节](#3-理论分析)中证明, 对于任意的 $N$ 均可解出唯一的不动点.

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

为方便读者参考, 我们同时列出 $N$ 为 1 至 72 时的每个 $N$ 截断不动点.

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

## 3. 理论分析

如果我们将所有 $N$ 截断不动点视为一个无穷长度不动点串的前缀, 就可以更直接地讨论这个"原"不动点的存在性与唯一性, 以此反映 Base64 变换的一些特性.

**存在性.** 从函数视角看, Base64 的查表过程 $f(\cdot): \\\{0, 1\\\}^6 \to \mathbb{A} \subset \mathbb{B}$ 是一个双射, 因此它可逆. 这意味着输入中的每一个布尔分量都可以表示为关于输出中各分量的布尔表达式, 因此我们可以应用普通的布尔等式求解法进行求解. 实际上, 我们在[第 2 节](#2-实验分析)中已经通过求解的方式证明了至少存在一个原不动点.

**唯一性.** 使用数学归纳法证明.

对任意整数 $i \in [0, N)$, 待证

$$\mathrm{Base64}(S)[i] = S[i].$$

Base64 的编码过程可以下式表示 (记组号 $m = \lfloor i/4 \rfloor$, 符号 $\mathbin\Vert$ 意为位串的拼接):

$$
\mathrm{Base64}(S)[i] = \begin{cases}
    f\left(S\left[3m\right]\left(7,2\right)\right) & \text{if}\ i \equiv 0 \pmod{4}\\
    f\left(S\left[3m\right]\left(1,0\right) \mathbin\Vert S\left[3m+1\right]\left(7,4\right)\right) & \text{if}\ i \equiv 1 \pmod{4}\\
    f\left(S\left[3m+1\right]\left(3,0\right) \mathbin\Vert S\left[3m+2\right]\left(7,6\right)\right) & \text{if}\ i \equiv 2 \pmod{4}\\
    f\left(S\left[3m+2\right]\left(5,0\right)\right) & \text{if}\ i \equiv 3 \pmod{4}
\end{cases}
$$

不难发现 $\mathrm{Base64}(S)[i]$ 仅依赖于某些 $S[j]$ 且 $j \le i$. 由于研究的是不动点, 上述表达式也等价于 $\mathrm{Base64}(S)[j]$. 那么, 如果 $i$ 之前的 Base64 输出都是唯一的, 那么 $\mathrm{Base64}(S)[i]$ 也是唯一的.

下面我们使用反证法说明 $\mathrm{Base64}(S)[0] = S[0]$ 有且仅有一个解.

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

综上所述, 该不动点中的第一个字符是唯一的, 因此之后的所有字符也是唯一的.

## 4. 结论

在本文中, 我们详细说明了截断 Base64 编码中存在一个唯一的不动点, 并提供了求解任意 $N$ 截断不动点的可运行脚本. 该不动点已经在软件漏洞分析等领域得到了应用. 尽管如此, 这个有趣现象的深层潜力依然值得进一步挖掘, 我们期待有更多感兴趣者能够在这个方向做出更深入的工作.
