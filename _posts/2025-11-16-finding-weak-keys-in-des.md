---
layout: post
title: "求解 DES 弱密钥"
date: 2025-11-16T13:03:45+08:00
lang: zh
tags: topic:research cryptography
use_mathjax: true
---

<style>
.theorem-label {
    padding-right: 1em;
}
</style>

[DES 加密算法存在四个弱密钥](https://en.wikipedia.org/wiki/Weak_key#Weak_keys_in_DES)，分别为：

* `0x0101010101010101`；
* `0xFEFEFEFEFEFEFEFE`；
* `0xE0E0E0E0F1F1F1F1`；
* `0x1F1F1F1F0E0E0E0E`。

它们均满足 $\forall x.\ \mathrm{DESEncrypt}(x, K_w) = \mathrm{DESDecrypt}(x, K_w)$。接下来我们将使用 [Z3](https://github.com/Z3Prover/z3/wiki) 求解所有的 $K_w$，以此证明弱密钥的存在性。

证明的第一步是将弱密钥存在性问题简化至对密钥编排（key schedule）性质的研究上。记16个轮密钥按顺序组成序列 $\mathrm{DESKeySched}(K) = \\{ k_i \\}$，我们首先证明以下引理：

------

<span class="theorem-label"><strong>引理</strong></span>$K$ 为弱密钥的充要条件为 $\mathrm{DESKeySched}(K)$ 构成回文。

<span class="theorem-label"><strong>证明</strong></span>由于 DES 算法为 Feistel 结构，可将加密、解密过程改写为：

$$
\begin{align}
\mathrm{DESEncrypt}(x, K) &= \mathrm{DESNetwork}(x, \mathrm{DESKeySched}(K)) \nonumber \\
&= \mathrm{DESNetwork}(x, \{ k_i \}) \nonumber \\
\mathrm{DESDecrypt}(x, K) &= \mathrm{DESNetwork}(x, \overline{\mathrm{DESKeySched}(K)}) \nonumber \\
&= \mathrm{DESNetwork}(x, \overline{\{ k_i \}}) \nonumber \\
\end{align}
$$

其中 $\overline{\\{ k_i \\}}$ 表示逆序。那么显然 $\forall x.\ \mathrm{DESEncrypt}(x, K_w) = \mathrm{DESDecrypt}(x, K_w)$ 等价于 $\\{ k_i \\} = \overline{\\{ k_i \\}}$，即轮密钥组成的序列构成回文。

------

由于 DES 的密钥编排仅涉及按位置换，可以较为平凡地使用 SMT 求解器实现，因此编写 Z3 脚本是不难的：

```python
#!/usr/bin/env python3

# SPDX-License-Identifier: BSD-3-Clause

import functools as ft

import z3


def des_keysched_round(i: int, s: z3.BitVecRef) -> tuple[z3.BitVecRef, z3.BitVecRef]:
    """
    Args:
        i: 1-indexed round count.
        s: Ci ++ Di, 56 bits.

    Returns:
        * ki without permutation but with dropped bits
        * s' for next iteration
    """
    ROT_AMOUNT = (1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1)
    ci, di = z3.Extract(55, 28, s), z3.Extract(27, 0, s)
    ci1, di1 = z3.RotateLeft(ci, ROT_AMOUNT[i - 1]), z3.RotateLeft(
        di, ROT_AMOUNT[i - 1]
    )
    s1 = z3.Concat(ci1, di1)
    # Ignore bits (1-indexed) 9, 18, 22, 25, 35, 38, 43, 54
    #             (0-indexed) 8, 17, 21, 24, 34, 37, 42, 53
    ki = z3.Concat(
        z3.Extract(55, 54, s1),
        z3.Extract(52, 43, s1),
        z3.Extract(41, 38, s1),
        z3.Extract(36, 25, s1),
        z3.Extract(23, 22, s1),
        z3.Extract(20, 18, s1),
        z3.Extract(16, 9, s1),
        z3.Extract(7, 0, s1),
    )
    return (ki, s1)


def des_pc1_inv(x: int) -> int:
    # fmt: off
    TABLE = (
        57, 49, 41, 33, 25, 17, 9,
        1, 58, 50, 42, 34, 26, 18,
        10, 2, 59, 51, 43, 35, 27,
        19, 11, 3, 60, 52, 44, 36,
        63, 55, 47, 39, 31, 23, 15,
        7, 62, 54, 46, 38, 30, 22,
        14, 6, 61, 53, 45, 37, 29,
        21, 13, 5, 28, 20, 12, 4,
    )
    # fmt: on
    bits = [(x >> i) & 1 for i in range(55, -1, -1)]
    new_bits = [0] * 64
    for i, ti in enumerate(TABLE):
        new_bits[ti - 1] = bits[i]
    for i in range(0, 64, 8):
        parity = ft.reduce(lambda acc, b: acc ^ b, new_bits[i : i + 7], 1)
        new_bits[i + 7] = parity
    return ft.reduce(lambda acc, b: (acc << 1) | b, new_bits)


s0 = z3.BitVec("s0", 56)

k = []
si = s0
for i in range(1, 16 + 1):
    ki, si = des_keysched_round(i, si)
    k.append(ki)

solver = z3.Solver()

assert len(k) == 16
for i in range(len(k) // 2):
    solver.add(k[i] == k[len(k) - i - 1])

sol = []
while solver.check() == z3.sat:
    m = solver.model()
    s0v = None
    for d in m.decls():
        if d.name() == "s0":
            s0v = m[d].as_long()
    assert s0v is not None
    sol.append(s0v)
    solver.add(s0 != z3.BitVecVal(s0v, 56))

for i, s in enumerate(sol):
    print(f"Solution {i}: {hex(des_pc1_inv(s))}")

```

运行后即可求得唯一的四个密钥，其产生的轮密钥序列构成回文：

```plain-text
> py.exe -3 ./des-weak-key.py
Solution 0: 0x101010101010101
Solution 1: 0xe0e0e0e0f1f1f1f1
Solution 2: 0xfefefefefefefefe
Solution 3: 0x1f1f1f1f0e0e0e0e
```

之后借助引理即可推出 DES 弱密钥存在，且上述四个密钥即为全部弱密钥。

