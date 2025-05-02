---
layout: post
title: "Numbers as expressions: demo with Z3"
date: 2025-05-02T19:08:57+08:00
lang: zh
tags: topic:misc snippet python
---

A while ago, I saw [an interesting post](https://t.me/abcthoughts/5957) from a Telegram channel I subscribed to. Briefly, it said:

> With these constants defined...
>
> ```javascript
> const a = -3 / 80;
> const e = 1;
> const f = 5;
> const g = 8 / 3;
> const h = 9 / 10;
> const i = 1;
> const l = 11 / 3;
> const n = 3;
> const o = 1 / 3;
> const r = 1;
> const s = 7 / 3;
> const t = 10 / 3;
> const u = 12 / 5;
> const v = 1;
> const w = 9 / 5;
> const x = 18 / 7;
> const z = 0;
> ```
>
> ... you can write numbers directly and perform arithmetic on it!
>
> ```javascript
> console.log(t*w*o + n*i*n*e)
> // 11
> console.log(e*l*e*v*e*n - f*i*v*e)
> // 6
> ```

We can use one of the many nonlinear solvers to produce a number of feasible solutions, with arbitrary number of words taken into consideration. My version uses [Z3.py](https://pypi.org/project/z3-solver/) and defines "zero" to "nine".

```python
import string

import z3

ALPHABET = {ch: z3.Real(f"{ch}") for ch in string.ascii_lowercase}
VALUES = {
    "zero": 0,
    "one": 1,
    "two": 2,
    "three": 3,
    "four": 4,
    "five": 5,
    "six": 6,
    "seven": 7,
    "eight": 8,
    "nine": 9,
}

solver = z3.Solver()

for word, value in VALUES.items():
    expr: z3.ArithRef = z3.IntVal(1)
    for ch in word:
        assert ch in ALPHABET
        expr = expr * ALPHABET[ch]  # type: ignore
    solver.add(expr == value)

assert solver.check() == z3.sat
model = solver.model()
for d in model.decls():
    name = d.name()
    value = model[d]
    assert isinstance(value, z3.RatNumRef)
    locals()[name] = value.as_fraction()
```

It can be run as follows and produce the desired output:

```python
# python -i alpha_numeric.py
>>> o*n*e + t*w*o
Fraction(3, 1)
>>> (t*h*r*e*e) / (f*o*u*r)
Fraction(3, 4)
>>> n*i*n*e - s*e*v*e*n
Fraction(2, 1)
>>>
```

**Open question:** What is the maximum number of consecutive "words" that can be added to this nonlinear system while maintaining its compatibility (i.e., ensuring it has at least one solution)?
