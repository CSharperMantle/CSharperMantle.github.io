---
layout: post
title: "A parser for LoongArch instruction encoding table"
date: 2025-02-07T09:45:05+08:00
lang: en
description: >-
    Turn an AsciiDoc table of LoongArch instruction encodings into a
    machine-readable format.
tags: topic:dev snippet python loongarch
---

This script turns [the AsciiDoc source of "Appendix A: Table of Instruction Encoding"](https://github.com/loongson/LoongArch-Documentation/blob/e2fb720ef303fd57c27eb1c80d4722dc6b5763c9/docs/LoongArch-Vol1-EN/table-of-instruction-encoding.adoc) in the *LoongArch Reference Manual, Volume 1: Basic Architecture* (a rendered version can be found [here](https://loongson.github.io/LoongArch-Documentation/LoongArch-Vol1-EN.html#table-of-instruction-encoding)) into machine-readable CSV lines containing mnemonic name, args, and bit patterns. It is also available as [a GitHub Gist](https://gist.github.com/CSharperMantle/97bb92f8f9e3689b5c19e4c64ee56aeb).


```python
#!/usr/bin/env python3

# MIT License
#
# Copyright (c) 2025 Rong "Mantle" Bao <webmaster@csmantle.top>.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import csv
import enum
import io
import re
import sys

RE_LIT_BIT = re.compile(r"^\|(0|1)$")
RE_WILD_BITS = re.compile(r"^(\d+)\+\|.*$")


class State(enum.IntEnum):
    MNEMONIC = enum.auto()
    OPERAND = enum.auto()
    BITS = enum.auto()


state = State.MNEMONIC
mnemonic = ""
args = ""
bit_pat = ""
rem_bits = 32
insns = []
for l in filter(lambda l: len(l) > 0, map(lambda l: l.strip(), sys.stdin.readlines())):
    match state:
        case State.MNEMONIC:
            rem_bits = 32
            bit_pat = ""
            mnemonic = l.lstrip("| ")
            state = State.OPERAND
        case State.OPERAND:
            args = l.lstrip("| ")
            state = State.BITS
        case State.BITS:
            if m := RE_LIT_BIT.match(l):
                bit_pat += m.group(1)
                rem_bits -= 1
            elif m := RE_WILD_BITS.match(l):
                bit_pat += "?" * int(m.group(1))
                rem_bits -= int(m.group(1))
            if rem_bits == 0:
                insns.append((mnemonic, args, bit_pat))
            state = State.MNEMONIC if rem_bits == 0 else State.BITS

with io.StringIO(newline="") as f:
    writer = csv.writer(f)
    writer.writerow(["mnemonic", "args", "bit_pat"])
    writer.writerows(insns)
    print(f.getvalue())

```

To use this script, download a copy of Appendix A from the link given above. Once downloaded, strip all headings, table headers, and footers:

```plain-text
|CLO.W
|rd, rj
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|1
|0
|0
5+|rj
5+|rd

|CLZ.W
|rd, rj
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|0
|1
|0
|1
5+|rj
5+|rd

[...]
```

Then pipe it into the script. The CSV format will pipe out.

```csv
mnemonic,args,bit_pat
CLO.W,"rd, rj",0000000000000000000100??????????
CLZ.W,"rd, rj",0000000000000000000101??????????
[...]
```
