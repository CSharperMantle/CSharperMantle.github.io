---
layout: post
title: "Upgrading VITS to PyTorch 2 on Windows"
date: 2023-06-14 07:08:25 +0800
lang: en
description: This blog analyzes frequent pitfalls and workarounds for running VITS on Windows with PyTorch 2.
categories: machine-learning
---

## 0. Introduction

Many issues may arise in the process of upgrading software dependencies, especially for stepping widely from `torch == 1.6.0` to `torch == 2.0.1`, where many breaking changes has been shipped by the PyTorch team.

This article targets users who wish to run the famous [VITS](https://github.com/jaywalnut310/vits) by Kim, J. *et al.* with upgraded frameworks on Windows. Common issues, their solutions and workarounds, and various improvements will be discussed here.

In this blog, the following conventions will be used:

* `[vits]`: The location of VITS repository. If you clone VITS to `D:\my_path\vits`, then substitute `[vits]` with `D:\my_path\vits`.
* `[venv]`: The location of your selected Python environment or virtual environment. If you create a venv at `D:\my_venv`, then substitute `[venv]` with `D:\my_venv`.
* *Fix*: A solution to a specific issue that fixes the problem with little to no impact on performance.
* *Workaround*: A solution to a specific issue that fixes the problem with moderate to major impact on performance.

Note that all outputs given here is only an example. Actual line numbers and target triplets may vary.

## 1. Common build issues

### `error: could not create 'monotonic_align\core.cp310-win_amd64.pyd': No such file or directory`

#### Description

This error occurs while building optimized `monotonic_align` with Cython:

```sh
cd monotonic_align
python setup.py build_ext --inplace
```

```plain
Generating code
Finished generating code
copying build\lib.win-amd64-cpython-310\monotonic_align\core.cp310-win_amd64.pyd -> monotonic_align
error: could not create 'monotonic_align\core.cp310-win_amd64.pyd': No such file or directory
```

Skipping this step will lead to further `ModuleNotFoundError` while training or making inferences. For example,

```plain
Traceback (most recent call last):
  File "[vits]\train.py", line 26, in <module>
    from models import (
  File "[vits]\models.py", line 12, in <module>
    import monotonic_align
  File "[vits]\monotonic_align\__init__.py", line 4, in <module>
    from .monotonic_align.core import maximum_path_c
ModuleNotFoundError: No module named 'monotonic_align.monotonic_align'
```

#### Solution

**Fix:** Check that there is a directory `monotonic_align` in the directory `monotonic_align`, that is, the following PowerShell expression is true:

```powershell
Test-Path -Path '[vits]\monotonic_align\monotonic_align' -Type Container
```

If not, create one, then rerun build command.

**Workaround:** You can also complete abandon optimized Cython code to fix this issue, at the cost of performance. See [this comment on jaywalnut310/vits#63](https://github.com/jaywalnut310/vits/issues/63#issuecomment-1376975528) for how to apply this workaround.

## 2. Common runtime issues

### `IndexError: Dimension out of range (expected to be in range of [-1, 0], but got 1)`

#### Description

This is the major blocker for VITS to run on any `torch >= 1.8.0`. When running vanilla VITS on said versions, this error will eventually appear:

```plain
-- Process 0 terminated with the following error:
Traceback (most recent call last):
    [...]
IndexError: Caught IndexError in DataLoader worker process 0.
Original Traceback (most recent call last):
  File "[venv]\lib\site-packages\torch\utils\data\_utils\worker.py", line 198, in _worker_loop
    data = fetcher.fetch(index)
  File "[venv]\lib\site-packages\torch\utils\data\_utils\fetch.py", line 47, in fetch
    return self.collate_fn(data)
  File "[vits]\data_utils.py", line 114, in __call__
    torch.LongTensor([x[1].size(1) for x in batch]),
  File "[vits]\data_utils.py", line 114, in <listcomp>
    torch.LongTensor([x[1].size(1) for x in batch]),
IndexError: Dimension out of range (expected to be in range of [-1, 0], but got 1)
```

This error is caused by an update in behavior in `torch.stft()`. According to their [documentation](https://pytorch.org/docs/stable/generated/torch.stft.html#torch-stft):

> **WARNING**
>
> From version 1.8.0, `return_complex` must always be given explicitly for real inputs and *return_complex=False* has been deprecated. Strongly prefer *return_complex=True* as in a future pytorch release, this function will only return complex tensors.
>
> Note that `torch.view_as_real()` can be used to recover a real tensor with an extra last dimension for real and imaginary components.

This change caused this function to return a complex tensor, breaking VITS codebase expecting a real tensor with one more dimension.

#### Solution

**Fix:** Search for all references to `torch.stft()`. Add `return_complex=True` to their argument list. Then chain the result with `torch.view_as_real()`. Fixed code may appear like this:

```python
...
result = torch.stft(..., return_complex=True)
result = torch.view_as_real(result)
...
```

**Workaround:** Downgrade to `torch >= 1.6.0, < 1.8.0`.
