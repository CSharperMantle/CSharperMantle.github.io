---
layout: post
title: "Upgrading VITS to PyTorch 2 on Windows"
date: 2023-06-14T07:08:25+08:00
lang: en
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

## 3. Utility scripts

These scripts are created during my optimization to VITS workflow. Note that they are all licensed under MIT with no warranties or guarantees, so you should adapt them to your specific case.

### WAV extraction from video

https://github.com/CSharperMantle/my_vits/tree/main/scripts/Extract-Wav-Ffmpeg.ps1

```powershell
<#
.SYNOPSIS
    Extract audio tracks in WAV from video files with FFMPEG.

.DESCRIPTION
    This script iterates over all files in given path and feeds them
    to FFMPEG. Extracted WAV contents are placed next to original
    video with the same base name. No format check is performed
    during this process.

.NOTES
    `ffmpeg.exe` should be in `$env:PATH` for this script to run
    normally.

    This script is licensed under a MIT license.
    Copyright (c) 2023 Rong Bao <baorong2005@126.com>
.PARAMETER Path
    Working path to find video files in.
.PARAMETER WhatIf
    Show operations without actually running.
#>

<#
 # Copyright (c) 2023 Rong Bao <baorong2005@126.com>
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
 #>

param (
    [Parameter(Mandatory = $true,
        Position = 0,
        ValueFromPipeline = $true,
        ValueFromPipelineByPropertyName = $true,
        HelpMessage = "Working path 1")]
    [Alias("PSPath")]
    [ValidateNotNullOrEmpty()]
    [string]
    $Path,

    [Parameter(Position = 1,
        HelpMessage = "Show operations without actually running")]
    [switch]
    $WhatIf
)

$files = Get-ChildItem -Path $Path -File
foreach ($f in $files) {
    $out_path = "$Path\$($f.BaseName).wav"

    if ($WhatIf) {
        Write-Output "ffmpeg.exe -i $($f.FullName) -vn $out_path"
    } else {
        ffmpeg.exe -i $($f.FullName) -vn $out_path
    }
}
```

### Filelist creation

https://github.com/CSharperMantle/my_vits/tree/main/scripts/Make-Filelist.ps1

```powershell
<#
.SYNOPSIS
    Match WAV audio files with their TXT transcriptions.

.DESCRIPTION
    This script iterates over all WAV files in given path, finding its
    TXT transcription file in the same path, whose name contains the base
    name of the WAV file as its prefix. It then produces a TXT filelist
    containing matched pairs with path to audio and content of transcription,
    separated by given delimiter.

.NOTES
    WAV files having multiple transcriptions will be skipped. Having only one
    contentless transcription will also cause the WAV file to be skipped.

    This script is licensed under a MIT license.
    Copyright (c) 2023 Rong Bao <baorong2005@126.com>

.PARAMETER Path
    Working path to find video files in.
.PARAMETER FilelistName
    Name of filelist to create.
.PARAMETER Delim
    Character used as delimiter.
.PARAMETER PunctChar
    Character substituting line breaks and spaces.
#>

<#
 # Copyright (c) 2023 Rong Bao <baorong2005@126.com>
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
 #>

param (
    [Parameter(Mandatory = $true,
        Position = 0,
        ValueFromPipeline = $true,
        ValueFromPipelineByPropertyName = $true,
        HelpMessage = "Working path")]
    [Alias("PSPath")]
    [ValidateNotNullOrEmpty()]
    [string]
    $Path,

    [Parameter(Mandatory = $true,
        Position = 1,
        HelpMessage = "Name for new filelist")]
    [Alias("FN")]
    [ValidateNotNullOrEmpty()]
    [string]
    $FilelistName,

    [Parameter(Mandatory = $false,
        Position = 2,
        HelpMessage = "Delimiter")]
    [Alias("D")]
    [ValidateNotNullOrEmpty()]
    [char]
    $Delim = "|",

    [Parameter(Mandatory = $false,
        Position = 3,
        HelpMessage = "Character for indicating punctuation")]
    [Alias("PC")]
    [ValidateNotNullOrEmpty()]
    [char]
    $PunctChar = ","
)

Write-Output $PunctChar

$filelist_items = [System.Collections.Generic.List[string]]::new()

$files = Get-ChildItem -Path $Path -File

$wav_files = $files | Where-Object { $_.Extension.ToLower() -eq ".wav" }
$txt_files = $files | Where-Object { $_.Extension.ToLower() -eq ".txt" }
foreach ($f in $wav_files) {
    $escaped_wav_name = [regex]::escape($f.BaseName)
    $matched_txt = $txt_files | Where-Object { $_.BaseName.Trim() -cmatch "^$escaped_wav_name.*$" }
    $matched_txt_count = $matched_txt | Measure-Object | ForEach-Object { $_.Count }
    if ($matched_txt_count -gt 1) {
        Write-Warning "$($f.Name): multiple transcriptions found, skipping"
        continue
    }
    
    $transcription = Get-Content -Path $matched_txt[0].FullName
    $transcription = $transcription -replace "\s+", "$PunctChar"
    if ($transcription.Length -eq 0) {
        Write-Warning "$($f.Name): transcription empty, skipping"
        continue
    }

    $filelist_items.Add("$($f.FullName)$Delim$transcription")
}

$final_content = $filelist_items -join [System.Environment]::NewLine
Set-Content -Path $FilelistName -Value $final_content
```

### Split audio on pause

https://github.com/CSharperMantle/my_vits/blob/main/scripts/split_on_pause.py

```python
# Copyright (c) 2023 Rong Bao <baorong2005@126.com>
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


import librosa as r
import soundfile as sf
import os

INPUT_WAV_FILE_PATH: str = R"[YOUR_FILE_PATH]"
WINDOW_LENGTH_SECONDS: float = 1
SILENCE_THRESHOLD: int = 50

if not os.path.isfile(INPUT_WAV_FILE_PATH):
    raise ValueError(f"{INPUT_WAV_FILE_PATH}: not a file")

audio_file_folder = os.path.split(INPUT_WAV_FILE_PATH)[0]
audio_file_base = os.path.splitext(os.path.basename(INPUT_WAV_FILE_PATH))[0]

audio_buffer, sample_rate = r.core.load(INPUT_WAV_FILE_PATH, sr=None)
print(f"File length: {audio_buffer.shape[0] / sample_rate * 1000.0}ms, SR {sample_rate}")

os.mkdir(os.path.join(audio_file_folder, audio_file_base))

for i, clip_range in enumerate(
        r.effects.split(
            y=audio_buffer,
            top_db=SILENCE_THRESHOLD,
            frame_length=int(sample_rate * WINDOW_LENGTH_SECONDS),
        )
):
    print(f"Chunk # {i}: {clip_range[0]} to {clip_range[1]}")
    chunk = audio_buffer[clip_range[0]: clip_range[1]]
    output_file_path = os.path.join(
        audio_file_folder, audio_file_base, f"{audio_file_base}-{i}#.wav"
    )
    sf.write(output_file_path, chunk, int(sample_rate))
    print(f"Chunk # {i}: exported")

```