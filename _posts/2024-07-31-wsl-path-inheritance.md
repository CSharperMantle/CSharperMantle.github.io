---
layout: post
title: "Turning off $PATH inheritance in a WSL2 guest"
date: 2024-07-31 14:10:02 +0800
lang: en
description: >-
    For Windows builds higher than 17713, there is a convenient way to prevent
    the inheritance of $PATH on the host environment into guests. Inherited
    $PATH may lead to significantly-low performance on certain scenarios, such as
    tab completion and shell theming.
author: Rong "Mantle" Bao
categories: misc
---

## 1. Description of problem

Some operations involving searching `$PATH` are extremely slow. This could include very slow shell command execution, tab completion, and rendering of certain themes in [ohmyzsh](https://github.com/ohmyzsh/ohmyzsh) and [oh-my-bash](https://github.com/ohmybash/oh-my-bash/).

The `$PATH` environment variable is very long in said scenarios:

```bash
$ echo $PATH
/home/mantle/.local/bin:/home/mantle/.sdkman/candidates/gradle/current/bin:/home/mantle/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/usr/lib/wsl/lib:/mnt/c/Program Files/NVIDIA GPU Computing Toolkit/CUDA/v12.1/bin:/mnt/c/Program Files/NVIDIA GPU Computing Toolkit/CUDA/v12.1/libnvvp:/mnt/d/Program Files/Python311/Scripts/:/mnt/d/Program Files/Python311/: [SNIP] :/mnt/c/ProgramData/mingw64/mingw64/bin:/mnt/c/Users/Mantle/AppData/Roaming/npm:/mnt/d/bdist/floss-v3.1.0-windows:/mnt/c/Users/Mantle/.dotnet/tools:/home/mantle/.dotnet/tools
$ echo $PATH | wc -m -
3058 -
```

## 2. Solution

Open `/etc/wsl.conf` and append these lines:

```ini
[interop]
appendWindowsPath=false
```

Then restart WSL.

```powershell
> wsl.exe --shutdown
```

Observe the updated `$PATH`.

```bash
$ echo $PATH
/home/mantle/.local/bin:/home/mantle/.sdkman/candidates/gradle/current/bin:/home/mantle/dist/verible-v0.0-3638-ge3ef2a37/bin:/home/mantle/.cargo/bin:/usr/lib/ccache:/home/mantle/loongson-gnu-toolchain-8.3-x86_64-loongarch64-linux-gnu-rc1.2/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/usr/lib/wsl/lib:/home/mantle/.dotnet/tools
$ echo $PATH | wc -m -
395 -
```

## 3. Discussion

The solution is first found in [microsoft/WSL#1493](https://github.com/microsoft/WSL/issues/1493), and it initially there is an obscure registry key that controlled this behavior. Since Windows Build 17713, [Microsoft added a entry in `wsl.conf`](https://learn.microsoft.com/en-us/windows/wsl/release-notes#build-17713) that allows convenient control. Since iterating all direct descendent of all `$PATH` entries is a costly operation, especially for mounted host drives, disabling this behavior can significantly speedup related operations.
