---
layout: post
title: Setting up V8 development environment on Arch Linux for Loong64
date: 2026-10-20T18:05:20+08:00
lang: en
description: >-
    This took ~4.5 hours including cloning, downloading, and pruning failed exploration branches.
tags: topic:dev loongarch
---

> Note: This isn't intended to replace the official [*Checking out and building Chromium on Linux*](https://chromium.googlesource.com/chromium/src/+/HEAD/docs/linux/build_instructions.md) guide.

## 1. Prepare tools

First, install tools that are directly available for download.

```console
$ sudo pacman -S --needed base-devel direnv git clang lld ninja ccache rustup rust-bindgen rustfmt
$ rustup default nightly
```

Then, build and install the following AURs:

* [python311](https://aur.archlinux.org/packages/python311): No modifications to PKGBUILD are needed, apart from appending `loong64` to `arch`.
* [gn-git](https://aur.archlinux.org/packages/gn-git): As of this writing, the built GN version is r2599.f90c3d9df. Edit PKGBUILD so that only target `gn` is built. The diff to PKGBUILD should look like the following:

```diff
diff --git a/PKGBUILD b/PKGBUILD
index 38d46f408f2369b38b262c90a4c827d9497485ef..17b12e5f4ff7cffd4072d2b9342f1d7e2c2768be 100644
--- a/PKGBUILD
+++ b/PKGBUILD
@@ -3,10 +3,10 @@

 pkgname=gn-git
 pkgdesc='Meta-build system which generates Ninja build files'
-pkgver=r1682.a5bcbd72
+pkgver=r2599.f90c3d9df
 pkgrel=1
 license=('BSD')
-arch=('x86_64' 'i686')
+arch=('x86_64' 'i686' 'loong64')
 conflicts=(gn-bin gn)
 provides=(gn)
 depends=(gcc-libs)
@@ -23,17 +23,16 @@ pkgver () {

 prepare () {
        cd gn
-       patch -p1 < "${srcdir}/gcc-support.patch"
+       patch -Np1 -i "${srcdir}/gcc-support.patch"
 }

 build () {
        cd gn
-       CC=cc CXX=c++ AR=ar \
        CFLAGS="${CFLAGS} -pthread" \
        CXXFLAGS="${CXXFLAGS} -pthread" \
        LDFLAGS="${LDFLAGS} -pthread" \
                python build/gen.py --use-lto --no-strip
-       ninja -C out
+       ninja -C out gn
 }

 package () {
```

## 2. Set up workspace directory

Make an empty directory for containing all our future works. Let's name it `google-source`.

```console
$ mkdir google-source
$ cd google-source
```

**From now on, make sure that you have `cd`'ed into `google-source`, or the workspace directory you choose.**

## 3. Install depot_tools

```console
$ git clone https://chromium.googlesource.com/chromium/tools/depot_tools.git
```

This is not directly usable. We also need to set up various environment variables for it to work.

First, create a Python 3.11 venv, and install dependencies required by V8 according to [v8/vpython.toml](https://github.com/v8/v8/blob/0f6635bc048450967271587d56e595237fc470ff/vpython.toml):

```console
$ mkdir venv
$ /usr/bin/python3.11 -m venv venv/depot_tools
$ ./venv/depot_tools/bin/pip install six==1.15.0 coverage==7.3.1 pbr==3.0.0 filecheck==1.0.1 funcsigs==1.0.2 mock==2.0.0 setuptools==68.0.0 numpy==1.23.5 protobuf==3.19.3 requests==2.31.0 urllib3==1.26.6 idna==2.8 certifi==2020.11.8 charset-normalizer==2.0.4 pyfakefs==5.7.3
```

The versions are to be derived from vpython.toml when you check out your own copy of V8.

Then, create an .envrc containing the following:

```sh
prepend_path () {
    case ":$PATH:" in
        *:"$1":*)
            ;;
        *)
            export PATH="$1:${PATH}"
            ;;
    esac
}

prepend_path "$(pwd)"/depot_tools

export GIT_CONFIG_COUNT=2
export GIT_CONFIG_KEY_0='core.autocrlf'
export GIT_CONFIG_VALUE_0='false'
export GIT_CONFIG_KEY_1='core.filemode'
export GIT_CONFIG_VALUE_1='false'

export VPYTHON_BYPASS='manually managed python not supported by chrome operations'
export DEPOT_TOOLS_BOOTSTRAP_PYTHON3=0

. ./venv/depot_tools/bin/activate
```

Run `direnv allow` to make it effective. This activates our Python 3.11 venv for depot_tools whenever we `cd` into our workspace. Also, we use the `GIT_CONFIG_*` family of environment variables to apply Git configurations required by V8, so that our global configuration wouldn't be contaminated.

## 4. Fetch the source

Make an empty directory to contain our V8 checkout, let's name it "v8". Then run `fetch`.

```console
$ mkdir v8
$ cd v8
$ fetch v8
```

**This will fail midway.** Ignore the failure. We'll fix it up soon&trade;.

## 5. Apply vendored tool patches

V8 intends to make builds reproducible by vendoring *all* tools. This isn't possible on Loong64, since most tools don't have Loong64 builds ready in Google's servers. We need to gate them away to prevent fetching failures.

```diff
diff --git a/.gn b/.gn
index fcc0c855322ef64d77611216783e10d70e8915f9..75e8108785092d5da399cd2a795013bd42948566 100644
--- a/.gn
+++ b/.gn
@@ -9,7 +9,7 @@ buildconfig = "//build/config/BUILDCONFIG.gn"
 
 # The hermetic Python interpreter to use by default. Platforms without a
 # hermetic CPython CIPD package fallback to the system python3 on $PATH.
-if (host_cpu == "s390x" || host_cpu == "ppc64" || host_os == "zos") {
+if (host_cpu == "s390x" || host_cpu == "ppc64" || host_os == "zos" || host_cpu == "loong64") {
   script_executable = "python3"
 } else {
   script_executable = "//third_party/cpython3/host/bin/python3"
diff --git a/DEPS b/DEPS
index 743e15833fba4771044d76ac47fab6298bfb9032..63d68e6e6a2c87da427a48c893fd0d9258dc3d8e 100644
--- a/DEPS
+++ b/DEPS
@@ -172,7 +172,7 @@ deps = {
       }
     ],
     'dep_type': 'cipd',
-    'condition': 'host_os == "linux" and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64"',
+    'condition': 'host_os == "linux" and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64" and host_cpu != "loong64"',
   },
   'buildtools/mac': {
     'packages': [
@@ -202,7 +202,7 @@ deps = {
       }
     ],
     'dep_type': 'cipd',
-    'condition': '(host_os == "linux" or host_os == "mac" or host_os == "win") and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64" and (host_cpu != "arm64" or host_os == "mac")',
+    'condition': '(host_os == "linux" or host_os == "mac" or host_os == "win") and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64" and (host_cpu != "arm64" or host_os == "mac") and host_cpu != "loong64"',
   },
   # TODO(498118202): Use checkout_benchmarks here too.
   'test/benchmarks/data':
@@ -363,7 +363,7 @@ deps = {
         'sha256sum': 'ab8ec1e75c7f74565e9f893212262780abc9174363ce5f1ff670c415e9cd4147',
         'size_bytes': 57258740,
         'generation': 1791353523054521,
-        'condition': 'host_os == "linux"',
+        'condition': 'host_os == "linux" and host_cpu == "x64"',
       },
       {
         'object_name': 'Linux_x64/clang-tidy-llvmorg-24-init-7747-g62397f8b-67.tar.xz',
@@ -391,7 +391,7 @@ deps = {
         'sha256sum': 'c575a16aa6516a47ad58c6f66ea604d3ec183d9b7a6ca72139b10d01a3ade984',
         'size_bytes': 5924452,
         'generation': 1791353523760046,
-        'condition': '(checkout_linux or checkout_mac or checkout_android) and host_os == "linux"',
+        'condition': '(checkout_linux or checkout_mac or checkout_android) and host_os == "linux" and host_cpu == "x64"',
       },
       {
         'object_name': 'Mac/clang-llvmorg-24-init-7747-g62397f8b-67.tar.xz',
@@ -526,7 +526,7 @@ deps = {
       }
     ],
     'dep_type': 'cipd',
-    'condition': 'host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64"'
+    'condition': 'host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64" and host_cpu != "loong64"'
   },
   'third_party/partition_alloc': {
     'url': Var('chromium_url') + '/chromium/src/base/allocator/partition_allocator.git@' + Var('partition_alloc_version'),
@@ -557,7 +557,7 @@ deps = {
         'sha256sum': '6287ecced3bc5113122a88dbe15c910edec0828718423a67529c24de0f060e98',
         'size_bytes': 287212360,
         'generation': 1791299089231058,
-        'condition': 'host_os == "linux"',
+        'condition': 'host_os == "linux" and host_cpu == "x64"',
       },
       {
         'object_name': 'Mac/rust-toolchain-1edd55dcfcd573872c727fa3e086369a71661ee0-1125-llvmorg-24-init-7747-g62397f8b.tar.xz',
@@ -600,7 +600,7 @@ deps = {
         'sha256sum': '1472e8a5cfc4959f94ff18aa5ec864b07991d877995a563eeb4176e344a7fa59',
         'size_bytes': 22761568,
         'generation': 1791299091145399,
-        'condition': 'host_os == "linux"',
+        'condition': 'host_os == "linux" and host_cpu == "x64"',
       },
       {
         'object_name': 'Mac/rust-libclang-1edd55dcfcd573872c727fa3e086369a71661ee0-1125-llvmorg-24-init-7747-g62397f8b.tar.xz',
@@ -643,7 +643,7 @@ deps = {
         'version': Var('cpython3_version'),
       }
     ],
-    'condition': 'not build_with_chromium and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64"',
+    'condition': 'not build_with_chromium and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64" and host_cpu != "loong64"',
     'dep_type': 'cipd',
   },
   # Host platform package.
@@ -654,7 +654,7 @@ deps = {
         'version': Var('cpython3_version'),
       }
     ],
-    'condition': 'not build_with_chromium and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64"',
+    'condition': 'not build_with_chromium and host_cpu != "s390x" and host_os != "zos" and host_cpu != "ppc64" and host_cpu != "loong64"',
     'dep_type': 'cipd',
   },
   'third_party/zlib':
```

Note that exact lines might differ from your checkout thanks to time differences, but the idea holds.

After patching, re-sync the tree:

```console
$ # In google-source/v8
$ gclient sync
```

## 6. Configuration

```console
$ ARGS=(
>   'is_clang=true'
>   'clang_base_path="/usr"'
>   'clang_use_chrome_plugins=false'
>   'use_sysroot=false'
>   'use_lld=true'
>   'is_debug=true'
>   'symbol_level=2'
>   'v8_optimized_debug=true'
>   'clang_version="23"'
>   'treat_warnings_as_errors=false'
>   'rust_sysroot_absolute="/home/csmantle/.rustup/toolchains/nightly-loongarch64-unknown-linux-gnu"'
>   'rust_bindgen_root="/usr"'
>   'v8_metagen_libclang_so="/usr/lib/libclang.so"'
>   'v8_metagen_libclang_bindings_dir="/home/csmantle/workspace/google-source/v8/v8/third_party/llvm-libclang/bindings/python"'
> )
$ gn gen out/loong64.debug --args="${ARGS[*]}"
```

Adjust `clang_version=` to your system's Clang version. Also adjust paths accordingly.

## 7. Generate compile_commands.json

```console
$ tools/clang/scripts/generate_compdb.py -p out/loong64.debug >compile_commmands.json
```

**Congratulations!** You now have a working environment for V8 development.

## 8. Build and test

```console
$ ninja -C out/loong64.debug
$ tools/run-tests.py --outdir=out/loong64.debug
```
