---
layout: post
title: Setting up SpiderMonkey development environment on Arch Linux for Loong64
date: 2026-10-20T17:54:20+08:00
lang: en
description: >-
    This took ~30 minutes including cloning and downloading.
tags: topic:dev loongarch
---

> Note: This isn't intended to replace the official [*Getting Set Up To Work On The Firefox Codebase*](https://firefox-source-docs.mozilla.org/setup/index.html) guide.

## 1. Prepare tools

```console
$ sudo pacman -S --needed base-devel git clang lld ninja ccache rustup rust-bindgen rustfmt uv
$ rustup default stable
```

## 2. Bootstrap

Bootstrapping would setup Python environment for Mach, the build system for Firefox and SpiderMonkey, and install a couple of other dependencies.

```console
$ git clone https://github.com/mozilla-firefox/firefox.git
$ cd firefox
$ ./mach bootstrap
Mach and the build system store shared state in a common directory
on the filesystem. The following directory will be created:
[...]
Please choose the version of Firefox you want to build (see note above):
  1. Firefox for Desktop Artifact Mode [default]
  2. Firefox for Desktop
  3. GeckoView/Firefox for Android Artifact Mode
  4. GeckoView/Firefox for Android
  5. SpiderMonkey JavaScript engine
Your choice: 5
[...]
Would you like to run a few configuration steps to ensure Git is
optimally configured? (Yn): n
[...]
sccache allows speeding up subsequent builds by caching compilation
results. Note that the initial build will be slower, and local changes
that invalidate the cache will not benefit from it.

Would you like to enable sccache? (Yn): y
[...]
Paste the lines between the chevrons (>>> and <<<) into
/home/csmantle/workspace/mozilla-firefox-dev/mozconfig:

>>>
ac_add_options --with-ccache=sccache
# Build only the SpiderMonkey JS test shell
ac_add_options --enable-project=js

<<<

Your system should be ready to build SpiderMonkey JavaScript engine!
```

Then you're ready.

Note that during the process, Mach might prompt you with several Y/N questions, e.g.:

* *Would you like to enable build system telemetry?*
* *Will you be using agentic coding tools to work on Firefox?*
* *Will you be submitting commits to Mozilla?*
* ... etc.

You could answer honestly or casually, but note that you might see errors like the following if you answer "Y" for the "agentic coding tools" one:

```
Installing cargo tools: searchfox-cli, socorro-cli, stmo-cli, treeherder-cli, webspec-index...
Could not install searchfox-cli.
Could not install socorro-cli.
Could not install stmo-cli.
Could not install treeherder-cli.
Could not install webspec-index.
```

These are non-fatal, and you can always install them later with [`cargo binstall`](https://github.com/cargo-bins/cargo-binstall).

## 3. Customize mozconfig

I use the following mozconfig for debug builds. You could customize yours. Use `./mach configure --help` to see all options. Use the environment variable `MOZCONFIG=path/to/mozconfig` to temporarily switch config for each Mach invocation. 

```sh
mk_add_options AUTOCLOBBER=1

ac_add_options --with-ccache=sccache

ac_add_options --enable-project=js
ac_add_options --enable-debug
ac_add_options --enable-debug-symbols
ac_add_options --enable-optimize

ac_add_options --enable-address-sanitizer
ac_add_options --disable-jemalloc

ac_add_options --enable-jit
ac_add_options --enable-wasm-jspi

ac_add_options --enable-linker=mold
export CFLAGS='-march=native'
export CXXFLAGS='-march=native'
export LDFLAGS='-Wl,--emit-relocs'
```

## 4. Set up VSCode integration

```console
$ ./mach ide vscode
```

**Congratulations!** You now have a fully-working environment for SpiderMonkey development.

## 5. Build and test

```console
$ ./mach build
$ ./mach jit-test
$ ./mach jit-test --ion
$ ./mach jstests
$ ./mach jsapi-tests
```
