---
layout: post
title: 在龙架构上“养龙虾”
date: 2026-03-10T23:15:45+08:00
lang: zh
tags: topic:misc loongarch
---

近期以 *Claw 为代表的智能体非常流行，其中不乏 Rust 语言的实现。因此，我试着在运行 [Arch Linux for Loong64](https://loongarchlinux.lcpu.dev/) 的龙芯 3B6000 上“养”了一只龙虾，达到了不错的效果。

## 0. 前置条件

这是一篇笔记式博客，包含了多种仅适用于我本人系统环境的操作与考虑，其中有些已在文内标出，有些则不然。我的系统配置如下：

* **主板：** [Loongson-3B6000x1-7A2000x1-EVB](https://loongfans.cn/devices/loongson-xb612b0-v1.2)
* **内核：** [Linux 6.19.6-arch1-1-csmantle-aosc-main-16k](https://github.com/CSharperMantle/linux-csmantle)

如果你想跟随本篇博客进行操作，需要准备以下材料：

* 使用 Linux 系统与常见开发工具的经验；
   * 能理解每步操作的目的、效果及对系统安全的影响
   * 能不借助 <abbr title="大语言模型">LLM</abbr>，利用手册、文档、Wiki 或搜索引擎进行故障检修
* 一个正常的网络环境；
* 30 分钟以上、一两个小时为宜的空余时间；
   * 我在安装时花了一个下午，但主要是[在多个 *Claw 实现与部署方案之间不断试错](#i-花絮失败的尝试)
* Rust 编译器套件和 Cargo。
   * [龙架构的 Rust 平台支持已较为完善](https://doc.rust-lang.org/nightly/rustc/platform-support.html#:~:text=loongarch64-unknown-linux-gnu)，一般可以无痛原生编译。

## 1. 编译二进制

在 `/opt` 下创建目录并设置权限。我在这里选择将所有者设置为 `csmantle:wheel`、目录权限设为 `drwxr-sr-x`，是为了对齐 `/opt` 下软件全局所有的设计用途，实践中可以自行考量：

> 3.13. /opt : Add-on application software packages
> 
> 3.13.1. Purpose
> 
> `/opt` is reserved for the installation of add-on application software packages.
>
> -- <https://refspecs.linuxfoundation.org/FHS_3.0/fhs-3.0.html#optAddonApplicationSoftwarePackages>

```console
$ sudo mkdir -p /opt/zeroclaw
$ sudo chown -R csmantle:wheel /opt/zeroclaw
$ sudo find /opt/zeroclaw -type d -exec chmod 2755 {} \;
$ sudo setfacl -R -d -m u::rwx,g::w-x,o::r-x /opt/zeroclaw
```

进入目录下后进行克隆、签出并构建。我选择的是 v0.1.7 tag，这是当时最新的 tag，读者可以自行选择基提交。

```console
$ cd /opt/zeroclaw
$ git clone -- https://github.com/zeroclaw-labs/zeroclaw.git .
$ git checkout v0.1.7
```

进行构建。

```console
$ cargo build --release --locked
```

## 2. 准备容器

使用 [systemd-nspawn(1)](https://wiki.archlinux.org/title/Systemd-nspawn) 创建容器。

```console
$ sudo pacstrap -K -c /var/lib/machines/claw base vim less
$ sudo systemd-nspawn -D /var/lib/machines/claw
# logout
```

之后配置容器内网络。我这里选择使用 NAT 联网，留出 198.18.1.0/24 作为容器网段。使用 systemd-networkd 创建一个虚拟接口。

```console
$ cat <<EOF | sudo tee /etc/systemd/network/10-ve-br0.netdev
[NetDev]
Name=ve-br0
Kind=bridge
EOF
$ cat <<EOF | sudo tee /etc/systemd/network/80-ve-br0.network
[Match]
Name=ve-br0

[Link]
RequiredForOnline=no

[Network]
Address=198.18.1.1/24
DHCPServer=yes
IPv4Forwarding=yes
IPMasquerade=ipv4
ConfigureWithoutCarrier=yes
LLMNR=no
MulticastDNS=no

[DHCPServer]
PoolSize=64
DefaultLeaseTimeSec=1h
MaxLeaseTimeSec=1d
EOF
$ cat <<EOF | sudo tee /etc/systemd/nspawn/claw.nspawn
[Exec]
Boot=yes
ResolvConf=copy-host

[Network]
VirtualEthernet=yes
Bridge=ve-br0
EOF
```

之后配置防火墙允许 DHCP。我的机器上部署的是 [ufw](https://manpages.org/ufw/8)。

```console
$ sudo ufw allow in on ve-br0 to any port 67 proto udp
```

之后启动 systemd-networkd。这里有一个需要注意的地方：虽然 systemd-networkd 并不会抢占其他网络管理器（比如 NetworkManager(1)）管理的接口，但是其 wait-online 服务 [systemd-networkd-wait-online.service](https://www.man7.org/linux/man-pages/man8/systemd-networkd-wait-online.8.html) 依然会默认开启。如果你的 systemd-networkd **只** 管理了虚拟接口，由于虚拟接口永远不会 online，这个服务会超时失败。这时候需要将其禁用。

```console
$ sudo systemctl disable --now systemd-networkd-wait-online.service
$ sudo systemctl mask systemd-networkd-wait-online.service
$ sudo systemctl enable --now systemd-networkd.service
```

之后将编译好的二进制 bind 至容器内即可。

```plain-text
# /etc/systemd/nspawn/claw.nspawn
[Files]
BindReadOnly=/opt/zeroclaw/target/release/zeroclaw:/usr/local/bin/zeroclaw
BindReadOnly=/opt/zeroclaw:/opt/zeroclaw
```

## 3. 部署

进入容器，进行 onboard 并且自定义配置，设置服务。

```console
$ sudo machinectl list
$ sudo machinectl shell claw
# cat <<EOF >/etc/systemd/system/zeroclaw.service
[Unit]
Description=ZeroClaw

[Service]
Type=exec
ExecStart=/usr/local/bin/zeroclaw daemon
User=root
WorkingDirectory=/root
Restart=always

[Install]
WantedBy=multi-user.target
EOF
# zeroclaw onboard
# # Other steps...
# systemctl enable --now zeroclaw.service
```

在宿主容器内设置开机启动。

```console
$ sudo systemctl enable --now systemd-nspawn@claw.service
```

之后还可以在容器内配置代理、隧道、工具等，对容器本身还可以进行资源限制，不多赘述。

------

> 这些都是只很通用的部署步骤，任何一台 x86 Arch 都可以这么操作，跟龙架构有什么关系？

这才是这个部署流程的关键所在。龙架构生态已经能够大体支持无痛、无缝部署 ZeroClaw，体验上甚至可以与 x86 Arch 并驾齐驱。这离不开龙芯中科与整个龙芯爱好者社区的不懈努力。

当然，这篇帖子只是故事的一部分……

## i. 花絮：失败的尝试

我最开始尝试的实现是 [IronClaw](https://github.com/nearai/ironclaw)。实际上，在整个踩坑过程中的 90% 时间花在这个部分中。

首先尝试的是原生编译 IronClaw。遗憾的是其依赖 [Wasmtime](https://wasmtime.dev/) 的 JIT 后端 [Cranelift](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift) 并不支持龙架构。为 Cranelift 增加新的后端是一个很大的工作，且目前暂无公开社区努力。

之后尝试交叉编译至 x86_64 并使用 QEMU 模拟执行。首先尝试的目标是 `x86_64-unknown-linux-gnu`，但 <abbr title="Arch Linux for Loong64">Arch4Loong</abbr> 对非原生架构的支持十分不完善，缺少 ld 等多种必须运行时库。因此尝试 `x86_64-unknown-linux-musl`，静态编译 OpenSSL 后再使用 Cargo 编译项目。这条路径上的第一个问题是 <abbr title="Arch Linux for Loong64">Arch4Loong</abbr> 的 x86_64 binutils 和原生 binutils 并不兼容。后者使用 2.46，[提供 `libsframe.so.3`](https://archlinux.org/packages/core/x86_64/binutils/#:~:text=%20libsframe.so=3-64)，而前者版本为 2.45，需要 `libsframe.so.2`。对[相关 PKGBUILD](https://github.com/lcpu-club/loongarch-packages/blob/511f520ff4583ff80f448c530cc31003a0055425/x86_64-linux-gnu-binutils/PKGBUILD) 打补丁保留这个 soname 后可以正常工作：

```diff
diff --git a/x86_64-linux-gnu-binutils/PKGBUILD b/x86_64-linux-gnu-binutils/PKGBUILD
index 547876b..729ae63 100644
--- a/x86_64-linux-gnu-binutils/PKGBUILD
+++ b/x86_64-linux-gnu-binutils/PKGBUILD
@@ -3,7 +3,7 @@
 _target=x86_64-linux-gnu
 pkgname=$_target-binutils
 pkgver=2.45
-pkgrel=1
+pkgrel=2
 pkgdesc='A set of programs to assemble and manipulate binary and object files for 32-bit and 64-bit x86'
 arch=(loong64)
 url='https://www.gnu.org/software/binutils/'
@@ -90,7 +90,10 @@ package() {

   # Remove file conflicting with host binutils and manpages for MS Windows tools
   rm "$pkgdir"/usr/share/man/man1/$_target-{dlltool,windres,windmc}*
-  rm -rf "$pkgdir"/usr/lib
+  find "$pkgdir"/usr/lib -mindepth 1 \
+                         ! -name 'libsframe.so.2' \
+                         ! -name 'libsframe.so.2.0.0' \
+                         -delete

   rm -rf "$pkgdir"/usr/include
```

之后继续尝试静态编译后，编译产物在 QEMU 下和原生环境下始终出现段错误。再加上其令人担忧的代码质量、onboarding 体验、版本兼容性、修复 bug 的方式等种种因素，最终选择放弃部署 IronClaw。
