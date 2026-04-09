---
layout: post
title: 用龙架构 QEMU 启动自编译 Linux 内核与 Alpine rootfs
date: 2026-04-09T14:44:51+08:00
lang: zh
tags: topic:dev loongarch
---

## 0. 动机

上个月，学校的操作系统实验课要求在自行编译的 Linux <abbr title="内核">kernel</abbr> 上添加系统调用并进行验证。教案与教材上推荐的方法是购买一台 Linux 云服务器或创建虚拟机，在修改启动配置后用于实验。这种方法存在诸多缺点。替换实机启动内核需要对 <abbr title="引导程序">bootloader</abbr> 配置进行修改。此外，若选择云服务器，则需向提供商支付费用，且在遇到无法启动的情况时较为棘手；若选择自己创建虚拟机，则必须安装虚拟机管理软件、完整执行 Linux 发行版的安装流程，而后才能开始实验。虽然在 2026 年，每个步骤都正在向新手友好的方向改进，但这对于达成实验目标而言是额外的、不必要的复杂性。

为了解决这个问题，需要先了解一个可启动 Linux 操作系统在功能上的组成。不精确地讲，在机器上电后由固件和 <abbr title="引导程序">bootloader</abbr> 进行基本的初始化，然后将 <abbr title="内核">kernel</abbr> 加载至内存中。<abbr title="内核">Kernel</abbr> 探测硬件信息，初始化运行环境、文件系统与必需设备后，启动 PID 为 1 的用户进程（又称 [`init`](https://en.wikipedia.org/wiki/Init)），由它搭建最终的用户环境[^0]。固件、<abbr title="引导程序">bootloader</abbr>、<abbr title="内核">kernel</abbr>、`init`（以及其所在的文件系统，又称 <abbr title="根文件系统">rootfs</abbr>）四个组件相对独立，这是实验中能够替换 <abbr title="内核">kernel</abbr>、保持其他组件不变的原因。

[QEMU](https://qemu-project.gitlab.io/qemu/about/index.html) 是一系列模拟器，可以在应用或系统层面进行同架构或跨架构模拟。它支持 [Direct Linux Boot](https://qemu-project.gitlab.io/qemu/system/linuxboot.html#direct-linux-boot)，意味着只要提供了合适的 <abbr title="内核">kernel</abbr> 文件、<abbr title="根文件系统">rootfs</abbr> 镜像、适用于目标架构的固件，就可以使用一行命令启动一个精简但完整的虚拟机，无需复杂的配置流程。

## 1. 搭建 <abbr title="根文件系统">rootfs</abbr> 镜像

由于内核与其上 <abbr title="根文件系统">rootfs</abbr> 相对独立，我们可以自由选择喜欢的 <abbr title="根文件系统">rootfs</abbr>，这也将在很大程度上决定启动后的发行版。这里选择 [Alpine Linux](https://alpinelinux.org/)，它是一个精简发行版，需要的存储空间与运行占用资源都较少。

首先创建一个空镜像文件并挂载。我选择的文件名是 `~/alpine-rootfs-qemu-2.img`，大小 64M，挂载到 `/mnt/alpine-rootfs`。这里 dd(1) 的 `bs` 和 `count` 只要乘积对就可以，因为我们实际上并不是在做裸磁盘操作，只是创建一个文件而已。

```console
$ dd if=/dev/zero of=~/alpine-rootfs-qemu-2.img bs=64M count=1
1+0 records in
1+0 records out
67108864 bytes (67 MB, 64 MiB) copied, 0.124744 s, 538 MB/s
$ mkfs.ext4 -F ~/alpine-rootfs-qemu-2.img
mke2fs 1.47.4 (6-Mar-2025)
Discarding device blocks: done
Creating filesystem with 65536 1k blocks and 16384 inodes
Filesystem UUID: eb760f6e-1a4b-4cc7-a0e2-ae4c88786cb6
Superblock backups stored on blocks:
        8193, 24577, 40961, 57345

Allocating group tables: done
Writing inode tables: done
Creating journal (4096 blocks): done
Writing superblocks and filesystem accounting information: done
$ sudo mount --mkdir -o loop ~/alpine-rootfs-qemu-2.img /mnt/alpine-rootfs
$
```

下载软件源的密钥文件。由于我使用的是龙架构平台，官方脚本只预装了 x86-64 平台的软件源密钥，所以需要提前下载好龙架构的密钥。获得密钥的最快方式是从[官方的 <abbr title="根文件系统">rootfs</abbr> 压缩包](https://alpinelinux.org/downloads/)中解压。我选择解压到 `/tmp/alpine/` 下，因为在创建完成后就不需要这个密钥文件了。

> **为什么不直接使用官方 <abbr title="根文件系统">rootfs</abbr> 压缩包？**
>
> 因为官方的 <abbr title="根文件系统">rootfs</abbr> 压缩包是为了 [chroot(1)](https://www.man7.org/linux/man-pages/man1/chroot.1.html) 设计的，不包含 init 程序，无法作为独立的操作系统在虚拟机内启动。

```console
$ pushd /tmp/
$ wget https://dl-cdn.alpinelinux.org/alpine/v3.23/releases/loongarch64/alpine-minirootfs-3.23.3-loongarch64.tar.gz
$ mkdir alpine
$ tar -xf alpine-minirootfs-3.23.3-loongarch64.tar.gz -C alpine
$ cat /tmp/alpine/etc/apk/keys/*
-----BEGIN PUBLIC KEY-----
[...]
-----END PUBLIC KEY-----
$ popd
$
```

使用 [alpine-make-rootfs](https://github.com/alpinelinux/alpine-make-rootfs) 脚本构建 <abbr title="根文件系统">rootfs</abbr>。完成后卸载磁盘即可。

```console
$ sudo ./alpine-make-rootfs --keys-dir /tmp/alpine/etc/apk/keys -p alpine-base -p vim -p strace -p fastfetch -- /mnt/alpine-rootfs
[...]
OK: 1966 KiB in 8 packages
( 1/33) Installing bridge (1.5-r5)
( 2/33) Installing ifupdown-ng (0.12.1-r7)
( 3/33) Installing openrc-user (0.63-r1)
( 4/33) Installing libcap2 (2.77-r0)
( 5/33) Installing openrc (0.63-r1)
  Executing openrc-0.63-r1.post-install
[...]
Executing busybox-1.37.0-r30.trigger
OK: 49.1 MiB in 41 packages
[...]
$
```

完成后卸载磁盘。

```console
$ sudo umount /mnt/alpine-rootfs
$
```

## 2. 准备内核文件

构建内核，得到内核文件。在龙平台上内核文件为 `arch/loongarch/boot/vmlinuz.efi`，在 x86-64 上为 `arch/x86/boot/bzImage`，其他平台同理，需自行确认。

## 3. 启动虚拟机

使用 qemu-system-loongarch64(1) 或相对应平台的系统级模拟器，指定内存大小（我这里选的是 1GiB）、固件文件、内核文件路径、磁盘镜像后即可启动。

第一步是使用一个简单的 shell，对 root 用户设置密码，并在串口 `ttyS0` 启用输入输出。设置完后使用 Ctrl-A+X 强制退出 QEMU，因为目前 shell 是 PID 1 进程，若直接 exit 会引发 kernel panic 并重启。

```console
$ qemu-system-loongarch64 -machine virt -cpu la464 -m 1G -bios /usr/share/edk2/loongarch64/QEMU_EFI.fd -kernel ~/dist/linux-arch/arch/loongarch/boot/vmlinuz.efi -drive file=~/alpine-rootfs-qemu-2.img,format=raw,if=virtio -append 'loglevel=7 root=/dev/vda rw console=ttyS0,115200 init=/bin/sh' -nographic
[...]
[    2.325567] Run /bin/sh as init process
~ # passwd
Changing password for root
New password:
Retype password:
passwd: password for root changed by root
~ # sed -i 's/^#ttyS0/ttyS0/' /etc/inittab
~ #
(C-a X)
$ 
```

参数的含义如下：

* `-machine virt`、`-cpu la464`：设置模拟的 CPU 型号与平台
* `-m 1G`：给虚拟机分配 1GiB 内存
* `-bios /usr/share/edk2/loongarch64/QEMU_EFI.fd`：设置 BIOS 文件的路径
* `-kernel ~/dist/linux-arch/arch/loongarch/boot/vmlinuz.efi`：设置内核文件路径
* `-drive file=~/alpine-rootfs-qemu-2.img,format=raw,if=virtio`：设置磁盘挂载参数
  * `file=~/alpine-rootfs-qemu-2.img`：设置磁盘文件在宿主上的路径
  * `format=raw`：格式为裸镜像，直接包含文件系统层数据，没有封装容器
  * `if=virtio`：挂载为 VirtIO-BLK 磁盘，虚拟机内设备路径为 `/dev/vd*` [^1] [^2]
* `-append 'loglevel=7 root=/dev/vda rw console=ttyS0,115200 init=/bin/sh'`：添加内核命令行参数[^3]
  * `loglevel=7`：设置日志输出为 `KERN_DEBUG` 级别
  * `root=/dev/vda`：设置 <abbr title="根文件系统">rootfs</abbr> 的设备路径
  * `rw`：将 <abbr title="根文件系统">rootfs</abbr> 挂载为可读可写
  * `console=ttyS0,115200`：设置输出到串口 `ttyS0` 并使用 115200 波特率
  * `init=/bin/sh`：使用 `/bin/sh` 作为 init 进程
* `-nographic`：

之后，将 init 在内核命令行中换为正常的 `/sbin/init`，即可进入正常的 Alpine 系统。

```console
$ qemu-system-loongarch64 -machine virt -cpu la464 -m 1G -bios /usr/share/edk2/loongarch64/QEMU_EFI.fd -kernel ~/dist/linux-arch/arch/loongarch/boot/vmlinuz.efi -drive file=~/alpine-rootfs-qemu-2.img,format=raw,if=virtio -append 'loglevel=7 root=/dev/vda rw console=ttyS0,115200 init=/sbin/init' -nographic
[...]
[    2.350173] Run /sbin/init as init process

   OpenRC 0.63 is starting up Linux 6.19.6-arch1-hdu-dirty (loongarch64)
[...]
Welcome to Alpine Linux 3.23
Kernel 6.19.6-arch1-hdu-dirty on loongarch64 (/dev/ttyS0)

(none) login: root
Password:
Welcome to Alpine!

The Alpine Wiki contains a large amount of how-to guides and general
information about administrating Alpine systems.
See <https://wiki.alpinelinux.org/>.

You can setup the system with the command: setup-alpine

You may change this message by editing /etc/motd.

login[195]: root login on 'ttyS0'
(none):~# fastfetch
       .hddddddddddddddddddddddh.           root@(none)
      :dddddddddddddddddddddddddd:          -----------
     /dddddddddddddddddddddddddddd/         OS: Alpine Linux v3.23 loongarch64
    +dddddddddddddddddddddddddddddd+        Kernel: Linux 6.19.6-arch1-hdu-dirty
  `sdddddddddddddddddddddddddddddddds`      Uptime: 35 seconds
 `ydddddddddddd++hdddddddddddddddddddy`     Packages: 41 (apk)
.hddddddddddd+`  `+ddddh:-sdddddddddddh.    Shell: sh
hdddddddddd+`      `+y:    .sddddddddddh    Terminal: vt100
ddddddddh+`   `//`   `.`     -sddddddddd    CPU: Loongson-3A5000 @ 2.00 GHz
ddddddh+`   `/hddh/`   `:s-    -sddddddd    Memory: 102.59 MiB / 879.08 MiB (12%)
ddddh+`   `/+/dddddh/`   `+s-    -sddddd    Swap: Disabled
ddd+`   `/o` :dddddddh/`   `oy-    .yddd    Disk (/): 50.89 MiB / 54.72 MiB (93%) - ext4
hdddyo+ohddyosdddddddddho+oydddy++ohdddh    Locale: C.UTF-8
.hddddddddddddddddddddddddddddddddddddh.
 `yddddddddddddddddddddddddddddddddddy`
  `sdddddddddddddddddddddddddddddddds`
    +dddddddddddddddddddddddddddddd+
     /dddddddddddddddddddddddddddd/
      :dddddddddddddddddddddddddd:
       .hddddddddddddddddddddddh.
(none):~#
```

此时虚拟机已经可用，可以正常使用 poweroff(1) 等通用方法进行管理。也可以在宿主机中重新挂载虚拟磁盘来修改磁盘内容。

有需要的可以删除刚才下载的临时文件。

```console
$ rm -rf /tmp/alpine*
$
```

[^0]: 准确的介绍可以参考 <https://wiki.archlinux.org/title/Arch_boot_process> 或其他发行版的相关文档。
[^1]: <https://www.kernel.org/doc/Documentation/admin-guide/devices.txt>
[^2]: <https://serverfault.com/questions/803388/what-is-the-difference-between-dev-vda-and-dev-sda>
[^3]: 详见 <https://www.kernel.org/doc/html/v4.14/admin-guide/kernel-parameters.html>。
