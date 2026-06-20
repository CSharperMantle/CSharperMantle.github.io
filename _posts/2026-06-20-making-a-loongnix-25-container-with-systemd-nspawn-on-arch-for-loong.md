---
layout: post
title: Making a Loongnix 25 container with systemd-nspawn on Arch Linux for Loong64
date: 2026-06-20T15:58:18+08:00
lang: en
tags: topic:dev loongarch
---

[Loongnix](https://www.loongnix.cn) is LoongArch's reference Linux distribution. Since it's derived from Debian, it should not be hard to make a rootfs using debootstrap(8). However, it turns out to be less straightforward than expected.

[There is a paragraph](https://docs.loongnix.cn/loongnix/faq/%E6%93%8D%E4%BD%9C%E7%B3%BB%E7%BB%9F/%E6%A1%8C%E9%9D%A2%E6%93%8D%E4%BD%9C%E7%B3%BB%E7%BB%9F.html#%E5%88%B6%E4%BD%9Crootfs%E6%96%87%E4%BB%B6%E7%B3%BB%E7%BB%9F) in Loongnix's official documentation about how to make a rootfs. However, it's outdated and contains bad practices.

Since we're using [systemd-nspawn(1)](https://wiki.archlinux.org/title/Systemd-nspawn) in this post, we create the rootfs at `/var/lib/machines/loongnix`.

```console
$ sudo pacman -S debootstrap
$ sudo ln -s sid /usr/share/debootstrap/scripts/loongnix-stable
$ sudo cd /var/lib/machines
$ sudo debootstrap --no-check-gpg --variant=minbase --components=main,non-free,contrib --include=dbus,libpam-systemd --arch=loong64 --foreign --verbose loongnix-stable ./loongnix https://pkg.loongnix.cn/loongnix/25
$ sudo arch-chroot ./loongnix /debootstrap/debootstrap --second-stage
```

As this is a minimal installation, many essential services and utilities are missing. One of them is systemd-networkd.service(8). Start it inside the container for network access:

```console
$ sudo machinectl shell loongnix
# systemctl enable --now systemd-networkd.service
```

Then, in the host, set up appropriate networking in `/etc/systemd/nspawn/loongnix.nspawn`.

Some other utilities are needed for normal operation inside the container.

```console
# apt update
# apt install -y bash-completion \
    dialog apt-utils libterm-readline-perl-perl ncurses-term \
    locales \
    vim \
    iputils-ping curl wget iproute2 systemd-resolved ca-certificates
# dpkg-reconfigure locales
# ln -sf ../usr/share/zoneinfo/Asia/Shanghai /etc/localtime
# dpkg-reconfigure -f noninteractive tzdata
# echo 'export TERM=xterm-256color' >>~/.bash_profile
# systemd-machine-id-setup
```

Finally can you enjoy this non-rolling, *official*, *standard* distribution for LoongArch. Remember to backport fixes to LLVM/Clang/GCC, binutils, linkers, and runtimes. It's better build a newer stable version of those from scratch for anything serious.

```console
# fastfetch
        #####            root@loongcatbox
       #######           ----------------
       ##O#O##           OS: Loongnix GNU/Linux 25 (loongnix) loongarch64
       #######           Host: Loongson-3B6000x1-7A2000x1-XB612B0_v1.2
     ###########         Kernel: Linux 7.0.12-arch1-2-csmantle-aosc-main-16k
    #############        Uptime: 6 days, 1 hour, 32 mins
   ###############       Packages: 322 (dpkg)
   ################      Shell: bash 5.2.37
  #################      Display (NanoKVM): 1920x1080 @ 60 Hz in 22" [External]
#####################    Terminal: xterm-256color
#####################    CPU: Loongson-3B6000 (24) @ 2.20 GHz
  #################      GPU: AMD Device 67C7 (VGA compatible) [Discrete]
                         Memory: 6.07 GiB / 31.60 GiB (19%)
                         Swap: 2.38 GiB / 23.10 GiB (10%)
                         Disk (/): 359.95 GiB / 928.87 GiB (39%) - btrfs
                         Local IP (host0): 198.18.1.43/24
                         Locale: en_US.UTF-8
```
