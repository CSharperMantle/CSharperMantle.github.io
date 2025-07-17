---
layout: post
title: "WSL2 上使用 Canokeys 踩坑"
date: 2025-07-17T22:08:14+08:00
lang: en
tags: topic:misc wsl
---

> 本文可供大多数需要将USB设备直通至WSL2虚拟机内的场景参考，并不局限于Canokeys或USB智能卡等话题。

WSL2支持使用[usbipd-win](https://github.com/dorssel/usbipd-win)实现USB设备直通，可以较为方便地将OpenPGP智能卡直通至虚拟机内供GPG使用，配置方法推荐阅读微软的文章：<https://learn.microsoft.com/en-us/windows/wsl/connect-usb>。一般而言，出现类似以下的输出，即可认为USB直通配置正确：

```sh
$ lsusb
[...]
Bus 001 Device 005: ID 20a0:42d4 Clay Logic CanoKey Canary
[...]
```

但是即使设备直通成功，gpg也可能无法找到智能卡：

```sh
$ gpg --card-status
gpg: selecting card failed: No such device
gpg: OpenPGP card not available: No such device
```

运行`pcsc_scan`可以发现是权限不足：

```sh
$ pcsc_scan
PC/SC device scanner
V 1.7.1 (c) 2001-2022, Ludovic Rousseau <ludovic.rousseau@free.fr>
SCardEstablishContext: Access denied.
```

`scdaemon`的日志也有类似的问题：

```plain-text
2025-07-17 21:29:29 scdaemon[112573] DBG: chan_7 <- learn
2025-07-17 21:29:29 scdaemon[112573] ccid open error: skip
2025-07-17 21:29:29 scdaemon[112573] check permission of USB device at Bus 001 Device 002
2025-07-17 21:29:29 scdaemon[112573] DBG: chan_7 -> ERR 100696144 No such device <SCD>
2025-07-17 21:29:29 scdaemon[112573] DBG: chan_7 <- RESTART
2025-07-17 21:29:29 scdaemon[112573] DBG: chan_7 -> OK
```

可以通过创建热插拔规则形式自动配置设备的权限，允许当前用户所在的组（可以使用`groups`查看，这里选择`plugdev`组）写入该设备。

```sh
sudo tee /etc/udev/rules.d/99-canokey.rules << EOF
SUBSYSTEM=="usb", ATTR{idVendor}=="20a0", ATTR{idProduct}=="42d4", MODE="0664", GROUP="plugdev"
EOF
sudo udevadm control --reload-rules
sudo udevadm trigger
```

运行后可验证生效：

```sh
$ ls -la /dev/bus/usb/*/*
crw-rw-r-- root root    0 B Thu Jul 17 22:22:35 2025  /dev/bus/usb/001/001
crw-rw-r-- root root    0 B Thu Jul 17 22:22:35 2025  /dev/bus/usb/002/001
crw-rw-r-- root plugdev 0 B Thu Jul 17 22:23:04 2025  /dev/bus/usb/001/005
$ gpg --card-status
Reader ...........: 20A0:42D4:013138D7:0
Application ID ...: D276000124010304F1D0013138D70000
Application type .: OpenPGP
Version ..........: 3.4
Manufacturer .....: CanoKeys
[...]
```

在签名时有可能出现以下错误：

```sh
$ git commit --amend -S --no-edit
error: gpg failed to sign the data:
[GNUPG:] KEY_CONSIDERED <...> 0
[GNUPG:] BEGIN_SIGNING H10
[GNUPG:] PINENTRY_LAUNCHED 130663 curses 1.2.1 - xterm-256color :0 - 1000/1000 -
gpg: signing failed: Inappropriate ioctl for device
[GNUPG:] FAILURE sign 83918950
gpg: signing failed: Inappropriate ioctl for device

fatal: failed to write commit object
```

可以参考<https://stackoverflow.com/questions/39494631/gpg-failed-to-sign-the-data-fatal-failed-to-write-commit-object-git-2-10-0/55993078#55993078>，导出环境变量：

```sh
export GPG_TTY=$(tty)
```

这样就能够正确显示合适的PIN输入界面。若有需要，也可以修改sudoers文件让sudo保留这个环境变量：

```sudoers
Defaults env_keep += "GPG_TTY"
```
