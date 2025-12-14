---
layout: post
title: A POSIX-compliant rewrite of reresolve-dns.sh
date: 2025-12-14T09:14:50+08:00
lang: en
tags: topic:misc shell networking
---

## The script

Please be careful with line endings if you're copy-pasting the script from below.

If you're interested in the story behind it, please scroll down to [#background-story](#background-story).

```sh
#!/bin/sh
# SPDX-License-Identifier: GPL-2.0
#
# POSIX sh-compliant rewrite of reresolve-dns.sh.
#
# Notes for BusyBox-based coreutils:
#  * A POSIX-compliant tr(1) is expected for [:upper:] and [:lower:].
#
# Copyright (C) 2015-2020 Jason A. Donenfeld <Jason@zx2c4.com>. All Rights Reserved.
# Copyright (C) 2025 Rong Bao <webmaster@csmantle.top>.
#
# Link: https://github.com/WireGuard/wireguard-tools/blob/master/contrib/reresolve-dns/reresolve-dns.sh
# Link: https://gist.github.com/CSharperMantle/ffff2a5e781fe2e4adff22a293315a65#file-reresolve-dns-posix-sh

set -e
export LC_ALL=C

trim() {
    echo "$1" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//'
}

lower() {
    echo "$1" | tr '[:upper:]' '[:lower:]'
}

CONFIG_FILE="$1"

if echo "$CONFIG_FILE" | grep -qE '^[a-zA-Z0-9_=+.-]{1,15}$'; then
    CONFIG_FILE=/etc/wireguard/"$CONFIG_FILE".conf
fi

INTERFACE=$(basename "$CONFIG_FILE" .conf)

PEER_SECTION=0
PUBLIC_KEY=''
ENDPOINT=''

process_peer() {
    if [ "$PEER_SECTION" -ne 1 ] || [ -z "$PUBLIC_KEY" ] || [ -z "$ENDPOINT" ]; then
        return 0
    fi
    handshake_line=$(wg show "$INTERFACE" latest-handshakes | grep -F "$PUBLIC_KEY" || true)
    if [ -z "$handshake_line" ]; then
        return 0
    fi
    if [ $(( $(date +%s) - $(echo "$handshake_line" | awk '{print $2}') )) -gt 135 ]; then
        wg set "$INTERFACE" peer "$PUBLIC_KEY" ENDPOINT "$ENDPOINT"
    fi
    reset_peer_section
}

reset_peer_section() {
    PEER_SECTION=0
    PUBLIC_KEY=''
    ENDPOINT=''
}

reset_peer_section
while read -r line || [ -n "$line" ]; do
    stripped="${line%%\#*}"
    raw_key="${stripped%%=*}"
    if echo "$stripped" | grep -q '='; then
        raw_value="${stripped#*=}"
    else
        raw_value=''
    fi
    key=$(lower "$(trim "$raw_key")")
    value=$(trim "$raw_value")

    case "$key" in
        "["*) 
            process_peer
            reset_peer_section
            if lower "$key" | grep -qEi '^\[peer\]$'; then
                PEER_SECTION=1
            fi
            ;;
        *)
            if [ $PEER_SECTION -eq 1 ]; then
                case "$(lower "$key")" in
                    publickey) PUBLIC_KEY="$value" ;;
                    endpoint) ENDPOINT="$value" ;;
                esac
            fi
            ;;
    esac
done < "$CONFIG_FILE"
process_peer
```

## Background story

Recently, I finally decided to setup a lightweight auto-refresher for my [WireGuard](https://www.wireguard.com/) peers's DDNS endpoints. A brief search brought me [reresolve-dns.sh](https://github.com/WireGuard/wireguard-tools/blob/0b7d9821f2815973a2930ace28a3f73c205d0e5c/contrib/reresolve-dns/reresolve-dns.sh), an awesome small script written by Jason A. Donenfeld.

I am running WireGuard on several different boxes. I have:

1. A small VPS running Debian 13,
2. A medium VPS running Ubuntu 24.04,
3. A router running OpenWrt 24.10.

The first two have all the modern amenities available, so I deployed reresolve-dns.sh using [`systemd` timers](https://www.freedesktop.org/software/systemd/man/latest/systemd.timer.html) fairly quickly. The third one is trickier. The coreutils on this OpenWrt distro uses [BusyBox](https://busybox.net/) by default, so the built-in shell is ash, a barely POSIX-compliant shell without much extra fuss. Its source docs says:

> The most complete and most pedantically correct shell included with busybox. This shell is actually a derivative of the Debian 'dash' shell (by Herbert Xu), which was created by porting the 'ash' shell written by Kenneth Almquist) from NetBSD.
> 
> -- [BusyBox shell/ash.c](https://github.com/mirror/busybox/blob/371fe9f71d445d18be28c82a2a6d82115c8af19d/shell/ash.c#L28-L31)

The original reresolve-dns.sh uses quite a lot of Bash features. I also don't want to break the embedded firmware immutability yet once more, so a rewrite seems natural.

After completing the first draft, I tested it on my OpenWrt box. It didn't work as expected, for the [BusyBox tr(1)](https://busybox.net/downloads/BusyBox.html#:~:text=tr%20[-cds]%20STRING1%20[STRING2]) utility came with my OpenWrt distro can't recognize character classes (like `[:upper:]`). In fact, it does have such feature in its source code, but [it's disabled on OpenWrt builds](https://github.com/openwrt/openwrt/blob/ff4546093e0146654007d71a2cc37034fe9f633e/package/utils/busybox/Config-defaults.in#L871-L873). Breaking immutability and installing [coreutils-tr](https://openwrt.org/packages/pkgdata/coreutils-tr) resolves this issue.
