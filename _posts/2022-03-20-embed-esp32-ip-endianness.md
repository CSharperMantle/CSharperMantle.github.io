---
layout: post
title: "Endianness in ESP32/Arduino IPAddress"
date: 2022-03-20T07:42:14+08:00
lang: en-US
tags: topic:dev embedded esp32 arduino c/c++
---

## 0. Introduction

ESP32, manufactured by [Espressif](https://www.espressif.com/), is a multi-purpose WiFi and BLE-enabled MCU for embedded systems. It is gaining popularity in the area thanks to its documentation, ecosystems and so on.

One scenario I have just experienced in ESP32 is a handshake protocol which utilized extensively the broadcast feature in UDP. A client has to confirm that a handshake confirmation contains the IP address of itself by comparing the `uint32_t` representation of IP carried in the message and in the client itself. While implementing this, I discovered that the byte order of `IPAddress` is odd, which finally led to the production of this text.

In this small article, we will see how this endianness issue is solved.

<!-- seo-excerpt-separator -->

My development environment is as follows.

1. Hardware
    * `NodeMCU-32S powered by ESP32-S`
2. Software
    * IDE: `PlatformIO Core v5.2.5`
    * Platform: `espressif32 v3.5.0`
    * Toolchain: `xtensa-esp32-elf-g++ (crosstool-NG crosstool-ng-1.22.0-97-gc752ad5d) 5.2.0`

## 1. Problem

We want to convert an `IPAddress` object - a standard way to represent an IP address in the world of Arduino - to its bytes representation in a correct byte order.

## 2. Solution

Reverse the bytes returned by a cast of `IPAddress`.

```cpp
#include <cstdint>
#include <Arduino.h>
#include <IPAddress.h>

static constexpr std::uint32_t helper_reverse_bytes(const std::uint32_t x) noexcept
{
  // https://forum.arduino.cc/t/reversed-byte-order/699873/6
  return static_cast<std::uint32_t>((x & 0xFF) << 24 | ((x >> 8) & 0xFF) << 16 | ((x >> 16) & 0xFF) << 8 | ((x >> 24) & 0xFF));
}

IPAddress ip{127, 0, 0, 1};
printf("%u\n", helper_reverse_bytes(static_cast<std::uint32_t>(ip)));
// Prints: 2130706433
```

## 3. Discussions

`IPAddress` objects have defined their cast operators so it's (seemingly) straightforward to `static_cast` such an object to `uint32_t`.

```cpp
#include <cstdint>
#include <Arduino.h>
#include <IPAddress.h>

IPAddress ip{127, 0, 0, 1};
printf("%u\n", static_cast<std::uint32_t>(ip));
// Prints: 16777343
```

However we may at once spot some issue with this approach. While `127.0.0.1` has a decimal representation of `2130706433`, the output actually represents `1.0.0.127`. The bytes is reversed. We can see here that a simple reversal function will do the mending job.
