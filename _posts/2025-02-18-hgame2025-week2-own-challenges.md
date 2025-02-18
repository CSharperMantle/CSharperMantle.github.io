---
layout: post
title: "HGAME 2025 命题小记 - WEEK2"
date: 2025-02-18T20:01:21+08:00
lang: zh
description: >-
    阅读赛题源码和研究writeup同样重要。（第二部分）
tags: topic:ctf hgame-2025 announcement
---

> [HGAME 2025介绍与WEEK1文章见此。]({% link _posts/2025-02-15-hgame2025-week1-own-challenges.md %})

本篇文章中列出出现于WEEK2（目前也已结束）的赛题。可以文末评论区中与我讨论赛题相关内容。与WEEK1赛题一样，公开的附件与源代码重分发权归Vidar-Team与本人所有，详见仓库内许可文件。

## Fast and frustrating

* **方向：** 逆向工程（RE）
* **预期难度：** 中等
* **正解数/提交数：**
  * **校内：** 1/1 = 100.00% （队伍总数：144）
  * **总计：** 9/22 = 40.91% （队伍总数：2231）
* **仓库：** <https://github.com/CSharperMantle/hgame2025_FastAndFrustrating_public>

.NET AOT赛题，需要选手研究.NET平台上[i18n/l10n](https://blog.mozilla.org/l10n/2011/12/14/i18n-vs-l10n-whats-the-diff/)的实现细节以成功解题。C#的[LINQ](https://learn.microsoft.com/en-us/dotnet/csharp/linq/)特色也在本题中有所体现。

## Nop'd

* **方向：** 逆向工程（RE）
* **预期难度：** 困难
* **正解数/提交数：**
  * **校内：** 2/3 = 66.67% （队伍总数：144）
  * **总计：** 8/11 = 72.73% （队伍总数：2231）
* **仓库：** <https://github.com/CSharperMantle/hgame2025_nopd_public>

借助`syscall`和多字节`nop`特性在x86-64中实现类semihosting机制，并以此进行控制流隐藏。不存在监视进程时，子进程执行正常逻辑；存在监视进程时，子进程通过魔法`nop`序列与监视进程通信。选手需要通过[手动指定黑盒指令的输入输出](https://hex-rays.com/blog/igors-tip-of-the-week-71-decompile-as-call)指导IDA进行数据流分析。关于实现细节，可阅读官方writeup或[《Much ado about nothing》一文]({% link _posts/2025-02-07-much-ado-about-nothing.md %})。
