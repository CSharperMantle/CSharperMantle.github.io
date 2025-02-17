---
layout: post
title: "HGAME 2025 命题小记 - WEEK1"
date: 2025-02-15T10:24:38+08:00
lang: zh
description: >-
    阅读赛题源码和研究writeup同样重要。（第一部分）
tags: topic:ctf hgame-2025 announcement
---

HGAME 2025 ([Hello-CTF链接](https://github.com/ProbiusOfficial/Hello-CTFtime/issues/213))是由Vidar-Team战队举行的入门难度CTF赛事，比赛时间为[2025-02-03 20:00 GMT+8](https://www.timeanddate.com/worldclock/converter.html?iso=20250203T120000&p1=33)至[2025-02-17 20:00 GMT+8](https://www.timeanddate.com/worldclock/converter.html?iso=20250217T120000&p1=33)。赛事由两个*WEEK*组成，每个WEEK时长均为7天。HGAME本身为Vidar-Team面向杭州电子科技大学校内新生的招新赛，但也设有社会赛道，欢迎所有想学习的同学、选手参加。

我非常高兴能够为赛事供题，也希望各位选手同样在今年的比赛中感受到了研究、解题的乐趣。官方writeup将在两个WEEK均结束后由Vidar-Team发布于其官方GitHub组织仓库内（链接待赛后添加）。除此之外，我也以个人身份将我编写赛题的源码公开于个人账号下，以便选手归档、复现和学习。公开的赛题附件与源代码重分发权归Vidar-Team与本人所有，详见仓库内许可文件。

本篇文章中仅列出出现于WEEK1（目前已结束）的赛题。可以文末评论区中与我讨论赛题相关内容。

## Compress dot new

* **方向：** 逆向工程（RE）
* **预期难度：** 简单
* **正解数/提交数：**
  * **校内：** 26/58 = 44.83% （队伍总数：144）
  * **总计：** 453/762 = 59.45% （队伍总数：2231）
* **仓库：** <https://github.com/CSharperMantle/hgame2025_compress_nu_public>

一道简单的热身赛题，鼓励选手与AI交互以快速掌握新的概念、写出解题脚本。有趣的是，在命题过程中我发现Nushell类型系统难以表达递归类型，这大概是这个几乎函数式Shell语言的一点缺陷。[我的另一篇短文]({% link _posts/2025-02-05-achilles-s-heel-of-nushell.md %})中对此有更详细的描述。

## Two wires

* **方向：** 杂项（Misc）、物联网（Internet-of-Things）
* **预期难度：** 困难
* **正解数/提交数：**
  * **校内：** 3/71 = 4.23% （队伍总数：144）
  * **总计：** 17/179 = 9.50% （队伍总数：2231）
* **仓库：** <https://github.com/CSharperMantle/hgame2025_two_wires_public>

综合了波形分析、固件逆向和文档检索的IoT赛题。由于HGAME不设IoT专项方向，因此本题归为Misc分类。当选手能够正确分析中断事件引起的状态变化时，离解出这道题也就不远了。当然，对AVR指令集的熟悉程度（或者快速查阅文档的能力）也是非常关键的。
