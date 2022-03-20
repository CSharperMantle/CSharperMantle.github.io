---
layout: post
title: "知乎回答草稿箱：long long"
date: 2022-01-15 07:58:46 +0800
lang: zh-Hans
description: 本文是一篇知乎回答的草稿。
categories: zhihu-answer
---

有意思的问题。我们先来看看`long long`的发展历史。

------

> 世有`long int`，然后有`long long int`。`long int`常有而`long long int` 不常有。

在C89标准中没有`long long`，但是给自定义的新类型留下了空间[^1]：

> There are four signed integer types, designated as `signed char`, `short int`, `int`, and `long int`. (The signed integer and other types may be designated in several additional ways, as described in 3.5.2)

这可能是因为C89标准制定时64位编程还没有那么流行，也可能是在当时主流32位CPU（486DX是在1989年发布的）上跑64位运算需要两个寄存器辅助，就像现在的`__int128`一样（猜的）。

随着应用的发展，64位操作的需求庞大起来，于是几个当时的编译器厂商都不约而同地实现了自己的64位扩展[^2]：

> They are implemented by many vendors.  3 years ago, there was an informal working group that included many vendors, (addressing 64-bit C progrmaming models for machines that also had 32-bit models), and the general consensus was that as much as we despised the syntax, it was:
> 
> a) Already in CONVEX & Amdahl, at least
> 
> b) Already in Gnu C
> 
> c) And various other hardware vendors either already had it in or were planning to.

用户开始呼吁标准委员会将`long long`加入下一个发布的C标准版本。有趣的是，这个讨论的发起者J. R. Mashey特意在邮件中加了一条“背景信息”[^2]：

> BACKGROUND
> 
> If 64-bit microprocessors are unfamiliar, consider reading: John R. Mashey, "64-bit Computing", *BYTE*, Sept 1991, 135-142. This explained what 64-bit micros were, the hardware trends leading to this, and that there would be widespread use of them by 1995 (there is). While a little old, most of what I said there still seems OK.

可见像64位CPU这样的新事物足以把当时早已熟悉x86的人们弄得晕头转向，也难怪C89标准没有`long long`了。

同样，C标准委员会对主动加入一个新类型并不是很反对，他们只是不愿意先于大众做这件事[^2]：

> Somebody in this group was also on ANSI C committee, and observed that fact of long long not being in ANSI C was no reason not to agree on doing it, since standards generally codify existing practice, rather than inventing new things, when reasonably possible.

果然在C99中，`long long`被正式确定为一个新类型[^3]：

> There are five standard signed integer types, designated as `signed char`, `short int`, `int`, `long int`, and `long long int`. (These and other types may be designated in several additional ways, as described in 6.7.2.) There may also be implementation-defined extended signed integer types.) The standard and extended signed integer types are collectively called signed integer types.)

------

所以回到题主的问题上来：为什么C采用了`long long int`表示比`long int`大的整数，却使用`char`表示比`short int`小的整数？`short short int`不是更好吗？其实`long long int`才是一个特例。题主也说了，这是一个历史包袱。

`long long int`是随需求发展而加入的类型，为了契合各厂商*已有的*实践而标准化。这名字的好处，一是在于它没有向语言添加新的关键字，不会让所有历史代码一夜之间废掉，二是它非常形象：什么比`long int`长？`long long int`。

再者来说，`char`诞生之初就与字符（**char**acter）紧密联系[^1]：

> An object declared as type `char` is large enough to store any member of the basic execution character set. If a member of the required source character set enumerated in 2.2.1 is stored in a `char` object, its value is guaranteed to be positive. If other quantities are stored in a `char` object, the behavior is implementation-defined: the values are treated as either signed or nonnegative integers. 

`char`是能保证存下所有基本字符（大小写字母、0-9、29个标点符号、空格、horizontal tab、vertical tab、form feed）的最小类型，恰好和ASCII字符大小一致，为8位。这也是最初表示字符的需求决定的，你觉得`char* str`和你提议的`short short int* str`哪个更直观？

所以一句话总结：`long long int`作为在标准制定以后因需求而加入的类型，与`char`这种标准制定之时便有需求的类型没有命名上的可比性。

[^1]: http://port70.net/~nsz/c/c89/c89-draft.html#3.1.2.5

[^2]: http://port70.net/~nsz/c/c89/longlong.html

[^3]: http://port70.net/~nsz/c/c99/n1256.html#6.2.5
