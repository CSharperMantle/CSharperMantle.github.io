---
layout: post
title: "Python随笔（5）：数值字面量与一元取反操作符 Numeric Literals vs. Unary Negation Operator"
date: 2022-06-11 19:51:42 +0800
lang: zh-Hans
description: 本文讨论了一元取反操作符在Python中的地位与常见疑问。
categories: python-notes
---

## 0. 前言

在Python中，`-10`到底属于什么类型？是一个*原子的*（atomic）数值字面量（即`-10`作为一个整体），还是一个表达式串（即对`10`取相反数）？这个看似很简单的问题，因为一个特殊的操作符而变得不那么平凡。我们将在此对Python中的数值字面量和一元取反操作符的关系展开探讨。

**本文中使用的软件环境**：
* **python**：`Python 3.7.0 (v3.7.0:1bf9cc5093, Jun 27 2018, 04:59:51) [MSC v.1914 64 bit (AMD64)] on win32`
* **node**：`v16.4.2`
* **bash**：`GNU bash, version 4.4.12(3)-release (x86_64-unknown-cygwin)`
* **php**：`PHP 7.2.9 (cli) (built: Aug 15 2018 23:10:01) ( ZTS MSVC15 (Visual C++ 2017) x64 )`
* **vbc**：`Microsoft (R) Visual Basic Compiler version 3.4.0-beta4-19562-05 (ff930dec)`
* **octave**：`GNU Octave, version 7.1.0`

## 1. 问题描述

对下述Python表达式求值：

```python
-3 ** 2
```

## 2. 解决方案

对表达式求值可得：

```plain
PS > py -3
Python 3.7.0 (v3.7.0:1bf9cc5093, Jun 27 2018, 04:59:51) [MSC v.1914 64 bit (AMD64)] on win32
Type "help", "copyright", "credits" or "license" for more information.
>>> -3 ** 2
-9
>>>
```

## 3. 讨论

### 3.1. 负号的地位

按照常识，对`-3 ** 2`求值应该以`(-3) ** 2`的顺序进行，因为在正常的数学计算中，`-3`一定作为一个整体出现。我们会说`-3`是一个负数，而`3`是一个正数——无论哪种情况，一个数都是带有符号的。这种含义下的正号和负号都是作为*数值字面量*（numeric literal）的一部分出现的，应该有与字面量相同的优先级，高于所有操作符。

> “字面量”的意思是“constant values of some built-in types”，正如字面量`10`代表数“10”，而*非字面*（non-literal）表达式`x`代表了一个名为“x”的变量的值，该值（目前）未指定。

但同时，我们又会写出`-x`这样的算式，这里的负号则代表了一种*操作符*（operator），执行“对紧随其后的表达式取相反数”这样的操作。因此，`-x`的结果可能是正数，也可能是负数，也可能是零——这里的负号不是`x`的一部分，有与其他操作符类似的优先级。

> 操作符有*一元*（unary）、*二元*（binary）、*三元*（ternary）和*多元*（N-ary）之分，分别意味着该操作符有一个、两个、三个和N个参数。如常见的四则运算是二元操作符，因为它们有`arg_1 Op arg_2`的形式。取反操作是一元的，因为它有`- arg`的形式。同样是一元操作符的是*布尔取反*（Boolean negation）操作符`not`。三元操作符中常见是定积分。典型的多元操作符有对序列进行操作的`max`和`min`等。

这样语义上的二义性必须被消除，否则它将对语言本身的严谨性构成威胁。Python采取的方法是这样的（见[Python 3.10.5 Reference 2.4.4. Numeric literals](https://docs.python.org/3/reference/lexical_analysis.html#numeric-literals)）：

> There are three types of numeric literals: integers, floating point numbers, and imaginary numbers. There are no complex literals (complex numbers can be formed by adding a real number and an imaginary number).
> 
> Note that numeric literals do not include a sign; a phrase like `-1` is actually an expression composed of the unary operator `-` and the literal `1`.

负号被明确排除在字面量之外。因此，根据优先级规则，表达式`-3 ** 2`应该被理解为`- (3 ** 2)`。至此，解释完成。

### 3.2. 其他语言的处理方式

我们再来看看其他语言对`-3 ** 2`这类带歧义表达式的处理方式。以下选中的语言都同时具有取反操作符和乘方操作符（形式可能有所不同）。以函数形式提供乘方的语言不在考虑范围内。

结论：

**运算结果为9**：
* bash

**运算结果为-9**：
* Python
* PHP
* Visual Basic .NET
* MATLAB

**其他**：
* JavaScript（报告`SyntaxError`）

------

**JavaScript on Node.js**

JavaScript的处理是最严格的，直接以语法错误拒绝计算该表达式，要求用户在乘方中使用一元运算符时必须添加括号以消除歧义。

```plain
PS > node
Welcome to Node.js v16.4.2.
Type ".help" for more information.
> -3 ** 2
-3 ** 2
^^^^^

Uncaught:
SyntaxError: Unary operator used immediately before exponentiation expression. Parenthesis must be used to disambiguate operator precedence
>
```

**bash on Cygwin64**

bash显然把-3当作了一整个字面量处理，得出9的结果。

```plain
$ echo $((-3 ** 2))
9

$
```

**PHP**

与Python相同，乘方的优先级高于取反。

```plain
PS > php -a
Interactive shell

php > echo -3 ** 2;
-9
php >
```

**Visual Basic .NET**

与Python相同，乘方的优先级高于取反。

```vb
Imports System

Module Test
    Public Sub Main(args() As string)
        Console.WriteLine(-3 ^ 2)
    End Sub
End Module
```

```plain
PS > main.exe
-9

PS >
```

**MATLAB on GNU Octave**

```plain
PS > octave
GNU Octave, version 7.1.0
Copyright (C) 1993-2022 The Octave Project Developers.
This is free software; see the source code for copying conditions.
There is ABSOLUTELY NO WARRANTY; not even for MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  For details, type 'warranty'.

Octave was configured for "x86_64-w64-mingw32".

Additional information about Octave is available at https://www.octave.org.

Please contribute if you find this software useful.
For more information, visit https://www.octave.org/get-involved.html

Read https://www.octave.org/bugs.html to learn how to submit bug reports.
For information about changes from previous versions, type 'news'.

octave:1> -3 ^ 2
ans = -9
octave:2>
```
