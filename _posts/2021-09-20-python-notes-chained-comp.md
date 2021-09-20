---
layout: post
title: "Python随笔（2）：连锁比较操作 Chained Comparisons"
date: 2021-09-20 18:29:31 +0800
categories: python-notes
---

## 0. 前言

Python中的*连锁比较操作*（chained comparisons）是在其他语言中少有实现的特性之一，本文将对此特性展开一定研究。

**本文中Python Interpreter版本**：`Python 3.8.0 (tags/v3.8.0:fa919fd, Oct 14 2019, 19:21:23) [MSC v.1916 32 bit (Intel)] on win32` （CPython）

## 1. 问题描述

代码片段如下：

```python
def is_ascending_simple(a: int, b: int, c: int) -> bool:
    return a < b and b < c


def is_ascending_chained(a: int, b: int, c: int) -> bool:
    return a < b < c


print("is_ascending_simple(1, 2, 3): {}".format(is_ascending_simple(1, 2, 3)))
print("is_ascending_simple(1, 3, 2): {}".format(is_ascending_simple(1, 3, 2)))
print("is_ascending_chained(1, 2, 3): {}".format(is_ascending_chained(1, 2, 3)))
print("is_ascending_chained(1, 3, 2): {}".format(is_ascending_chained(1, 3, 2)))
```

在Python 3.8.0 shell中执行产生以下结果：

```plain
>>>
>>> def is_ascending_simple(a: int, b: int, c: int) -> bool:
...     return a < b and b < c
...
>>>
>>> def is_ascending_chained(a: int, b: int, c: int) -> bool:
...     return a < b < c
...
>>>
>>> print("is_ascending_simple(1, 2, 3): {}".format(is_ascending_simple(1, 2, 3)))
is_ascending_simple(1, 2, 3): True
>>> print("is_ascending_simple(1, 3, 2): {}".format(is_ascending_simple(1, 3, 2)))
is_ascending_simple(1, 3, 2): False
>>> print("is_ascending_chained(1, 2, 3): {}".format(is_ascending_chained(1, 2, 3)))
is_ascending_chained(1, 2, 3): True
>>> print("is_ascending_chained(1, 3, 2): {}".format(is_ascending_chained(1, 3, 2)))
is_ascending_chained(1, 3, 2): False
>>>
```

那么，表达式`a < b and b < c`是否与`a < b < c`等价？

## 2. 解决方案与讨论

[Python 3.8 References 6.10. Comparisons](https://docs.python.org/3.8/reference/expressions.html#comparisons)一章对连锁比较操作进行了如下定义：

> Comparisons can be chained arbitrarily, e.g., `x < y <= z` is equivalent to `x < y and y <= z`, except that y is evaluated only once (but in both cases `z` is not evaluated at all when `x < y` is found to be false).
> 
> Formally, if *a*, *b*, *c*, …, *y*, *z* are expressions and *op1*, *op2*, …, *opN* are comparison operators, then `a op1 b op2 c ... y opN z` is equivalent to `a op1 b and b op2 c and ... y opN z`, except that each expression is evaluated at most once.

对该文段分析可以得到以下结论：

1. `x < y <= z`一类的连锁比较表达式通常情况下与`x < y and y <= z`等价；
2. 在由`a op1 b op2 c ... y opN z`描述的一般性连锁表达式中，类似`a`至`z`的子表达式**至多**被*求值*（evaluate）一次；
3. 连锁表达式存在*短路*（short-circuiting）现象，且与[Python 3.8 References 6.11. Boolean operations](https://docs.python.org/3.8/reference/expressions.html#boolean-operations)中的描述一致。

说人话（但并不normative）：连锁表达式可以按照`a op1 b op2 c ... y opN z => a op1 b and b op2 c and ... y opN z`的形式展开，但是每一个子表达式都最多被算一次。

下面我们用实例来分点研究定义中的描述。

### 2.1. 验证等价性

详见“1. 问题描述”一节。

### 2.2. 验证至多求值一次

代码：

```python
# chaining-comp-2-2.py

def get_number_log(n: int) -> int:
    """
    Return a number as is and log the requested number to terminal.
    """
    print("get_number_log(n) called with n={}".format(n))
    return n


print("Simple comp: {}".format(
    get_number_log(1) < get_number_log(2)
    and get_number_log(2) < get_number_log(3)
))
print("Chained comp: {}".format(
    get_number_log(1) < get_number_log(2) < get_number_log(3)
))
```

结果：

```plain
PS > py -3 .\chaining-comp-2-2.py
get_number_log(n) called with n=1
get_number_log(n) called with n=2
get_number_log(n) called with n=2
get_number_log(n) called with n=3
Simple comp: True
get_number_log(n) called with n=1
get_number_log(n) called with n=2
get_number_log(n) called with n=3
Chained comp: True
PS >
```

原理：使用`get_number_log()`函数记录每一次表达式的求值情况。

结论：由两次表达式求值中对`get_number_log()`求值的次数差可知，原命题得证。

### 2.3. 验证短路性

#### 2.3.1. 判断被短路表达式执行与否

代码：

```python
# chaining-comp-2-3-1.py

class MyInt:
    """
    A user-defined class similar to int.
    Every self.__lt__() call is logged.
    """

    def __init__(self, n: int):
        self._n = n
    
    def __lt__(self, another) -> bool:
        print("MyInt.__lt__() called with self={} another={}".format(self._n, another._n))
        return self._n < another._n


my_one = MyInt(1)
my_two = MyInt(2)
my_three = MyInt(3)


print("my_one < my_two < my_three: {}".format(
    my_one < my_two < my_three
))
print("my_three < my_one < my_two: {}".format(
    my_three < my_one < my_two
))
```

结果：

```plain
PS > py -3 .\chaining-comp-2-3-1.py
MyInt.__lt__() called with self=1 another=2
MyInt.__lt__() called with self=2 another=3
my_one < my_two < my_three: True
MyInt.__lt__() called with self=3 another=1
my_three < my_one < my_two: False
PS >
```

原理：使用自定义类和`__lt__()`特殊函数记录`<`表达式的求值情况。

结论：由第二次求值中`MyInt.__lt__()`仅被运行一次可见，原命题得证。

#### 2.3.2. 判断表达式返回值

代码：

```python
# chaining-comp-2-3-2.py

SENTRY = 999
SENTRY_RET_VAL = 1000


class MyInt:
    """
    A user-defined class similar to int.
    SENTRY_RET_VAL is returned when SENTRY is compared against any value.
    """

    def __init__(self, n: int):
        self._n = n
    
    def __lt__(self, another) -> bool:
        return (SENTRY_RET_VAL
            if another._n == SENTRY
            else self._n < another._n
            )


my_one = MyInt(1)
my_two = MyInt(2)
my_sentry = MyInt(SENTRY)

print("my_one < my_two < my_sentry: {}".format(
    my_one < my_two < my_sentry
))
```

结果：

```plain
PS > py -3 .\chaining-comp-2-3-2.py
my_one < my_two < my_sentry: 1000
PS >
```

原理：通过与2.3.1.节中相同的方法自定义`__lt__()`特殊函数，在遇到第二操作数为`SENTRY`时，返回`SENTRY_RET_VAL`而不是正常的布尔值，以检测连锁比较操作是否会有[Python 3.8 References 6.11. Boolean operations](https://docs.python.org/3.8/reference/expressions.html#boolean-operations)中描述的一般布尔操作行为。

结论：观察到`SENTRY_RET_VAL`被返回，原命题得证。

### 2.4. CPython字节码中的证据

CPython*字节码*（bytecode）是CPython对于已解析的Python*源码*（source）的一种的内部表示。CPython字节码的具体内容与*CPython实现细节*（CPython implementation detail）有关，故没有跨平台性。通过字节码，用户可以从执行的底层观察代码的解析情况。

Python内置电池中的`dis`模块（[文档见此](https://docs.python.org/3.8/library/dis.html)）允许用户在运行时检查已被解析的函数的字节码实现。

代码：

```python
def is_ascending_simple(a: int, b: int, c: int) -> bool:
    return a < b and b < c


def is_ascending_chained(a: int, b: int, c: int) -> bool:
    return a < b < c


import dis
dis.dis(is_ascending_simple)
dis.dis(is_ascending_chained)
```

结果：

```plain
>>>
>>> def is_ascending_simple(a: int, b: int, c: int) -> bool:
...     return a < b and b < c
...
>>>
>>> def is_ascending_chained(a: int, b: int, c: int) -> bool:
...     return a < b < c
...
>>>
>>> import dis
>>> dis.dis(is_ascending_simple)
  2           0 LOAD_FAST                0 (a)
              2 LOAD_FAST                1 (b)
              4 COMPARE_OP               0 (<)
              6 JUMP_IF_FALSE_OR_POP    14
              8 LOAD_FAST                1 (b)
             10 LOAD_FAST                2 (c)
             12 COMPARE_OP               0 (<)
        >>   14 RETURN_VALUE
>>> dis.dis(is_ascending_chained)
  2           0 LOAD_FAST                0 (a)
              2 LOAD_FAST                1 (b)
              4 DUP_TOP
              6 ROT_THREE
              8 COMPARE_OP               0 (<)
             10 JUMP_IF_FALSE_OR_POP    18
             12 LOAD_FAST                2 (c)
             14 COMPARE_OP               0 (<)
             16 RETURN_VALUE
        >>   18 ROT_TWO
             20 POP_TOP
             22 RETURN_VALUE
>>>
```

`is_ascending_simple()`的字节码相对简单，不再赘述。下面将对`is_ascending_chained()`的运行栈情况进行简要分析。

以下分析抽象的格式如下：`LineNo(("b" DescriptionOfBranch)|(["y""n"]))? ("Return("RetVal")")? ("Stack("StackDescription")")?`

```plain
2 Stack(Bottom a b Top)
4 Stack(Bottom a b b Top)
6 Stack(Bottom b a b Top)
8b a < b?
8 Stack(Bottom b a b a<b Top)

8n Not taking JMP
10 Stack(Bottom b a b Top)
12 Stack(Bottom b a b c Top)
14 Stack(Bottom b a b c b<c Top)
16 Return(b<c)

8y Taking JMP
18 Stack(Bottom b a a<b b Top)
20 Stack(Bottom b a a<b Top)
22 Return(a<b)
```

对`dis`产生的具体指令详见[文档](https://docs.python.org/3.8/library/dis.html)。

结论：两函数在执行上等效。
