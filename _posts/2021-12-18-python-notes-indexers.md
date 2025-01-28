---
layout: post
title: "Python随笔（4）：自定义索引器 Custom Indexers"
date: 2021-10-15T07:58:46+08:00
lang: zh-Hans
tags: topic:dev programming-language python
---

## 0. 前言

*索引器*（indexer，也被某些人称为“下标操作”）是大多数程序设计语言中访问有序数据结构（元组、向量、列表等）的传统方法。借助Python提供的强大自定义能力，我们可以为这一经典操作赋予新的功能——这也给刚刚接触各种数学计算库的新手带来了许多困惑。本文将简述索引器的几种可能用途并对此展开一些讨论。

**本文中Python Interpreter版本**：`Python 3.9.7 (tags/v3.9.7:1016ef3, Aug 30 2021, 20:19:38) [MSC v.1929 64 bit (AMD64)] on win32`

## 1. 问题描述

给定如下使用了`pandas`库的代码：

```python
# goods_list.py
import pandas

goods_dataframe = pandas.DataFrame({
    "name": [ "Pencil", "Eraser", "Ruler", "Compass" ],
    "price": [ 1.0, 3.5, 5.5, 12.8 ],
    "stock_amount": [ 152, 15, 98, 74 ]
})

print("Names of goods:")
print(goods_dataframe["name"])
print()
print("Goods cheaper than $4.0:")
print(goods_dataframe[goods_dataframe["price"] < 4.0])
print()
print("Goods at no risk in supply:")
print(goods_dataframe[goods_dataframe["stock_amount"] > 50])
print()
```

其产生以下结果：

```plain
PS > py -3 .\goods_list.py
Names of goods:
0     Pencil
1     Eraser
2      Ruler
3    Compass
Name: name, dtype: object

Goods cheaper than $4.0:
     name  price  stock_amount
0  Pencil    1.0           152
1  Eraser    3.5            15

Goods at no risk in supply:
      name  price  stock_amount
0   Pencil    1.0           152
2    Ruler    5.5            98
3  Compass   12.8            74

PS >
```

可以看到，其中类似`goods_dataframe[some_index]`的用法出现了多次。为什么可以用这么多不同的参数（`column`的类型、比较符结果等）调用？如何在自己的代码中实现这种行为？

## 2. 解决方案

以下代码综合使用了`__getitem__`、`__setitem__`和重载的比较操作符，实现了一个支持类似于`my_list[my_list BinOp some_arg]`形式表达式的简单列表。

```python
# queryable_list.py
from typing import Any, Generic, MutableSequence, SupportsIndex, TypeVar, Iterable

T = TypeVar("T")

QUERY_KIND_LESS_THAN = 0
QUERY_KIND_LESS_EQUAL = 1
QUERY_KIND_EQUAL = 2
QUERY_KIND_NOT_EQUAL = 3
QUERY_KIND_GREATER_THAN = 4
QUERY_KIND_GREATER_EQUAL = 5


class _Query:
    """
    Represent a query to the list.
    """
    __slots__ = ("kind", "arg")

    def __init__(self, kind: int, arg: Any):
        self.kind = kind
        self.arg = arg


class QueryableList(MutableSequence[T], Generic[T]):
    """
    Represent a simple list that can be queried with indexer.
    """

    def __init__(self, initial_value: Iterable[T] = None) -> None:
        self._underlying_list = list(initial_value)  \
            if initial_value is not None  \
            else []

    def insert(self, index: SupportsIndex, value: T) -> None:
        self._underlying_list.insert(index, value)

    def __getitem__(self, index: Any) -> Any:
        if isinstance(index, (SupportsIndex, slice)):
            return self._underlying_list[index]
        elif isinstance(index, _Query):
            query_kind = index.kind
            query_arg = index.arg
            query_filter = None
            if query_kind == QUERY_KIND_LESS_THAN:
                query_filter = filter(
                    lambda v: v < query_arg,
                    self._underlying_list
                )
            elif query_kind == QUERY_KIND_LESS_EQUAL:
                query_filter = filter(
                    lambda v: v <= query_arg,
                    self._underlying_list
                )
            elif query_kind == QUERY_KIND_EQUAL:
                query_filter = filter(
                    lambda v: v == query_arg,
                    self._underlying_list
                )
            elif query_kind == QUERY_KIND_NOT_EQUAL:
                query_filter = filter(
                    lambda v: v != query_arg,
                    self._underlying_list
                )
            elif query_kind == QUERY_KIND_GREATER_THAN:
                query_filter = filter(
                    lambda v: v > query_arg,
                    self._underlying_list
                )
            elif query_kind == QUERY_KIND_GREATER_EQUAL:
                query_filter = filter(
                    lambda v: v >= query_arg,
                    self._underlying_list
                )
            else:
                raise KeyError("index")
            return list(query_filter)
        else:
            raise KeyError("index")

    def __setitem__(self, index: SupportsIndex, value: T) -> None:
        self._underlying_list[index] = value

    def __delitem__(self, index: Any) -> None:
        del self._underlying_list[index]

    def __len__(self) -> int:
        return len(self._underlying_list)

    def __lt__(self, other: Any) -> _Query:
        return _Query(QUERY_KIND_LESS_THAN, other)

    def __le__(self, other: Any) -> _Query:
        return _Query(QUERY_KIND_LESS_EQUAL, other)

    def __eq__(self, other: Any) -> _Query:
        return _Query(QUERY_KIND_EQUAL, other)

    def __ne__(self, other: Any) -> _Query:
        return _Query(QUERY_KIND_NOT_EQUAL, other)

    def __gt__(self, other: Any) -> _Query:
        return _Query(QUERY_KIND_GREATER_THAN, other)

    def __ge__(self, other: Any) -> _Query:
        return _Query(QUERY_KIND_GREATER_EQUAL, other)


if __name__ == "__main__":
    my_queryable_list = QueryableList([1, 2, 3, 4, 100, 200, 100, 200])
    print("Simple indexing: ", my_queryable_list[0])
    print("Slicing: ", my_queryable_list[1:5:2])
    print("Querying: ", my_queryable_list[my_queryable_list >= 3])
    print()

```

运行结果：

```plain
PS > py -3 .\queryable_list.py
Simple indexing:  1
Slicing:  [2, 4]
Querying:  [3, 4, 100, 200, 100, 200]

PS >
```

## 3. 讨论

Python中，能使对象支持索引操作的是以下三个成员函数：

* `__getitem__(self, index)`，实现`my_var = my_list[idx]`；
* `__setitem__(self, index, value)`，实现`my_list[idx] = my_var`；
* `__delitem__(self, index)`，实现`del my_list[idx]`。

比如下面这个样例中的三个对象：

```python
# indexers.py
class GetList:
    def __getitem__(self, index):
        print("GetList.__getitem__, index=", index)
        return 0


class GetSetList:
    def __getitem__(self, index):
        print("GetSetList.__getitem__, index=", index)
        return 0

    def __setitem__(self, index, value):
        print("GetSetList.__setitem__, index=", index, "value=", value)


class GetSetDelList:
    def __getitem__(self, index):
        print("GetSetDelList.__getitem__, index=", index)
        return 0

    def __setitem__(self, index, value):
        print("GetSetDelList.__getitem__, index=", index, "value=", value)

    def __delitem__(self, index):
        print("GetSetDelList.__delitem__, index=", index)


if __name__ == "__main__":
    get_list = GetList()
    tmp = get_list[0]
    try:
        get_list[0] = 1
    except Exception as ex:
        print(ex)

    get_set_list = GetSetList()
    tmp = get_set_list[0]
    get_set_list[0] = 100

    get_set_del_list = GetSetDelList()
    tmp = get_set_del_list[0]
    get_set_del_list[0] = 200
    del get_set_del_list[1]
    print()

```

运行结果：

```plain
PS > py -3 .\indexers.py
GetList.__getitem__, index= 0
'GetList' object does not support item assignment
GetSetList.__getitem__, index= 0
GetSetList.__setitem__, index= 0 value= 100
GetSetDelList.__getitem__, index= 0
GetSetDelList.__getitem__, index= 0 value= 200
GetSetDelList.__delitem__, index= 1

PS >
```

其中`index`可以是任意对象，不一定是传统的`int`类型（或更精确地说，`SupportsIndex`类型）。十分著名的*切片*（slicing）操作，会将一个`slice`对象传入索引器函数：

```python
GetList()[0:10:2]
# prints GetList.__getitem__, index= slice(0, 10, 2)
```

鉴于索引器可以传入任意值，我们就可以通过自定义比较操作符来达到查询的目的，具体实现见“解决方案”一节。
