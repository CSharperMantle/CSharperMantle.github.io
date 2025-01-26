---
layout: post
title: "Python随笔（1）：int常量池 Constant Pooling of int"
date: 2020-08-24T17:51:24+08:00
lang: zh-Hans
categories: python-notes
---
## 0. 前言
浙江省新版高中技术教材将采用Python 3作为信息技术教学语言。作为一名高一学生，笔者开始复习自己的Python知识。复习之余，特意开设这个系列，来记录自己的复习所得。

本次笔记中提到的问题由笔者的一位同学提出，与Python中的`int object pool`有关。

## 1. 问题描述
代码片段如下：

```python
var_a = 1
var_b = 1
print("Address: var_a: {0} var_b: {1}".format(id(var_a), id(var_b)))
print("var_a is var_b? {0}".format(var_a is var_b))

var_c = 300
var_d = 300
print("Address: var_c: {0} var_d: {1}".format(id(var_c), id(var_d)))
print("var_c is var_d? {0}".format(var_c is var_d))
```

在Python shell中执行产生如下结果：

```plain
>>> 
>>> var_a = 1
>>> var_b = 1
>>> print("Address: var_a: {0} var_b: {1}".format(id(var_a), id(var_b)))
Address: var_a: 9310336 var_b: 9310336
>>> print("var_a is var_b? {0}".format(var_a is var_b))
var_a is var_b? True
>>> 
>>> var_c = 300
>>> var_d = 300
>>> print("Address: var_c: {0} var_d: {1}".format(id(var_c), id(var_d)))
Address: var_c: 140399450822160 var_d: 140399450823472
>>> print("var_c is var_d? {0}".format(var_c is var_d))
var_c is var_d? False
>>>                                                                                 
```

为什么同样是`int`类型的值，在对象地址和`is`判断中会有差别？

## 2. 解决方案与讨论

Python 3的C语言实现（又称CPython，即 python.org 上提供下载的版本）中，存在着`int`对象缓存池，即`int object pool`。为了提高解释器的运行效率，CPython会默认在解释器初始化时创建好一小部分（最常用的）`int`对象，存储在一个数组中。当这些`int`被引用时，解释器便直接返回已经缓存好的对象地址，而无需重新分配。这点在CPython的代码中可以清晰地看到。

```c
// Python-3.8.5/Objects/longobject.c, L18-L23
#ifndef NSMALLPOSINTS
#define NSMALLPOSINTS           257
#endif
#ifndef NSMALLNEGINTS
#define NSMALLNEGINTS           5
#endif
```

上面这段代码中，CPython预定义了两个宏，分别定义了“较小数字”的正边界（`NSMALLPOSINTS`）和“较小数字”的负边界（`NSMALLNEGINTS`）。也就是说，CPython中的`int object pool`边界在此定义。

```c
// Python-3.8.5/Objects/longobject.c, L37-L43

#if NSMALLNEGINTS + NSMALLPOSINTS > 0
/* Small integers are preallocated in this array so that they
   can be shared.
   The integers that are preallocated are those in the range
   -NSMALLNEGINTS (inclusive) to NSMALLPOSINTS (not inclusive).
*/
static PyLongObject small_ints[NSMALLNEGINTS + NSMALLPOSINTS];
```
这段代码创建了一个`PyLongObject`的数组。这个数组中可以放下在`[NSMALLNEGINTS, NSMALLPOSINTS)`（左闭右开）之内的数。

```c
// Python-3.8.5/Objects/longobject.c, L48-L79

static PyObject *
get_small_int(sdigit ival)
{
    PyObject *v;
    assert(-NSMALLNEGINTS <= ival && ival < NSMALLPOSINTS);
    v = (PyObject *)&small_ints[ival + NSMALLNEGINTS];
    Py_INCREF(v);
#ifdef COUNT_ALLOCS
    if (ival >= 0)
        _Py_quick_int_allocs++;
    else
        _Py_quick_neg_int_allocs++;
#endif
    return v;
}
#define CHECK_SMALL_INT(ival) \
    do if (-NSMALLNEGINTS <= ival && ival < NSMALLPOSINTS) { \
        return get_small_int((sdigit)ival); \
    } while(0)

static PyLongObject *
maybe_small_long(PyLongObject *v)
{
    if (v && Py_ABS(Py_SIZE(v)) <= 1) {
        sdigit ival = MEDIUM_VALUE(v);
        if (-NSMALLNEGINTS <= ival && ival < NSMALLPOSINTS) {    // <=== 关注这行
            Py_DECREF(v);
            return (PyLongObject *)get_small_int(ival);
        }
    }
    return v;
}
```

这个函数实现了判断数字是否在缓存范围内并获取缓存地址的功能，其中标有标记的一行便是关键的判断语句。该语句实现了对上述范围的判断。

考虑如下两段代码：
```python
# code/python_int_pool_a.py


for x in range(10000, 20000):
    for y in range(0, 100):
        pass

```

```python
# code/python_int_pool_b.py


for x in range(10000, 20000):
    for y in range(300, 400):
        pass

```

我们使用shell内置命令`time`统计两段代码的执行时间，结果如下：

```plain
$ time python ./python_int_pool_a.py

real    0m0.099s
user    0m0.000s
sys     0m0.015s

$ time python ./python_int_pool_b.py

real    0m0.115s
user    0m0.000s
sys     0m0.031s

$
```

明显，同样分配100个`int`，能够使用`int object pool`的`python_int_pool_a.py`（0.099s）远快于直接分配的`python_int_pool_b.py`（0.115s）。常量池的优势便在这里体现出来。

## 3. 延伸

一般来说，我们对于Python代码进行运行时间分析，有以下三种方法：

1. **`time`工具**

最简单的计时方法，一般在想要获取解释器总体运行时间时有较好表现。

**优点：** 简洁直白；内置于shell中；额外开销少；对任意可执行文件皆有效

**缺点：** 输出过于简单，没有具体执行信息；shell之间实现不一致

**样例：**

```plain
$ time python ./python_int_pool_a.py 

real	0m0.071s
user	0m0.046s
sys	    0m0.009s

$ zsh
% time python ./python_int_pool_a.py 
python ./python_int_pool_b.py  0.04s user 0.00s system 99% cpu 0.047 total

%
```

对于它的使用不再赘述。

2. **`cProfile`模块**

CPython自带的性能统计工具，可以精确到每个函数。

**优点：** 使用方便；内置于Python中；精确到每个Python函数

**缺点：** 开销较大；输出繁杂；只针对Python脚本有效；只存在于CPython中

**样例：**

```plain
$ python -m cProfile ./python_int_pool_a.py 
         3 function calls in 0.022 seconds

   Ordered by: standard name

   ncalls  tottime  percall  cumtime  percall filename:lineno(function)
        1    0.022    0.022    0.022    0.022 python_int_pool_a.py:4(<module>)
        1    0.000    0.000    0.022    0.022 {built-in method builtins.exec}
        1    0.000    0.000    0.000    0.000 {method 'disable' of '_lsprof.Profiler' objects}


$ 
```

可以看到，输出内容非常详细，包含了函数调用次数`ncalls`，函数本体（不包括子函数调用）运行总时间`tottime`，函数（包括子函数调用）运行总时间`cumtime`，具体的文件名、行号和函数名。但是对于较大的脚本，`cProfile`便显得过于详细以至于冗杂了：

```plain
$ python -m cProfile gen_pattern.py --help
    ... 省略脚本本身的输出 ...

         24601 function calls (23801 primitive calls) in 0.024 seconds

   Ordered by: standard name

   ncalls  tottime  percall  cumtime  percall filename:lineno(function)
       37    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:1009(_handle_fromlist)
       28    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:103(release)
       28    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:143(__init__)
       28    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:147(__enter__)
       28    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:151(__exit__)
       28    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:157(_get_module_lock)
       28    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:176(cb)
     36/2    0.000    0.000    0.019    0.009 <frozen importlib._bootstrap>:211(_call_with_frames_removed)
      319    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:222(_verbose_message)
        8    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:232(_requires_builtin_wrapper)
       25    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:307(__init__)
       25    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:311(__enter__)
       25    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:318(__exit__)
      100    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:321(<genexpr>)
       16    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:35(_new_module)
       26    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:369(__init__)
       33    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:403(cached)
       25    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:416(parent)
       25    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:424(has_location)
        8    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:433(spec_from_loader)
       25    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:504(_init_module_attrs)
       25    0.000    0.000    0.002    0.000 <frozen importlib._bootstrap>:576(module_from_spec)
       28    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:58(__init__)
     25/2    0.000    0.000    0.020    0.010 <frozen importlib._bootstrap>:663(_load_unlocked)
       26    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:719(find_spec)
        8    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:740(create_module)
        
        ... 此处省略529行 ...

        1    0.000    0.000    0.000    0.000 {method 'write' of '_io.TextIOWrapper' objects}


$
```

> 此处`gen_pattern.py`出自**Open Source Computer Vision Library**（`opencv/opencv`），作者Jaycee（yassiezar），Vladislav Sovrasov（sovrasov），S. Garrido（sergarrido），Nicholas Nadeau（nnadeau），Rong "Mantle" Bao（CSharperMantle）和debjan（debjan）

3. **采用`ld`链接器的运行时库打桩**

使用运行时库打桩机制，我们可以重定向任意函数至我们自己的函数。

**优点：** 高度自定义；自由度高

**缺点：** 只在带有GCC的Linux设备上起效；使用复杂

**样例：**

这里我们打桩分配内存的标准库函数`malloc()`。

```cpp
// code/mymalloc.cpp

#include <cstdio>
#include <dlfcn.h>
#include <stdexcept>

#define LOG_INFO std::printf

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

void* malloc(size_t size)
{
    auto symbol_addr = dlsym(RTLD_NEXT, "malloc");
    if (!symbol_addr)
    {
        throw std::runtime_error(dlerror());
    }
    typedef void* (*__malloc)(size_t);
    auto libc_malloc = reinterpret_cast<__malloc>(symbol_addr);
    auto ptr = libc_malloc(size);

    static thread_local bool called = false;
    if (!called)
    {
        called = true;
        LOG_INFO("malloc(%ld) = %p\n", size, ptr);
        called = false;
    }

    return ptr;
}

void free(void *ptr)
{
    auto symbol_addr = dlsym(RTLD_NEXT, "free");
    if (!symbol_addr)
    {
        throw std::runtime_error(dlerror());
    }
    typedef void (*__free)(void *);
    auto libc_free = reinterpret_cast<__free>(symbol_addr);
    libc_free(ptr);
    LOG_INFO("free() = %p\n", ptr);
}

#ifdef __cplusplus
}
#endif /* __cplusplus */
```

编译、运行：

```plain
$ g++ -o mymalloc.so mymalloc.cpp -shared -fPIC -ldl -D_GNU_SOURCE -g -Wall -Wextra

$ LD_PRELOAD="./mymalloc.so" python ./python_int_pool_a.py 
malloc(72704) = 0x138a2d0
malloc(32) = 0x139c2f0
malloc(2) = 0x139c320
malloc(5) = 0x139c340
free() = 0x139c340
malloc(120) = 0x139c360

...以下省略...

$
```

**THE END**
