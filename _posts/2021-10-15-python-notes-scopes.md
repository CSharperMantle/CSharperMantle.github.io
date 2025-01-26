---
layout: post
title: "Python随笔（3）：作用域 Scopes"
date: 2021-10-15T07:58:46+08:00
lang: zh-Hans
categories: python-notes
---

## 0. 前言

变量与其*作用域*（scope）是大部分计算机语言入门所不能回避的问题。但是，在传统C-like语言中存在的“作用域”概念并不完全适用于Python。本文将对Python的作用域机制进行分析。

**本文中使用的软件环境**：
* **Python Interpreter**: `Python 3.7.0 (v3.7.0:1bf9cc5093, Jun 27 2018, 04:59:51) [MSC v.1914 64 bit (AMD64)] on win32` （CPython）
* **Rust Compiler (rustc)**: `rustc 1.55.0 (c8dfcfe04 2021-09-06)`
* **Clang (clang++)**: `clang version 12.0.1`

## 1. 问题描述

代码片段如下：

Python:

```python
# scope_py.py

def my_fun(flag):
    var_a = 100
    if flag:
        var_b = 200
    return var_a + var_b


if __name__ == "__main__":
    print(my_fun(True))

```

C++:
```cpp
// scope_cpp.cpp

#include <cstdio>

int my_fun(bool flag) {
    auto var_a = 100;
    if (flag) {
        auto var_b = 200;
    }
    return var_a + var_b;
} 

int main(int argc, char const *argv[])
{
    std::printf("%d\r\n", my_fun(true));
    return 0;
}

```

Rust:
```rust
// scope_rust.rs

fn my_fun(flag: bool) -> i32 {
    let var_a: i32 = 100;
    if flag {
        let var_b: i32 = 200;
    }
    var_a + var_b
}

fn main() {
    print!("{}", my_fun(true));
}

```

试判断以上代码片段能否正常编译（如果需要）和运行，对于其中能正常运行的代码片段，给出运行结果。

## 2. 解决方案

### 2.1. Python

**编译命令**：N/A

```plain
PS > py -3 .\scope_py.py
300
PS >
```

**结果**：输出答案`300`

### 2.2. C++

**编译命令**：`clang++ .\scope_cpp.cpp -o scope_cpp.exe -O0 -g`

```plain
PS > clang++ .\scope_cpp.cpp -o scope_cpp.exe -O0 -g
.\scope_cpp.cpp:10:20: error: use of undeclared identifier 'var_b'; did you mean 'var_a'?
    return var_a + var_b;
                   ^~~~~
                   var_a
.\scope_cpp.cpp:6:10: note: 'var_a' declared here
    auto var_a = 100;
         ^
1 error generated.
PS >
```

**结果**：编译失败。

### 2.3. Rust

**编译命令**：`rustc .\scope_rust.rs -C opt-level=0`

```plain
PS > rustc .\scope_rust.rs -C opt-level=0
error[E0425]: cannot find value `var_b` in this scope
 --> .\scope_rust.rs:8:13
  |
8 |     var_a + var_b
  |             ^^^^^ help: a local variable with a similar name exists: `var_a`

error: aborting due to previous error

For more information about this error, try `rustc --explain E0425`.
PS >
```

**结果**：编译失败。

## 3. 讨论

熟悉C-like语言的程序员在看到`scope_py.py`试图访问一个在`if`语句的语句体中定义的变量`var_b`时，可能会想当然地认为该操作会引起`NameError`。他们认为，在控制流离开`if`语句体时，`var_b`和它所含的值都会被销毁，正如我们在之后的两个样例中看到的一样：C++和Rust语言中类似的操作会产生编译错误，提示在当前作用域内找不到指定的*标识符*（identifier）。

这种不一致性，最终归因于Python对代码*块*（block）以及*名称解析*（resolution of names）的特殊规定，这也是在使用变量时Python与C-like语言最大的差别之一。

Python中将标识符称作*名称*（name）：

> *Names* refer to objects. (1)
> 
> Identifiers (also referred to as *names*) are described by the following lexical definitions. (2)
> 
> (1): [Python 3.7 Reference 4.2.1. Binding of names](https://docs.python.org/3.7/reference/executionmodel.html#binding-of-names)
> 
> (2): [Python 3.7 Reference 2.3. Identifiers and keywords](https://docs.python.org/3.7/reference/lexical_analysis.html?highlight=identifier#identifiers)

为了方便起见，我们将沿用“标识符”这一称呼。

### 3.1. 作用域与块

[Python 3.7 Reference 4.2.2. Resolution of names](https://docs.python.org/3.7/reference/executionmodel.html#resolution-of-names)中对于名称解析是这样描述的：

> A *scope* defines the visibility of a name within a block. If a local variable is defined in a block, its scope includes that block. If the definition occurs in a function block, the scope extends to any blocks contained within the defining one, unless a contained block introduces a different binding for the name.

简单翻译一下可以得到以下结论：

1. 标识符的*作用域*（scope）指的是该标识符在块中的可见性。
2. 如果在一个标识符`i`在某一个块`B`中被定义，它的作用域包括`B`；如果`B`是一个函数，那么它的作用域也包含`B`所包含的所有块（也就是说，`i`将在`B`中可见，当`B`是函数时，`i`也对`B`的子块可见）。
3. 标识符可以被*绑定*（bind）。

Python对块的定义见[Python 3.7 Reference 4.1. Structure of a program](https://docs.python.org/3.7/reference/executionmodel.html#structure-of-a-program)：

> A *block* is a piece of Python program text that is executed as a unit. The following are blocks: a module, a function body, and a class definition. Each command typed interactively is a block. A script file [...] is a code block. A script command [...] is a code block. The string argument passed to the built-in functions eval() and exec() is a code block.

其内容可以总结如下：

1. *块*（block）是Python程序的执行单元。
2. 以下全都属于块：
    * 每个*模块*（module），
    * 每个*函数体*（function body），
    * 每个*类*（class）定义，
    * 每一条*以交互方式输入的*（typed interactively，也就是在交互提示符`>>>`后面输入的）命令，
    * 每一个*脚本文件*（script file，直接运行的以`.py`结尾的文件），
    * 一些不在此赘述的其他情况。

我们用一个例子来展示上述内容。

```python
# scope-blocks.py

def fun(flag):
    x = 100

    if flag:
        x = 200

    def inner_fun():
        x = 300

    inner_fun()
    return x


if __name__ == "__main__":
    print(fun(True))

```

上述代码执行后产生以下结果：

```plain
PS > py -3 .\scope-blocks.py
200
PS >
```

我们可以看到，上述代码输出的值是`200`而不是`300`。易得，`fun`是一个函数，所以它是一个块，标识符`x`最先定义（或者说绑定，详见[Python 3.7 Reference 4.2.1. Binding of names](https://docs.python.org/3.7/reference/executionmodel.html#binding-of-names)）于块`fun`中。`if`不属于一个块，所以在它内部对`x`的赋值不构成一个*不同的绑定*（a different binding），所以当`flag == True`时，`fun`中的`x`被赋值为`200`。

`inner_fun`是一个函数，所以它是一个块。虽然函数`fun`中标识符`x`的作用域包括`inner_fun`，但是`inner_fun`对`x`进行了赋值操作，视为一个对标识符`x`的新的、不同的绑定，所以`inner_fun`中标识符`x`不再指代`fun`中的`x`，后者的值因此并没有改变。所以，最后的输出结果为`200`。

### 3.2. 名称解析

有了实际的体验后，我们现在可以看看名称解析的形式化定义了。[Python 3.7 Reference 4.2.2. Resolution of names](https://docs.python.org/3.7/reference/executionmodel.html#resolution-of-names)中这么写：

> When a name is used in a code block, it is resolved using the nearest enclosing scope. [...]
> 
> When a name is not found at all, a `NameError` exception is raised. [...]
> 
> If a name binding operation occurs anywhere within a code block, all uses of the name within the block are treated as references to the current block. [...]
> 
> If the `global` statement occurs within a block, all uses of the name specified in the statement refer to the binding of that name in the top-level namespace. [...] The `global` statement must precede all uses of the name.
> 
> The `global` statement has the same scope as a name binding operation in the same block.
> 
> The `nonlocal` statement causes corresponding names to refer to previously bound variables in the nearest enclosing function scope. [...]

总结如下：

1. 标识符以就近原则进行解析。
2. 如果没有找到任何关于该标识符的定义，抛出`NameError`。
3. 如果在一个块内对某标识符进行了重绑定，则该块内对该标识符的**所有**使用都将被替换为该块内的绑定，而不是从父块处继承的、原来的绑定，且与重绑定发生的具体位置无关。换言之，解释器会通过预先扫描整个块来确定是否进行了重绑定。
4. `global`关键字将标识符重绑定至全局命名空间内的同名标识符。（可能有点抽象，详见下面的例子。）
5. `nonlocal`关键字将标识符指向（并未发生重绑定）至通过就近原则解析的上一个同名标识符。（详见下面的例子。）

下面，我们通过一个例子来加深对于名称解析的了解。

```python
# scope-blocks-2.py

my_var = 100


def foo():
    my_var = 200
    print("my_var in foo(): {}".format(my_var))


def bar():
    global my_var
    my_var = 200
    print("my_var in bar(): {}".format(my_var))


def grok():
    secret = 500

    def blah():
        secret = 600
    blah()
    print("secret in grok() after blah(): {}".format(secret))

    def blaz():
        nonlocal secret
        secret = 600
    blaz()
    print("secret in grok() after blaz(): {}".format(secret))


if __name__ == "__main__":
    print("my_var in global before foo(): {}".format(my_var))
    foo()
    print("my_var in global after foo(): {}".format(my_var))

    print("my_var in global before bar(): {}".format(my_var))
    bar()
    print("my_var in global after bar(): {}".format(my_var))

    grok()

```

运行结果：

```plain
PS > py -3 .\scope-blocks-2.py
my_var in global before foo(): 100
my_var in foo(): 200
my_var in global after foo(): 100
my_var in global before bar(): 100
my_var in bar(): 200
my_var in global after bar(): 200
secret in grok() after blah(): 500
secret in grok() after blaz(): 600
PS >
```

这里的分析不多描述，一句话：`global`使标识符指向全局同名标识符，`nonlocal`使标识符指向上一个块内的同名标识符。

### 3.3. C-like语言中的块

这类语言中的块均以大括号（`{`和`}`）分割。下面是一个例子。但由于这些语言中对*声明*（declaration）有显式要求，所以标识符作用域一般不是问题。

```cpp
// scope-blocks_cpp.cpp

#include <cstdio>

int my_var = 100;

void foo() {
    my_var = 200;
}

void bar() {
    int my_var = 200;
}

int main(int, char const *[])
{
    std::printf("my_var before foo(): %d\r\n", my_var);
    foo();
    std::printf("my_var after foo(): %d\r\n", my_var);
    std::printf("my_var before bar(): %d\r\n", my_var);
    bar();
    std::printf("my_var after bar(): %d\r\n", my_var);
    return 0;
}

```

编译运行结果：

```plain
PS > clang++ .\scope-blocks_cpp.cpp -o scope-blocks_cpp.exe -Og -Wall -Wextra -Wpedantic
.\scope-blocks_cpp.cpp:12:9: warning: unused variable 'my_var' [-Wunused-variable]
    int my_var = 200;
        ^
1 warning generated.
PS > .\scope-blocks_cpp.exe
my_var before foo(): 100
my_var after foo(): 200
my_var before bar(): 200
my_var after bar(): 200
PS >
```
