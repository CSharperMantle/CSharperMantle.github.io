---
layout: post
title: "Achilles's heel of Nushell"
date: 2025-02-05T19:09:33+08:00
lang: en
description: >-
    Gradual typing is not an excuse for inexpressibility.
tags: topic:dev programming-language shell nushell
---

Statically typing a Nushell script may not be as easy as how its functional appearance implies.

For those unfamiliar with [Nushell](https://www.nushell.sh/): It is a cross-platform shell scripting language implemented in Rust. [The Nu Book](https://www.nushell.sh/book/)[^1] has a [dedicated section](https://www.nushell.sh/book/coming_to_nu.html) mapping many Nushell features from imperative and functional languages. Like any other practically-usable language, it has [its subtleties](https://www.nushell.sh/book/thinking_in_nu.html).

At first glance, Nushell's pipeline provides a very functional look and feel. Compare these two snippets that compute each symbol's prefix code from a given [Huffman's tree](https://en.wikipedia.org/wiki/Huffman_coding), the former in Haskell (sampled from <https://ryanriddle.github.io/haskell-huffman.html>) and the latter in Nushell:

```haskell
encode :: Node -> Node -> [Symbol] -> [Bool]
encode _ _ [] = []
encode codeTree (Leaf s w) (sym:symbols) =
    encode codeTree codeTree symbols
encode codeTree (Interior l r _ _) (sym : symbols) 
    | elem sym (getSymbols l) = False : encode codeTree l (sym:symbols)
    | otherwise               = True  : encode codeTree r (sym:symbols)
```

```nushell
def "into bytes" []: binary -> list<int> { ... }

def get_codes [] {
    def traverse [node, path, codes] {
        match $node {
            { sym: $sym, weight: $_ } => ($codes | append { sym: $sym, code: $path }),
            { left: $left, right: $right, syms: $_, weight: $_ } => {
                traverse $right ($path | append 1) (traverse $left ($path | append 0) $codes)
            }
        }
    }
    traverse $in [] []
        | each { |e| { sym: $e.sym, code_str: ($e.code | each { |c| $c | into string } | str join) } }
}

def encode [codes] {
    $in
        | into bytes
        | each { |byte| $codes | filter { |e| $e.sym == $byte } | first | get "code_str" }
        | str join
}
```

We can see that Nushell has almost the same pattern-matching structure as Haskell. Indeed, the Nushell version applies some imperative commands, like `each`, to simplify the process, but they are totally replaceable with plain pattern matching, which operates on strongly-typed values just like Haskell.

*Strongly-typed?* But we haven't typed it yet! Let's try to define `Node` well.

A `Node` is either a `Leaf` or an `Interior`. Each `Leaf` has a symbol (and its weight) associated and no children, while each `Interior` has no symbols and exactly two children. To support functional state preservation, each `Interior` is assigned its subtree weight and symbols included in its subtree. In Haskell, this is straightforward to express: 

```haskell
data Node = Leaf Symbol Weight
          | Interior Node Node [Symbol] Weight
```

In Nushell, an object is typed as a specialized generic type `record<prop0: TProp0, [...]>`. In this format, we can smoothly type a leaf node as:

```nushell
record<sym: int, weight: int>
```

But how can we type internal nodes? An internal node can have both leaves and other internal nodes as its children. If we write an interior node as

```nushell
record<left: ???, right: ???, syms: list<int>, weight: int>
```

Then what should we plug into these `???`s? These types would refer to themselves, making it impossible to write out an expanded, literal type expression. Now, we are faced with recursive types which Nushell's typing system fails to express.

Recursive types are fundamental to many important concepts. Even most imperative languages support some degree of recursive types, as is demonstrated in this C code:

```c
typedef union Node_ {
    struct Leaf_ {
        char sym;
        int weight;
    } leaf;
    struct Interior_ {
        union Node_ *left;
        union Node_ *right;
        char *syms;
        size_t len_syms;
        int weight;
    } interior;
} Node_t;
```

This code utilizes pointers to [incomplete types](https://en.cppreference.com/w/c/language/type#Incomplete_types) to mimic recursive types. In C, this is possible because the size of a pointer is irrelevant to its underlying type. Compilers can then calculate the layout of `struct Interior_` (thus `union Node_`) without seeing a complete definition of `union Node_`.

In Nushell, however, the lack of ways to designate a custom type has forced us to put stinky, ugly `any` into these `???`s. This problem quickly gets more severe if we try to type `get_codes.traverse`. We have no choice but to type `node` as `any`:

```nushell
def get_codes []: record<left: any, right: any, syms: list<int>, weight: int> -> list<record<sym: int, code_str: string>> {
    def traverse [node: any, path: list<int>, codes: list<any>] { ... }
    traverse $in [] []
        | each { |e| { ... } }
}
```

The Nushell pros rationalize this as being [gradually typed](https://www.nushell.sh/lang-guide/chapters/types/00_types_overview.html). A mix of statically-typed and dynamically-typed values makes up the Nushell language. But it just defers the problem to run time. Allowing this compromise to exist is just like admitting defeat to bugs, a regression in terms of both its functional semantics and today's trends of fast-failing.

In a nutshell, the inability to designate user-specialized types is the Achilles's heel of Nushell. If you seek a purely functional experience in Nushell, you'd better learn to coexist with some jarring `any`.

------

### Footnotes

[^1]: Similar to [other](https://doc.rust-lang.org/nomicon/) [Rust](https://doc.rust-lang.org/book/) [projects](https://doc.rust-lang.org/cargo/index.html), the Nu Book is Nushell's compilation of documentation and guides, covering basic, intermediate and advanced chapters.
