---
layout: post
title: "Have fun decoding in Chisel"
date: 2025-03-05T08:09:57+08:00
lang: en
tags: topic:dev ee digital-logics chisel
use_mathjax: true
---

- [0. Introduction](#0-introduction)
- [1. The problem](#1-the-problem)
- [2. `TruthTable`: Programmatic logic generation](#2-truthtable-programmatic-logic-generation)
- [3. `DecodeTable`: Combined truth tables](#3-decodetable-combined-truth-tables)
  - [Extensibility](#extensibility)
- [4. Conclusion](#4-conclusion)

------

## 0. Introduction

Decoders are everyday components in digital logic designs. Maintaining large, complex decoding circuits can be challenging in vanilla SystemVerilog. Today, we are exploring the utilities provided by [`chisel3.util.experimental.decode._`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/util/experimental/decode/index.html) to decode whatever we want elegantly. We'll see how Chisel's *circuit generator* nature contributes to its simplicity and extensibility.

Chisel's experimental public APIs often lack usage information. This post is also intended to be an incomprehensive example of (in my view) important yet undocumented utilities.

## 1. The problem

Suppose we are making an automatic burger maker and wish to use an FPGA as its controller. The stock contains these burgers:

| Burger           | ID  | Buns? | Cheese? | Bacon? | Patty? | Pickles? | Ketchup? |
| ---------------- | --- | :---: | :-----: | :----: | :----: | :------: | :------: |
| Classic Cheezy   | 0   |   Y   |    Y    |        |   Y    |    Y     |    Y     |
| Bacon Deluxe     | 1   |   Y   |    Y    |   Y    |   Y    |    Y     |    Y     |
| Double Stack     | 2   |   Y   |    Y    |   Y    |   Y    |          |    Y     |
| Veggie Delight   | 3   |   Y   |         |        |        |    Y     |    Y     |
| Bacon Bliss      | 4   |   Y   |    Y    |   Y    |   Y    |          |    Y     |
| Bunless Fury     | 5   |       |         |   Y    |   Y    |    Y     |          |
| Ultimate Supreme | 6   |   Y   |    Y    |   Y    |   Y    |    Y     |    Y     |

The controller needs to know which burger contains what ingredients. That is, we are tasked to design a burger *decoder* that decodes a burger's ID into each ingredient's `enable` signal. When a burger contains a certain ingredient, its `en`[^1] signal should *assert* (go high).

If you are a seasoned HDL designer, you may already have an approach in mind. For example, we may write a SystemVerilog module like this:

```verilog
`define BURGER_CLASSIC_CHEEZY   3'b000
`define BURGER_BACON_DELUXE     3'b001
`define BURGER_DOUBLE_STACK     3'b010
`define BURGER_VEGGIE_DELIGHT   3'b011
`define BURGER_BACON_BLISS      3'b100
`define BURGER_BUNLESS_FURY     3'b101
`define BURGER_ULTIMATE_SUPREME 3'b110

module BurgerDecoder (
    input  [2:0] burger,
    output       valid,
    output       en_buns,
    output       en_cheese,
    output       en_bacon,
    output       en_patty,
    output       en_pickles,
    output       en_ketchup
);
    assign valid = burger != 3'b111;

    assign en_buns = burger != `BURGER_BUNLESS_FURY;
    assign en_cheese = (burger == `BURGER_CLASSIC_CHEEZY) ||
                       (burger == `BURGER_BACON_DELUXE)   ||
                       (burger == `BURGER_DOUBLE_STACK)   ||
                       (burger == `BURGER_BACON_BLISS)    ||
                       (burger == `BURGER_ULTIMATE_SUPREME);
    assign en_bacon = (burger == `BURGER_BACON_DELUXE) ||
                      (burger == `BURGER_DOUBLE_STACK) ||
                      (burger == `BURGER_BACON_BLISS)  ||
                      (burger == `BURGER_BUNLESS_FURY) ||
                      (burger == `BURGER_ULTIMATE_SUPREME);
    assign en_patty = burger != `BURGER_VEGGIE_DELIGHT;
    assign en_pickles = (burger == `BURGER_CLASSIC_CHEEZY) ||
                        (burger == `BURGER_BACON_DELUXE)   ||
                        (burger == `BURGER_VEGGIE_DELIGHT) ||
                        (burger == `BURGER_BUNLESS_FURY)   ||
                        (burger == `BURGER_ULTIMATE_SUPREME);
    assign en_ketchup = burger != `BURGER_BUNLESS_FURY;
endmodule
```

This module can achieve our desired results, but its extensibility is not delightful. If we add 90 more kinds of burgers in the future, it will be very cumbersome to maintain individual expressions for each single output bit. That is to say, the number of *rows* can't get too high for this module to be maintainable.

Alternatively, `casez` statements can express the same circuit:

```verilog
`define ...

module BurgerDecoder (
    input      [2:0] burger,
    output reg       valid,
    output reg       en_buns,
    output reg       en_cheese,
    output reg       en_bacon,
    output reg       en_patty,
    output reg       en_pickles,
    output reg       en_ketchup
);
    always_comb begin
        casez (burger)
            `BURGER_CLASSIC_CHEEZY:   begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b1110111; end
            `BURGER_BACON_DELUXE:     begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b1111111; end
            `BURGER_DOUBLE_STACK:     begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b1111101; end
            `BURGER_VEGGIE_DELIGHT:   begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b1100011; end
            `BURGER_BACON_BLISS:      begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b1111101; end
            `BURGER_BUNLESS_FURY:     begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b1001110; end
            `BURGER_ULTIMATE_SUPREME: begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b1111111; end
            default:                  begin {valid, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 7'b0xxxxxx; end
        endcase
    end
endmodule
```

This approach also works, and adding new burgers is rather easy. However, if each burger has 25 ingredients, adding all these components will be a new headache. The number of *columns* is now the limiting factor of its maintainability. The same happens when outputs are no longer single-bit. See this line below, and try to guess each component's value!

```verilog
begin {valid, size, en_buns, en_cheese, en_bacon, en_patty, en_pickles, en_ketchup} = 9'b110111111; end
```

And this is when Chisel comes to the rescue.

## 2. `TruthTable`: Programmatic logic generation

**We write Verilog to describe hardware. We write Chisel to generate a description of hardware.**

As *hardware generators*, Chisel apps are compiled into executables that *elaborate* (i.e. generate) an *intermediate circuit representation* at run time. This IR can then be:

1. emitted into HDLs like SystemVerilog, and then synthesized to hardware,
2. serialized into some binary format, and later revived elsewhere,
3. fed into simulators and symbolic verifiers.

Generating this intermediate representation is distinct from actual hardware synthesis. What Chisel users do is:

1. Instantiate hardware types, either abstract ones like `UInt(16.W)` or concrete ones like `0xdead.U`,
2. Contain them in hardware objects, for example, `Wire(UInt(16.W))`, `WireInit(0xdead.U(16.W))` and `RegInit(0.U(4.W))`,
3. Apply connection operators, like `:=` and `<>` to hardware objects.

It is totally up to the user to decide in what way to apply them, allowing for great flexibility compared with Verilog `generate` blocks. Thanks to Chisel's host language, Scala, we will have a bunch of options to perform these three steps to create our desired IR (thus our desired circuits).

[`chisel3.util.experimental.decode.TruthTable`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/util/experimental/decode/TruthTable.html) is our go-to tool for generating logics from truth tables. The Javadoc for this module tells almost nothing about its usage.[^2] But in fact, it is quite similar to `casez` statements but allows more flexible entry generation.

For example, an 8-to-3 priority encoder can be written in Chisel with `TruthTable` as this:

```scala
import chisel3._
import chisel3.util._
import chisel3.util.experimental.decode._

class PriorityEncoder extends Module {
  class Port extends Bundle {
    val din   = Input(UInt(8.W))
    val dout  = Output(UInt(3.W))
    val valid = Output(Bool())
  }
  val io = IO(new Port)

  private val table = TruthTable(
    Seq(
      BitPat("b00000001") -> BitPat(0.U(3.W)),
      BitPat("b0000001?") -> BitPat(1.U(3.W)),
      BitPat("b000001??") -> BitPat(2.U(3.W)),
      BitPat("b00001???") -> BitPat(3.U(3.W)),
      BitPat("b0001????") -> BitPat(4.U(3.W)),
      BitPat("b001?????") -> BitPat(5.U(3.W)),
      BitPat("b01??????") -> BitPat(6.U(3.W)),
      BitPat("b1???????") -> BitPat(7.U(3.W))
    ),
    BitPat("b???")
  )

  io.dout  := decoder(io.din, table)
  io.valid := io.din.orR
}
```

The [`apply`](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/util/experimental/decode/TruthTable$.html#apply(table:Iterable[(chisel3.util.BitPat,chisel3.util.BitPat)],default:chisel3.util.BitPat,sort:Boolean):chisel3.util.experimental.decode.TruthTable) method of `TruthTable` takes two mandatory arguments: the first is an [`Iterable`](https://www.scala-lang.org/api/2.13.x/scala/collection/Iterable.html) that produces `(BitPat, BitPat)`s, and the second is a default output if none of the patterns are matched. The `Iterable` produces many pairs of input/outputs, and the input [`BitPat`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/util/BitPat.html)s can have don't care bits, the same as `casez` statements.

> **Attention!** When don't care bits ("`?`") appear on the left-hand side of a truth table, they mean a wildcard matching. When they appear on the right-hand side, they mean "any output is allowed". If you haven't heard of this convention yet, go through your digital logic textbook again.

Since the first argument is an `Iterable`, it can be generated in many ways. In the above case, we use a Scala [`Seq`](https://www.scala-lang.org/api/2.13.x/scala/collection/Seq.html) to create a literal value. We can also use all Scala functional facilities to transform our input before we feed it into our `TruthTable`. Remember, these processes all happen at elaboration time, which is independent of the later emission stage.

Here, we create a `case class` for our burgers, write a list of `Burger` instances, and then use `map` to programmatically create truth tables from them.

```scala
import chisel3._
import chisel3.util._
import chisel3.util.experimental.decode._

case class Burger(
  val name:       String,
  val encoding:   BitPat,
  val hasBuns:    Boolean,
  val hasCheese:  Boolean,
  val hasBacon:   Boolean,
  val hasPatty:   Boolean,
  val hasPickles: Boolean,
  val hasKetchup: Boolean) {}

class BurgerDecoder extends Module {
  class Port extends Bundle {
    val burger    = Input(UInt(3.W))
    val valid     = Output(Bool())
    val enBuns    = Output(Bool())
    val enCheese  = Output(Bool())
    val enBacon   = Output(Bool())
    val enPatty   = Output(Bool())
    val enPickles = Output(Bool())
    val enKetchup = Output(Bool())
  }
  val io = IO(new Port)

  private val burgers = Seq(
    // scalafmt: { align.tokens.add = [ { code = "," } ] }
    Burger("Classic Cheezy",   BitPat("b000"), true,  true,  false, true,  true,  true),
    Burger("Bacon Deluxe",     BitPat("b001"), true,  true,  true,  true,  true,  true),
    Burger("Double Stack",     BitPat("b010"), true,  true,  true,  true,  false, true),
    Burger("Veggie Delight",   BitPat("b011"), true,  false, false, false, true,  true),
    Burger("Bacon Bliss",      BitPat("b100"), true,  true,  true,  true,  false, true),
    Burger("Bunless Fury",     BitPat("b101"), false, false, true,  true,  true,  false),
    Burger("Ultimate Supreme", BitPat("b110"), true,  true,  true,  true,  true,  true)
    // scalafmt: { align.tokens.add = [] }
  )

  private val validTable = TruthTable(
    burgers map (b => b.encoding -> BitPat(1.U(1.W))),
    BitPat(0.U(1.W))
  )
  io.valid := decoder(io.burger, validTable)

  private val bunsTable = TruthTable(
    burgers map (b => b.encoding -> BitPat(b.hasBuns.B.asUInt)),
    BitPat(0.U(1.W))
  )
  io.enBuns := decoder(io.burger, bunsTable)

  private val cheeseTable = TruthTable(
    burgers map (b => b.encoding -> BitPat(b.hasCheese.B.asUInt)),
    BitPat(0.U(1.W))
  )
  io.enCheese := decoder(io.burger, cheeseTable)

  private val baconTable = TruthTable(
    burgers map (b => b.encoding -> BitPat(b.hasBacon.B.asUInt)),
    BitPat(0.U(1.W))
  )
  io.enBacon := decoder(io.burger, baconTable)

  private val pattyTable = TruthTable(
    burgers map (b => b.encoding -> BitPat(b.hasPatty.B.asUInt)),
    BitPat(0.U(1.W))
  )
  io.enPatty := decoder(io.burger, pattyTable)

  private val picklesTable = TruthTable(
    burgers map (b => b.encoding -> BitPat(b.hasPickles.B.asUInt)),
    BitPat(0.U(1.W))
  )
  io.enPickles := decoder(io.burger, picklesTable)

  private val ketchupTable = TruthTable(
    burgers map (b => b.encoding -> BitPat(b.hasKetchup.B.asUInt)),
    BitPat(0.U(1.W))
  )
  io.enKetchup := decoder(io.burger, ketchupTable)
}
```

This module elaborates to the following SystemVerilog code:

```verilog
// Generated by CIRCT firtool-1.77.0
module BurgerDecoder(
  input  [2:0] io_burger,
  output       io_valid,
               io_enBuns,
               io_enCheese,
               io_enBacon,
               io_enPatty,
               io_enPickles,
               io_enKetchup
);

  wire [2:0] io_valid_invInputs = ~io_burger;
  wire [2:0] io_enBuns_invInputs = ~io_burger;
  wire [2:0] io_enCheese_invInputs = ~io_burger;
  wire [1:0] io_enBacon_invInputs = ~(io_burger[1:0]);
  wire [1:0] io_enPatty_invInputs = ~(io_burger[1:0]);
  wire [2:0] io_enPickles_invInputs = ~io_burger;
  wire [2:0] io_enKetchup_invInputs = ~io_burger;
  assign io_valid =
    |{io_valid_invInputs[0], io_valid_invInputs[1], io_valid_invInputs[2]};
  assign io_enBuns = |{io_enBuns_invInputs[0], io_enBuns_invInputs[2]};
  assign io_enCheese =
    |{io_enCheese_invInputs[0], &{io_enCheese_invInputs[1], io_enCheese_invInputs[2]}};
  assign io_enBacon =
    |{&{io_burger[0], io_enBacon_invInputs[1]},
      &{io_enBacon_invInputs[0], io_burger[1]},
      &{io_enBacon_invInputs[0], io_burger[2]}};
  assign io_enPatty = |{io_enPatty_invInputs[0], io_enPatty_invInputs[1]};
  assign io_enPickles =
    |{&{io_enPickles_invInputs[1], io_enPickles_invInputs[2]},
      &{io_burger[0], io_enPickles_invInputs[1]},
      &{io_burger[0], io_enPickles_invInputs[2]},
      &{io_enPickles_invInputs[0], io_burger[1], io_burger[2]}};
  assign io_enKetchup = |{io_enKetchup_invInputs[0], io_enKetchup_invInputs[2]};
endmodule
```

It is logically equivalent to the Verilog versions. An optimizing synthesizer should produce the same circuit.

## 3. `DecodeTable`: Combined truth tables

In [Section 2](#2-truthtable-programmatic-logic-generation), we use `TruthTable`s to generate hardware circuits from Scala-land data. However, we instantiated 7 `TruthTable`s for each output field, and all of them have almost the same structure. Is there a way to deduplicate these?

We can view this problem from the perspective of Boolean functions. We are given many decoders $f_i: X \rightarrow Y_i$ and all of them are defined over the same domain. Thus, it is natural to combine them into a single decoder $f: X \rightarrow \underset{i}{\times}Y_i$. Each $y \in Y_i$ is called a *field*, and the combined decoder $f$ is a *multi-field decoder*. The synthesizer is usually better at optimizing these combined decoders since their input-output relations are clearer.

Chisel provides a convenient way to generate multi-field decoders. These traits and classes/objects are of great importance:

* [`chisel3.util.experimental.decode.DecodeTable`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/util/experimental/decode/DecodeTable.html): The main class/object for a multi-field decoder $f$.
* [`chisel3.util.experimental.decode.DecodePattern`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/util/experimental/decode/DecodePattern.html): Trait for $X$. We need to derive this trait to make our own $X$.
* [`chisel3.util.experimental.decode.DecodeField`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/util/experimental/decode/DecodeField.html): Trait for a single $Y_i$. We need to derive this trait to make our own $Y_i$. We can designate our own Chisel hardware type for each $Y_i$.
* [`chisel3.util.experimental.decode.BoolDecodeField`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/util/experimental/decode/BoolDecodeField.html): Ditto, but the output is a `Bool()`. In fact, it extends `DecodeField[T <: DecodePattern, Bool]`.

Basically, when we create our multi-field decoders, we define the input domain $X$ by deriving `DecodePattern`, and each output field $Y_i$ by deriving `DecodeField`. Then we create a sequence of valid $x_i \in X$ and plug it into the constructor of `DecodeTable` together with a sequence of $Y_i$. And, hey presto, we can get the decoded output.

Let's implement our burger ingredient decoder in `DecodeTable`.

```scala
case class Burger(
  val name:       String,
  val encoding:   BitPat,
  val hasBuns:    Boolean,
  val hasCheese:  Boolean,
  val hasBacon:   Boolean,
  val hasPatty:   Boolean,
  val hasPickles: Boolean,
  val hasKetchup: Boolean)
    extends DecodePattern {
  override def bitPat: BitPat = encoding
}

object HasBunsField extends BoolDecodeField[Burger] {
  override def name = "hasBuns"
  override def genTable(burger: Burger): BitPat = {
    if (burger.hasBuns) y else n
  }
}

object HasCheeseField extends BoolDecodeField[Burger] {
  override def name = "hasCheese"
  override def genTable(burger: Burger): BitPat = {
    if (burger.hasCheese) y else n
  }
}

object HasBaconField extends BoolDecodeField[Burger] {
  override def name = "hasBacon"
  override def genTable(burger: Burger): BitPat = {
    if (burger.hasBacon) y else n
  }
}

object HasPattyField extends BoolDecodeField[Burger] {
  override def name = "hasPatty"
  override def genTable(burger: Burger): BitPat = {
    if (burger.hasPatty) y else n
  }
}

object HasPicklesField extends BoolDecodeField[Burger] {
  override def name = "hasPickles"
  override def genTable(burger: Burger): BitPat = {
    if (burger.hasPickles) y else n
  }
}

object HasKetchupField extends BoolDecodeField[Burger] {
  override def name = "hasKetchup"
  override def genTable(burger: Burger): BitPat = {
    if (burger.hasKetchup) y else n
  }
}

class BurgerDecoder extends Module {
  class Port extends Bundle {
    val burger    = Input(UInt(3.W))
    val valid     = Output(Bool())
    val enBuns    = Output(Bool())
    val enCheese  = Output(Bool())
    val enBacon   = Output(Bool())
    val enPatty   = Output(Bool())
    val enPickles = Output(Bool())
    val enKetchup = Output(Bool())
  }
  val io = IO(new Port)

  private val burgers = Seq(
    // scalafmt: { align.tokens.add = [ { code = "," } ] }
    Burger("Classic Cheezy",   BitPat("b000"), true,  true,  false, true,  true,  true),
    Burger("Bacon Deluxe",     BitPat("b001"), true,  true,  true,  true,  true,  true),
    Burger("Double Stack",     BitPat("b010"), true,  true,  true,  true,  false, true),
    Burger("Veggie Delight",   BitPat("b011"), true,  false, false, false, true,  true),
    Burger("Bacon Bliss",      BitPat("b100"), true,  true,  true,  true,  false, true),
    Burger("Bunless Fury",     BitPat("b101"), false, false, true,  true,  true,  false),
    Burger("Ultimate Supreme", BitPat("b110"), true,  true,  true,  true,  true,  true)
    // scalafmt: { align.tokens.add = [] }
  )
  private val burgerFields = Seq(
    HasBunsField,
    HasCheeseField,
    HasBaconField,
    HasPattyField,
    HasPicklesField,
    HasKetchupField
  )
  private val table  = new DecodeTable(burgers, burgerFields)
  private val result = table.decode(io.burger)

  io.enBuns    := result(HasBunsField)
  io.enCheese  := result(HasCheeseField)
  io.enBacon   := result(HasBaconField)
  io.enPatty   := result(HasPattyField)
  io.enPickles := result(HasPicklesField)
  io.enKetchup := result(HasKetchupField)
  io.valid     := ???
}
```

In the above code, we extend `DecodePattern` to create our own Scala-land `case class` for our burgers: `Burger`. There's a required method `bitPat` which derives the hardware input pattern for the decoder.

Then, we create an object extending `BoolDecodeField` for each output field. These objects map each `Burger` to the field's output. So, they are also mappings from Scala-land objects to hardware values. For example, this following object maps each `Burger`'s `hasBacon` property to a single-bit `BitPat` hardware value [`y`](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/util/experimental/decode/BoolDecodeField.html#y:chisel3.util.BitPat) or [`n`](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/util/experimental/decode/BoolDecodeField.html#n:chisel3.util.BitPat):

```scala
object HasBaconField extends BoolDecodeField[Burger] {
  override def name = "hasBacon"
  override def genTable(burger: Burger): BitPat = {
    if (burger.hasBacon) y else n
  }
}
```

Afterward, we make a list of possible instances of `Burger`s and plug it into the constructor alongside the list of fields. Finally, we can get each field's output with the decoded `result` and its corresponding `DecodeField` subobject.

Wait! The wire `io.valid` is still not implemented!

Normally, we may consider adding another property `valid` to our `Burger`, and fill the invalid `Burger` entry with other bogus properties. But that's not elegant, since it fails to convey the idea of being "invalid" and "don't care". Let's leverage Scala's awesome [`Option`](https://www.scala-lang.org/api/2.13.x/scala/Option.html) feature to denote this semantically.

We split our `Burger` into two layers of objects. The outer object `BurgerPattern` extends `DecodePattern`, and the inner `BurgerInfo` stores the burger ingredients info. For valid burgers, its `BurgerPattern.info` will be a `Some`, and for invalid entries, it will be a `None`.

```scala
case class BurgerInfo(
  val name:       String,
  val hasBuns:    Boolean,
  val hasCheese:  Boolean,
  val hasBacon:   Boolean,
  val hasPatty:   Boolean,
  val hasPickles: Boolean,
  val hasKetchup: Boolean) {}

case class BurgerPattern(
  val encoding: BitPat,
  val info:     Option[BurgerInfo])
    extends DecodePattern {
  override def bitPat: BitPat = encoding
}
```

Then, we add a `BurgerValidField` that produces the `valid` signal. To minimize the usage of `if`-`else`s, here we use Scala's pattern matching mechanism.

```scala
object BurgerValidField extends BoolDecodeField[BurgerPattern] {
  override def name = "valid"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None    => n
      case Some(_) => y
    }
  }
}
```

We also need to adjust other fields to match the new object structure. Also, for invalid burger ID inputs, we don't care anything about it except for the `valid` signal, so why not set them to [don't cares](https://en.wikipedia.org/wiki/Don%27t-care_term), leaving room for further simplification? For example:

```scala
object HasBaconField extends BoolDecodeField[BurgerPattern] {
  override def name = "hasBacon"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None        => dc
      case Some(value) => if (value.hasBacon) y else n
    }
  }
}
```

The mysterious [`dc`](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/util/experimental/decode/BoolDecodeField.html#dc:chisel3.util.BitPat) stands for "don't care" here, not the superhero universe. Remember that `BoolDecodeField` is a subtrait of `DecodeField`? [Well, `dc` is inherited from `DecodeField`.](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/util/experimental/decode/DecodeField.html#dc:chisel3.util.BitPat)

We also need to adjust the `BurgerPattern` construction, add the new field, and finally retrieve and assign the output.

```scala
private val burgers = Seq(
  // scalafmt: { maxColumn = 512, align.tokens.add = [ { code = "," } ] }
  BurgerPattern(BitPat("b000"), Some(BurgerInfo("Classic Cheezy", true, true, false, true, true, true))),
  BurgerPattern(BitPat("b001"), Some(BurgerInfo("Bacon Deluxe", true, true, true, true, true, true))),
  BurgerPattern(BitPat("b010"), Some(BurgerInfo("Double Stack", true, true, true, true, false, true))),
  BurgerPattern(BitPat("b011"), Some(BurgerInfo("Veggie Delight", true, false, false, false, true, true))),
  BurgerPattern(BitPat("b100"), Some(BurgerInfo("Bacon Bliss", true, true, true, true, false, true))),
  BurgerPattern(BitPat("b101"), Some(BurgerInfo("Bunless Fury", false, false, true, true, true, false))),
  BurgerPattern(BitPat("b110"), Some(BurgerInfo("Ultimate Supreme", true, true, true, true, true, true))),
  BurgerPattern(BitPat("b111"), None)
  // scalafmt: { align.tokens.add = [] }
)
private val burgerFields = Seq(
  BurgerValidField,
  ...
)
...
io.valid := result(BurgerValidField)
```

Putting all of these together, we will get the following code:

```scala
import chisel3._
import chisel3.util._
import chisel3.util.experimental.decode._

case class BurgerInfo(
  val name:       String,
  val hasBuns:    Boolean,
  val hasCheese:  Boolean,
  val hasBacon:   Boolean,
  val hasPatty:   Boolean,
  val hasPickles: Boolean,
  val hasKetchup: Boolean) {}

case class BurgerPattern(
  val encoding: BitPat,
  val info:     Option[BurgerInfo])
    extends DecodePattern {
  override def bitPat: BitPat = encoding
}

object BurgerValidField extends BoolDecodeField[BurgerPattern] {
  override def name = "valid"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None    => n
      case Some(_) => y
    }
  }
}

object HasBunsField extends BoolDecodeField[BurgerPattern] {
  override def name = "hasBuns"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None        => dc
      case Some(value) => if (value.hasBuns) y else n
    }
  }
}

object HasCheeseField extends BoolDecodeField[BurgerPattern] {
  override def name = "hasCheese"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None        => dc
      case Some(value) => if (value.hasCheese) y else n
    }
  }
}

object HasBaconField extends BoolDecodeField[BurgerPattern] {
  override def name = "hasBacon"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None        => dc
      case Some(value) => if (value.hasBacon) y else n
    }
  }
}

object HasPattyField extends BoolDecodeField[BurgerPattern] {
  override def name = "hasPatty"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None        => dc
      case Some(value) => if (value.hasPatty) y else n
    }
  }
}

object HasPicklesField extends BoolDecodeField[BurgerPattern] {
  override def name = "hasPickles"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None        => dc
      case Some(value) => if (value.hasPickles) y else n
    }
  }
}

object HasKetchupField extends BoolDecodeField[BurgerPattern] {
  override def name = "hasKetchup"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None        => dc
      case Some(value) => if (value.hasKetchup) y else n
    }
  }
}

class BurgerDecoder extends Module {
  class Port extends Bundle {
    val burger    = Input(UInt(3.W))
    val valid     = Output(Bool())
    val enBuns    = Output(Bool())
    val enCheese  = Output(Bool())
    val enBacon   = Output(Bool())
    val enPatty   = Output(Bool())
    val enPickles = Output(Bool())
    val enKetchup = Output(Bool())
  }
  val io = IO(new Port)

  private val burgers = Seq(
    // scalafmt: { maxColumn = 512, align.tokens.add = [ { code = "," } ] }
    BurgerPattern(BitPat("b000"), Some(BurgerInfo("Classic Cheezy", true, true, false, true, true, true))),
    BurgerPattern(BitPat("b001"), Some(BurgerInfo("Bacon Deluxe", true, true, true, true, true, true))),
    BurgerPattern(BitPat("b010"), Some(BurgerInfo("Double Stack", true, true, true, true, false, true))),
    BurgerPattern(BitPat("b011"), Some(BurgerInfo("Veggie Delight", true, false, false, false, true, true))),
    BurgerPattern(BitPat("b100"), Some(BurgerInfo("Bacon Bliss", true, true, true, true, false, true))),
    BurgerPattern(BitPat("b101"), Some(BurgerInfo("Bunless Fury", false, false, true, true, true, false))),
    BurgerPattern(BitPat("b110"), Some(BurgerInfo("Ultimate Supreme", true, true, true, true, true, true))),
    BurgerPattern(BitPat("b111"), None)
    // scalafmt: { align.tokens.add = [] }
  )
  private val burgerFields = Seq(
    BurgerValidField,
    HasBunsField,
    HasCheeseField,
    HasBaconField,
    HasPattyField,
    HasPicklesField,
    HasKetchupField
  )
  private val table  = new DecodeTable(burgers, burgerFields)
  private val result = table.decode(io.burger)

  io.enBuns    := result(HasBunsField)
  io.enCheese  := result(HasCheeseField)
  io.enBacon   := result(HasBaconField)
  io.enPatty   := result(HasPattyField)
  io.enPickles := result(HasPicklesField)
  io.enKetchup := result(HasKetchupField)
  io.valid     := result(BurgerValidField)
}
```

It elaborates to the following SystemVerilog:

```verilog
// Generated by CIRCT firtool-1.77.0
module BurgerDecoder(
  input  [2:0] io_burger,
  output       io_valid,
               io_enBuns,
               io_enCheese,
               io_enBacon,
               io_enPatty,
               io_enPickles,
               io_enKetchup
);

  wire [2:0] result_invInputs = ~io_burger;
  wire [1:0] _result_andMatrixOutputs_T = {result_invInputs[1], result_invInputs[2]};
  wire [1:0] _result_andMatrixOutputs_T_1 = {io_burger[0], result_invInputs[1]};
  wire [1:0] _result_andMatrixOutputs_T_2 = {io_burger[0], result_invInputs[2]};
  wire [1:0] _result_andMatrixOutputs_T_3 = {result_invInputs[0], io_burger[1]};
  wire [1:0] _result_andMatrixOutputs_T_4 = {result_invInputs[0], io_burger[2]};
  assign io_valid =
    |{&_result_andMatrixOutputs_T,
      &_result_andMatrixOutputs_T_1,
      &_result_andMatrixOutputs_T_2,
      &_result_andMatrixOutputs_T_3,
      &_result_andMatrixOutputs_T_4};
  assign io_enBuns =
    |{&_result_andMatrixOutputs_T,
      &_result_andMatrixOutputs_T_2,
      &_result_andMatrixOutputs_T_3,
      &_result_andMatrixOutputs_T_4};
  assign io_enCheese =
    |{&_result_andMatrixOutputs_T,
      &_result_andMatrixOutputs_T_3,
      &_result_andMatrixOutputs_T_4};
  assign io_enBacon =
    |{&_result_andMatrixOutputs_T_1,
      &_result_andMatrixOutputs_T_3,
      &_result_andMatrixOutputs_T_4};
  assign io_enPatty =
    |{&_result_andMatrixOutputs_T,
      &_result_andMatrixOutputs_T_1,
      &_result_andMatrixOutputs_T_3,
      &_result_andMatrixOutputs_T_4};
  assign io_enPickles =
    |{&_result_andMatrixOutputs_T,
      &_result_andMatrixOutputs_T_1,
      &_result_andMatrixOutputs_T_2,
      &{io_burger[1], io_burger[2]}};
  assign io_enKetchup =
    |{&_result_andMatrixOutputs_T,
      &_result_andMatrixOutputs_T_2,
      &_result_andMatrixOutputs_T_3,
      &_result_andMatrixOutputs_T_4};
endmodule
```

### Extensibility

Why does this method have advantages compared to the former ones? Imagine when we need to add a new field, `bulky`, to inform the machine that this burger is very big and should use a larger wrapper. We define a burger to be bulky if it has more than four ingredients excluding ketchup. If we implement the decoder in SystemVerilog or `TruthTable`, it takes a lot to manually compute the new field. But with `DecodeTable`, it is as simple as writing a new `BoolDecodeField`:

```scala
object IsBulkyField extends BoolDecodeField[BurgerPattern] {
  override def name = "isBulky"
  override def genTable(burger: BurgerPattern): BitPat = {
    burger.info match {
      case None => dc
      case Some(value) => {
        val count = Seq(
          value.hasBuns,
          value.hasCheese,
          value.hasBacon,
          value.hasPatty,
          value.hasPickles
        ).count(_ == true)
        if (count >= 4) y else n
      }
    }
  }
}
```

## 4. Conclusion

In this post, we have explored many ways to implement a complex decoder in Chisel with `DecodeTable` and friends. By understanding Chisel's generator nature and utilizing Scala's rich features, we can express the same logic much more efficiently, clearly, and extensibly.

[^1]: The abbreviation "en" could mean "enable" or "engage". Feel free to choose the one you like.
[^2]: The same is true for most of Chisel's public APIs.
