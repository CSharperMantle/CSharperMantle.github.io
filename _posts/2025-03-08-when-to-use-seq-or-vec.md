---
layout: post
title: "When to use Seq or Vec in Chisel?"
date: 2025-03-08T12:00:26+08:00
lang: en
tags: topic:dev ee digital-logics chisel
---

**Use `Seq` if you just need a Scala array or container. Use `Vec` if you want a multiplexer.**

[`scala.collection.immutable.Seq`](https://www.scala-lang.org/api/2.13.x/scala/collection/immutable/Seq.html) is purely a Scala-land concept. You can index into it via a `Int` thanks to its [`apply`](https://www.scala-lang.org/api/2.13.x/scala/collection/immutable/Seq.html#apply(i:Int):A) function.

[`chisel3.Vec`](https://javadoc.io/doc/org.chipsalliance/chisel_2.13/latest/chisel3/Vec.html) is a hardware container that can be indexed by Scala-land `Int`s and hardware `UInt`s. It has two `apply` overloads: [`apply(idx: Int): T`](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/Vec.html#apply(idx:Int):T) and [`apply(p: UInt): T`](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/Vec.html#apply(p:chisel3.UInt):T). It also have connection operators like [`:=`](https://javadoc.io/static/org.chipsalliance/chisel_2.13/7.0.0-M2/chisel3/Vec.html#:=(that:chisel3.Vec[T])(implicitsourceInfo:chisel3.experimental.SourceInfo):Unit), allowing for element-wise connection.

Always refer to the (scarce) Chisel documentation when in doubt. If the API in question is not documented (which is very likely), read the source code for its exact behavior.
