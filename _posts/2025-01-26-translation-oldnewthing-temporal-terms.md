---
layout: post
title: "翻译：《留意文档中的时间用语：参照时刻为何？》"
date: 2025-01-26T13:50:47+08:00
lang: zh
tags: topic:misc translation old-new-thing
---

> 原标题：Be mindful of temporal terms in documents: What is the reference point in time?
> 
> 作者：Raymond Chen
> 
> 地址：<https://devblogs.microsoft.com/oldnewthing/20250122-00/?p=110797>

------

在诸如功能提案或pull request的文档中，需要特别注意指代时刻的词语，因为语境中隐含的参照时刻并不总是清晰的。

例如，在pull request中也许会有如下的对话：

> 甲：“如果文件不存在会发生什么？”
> 
> 乙：“目前来说，如果文件不存在它会崩溃。”

此处“目前”所指代的时刻具有歧义。

* “目前仓库中”：按照（更改前的）现状，它会在文件不存在时崩溃。
* “目前在此pull request中”：如果使用pull request里的变更构建，那么它会在文件不存在时崩溃。（在这些更改前它不会崩溃。）

功能提案文档中也存在相似的歧义。

> 将有一种方法来逆转中子流的极性。

该处将来时的参考时刻是什么？

* 此功能提案包括了一种逆转中子流极性的方法：“现在”指的是系统当前不具有该功能的状态。
* 后续另一个功能提案将包含一种逆转中子流极性的方法：“现在”指的是系统具有初始功能后（但是尚未实现后续功能）的状态。

“目前”一词在功能提案中也有另一个可能的含义。

* “目前的实现中”：如果你在[测试分支（fun fork）](https://devblogs.microsoft.com/oldnewthing/20240625-00/?p=109931)中体验这个功能，它会崩溃。（我们计划修复这个问题，但是目前测试分支中的行为就是这样。）

我只是希望能够更为清晰地使用时间副词；不同的读者可能对参考时间点有着不同的假设。

<!-- seo-excerpt-separator -->

**花絮**：在长期有效的文档中使用“最近”一类的词是另一种时间词语的误用。也许它们在文章写就时具有恰当的含义，但是几个月甚至几年后，“最近”便再也不近了。

比如，在一个内部百科上有这样一条备注：

> 最近对X做了一项变动，导致管理Y的方法发生了变化。如果你有Y，那么你需要在已有的Y上进行Z更新。

我有一个Y，很担心必须进行Z。但之后我查看了百科的更新历史，发现那句备注是几个月之前加上的[^1]。所以其实它并不那么“最近”。实际上，我几天前才创建了我的Y，所以我并不需要进行Z更新。我的Y创建时就已经是最新的了。

[^1]: MediaWiki百科里有类似`wiki blame`的命令来查看某个句子的最近更新者吗？
