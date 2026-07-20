---
layout: post
title: User-Agent drama of coding agents
date: 2026-07-20T21:49:24+08:00
lang: en
description: >-
    History repeats itself once more.
tags: topic:misc ai
---

Recently, I've been using coding agents to perform code reviews on my works. As is commonly accepted, <abbr title="Large Language Models">LLMs</abbr> have undisputed pattern discovery abilities, especially when paired with good harnesses and forming an *agent*. Basically, the harness sets an initial prompt, then invokes the underlying <abbr title="Large Language Model">LLM</abbr> iteratively, satisfying the model's requests to achieve a user-defined goal. When performing coding tasks, these requests often include file reads, edits, command invocation, MCP calls, etc. The harness extracts the (hopefully) structured request from the model's output, execute them, then serialize the results into the prompt for the next turn. This multi-round text completion loop creates an illusion of agency towards completing said user-supplied goals.

Command invocation is one of the few generic ways for the agent to interact with the environment; as such, all recent <abbr title="Large Language Models">LLMs</abbr> are trained or fine-tuned to execute common commands. However, most CLI utilities are either designed for humans (usually with a time-based context window and significant adaptability) or machines (which can process structured data algorithmically), meaning that they are either too verbose or too alien from natural language to <abbr title="Large Language Models">LLMs</abbr>. As a result, models are often compelled to use post-processing techniques, like shell redirection, tail(1), jq(1), or even python(1) and perl(1). These are lossy transformations, and they rely heavily on model's priors to properly extract desired information, resulting in great variations in retrieval quality.

Some progress has been made towards this. For example, Mozilla's [mach](https://firefox-source-docs.mozilla.org/mach/index.html) build system has an interesting feature to detect if it's invoked by an agent (or precisely, an <abbr title="Large Language Model">LLM</abbr> harness). It does this by [checking for several environment variables](https://searchfox.org/firefox-main/rev/d951c4a19a6958816b35a228ff38fc6ae2c34f13/python/mozbuild/mozbuild/util.py#91):

```python
def is_running_under_coding_agent():
    return bool(
        os.environ.get("CLAUDECODE")
        or os.environ.get("CODEX_SANDBOX")
        or os.environ.get("GEMINI_CLI")
        or os.environ.get("OPENCODE")
    )
```

When agents are detected, it becomes less verbose while keeping the behaviors matching human expectations:

```plain-text
0:02.60 W AI agent detected. Terminal output limited to warnings and errors.
```

So far so good. However, I use [Pi.dev](https://pi.dev/docs/latest), which isn't included in the detection list. Also undetected are other popular choices like [crush](https://github.com/charmbracelet/crush), [Cline](https://github.com/cline/cline), Copilot CLI, as well as most open-source provider's agents.

To solve this, we can either:

1. Send a patch upstream to include whatever environment variable other agents will set in the function,
2. Or, make agents impersonate one of the four "known" agents.

The first one seems impractical, since most of these agents do *not* set specific environment variable to declare their presence, and the set of agents is ever-growing. For Pi.dev, fortunately, the second option can be implemented easily via a custom extension:

```typescript
// ~/.pi/agent/extensions/inject-opencode-env.ts

import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";

export default function (_pi: ExtensionAPI) {
  if (!process.env.OPENCODE) {
    process.env.OPENCODE = "1";
  }
}
```

This adds `OPENCODE=1` to the agent's environment, which is then carried along to the subprocesses it launches.

Sounds familiar? To me, it's a replica of [the `User-Agent:` drama](https://webaim.org/blog/user-agent-string-history/). To those not familiar with that, here's a short version: Early websites pattern-match on the `User-Agent:` header value to serve different browsers different content to match their feature level; when browser vendors reached consensus on their features (by competition), the websites weren't updated in time, so browsers started to impersonate each other by adding fragments from others's UA to get served the most feature-rich version. This turned the UA string from a simple `NCSA_Mosaic/2.0 (Windows 3.1)` (which is *indeed* a Mosaic) to today's monstrous `Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/151.0.0.0 Safari/537.36 Edg/151.0.0.0` (which is neither Mozilla Firefox nor Safari but Edge).

We're still at an early stage of this drama, and it's interesting to see where it goes. One example to learn from is probably the de-facto [`CI=true`](https://stackoverflow.com/a/60026913) standard of the continuous integration community. But I'm negative towards a proper resolution in the near future. The standard will arrive sometime after the neo-<abbr title="Artificial Intelligence">AI</abbr> hype bubble bursts, when we can finally take time to slow down and distill a few ideas worth weighing, and not a moment before.
