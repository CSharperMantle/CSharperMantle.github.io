---
layout: post
title: "When spaces break your CreateProcess (and how to fix it)"
date: 2025-06-17T20:38:55+08:00
lang: en
tags: topic:dev windows
---

The username on my Windows laptop contains a space ("` `"). This little character is known to [cause](https://github.com/pypa/pip/issues/10114) [dozens](https://superuser.com/questions/119610/spaces-and-parenthesis-in-windows-path-variable-screws-up-batch-files) [of](https://forum.posit.co/t/spaces-in-library-path-names-on-windows-causes-problems-installing-packages-after-installing-r-3-5-0/8978) [software](https://superuser.com/questions/1420212/im-getting-an-error-indicating-that-the-file-path-has-a-space-in-the-name-when) [problems](https://github.com/espressif/esp-idf/issues/5576), and most of them are attributed to the existing codebase which does not properly quote file paths.

Recently this space started troubling me more than before. Two pieces of software *suddenly* refused to work. I spent a while diagnosing the bugs, then filed bug reports and patches to the developers:

* **Nushell.** It's my daily shell environment. Nushell is functional, elegant, and expressive. However, it now refused to start up in my Windows Terminal, producing an [`ERROR_BAD_EXE_FORMAT`](https://learn.microsoft.com/en-us/windows/win32/debug/system-error-codes--0-499-#:~:text=ERROR_BAD_EXE_FORMAT).
  * PR [nushell/nushell#15881](https://github.com/nushell/nushell/pull/15881) (merged)
  * PR [nushell/nushell#15889](https://github.com/nushell/nushell/pull/15889) (merged)
  * PR [nushell/integrations#57](https://github.com/nushell/integrations/pull/57) (merged)
* **Galarius/vscode-opencl.** I have used this extension on my other Windows machines without problems, so I installed it in my VS Code. It failed to start, producing a "file not found" error.
  * Issue [Galarius/vscode-opencl#72](https://github.com/Galarius/vscode-opencl/issues/72) (closed as done)

Here's a TL;DR version for them: Both apps pass the target executable name *in a shell command* rather than *as an image path*. For Nushell < 0.105.0 on Windows, it put the bare path in the ["`commandline`" property of the Windows Terminal profile](https://learn.microsoft.com/en-us/windows/terminal/customize-settings/profile-general#command-line). For vscode-opencl, it runs [`child_process.exec`](https://nodejs.org/api/child_process.html#child_processexeccommand-options-callback) with bare path and CLI arguments. In both cases, the first fragment delimited by space is recognized as the "real" executable name, and that does not exist of course.

Wait, did I say "suddenly"? Both software worked fine *up to a recent time point*. That's not normal, since my username was set long ago. They should either work or break from the very beginning. So I dug deeper and took a look at the "Users" directory. I found a file with the same name as the first fragment of my username:

```nushell
> ls `C:\Users\` | find "Mantle" | select name type
╭───┬─────────────────────────────────────────────────┬──────╮
│ # │                      name                       │ type │
├───┼─────────────────────────────────────────────────┼──────┤
│ 0 │ C:\Users\Mantle                                 │ file │
│ 1 │ C:\Users\Mantle Bao                             │ dir  │
╰───┴─────────────────────────────────────────────────┴──────╯
>
```

File #0 is an empty file and not an executable, thus the `ERROR_BAD_EXE_FORMAT`. So I proposed the three PRs to Nushell upstream that fixes the profile creation. They worked as intended, but one question remains: Why did they work before?

Windows apps call `CreateProcess` series of functions to load and execute another image. Take [`CreateProcessW`](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-createprocessw#parameters) as an example. When an image name (`lpApplicationName`) is not specified, the command line (`lpCommandLine`) would be used to specify the executable to run. Here, Windows applies a curious strategy to *iteratively* determine which executable to run, literally:

> For example, consider the string "c:\program files\sub dir\program name". This string can be interpreted in a number of ways. The system tries to interpret the possibilities in the following order:
> 
> 1. **c:\program.exe**
> 2. **c:\program files\sub.exe**
> 3. **c:\program files\sub dir\program.exe**
> 4. **c:\program files\sub dir\program name.exe**

I think this is a compatibility and developer experience consideration. Very often developers forget to quote their executable names, and spaces are common in standard Windows paths (like "Program Files", and "Application Data", and even mixed with parentheses like "Program Files (x86)"). Having this strategy can handle most misquoted situations and end up finding the right executable. But under some conditions, it could go wrong in a disastrous way.

Suppose an application named "My App" creates a data directory at `%APPDATA%\My App\`, and drops a helper executable into `%APPDATA%\My App\helper.exe`. Suppose the developers of this app forget to quote the path and pass it to `CreateProcess`. An attacker or hacker can create a backdoor executable named `My` at `%APPDATA%\`. When the app tries to run the helper executable, the backdoor would be called instead.

How to prevent these from happening? There are three common approaches:

1. Tell the user that they cannot use any paths with spaces inside. When the app launches, it checks all used paths and complains about the spaces found in them. It's effective, but some users may find it annoying.
2. Quote every path when building `lpCommandLine`. This is safer and more user-friendly than the last approach.
3. Pass the executable name in `lpApplicationName`, and use `lpCommandLine` solely for command line arguments. Some quotes may still be needed to help the callee parse the correct `argv[0]`. This is the safest, as it's now impossible to have the executable path truncated.

But as the developers review their codebase and take whatever approaches above, maybe it's time for me to switch my username.
