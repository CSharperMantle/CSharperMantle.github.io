---
layout: post
title: "Python随笔（i1）：DataFrame多条件“与”选择 Parallel Criteria Selection in DataFrame"
date: 2022-01-22T13:15:23+08:00
lang: zh-Hans
tags: topic:dev programming-language python
---

可以使用`&`操作符连接由形为`dataframe_obj[col] Op arg`的语句所创建的布尔值`Series`。

```python
import pandas


data = {
    "Name": [ "pencil", "ruler", "compass" ],
    "Price": [ 1.5, 4.3, 8.1 ],
    "InStock": [ False, True, True ]
}

df = pandas.DataFrame(data)

print("Mantle has 5 yuan so he can afford the following stuff:")
print(df[df["Price"] < 5.0])
print("... but he can only buy things in stock so he can actually get:")
print(df[(df["Price"] <= 5.0) & (df["InStock"] == True)])

```

结果：

```plain
mantlebao@mantletmx:~# python3 pandas_comb_cond.py       
Mantle has 5 yuan so he can afford the following stuff:
     Name  Price  InStock
0  pencil    1.5    False
1   ruler    4.3     True
... but he can only buy things in stock so he can actually get:
    Name  Price  InStock
1  ruler    4.3     True
mantlebao@mantletmx:~#
```

同样也可以使用`dataframe_obj.where(crit, inplace=False)`方法，该函数会将所有不符合要求的行的所有字段设为`NaN`。
