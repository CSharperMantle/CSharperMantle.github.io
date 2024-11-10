---
layout: post
title: "Code Snippet: Generalized Transpose in C++"
date: 2022-07-31 12:47:32 +0800
lang: en
categories: snippets
---

Generalized transpose, or 'permutation' sometimes, reorders the dimensions of a tensor.

```cpp
/*
 * MIT License
 * 
 * Copyright (c) 2022 Rong "Mantle" Bao
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <array>
#include <cstdlib>
#include <iostream>
#include <stdexcept>

template <typename T, unsigned D>
T *permute(T *tensor, const std::array<size_t, D> &dims,
           const std::array<size_t, D> &order)
{
    // Check for proper orders
    for (const auto &o : order)
    {
        if (o == 0 || o > D)
        {
            throw std::invalid_argument{"invalid order"};
        }
    }
    // Get count of elements
    size_t cnt_elems = 1;
    for (const auto &dim : dims)
    {
        cnt_elems *= dim;
    }
    // Create space for new elements
    T *new_tensor = new T[cnt_elems];
    // Calculate shape of new tensor
    std::array<size_t, D> new_dims{};
    for (size_t i = 0; i < D; i++)
    {
        new_dims[i] = dims[order[i] - 1];
    }
    // Calculate stride for new tensor
    std::array<size_t, D> new_strides{1};
    new_strides.fill(1);
    for (size_t i = 0; i < D; i++)
    {
        for (size_t j = i + 1; j < D; j++)
        {
            new_strides[i] *= new_dims[j];
        }
    }
    // Perform the permutation
    std::array<size_t, D> new_cursor{};
    new_cursor.fill(0);
    new_tensor[0] = tensor[0]; // We should always copy the first one
    for (size_t i = 1; i < cnt_elems; i++)
    {
        // Increase new_cursor by one element
        for (size_t d = D - 1; d >= 0; d--)
        {
            // actual_d is the actual dimension after permutation.
            size_t actual_d = order[d] - 1;
            if (new_cursor[actual_d] == new_dims[actual_d] - 1)
            {
                new_cursor[actual_d] = 0;
            }
            else
            {
                new_cursor[actual_d]++;
                break;
            }
        }
        // Calculate placement of element in new tensor
        size_t j = 0;
        for (size_t k = 0; k < D; k++)
        {
            j += new_strides[k] * new_cursor[k];
        }
        // Copy
        new_tensor[j] = tensor[i];
    }
    // Done
    return new_tensor;
}

int main(int, char **)
{
    double arr[2][3] = {
        {0.1, 0.2, 0.3}, {0.4, 0.5, 0.6}
    };

    std::cout << "Before permutation:\n";
    for (size_t i = 0; i < 6; i++)
    {
        std::cout << ((double *)arr)[i] << ", ";
    }
    std::cout << '\n';

    double *result = permute<double, 2>((double *)arr, {2, 3}, {2, 1});

    std::cout << "After permutation:\n";
    for (size_t i = 0; i < 6; i++)
    {
        std::cout << ((double *)result)[i] << ", ";
    }
    std::cout << '\n';

    return 0;
}

```

The output of the above program is listed below.

```plain
Before permutation:
0.1, 0.2, 0.3, 0.4, 0.5, 0.6,
After permutation:
0.1, 0.4, 0.2, 0.5, 0.3, 0.6,
```
