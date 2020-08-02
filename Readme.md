# Buchholz ψ analyzer

This program analyzes Buchholz ψ function defined in Buchholz (1986). When the user gives an ordinal term a ∈ T, as defined in the reference, the program determines if a ∈ OT. If a ∉ OT, b ∈ OT (o(a) = o(b)) is suggested. For example:

```
Input: D1(D0(0),D1(D4(0)),D3(D0(0)))
a = D1(D0(0),D1(D4(0)),D3(D0(0)))
where a ∈ T, a ∉ OT. Showing b ∈ OT where o(a) = o(b):
b = D1(D3(D0(0)),D2(0))
o(a) = o(b) = ψ1(ψ3(ψ0(0))+ψ2(0))
 = ψ1(ψ3(1)+ψ2(0))
```

## Use from web or terminal

When environmental variable SCRIPT_NAME is set, it runs as a CGI program. It is running at

https://gyafun.jp/ln/psi.cgi

From command line, ordinal string can be given by comman-line argument. As it is mainly intended for debugging, test script is always run.

## Use from program

See following sample code.

```
#!/usr/bin/env python
# -*- coding: utf-8 -*-
from psi import ordinal
a = '0(1(2(0)),w,2)'  # ordinal string
print(ordinal(a).T)  # a ∈ T as array
print(ordinal(a).strT)  # String of a ∈ T
print(ordinal(a).isPT)  # If a is principal term
print(ordinal(a).isOT)  # If a ∉ OT
print(ordinal(a).strOT)  # b ∈ OT where o(a) = o(b)
print(ordinal(a).ord)  # ordinal expression
print(ordinal(a).simple)  # Simplified ordinal expression
# Error handling
print(ordinal('(1)(2)').invalidString)  # Error in string
print(ordinal('(1)(2)').errMessage)  # Error message
```

## Input string

Examples

- D0(D1(Dw(0)),0(0))
- D0(D0(D2(0)),D0(0))
- D2(D0(D4(0)),D3(0),D6(D3(D6(0))))
- D0(D3(0),D1(D2(0)),D0(0))
- 0(1(2),w(3))
- 0(1(2(0)),0(0))
- 0(w,1(2(0
- w#3
- 1#w
- ψ0(ψω(0)#1)

Rules

- Input a ∈ T as shown in the reference
- D, ψ, ' ' are neglected
- &num; is regarded as ,
- natural numbers are analyzed
- w and ω are regarded as ω
- ) is added at the end if needed

## Reference

Buchholz, W. (1986): A New System of Proof-Theoretic Ordinal Function. Annals of Pure and Applied Logic, 32:195-207. https://doi.org/10.1016/0168-0072(86)90052-7
