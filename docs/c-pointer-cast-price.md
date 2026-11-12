# C pointer/integer wall price

- survey commit: `04e05fa491c9104d03fdbdf1edc98eb20bd220f4`
- rows priced: 30

| shape | files |
| --- | ---: |
| `implicit-pointer-read-or-use` | 15 |
| `pointer-arithmetic` | 11 |
| `pointer-bit-cast` | 4 |

Every classification is derived from Clang AST envelope nodes; no pointer address or type spelling is invented. A missing node is priced as a tool gap rather than admitted as a conversion.

| file | shape | AST evidence |
| --- | --- | --- |
| `00032.c` | `implicit-pointer-read-or-use` | pointer type only |
| `00173.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=3 |
| `00182.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=5 |
| `20000412-6.c` | `pointer-arithmetic` | FunctionToPointerDecay=3; arithmetic=[{'op': '+', 'type': 'unsigned short *'}] |
| `20000801-1.c` | `pointer-bit-cast` | FunctionToPointerDecay=5; BitCast=2; arithmetic=[{'op': '+', 'type': 'char *'}, {'op': '+', 'type': 'char *'}, {'op': '+', 'type': 'char *'}] |
| `20000910-1.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=5 |
| `20011126-2.c` | `pointer-arithmetic` | FunctionToPointerDecay=1; arithmetic=[{'op': '+', 'type': 'const char *'}] |
| `20020503-1.c` | `pointer-arithmetic` | FunctionToPointerDecay=2; arithmetic=[{'op': '+', 'type': 'char *'}] |
| `20030606-1.c` | `pointer-bit-cast` | BuiltinFnToFnPtr=2; BitCast=2; FunctionToPointerDecay=5 |
| `20030920-1.c` | `pointer-bit-cast` | BitCast=1; FunctionToPointerDecay=1 |
| `20050502-1.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=23 |
| `20060910-1.c` | `pointer-arithmetic` | FunctionToPointerDecay=4; arithmetic=[{'op': '+', 'type': 'unsigned char *'}] |
| `20070201-1.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=3 |
| `20100827-1.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=3 |
| `20111208-1.c` | `pointer-bit-cast` | FunctionToPointerDecay=8; BitCast=4; arithmetic=[{'op': '+', 'type': 'char *'}, {'op': '+', 'type': 'char *'}] |
| `20120808-1.c` | `pointer-arithmetic` | FunctionToPointerDecay=2; arithmetic=[{'op': '+', 'type': 'unsigned char *'}, {'op': '+', 'type': 'unsigned char *'}] |
| `20140828-1.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=1; BuiltinFnToFnPtr=2 |
| `930429-1.c` | `pointer-arithmetic` | FunctionToPointerDecay=3; arithmetic=[{'op': '+', 'type': 'char *'}] |
| `931110-2.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=2 |
| `950714-1.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=2 |
| `961125-1.c` | `pointer-arithmetic` | FunctionToPointerDecay=3; arithmetic=[{'op': '+', 'type': 'char *'}, {'op': '+', 'type': 'char *'}, {'op': '+', 'type': 'char *'}] |
| `990222-1.c` | `pointer-arithmetic` | FunctionToPointerDecay=1; arithmetic=[{'op': '+', 'type': 'char *'}] |
| `loop-12.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=2 |
| `pr116799.c` | `pointer-arithmetic` | BuiltinFnToFnPtr=2; FunctionToPointerDecay=2; arithmetic=[{'op': '+', 'type': 'const char *'}, {'op': '+', 'type': 'const char *'}, {'op': '-', 'type': 'const char *'}, {'op': '-', 'type': 'const char *'}] |
| `pr20601-1.c` | `pointer-arithmetic` | FunctionToPointerDecay=12; arithmetic=[{'op': '+', 'type': 'char **'}, {'op': '+', 'type': 'char **'}] |
| `pr27073.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=3 |
| `pr34176.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=3 |
| `pr34415.c` | `pointer-arithmetic` | FunctionToPointerDecay=1; arithmetic=[{'op': '+', 'type': 'const char *'}] |
| `pr54985.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=2 |
| `pr71631.c` | `implicit-pointer-read-or-use` | FunctionToPointerDecay=1; BuiltinFnToFnPtr=1 |
