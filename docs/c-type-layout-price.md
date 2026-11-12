# C type-layout wall price

This report compares the envelope-derived candidate wall with the runner's first refusal.

- survey commit: `04e05fa491c9104d03fdbdf1edc98eb20bd220f4`
- survey measured at: `2026-11-12T12:48:42Z`
- static candidates: 1061 present, 353 sole
- observed declaration `no layout`: 261 (candidate overlap 233)
- observed declaration refusals without a static candidate: 28
- static candidates without an observed declaration refusal: 828

| corpus | static present | static sole | observed declaration no-layout | overlap |
| --- | ---: | ---: | ---: | ---: |
| `c-testsuite/single-exec` | 123 | 41 | 17 | 13 |
| `gcc.c-torture/execute` | 909 | 308 | 235 | 212 |
| `gcc.c23-run` | 29 | 4 | 9 | 8 |

## Most frequent observed declaration refusals

| detail | files |
| --- | ---: |
| `no layout for declared type 'double'` | 27 |
| `no layout for declared type 'struct S'` | 22 |
| `no layout for declared type 'float'` | 9 |
| `no layout for declared type 'V'` | 9 |
| `no layout for declared type 'struct s'` | 7 |
| `no layout for declared type 'va_list'` | 7 |
| `no layout for declared type '_Complex double'` | 5 |
| `no layout for declared type 'union U'` | 4 |
| `no layout for declared type 'const double'` | 4 |
| `no layout for declared type 'struct foo'` | 3 |
| `no layout for declared type 'struct x'` | 3 |
| `no layout for declared type 'A'` | 3 |
| `no layout for declared type 'int[n % 1000 + 1]'` | 3 |
| `no layout for declared type 'struct S[2]'` | 3 |
| `no layout for declared type '_Complex float'` | 3 |
| `no layout for declared type 'enum bar'` | 3 |
| `no layout for declared type 'enum E'` | 2 |
| `no layout for declared type 'S'` | 2 |
| `no layout for declared type 'long double'` | 2 |
| `no layout for declared type 'struct A'` | 2 |

## `struct S` parser-envelope dependencies

| file | fields from Clang envelope |
| --- | --- |
| `00087.c` | fptr:int (*)(void) |
| `20050107-1.c` | <anonymous>:ModeAttr, <anonymous>:ModeAttr |
| `20081103-1.c` | c:char, arr:char[4], f:float |
| `20100708-1.c` | for_alignment:double, <anonymous>:?, a:struct (unnamed struct at src/20100708-1.c:7:3)[16] |
| `20171008-1.c` | <anonymous>:AlignedAttr, c1:char, c2:char, c3:char, c4:char |
| `20230630-1.c` | i:short, c1:char, c2:char, c3:char, c4:char |
| `20230630-2.c` | i:short, c1:char, c2:char, c3:char, c4:char |
| `20230630-3.c` | i:int, c1:char, c2:char, c3:char, c4:char, c5:char, c6:char, c7:char, c8:char |
| `20230630-4.c` | i:int, c1:char, c2:char, c3:char, c4:char, c5:char, c6:char, c7:char, c8:char |
| `pr101188.c` | buffer:uint8_t[64], n:uint16_t, f2:fn2, a:void *, f1:fn1 |
| `pr108498-2.c` | a:unsigned int, b:unsigned int, c:unsigned int, d:struct U, e:unsigned int, f:struct V, g:unsigned int, h:unsigned int |
| `pr47538.c` | a:double, b:double, c:double *, d:unsigned long |
| `pr49123.c` | f:int |
| `pr52979-1.c` | <anonymous>:PackedAttr, g:int, h:int |
| `pr52979-2.c` | <anonymous>:PackedAttr, g:int, h:int |
| `pr58984.c` | f0:int, <anonymous>:int, f1:int |
| `pr65215-3.c` | l1:unsigned long long, l2:unsigned long long, l3:unsigned long long |
| `pr65215-4.c` | l1:unsigned long long |
| `pr70127.c` | f:int, g:int |
| `pr79737-1.c` | <anonymous>:MaxFieldAlignmentAttr, b:int32_t, c:int32_t, d:int32_t, e:int32_t, f:int32_t |
| `pr89195.c` | i:unsigned int |
| `pr97764.c` | b:int, c:int, d:int |

field records come directly from the approved Clang envelope; an empty list means the envelope has no named S record, not that a layout was guessed.


type-layout is a candidate wall, not a dynamic verdict: the static heuristic over-approximates the files that reach a missing layout and misses some declaration types. Price a tier from observed no-layout refusals, retaining the static ranking for discovery.
