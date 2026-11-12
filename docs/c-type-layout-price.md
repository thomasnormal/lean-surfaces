# C type-layout wall price

This report compares the envelope-derived candidate wall with the runner's first refusal.

- survey commit: `ecac15649`
- survey measured at: `2026-11-12T01:52:00Z`
- static candidates: 1061 present, 353 sole
- observed declaration `no layout`: 214 (candidate overlap 186)
- observed declaration refusals without a static candidate: 28
- static candidates without an observed declaration refusal: 875

| corpus | static present | static sole | observed declaration no-layout | overlap |
| --- | ---: | ---: | ---: | ---: |
| `c-testsuite/single-exec` | 123 | 41 | 17 | 13 |
| `gcc.c-torture/execute` | 909 | 308 | 191 | 168 |
| `gcc.c23-run` | 29 | 4 | 6 | 5 |

## Most frequent observed declaration refusals

| detail | files |
| --- | ---: |
| `no layout for declared type 'double'` | 26 |
| `no layout for declared type 'struct S'` | 18 |
| `no layout for declared type 'float'` | 9 |
| `no layout for declared type 'V'` | 9 |
| `no layout for declared type 'struct s'` | 6 |
| `no layout for declared type 'va_list'` | 6 |
| `no layout for declared type '_Complex double'` | 4 |
| `no layout for declared type 'struct foo'` | 3 |
| `no layout for declared type 'S'` | 3 |
| `no layout for declared type 'A'` | 3 |
| `no layout for declared type 'int[n % 1000 + 1]'` | 3 |
| `no layout for declared type 'T'` | 3 |
| `no layout for declared type 'size_t'` | 3 |
| `no layout for declared type 'enum E'` | 2 |
| `no layout for declared type 'int[2][1]'` | 2 |
| `no layout for declared type 'long double'` | 2 |
| `no layout for declared type 'struct A'` | 2 |
| `no layout for declared type 'struct packed_ushort'` | 2 |
| `no layout for declared type 'U'` | 2 |
| `no layout for declared type 'struct mouse_button_str'` | 2 |

type-layout is a candidate wall, not a dynamic verdict: the static heuristic over-approximates the files that reach a missing layout and misses some declaration types. Price a tier from observed no-layout refusals, retaining the static ranking for discovery.
