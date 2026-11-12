# C torture survey

Generated from the pinned `gcc.c-torture/execute` manifest.

- verdicts: 107/300 MATCH (passed 107, failed 0, oracle 0)
- manifest SHA-256: `fe8c9613906eaea8683b628deb19fd5e8c2079812f4fa5e2e6ead29c752bf273`
- measured commit: `d1bf8b677`
- measured at: `2026-11-12T02:33:24Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `not-ingested` | 1 |
| `not-parsed` | 30 |
| `passed` | 107 |
| `refused-libc` | 23 |
| `refused-ub` | 7 |
| `refused-unsupported` | 129 |
| `timeout` | 3 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `gcc.c-torture/execute` | `not-ingested` | 1 |
| `gcc.c-torture/execute` | `not-parsed` | 30 |
| `gcc.c-torture/execute` | `passed` | 107 |
| `gcc.c-torture/execute` | `refused-libc` | 23 |
| `gcc.c-torture/execute` | `refused-ub` | 7 |
| `gcc.c-torture/execute` | `refused-unsupported` | 129 |
| `gcc.c-torture/execute` | `timeout` | 3 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 76 | 151 | 20000113-1.c, 20000121-1.c, 20000223-1.c, 20000403-1.c, 20000412-1.c |
| `libc-call` | 4 | 36 | 20000519-1.c, 20000703-1.c, 20000910-2.c, 20001011-1.c, 20001203-2.c |
| `cast:IntegralToPointer` | 2 | 4 | 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `unsupported:CXXBoolLiteralExpr` | 1 | 1 | 20010604-1.c |
| `string-literal` | 0 | 33 | 20000121-1.c, 20000223-1.c, 20000703-1.c, 20000722-1.c, 20000801-4.c |
| `cast:IntegralToFloating` | 0 | 11 | 20000605-1.c, 20000731-1.c, 20010118-1.c, 20020225-2.c, 20020227-1.c |
| `cast:FloatingCast` | 0 | 6 | 20000605-1.c, 20020411-1.c, 20020413-1.c, 20030125-1.c, 20040709-1.c |
| `cast:FloatingToIntegral` | 0 | 6 | 20000605-1.c, 20010118-1.c, 20031003-1.c, 20040709-1.c, 20040709-2.c |
| `unsupported:PackedAttr` | 0 | 5 | 20010518-2.c, 20020227-1.c, 20030224-2.c, 20040625-1.c, 20040709-2.c |
| `unsupported:StmtExpr` | 0 | 5 | 20000703-1.c, 20000917-1.c, 20001203-2.c, 20020206-1.c, 20020320-1.c |
| `cast:PointerToIntegral` | 0 | 3 | 20000622-1.c, 20011121-1.c, 20030811-1.c |
| `unsequenced-effects` | 0 | 2 | 20001228-1.c, 20020406-1.c |
| `unsupported:AlignedAttr` | 0 | 2 | 20010904-1.c, 20010904-2.c |
| `unsupported:AddrLabelExpr` | 0 | 1 | 20040302-1.c |
| `unsupported:ExprWithCleanups` | 0 | 1 | 20020320-1.c |
| `unsupported:IndirectGotoStmt` | 0 | 1 | 20040302-1.c |
| `unsupported:PredefinedExpr` | 0 | 1 | 20001011-1.c |
| `unsupported:VAArgExpr` | 0 | 1 | 20000519-1.c |
