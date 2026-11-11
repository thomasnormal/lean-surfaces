# C torture survey

Generated from the pinned `gcc.c-torture/execute` August 300-test manifest.

- verdicts: 30/300 scored (passed 30, failed 0)
- manifest SHA-256: `33aa92be14205ed07df2a2df9c4a937c64c4df9d20aa63eefb34f96ae5951157`
- measured commit: `3ccd4f100`
- measured at: `2026-11-11T23:20:17Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `not-ingested` | 1 |
| `not-parsed` | 30 |
| `passed` | 30 |
| `refused-libc` | 80 |
| `refused-ub` | 6 |
| `refused-unsupported` | 151 |
| `timeout` | 2 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 57 | 150 | 20000113-1.c, 20000121-1.c, 20000223-1.c, 20000403-1.c, 20000412-1.c |
| `unsupported:SwitchStmt` | 6 | 9 | 20001130-2.c, 20010106-1.c, 20011109-1.c, 20011219-1.c, 20011223-1.c |
| `operator:~` | 5 | 8 | 20000205-1.c, 20000715-2.c, 20020127-1.c, 20021120-3.c, 20040409-3.c |
| `unsupported:NullStmt` | 4 | 5 | 20000412-4.c, 20020108-1.c, 20020716-1.c, 20030909-1.c, 20040811-1.c |
| `libc-call` | 3 | 35 | 20000519-1.c, 20000703-1.c, 20000910-2.c, 20001011-1.c, 20001203-2.c |
| `cast:IntegralToPointer` | 2 | 4 | 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `assignment-call` | 1 | 29 | 20000801-2.c, 20000818-1.c, 20000917-1.c, 20001124-1.c, 20001130-1.c |
| `unsupported:CXXBoolLiteralExpr` | 1 | 1 | 20010604-1.c |
| `string-literal` | 0 | 32 | 20000121-1.c, 20000223-1.c, 20000703-1.c, 20000722-1.c, 20000801-4.c |
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
