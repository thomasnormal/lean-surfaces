# C torture survey

Generated from the pinned `gcc.c-torture/execute` manifest.

- verdicts: 157/300 MATCH (passed 157, failed 0, oracle 0)
- manifest SHA-256: `9fa5a961dfa2a56523b90a37c121d533aa9763dfd0251b56f24d8a596d0069b1`
- measured commit: `e4001e8aa137d650c915dc032ea10e5483359f33`
- measured at: `2026-11-12T13:15:59Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `not-parsed` | 30 |
| `oracle-tests-compiler` | 1 |
| `passed` | 157 |
| `refused-libc` | 3 |
| `refused-ub` | 9 |
| `refused-unsupported` | 96 |
| `timeout` | 4 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `gcc.c-torture/execute` | `not-parsed` | 30 |
| `gcc.c-torture/execute` | `oracle-tests-compiler` | 1 |
| `gcc.c-torture/execute` | `passed` | 157 |
| `gcc.c-torture/execute` | `refused-libc` | 3 |
| `gcc.c-torture/execute` | `refused-ub` | 9 |
| `gcc.c-torture/execute` | `refused-unsupported` | 96 |
| `gcc.c-torture/execute` | `timeout` | 4 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 76 | 151 | 20000113-1.c, 20000121-1.c, 20000223-1.c, 20000403-1.c, 20000412-1.c |
| `libc-call` | 4 | 36 | 20000519-1.c, 20000703-1.c, 20000910-2.c, 20001011-1.c, 20001203-2.c |
| `cast:IntegralToPointer` | 2 | 4 | 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
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

## Dynamic first-refusal ranking

The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `frontend` | 30 | 30 | 20000112-1.c, 20000227-1.c, 20000314-3.c, 20000412-3.c, 20000717-3.c |
| `undefined-behavior` | 9 | 9 | 20001203-2.c, 20010409-1.c, 20020129-1.c, 20020508-2.c, 20020508-3.c |
| `unsupported:string literal (inch 4` | 7 | 7 | 20000801-4.c, 20001229-1.c, 20010915-1.c, 20011128-1.c, 20021219-1.c |
| `unsupported:pointer used as an integer (no ptr↔int cast in tier)` | 6 | 6 | 20000412-6.c, 20000801-1.c, 20000910-1.c, 20011126-2.c, 20020503-1.c |
| `unsupported:string literal with escape or non-ASCII spelling` | 5 | 5 | 20000121-1.c, 20001130-2.c, 20010325-1.c, 20030626-1.c, 20030920-1.c |
| `timeout` | 4 | 4 | 20000412-2.c, 20020108-1.c, 20030916-1.c, 20040313-1.c |
| `unsupported:StmtExpr` | 4 | 4 | 20000703-1.c, 20000917-1.c, 20020206-1.c, 20020320-1.c |
| `cast:IntegralToPointer` | 3 | 3 | 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `unsupported:no definition for 'main'` | 3 | 3 | 20040705-1.c, 20040705-2.c, 20040709-3.c |
| `unsupported:no layout for declared type 'double'` | 3 | 3 | 20000731-1.c, 20011217-1.c, 20040831-1.c |
| `unsupported:break, continue or goto escaped a function body` | 2 | 2 | 20030909-1.c, 20040704-1.c |
| `unsupported:floating literal (floats are a named decision)` | 2 | 2 | 20020720-1.c, 20030914-1.c |
| `unsupported:no layout for declared type 'struct A'` | 2 | 2 | 20040709-1.c, 20040709-2.c |
| `unsupported:no layout for declared type 'struct x'` | 2 | 2 | 20000113-1.c, 20020227-1.c |
| `unsupported:operator '-' on two pointers` | 2 | 2 | 20021015-1.c, 20021204-1.c |
| `cast:FloatingCast` | 1 | 1 | 20020413-1.c |
| `cast:FloatingToIntegral` | 1 | 1 | 20031003-1.c |
| `cast:PointerToIntegral` | 1 | 1 | 20011121-1.c |
| `libc-call: __builtin_expect` | 1 | 1 | 20020418-1.c |
| `libc-call: malloc` | 1 | 1 | 20020406-1.c |
| `libc-call: strchr` | 1 | 1 | 20000910-2.c |
| `unsequenced-effects` | 1 | 1 | 20001228-1.c |
| `unsupported:AddrLabelExpr` | 1 | 1 | 20040302-1.c |
| `unsupported:case label nested in a control statement` | 1 | 1 | 20011109-1.c |
| `unsupported:extern object 'aa' has no definition in the translation unit` | 1 | 1 | 20000403-1.c |
| `unsupported:indirect call through a non-FunctionDecl reference` | 1 | 1 | 20010122-1.c |
| `unsupported:integer-to-floating conversion (floats` | 1 | 1 | 20020321-1.c |
| `unsupported:more arguments than parameters` | 1 | 1 | 20000519-1.c |
| `unsupported:no layout for compound literal type 'A'` | 1 | 1 | 20020206-2.c |
| `unsupported:no layout for declared type 'A'` | 1 | 1 | 20010118-1.c |
| `unsupported:no layout for declared type 'DB_TXNLIST'` | 1 | 1 | 20011008-3.c |
| `unsupported:no layout for declared type 'Data[4]'` | 1 | 1 | 20010116-1.c |
| `unsupported:no layout for declared type 'RenderInfo'` | 1 | 1 | 20000605-1.c |
| `unsupported:no layout for declared type '_Complex double'` | 1 | 1 | 20030910-1.c |
| `unsupported:no layout for declared type '_Complex double[1]'` | 1 | 1 | 20020411-1.c |
| `unsupported:no layout for declared type 'double[1]'` | 1 | 1 | 20001017-1.c |
| `unsupported:no layout for declared type 'float[3]'` | 1 | 1 | 20021118-2.c |
| `unsupported:no layout for declared type 'int[n % 1000 + 1]'` | 1 | 1 | 20040811-1.c |
| `unsupported:no layout for declared type 'io'` | 1 | 1 | 20031201-1.c |
| `unsupported:no layout for declared type 'long double'` | 1 | 1 | 20040208-1.c |
| `unsupported:no layout for declared type 'struct a'` | 1 | 1 | 20031211-1.c |
| `unsupported:no layout for declared type 'struct s'` | 1 | 1 | 20040625-1.c |
| `unsupported:no layout for declared type 'union u'` | 1 | 1 | 20000603-1.c |
| `unsupported:no layout for declared type 'volatile a_struct'` | 1 | 1 | 20010518-2.c |
| `unsupported:no layout for declared type 'volatile enum X'` | 1 | 1 | 20030903-1.c |
| `unsupported:no layout for parameter type 'const struct b *restrict'` | 1 | 1 | 20001024-1.c |
| `unsupported:not an integer type: 'int *'` | 1 | 1 | 20000819-1.c |
| `unsupported:not an lvalue: PredefinedExpr` | 1 | 1 | 20001011-1.c |
| `unsupported:pointer bit-cast across incompatible effective types` | 1 | 1 | 20001017-2.c |
| `unsupported:sizeof: no layout for operand type 'c'` | 1 | 1 | 20040411-1.c |
| `unsupported:src/20000412-5.c` | 1 | 1 | 20000412-5.c |
| `unsupported:src/20020225-2.c` | 1 | 1 | 20020225-2.c |
| `unsupported:src/20040307-1.c` | 1 | 1 | 20040307-1.c |
| `unsupported:src/20040331-1.c` | 1 | 1 | 20040331-1.c |
| `unsupported:type trait '__alignof'` | 1 | 1 | 20000223-1.c |
| `unsupported:unbound declaration 'id18' (name 'g')` | 1 | 1 | 20031214-1.c |
| `unsupported:unbound declaration 'id197' (name 't')` | 1 | 1 | 20011113-1.c |
| `unsupported:unbound declaration 'id24' (name 'a1')` | 1 | 1 | 20010924-1.c |
| `unsupported:unbound declaration 'id25' (name 'x')` | 1 | 1 | 20030109-1.c |
| `unsupported:unbound declaration 'id26' (name 'a')` | 1 | 1 | 20020213-1.c |
| `unsupported:unbound declaration 'id27' (name 'a')` | 1 | 1 | 20031215-1.c |
| `unsupported:unbound declaration 'id27' (name 'd')` | 1 | 1 | 20001121-1.c |
| `unsupported:unbound declaration 'id27' (name 'gd')` | 1 | 1 | 20021120-1.c |
| `unsupported:unbound declaration 'id27' (name 'x')` | 1 | 1 | 20030209-1.c |
| `unsupported:unbound declaration 'id30' (name 'x')` | 1 | 1 | 20011019-1.c |
| `unsupported:unbound declaration 'id31' (name 'wordlist')` | 1 | 1 | 20000412-1.c |
| `unsupported:unbound declaration 'id32' (name 'node')` | 1 | 1 | 20030224-2.c |
| `unsupported:unbound declaration 'id37' (name 'b')` | 1 | 1 | 20040629-1.c |
| `unsupported:unbound declaration 'id38' (name 's')` | 1 | 1 | 20000801-3.c |
| `unsupported:unbound declaration 'id42' (name 'y')` | 1 | 1 | 20010904-1.c |
| `unsupported:unbound declaration 'id43' (name 'y')` | 1 | 1 | 20010904-2.c |
| `unsupported:unbound declaration 'id487' (name 'MyPte')` | 1 | 1 | 20020402-2.c |
| `unsupported:unknown enum declaration 'id41' (name 'N')` | 1 | 1 | 20011219-1.c |
