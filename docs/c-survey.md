# C torture survey

Generated from the pinned `C1-C3 (gcc torture, c-testsuite, gcc c23-run)` manifest.

- verdicts: 595/2214 MATCH (passed 595, failed 0, oracle 0)
- manifest SHA-256: `1de1a60c299d5bb51dae7ca001b0a008010cad0b25670cde2090c08bfc1a84ce`
- measured commit: `d7159d66a`
- measured at: `2026-11-12T03:38:00Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `not-ingested` | 25 |
| `not-parsed` | 350 |
| `passed` | 595 |
| `refused-libc` | 99 |
| `refused-ub` | 31 |
| `refused-unsupported` | 1070 |
| `timeout` | 44 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `c-testsuite/single-exec` | `not-ingested` | 5 |
| `c-testsuite/single-exec` | `not-parsed` | 1 |
| `c-testsuite/single-exec` | `passed` | 97 |
| `c-testsuite/single-exec` | `refused-libc` | 2 |
| `c-testsuite/single-exec` | `refused-ub` | 2 |
| `c-testsuite/single-exec` | `refused-unsupported` | 111 |
| `c-testsuite/single-exec` | `timeout` | 2 |
| `gcc.c-torture/execute` | `not-ingested` | 19 |
| `gcc.c-torture/execute` | `not-parsed` | 321 |
| `gcc.c-torture/execute` | `passed` | 498 |
| `gcc.c-torture/execute` | `refused-libc` | 95 |
| `gcc.c-torture/execute` | `refused-ub` | 28 |
| `gcc.c-torture/execute` | `refused-unsupported` | 915 |
| `gcc.c-torture/execute` | `timeout` | 42 |
| `gcc.c23-run` | `not-ingested` | 1 |
| `gcc.c23-run` | `not-parsed` | 28 |
| `gcc.c23-run` | `refused-libc` | 2 |
| `gcc.c23-run` | `refused-ub` | 1 |
| `gcc.c23-run` | `refused-unsupported` | 44 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 353 | 1061 | 00015.c, 00016.c, 00017.c, 00018.c, 00019.c |
| `libc-call` | 212 | 737 | 00025.c, 00040.c, 00056.c, 00087.c, 00089.c |
| `cast:IntegralToPointer` | 3 | 26 | 00214.c, 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `unsequenced-effects` | 3 | 20 | 00121.c, 20001228-1.c, 20020406-1.c, 20060102-1.c, 20230802-1.c |
| `cast:PointerToIntegral` | 2 | 27 | 00144.c, 20000622-1.c, 20011121-1.c, 20030811-1.c, 20050215-1.c |
| `unsupported:StmtExpr` | 1 | 10 | 00213.c, 00214.c, 20000703-1.c, 20000917-1.c, 20001203-2.c |
| `unsupported:AddrLabelExpr` | 1 | 8 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `unsupported:EmptyDecl` | 1 | 6 | 20050106-1.c, 20230630-2.c, 20230630-4.c, builtin-bitops-1.c, pr34154.c |
| `unsupported:ChooseExpr` | 1 | 1 | pr19449.c |
| `string-literal` | 0 | 262 | 00025.c, 00026.c, 00056.c, 00058.c, 00112.c |
| `cast:IntegralToFloating` | 0 | 81 | 00113.c, 00119.c, 00123.c, 00174.c, 00175.c |
| `unsupported:VAArgExpr` | 0 | 57 | 00204.c, 20000519-1.c, 20041113-1.c, 20041214-1.c, 20071213-1.c |
| `cast:FloatingCast` | 0 | 53 | 00174.c, 00175.c, 00204.c, 20000605-1.c, 20020411-1.c |
| `cast:FloatingToIntegral` | 0 | 26 | 00175.c, 20000605-1.c, 20010118-1.c, 20031003-1.c, 20040709-1.c |
| `unsupported:PackedAttr` | 0 | 26 | 00210.c, 20010518-2.c, 20020227-1.c, 20030224-2.c, 20040625-1.c |
| `unsupported:AlignedAttr` | 0 | 15 | 20010904-1.c, 20010904-2.c, 20171008-1.c, 960117-1.c, 990326-1.c |
| `unsupported:ImaginaryLiteral` | 0 | 13 | 20041124-1.c, 20041201-1.c, 20070614-1.c, builtins/complex-1.c, complex-1.c |
| `unsupported:IndirectGotoStmt` | 0 | 7 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `unsupported:DesignatedInitUpdateExpr` | 0 | 6 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-1.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-17.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-2.c, gcc/testsuite/gcc.dg/c23-empty-init-warn-4.c |
| `unsupported:ExprWithCleanups` | 0 | 6 | 00204.c, 20020320-1.c, 20041124-1.c, 950628-1.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c |
| `unsupported:GenericSelectionExpr` | 0 | 6 | 00219.c, gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c |
| `unsupported:IndirectFieldDecl` | 0 | 6 | 00046.c, 00050.c, 00216.c, anon-1.c, gcc/testsuite/gcc.dg/c23-tag-5.c |
| `unsupported:GCCAsmStmt` | 0 | 4 | 20071211-1.c, 990413-2.c, pr56982.c, pr81588.c |
| `unsupported:OffsetOfExpr` | 0 | 4 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, pr103255.c, pr30778.c, pr44468.c |
| `unsupported:MaxFieldAlignmentAttr` | 0 | 3 | 20131127-1.c, pr58570.c, pr79737-1.c |
| `unsupported:MayAliasAttr` | 0 | 3 | mayalias-2.c, mayalias-3.c, pr43987.c |
| `unsupported:ModeAttr` | 0 | 3 | 20050107-1.c, 20050119-1.c, 20050119-2.c |
| `unsupported:PredefinedExpr` | 0 | 2 | 20001011-1.c, pr58831.c |
| `unsupported:StaticAssertDecl` | 0 | 2 | gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-digit-separators-1.c |
| `unsupported:BinaryConditionalOperator` | 0 | 1 | pr68249.c |
| `unsupported:CXXNullPtrLiteralExpr` | 0 | 1 | gcc/testsuite/gcc.dg/c23-nullptr-5.c |
| `unsupported:CaseStmt` | 0 | 1 | pr34154.c |
| `unsupported:LabelDecl` | 0 | 1 | 980526-1.c |
| `unsupported:NullStmt` | 0 | 1 | gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:TypeTraitExpr` | 0 | 1 | builtin-types-compatible-p.c |
