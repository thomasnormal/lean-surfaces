# C torture survey

Generated from the pinned `C1-C3 (gcc torture, c-testsuite, gcc c23-run)` manifest.

- verdicts: 604/2214 MATCH (passed 604, failed 0, oracle 0)
- manifest SHA-256: `1de1a60c299d5bb51dae7ca001b0a008010cad0b25670cde2090c08bfc1a84ce`
- measured commit: `fe2552444`
- measured at: `2026-11-12T04:55:00Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `not-ingested` | 25 |
| `not-parsed` | 350 |
| `passed` | 604 |
| `refused-libc` | 99 |
| `refused-ub` | 31 |
| `refused-unsupported` | 1061 |
| `timeout` | 44 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `c-testsuite/single-exec` | `not-ingested` | 5 |
| `c-testsuite/single-exec` | `not-parsed` | 1 |
| `c-testsuite/single-exec` | `passed` | 103 |
| `c-testsuite/single-exec` | `refused-libc` | 2 |
| `c-testsuite/single-exec` | `refused-ub` | 2 |
| `c-testsuite/single-exec` | `refused-unsupported` | 105 |
| `c-testsuite/single-exec` | `timeout` | 2 |
| `gcc.c-torture/execute` | `not-ingested` | 19 |
| `gcc.c-torture/execute` | `not-parsed` | 321 |
| `gcc.c-torture/execute` | `passed` | 500 |
| `gcc.c-torture/execute` | `refused-libc` | 95 |
| `gcc.c-torture/execute` | `refused-ub` | 28 |
| `gcc.c-torture/execute` | `refused-unsupported` | 913 |
| `gcc.c-torture/execute` | `timeout` | 42 |
| `gcc.c23-run` | `not-ingested` | 1 |
| `gcc.c23-run` | `not-parsed` | 28 |
| `gcc.c23-run` | `passed` | 1 |
| `gcc.c23-run` | `refused-libc` | 2 |
| `gcc.c23-run` | `refused-ub` | 1 |
| `gcc.c23-run` | `refused-unsupported` | 43 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 353 | 1061 | 00015.c, 00016.c, 00017.c, 00018.c, 00019.c |
| `libc-call` | 213 | 738 | 00025.c, 00040.c, 00056.c, 00087.c, 00089.c |
| `cast:IntegralToPointer` | 3 | 26 | 00214.c, 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `unsequenced-effects` | 3 | 20 | 00121.c, 20001228-1.c, 20020406-1.c, 20060102-1.c, 20230802-1.c |
| `cast:PointerToIntegral` | 2 | 27 | 00144.c, 20000622-1.c, 20011121-1.c, 20030811-1.c, 20050215-1.c |
| `unsupported:StmtExpr` | 1 | 10 | 00213.c, 00214.c, 20000703-1.c, 20000917-1.c, 20001203-2.c |
| `unsupported:AddrLabelExpr` | 1 | 8 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
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
| `unsupported:LabelDecl` | 0 | 1 | 980526-1.c |
| `unsupported:NullStmt` | 0 | 1 | gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:TypeTraitExpr` | 0 | 1 | builtin-types-compatible-p.c |

## Dynamic first-refusal ranking

The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `frontend` | 350 | 350 | 00209.c, 20000112-1.c, 20000227-1.c, 20000314-3.c, 20000412-3.c |
| `unsupported:not an lvalue` | 129 | 129 | 00025.c, 00026.c, 00056.c, 00058.c, 00112.c |
| `libc-call` | 99 | 99 | 00040.c, 00214.c, 20000402-1.c, 20000412-6.c, 20000722-1.c |
| `unsupported:no definition for 'main'` | 94 | 94 | 20040705-1.c, 20040705-2.c, 20040709-3.c, builtins/20010124-1.c, builtins/abs-1.c |
| `unsupported:not an integer type` | 54 | 54 | 00072.c, 00073.c, 20000419-1.c, 20000706-1.c, 20000706-2.c |
| `timeout` | 44 | 44 | 00041.c, 00128.c, 20020108-1.c, 20030916-1.c, 20040313-1.c |
| `unsupported:fewer arguments than parameters` | 43 | 43 | 00200.c, 20000412-2.c, 20000412-4.c, 20001124-1.c, 20010915-1.c |
| `unsupported:extern object 'inside_main' has no definition in the translation unit` | 38 | 38 | builtins/20010124-1-lib.c, builtins/complex-1-lib.c, builtins/fputs-lib.c, builtins/lib/abs.c, builtins/lib/bfill.c |
| `unsupported:floating literal (floats are a named decision)` | 34 | 34 | 20020720-1.c, 20080502-1.c, 20080529-1.c, 920501-8.c, 980205.c |
| `unsupported:string literal (inch 4` | 32 | 32 | 00115.c, 00204.c, 00208.c, 00217.c, 20000801-4.c |
| `undefined-behavior` | 31 | 31 | 00141.c, 00144.c, 20020129-1.c, 20020508-2.c, 20020508-3.c |
| `unsupported:block-scope storage class 'static' is outside the tier` | 27 | 27 | 00182.c, 20000910-1.c, 20010129-1.c, 20020615-1.c, 20021024-1.c |
| `unsupported:no layout for declared type 'double'` | 26 | 26 | 00178.c, 20000731-1.c, 20011217-1.c, 20040831-1.c, 20190901-1.c |
| `ingestion` | 25 | 25 | 00046.c, 00050.c, 00078.c, 00198.c, 00216.c |
| `unsequenced-effects` | 25 | 25 | 00121.c, 20001228-1.c, 20051021-1.c, 20060102-1.c, 20060929-1.c |
| `unsupported:declaration outside a block` | 24 | 24 | 20230802-1.c, bitops-1.c, bswap-3.c, minmaxcmp-1.c, pr104814.c |
| `unsupported:pointer bit-cast across incompatible effective types` | 20 | 20 | 00103.c, 20001017-2.c, 20050316-1.c, 20050607-1.c, 20060412-1.c |
| `unsupported:sizeof` | 19 | 19 | 00205.c, 20040411-1.c, 20051113-1.c, 20120105-1.c, 941014-2.c |
| `unsupported:no layout for declared type 'struct S'` | 18 | 18 | 00087.c, 20081103-1.c, 20100708-1.c, 20171008-1.c, 20230630-1.c |
| `unsupported:more arguments than parameters` | 13 | 13 | 20000519-1.c, 20071213-1.c, 991216-2.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c, pr117432.c |
| `cast:IntegralToPointer` | 11 | 11 | 20000622-1.c, 20010329-1.c, 20021010-2.c, 20041112-1.c, 960116-1.c |
| `cast:PointerToIntegral` | 10 | 10 | 20011121-1.c, 941014-1.c, loop-2c.c, pr22098-1.c, pr22098-2.c |
| `unsupported:compound literal (inch 4` | 10 | 10 | 00149.c, 00150.c, 20010123-1.c, 20020215-1.c, 20050929-1.c |
| `unsupported:pointer used as an integer (no ptr↔int cast in tier)` | 10 | 10 | 00032.c, 20000801-1.c, 20020503-1.c, 20060910-1.c, 20120808-1.c |
| `unsupported:case label nested in a control statement` | 9 | 9 | 00051.c, 00143.c, 20011109-1.c, 20080719-1.c, 920506-1.c |
| `unsupported:no layout for declared type 'V'` | 9 | 9 | pr105613.c, pr110817-1.c, pr110817-2.c, pr110817-3.c, pr71626-1.c |
| `unsupported:no layout for declared type 'float'` | 9 | 9 | 00113.c, 00174.c, 20050121-1.c, ieee/920518-1.c, ieee/980619-1.c |
| `cast:FloatingCast` | 6 | 6 | 20020413-1.c, 920618-1.c, ieee/20010114-2.c, ieee/20030331-1.c, ieee/pr67218.c |
| `cast:ToVoid` | 6 | 6 | 00212.c, 00213.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c, gcc/testsuite/gcc.dg/c23-float-4.c |
| `unsupported:integer-to-floating conversion (floats` | 6 | 6 | 20020321-1.c, 920710-1.c, 930622-2.c, gofast.c, ieee/compare-fp-3.c |
| `unsupported:no layout for declared type 'struct s'` | 6 | 6 | 00043.c, 20040625-1.c, 961223-1.c, pr110165-1.c, pr110166-1.c |
| `unsupported:no layout for declared type 'va_list'` | 6 | 6 | stdarg-1.c, va-arg-14.c, vfprintf-1.c, vfprintf-chk-1.c, vprintf-1.c |
| `unsupported:StmtExpr` | 5 | 5 | 20000917-1.c, 20020206-1.c, 20020320-1.c, 930406-1.c, 950906-1.c |
| `unsupported:break, continue or goto escaped a function body` | 5 | 5 | 00010.c, 20030909-1.c, 20040704-1.c, pr119291.c, pr17078-1.c |
| `unsupported:operator '-' on two pointers` | 5 | 5 | 00037.c, 20021015-1.c, 950710-1.c, 980701-1.c, pr36038.c |
| `cast:FloatingToIntegral` | 4 | 4 | 20031003-1.c, cbrt.c, pr38048-2.c, pr66233.c |
| `unsupported:extern object 'b' has no definition in the translation unit` | 4 | 4 | alias-2.c, alias-3.c, alias-4.c, gcc/testsuite/gcc.dg/c23-bool-2.c |
| `unsupported:indirect call through a non-FunctionDecl reference` | 4 | 4 | 00089.c, 20010122-1.c, pr34768-1.c, pr34768-2.c |
| `unsupported:no layout for declared type '_Complex double'` | 4 | 4 | 20030910-1.c, 960512-1.c, complex-1.c, complex-2.c |
| `unsupported:unbound declaration 'id25' (name 's')` | 4 | 4 | pr40404.c, pr48973-1.c, pr48973-2.c, pr49123.c |
| `unsupported:ExprWithCleanups` | 3 | 3 | 20041124-1.c, 950628-1.c, pr30185.c |
| `unsupported:function-to-pointer decay (inch 5)` | 3 | 3 | 20041212-1.c, 20101011-1.c, pr42231.c |
| `unsupported:no layout for declared type 'A'` | 3 | 3 | 20010118-1.c, restrict-1.c, strct-pack-2.c |
| `unsupported:no layout for declared type 'S'` | 3 | 3 | 00153.c, pr56799.c, pr85582-2.c |
| `unsupported:no layout for declared type 'T'` | 3 | 3 | 920908-1.c, pr84169.c, pr98474.c |
| `unsupported:no layout for declared type 'enum bar'` | 3 | 3 | gcc/testsuite/gcc.dg/c23-tag-alias-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-2.c, gcc/testsuite/gcc.dg/c23-tag-alias-3.c |
| `unsupported:no layout for declared type 'int[n % 1000 + 1]'` | 3 | 3 | 20040811-1.c, pr43220.c, vla-dealloc-1.c |
| `unsupported:no layout for declared type 'size_t'` | 3 | 3 | strcmp-1.c, strlen-1.c, strncmp-1.c |
| `unsupported:no layout for declared type 'struct foo'` | 3 | 3 | 00140.c, bf-pack-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-7.c |
| `unsupported:unbound declaration 'id15' (name 'x')` | 3 | 3 | 00119.c, 00123.c, 20090623-1.c |
| `unsupported:unbound declaration 'id180' (name 'stdout')` | 3 | 3 | 00189.c, fprintf-1.c, fprintf-chk-1.c |
| `unsupported:unbound declaration 'id27' (name 'x')` | 3 | 3 | 20030209-1.c, 960405-1.c, 991030-1.c |
| `unsupported:unbound declaration 'id320' (name 'u')` | 3 | 3 | memset-1.c, memset-2.c, memset-3.c |
| `unsupported:AddrLabelExpr` | 2 | 2 | 920501-5.c, 990208-1.c |
| `unsupported:extern object 'abs_called' has no definition in the translation unit` | 2 | 2 | builtins/abs-1-lib.c, builtins/uabs-1-lib.c |
| `unsupported:extern object 'x' has no definition in the translation unit` | 2 | 2 | 00094.c, 00110.c |
| `unsupported:goto skips a block declaration` | 2 | 2 | 00129.c, gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:no layout for declared type 'U'` | 2 | 2 | 20180131-1.c, pr85582-3.c |
| `unsupported:no layout for declared type '_Complex float'` | 2 | 2 | complex-6.c, pr38969.c |
| `unsupported:no layout for declared type 'double[4]'` | 2 | 2 | ieee/acc1.c, ieee/acc2.c |
| `unsupported:no layout for declared type 'enum E'` | 2 | 2 | 00054.c, 00055.c |
| `unsupported:no layout for declared type 'long double'` | 2 | 2 | 20040208-1.c, ieee/pr29302-1.c |
| `unsupported:no layout for declared type 'st'` | 2 | 2 | pr31448-2.c, pr31448.c |
| `unsupported:no layout for declared type 'struct A'` | 2 | 2 | 20040709-1.c, 20040709-2.c |
| `unsupported:no layout for declared type 'struct S1'` | 2 | 2 | pr60017.c, stdarg-3.c |
| `unsupported:no layout for declared type 'struct U'` | 2 | 2 | pr22141-1.c, pr22141-2.c |
| `unsupported:no layout for declared type 'struct mouse_button_str'` | 2 | 2 | bitfld-8.c, bitfld-9.c |
| `unsupported:no layout for declared type 'struct packed_ushort'` | 2 | 2 | 20170401-1.c, pr45070.c |
| `unsupported:no layout for declared type 'struct1'` | 2 | 2 | pr86659-1.c, pr86659-2.c |
| `unsupported:no layout for declared type 'union U'` | 2 | 2 | pr86492.c, pr88739.c |
| `unsupported:no layout for declared type 'v16di'` | 2 | 2 | pr123625-2.c, pr126405-3.c |
| `unsupported:type trait '__alignof'` | 2 | 2 | align-3.c, zerolen-2.c |
| `unsupported:unbound declaration 'id15' (name 'a')` | 2 | 2 | gcc/testsuite/gcc.dg/c23-imaginary-constants-1.c, gcc/testsuite/gcc.dg/c23-imaginary-constants-7.c |
| `unsupported:unbound declaration 'id15' (name 'dnan')` | 2 | 2 | ieee/fp-cmp-6.c, ieee/fp-cmp-9.c |
| `unsupported:unbound declaration 'id19' (name 'b')` | 2 | 2 | bitfld-signed1-1.c, pr84748.c |
| `unsupported:unbound declaration 'id19' (name 's')` | 2 | 2 | 00047.c, pr37882.c |
| `unsupported:unbound declaration 'id19' (name 'x')` | 2 | 2 | pr32244-1.c, pr34971.c |
| `unsupported:unbound declaration 'id20' (name 'u')` | 2 | 2 | bitfld-6.c, bitfld-7.c |
| `unsupported:unbound declaration 'id21' (name 'a')` | 2 | 2 | 00091.c, pr56837.c |
| `unsupported:unbound declaration 'id21' (name 'pinf')` | 2 | 2 | ieee/compare-fp-1.c, ieee/compare-fp-4.c |
| `unsupported:unbound declaration 'id22' (name 's')` | 2 | 2 | pr67781.c, pr78436.c |
| `unsupported:unbound declaration 'id320' (name 'u1')` | 2 | 2 | memcpy-2.c, strcpy-1.c |
| `unsupported:unbound declaration 'id37' (name 'x')` | 2 | 2 | 931110-1.c, compndlit-1.c |
| `unsupported:unbound declaration 'id38' (name 'v')` | 2 | 2 | builtins/pr22237-1.c, builtins/pr22237.c |
| `unsupported:unbound declaration 'id39' (name 'X')` | 2 | 2 | 960215-1.c, regstack-1.c |
| `unsupported:union initializer has no member` | 2 | 2 | pr15296.c, pr19687.c |
| `cast:FloatingComplexCast` | 1 | 1 | 20070614-1.c |
| `cast:FloatingRealToComplex` | 1 | 1 | complex-4.c |
| `cast:IntegralRealToComplex` | 1 | 1 | pr104604.c |
| `unsupported:AlignedAttr` | 1 | 1 | pr108064.c |
| `unsupported:GCCAsmStmt` | 1 | 1 | pr81588.c |
| `unsupported:GenericSelectionExpr` | 1 | 1 | gcc/testsuite/gcc.dg/c23-bool-1.c |
| `unsupported:block-scope storage class 'extern' is outside the tier` | 1 | 1 | scope-1.c |
| `unsupported:call through an incompatible function-pointer cast` | 1 | 1 | call-trap-1.c |
| `unsupported:cannot initialize aggregate 'int'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-empty-init-1.c |
| `unsupported:extern object 'ReadyFlag_NotProperlyInitialized' has no definition in the translation unit` | 1 | 1 | pr31072.c |
| `unsupported:extern object 'aa' has no definition in the translation unit` | 1 | 1 | 20000403-1.c |
| `unsupported:extern object 'i' has no definition in the translation unit` | 1 | 1 | pure-1.c |
| `unsupported:extern object 'p' has no definition in the translation unit` | 1 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `unsupported:function instrumentation is outside the tier` | 1 | 1 | eeprof-1.c |
| `unsupported:no layout for declared type 'A0'` | 1 | 1 | va-arg-22.c |
| `unsupported:no layout for declared type 'Data[4]'` | 1 | 1 | 20010116-1.c |
| `unsupported:no layout for declared type 'PgHdr[5]'` | 1 | 1 | pr33870-1.c |
| `unsupported:no layout for declared type 'Point'` | 1 | 1 | 950607-2.c |
| `unsupported:no layout for declared type 'Q'` | 1 | 1 | simd-5.c |
| `unsupported:no layout for declared type 'RenderInfo'` | 1 | 1 | 20000605-1.c |
| `unsupported:no layout for declared type 'T0 *const'` | 1 | 1 | 991016-1.c |
| `unsupported:no layout for declared type 'TRIAL'` | 1 | 1 | strct-pack-1.c |
| `unsupported:no layout for declared type 'Test1'` | 1 | 1 | 990525-2.c |
| `unsupported:no layout for declared type 'V2SF'` | 1 | 1 | 20050316-2.c |
| `unsupported:no layout for declared type 'V32'` | 1 | 1 | pr70903.c |
| `unsupported:no layout for declared type 'V[32]'` | 1 | 1 | ieee/pr72824-2.c |
| `unsupported:no layout for declared type 'X'` | 1 | 1 | struct-ret-1.c |
| `unsupported:no layout for declared type '_Complex double[12]'` | 1 | 1 | pr49644.c |
| `unsupported:no layout for declared type '_Complex double[1]'` | 1 | 1 | 20020411-1.c |
| `unsupported:no layout for declared type '__m128i'` | 1 | 1 | pr92618.c |
| `unsupported:no layout for declared type 'aun'` | 1 | 1 | pr19515.c |
| `unsupported:no layout for declared type 'big_t'` | 1 | 1 | pr23135.c |
| `unsupported:no layout for declared type 'bu'` | 1 | 1 | 921204-1.c |
| `unsupported:no layout for declared type 'char[argc]'` | 1 | 1 | 00207.c |
| `unsupported:no layout for declared type 'const int *const'` | 1 | 1 | 00219.c |
| `unsupported:no layout for declared type 'const struct s'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-constexpr-2a.c |
| `unsupported:no layout for declared type 'creal_T[16]'` | 1 | 1 | pr93434.c |
| `unsupported:no layout for declared type 'double[1]'` | 1 | 1 | 20001017-1.c |
| `unsupported:no layout for declared type 'double[32]'` | 1 | 1 | pr59643.c |
| `unsupported:no layout for declared type 'double[6]'` | 1 | 1 | 930614-1.c |
| `unsupported:no layout for declared type 'double[n]'` | 1 | 1 | 920929-1.c |
| `unsupported:no layout for declared type 'enum e'` | 1 | 1 | enum-3.c |
| `unsupported:no layout for declared type 'enum fred'` | 1 | 1 | 00170.c |
| `unsupported:no layout for declared type 'float[32]'` | 1 | 1 | ieee/pr72824.c |
| `unsupported:no layout for declared type 'float[3]'` | 1 | 1 | 20021118-2.c |
| `unsupported:no layout for declared type 'float[4]'` | 1 | 1 | loop-ivopts-1.c |
| `unsupported:no layout for declared type 'float[8]'` | 1 | 1 | ieee/copysign2.c |
| `unsupported:no layout for declared type 'float[8][2][8][2]'` | 1 | 1 | 930614-2.c |
| `unsupported:no layout for declared type 'four_quarters'` | 1 | 1 | 921123-2.c |
| `unsupported:no layout for declared type 'gfc_array_i4'` | 1 | 1 | 20090113-1.c |
| `unsupported:no layout for declared type 'info_t'` | 1 | 1 | 20100430-1.c |
| `unsupported:no layout for declared type 'int (*(*)(int, int))(int, int)'` | 1 | 1 | 00124.c |
| `unsupported:no layout for declared type 'int (*)(int, int)'` | 1 | 1 | 991112-1.c |
| `unsupported:no layout for declared type 'int (*)[++i]'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-auto-2.c |
| `unsupported:no layout for declared type 'int32_t'` | 1 | 1 | 00104.c |
| `unsupported:no layout for declared type 'io'` | 1 | 1 | 20031201-1.c |
| `unsupported:no layout for declared type 'material_type'` | 1 | 1 | 991019-1.c |
| `unsupported:no layout for declared type 'mp_int'` | 1 | 1 | 20180226-1.c |
| `unsupported:no layout for declared type 'neon_s8'` | 1 | 1 | pr42833.c |
| `unsupported:no layout for declared type 'object'` | 1 | 1 | 980223.c |
| `unsupported:no layout for declared type 'spinlock_t'` | 1 | 1 | zero-struct-2.c |
| `unsupported:no layout for declared type 'struct B'` | 1 | 1 | pr15262-2.c |
| `unsupported:no layout for declared type 'struct D'` | 1 | 1 | 20050613-1.c |
| `unsupported:no layout for declared type 'struct E'` | 1 | 1 | pr39339.c |
| `unsupported:no layout for declared type 'struct S0'` | 1 | 1 | pr78170.c |
| `unsupported:no layout for declared type 'struct S[21]'` | 1 | 1 | pr70602.c |
| `unsupported:no layout for declared type 'struct a'` | 1 | 1 | 20031211-1.c |
| `unsupported:no layout for declared type 'struct bar'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-alias-4.c |
| `unsupported:no layout for declared type 'struct c'` | 1 | 1 | packed-aligned.c |
| `unsupported:no layout for declared type 'struct complex'` | 1 | 1 | complex-3.c |
| `unsupported:no layout for declared type 'struct f'` | 1 | 1 | bitfld-10.c |
| `unsupported:no layout for declared type 'struct g'` | 1 | 1 | zero-struct-1.c |
| `unsupported:no layout for declared type 'struct mystruct'` | 1 | 1 | pr70566.c |
| `unsupported:no layout for declared type 'struct reg_stat'` | 1 | 1 | pr30778.c |
| `unsupported:no layout for declared type 'struct test2'` | 1 | 1 | pr29156.c |
| `unsupported:no layout for declared type 'struct tmp'` | 1 | 1 | bf64-1.c |
| `unsupported:no layout for declared type 'struct tree_type'` | 1 | 1 | pr31169.c |
| `unsupported:no layout for declared type 'struct x'` | 1 | 1 | 20000113-1.c |
| `unsupported:no layout for declared type 'struct_list'` | 1 | 1 | 921113-1.c |
| `unsupported:no layout for declared type 't'` | 1 | 1 | 920810-1.c |
| `unsupported:no layout for declared type 't1'` | 1 | 1 | divconst-1.c |
| `unsupported:no layout for declared type 't_be'` | 1 | 1 | 960416-1.c |
| `unsupported:no layout for declared type 'three_byte_t'` | 1 | 1 | struct-ret-2.c |
| `unsupported:no layout for declared type 'three_char_t'` | 1 | 1 | strct-pack-4.c |
| `unsupported:no layout for declared type 'uint32_t'` | 1 | 1 | 20120111-1.c |
| `unsupported:no layout for declared type 'union U1'` | 1 | 1 | 20181120-1.c |
| `unsupported:no layout for declared type 'union Y'` | 1 | 1 | pr92904.c |
| `unsupported:no layout for declared type 'union _D_rep'` | 1 | 1 | pr42691.c |
| `unsupported:no layout for declared type 'union at6'` | 1 | 1 | pr23324.c |
| `unsupported:no layout for declared type 'union tree_node'` | 1 | 1 | 00218.c |
| `unsupported:no layout for declared type 'union u'` | 1 | 1 | 20000603-1.c |
| `unsupported:no layout for declared type 'unsigned __int128'` | 1 | 1 | pr54471.c |
| `unsupported:no layout for declared type 'v4qi'` | 1 | 1 | pr60960.c |
| `unsupported:no layout for declared type 'v8qi'` | 1 | 1 | simd-6.c |
| `unsupported:no layout for declared type 'void *volatile'` | 1 | 1 | pr84521.c |
| `unsupported:no layout for declared type 'volatile a_struct'` | 1 | 1 | 20010518-2.c |
| `unsupported:no layout for declared type 'volatile double'` | 1 | 1 | 980709-1.c |
| `unsupported:no layout for declared type 'volatile long double'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-12.c |
| `unsupported:no layout for declared type 'wchar_t[21]'` | 1 | 1 | 00220.c |
| `unsupported:no layout for field 'n'` | 1 | 1 | pr39100.c |
| `unsupported:no layout for field 'y'` | 1 | 1 | 00053.c |
| `unsupported:no layout for parameter type 'const unsigned int *const'` | 1 | 1 | pr63209.c |
| `unsupported:no layout for parameter type 'foo_t *const'` | 1 | 1 | pr33669.c |
| `unsupported:no layout for parameter type 'int **restrict'` | 1 | 1 | 20080506-2.c |
| `unsupported:no layout for parameter type 'int *restrict'` | 1 | 1 | pr38212.c |
| `unsupported:src/20000412-5.c` | 1 | 1 | 20000412-5.c |
| `unsupported:src/20001203-1.c` | 1 | 1 | 20001203-1.c |
| `unsupported:src/20020225-2.c` | 1 | 1 | 20020225-2.c |
| `unsupported:src/20020619-1.c` | 1 | 1 | 20020619-1.c |
| `unsupported:src/20040307-1.c` | 1 | 1 | 20040307-1.c |
| `unsupported:src/20040331-1.c` | 1 | 1 | 20040331-1.c |
| `unsupported:src/20050316-3.c` | 1 | 1 | 20050316-3.c |
| `unsupported:src/20111212-1.c` | 1 | 1 | 20111212-1.c |
| `unsupported:src/921016-1.c` | 1 | 1 | 921016-1.c |
| `unsupported:src/930628-1.c` | 1 | 1 | 930628-1.c |
| `unsupported:src/950607-1.c` | 1 | 1 | 950607-1.c |
| `unsupported:src/980506-2.c` | 1 | 1 | 980506-2.c |
| `unsupported:src/bf-sign-1.c` | 1 | 1 | bf-sign-1.c |
| `unsupported:src/ieee/930529-1.c` | 1 | 1 | ieee/930529-1.c |
| `unsupported:src/ieee/minuszero.c` | 1 | 1 | ieee/minuszero.c |
| `unsupported:src/ieee/pr30704.c` | 1 | 1 | ieee/pr30704.c |
| `unsupported:src/pr33631.c` | 1 | 1 | pr33631.c |
| `unsupported:src/pr38051.c` | 1 | 1 | pr38051.c |
| `unsupported:src/simd-4.c` | 1 | 1 | simd-4.c |
| `unsupported:tests/single-exec/00118.c` | 1 | 1 | 00118.c |
| `unsupported:unbound declaration 'id103' (name 'test')` | 1 | 1 | pr71083.c |
| `unsupported:unbound declaration 'id126' (name 'f')` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-5.c |
| `unsupported:unbound declaration 'id137' (name 'tmp')` | 1 | 1 | pr36034-2.c |
| `unsupported:unbound declaration 'id142' (name 'tmp')` | 1 | 1 | pr36034-1.c |
| `unsupported:unbound declaration 'id15' (name 'array0')` | 1 | 1 | postmod-1.c |
| `unsupported:unbound declaration 'id15' (name 'f1')` | 1 | 1 | complex-7.c |
| `unsupported:unbound declaration 'id15' (name 'fptr')` | 1 | 1 | 00088.c |
| `unsupported:unbound declaration 'id15' (name 'vd')` | 1 | 1 | 20120919-1.c |
| `unsupported:unbound declaration 'id151' (name 's')` | 1 | 1 | pr91597.c |
| `unsupported:unbound declaration 'id18' (name 'a')` | 1 | 1 | pr65427.c |
| `unsupported:unbound declaration 'id18' (name 'g')` | 1 | 1 | 20031214-1.c |
| `unsupported:unbound declaration 'id18' (name 's')` | 1 | 1 | 20051104-1.c |
| `unsupported:unbound declaration 'id18' (name 'x')` | 1 | 1 | pr33382.c |
| `unsupported:unbound declaration 'id185' (name 'w')` | 1 | 1 | pr47337.c |
| `unsupported:unbound declaration 'id19' (name 'f')` | 1 | 1 | signed1bitfield-1.c |
| `unsupported:unbound declaration 'id197' (name 't')` | 1 | 1 | 20011113-1.c |
| `unsupported:unbound declaration 'id20' (name 'b')` | 1 | 1 | pr59388.c |
| `unsupported:unbound declaration 'id21' (name 'b')` | 1 | 1 | pr82192.c |
| `unsupported:unbound declaration 'id21' (name 'g1s')` | 1 | 1 | pr42248.c |
| `unsupported:unbound declaration 'id21' (name 's')` | 1 | 1 | 20041201-1.c |
| `unsupported:unbound declaration 'id21' (name 'v')` | 1 | 1 | 00024.c |
| `unsupported:unbound declaration 'id22' (name 'b')` | 1 | 1 | pr58726.c |
| `unsupported:unbound declaration 'id22' (name 'c')` | 1 | 1 | pr103417.c |
| `unsupported:unbound declaration 'id22' (name 'f')` | 1 | 1 | pr100453.c |
| `unsupported:unbound declaration 'id22' (name 't')` | 1 | 1 | packed-2.c |
| `unsupported:unbound declaration 'id23' (name 'a')` | 1 | 1 | pr44164.c |
| `unsupported:unbound declaration 'id23' (name 'f')` | 1 | 1 | 20100316-1.c |
| `unsupported:unbound declaration 'id23' (name 'u')` | 1 | 1 | pr97073.c |
| `unsupported:unbound declaration 'id24' (name 'a1')` | 1 | 1 | 20010924-1.c |
| `unsupported:unbound declaration 'id24' (name 'gstate_initial')` | 1 | 1 | 20080117-1.c |
| `unsupported:unbound declaration 'id25' (name 'c')` | 1 | 1 | pr52209.c |
| `unsupported:unbound declaration 'id25' (name 'f')` | 1 | 1 | pr19689.c |
| `unsupported:unbound declaration 'id25' (name 't')` | 1 | 1 | vrp-7.c |
| `unsupported:unbound declaration 'id25' (name 'v')` | 1 | 1 | 20050215-1.c |
| `unsupported:unbound declaration 'id25' (name 'x')` | 1 | 1 | 20030109-1.c |
| `unsupported:unbound declaration 'id26' (name 'a')` | 1 | 1 | 20020213-1.c |
| `unsupported:unbound declaration 'id26' (name 'd')` | 1 | 1 | pr58570.c |
| `unsupported:unbound declaration 'id26' (name 'j')` | 1 | 1 | pr117095.c |
| `unsupported:unbound declaration 'id26' (name 'v')` | 1 | 1 | pr43784.c |
| `unsupported:unbound declaration 'id27' (name 'a')` | 1 | 1 | 20031215-1.c |
| `unsupported:unbound declaration 'id27' (name 'd')` | 1 | 1 | 20001121-1.c |
| `unsupported:unbound declaration 'id27' (name 'f')` | 1 | 1 | 921208-1.c |
| `unsupported:unbound declaration 'id27' (name 'gd')` | 1 | 1 | 20021120-1.c |
| `unsupported:unbound declaration 'id27' (name 'pzero')` | 1 | 1 | ieee/mzero2.c |
| `unsupported:unbound declaration 'id27' (name 's2848')` | 1 | 1 | pr38151.c |
| `unsupported:unbound declaration 'id2748' (name 'pinf')` | 1 | 1 | ieee/hugeval.c |
| `unsupported:unbound declaration 'id28' (name 'arr')` | 1 | 1 | pr55750.c |
| `unsupported:unbound declaration 'id28' (name 'g_6')` | 1 | 1 | 20101025-1.c |
| `unsupported:unbound declaration 'id28' (name 's')` | 1 | 1 | pr31136.c |
| `unsupported:unbound declaration 'id28' (name 'sv')` | 1 | 1 | 20071211-1.c |
| `unsupported:unbound declaration 'id28' (name 'terminate_me')` | 1 | 1 | pr54937.c |
| `unsupported:unbound declaration 'id28' (name 'test')` | 1 | 1 | 20030903-1.c |
| `unsupported:unbound declaration 'id28' (name 'x')` | 1 | 1 | bitfld-4.c |
| `unsupported:unbound declaration 'id29' (name 'a')` | 1 | 1 | pr44575.c |
| `unsupported:unbound declaration 'id29' (name 'f1')` | 1 | 1 | floatunsisf-1.c |
| `unsupported:unbound declaration 'id29' (name 'fp')` | 1 | 1 | func-ptr-1.c |
| `unsupported:unbound declaration 'id30' (name 'b')` | 1 | 1 | 20131127-1.c |
| `unsupported:unbound declaration 'id30' (name 'f')` | 1 | 1 | pr98366.c |
| `unsupported:unbound declaration 'id30' (name 'u')` | 1 | 1 | 20050604-1.c |
| `unsupported:unbound declaration 'id30' (name 'x')` | 1 | 1 | 20011019-1.c |
| `unsupported:unbound declaration 'id30' (name 'y')` | 1 | 1 | ieee/pr28634.c |
| `unsupported:unbound declaration 'id31' (name 't')` | 1 | 1 | 980602-2.c |
| `unsupported:unbound declaration 'id31' (name 'wordlist')` | 1 | 1 | 20000412-1.c |
| `unsupported:unbound declaration 'id32' (name 'node')` | 1 | 1 | 20030224-2.c |
| `unsupported:unbound declaration 'id32' (name 's')` | 1 | 1 | pr38422.c |
| `unsupported:unbound declaration 'id33' (name 'entry')` | 1 | 1 | zerolen-1.c |
| `unsupported:unbound declaration 'id33' (name 'n1')` | 1 | 1 | ieee/builtin-nan-1.c |
| `unsupported:unbound declaration 'id33' (name 't')` | 1 | 1 | packed-1.c |
| `unsupported:unbound declaration 'id34' (name 'a')` | 1 | 1 | pr52979-1.c |
| `unsupported:unbound declaration 'id34' (name 'zerod')` | 1 | 1 | ieee/mzero3.c |
| `unsupported:unbound declaration 'id36' (name 'actual_function')` | 1 | 1 | 00210.c |
| `unsupported:unbound declaration 'id37' (name 'a')` | 1 | 1 | bitfld-3.c |
| `unsupported:unbound declaration 'id37' (name 'b')` | 1 | 1 | 20040629-1.c |
| `unsupported:unbound declaration 'id37' (name 'pts')` | 1 | 1 | 920625-1.c |
| `unsupported:unbound declaration 'id38' (name 'a')` | 1 | 1 | pr52979-2.c |
| `unsupported:unbound declaration 'id38' (name 's')` | 1 | 1 | 20000801-3.c |
| `unsupported:unbound declaration 'id40' (name 'x')` | 1 | 1 | extzvsi.c |
| `unsupported:unbound declaration 'id42' (name 'x')` | 1 | 1 | ieee/20041213-1.c |
| `unsupported:unbound declaration 'id42' (name 'y')` | 1 | 1 | 20010904-1.c |
| `unsupported:unbound declaration 'id420' (name 'buffer')` | 1 | 1 | 20060420-1.c |
| `unsupported:unbound declaration 'id426' (name 'array')` | 1 | 1 | pr34456.c |
| `unsupported:unbound declaration 'id43' (name 'h')` | 1 | 1 | pr58277-2.c |
| `unsupported:unbound declaration 'id43' (name 'y')` | 1 | 1 | 20010904-2.c |
| `unsupported:unbound declaration 'id45' (name 'k')` | 1 | 1 | simd-1.c |
| `unsupported:unbound declaration 'id45' (name 's')` | 1 | 1 | 20081117-1.c |
| `unsupported:unbound declaration 'id48' (name 'curval')` | 1 | 1 | 960117-1.c |
| `unsupported:unbound declaration 'id49' (name 'result')` | 1 | 1 | struct-ini-3.c |
| `unsupported:unbound declaration 'id49' (name 's_c_f')` | 1 | 1 | align-2.c |
| `unsupported:unbound declaration 'id50' (name 'ws')` | 1 | 1 | widechar-2.c |
| `unsupported:unbound declaration 'id515' (name 'point_array')` | 1 | 1 | 00195.c |
| `unsupported:unbound declaration 'id52' (name 'x')` | 1 | 1 | bf-sign-2.c |
| `unsupported:unbound declaration 'id64' (name 'buf')` | 1 | 1 | 20210505-1.c |
| `unsupported:unbound declaration 'id66' (name 'k')` | 1 | 1 | simd-2.c |
| `unsupported:unbound declaration 'id67' (name 'z')` | 1 | 1 | complex-5.c |
| `unsupported:unbound declaration 'id725' (name 'input')` | 1 | 1 | pr28982a.c |
| `unsupported:unbound declaration 'id74' (name 'p')` | 1 | 1 | pr64242.c |
| `unsupported:unbound declaration 'id751' (name 'input')` | 1 | 1 | pr28982b.c |
| `unsupported:unbound declaration 'id95' (name 'tmp')` | 1 | 1 | 991118-1.c |
| `unsupported:unknown enum declaration 'id17' (name 'X')` | 1 | 1 | 00120.c |
| `unsupported:unknown enum declaration 'id29' (name 'BAR')` | 1 | 1 | enum-2.c |
| `unsupported:unknown enum declaration 'id41' (name 'N')` | 1 | 1 | 20011219-1.c |
| `unsupported:unnamed pointer parameter (array-bound effects are not retained by clang)` | 1 | 1 | gcc/testsuite/gcc.dg/c23-parm-omit-3.c |
