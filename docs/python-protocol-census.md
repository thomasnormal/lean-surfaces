# Python protocol census

Foundation step 2 (2026-11-10). This is a source census, not a refinement
claim. The two interpreter columns name the implementation currently called by
each surface. `shared` means both surfaces call the same worker; `separate`
marks a control/transport wrapper that still needs an adequacy theorem.

| CPython 3.9 protocol | Trunk (`Semantics.lean`) | Runner (`Monadic/`) | Current observation / gap |
|---|---|---|---|
| `PyObject_RichCompare` / `PyObject_RichCompareBool` | `valEq`, `heapEq`, `keyEq`, `heapContainsScan`, `rvalLt` | `evalCompareOpH` and shared workers through `Monadic.Prim` | Shared value equality; container identity for non-finite floats now refuses at equality, membership, tuple/list ordering, `sorted`, `max`, `min`, and key probes. |
| `PyObject_IsTrue` | `truthyH` | `truthyM` → `truthyH` | shared |
| `PyObject_Hash` | `hashableKey`, `setHashNat`, dict/set key gates | same workers through `liftRes` / evaluator arms | finite numeric and tuple key slice; identity-hashed objects and unmodeled set construction refuse |
| `PyNumber_Index` | `asInt`, `asRangeBound` | shared through `asInt` in builtin/method arms | the raising `Py_ssize_t` conversion is now a separate pinned boundary for list/range-length sites; full messages remain owed |
| `PyLong_AsSsize_t` (after `PyNumber_Index` in list Clinic wrappers) | `pySsizeRaising` at `heapInsert`, `heapPop`, `lenVal` | same workers | shared raising conversion with CPython's exact `OverflowError`; sequence subscripting's `PyExc_IndexError` replacement is `pySsizeIndex` and `indexErrorSize` |
| `_PyEval_SliceIndex` | `pySsizeClamping`, `asSliceIdx`, `normIndex` | shared | slice bounds clip to the pinned `Py_ssize_t` range before ordinary sequence clamping |
| `PyFloat_AsDouble` / `PyLong_AsDouble` | `floatNumber` / `Float64.fromInt` | shared through `evalBinOp` | mixed true division and negative integer or mixed-float power convert left then right before special cases (`mixed_div_left_overflow`, `mixed_div_right_overflow`, `negative_pow_exponent_overflow`, `negative_pow_base_overflow`); integer true division retains its separate exact-ratio path (`integer_div_huge_ratio`); unit integer powers use converted exponent parity (`negative_pow_unit_boundary`), and floating zero, infinity and unit-base cases are decided (`float_power_special`); NaN payload, complex and platform `pow` cases stay loud |
| `PyObject_GetIter` / `iternext` | `rangeVals`, `heapContains`, `execFor*`, generator steppers | `iterValues`, `Kont` cursors, `exec*` shells | shared value workers; live generator/dict mutation has explicit stateful arms |
| `PyObject_Size` | `lenVal`, `lenValH`, `heapLen` | `lenM`, `liftRes` | `len(range(...))` applies `pySsizeRaising` to the `PyLong_AsSsize_t` result |
| `PyObject_GetItem` / `PyObject_SetItem` | `indexValH`, `heapIndex`, `assignToH` | `indexM`, `assignM` | shared; receiver-specific heap paths |
| `PyObject_Str` / `PyObject_Repr` | `strOfVal`, `reprVal`, `printOne` | `strOfVal`/rendering through `applyBuiltin` | shared rendering workers; sets and identity objects remain loud |
| `Py_EnterRecursiveCall` | `callIn` `callDepth` guard; `heapEq` active-pair recursion | `callInM` `callDepth` guard; `Kont` generator frames | call-depth limit modeled; comparison/repr C recursion units remain a ledger item |
| guarded accelerator admission | extractor `ACCELERATOR_ADMISSIONS` | extraction shared by both surfaces | `_bisect` is domain-guarded after `hi=-1` diverges (`ImportFrom:accelerator-outside-domain`); `_stat`/`_opcode` are measured or inspected divergences, and unmeasured entries refuse |

## Operator dispatch

| Source arm | Trunk | Runner | Protocol route |
|---|---|---|---|
| `+`, `-`, `*`, `/`, `//`, `%`, `**`, shifts, bitwise ops | `evalBinOp`; heap `evalBinOpH` for refs | `binOpM` / `evalOpen` | shared arithmetic workers; `**` uses the declared exact-base slice |
| unary `+`, `-`, `~`, `not` | `evalUnaryOp`, `evalUnaryOpH` | `unaryOpM` | `not` delegates to shared truthiness |
| `==`, `!=`, `<`, `<=`, `>`, `>=` | `evalCompareOpH`, `ordFromLt` | `evalCompareChainM` → shared `evalCompareOpH` | equality/order workers; non-finite container comparisons refuse |
| `is`, `is not` | `evalCompareOpH` identity arms | `evalCompareChainM` identity arms | refs/None/singletons; other immediate identity is loud |
| `in`, `not in` | `valContains`, `heapContains` | shared through `evalCompareChainM` | string, tuple/list, dict/set key paths; generator membership is loud/stateful |

## Builtin and method arms

Both surfaces expose the same following builtin inventory; the runner dispatch
is in `Monadic.Eval.applyBuiltin`, while the trunk dispatch is in its
`evalExpr` call arm. Each name below is one arm in both inventories.

| Builtins | Shared worker / protocol |
|---|---|
| `len` | `lenValH` / `heapLen` |
| `abs`, `int`, `float`, `bool`, `round` | scalar conversion/rounding workers |
| `divmod`, `pow` | `divmodVal`, `powModArgs`, `evalBinOp .pow` |
| `range` | `rangeMake`, `rangeVals` |
| `sorted` | `sortedValH`, `sortByLt` |
| `max`, `min` | `extremumValH`, `rvalLt` |
| `sum` | `sumFold`, iterator dispatch |
| `tuple`, `list`, `set`, `dict` | iterator protocol plus allocation workers |
| `any`, `all` | `anyAllScan` or stateful generator cursor |
| `next`, `iter`, `enumerate`, `count` | generator/iterator step workers |
| `ord`, `chr`, `ascii`, `hex`, `oct`, `bin`, `format`, `str`, `repr` | scalar/rendering workers |
| `print` | `strOfArgs`/`emit` (runner) and stdout-aware trunk arm |
| internal `<dictdel>`, `<attrdel>`, f-string and star markers | explicit synthetic boundaries; no source-level builtin lookup |

| Methods | Shared worker / protocol |
|---|---|
| dict `.get`, `.keys`, `.values`, `.items`, `.clear` | heap dict/view workers and live view cursors |
| list `.append`, `.pop`, `.insert` | `heapAppend`, `heapPop`, `heapInsert` |
| str `.swapcase`, `.isupper`, `.islower`, `.upper`, `.index`, `.join` | string workers, iterator drain |
| float `.is_integer` | `floatIsInteger` |
| admitted instance methods and namedtuple methods | `callIn` / class and tuple dispatch |

The census identifies the next protocol work precisely: replace raw `Int`
arguments at every C-index site with typed raising/clamping conversions;
separate `PyFloat_AsDouble` + platform `pow` from exact reciprocal arithmetic;
and add recursion-unit accounting at comparison/rendering sites. The runner
and trunk share the workers listed above, but their control/transport wrappers
remain separate and are not a refinement theorem.
