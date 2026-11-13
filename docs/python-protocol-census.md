# Python protocol census

Foundation step 2 (2026-11-10), refreshed 2026-11-11. This is a source
census, not a refinement claim. The CPython column names the entry point and
the protocol calls that can observe an argument. The two Lean columns name the
worker reached by each surface. `shared` means both surfaces call the same
worker; `separate` marks a control or transport wrapper that still needs an
adequacy theorem.

The F9 ledger also has a concrete assignment-body bridge:
`Monadic.finishCallM_assign_constant_body_ok` runs a name assignment through
the fuel-free statement walker and the stateful call restoration boundary. It
is theorem-only and leaves the assignment AST shape intact; general assignment
expressions and recursive calls remain open.

The matching exception path is covered by `Monadic.leaveCallM_modify_exn`,
using the generic `toRun_tryCatch_exn` substrate equation. A raised Python
error retains the mutated world and receives the same nested-frame depth
decrement as a successful return.

The top-level restoration half is now symmetric: `Monadic.finishCallM_modify_exn`
proves that an exception after an arbitrary world mutation restores the
requested boundary depth while retaining the mutated world.

## Protocol families

| CPython 3.9 entry and call order | Trunk (`Semantics.lean`) | Runner (`Monadic/`) | Current observation / gap |
|---|---|---|---|
| `Objects/object.c:PyObject_RichCompareBool` (identity shortcut, then rich comparison) and `PyObject_RichCompare` | `valEq`/`valEqList` for ref-free values; `heapEq`/`heapEqList`/`heapEqEntries` for heap values; `keyEq`/`keyEqList` for hash-key probes; `heapContainsScan`; `rvalLt`/`rvalLtList` for ordering | `evalCompareOpH`, `valContains`, and the same workers through `Monadic.Prim` | **Closed for the admitted overlap:** `keyEq_bool_int_richCompare` proves `keyEq` and `valEq` agree on bool/int keys, and `richcompare_bool.py` drives scalar equality, list membership, dict probes, and nested equality in both interpreters. The remaining workers stay separate because CPython dispatches table lookup, container equality, and ordering through different protocol functions; non-finite identity remains a loud boundary. |
| `Objects/object.c:PyObject_IsTrue` (type `nb_bool`, then `sq_length`, then default true) | `truthyH` and `truthy` | `truthyM` → `truthyH` | shared; instances and generators use the admitted default protocol, while unsupported cells refuse. |
| `Objects/object.c:PyObject_Hash` and `Objects/dictobject.c` key lookup (hash, then equality) | `hashableKey`, `setHashNat`, `dictFind`/`keyEq`, dict/set key gates | same workers through `liftRes` and evaluator arms | **Closed for the admitted key domain:** `keyEq_false_of_unhashable_left` and `dictFind_unhashable` prove the hash gate prevents an unhashable probe from matching; `hashkey_probe.py` covers bool/int collisions, tuple keys, and the unhashable TypeError in both interpreters. Hashing and equality remain separate CPython protocols; identity hashes and unsupported set construction refuse. |
| `Objects/abstract.c:PyNumber_Index`, then `PyNumber_AsSsize_t` / `Objects/listobject.c` Clinic conversion | `asInt`, `asRangeBound`, then `pySsizeRaising` at `heapInsert`, `heapPop`, and `lenVal` | same workers | shared raising conversion with CPython's exact `OverflowError`; the sequence-subscript `PyExc_IndexError` variant is `pySsizeIndex`/`indexErrorSize`. |
| `Python/ceval.c:_PyEval_SliceIndex` (index protocol, then signed-size clipping) | `pySsizeClamping`, `asSliceIdx`, `normIndex` | shared | slice bounds clip to the pinned signed 64-bit range before ordinary sequence normalization. |
| `Objects/floatobject.c:PyFloat_AsDouble` and `Objects/longobject.c:PyLong_AsDouble` (left conversion, right conversion, then operation) | `floatNumber` / `Float64.fromInt`; integer true division uses `Float64.divideInt` directly | shared through `evalBinOp` | Mixed division and negative or mixed-float power preserve conversion order. Portable zero, infinity, and unit-base power cases are decided; NaN payload, complex, and platform-libm `pow` cases stay loud. |
| `Objects/abstract.c:PyObject_GetIter`, then `PyIter_Next` | `rangeVals`, `heapContains`, `execFor*`, and generator steppers | `iterValues`, `Kont` cursors, and `exec*` shells | **Closed for the admitted value/cursor domain:** `iterValues_rangeVals` proves the shared immediate range worker; `iteration_probe.py` covers range, tuple, and live list growth in both interpreters. Generator and dictionary mutation remain explicit stateful cursors, following their distinct CPython iterator objects. |
| `Objects/abstract.c:PyObject_Size` (sequence/mapping length) | `lenVal`, `lenValH`, `heapLen` | `lenM`, `liftRes` | shared; `len(range(...))` narrows the computed result through `pySsizeRaising`. |
| `Objects/abstract.c:PyObject_GetItem` / `PyObject_SetItem` | `indexValH`, `heapIndex`, `assignToH` | `indexM`, `assignM` | shared receiver-specific heap paths; list and dict errors retain their CPython classes/messages. |
| `Objects/object.c:PyObject_Str` / `PyObject_Repr`, and `Objects/listobject.c`/`dictobject.c` container renderers | `strOfVal`, `reprVal`, `printOne` | the same rendering workers through `applyBuiltin` and `emit` | **Closed for the admitted overlap:** `strOfValH_basic` proves heap-aware `str()` delegates the four immediate scalar cases to `strOfVal`; `render_probe.py` covers scalar `str`, tuple `repr`, and list `repr` in both interpreters. Sets, identity objects, unsupported Unicode rendering, and unbounded recursion remain loud. |
| `Include/internal/pycore_ceval.h:Py_EnterRecursiveCall` at each C frame (with matching leave) | `pythonRecursionFull` plus call, argument-binding, exception, comparison, builtin, generator, and class-construction checks | the same predicate through `callInM`, `withFrameRecursionUnit`, `withWorldRecursionUnit`, and `richCompareRecursionCheckH` | **Closed:** `python_frame_then_c_boundary` proves the Python-frame and nested C-call predicates differ at the pinned boundary; `recursive_entry_probe.py` covers int/str calls at shallow and boundary depths in both interpreters. The normalized `World.callDepth` and pinned limit 1000 cover admitted sites; direct rendering beyond `reprFuel` remains a declared refusal. |
| extractor `ACCELERATOR_ADMISSIONS` (native import, then guarded call domain) | structured admission metadata | extraction shared by both surfaces | `_bisect` is guarded after the measured `hi=-1` divergence; `_stat` and `_opcode` remain explicitly unadmitted where equivalence is not established. |

The census therefore records five protocol families with more than one Lean
worker (`RichCompareBool`, hash/equality key lookup, iteration, rendering, and
recursive entry). Those splits are now named rather than hidden behind the word
"shared". A future admission must either route all observers through one
worker or add a theorem and a domain row explaining why the split is exact.

The two interpreter control surfaces now have a first compositional adequacy
edge: `Monadic.twinAgrees_evalOpenList_constants` proves by induction on an
arbitrary-length expression list that the fuel-free monadic list walker and the
trunk's fuelled `evalExprs` agree for constant lists whenever the strict list
length fuel bound holds. This composes the literal bridge with left-to-right
list control without adding another per-operator refinement lemma.
`Monadic.twinAgrees_evalOpenList_of_each` factors that induction into a
reusable composition theorem: any pointwise expression bridge, quantified over
the continuation state and positive remaining fuel, lifts to the whole list.
`Monadic.twinAgrees_execOpenList_of_each` supplies the matching statement
sequencing theorem, preserving the updated state after `.next` and the early
`.brk`, `.cont`, `.ret`, exception, timeout, and refusal flows. Calls and
stateful script control remain the next adequacy boundary. At the call entry,
`Monadic.twinAgrees_callIn_missing_function` now closes the preflight branch:
for a positive fuel and an absent function table entry, both interpreters
return the same depth-normalized `NameError` without changing the world.
`Monadic.twinAgrees_callIn_unsupported_args` closes the next ordered preflight
branch when the function has unsupported parameter features and the generator
capture guard is clear; both surfaces return the same loud refusal before body
execution. `Monadic.twinAgrees_callIn_arity_error` now closes the arity branch
as well, including the depth-sensitive CPython diagnostic and retained world.
`Monadic.twinAgrees_callIn_static_locals` closes the following static-locals
refusal branch before body execution.
`Monadic.twinAgrees_callIn_zero_fuel` also pins the shared timeout boundary for
every call shape.
The substrate now exposes kernel-checked `Monadic.toRun_set` and
`Monadic.toRun_modify` equations beside `toRun_get`/`toRun_bind`, so positive
fuel calls and scripts share one state-wrapper boundary.
`Monadic.toRun_liftState` extends that boundary across the `StateT`-to-`ExceptT`
frame lift, preserving timeout, refusal, exception, and success projections.
`Monadic.toRun_bind_ok` factors the successful bind projection used by
`tryCatch` and call unwinding, so those proofs can stay at the `Run` boundary.
`Monadic.toRun_tryCatch_ok` specializes the same projection to a successful
protected action, preserving its returned state and value through the handler
layer.
`Monadic.twinAgrees_execOpenList_nil` and its world projection close the empty
statement-body base case consumed by ordinary call entry.
`Run.finishCallAt_ok` pins the successful trunk-side call-depth restoration
that the monadic `finishCallM` must match.
`Run.finishCallAt_exn` pins the corresponding raised-exception unwind, keeping
the world observable while restoring the requested depth.
`Monadic.finishCallM_pure_ok` composes the state-retaining try/catch and modify
projections for a pure successful body, restoring call depth on the monadic
surface as well.
`Monadic.finishCallM_empty_body_ok` composes the same restoration with the
actual empty `execOpenList` body and its `inWorld` projection.
`Monadic.finishCallM_pass_body_ok` extends this composition to the first
nonempty statement body, a one-statement `pass` sequence.
`Monadic.finishCallM_expr_constant_body_ok` covers the first effectful body:
an expression statement evaluating an integer constant before completion.
`Monadic.finishCallM_modify_ok` is the first state-mutating call theorem: an
arbitrary world mutation threads through restoration while preserving the
mutated heap/global/output/clock fields.
`Monadic.leaveCallM_modify_ok` covers the matching nested-call unwind: an
arbitrary mutation is followed by the active frame's depth decrement while
the mutated world remains observable.

## Operator dispatch

| Source arm | CPython entry and protocol order | Trunk | Runner | Domain / remaining gap |
|---|---|---|---|---|
| `+`, `-`, `*`, `/`, `//`, `%`, `**`, shifts, bitwise ops | `Objects/abstract.c:PyNumber_*` (numeric dispatch, then operand conversion); string `%` uses `PyUnicode_Format`; power uses `float_pow` for floating paths | `evalBinOp`; heap `evalBinOpH` for refs | `binOpM` / `evalOpen` | shared arithmetic workers; bare and measured-width string conversions are live, while precision, mapping keys, complex results, and platform `pow` remain loud. |
| unary `+`, `-`, `~`, `not` | `PyNumber_Positive`, `PyNumber_Negative`, `PyNumber_Invert`, or `PyObject_IsTrue` for `not` | `evalUnaryOp`, `evalUnaryOpH` | `unaryOpM` | `not` delegates to shared truthiness. |
| `==`, `!=`, `<`, `<=`, `>`, `>=` | `PyObject_RichCompare` (container implementations call `PyObject_RichCompareBool` for element equality) | `evalCompareOpH`, `ordFromLt` | `evalCompareChainM` → shared `evalCompareOpH` | value and heap workers are explicit; non-finite container comparisons refuse because immediate identity is not represented. |
| `is`, `is not` | `Py_Is`/pointer identity in the comparison opcode; no value comparison | identity arms of `evalCompareOpH` | identity arms of `evalCompareChainM` | refs, `None`, and singleton markers are exact; other immediate identity is loud. |
| `in`, `not in` | `PySequence_Contains` or mapping key lookup; each element probe uses `PyObject_RichCompareBool` | `valContains`, `heapContains` | shared through `evalCompareChainM` | strings, tuples/lists, and dict/set keys are admitted; generator membership remains stateful/loud. |

## Builtin arms

Both surfaces expose the following names. The runner dispatch is in
`Monadic.Eval.applyBuiltin`; the trunk dispatch is its `evalExpr` call arm.
The middle column records the CPython entry point and the protocol sequence
that the worker must preserve.

| Builtin arm | CPython entry and protocol order | Trunk / runner worker | Current boundary |
|---|---|---|---|
| `len` | `builtin_len` → `PyObject_Size` | `lenValH` / `heapLen`; `lenM` | signed-size narrowing is pinned; unsupported objects refuse. |
| `abs`, `int`, `float`, `bool`, `round` | `builtin_abs`, `PyNumber_Long`, `PyNumber_Float`, `PyObject_IsTrue`, `builtin_round` (conversion, then admitted numeric method frame) | scalar conversion, truthiness, and rounding workers | scalar domain is live; unsupported protocols and unmodeled frames refuse. |
| `divmod`, `pow` | `builtin_divmod` / `PyNumber_Divmod`; `builtin_pow` / `PyNumber_Power` (argument conversion before arithmetic) | `divmodVal`, `powModArgs`, `evalBinOp .pow` | integer modular slice and portable power cases are live; platform `pow` remains loud. |
| `range` | `range_constructor` (argument `__index__`, then size computation) | `rangeMake`, `rangeVals` | range bounds and result narrowing use the shared index workers. |
| `sorted` | `builtin_sorted` → `PySequence_List`/`PyList_Sort` → rich comparison | `sortedValH`, `sortByLt` | list materialization and stable `rvalLt` are live; non-finite comparison and unsupported key/cmp paths refuse. |
| `max`, `min` | `builtin_min_max` → `PyObject_RichCompareBool` for each candidate | `extremumValH`, `rvalLt` | argument order and comparison recursion are pinned; unsupported ordering refuses. |
| `sum` | `builtin_sum` → iterator protocol and numeric addition | `sumFold` and iterator dispatch | admitted scalar and iterator paths are live; unsupported additions refuse. |
| `tuple`, `list`, `set`, `dict` | constructors drain `PyObject_GetIter`; list/dict/set constructors allocate and may hash or compare keys | iterator workers plus allocation workers | modeled allocation budgets replace environment-dependent exhaustion; unsupported pair/key forms refuse. |
| `any`, `all` | `builtin_any`/`builtin_all` → `PyObject_IsTrue` for each iterator item | `anyAllScan` or stateful generator cursor | short circuit and generator state are explicit. |
| `next`, `iter`, `enumerate`, `count` | iterator constructor/`tp_iternext`, including `StopIteration` | generator/iterator step workers | admitted generators are stateful; unsupported delegation remains loud. |
| `ord`, `chr`, `ascii`, `hex`, `oct`, `bin`, `format`, `str`, `repr` | scalar conversion and `PyObject_Str`/`PyObject_Repr` | scalar and rendering workers | printable scalar/container inventory is shared; sets and identity objects refuse. |
| `print` | `builtin_print` → `PyObject_Str`/`PyFile_WriteObject` in argument order | stdout-aware trunk arm; `strOfArgs`/`emit` in runner | stdout is visible only through stateful/script surfaces; kwargs and unsupported rendering remain loud. |
| internal `<dictdel>`, `<attrdel>`, f-string and star markers | extractor marker arms, not Python-name lookup | explicit synthetic boundaries | source-level shadows cannot change these internal dispatches; native source-node semantics remain follow-up work. |

## Method arms

| Method arm | CPython entry and protocol order | Trunk / runner worker | Current boundary |
|---|---|---|---|
| dict `.get`, `.keys`, `.values`, `.items`, `.clear` | `dict_get`, `dict_keys`, `dict_values`, `dict_items`, `dict_clear`; key methods hash/probe before returning a view | heap dict/view workers and live view cursors | dict lookup, mutation, and live views are admitted; unsupported view operations refuse. |
| list `.append`, `.pop`, `.insert` | `list_append`, `list_pop`, `list_insert`; index arguments use `PyNumber_Index` then the raising or clamping size conversion | `heapAppend`, `heapPop`, `heapInsert` | raising/clamping workers are shared and endpoint-tested; allocation limits remain loud. |
| str `.swapcase`, `.isupper`, `.islower`, `.upper`, `.index`, `.join` | Unicode methods, with `.index` raising after a search and `.join` draining an iterable | string workers and iterator drain | admitted Unicode 3.9 table is live; unsupported Unicode/rendering forms refuse. |
| float `.is_integer` | `float_is_integer` on the binary64 value | `floatIsInteger` | binary64 word semantics are shared. |
| admitted instance methods and namedtuple methods | descriptor lookup, bound `self`, then `PyObject_Call` | `callIn` / class and tuple dispatch | qualified method entries and static namedtuple recognition remain architectural boundaries; runtime class/namedtuple values are the follow-up. |

## Work list produced by the census

The remaining protocol work is now explicit. Rich comparison has multiple
context workers and needs either one shared worker or a refinement/domain
theorem before widening identity-sensitive values. Hash/key probes and
rendering have the same obligation. The index workers already separate raising
and clamping conversions; the float conversion worker is shared, but platform
`pow` remains refused. Recursive entry is shared as a predicate, with direct
rendering beyond `reprFuel` still outside the decided domain. The runner and
trunk control/transport wrappers remain separate and do not yet have a full
recursive expression, statement, or script adequacy theorem.

The nonempty control-flow bridge `Monadic.finishCallM_ret_constant_body_ok`
also covers a one-statement `return 1` body, preserving `RFlow.ret` through
the same world and depth restoration boundary.

Its bare-return counterpart, `Monadic.finishCallM_ret_none_body_ok`, preserves
the `RFlow.ret .none` channel through the same boundary.

The loop-control bridge `Monadic.finishCallM_break_body_ok` preserves
`RFlow.brk` through the boundary as well; enclosing-loop handling remains in
the continuation layer.

The corresponding `Monadic.finishCallM_continue_body_ok` bridge preserves
`RFlow.cont`; loop re-testing remains owned by the continuation layer.

The two-statement sequencing bridge `Monadic.finishCallM_pass_expr_body_ok`
composes `pass` followed by an integer expression statement through the same
left-to-right body walker and restoration boundary.

`Monadic.finishCallM_pass_ret_body_ok` covers the corresponding early-return
sequence, proving that the second statement's `RFlow.ret` stops the body walk.

`Monadic.finishCallM_pass_break_body_ok` covers normal sequencing into a
`break`, preserving `RFlow.brk` for the enclosing loop shell.

`Monadic.finishCallM_pass_continue_body_ok` covers the matching normal-to-
`continue` sequence and preserves `RFlow.cont`.

`Monadic.finishCallM_three_pass_body_ok` checks a three-statement normal body,
showing that the sequence walker composes beyond the two-statement cases.

`Monadic.finishCallM_four_pass_body_ok` extends the same kernel-checked
normal sequencing to four statements.

`Monadic.finishCallM_five_pass_body_ok` extends normal sequencing to five
statements.

`Monadic.finishCallM_four_pass_ret_body_ok` extends early-return sequencing
to four normal statements followed by a return.

`Monadic.finishCallM_pass_assign_empty_locals_body_ok` is the first assignment
sequencing bridge with an explicit empty frame-local environment; the body
updates its local binding and still returns normal after projection to `World`.

`Monadic.finishCallM_assign_existing_local_body_ok` covers assignment to an
already-bound local, preserving the same normal-flow and depth result.

`Monadic.finishCallM_assign_existing_local_ret_body_ok` composes that local
update with a following constant return, checking assignment state threading
into early flow.

`Monadic.finishCallM_assign_existing_local_pass_body_ok` checks the symmetric
normal continuation after the local assignment.

`Monadic.finishCallM_assign_existing_local_break_body_ok` composes the local
assignment into `RFlow.brk` for the enclosing loop shell.

`Monadic.finishCallM_assign_existing_local_continue_body_ok` composes the
same local assignment into `RFlow.cont`.

`Monadic.finishCallM_assign_existing_local_ret_none_body_ok` composes the
assignment into bare-return flow, preserving `RFlow.ret .none`.

`Monadic.finishCallM_assign_existing_local_expr_body_ok` composes the local
assignment into a following normal expression statement.

`Monadic.finishCallM_assign_two_existing_locals_body_ok` checks two successive
existing-local assignments, threading both updates through normal completion.

`Monadic.finishCallM_assign_three_existing_locals_body_ok` extends the same
state threading to three successive assignments.

`Monadic.finishCallM_assign_existing_local_ret_pass_body_ok` checks that a
return after assignment short-circuits a trailing statement.

`Monadic.finishCallM_three_pass_ret_body_ok` extends early-return sequencing
to three normal statements followed by a return.

`Monadic.finishCallM_three_pass_break_body_ok` extends break-flow sequencing
to three normal statements followed by `break`.

`Monadic.finishCallM_three_pass_continue_body_ok` extends continue-flow
sequencing to three normal statements followed by `continue`.

`Monadic.finishCallM_three_pass_ret_none_body_ok` extends bare-return
sequencing to three normal statements followed by `return`.

`Monadic.finishCallM_assign_two_existing_locals_ret_body_ok` extends
assignment return short-circuiting to two successive local updates.

`Monadic.finishCallM_assign_three_existing_locals_ret_body_ok` extends it to
three successive local updates followed by a return.

`Monadic.finishCallM_assign_three_existing_locals_pass_body_ok` checks the
normal continuation after those three updates.

`Monadic.finishCallM_assign_three_existing_locals_expr_body_ok` checks the
normal expression continuation after the three updates.

`Monadic.finishCallM_assign_four_existing_locals_body_ok` extends normal
assignment state threading to four successive local updates.

`Monadic.finishCallM_assign_four_existing_locals_ret_body_ok` extends the same
four-update bridge through an early value return.

`Monadic.finishCallM_assign_four_existing_locals_pass_body_ok` extends the
four-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_four_existing_locals_expr_body_ok` extends the
four-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_four_existing_locals_ret_none_body_ok` extends the
four-update bridge through a bare return.

`Monadic.finishCallM_assign_four_existing_locals_break_body_ok` extends the
four-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_four_existing_locals_continue_body_ok` extends the
four-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_five_existing_locals_body_ok` extends normal
assignment state threading to five successive local updates.

`Monadic.finishCallM_assign_five_existing_locals_ret_body_ok` extends the
five-update bridge through an early value return.

`Monadic.finishCallM_assign_five_existing_locals_pass_body_ok` extends the
five-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_five_existing_locals_expr_body_ok` extends the
five-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_five_existing_locals_ret_none_body_ok` extends the
five-update bridge through a bare return.

`Monadic.finishCallM_assign_five_existing_locals_break_body_ok` extends the
five-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_five_existing_locals_continue_body_ok` extends the
five-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_six_existing_locals_body_ok` extends normal
assignment state threading to six successive local updates.

`Monadic.finishCallM_assign_six_existing_locals_ret_body_ok` extends the
six-update bridge through an early value return.

`Monadic.finishCallM_assign_six_existing_locals_pass_body_ok` extends the
six-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_six_existing_locals_expr_body_ok` extends the
six-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_six_existing_locals_ret_none_body_ok` extends the
six-update bridge through a bare return.

`Monadic.finishCallM_assign_six_existing_locals_break_body_ok` extends the
six-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_six_existing_locals_continue_body_ok` extends the
six-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_seven_existing_locals_body_ok` extends normal
assignment state threading to seven successive local updates.

`Monadic.finishCallM_assign_seven_existing_locals_ret_body_ok` extends the
seven-update bridge through an early value return.

`Monadic.finishCallM_assign_seven_existing_locals_pass_body_ok` extends the
seven-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_seven_existing_locals_expr_body_ok` extends the
seven-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_seven_existing_locals_ret_none_body_ok` extends the
seven-update bridge through a bare return.

`Monadic.finishCallM_assign_seven_existing_locals_break_body_ok` extends the
seven-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_seven_existing_locals_continue_body_ok` extends the
seven-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_eight_existing_locals_body_ok` extends normal
assignment state threading to eight successive local updates.

`Monadic.finishCallM_assign_eight_existing_locals_ret_body_ok` extends the
eight-update bridge through an early value return.

`Monadic.finishCallM_assign_eight_existing_locals_pass_body_ok` extends the
eight-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_eight_existing_locals_expr_body_ok` extends the
eight-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_eight_existing_locals_ret_none_body_ok` extends the
eight-update bridge through a bare return.

`Monadic.finishCallM_assign_eight_existing_locals_break_body_ok` extends the
eight-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_eight_existing_locals_continue_body_ok` extends the
eight-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_nine_existing_locals_body_ok` extends normal
assignment state threading to nine successive local updates.

`Monadic.finishCallM_assign_nine_existing_locals_ret_body_ok` extends the
nine-update bridge through an early value return.

`Monadic.finishCallM_assign_nine_existing_locals_pass_body_ok` extends the
nine-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_nine_existing_locals_expr_body_ok` extends the
nine-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_nine_existing_locals_ret_none_body_ok` extends the
nine-update bridge through a bare return.

`Monadic.finishCallM_assign_nine_existing_locals_break_body_ok` extends the
nine-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_nine_existing_locals_continue_body_ok` extends the
nine-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_ten_existing_locals_body_ok` extends normal
assignment state threading to ten successive local updates.

`Monadic.finishCallM_assign_ten_existing_locals_ret_body_ok` extends the
ten-update bridge through an early value return.
