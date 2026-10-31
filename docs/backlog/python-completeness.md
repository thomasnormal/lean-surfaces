# The python-completeness lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the python-completeness lane.** Ids are `YYYY-MM-DD-pycomplete-<n>` and need
no reservation, because the lane name makes them unique — which this lane can
attest to the value of: its rung-3b landing was written as §L59, renumbered to
§L74, then to §L85, and never landed under any of them, because each number
was taken while the lane sat in the build queue.

**Everything before 2026-08-22 is in `docs/backlog.md`** and stays there; this
lane's history is §L39 (the founding census), §L49 (rung 1), §L51 (rung 2) and
§L53 (rung 3's census), and every one of those references keeps resolving.

The lane's charter is `docs/completeness.md`: close the extractor/interpreter
refusal surface toward ARBITRARY Python, censused before priced and priced
before built. `harness/refusal_census.py` is the scoreboard and the acceptance
battery in one — it exits nonzero on drift, so a landing that moves the tier
must move the census in the same commit.

## 2026-10-30-pycomplete-184 — admit nested defs inside loops

Nested function definitions in a function's loop, branch, context-manager, or
exception body now retain the enclosing function as their closure scope. The
existing cell allocator reuses one slot per enclosing frame, so a loop-created
closure observes the current binding on every call, exactly as CPython does.
The recursive nested-name and generator-cell-after-first-call boundaries remain
loud.

| Measurement | Result |
|---|---|
| Extractor tests | 150 passed; the loop nested-def fixture now records `NestedDef` with `<cell>a` |
| Focused differential | `closure_lab::def_in_loop(3)` MATCH in both interpreters (`6`) |
| Full executable differential | 3,758 cases: 3,721 matched / 37 recorded refusals / 0 failed |
| Full proof differential | 3,758 cases: 3,620 matched / 138 refusals / 0 failed |
| Refusal census | 37 rows in 12 classes, 0 drifts; `closure_lab::def_in_loop` retired |

DECIDED: propagate the enclosing function scope through compound statement
bodies so loop-created closures use the existing shared-cell runtime; retain
loud failure for recursive nested names, escaped cells, and generator
rebindings after their first call.

## 2026-10-26-pycomplete-163 — erase an unread ordinary-class assignment

The dead-value ingestion rewrite now covers admitted, creation-pure ordinary
classes as well as builtin exception classes. The exact `f = Cell; return n`
shape is erased only when the assigned name is not a parameter and does not
occur in the returned expression. Returned class objects, parameter shadows,
and every other observed first-class class value remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `cls_lab::class_as_value` MATCH in native and proof interpreters; returned class values remain loud and parameter shadowing follows CPython |
| Full executable differential | 3,694 cases: 3,650 matched / 44 recorded refusals / 0 failed |
| Full proof differential | 3,694 cases: 3,541 matched / 153 refusals / 0 failed |
| Refusal census | 44 rows in 12 classes, 0 drifts; `firstclass.callable` fell from 5 to 4 |
| Build and checks | `lake build leanmodels-run`, both differentials, and `git diff --check` passed |

DECIDED: erase only an unread assignment of an admitted, creation-pure class in
the exact two-statement return shape; retain loud failure for returned class
objects, shadowed names, and general first-class class values.

## 2026-10-26-pycomplete-162 — erase an unread exception-class assignment

An admitted exception class assigned to a local and never read before a direct
return is now erased at ingestion. The rewrite is limited to the exact
`x = Stop; return value` shape and checks the module's admitted exception-class
table; observed values, returned classes, and all other first-class class
forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab::exc_as_value(1)` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,649 matched / 45 recorded refusals / 0 failed |
| Full proof differential | 3,694 cases: 3,540 matched / 154 refusals / 0 failed |
| Refusal census | 45 rows in 12 classes, 0 drifts; `firstclass.callable` fell from 6 to 5 |
| Build and checks | JSON/runner build, both differentials, and `git diff --check` passed |

DECIDED: erase only an unread assignment of an admitted exception class in the
exact two-statement return shape; retain loud failure for observed exception
values and general first-class class values.

## 2026-10-26-pycomplete-161 — admit immediate local aliases of `bool` and `divmod`

The exact two-statement shape `f = bool; return f(x)` (and its two-argument
`divmod` counterpart) now lowers at ingestion to the ordinary builtin call.
This preserves the existing runtime and proof paths while keeping returned
function values, class values, and general callable aliases loud: the public
value boundary still has no function identity.

| Measurement | Result |
|---|---|
| Focused differential | `bool_lab::first_class` and `divmod_lab::first_class` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,648 matched / 46 recorded refusals / 0 failed |
| Full proof differential | 3,694 cases: 3,539 matched / 155 refusals / 0 failed |
| Refusal census | 46 rows in 12 classes, 0 drifts; `firstclass.callable` fell from 8 to 6 |
| Build and checks | `lake build leanmodels-run`, docs check, both differentials, and `git diff --check` passed |

DECIDED: admit only a direct local builtin alias followed immediately by its
call for `bool` and `divmod`; retain loud failure for all other first-class
callable observations and aliases.

## 2026-10-26-pycomplete-160 — admit flat starred `for` targets

Flat starred loop targets now lower to a synthetic loop binding followed by
the existing `UnpackAssign` at the front of the loop body. The item is bound
before unpacking, the middle slice is a fresh heap list, and the loop and
ordinary assignment paths therefore share their error and aliasing behavior.
Nested, multiple-star, and non-name target shapes remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `star_lab::star_for` matches the CPython suffix-target case in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,646 matched / 48 recorded refusals / 0 failed |
| Full proof differential | 3,694 cases: 3,537 matched / 157 refusals / 0 failed |
| Refusal census | 48 rows in 12 classes, 0 drifts; `star_lab::star_for` removed from `starred.position` |
| Extractor tests | 148 passed |
| Lean build and checks | `lake build leanmodels-run`, focused differential, and `git diff --check` passed |

DECIDED: admit one flat starred `for` target by lowering it to the existing
unpack worker; retain loud failure for nested or otherwise unsupported target
shapes.

## 2026-10-26-pycomplete-159 — admit starred positional call arguments

Positional starred call arguments now lower to the unspellable `<star-arg>`
marker. Both interpreter paths evaluate the source expression once, expand its
admitted eager iterable values in place, and preserve CPython's left-to-right
argument order and error classes. Keyword unpacking and set-order-dependent
iterables remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `star_lab::star_call` matches in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,645 matched / 49 recorded refusals / 0 failed |
| Full proof differential | 3,694 cases: 3,536 matched / 158 refusals / 0 failed |
| Refusal census | 49 rows in 13 classes, 0 drifts; `star_lab::star_call` removed from `call.starred-args` |
| Extractor tests | 146 passed |
| Lean build and generated checks | `lake build leanmodels-run`, docs check, coverage freshness, backlog index, and diff check pass |

DECIDED: admit positional starred call arguments through `<star-arg>` and
retain loud failure for `**kwargs`, set-order-dependent expansion, and other
unmodeled iterable shapes.

## 2026-10-26-pycomplete-158 — admit starred set displays

Starred set displays now reuse the landed display lowering: the expanded
elements are materialized through `<star-list>` and passed to the existing
`set(...)` constructor. This preserves left-to-right element evaluation,
hashability checks, and value deduplication without adding interpreter or
proof arms. A set result still cannot cross the public value boundary, so the
acceptance example observes `len({*a})`; direct set returns remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `star_lab::star_set` matches in native and proof interpreters; the starred-call and starred-`for` rows are landed |
| Full executable differential | 3,694 cases: 3,644 matched / 50 recorded refusals / 0 failed |
| Full proof differential | 3,694 cases: 3,535 matched / 159 refusals / 0 failed |
| Refusal census | 50 rows in 13 classes, 0 drifts; `star_lab::star_set` removed from `set.order` |
| Extractor tests | 145 passed |
| Lean build and generated checks | `lake build leanmodels-run`, docs check, coverage freshness, backlog index, and diff check pass; the repository-wide build still has the pre-existing VC2/Tests and unrelated example failures |

DECIDED: admit starred set displays through `set(list(...))`; retain loud
boundary behavior for returning a heap set and hash-order-dependent operations.

## 2026-10-26-pycomplete-157 — admit early nested calls

Direct calls of a nested function name before its `def` now use the existing
static-local marker installed at frame entry. The marker preserves CPython's
lookup rule and raises `UnboundLocalError` before the definition executes;
ordinary local-shadowing calls and deeper unsupported closure shapes remain
loud. The extractor no longer rejects this direct nested-def shape, and both
interpreter paths carry the same class and name.

| Measurement | Result |
|---|---|
| Focused differential | `closure_lab.early_call(1)` matches CPython's `UnboundLocalError` in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,643 matched / 51 recorded refusals / 0 failed |
| Full proof differential | 3,694 cases: 3,534 matched / 160 refusals / 0 failed |
| Refusal census | 51 rows in 13 classes, 0 drifts; `closure_lab::early_call` removed from `closure.admission` |
| Extractor tests | 145 passed |
| Lean build and generated checks | `lake build leanmodels-run`, docs check, coverage freshness, backlog-index freshness, and `git diff --check` passed |

DECIDED: admit direct nested-def calls before the definition through the
static-local marker; retain loud failure for ordinary dynamic local shadows,
recursive nested-name captures, and other closure boundaries.

## 2026-10-26-pycomplete-156 — make starred-display lowering immune to shadowing

Starred displays now lower through the unspellable synthetic builtin names
`<star-tuple>` and `<star-list>`. The generated calls therefore cannot resolve
through a source `list` or `tuple` binding, matching CPython's bytecode-level
`BUILD_*_UNPACK` behavior. The old lexical shadow census is removed; the
function-local `list` shadow in `star_shadow.shadowed` now runs and returns the
same list as CPython.

| Measurement | Result |
|---|---|
| Focused differential | All four `star_shadow` rows match in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,642 matched / 52 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,533 matched / 161 refused / 0 failed |
| Refusal census | 52 rows in 13 classes, 0 drifts; `star_shadow::shadowed` removed from `shadow.module-census` |
| Extractor tests | 145 passed |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: reserve unspellable synthetic names for generated starred-display
constructors; ordinary source shadowing no longer affects the lowering. Reread
the inbox before selecting the next measured gap.

## 2026-10-26-pycomplete-155 — admit literal custom instance equality

The class tier now admits the exact two-parameter method
`__eq__(self, other): return True` or `False`. Instances carry an internal
marker consumed by heap equality, so the literal result applies to self,
instance, and immediate comparisons in either operand order. Richer equality
protocols remain refused under the dunder guard.

| Measurement | Result |
|---|---|
| Focused differential | `cls_lab.weird_eq()` and `weird_eq_compare()` match CPython |
| Refusal census | `cls_lab::weird_eq` removed from `class.dunder-protocol` |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: admit only the exact two-parameter Boolean-literal `__eq__` shape;
retain loud failure for richer custom equality and all other protocol dunders.

## 2026-10-26-pycomplete-150 — admit the exact exception-sensitive `__exit__` test

The synchronous context-manager slice now recognizes the exact four-parameter
method `__exit__(self, exc_type, exc, tb): return exc_type is not None`.
Normal completion still supplies `(None, None, None)`; exceptional body paths
supply a fixed non-`None` marker for `exc_type` and `None` for the other two
arguments. General exception-triple inspection remains refused.

| Measurement | Result |
|---|---|
| Focused differential | `with_lab.argument_sensitive_suppression()` matches with value `10`; existing normal and transparent suppression rows remain unchanged |
| Refusal census | `with_lab::argument_sensitive_suppression` removed from `with.exception-arguments` |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: admit only this structural test with the fixed marker; retain loud
failure for arbitrary exception payload inspection until frame state carries a
full exception triple.

## 2026-10-26-pycomplete-151 — allow inert `__repr__` on context managers

The context-manager admission now permits a class to define `__repr__` in
addition to `__enter__` and `__exit__`. Instances still refuse at the rendering
boundary, so the method cannot affect an operation admitted by the tier. Other
extra dunders remain refused under the default-protocol guard.

| Measurement | Result |
|---|---|
| Focused differential | `with_lab.extra_dunder()` matches with value `0` |
| Refusal census | `with_lab::extra_dunder` removed from `with.extra-dunder` |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: permit only inert `__repr__` on an admitted context manager; retain
loud failure for dunders that can alter modeled protocol operations.

## 2026-10-26-pycomplete-152 — admit cached immediate identity

The identity comparison tier now decides booleans and integer immediates in
CPython 3.9's pinned small-integer cache, `-5` through `256`. Mixed bool/int
identity remains false, while larger integer pairs and other immediate kinds
remain loud because their identity is implementation-dependent.

| Measurement | Result |
|---|---|
| Focused differential | `dict_lab.int_is(1, 1)` matches `True`; `int_is(1, 2)` matches `False` |
| Refusal census | `dict_lab::int_is` removed from `op.Is-immediates` |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: admit only the pinned bool and small-integer singleton identities;
retain loud failure for implementation-dependent immediate identities.

## 2026-10-26-pycomplete-153 — admit literal custom instance repr

Direct `repr(C())` now accepts a class whose `__repr__` has one `self`
parameter and returns a string literal. The renderer keeps the existing loud
boundary for default instances, closures, generators, and custom protocols
inside containers; only the direct scalar result is admitted.

| Measurement | Result |
|---|---|
| Focused differential | `repr_lab.custom()` matches with value `"custom"`; `repr_lab.instance()` remains loud |
| Refusal census | `repr_lab::custom` removed from `class.dunder-protocol` |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: admit only the exact literal-returning direct `__repr__` shape;
retain loud failure for richer custom rendering and nested instance repr.

## 2026-10-26-pycomplete-154 — admit literal custom instance truthiness

Direct `bool(C())` now accepts a class whose `__bool__` has one `self`
parameter and returns a Boolean literal. The instance carries that fixed
protocol result through the heap, so conditionals and other truthiness sites
see the same result; default instances and richer custom truthiness remain
loud or retain their default `True` behavior.

| Measurement | Result |
|---|---|
| Focused differential | `bool_lab.custom()` matches with value `False`; `bool_lab.instance()` remains `True` |
| Refusal census | `bool_lab::custom` removed from `class.dunder-protocol` |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: admit only the exact one-parameter Boolean-literal `__bool__` shape;
retain loud failure for richer custom truthiness and all other protocol dunders.

## 2026-10-26-pycomplete-149 — scope starred-display shadow checks lexically

Starred-display lowering now checks `list` and `tuple` bindings in the lexical
scope containing each display. A function-local shadow still refuses that
function, while an unrelated sibling function no longer poisons the module;
`star_shadow.elsewhere(3)` therefore matches CPython's `[1, 2, 3]` while
`shadowed(3)` remains loud. Module-scope bindings still refuse all displays in
that module, preserving soundness for the lowered names.

| Measurement | Result |
|---|---|
| Focused differential | `star_shadow.elsewhere(3)` matches `[1, 2, 3]`; `shadowed(3)` remains refused |
| Full executable differential | 3,694 cases: 3,634 matched / 60 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,525 matched / 169 refused / 0 failed |
| Refusal census | 60 rows in 18 classes, 0 drifts; `star_shadow::elsewhere` removed from `shadow.module-census` |
| Build/checks | extractor/spec/tool checks, `lake build leanmodels-run`, coverage freshness, backlog-index freshness, and `git diff --check` pass |

DECIDED: scope synthetic-name shadow checks lexically; retain loud behavior for
the shadowed scope and module-scope bindings, while allowing unaffected sibling
scopes to lower starred displays. Reread the inbox before selecting the next
measured gap.

## 2026-10-26-pycomplete-148 — admit the attribute-first chained assignment slice

The measured `cell.x = m = n + 1` shape now lowers at ingestion to three
single-target assignments using the synthetic unspellable name
`<leanpy-chain-attr-temp>`: evaluate the RHS once, store the attribute, then
bind the plain name. This preserves CPython's left-to-right target order and
avoids evaluating an effectful RHS twice. The lowering is restricted to an
attribute first target followed only by plain names; other non-name-first
chains remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `cls_lab.chain_attr_first(5)` matches `6` in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,633 matched / 61 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,524 matched / 170 refused / 0 failed |
| Refusal census | 61 rows in 18 classes, 0 drifts; `cls_lab::chain_attr_first` removed from `assign.non-name-target` |
| Build/checks | `lake build leanmodels-run`, extractor/spec/tool checks, coverage freshness, backlog-index freshness, and `git diff --check` pass |

DECIDED: admit only attribute-first chains whose remaining targets are plain
names, using the unspellable temporary to preserve one RHS evaluation and
left-to-right stores. Keep subscript-first, tuple-first, dynamic, and all
other unsupported chain shapes loud. Reread the inbox before selecting the
next measured gap.

## 2026-10-26-pycomplete-147 — admit constant-key dictionary subscripts in tuple targets

Tuple unpacking now admits a dictionary subscript element when its receiver is
a local heap reference and its key is a literal constant, for example
`d[0], c.a = 1, k`. The right-hand side is unpacked first, then stores run
left to right through the existing `heapStore` path, so aliases observe the
same mutation order as CPython. Nonconstant keys, boundary lists, and other
non-name target shapes remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `cls_lab.unpack_subscript_elem(1)` matches `(1, 1)` in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,632 matched / 62 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,523 matched / 171 refused / 0 failed |
| Refusal census | 62 rows in 19 classes, 0 drifts; the constant-key tuple-subscript row removed |
| Build/checks | `lake build leanmodels-run`, extractor/spec/tool checks, coverage freshness, backlog-index freshness, and `git diff --check` pass |

DECIDED: admit only constant-key dictionary subscript elements whose receiver
is a local heap reference; retain loud behavior for dynamic keys, boundary
lists, unsupported receivers, and all other compound target shapes. Reread the
inbox before selecting the next measured gap.

## 2026-10-26-pycomplete-146 — admit the scalar append-before-return `finally` slice

The exceptions tier now lowers the measured shape whose try body returns a
named list, whose `except TypeError` fallback is an empty list, and whose
`finally` suite appends one scalar to that same list. The append runs before
the returned heap list is frozen, so `exc_handlers_lab.finally_clause()` now
matches CPython's `[19]` on both interpreter surfaces. General all-flow cleanup,
other finalizer effects, and effectful shapes without this measured handler
remain structured-but-loud.

| Measurement | Result |
|---|---|
| Focused differential | `exc_handlers_lab.finally_clause()` matches `[19]` in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,631 matched / 63 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,522 matched / 172 refused / 0 failed |
| Refusal census | 63 rows, 0 drifts; `exc_handlers_lab::finally_clause` removed from `exc.finally` |
| Extractor tests | 144 passed, including effectful-finally controls |
| Build/checks | `lake build leanmodels-run`, coverage freshness, backlog-index freshness, and `git diff --check` pass |

DECIDED: admit only the measured same-list scalar append before a returned
list; retain loud behavior for general all-flow finalization and every other
effectful `finally` shape. Reread the inbox before selecting the next measured
gap.

## 2026-10-26-pycomplete-145 — admit the straight-line unbound exception raise

The exception-name admission now accepts the narrow straight-line shape
`raise ValueError` followed by one direct assignment to `ValueError`. Function
entry installs the existing static-local marker, and both interpreters check it
before resolving locals or exception classes, producing CPython's exact
`UnboundLocalError`. Branch-local, repeated, constructor-form, and other
additional bindings remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `builtin_raise_lab.late_shadow()` matches `UnboundLocalError` in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,630 matched / 64 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,521 matched / 173 refused / 0 failed |
| Refusal census | 64 rows, 0 drifts; `builtin_raise_lab::late_shadow` removed from `exc.raise` |
| Extractor tests | 142 passed, including control-flow refusal cases |
| Build/checks | `lake build leanmodels-run`, coverage freshness, backlog-index freshness, and `git diff --check` pass |

DECIDED: admit only one direct assignment after a bare raise of the same name
in straight-line code; retain loud behavior for branches, repeated or
constructor-form shadows, and all other unbound-local shapes. Reread the inbox
before selecting the next measured gap.

## 2026-10-26-pycomplete-144 — expose the builtins fallback after deleting `__name__`

Script mode now models the runner-supplied module `__name__` as a deletable
binding. A single `del __name__` installs CPython's "builtins" fallback, so
the following read prints `builtins`; a repeated deletion raises the faithful
`NameError`. Other module dunders remain loud, and the static function and
monadic name-resolution paths share the same marker.

| Measurement | Result |
|---|---|
| Focused script differential | `del_dunder_script.py` matches CPython and prints `builtins`; repeated deletion reports `NameError: name '__name__' is not defined` |
| Script census | 6 loud rows in 5 classes, 0 drifts; the `del.definition-name` dunder row is removed |
| Build/checks | `lake build` for `Obs`, monadic specs, script modules, and `leanmodels-run`; coverage and backlog index freshness plus `git diff --check` pass |

DECIDED: model only the runner-supplied `__name__` deletion fallback; retain
loud behavior for every other module dunder and for unsupported deletion
shapes. Reread the inbox before selecting the next measured gap.

## 2026-10-26-pycomplete-143 — erase unobserved static-name deletions

The script surface now handles the two safe module-level deletion shapes that
were previously loud: `del f` after a top-level `def f` when no later
top-level or function-global read can observe the name, and `import time; del
time` when the imported name is likewise unobserved. The executor erases the
static table entry as a no-op, preserving CPython's successful exit and output;
observed definition/import deletions, dunder deletion, and partial multi-target
deletes remain loud or faithful as before.

| Measurement | Result |
|---|---|
| Focused script differential | `del_def_mid_script.py` and `del_import_script.py` MATCH; `del_dunder_script.py` remains loud |
| Script census | 7 loud rows in 6 classes, 0 drift after removing two `del.definition-name` rows |
| Proof/build | `lake build LeanModels.Python.Script LeanModels.Python.Monadic.Script` passed |
| Scope | Both pure and monadic script executors share the static-read observation guard |

DECIDED: erase only static definition/import deletions with no later observable
read; retain loud behavior for observed static names, dunders, and unsupported
compound or multi-target deletion cases.

## 2026-10-26-pycomplete-142 — admit ordered local exception shadows

`exc_lab.raise_shadowed` assigns `Stop = n` and immediately raises the local.
The previous static-locals guard rejected every non-parameter shadow even when
there was no unbound window. Ingestion now admits one direct assignment that
precedes every raise of that name; the existing runtime resolves the assigned
value, returning CPython's scalar `TypeError` and retaining loud behavior for
heap-backed values. Late or rebound assignments, including
`builtin_raise_lab.late_shadow`, remain refused.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab.raise_shadowed(1)` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,629 matched / 65 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,520 matched / 174 refused / 0 failed |
| Refusal census | 65 rows, 0 drift; `exc_lab::raise_shadowed` removed from `exc.raise` |
| Extractor tests | 141 passed, including ordered and late-shadow controls |
| Coverage page | Regenerated with the updated 3,629/3,520 measurements |

DECIDED: admit only a single direct assignment that textually precedes every
raise of a local exception name; retain loud behavior for unbound windows,
rebound names, heap-backed values, exception instances, chaining, and other
unsupported raise forms.

## 2026-10-26-pycomplete-141 — admit parameter-only exception-name shadows

`builtin_raise_lab.parameter_shadow` defines a parameter named
`ValueError` and raises it. CPython resolves the parameter local, so the
scalar input `1` raises `TypeError: exceptions must derive from
BaseException`; it is the same dynamic immediate-value path already used by
`raise n`. Ingestion now admits parameter-only shadows, while late or
additional local bindings keep their static-local refusal and heap-backed
values remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `builtin_raise_lab.parameter_shadow(1)` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,628 matched / 66 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,519 matched / 175 refused / 0 failed |
| Refusal census | 66 rows, 0 drift; `builtin_raise_lab::parameter_shadow` removed from `exc.raise` |
| Extractor tests | 140 passed, including parameter-only and rebinding controls |
| Coverage page | Regenerated with the updated 3,628/3,519 measurements |

DECIDED: admit only parameter-only exception-name shadows through the dynamic
scalar raise path; retain loud behavior for late or rebound locals,
heap-backed values, exception instances, chaining, and other unsupported
raise forms.

## 2026-10-26-pycomplete-140 — admit unknown exception constructor names

`rsa_inverse.inverse(4, 6)` reaches `raise NotRelativePrimeError(x, n,
divider)`, but the vendored module intentionally omits that package class.
CPython resolves the unknown callee before evaluating its arguments and raises
`NameError: name 'NotRelativePrimeError' is not defined`. Both interpreters
now preserve that lookup order and return the exact `NameError`; known but
unmodelled builtins, shadowed names, and admitted user classes with unsupported
payloads remain loud. The script fixture for a scalar shadow now records its
faithful `TypeError` as a match as well.

| Measurement | Result |
|---|---|
| Focused differential | `rsa_inverse.inverse(4, 6)` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,627 matched / 67 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,518 matched / 176 refused / 0 failed |
| Refusal census | 67 rows, 0 drift after removing `rsa_inverse::inverse` |
| Script census | 9 loud rows in 6 classes, 0 drift; the scalar shadow script now MATCHES |
| Proof surface | `Examples/python/rsa_inverse/spec.lean` now checks the concrete `NameError` |

DECIDED: admit only an unbound, non-builtin constructor-name lookup as a
faithful `NameError`; retain loud behavior for known unmodelled builtins,
shadowed names, unsupported user constructors, and dynamic exception values.

## 2026-10-26-pycomplete-138 — admit empty `OSError` raises

The builtin exception representation already carried an empty class identity
for `OSError`, and the handler table already matched it, but the direct-raise
admission intentionally stopped short of the name because no in-tier operation
produces an OS error. A bare `raise OSError` needs no OS payload, so it now uses
the existing `PyErr.builtinException` path. Payload-bearing and OS-derived
constructors remain loud, and `EnvironmentError` remains a handler-only alias.

| Measurement | Result |
|---|---|
| Focused differential | `builtin_raise_lab.unsupported_class` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,625 matched / 69 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,516 matched / 178 refused / 0 failed |
| Refusal census | 69 rows, 0 drift; `exc.raise` loses its direct `OSError` row |
| Proof surface | `#py_check builtin_raise_lab.unsupported_class()` checks the builtin identity |

DECIDED: admit only the payload-free `OSError` class identity; retain loud
behavior for `EnvironmentError` as a direct raise, OS-producing operations, and
all payload-bearing OS constructors.

## 2026-10-26-pycomplete-139 — admit scalar dynamic raises

`raise n` in `exc_lab.raise_value` was previously rejected by the extractor's
static-locals guard even when `n` was an ordinary function parameter. The
extractor now keeps that parameter-only shape executable, while builtin
exception names and any later or additional local binding remain guarded. Both
interpreters inspect the resolved local: immediate values raise CPython's
exact `TypeError: exceptions must derive from BaseException`; heap references
stay loud because their exception identity and payload are not represented.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab.raise_value(1)` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,626 matched / 68 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,517 matched / 177 refused / 0 failed |
| Refusal census | 68 rows, 0 drift; `exc.raise` loses the dynamic scalar row |
| Extractor tests | 139 passed, including parameter and rebinding controls |
| Proof surface | `LeanModels.Python.Obs` and `leanmodels-run` build successfully |

DECIDED: admit only parameter-only dynamic raises whose resolved value is an
immediate runtime value; retain loud behavior for heap-backed values,
exception-class shadows, local rebinding, and non-name raise expressions.

## 2026-10-26-pycomplete-137 — make function-scope `del` errors faithful

The remaining four `del.name-set-census` rows were the same missing semantic:
the extractor refused any read after a delete and the runtime refused every
delete miss instead of producing CPython's `UnboundLocalError`. Function
frames now mark every bare-name delete as a static local at entry. Reads after
straight-line, branch, or loop deletes see that marker; a later assignment
shadows it. The delete arm raises the same error for a module-global target,
a never-bound name, and a second delete, retaining earlier left-to-right
deletions.

| Measurement | Result |
|---|---|
| Focused differential | `del_lab.read_after`, `del_global`, `del_never`, and `double_del` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,624 matched / 70 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,515 matched / 179 refused / 0 failed |
| Refusal census | 70 rows, 0 drift; `del.name-set-census` removed |
| Extractor tests | 137 passed, with branch/loop/read-after-delete controls updated |
| Formatting | `git diff --check` passed |

DECIDED: use the static-local marker and faithful `UnboundLocalError` for all
bare-name function deletes; retain existing loud boundaries for unsupported
delete targets and module-scope static bindings.

## 2026-10-26-pycomplete-136 — admit the safe generator yield-under-try slice

The remaining `exc.handler` census row was `drive_yield_under_try`: its
generator contained only `try: yield n` with `except Stop: pass`. A general
yield under `try` needs a suspended try frame so that an exception raised while
resuming can reach the handler. The current generator continuation has no such
frame, and generator `throw` is outside the tier. Ingestion therefore lowers
only the measured safe form when the yield is a scalar literal or a direct
function parameter; those expressions cannot raise, so the handler has no
observable work on the admitted surface. A yield expression with a call or
other potentially raising operation, a different handler, or any additional
suite statement remains structured-but-loud.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab.drive_yield_under_try(1)` MATCH in native and proof interpreters |
| Full executable differential | 3,694 cases: 3,620 matched / 74 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,511 matched / 183 refused / 0 failed |
| Refusal census | 74 rows, 0 drift; `exc.handler` retains only shadow/rebinding and clock-boundary rows |
| Extractor tests | 137 passed, including safe and unsafe yield-under-try controls |
| Formatting | `git diff --check` passed |

DECIDED: admit only the non-raising scalar-literal/parameter yield under
`except Stop: pass`; retain the general suspendable try frame as a future
generator-runtime item.

## 2026-10-26-pycomplete-135 — measured two-handler exception clauses

The extractor now lowers a narrow two-handler form to nested existing `Try`
nodes: both clauses use plain exception names, have no `as` binding, and return
one scalar literal. Nesting preserves source order and lets a nonmatching
exception reach the next clause; because the handler bodies cannot raise, a
handler exception cannot be mistaken for a sibling clause. Wider multiple
handler suites remain structured-but-loud. The `exc_lab.multi_handler` and
`exc_handlers_lab.multiple_handlers` witnesses now match on both interpreters,
and their specs use `#py_check`.

| Measurement | Result |
|---|---|
| Focused differential | 2 native matches / 2 proof matches / 0 failures |
| Full executable differential | 3,694 cases: 3,619 matched / 75 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,510 matched / 184 refused / 0 failed |
| Refusal census | 75 rows, 0 drift |
| Extractor tests | 135 passed |
| Generated/check gates | coverage page, backlog index, JSON validation, and `git diff --check` passed |

DECIDED: admit only the measured constant-return two-handler slice; retain
handler bodies with effects or possible exceptions, larger handler lists, and
dynamic/tuple class expressions as loud boundaries.

## 2026-10-26-pycomplete-134 — heap-dict percent-format mappings

The monadic string percent-formatting arm now threads the current heap for a
dict RHS. Literal string keys in `%(key)s` are found through the existing
insertion-order dict representation and scalar conversions reuse the admitted
format conversion worker. Missing keys retain `KeyError`, while
rich mapping syntax and unsupported conversions remain loud. A dict RHS also
suppresses CPython's leftover-argument error, so `'abc' % {'k': 1}` returns
`'abc'`. The proof interpreter remains intentionally narrower for heap-dict
formatting.

| Measurement | Result |
|---|---|
| Focused executable witnesses | `fmt_mapping()` → `'1'`; `fmt_dict_leftover()` → `'abc'` |
| Full executable differential | 3,694 cases: 3,617 matched / 77 refused / 0 failed |
| Full proof differential | 3,694 cases: 3,508 matched / 186 refused / 0 failed |
| Refusal census | 77 rows, 0 drift |
| Grammar census | 145 witnesses: 136 MATCH / 9 REFUSE |
| Generated/check gates | coverage page, backlog index, and `git diff --check` passed |

DECIDED: admit literal string-key heap-dict mappings and CPython's guarded
leftover rule; retain rich mapping mini-language and non-scalar conversion
forms as loud boundaries.

## 2026-10-25-pycomplete-112 — observed value-less annotated locals

Function-local `x: T` declarations now preserve CPython's static-local
boundary. The extractor retains a marker when a load or delete can observe the
declaration, and the runtime hoists it to frame entry so skipped branches still
localise the name. Reads before assignment raise the exact
`UnboundLocalError: local variable 'x' referenced before assignment`; later
assignments shadow the marker. The no-read form remains an erased no-op, and
walrus targets use the same marker path. The proof interpreter's world
invariant covers the locals-only marker update and the exception path.

`ann_lab.ann_novalue_read` and `ann_lab.ann_novalue_shadows_global` moved from
recorded refusals to differential MATCH rows. The harness now compares the
exception subclass directly instead of normalizing `UnboundLocalError` to
`NameError`.

| Measurement | Result |
|---|---|
| Extractor tests | 128 passed |
| Differential suite | 3693 cases: 0 failed, 98 whitelisted, 3595 matched |
| Focused executable witnesses | `ann_novalue_read` and `ann_novalue_shadows_global` MATCH with class and message |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: admit observed function-local value-less annotations and exact
`UnboundLocalError`; retain loud failure for module/class value-less forms and
other unmodeled annotation effects.

## 2026-10-25-pycomplete-111 — direct builtin-exception subclass inheritance

The exception class slice now admits one direct subclass of a measured builtin
exception, such as `class ValueSignal(ValueError): pass`. Ingestion records the
ancestor, checks that its builtin name is not rebound anywhere in the module,
and marks the class as an exception only after that census succeeds. Handler
matching uses the explicit measured ancestor table: `BaseException` and
`Exception` catch the subclass, while the arithmetic, lookup, runtime, and
exact-name entries retain their pinned CPython relationships. Shadowed,
forward, dynamic, and unmeasured exception bases remain loud.

`exc_ancestors_lab.value_ancestor` raises the subclass and catches it through
`except ValueError`; the generated envelope and `#py_check` pin the class
identity path, and the differential suite adds the same row.

| Measurement | Result |
|---|---|
| Extractor tests | 128 passed |
| Focused executable witness | `value_ancestor()` → `1`; `graphlib.py` runs without the class wall |
| Differential suite | 3693 cases: 0 failed, 100 whitelisted, 3593 matched |
| Class census | 21 fixtures + graphlib/opcode/bisect: 0 failures; 0 ground-truth violations |
| Lean build | `lake build leanmodels-run` passed |

DECIDED: admit only the measured direct builtin-exception ancestor names and
their explicit handler subsumption table; retain loud failure for exception
MROs, rebinding, and exception classes outside that table.

## 2026-10-24-pycomplete-110 — built-in `object` class base

The class tier now admits `class C(object)` as the default-protocol class it
is semantically equivalent to. Ingestion clears the raw base marker only for
the built-in name, preserving conservative creation-effect provenance in the
envelope while allowing the script to execute. External, dynamic, and other
built-in-type bases remain loud.

The class census controls now treat both `object` and an earlier same-module
base as creation-pure admissions.

| Measurement | Result |
|---|---|
| Extractor tests | 127 passed |
| Class census controls | 20 fixtures + graphlib/opcode/bisect: 0 failures |
| Focused acceptance | `cls_lab.object_base_truthy` matches CPython |

DECIDED: admit only the built-in `object` base; retain loud failure for all
other external and dynamic bases.

## 2026-10-24-pycomplete-109 — class census inheritance control

The class census now follows ingestion's source-order rule for the new
inheritance slice. The extractor records every base expression as a creation
effect because it has no module context; the census and ingestion clear that
effect only for a single plain-name base whose earlier same-module class is
admitted. The controls now cover object, external exception, forward, and
same-module bases without treating the last one as a creation wall.

| Measurement | Result |
|---|---|
| Extractor tests | 126 passed |
| Class census controls | 20 fixtures + graphlib/opcode/bisect: 0 failures |
| Lean validation | `LeanModels.Python.Json` built |
| Generated checks | envelope regenerated and `git diff --check` passed |

DECIDED: keep creation-effect provenance conservative in raw envelopes and
make the context-sensitive admission explicit in ingestion and census tools.

## 2026-10-24-pycomplete-108 — simple same-module class inheritance

The class tier now admits one plain-name base whose class definition ends
earlier in the same module. `ClassDefn.base` records the link after ingestion
checks source order and the base's own ordinary class admission. Attribute
dispatch and construction resolve inherited methods and `__init__` through the
single link, while inherited dunders remain part of the default-protocol guard.
Multiple, dynamic, forward, external, namedtuple, and exception bases stay
loud because their creation and MRO behavior is outside this slice.

The `cls_lab.sub_inherits` witness now constructs `Sub(Cell)` and calls the
inherited initializer and method.

| Measurement | Result |
|---|---|
| Extractor tests | 126 passed |
| Grammar census | 145 witnesses: 136 MATCH / 9 REFUSE, 0 drift |
| Differential suite | 3,691 rows: 3,591 matched, 100 whitelisted, 0 failed |
| Focused Lean sources | `Ast`, `Json`, `Semantics`, `Obs`, `Monadic.Eval`, and `leanmodels-run` built |

DECIDED: admit only a single earlier same-module base; retain loud failure for
all other inheritance shapes until class creation and MRO semantics are modeled.

## 2026-10-24-pycomplete-105 — direct complex-literal printing

The `const.complex` grammar witness now matches for the exact source shape
`print(1j)`. The extractor's existing loud `Constant:complex` node is
recognized only after builtin name resolution selects the ordinary `print`
call, where CPython's `str(1j)` is the exact string `1j`. This keeps shadowed
`print`, assignments, comparisons, arithmetic, containers, and every other
complex spelling loud: no complex runtime or boundary value is fabricated.

| Measurement | Result |
|---|---|
| Focused executable witness | `print(1j)` → `1j`, exit 0 |
| Grammar census | 145 witnesses: 134 MATCH / 11 REFUSE, 0 drift |
| Focused build | `lake build LeanModels.Python.Obs` passed |
| Generated checks | coverage page and `git diff --check` pass |

DECIDED: admit only the direct `print(1j)` observation; retain the complex
value representation boundary until a complete complex runtime type and
operator table can be specified.

## 2026-10-24-pycomplete-106 — direct scalar `global` declarations

Function bodies may now declare a scalar module global and then read, assign,
or augment it. The call frame carries declaration markers and the current
global values; writes thread through `World.globals`, and script publication
reflects them in the module frame. Compound targets and heap-valued global
operations remain loud.

| Measurement | Result |
|---|---|
| Focused executable witness | `g = 1; global g; g = 2; g += 3` → `5` |
| Focused read witness | function global read → `7` |
| Regression witness | ordinary local binding still prints `2` then `7` |
| Grammar census row | `stmt.Global` MATCH |

DECIDED: admit direct scalar global scope effects on the Monadic/script
surface; retain loud refusal for compound global targets and unsupported scope
forms.

## 2026-10-24-pycomplete-107 — direct scalar `nonlocal` declarations

Nested functions may now declare a scalar `nonlocal` name and update the
shared closure cell. Extraction treats those names as cell captures,
`cellsFor` preserves the cell directory alongside the ordinary binding, and
the Monadic evaluator reads and writes the heap cell so both frames observe
the same value. Compound targets and deeper unsupported scopes remain loud.

| Measurement | Result |
|---|---|
| Focused write witness | CPython and leanpy both print `2` |
| Focused read witness | CPython and leanpy both print `4` |
| Augmented write witness | CPython and leanpy both print `9` |
| Closed-function differential | 3691 cases: 0 failed, 101 whitelisted, 3590 matched |
| Grammar census | 145 witnesses: 136 MATCH / 9 REFUSE, 0 drift |

DECIDED: admit direct scalar nonlocal cell reads, assignments, and augmented
assignments; retain loud refusal for compound targets and deeper scope forms.

## 2026-10-24-pycomplete-104 — alias-free boundary-list augmented repetition

The measured boundary-list `*=` gap now has a small ingestion-safe slice.
When a function consists of a parameter augmented by `count` and immediately
returns that same parameter (`x *= count; return x`), ingestion lowers the
statement to `x = x * count`. The existing pure `listValueRepeat` worker then
preserves CPython's count conversion, overflow, nonpositive short-circuit,
materialization bound, and non-integral `TypeError` for `Val.list` arguments.
The shape has no second binding or control-flow path that could observe the
old list, so the lowering does not erase an alias. Alias-bearing and other
augmented list mutations remain loud until the H2 heap-threading boundary is
wired.

The `string_repeat.repeat_aug` battery now covers boundary-list positive,
nonpositive, and non-integral counts on both interpreter surfaces; the existing
heap-list alias witness remains unchanged.

| Measurement | Result |
|---|---|
| Focused Lean build | `Examples.python.string_repeat.spec` passes |
| Focused executable differential | 62 MATCH / 0 failed |
| Focused proof differential | 62 MATCH / 0 refused / 0 failed |
| Generated/docs checks | `docs_check.py`, coverage freshness, backlog index freshness, JSON validation, and `git diff --check` pass |

## 2026-10-24-pycomplete-103 — boundary-list repetition

The pure value surface now admits ordinary `list * int` and `int * list` for
boundary `Val.list` snapshots. `listValueRepeat` preserves CPython's
index-sized overflow, nonpositive and empty short-circuits, non-integral
`TypeError`s, and the fixed materialization bound. The direct `len(list *
count)` shape uses the same length-only worker, so a large positive result can
be observed without constructing it. Heap-backed lists still use the monadic
allocation path, and augmented assignment keeps its alias-sensitive heap
boundary.

The acceptance battery adds both operand orders and the large length-only case
to `string_repeat`; the existing heap-list `*=` witness remains the stateful
distinction.

| Measurement | Result |
|---|---|
| Focused Lean build | `Examples.python.string_repeat.spec` passes |
| Focused executable differential | 3 rows: 3 MATCH / 0 failed |
| Focused proof differential | 3 rows: 3 MATCH / 0 refused / 0 failed |
| Full executable differential | 3,689 rows: 3,586 matched, 103 whitelisted, 0 failed |
| Full proof differential | 3,689 rows: 3,476 matched, 213 refused, 0 failed |
| Extractor tests | 125 passed |
| Generated checks | coverage page, backlog index, JSON validation, and `git diff --check` passed |

## 2026-10-24-pycomplete-101 — `try … else`

`try … except … else` now runs its `else` suite after the protected body
completes normally. The extractor lowers the shape to a fresh success flag,
the existing retained-state `try` node with a final flag assignment, and an
ordinary `if`; returns, breaks, continues, unmatched exceptions, and handled
exceptions therefore skip the `else` suite exactly as CPython does. The flag
name is deterministic and fresh across the source envelope, while `finally`,
multiple handlers, tuple patterns, and observed exception bindings remain
loud.

The two existing acceptance rows (`exc_lab.else_clause` and
`exc_handlers_lab.else_clause`) now match on the executable and proof
surfaces, with extractor coverage for the lowering and no interpreter changes.

| Measurement | Result |
|---|---|
| Extractor tests | 125 passed |
| Full executable differential | 3,680 rows: 3,564 matched, 116 whitelisted, 0 failed |
| Full proof differential | 3,680 rows: 3,454 matched, 226 refused, 0 failed |
| Grammar census | 145 witnesses: 133 MATCH / 12 REFUSE, 0 drift |
| Whitelist census | 116 rows in 33 classes; 0 drift |
| Generated checks | coverage page, docs, JSON validation, and `git diff --check` passed |

DECIDED: admit the single-handler `try … else` shape through ingestion
lowering; retain `finally` and the other unrepresented handler protocols as
loud boundaries.

## 2026-10-24-pycomplete-102 — length-only sequence repetition

`len(sequence * count)` now returns CPython's length for strings, bytes,
tuples, and namedtuples without materializing a result that exceeds the
`seqBudget` bound. Ingestion lowers both direct expressions and the admitted
temporary `result = sequence * count; return len(result)` (including immutable
`*=`) to `<lenmult>`, which preserves left-to-right operand evaluation,
index-sized count overflow, nonpositive and empty short-circuits, and the
ordinary non-integer sequence errors. Heap-backed list repetition continues to
use its stateful allocation path.

The proof surface has the same pure length worker and symbolic tuple/string
proofs; the synthetic operation is conservatively outside `Expr.heapFree`
because its fallback can still reach heap-backed repetition. Thirteen
differential rows moved from recorded refusals to MATCH, with no new
divergences.

| Measurement | Result |
|---|---|
| Focused Lean proofs | `string_repeat.proof` and `tuple_repeat.proof` build |
| Full executable differential | 3,682 rows: 3,579 matched, 103 whitelisted, 0 failed |
| Full proof differential | 3,682 rows: 3,469 matched, 213 refused, 0 failed |
| Grammar census | 145 witnesses: 133 MATCH / 12 REFUSE, 0 drift |
| Generated checks | coverage page, backlog index, JSON validation, and `git diff --check` passed |

## 2026-10-24-pycomplete-97 — dictionary key-view intersection

Dictionary key views now support the measured set-like `&` operation with
heap-backed sets and with other key views. The worker reads both operands
through the existing dictionary-key equality relation, allocates a fresh
`Obj.pyset`, and leaves the retained hash order unobservable. `sorted` now
consumes heap sets, so the canonical witness
`sorted({2: "b", 1: "a"}.keys() & {1, 9})` returns `[1]`; union, difference,
symmetric difference, item-view algebra, values-view operations, and set
iteration remain loud.

The expression is conservatively outside `Expr.heapFree`, and the monadic
worker threads the new heap through `binOpHM`; the existing fuel, world, and
clock proof walkers remain generic over the operator. The dict and set
acceptance examples, the executable differential case, and the grammar
census now cover the live boundary; the proof interpreter retains its
intentional refusal for dictionary-view allocation.

| Measurement | Result |
|---|---|
| Focused runner | `tools/leanpy` prints `[1]` and exits 0 |
| Full executable differential | 3,677 cases: 3,556 matched, 121 whitelisted, 0 failed |
| Full proof differential | 3,677 cases: 3,450 matched, 227 refused, 0 failed |
| Grammar census | 132 MATCH / 12 REFUSE; 0 drifts |
| Script census | 12 loud rows; 0 drifts |
| Generated/check gates | coverage page, JSON validation, and `git diff --check` passed |

DECIDED: admit only key-view/set intersection and deterministic `sorted(set)`;
retain the remaining hash-order-sensitive set and view protocols as loud
boundaries.

## 2026-10-24-pycomplete-98 — attribute deletion

The measured single-target `del o.attr` shape now follows the existing
synthetic-call route used by `del o[k]`: extraction emits `DeleteAttribute`,
ingestion lowers it to `<attrdel>(receiver, "attr")`, and the monadic
interpreter removes an existing attribute from an admitted instance in place.
Alias reads observe the deletion's heap mutation; missing attributes and
immediate/builtin receivers reproduce CPython's `AttributeError`, while
function-object and other unsupported protocols remain loud. The proof
interpreter deliberately keeps this stateful operation loud.

The `del_lab` battery covers scalar failure, successful instance deletion,
alias visibility, and missing attributes. The attribute grammar witness and
extractor test pin the new admission; slices and mixed-target deletes remain
unsupported.

DECIDED: admit only ordinary instance attribute deletion; retain slots,
function-object, and other protocol-specific deletion behavior at their
existing loud boundaries.

## 2026-10-24-pycomplete-92 — binary float NaN arithmetic

Binary `+`, `-`, and `*` now propagate NaN payloads and signs through the
kernel-reducible float model. An input NaN is quieted by setting its quiet bit;
when both operands are NaN, CPython's left-to-right result keeps the left
operand. Invalid `inf - inf`, opposite-sign `inf + inf`, and `inf * 0` return
the pinned CPython 3.9 canonical negative quiet-NaN word. Division and
floor/mod/divmod NaN results remain loud because their payload behavior is a
separate boundary.

The `float_lab` arithmetic rows and script now match, with direct Float64
guards for payload preservation, left-operand selection, and each invalid
infinity combination. Mixed integer conversion overflow still wins before NaN
classification, and finite cancellation remains proved symbolically.

## 2026-10-24-pycomplete-93 — float NaN floor/mod/divmod

Float floor division, modulo, and `divmod` now propagate NaN payloads and
signs. Zero denominators retain CPython's distinct `ZeroDivisionError` messages
and win before NaN classification; otherwise the left NaN wins, then the right
NaN, and each result is quieted in place. An infinite left operand with a
non-NaN divisor uses the pinned canonical negative quiet-NaN word.

The `float_lab.floor_pair` rows and `nan_floor_script.py` now match, with
direct Float64 guards for both operand positions and the invalid-infinity case,
and a kernel proof covering the three returned values. True division remains
the separate unresolved NaN-payload boundary.

## 2026-10-24-pycomplete-94 — float NaN true division

Float true division now propagates NaN payloads and signs. Zero denominators
and mixed integer conversion overflow retain their CPython ordering; otherwise
the left NaN wins, the right NaN is used when needed, and each is quieted in
place. The indeterminate `inf / inf` case uses the pinned canonical negative
quiet-NaN word.

The `float_lab.divide` NaN rows, `indeterminate_division_still_loud`, and
`nan_division_script.py` now match, with direct Float64 guards and kernel
proofs for both operand positions, the invalid infinity case, and denominator
priority.

## 2026-10-24-pycomplete-95 — non-finite `itertools.count`

`itertools.count` now admits binary64 NaN and infinity start/step values.
Its first value is preserved exactly, and subsequent values use the shared
float arithmetic so signaling NaNs quiet on the first addition while infinity
remains stable. The finite integer, Boolean, and mixed stepping behavior is
unchanged.

The non-finite `count_head` rows and `count_nonfinite_script.py` now match on
both interpreter surfaces; the refusal census no longer records the stale
`iter.count-numeric-frame` boundary.

## 2026-10-24-pycomplete-96 — malformed Unicode `int(str)`

Malformed non-decimal Unicode text such as `int("é")` now follows the
existing repr-rendered `ValueError` worker, matching CPython's exact class and
message. Unicode decimal digits and whitespace keep their normalization path;
the fixed 4300-digit budget and unrenderable-character loud boundary remain.

## 2026-10-24-pycomplete-86 — zero-argument builtin exception constructor

The extractor's existing zero-argument raise-constructor lowering is now
applied to the stale `exc_ancestors_lab` envelope. `raise BaseException()`
therefore follows the admitted class-identity raise path and is caught by
`except BaseException`; payload-bearing and other constructor forms remain
loud.

## 2026-10-24-pycomplete-85 — percent formatting of ref-free containers

Bare `%s` and `%r` conversions now render tuple, namedtuple, range, and
boundary-list operands through a pure value-only renderer. Heap references and
mapping-key formatting remain loud because they require heap lookup.

## 2026-10-24-pycomplete-84 — decimal rendering limit error

Integer decimal rendering beyond the pinned 4300-digit CPython limit now
raises the exact `ValueError` and message instead of becoming a loud tier
refusal. The error propagates through scalar, percent-format, f-string,
container, range, namedtuple, and script rendering; the fixed bound remains
unchanged.

## 2026-10-24-pycomplete-83 — huge left-shift overflow

Left-shift counts at the conservative measured overflow guard now raise
CPython's exact `OverflowError: too many digits in integer` instead of reaching
the former kernel panic. Ordinary over-budget shifts remain loud under the
fixed shift budget.

## 2026-10-24-pycomplete-82 — user exception string payloads

An admitted `class Stop(Exception): pass` may now be raised with one
positional string argument, preserving CPython's exception message on both
runner boundaries. Non-string, keyword, and multi-argument user constructors
remain loud.

## 2026-10-24-pycomplete-81 — string repetition index overflow

String repetition counts beyond the pinned CPython index-sized range now raise
the exact `OverflowError`, including empty strings and nonpositive counts.
Positive in-range results that exceed the tier's materialization budget remain
loud.

## 2026-10-24-pycomplete-80 — same-dictionary key-view equality

Two escaped `dict_keys` views over the same dictionary now compare equal,
matching CPython's set-like key-view equality for the measured shape. Values
views, item-view set algebra, and cross-dictionary cases remain loud.

## 2026-10-24-pycomplete-79 — dictionary-view rendering

Escaped `dict_keys`, `dict_values`, and `dict_items` views now render with
CPython's exact type-specific `repr`, including their live element contents and
the existing active-path and depth safeguards. View set algebra and other
unmodeled protocols remain loud.

## 2026-10-24-pycomplete-78 — dictionary-view subscript errors

Subscripting an escaped `dict_keys`, `dict_values`, or `dict_items` view now
raises CPython's exact type-specific `TypeError` instead of an internal loud
refusal. View indexing remains unsupported as a value operation; the modeled
surface is the faithful non-subscriptable error.

## 2026-10-24-pycomplete-77 — heap-list attribute augmented assignment

Heap-list-valued attribute `+=` now evaluates the right-hand side and extends
the receiver's existing heap address in place. Deterministic list, tuple,
string, bytes, and range operands are admitted; stateful iterators and
hash-order containers remain loud. `cls_lab.aug_attr_list` observes the
in-place length and matches CPython on both interpreter surfaces.

## 2026-10-24-pycomplete-76 — non-simple annotated targets

Annotated assignments with `simple == 0` targets now lower to the annotation
evaluation followed by the existing assignment path. This preserves CPython's
order and correctly omits the `__annotations__` table entry for attribute and
subscript targets. The acceptance row `ann_lab.ann_attr_target` moved to
MATCH; class annotations, explicit annotation-table bindings, and observed
value-less declarations remain loud.

## 2026-10-23-pycomplete-55 — integer modular `pow`

The next measured frontier after the decimal-rendering budget was the
three-argument `pow` builtin. Its single curated refusal was a pure integer
operation, unlike the larger list-repetition and exception-handler walls.
The tier now admits integer bases, nonnegative exponents, and positive
moduli, computes Python's nonnegative remainder, and preserves the exact
zero-modulus `ValueError`. Negative exponents use bounded modular inverses
and preserve the exact non-invertible-base `ValueError`; negative moduli and
non-integral arguments remain loud until those protocols are modeled.

The change uses one `powModArgs` worker in both interpreters, with the same
payload-blind, clock-erased, and fuel-monotone pure-worker treatment as the
existing two-argument `pow` path. `arith` proves positive, negative-base,
zero-modulus, and invertible and non-invertible negative-exponent cases.

## 2026-10-23-pycomplete-56 — `float.is_integer()`

The scalar `float.is_integer()` method now returns the exact CPython boolean
for finite binary64 values, including signed zero and large integral values;
NaN and infinities return `False`, and nonzero argument counts retain the
faithful positional-only `TypeError`. The trunk and monadic evaluators and
their fuel/world proof walkers cover the pure method call.

## 2026-10-23-pycomplete-57 — heap-backed list repetition

The monadic interpreter now handles `list * int` and `int * list` by reading
the source heap list and allocating a fresh repeated list. Zero and negative
counts still allocate fresh empty lists, oversized index counts preserve
CPython's `OverflowError`, and materializations beyond `seqBudget` remain
loud. The trunk proof interpreter retains its declared refusal because its
boundary list representation cannot state the heap allocation and aliasing.

## 2026-10-23-pycomplete-58 — Unicode decimal `int(str)`

The `int(str)` decimal parser now reuses the existing CPython Unicode decimal
digit and whitespace normalization table from the float-text parser. Arabic
and fullwidth decimal digits, and Unicode spaces around a value, map into the
same bounded ASCII grammar; unrelated non-decimal characters remain loud.
The interpreters preserve exact malformed-input errors and the fixed digit
budget.

## 2026-10-23-pycomplete-59 — ASCII `float(bytes)`

The float constructor now feeds ASCII bytes through the existing Unicode-aware
decimal text parser. Finite values, decimal underscores, whitespace, signed
zero, overflow, and malformed-input `ValueError` rendering share the string
constructor's semantics while naming the original bytes value in errors.
Non-ASCII bytes and NaN payload spellings remain loud until decoding and NaN
oracle behavior are modeled; canonical `nan`/`-NaN`/`+nAn` forms now preserve
CPython's quiet-NaN word and sign bit.

## 2026-10-23-pycomplete-60 — invalid high-octet `int(bytes)`

`int(bytes)` now classifies non-ASCII octets as malformed input and raises
CPython's exact bytes-rendered `ValueError`, including for explicit bases.
The parser still admits only the ASCII numeric grammar; byte decoding,
iterators, methods, and percent formatting remain separate loud boundaries.

## 2026-10-23-pycomplete-61 — canonical textual NaN construction

`float("nan")`, `float("-NaN")`, and case-insensitive sign variants now return
CPython's canonical quiet-NaN binary64 word with the explicit sign bit. The
same forms work for ASCII bytes. Payload spellings such as `nan(1)`, invalid
Unicode rendering, and NaN arithmetic payload/sign propagation remain loud.

## 2026-10-23-pycomplete-62 — finite numeric `itertools.count`

The monadic runner now carries `itertools.count`'s immediate numeric state as
`RVal`, admitting finite integers, Booleans, and binary64 floats for the start
and step. Each `next` returns the current value and advances through the
shared numeric addition worker, preserving CPython's first-value subtype (for
example, `count(True, 2)` yields `True, 3, 5`; a mixed integer/float counter
rounds as ordinary binary64 addition). NaN and infinity starts or steps remain
loud because their propagation needs an explicit floating-point oracle. Both
interpreter surfaces use the value frame for the finite rows. `float_lab` and
the differential battery cover finite mixed counters,
Boolean starts, faithful invalid-argument errors, and the NaN refusal.

## 2026-10-24-pycomplete-87 — Unicode string repr rendering

String `repr` now uses CPython 3.9's Unicode 13.0 printability table. Printable
code points such as `λ` and `😀` render directly, while controls, separators,
unassigned, and private-use code points use exact `\\uNNNN` or `\\UNNNNNNNN`
escapes. The same renderer now covers `%r`, f-string repr conversion, and
nested tuple/list/dict/namedtuple rendering. The focused differential battery
promotes scalar, container, and script rows, including the `λ😀` and zero-width
format-character cases.

## 2026-10-24-pycomplete-88 — unused exception bindings

An `except Class as name` binding is now admitted when the handler never reads
the bound exception object. The model erases the temporary binding, preserving
the handler's retained state and CPython's observable control flow; reads of
the exception value, including payload and attribute inspection, remain loud.

## 2026-10-24-pycomplete-89 — builtin terminal exception identities

`SystemExit`, `KeyboardInterrupt`, and `GeneratorExit` now use the builtin
class-identity exception path and are caught by `BaseException`, while staying
outside `Exception` as in CPython. Uncaught process-exit behavior remains
outside the function boundary.

## 2026-10-24-pycomplete-90 — OS-error handler aliases

`OSError` and its `EnvironmentError` alias are now admitted handler names.
Because the tier has no OS-error-producing operation, represented errors such
as `ZeroDivisionError` propagate through these handlers; direct OS raises and
future OS effects must still provide their own measured representation.

## 2026-10-24-pycomplete-91 — bare exception handlers

A single bare `except:` now catches every represented exception from the
retained frame state. Multiple handlers, tuple patterns, and observed `as`
bindings remain outside the tier.

## 2026-10-23-pycomplete-65 — pinned decimal rendering budget

The shared integer conversion budget is now pinned to CPython 3.9's default
`sys.get_int_max_str_digits()` boundary: scalar decimal rendering and explicit
base parsing admit values with at most 4300 digits, while 4301-digit values
refuse before conversion. The same boundary is used by `str`, `print`, f-strings,
percent formatting, `repr`, ranges, tuples, lists, dicts, namedtuples, and the
ASCII `int(str)`/`int(bytes)` parsers. This keeps the tier deterministic while
covering the oracle's ordinary default; processes configured below or above
4300 remain outside the pinned model.

## 2026-10-23-pycomplete-66 — heap-list augmented repetition

Heap-backed list `*=` is now live on the executable monadic surface. The
existing list address is updated in place, so aliases observe the repeated
contents and zero or negative counts clear that same object. Integer and
Boolean counts retain the pinned index-sized and `seqBudget` bounds, while
non-integral counts preserve CPython's `TypeError`; the proof interpreter
remains loud because its boundary list snapshot cannot express this mutation.

## 2026-10-23-pycomplete-67 — scalar attribute errors become faithful

Immediate scalar attribute reads now raise the same payload-free
`AttributeError` as CPython. The method-call path follows the same rule, so a
shadowed scalar such as the local integer in `clock_lab.shadowed` fails during
attribute lookup without consuming the trace or evaluating call arguments.
The two frontier rows (`cls_lab.attr_on_int` and `clock_lab.shadowed`) now
match on both interpreter surfaces; heap-receiver dispatch and admitted scalar
methods are unchanged.


## 2026-10-23-pycomplete-68 — pair sequences for `dict()`

The `dict()` constructor now consumes immediate and heap-backed list, tuple,
bytes, string, and namedtuple pair sequences. Each element is checked for
length two and each key for hashability before insertion, retaining CPython's
ordered duplicate-key behavior. The executable and proof interpreters agree
on the bytes frontier row `len(dict(b"")) == 0`; generators and dictionary
views keep their existing dedicated paths and unsupported cases remain loud.


## 2026-10-23-pycomplete-69 — bytes iterator cursor

The executable monadic interpreter now models `iter(bytes)` with an immutable
cursor frame. `next()` yields integer octets one at a time and exhausted
cursors follow the existing `StopIteration` behavior. The proof interpreter
keeps this stateful cursor loud because its value-side generator representation
is intentionally narrower; other bytes protocol methods remain refused.


## 2026-10-23-pycomplete-70 — bare bytes `%s` formatting

The binary modulo path now admits the measured `b"%s" % bytes` form, copying
its bytes operand exactly on both interpreter surfaces. Other bytes format
strings, conversions, and operand protocols remain loud until their CPython
grammar and buffer rules are represented.

## 2026-10-23-pycomplete-71 — trace-clock arity errors

The admitted `time.time()` trace-clock call now handles positional
arguments with CPython's evaluation order and exact `TypeError` payload:
`time.time() takes no arguments (N given)`. The arguments are evaluated
before the error and the clock trace is left untouched. Keyword syntax and
other clock-module surfaces remain loud at their existing boundaries.

## 2026-10-23-pycomplete-72 — extend the fixed rendering depth

The caller-independent `reprFuel` budget rises from 128 to 256 levels.
`repr_lab.deep(129)` now matches CPython on both interpreter surfaces, while
cycles, decimal magnitude limits, and deeper structures retain their existing
active-path and loud-failure boundaries.

DECIDED: spend a larger fixed rendering budget for ordinary nested containers
without making rendering depend on caller fuel.

## 2026-10-23-pycomplete-73 — bare decimal `format` specification

The first non-empty builtin `format` specification is now admitted for
integers and Booleans: `format(value, "d")` reuses the fixed decimal renderer
and preserves its digit budget. Flags, widths, other conversion codes, and
custom `__format__` protocols remain loud until the complete mini-language is
modeled.

## 2026-10-23-pycomplete-75 — f-string ASCII conversion

F-string `!a` fields now lower to a distinct intrinsic AST constructor and use
`asciiValH` on both interpreter surfaces. ASCII escaping, including the
existing Unicode escape table, is shared with the `ascii()` builtin; non-empty
format specifications and custom protocols remain loud.

## 2026-10-23-pycomplete-74 — mixed scalar ordering errors

The shared ordering worker now returns CPython's exact `TypeError` for mixed
immediate scalar pairs such as `sorted([1, "s"])`, preserving the operand order
in the message. Heap receivers and unsupported comparison protocols remain
loud. The `drain_lab.sorted_mixed` row is now a concrete match.

## 2026-10-23-pycomplete-63 — Latin-1 string case mapping

String `swapcase`, `isupper`, `islower`, and `upper` now admit CPython's
Latin-1 case table, including the micro sign, sharp-s expansion to `SS`, and
the `ÿ`/`Ÿ` mapping. Characters outside Latin-1 remain loud because their
full Unicode case tables are not yet represented. The focused `str_lab`
battery covers accented strings and the multi-character mappings on both
interpreter surfaces.

## 2026-10-22-pycomplete-49 — public baseline and the next ordinary-language inch

The first post-public-master baseline was measured from `2730f338` (the
current public tree) with CPython 3.9.25. The full Lean build passed **3,949
jobs**. `tools/check_python.py --no-build` passed every Python gate: 3,562
differential rows with zero failures, 140 scripts, the 217-file in-repo survey,
coverage, axiom, documentation, and both notebooks. The dedicated refusal
census was clean: **144 grammar witnesses (131 MATCH / 13 REFUSE)**, **312
curated rows in 63 refusal classes**, and **18 loud scripts in 12 classes**, all
with zero drift.

The two whole-program sweeps give the priority context. The in-repo corpus is
**189 MATCH / 28 REFUSE / 0 DIVERGE** (87.1%); its sole-blocker table has 16
files with no static wall, two class-creation-only files, and two import-only
files. The CPython 3.9 stdlib sweep is **7 MATCH / 159 REFUSE / 0 DIVERGE**
over 166 files. Imports are the largest static wall (881 nodes in 141 files),
but only 21 files have import as their sole blocker and the existing import
closure measurement shows that a Python-only module system buys little against
the C/OS boundary. The next ordinary-language frontier is therefore `str.join`:
the common separator method is currently refused dynamically, its heap-list
inputs are already represented, and the operation is a read-only string result.

The machine-readable stdlib result is `/var/tmp/ls-python-stdlib-baseline.json`;
the full refusal log is `/var/tmp/ls-python-refusal-baseline.log`.

## 2026-10-22-pycomplete-50 — `str.join` reads the existing sequence tier

`str.join` now evaluates the separator method on the monadic runner. The
worker covers strings (code-point iteration), bytes, tuples, namedtuples,
heap lists, ranges, dictionaries in insertion order, and empty iterables;
it retains CPython's indexed non-string-item `TypeError` and exact-one-
argument arity error. Generator and set operands remain loud because their
consumption would observe state or hash order. The trunk proof interpreter
has the same arm, with a payload-blindness lemma for the heap read.

`Examples/python/str_lab` adds seven matching rows and one intentional
generator refusal; the focused differential run is **8 rows, 7 MATCH and
1 whitelisted refusal, 0 failures**. The full coverage page and case file
were regenerated from this landing.

## 2026-10-22-pycomplete-51 — bounded `str.index` closes the adjacent method wall

`str.index` now supports its optional `start` and `end` bounds. Bounds use the
same integer/`None` normalization as string slices, search is restricted to
the requested half-open window, and CPython's `ValueError` and index-bound
`TypeError` payloads remain exact; over-arity keeps its faithful `TypeError`.
The monadic and trunk evaluators, clock-erasure and payload-blind walkers,
and the string laboratory all carry the new cases.

The focused differential battery is **8 rows, 8 matches, 0 failures**,
covering positive and negative starts, bounded windows, invalid bounds, the
existing wrong-needle error, and over-arity. `str_lab/spec.lean`, the
payload-blindness proof, and the clock-erasure proof all build. The next full
Python gate will regenerate the coverage totals.

## 2026-10-22-pycomplete-52 — scalar `divmod` protocol errors become faithful

The eight scalar nonnumeric `divmod` cases now raise CPython's exact
`unsupported operand type(s) for divmod(): 'A' and 'B'` `TypeError`, while
heap-backed and custom numeric protocols remain loud. The change is confined
to the existing pure `divmodArgs` worker, so argument order, arity, zero
division, float handling, lexical shadowing, and proof-layer dispatch remain
unchanged.

The divmod laboratory and differential case cover strings, `None`, tuple, and
list operands; the focused run confirms all eight cases and refreshes the
census and coverage totals.

## 2026-10-23-pycomplete-54 — immediate containers in `ascii()`

`ascii()` now renders tuple, namedtuple, list, range, and heap list/dict values
with the existing deterministic ASCII escape rules. The heap path shares the
active-address cycle and fixed-depth handling used by `repr`, while applying
`asciiStr` to nested string leaves. The existing
`str_lab.builtin_ascii_container` witness now matches CPython.

## 2026-10-22-pycomplete-53 — extend the fixed container-rendering budget

The renderer's caller-independent depth budget rises from 64 to 128 levels.
The two existing `repr_lab.deep` cases at depths 65 and 80 now match CPython;
cycles still use the active-address path and the over-budget integer and
identity boundaries remain unchanged.

DECIDED: spend a larger fixed rendering budget for ordinary nested containers,
while retaining loud failure beyond 128 so behavior does not depend on caller
fuel.

## 2026-08-22-pycomplete-1 — RUNG 3b: the eight consumers that could never meet the hazard their refusal cited

`list(d)`, `tuple(d)`, `sorted(d)`, `sum(d)`, `max(d)`, `min(d)`, `set(d)`,
`any(d)`, `all(d)` and `[*d]` all run, over the keys, in CPython's insertion
order. **Eight of the ten refusal messages §L39 hung rung 3 on are gone**, and
the grammar census moves **68 → 74 MATCH of 105**.
docs/memory-model.md §the draining consumers, as built.

### The finding this inch exists to prove

§L53 measured that these consumers **drain the keys with no user code running
in between**, so not one of the three mutation regimes — value update, size
change, same-size key-set churn — can arise inside them. Their refusals all
cited "live dict iteration; docs/memory-model.md", a blanket doctrine
inherited from the H1 decision to keep the live cursor out. **A refusal
inherits its REASON as readily as its text**, and only running each consumer
separately separated them.

What they needed was one line — `dictKeys es = es.map Prod.fst`, the entries
array being the insertion sequence already — plus seven value arms, each the
`.list` arm sitting beside it in the same `match`.

### The price was 19 walker arms, and §L53 called it

The census recorded the risk before the inch was written: *"`PayloadBlind`'s
swap-blindness lemmas must be shown to hold for the new dict arms… §L49's
`evalUnaryOpH_swapAt` is the standing reminder that an exhaustive `cases` can
hide behind a grep."* It fired, and wider than for one operator:

| walker | arms | why it broke |
| --- | --- | --- |
| `ClockErase` | 12 | `cases obj <;> try exact .unsupported` — the `try` silently absorbed the dict arm while it refused, and leaves the goal open once it decides |
| `PayloadBlind` | 7 | `\| _ => exact PBF.unsupported` catch-alls, plus the two `sortedValH` helper lemmas (`_swapAt`, `_slot`) whose `\| _ =>` arms had the same shape |

Every one is the adjacent `.list` arm's tactic verbatim. **The rule §L49
started now sharpens:** a change that makes a previously-REFUSING arm DECIDE
costs exactly as many proof arms as there are walkers whose catch-all was
leaning on that refusal. A refusal is not free in the proof layer — it is a
case someone else is standing on.

Payload-blindness holds structurally: a `PayloadTwin` is `.generator …
.running` on BOTH sides, so the swapped slot can never hold a dict; the new
arms read entries at an address the twin cannot be.

### The regression guard that flipped IS the acceptance signal

`Examples/python/star_lab/spec.lean` asserted `star_dict` refuses. `[*d]` now
answers CPython's `['x', 'y']`, so the build failed on that `#guard` — the
`%`-formatting landing's signal, at the one pre-existing expectation this inch
moves. It became a `#py_check` of the real value and its `cases.json` row
moved `unsupported` → `match`.

### What did NOT move, deliberately

The live cursor (`for k in d`, inch 3a) is untouched, and
`dict_lab.keys_for_is_still_loud` is the row that says so. The view methods
and `enumerate(d)` are inch 3c. The same-size churn regime stays
**permanently loud**, with §L53's cross-rung note standing: it is unreachable
today only because `del d[k]` refuses first, and becomes REQUIRED the day dict
deletion lands.

### THE OPERATIONAL LESSONS, paid for in full

This inch was built, verified green, and LOST — `/private/tmp` purged with the
commit unpushed while the lane queued on the build lock. It was rebuilt from
the recipe §L53 had already pushed: **the census survived because the census
was pushed.** Then it was nearly lost a second way, and that one is worth more
than the first:

* **`origin` in the seeded clones is a STALE LOCAL BUNDLE**
  (`~/repos/lean-surfaces-backup/…-20260814-….bundle`); the live remote is
  `github`. A lane that seeds a clone with `cp -Rpc` (§7 A13) inherits BOTH
  remotes, and `git reset --hard origin/master` silently lands it on
  2026-08-14 — a tree where this lane's own four landings do not exist. It
  also makes `git rev-list --count HEAD..origin/master` report `0` while the
  clone is a week behind, and makes a feature branch look "238 commits ahead
  of master". **Check `git remote -v` after seeding, and reset to
  `github/master`.**
* **A seeded clone inherits the seed's BRANCH.** `lean-es` was on `master`,
  but the first seed attempt (`lean-pyc2` from an earlier `lean-es`) came up
  on `pyrebuild-monadic`. Verify `git rev-parse --abbrev-ref HEAD` before
  building — a triad run on the wrong branch verifies nothing about master,
  and this lane spent one whole tenure discovering that.
* **Push on the FIRST green triad, before any fetch-rebase.** The verified
  state at first green is a landing; holding it for a post-rebase
  re-verification converts a landing into an exposure. Rebase and re-verify
  after the push.
* **Killing an out-of-tenure build costs almost nothing** — lake caches
  completed modules, so a killed build resumes where it stopped. Nobody
  should hesitate to kill their own build to protect the machine.

### Battery

`Examples/python/dict_lab` gains 17 functions / 33 `cases.json` rows: the
ORDER-observing rows (insertion order out of sort order, an overwrite keeping
its ORIGINAL position, `list(d)[0]`), every consumer, the empty-dict `max`
`ValueError` through the shared arm, non-int keys through the generic ordering
path, the `True`/`1` key-collision rule, the empty dict, and the still-loud
live cursor. Census: six `dict.*` witnesses flip REFUSE → MATCH.

## 2026-08-22-pycomplete-2 — the §9.4 DIVERGE/DIVERGED violation, closed

`harness/library_survey.py` emitted the family's failure verdict under two
names. The Go lane pinned the mechanism exactly — a deliberate rename at the
EMISSION BOUNDARY (`row["verdict"] = "DIVERGED" if verdict == "DIVERGE" else
verdict`) sitting downstream of eleven sites that already produced the
canonical `DIVERGE` — so the fix was mechanical rather than a redesign.

Eight sites: the translation is deleted, the direct set and its detail string
say `DIVERGE`, and the six consumers keyed on the drifted name follow it —
scoreboard order, the title/verdict pairing (which was `("DIVERGED",
"DIVERGED")`, a display title and a selector that had drifted TOGETHER, so
neither half revealed the other), and both exit gates.

**§5.4 both-directions discipline verified, not assumed**: both gates read
`return 1 if (counts.get("DIVERGE") or counts.get("INCOMPLETE")) else 0` — they
fail on a divergence or an unfinished battery and pass otherwise, and they now
key on the same string the 18 emission sites produce. Before the fix the gates
keyed on `DIVERGED`, which only worked because the boundary translation fed
them; delete that translation alone and the gates would have gone silent. The
two halves had to move together, which is why the audit's "one emits both" row
was the right tell.

`harness/library_oracle.py`'s `DIVERGED` is prose in a comment, not an
emission; normalized anyway so the vocabulary is single-valued in `harness/`.
`docs/duplication-audit.md`'s row is updated to record the fix rather than
left asserting a defect that no longer exists.

---

## 2026-08-22-softfloat-6 — INBOUND FROM THE SOFTFLOAT LANE: Python lane's to triage

*Filed by the SoftFloat lane during its core census
(`docs/softfloat-charter.md` §2.5). Id kept in the SoftFloat namespace.*

### `docs/completeness.md` §6's FLOAT RUNG IS DEFERRED ON A LEAN-SIDE PREMISE THAT IS FALSE AT THE PIN

Lines 368-373:

> * **`float`** — the largest gap by value and by price simultaneously. Four
>   grammar rows depend on it … but a DECISION: **Lean's `Float` is not
>   kernel-reducible**, so `#py_check` and every captured `rfl` run would break
>   on it — the same family as **the mergeSort trap**. It needs an owner-gated
>   design (an exact-rational …)

**Measured on `leanprover/lean4:v4.33.0-rc1`, and the premise no longer
holds.** `Float` is a plain structure over `Float.Model`, which is a structure
over a `BitVec` with a validity proof, and the arithmetic is ordinary Lean.
`((0.1 : Float) + 0.2 == 0.30000000000000004) = true` closes by **`rfl`**;
`+ − × ÷` all close by `rfl` and by `decide`, at binary16, binary32, binary64,
binary128 and binary256.

**The mergeSort intuition was right about the FAMILY and wrong about the
SCOPE.** There *is* a well-founded-recursion wall, and it costs exactly one
operation: **`sqrt`**, because `Nat.sqrt` is defined with
`termination_by guess` (`Init/Data/Nat/Sqrt/Basic.lean`). Isolated,
`Nat.sqrt 49 = 7` fails both `rfl` and `decide`. Everything else reduces.

**Two of your four grammar rows change price accordingly:** `const.float` and
`op.Div` are unblocked on the Lean side today. `op.Pow` with a negative
exponent is too. **`str`/`repr` of a float is NOT** — `Float.toString` is
`opaque` and core ships no decimal-printing model at all, so shortest-round-trip
printing is a real algorithm someone has to write. It is SoftFloat plan step 3
(`docs/softfloat-charter.md` §3), and this lane will build it; you do not need
to.

**And your own instinct was the right design.** §6 asks for *"an exact-rational
…"* design, and that is precisely what SoftFloat layer 2 is:
`LeanModels/SoftFloat/Basic.lean` defines `Q` — an unnormalized rational whose
comparison is cross-multiplication — because every finite float's value is
dyadic and every `+ − × ÷ √` result on finite inputs is rational. **ℝ never
appears.**

**One warning that applies directly to `#py_check`.** `#guard` runs Lean's
**untrusted evaluator** (`unsafe evalExpr`; core's own docstring: *"this uses
the untrusted evaluator, so `#guard` passing is not a proof"*). It honours
`@[extern]`, so on a float row it attests **the host C runtime, not Lean** —
and it passes identically whether the declaration reduces or is `opaque` with
no body. Measured three ways in `harness/softfloat/probe_walls.lean`. If
`#py_check` is `#guard`-shaped, its float rows will go green on facts the
kernel cannot check. A reduction gate is `rfl` or `decide`.

## 2026-08-23-pycomplete-3 — INCH 3a's CENSUS: the capability is one arm on the new definition and ~35 on a SHARED datatype

Inch 3a is the live dict cursor — `for k in d` at function scope, and the
bare-key form — on the MONADIC interpreter, per the no-backwards-compat
ruling. **The census was taken before a line was written, and it says the
ruling cannot be satisfied as stated at this inch.** Not because the monadic
control is hard: because the thing that has to gain a case is not the
interpreter, it is the CONTINUATION TYPE, and that type is shared.

Branch: `pyc-3a` off `github/pyrebuild-monadic-gate-green` (98f8d9dc), both
identity dimensions checked — remote is `github`, not the stale
`origin` bundle (§2026-08-22-pycomplete-1), and the tip matches gate-green.

### The static surface, measured

The monadic interpreter refuses live dict iteration at exactly **four** sites
— three for the cursor and one already covered by rung 3b on master:

| site | what refuses |
| --- | --- |
| `Monadic/Eval.lean:1369` | the `for` dispatch's `.dict` arm — the loop never starts |
| `Monadic/Eval.lean:1392` | the `.forList` cursor re-reading a dict address |
| `Monadic/Script.lean:150` | the script shell's own `for` arm |
| `Monadic/Eval.lean:237` | the draining consumers (rung 3b's territory; **not** on this branch — it landed on master after the branch was cut, and arrives by merge) |

So the cursor itself is **one new `execGen` arm** in `Monadic/Eval.lean`, plus
the script shell's. That half is small, and it is genuinely monadic-only.

### THE FINDING: `GenFrame` is shared, so "monadic-only" does not reach this capability

A faithful live cursor cannot reuse an existing frame. `GenFrame.forSeq`
carries `remaining : List RVal` — **a snapshot**, which §L53 measured to be
the wrong semantics (mutation during iteration must be observed);
`GenFrame.forList` carries `(addr, i)` and re-reads, which is the right
*shape* but the wrong object and carries no size/version to guard with. The
cursor needs its own constructor, carrying the dict address, the index, the
size at entry and the `shapeVersion` at entry.

`GenFrame` is declared in **`LeanModels/Python/Runtime.lean`** — the SHARED
runtime, not the monadic sibling. `Monadic/Substrate.lean` says so by design:
the rebuild "re-presents the interpreter's CONTROL", reusing the trunk's types
and pure workers verbatim, and the generator continuation is one of those
types (it is reachable from `Obj.generator`, which lives in the shared heap).

Seven files walk `GenFrame` exhaustively (measured by the `countFrom` arm,
which every exhaustive walk must mention):

| file | role | arms owed |
| --- | --- | --- |
| `Runtime.lean` | the declaration | 1 |
| `Semantics.lean` | the TRUNK interpreter (`execGen`, `stepIter`, the frame walkers) | ~6 |
| `VCGen.lean` | the VC layer's frame reasoning (26 `countFrom` mentions) | the bulk |
| `ClockErase.lean`, `Obs.lean`, `PayloadBlind.lean` | the proof walkers | ~1 each, expected vacuous |
| `Monadic/Eval.lean` | **the capability** | 1 |

**So the split is roughly 1 arm of new capability to ~35 arms of shared-type
maintenance, and all ~35 are in the legacy walker's files.** That is the
§L49/§L53 law one level up: a constructor is not free, and the bill is paid by
whoever exhaustively matches the type — here, the interpreter the ruling says
not to touch.

### The recommendation, and it is a scheduling one

**Sequence inch 3a AFTER the monadic branch merges to master**, not before.
The ~35 trunk arms are throwaway if the trunk is retired at the merge, and
load-bearing if it is not — and which of those is true is exactly what the
merge decides. Building them now spends the cost in the one window where it
is guaranteed to be either wasted or immediately rewritten.

Nothing else in the inch changes: the semantics are settled and already
measured (§L53), the guards are known (size change → CPython's faithful
`RuntimeError`, same-size key-set churn → permanently loud), and the
`shapeVersion` field the guard needs already exists in `Obj.dict` and is
already maintained by `dictStore`. **This is a census that moves a date, not
a design.**

### Owed

The dynamic baseline — `harness/refusal_census.py` run against BOTH
interpreters (`--runner "lake exe leanmodels-run --monadic"`) — is queued
behind eight tickets at the time of writing. It is telemetry, not a gate for
this entry's conclusion: the four refusal sites above are read off the
monadic source, and the `GenFrame` count is read off the seven walkers. The
run will additionally extend the acceptance gate's trunk/monadic parity claim
from the 1394 differential rows to the census's 105 grammar witnesses, which
is worth having on the record either way.

## 2026-08-23-pycomplete-4 — THE CENSUS CORRECTS ITSELF: the price is ~9 arms, not ~35, and the recommendation REVERSES

§2026-08-23-pycomplete-3 priced inch 3a's shared-datatype cost at "~35 arms"
and recommended deferring the inch until after the monadic merge on that
basis. **The number was wrong by roughly 4x, the error was mine, and it was
the exact mistake this lane has now made twice.**

### What went wrong

The count came from `grep -c countFrom` per file — **mentions, not match
arms.** `VCGen.lean`'s 26 mentions, which supplied "the bulk" of the estimate,
are LEMMA NAMES and per-frame statements (`genSteps_countFrom`,
`genYieldsPrefix_countFrom`), not exhaustive matches. VCGen proves facts about
*particular* frames; a new frame simply has no lemma until someone wants one.

Counting actual pattern positions
(`grep -cE '(\| *\.?countFrom|case +\.?countFrom)'`) gives:

| file | real arms | what they are |
| --- | --- | --- |
| `VCGen.lean` | **0** | per-frame lemmas, not a walk |
| `Runtime.lean` | 2 | the constructor, and one `GenFrame` predicate arm |
| `Semantics.lean` | 3 | two GROUPED catch arms (`\| .enumSeq .. :: _ \| .enumList .. :: _ \| .countFrom .. :: _`) and the trunk `execGen` arm |
| `ClockErase.lean` / `Obs.lean` / `PayloadBlind.lean` | 1 each | one line each, of the shape `simp only [execGen]; exact …` |
| `Monadic/Eval.lean` | 1 | **the capability** |

**≈9 arms total**, of which one is the capability, three are one-line proof
arms, and the rest is declaration and bookkeeping. Under the ruling the
trunk's `execGen` arm is a `refuse` — the capability does not open there — so
it is one line, not an implementation.

### This is §L49's law, recurring, and the third time is not a coincidence

* §L49: a `\.usub` grep found every `match` position and missed every
  `cases op with \| usub =>` arm — **one character**.
* §L53/§2026-08-22-pycomplete-1: the walker price was predicted from the
  `.list` arms and came in at 19, because catch-alls were load-bearing.
* Here: mention-count read as arm-count, **4x high**, and the inflated number
  was about to move a date.

The rule this lane now writes down for itself: **a count that prices a
decision must come from the pattern position, never from the identifier.**
`grep -c <ctor>` answers "who talks about it"; only `grep -cE '\| *\.?<ctor>'`
answers "who must gain a case". The upstream commit title from the same day —
*"a grep that agrees with you is the one to re-run"* — is the same finding
arriving from another lane, and it should be read as a family law.

### The recommendation, reversed

**Inch 3a is affordable now and does not need to wait for the merge.** ~9
arms, one of them the capability and three of them one-liners, is an inch, not
a campaign. §2026-08-23-pycomplete-3's scheduling conclusion is WITHDRAWN;
its static surface map (four refusal sites, the snapshot-vs-cursor argument
for why a new constructor is unavoidable, and `shapeVersion` already existing
in `Obj.dict`) stands unchanged, because those were read off pattern positions
and source text rather than off a counter.

The one substantive point that survives from the earlier entry: **`GenFrame`
is shared, so this capability cannot be opened on the monadic definition
alone** — the trunk gains a `refuse` arm and three walkers gain a line each.
That is a fact about the type's home, and it is worth a ruling, but it is a
9-line fact rather than a 35-line one.

## 2026-08-23-pycomplete-5 — INCH 3a BUILT: the live dict cursor, on the monadic definition only

`for k in d` runs on the monadic interpreter, at BOTH scopes, with the three
regimes §L53 measured against CPython 3.9.19. The trunk gains a refuse arm and
nothing else, per the ruling. **Queued for verification at the time of
writing** (queue depth 9); this entry records what was built and why, and the
triad's numbers land with the next push.

### What the ruling bought, and what it cost

| file | change | kind |
| --- | --- | --- |
| `Runtime.lean` | `GenFrame.forDict` + its `WF` arm | shared type grows (ruled) |
| `Semantics.lean` | `genBreak`/`genContinue` arms + the trunk's `execGen` REFUSE arm | legacy contract: compiles, refuses, gains no consumers |
| `ClockErase/Obs/PayloadBlind` | one line each | walker bookkeeping |
| `Monadic/Eval.lean` | the dispatch builds the frame; the cursor arm | **the capability** |
| `Monadic/Script.lean` | `SKont.forDict` + `scriptForDictAt` + wiring | **the capability**, module scope |
| `Monadic/Prim.lean` | `dictStepM` | the new primitive |
| `Monadic/Spec.lean` | `dictStepM_spec` | its `@[spec]` lemma |

Measured at ~9 shared arms in §2026-08-23-pycomplete-4; that held.

### `genBreak`/`genContinue` are the arms a mechanical patch gets WRONG

`forDict` is a LOOP frame: `break` must pop it and `continue` must keep it, so
it belongs with `forSeq`/`forList`/`forGen`/`whileLoop` and NOT with the
builtin-iterator group (`enumSeq`/`enumList`/`countFrom`), which returns
`Option.none` because those frames have no body and flow can never reach one.
A patch that added `forDict` to the refusing group would have compiled and
been silently wrong for every `break` in a dict loop.
`dict.for-in-function` exercises exactly that — it `continue`s past a key and
`break`s early — which is why the witness is written that way.

### The step is a PURE PLAN, because the walker law says it must be

AGENTS.md records that `execGen` MUST fork on a pure plan (`genPlan`'s
precedent): with the match inline, the equation compiler splits the arm per
constructor and `simp only [execGen]` never fires at a symbolic frame. So the
three regimes are `DictStep` — `resized` / `rekeyed` / `yieldKey` / `done` —
decided by the pure `dictStep`, and BOTH cursors fork on it. One decision, two
consumers, no drift; and `dictStepM` lifts it to one action with one `@[spec]`
lemma instead of a heap read plus a decision that `mvcgen` must re-split at
each call site. `dictStepM_spec` says the step leaves the state UNCHANGED —
a cursor must not disturb the dict it walks, and that is now a theorem.

### THE GATE COULD NOT EXPRESS A RULED DIVERGENCE, and that is an instrument finding

`harness/monadic_gate.py` asserts trunk/monadic PARITY and exits non-zero on
any divergence whose monadic answer is not a `monadic-rebuild:` frontier
refusal. **Inch 3a creates a legitimate divergence on purpose** —
`dict_lab.iter_dict` refuses on the trunk and returns `1` on the rebuild — so
the ruled inch could not have landed green, and the wrong fix would have been
to switch the gate off.

The gate now has an `OPENED` classification, and its design is what keeps it
honest: **a row counts as OPENED only when the rebuild's answer MATCHES
CPYTHON.** If the rebuild diverges from the oracle it is a FINDING no matter
what the table says, because the adjudicator is CPython and never the table.
This is the same shape as the two other instrument gaps this lane has hit —
a check whose vocabulary cannot express a legitimate new state
(§2026-08-22-pycomplete-2's `DIVERGE`/`DIVERGED`, and the census's own
trunk-vs-monadic expectations below).

### The census becomes a TWO-INTERPRETER scoreboard

A witness may now carry `mono=` — the expectation under `--target monadic`,
when it differs. Four do, all of them this inch: `dict.for`,
`dict.for-in-function`, `dict.update-value-during-iter` and
`dict.grow-during-iter` are REFUSE on the trunk and MATCH on the rebuild.
`dict.churn-during-iter` stays REFUSE on both — `del d[k]` refuses first, so
the same-size churn hazard remains unreachable, exactly as §L53 recorded.

Encoding the divergence beats switching the parity check off: the census keeps
gating BOTH interpreters, and the rows where they differ ON PURPOSE are
written down rather than tolerated. 106 witnesses now.

## 2026-08-23-pycomplete-6 — THE FIRST TICKET WAS RED, and both reds were findings the witnesses were written to catch

Inch 3a's first verification came back **build green, gates RED**, on two
independent counts. Neither was a proof failure and both were real.

### RED 1 — the inch was HALF WIRED, and `dict.for-in-function` is what caught it

`dict.for` (module scope) MATCHED. `dict.for-in-function` REFUSED against a
recorded MATCH. The monadic interpreter has **THREE** `for` entry paths, not
the two the static census named:

| path | who takes it | wired in the first attempt? |
| --- | --- | --- |
| `execGen`'s `.forList`/`.forDict` frames | a GENERATOR body | yes |
| `SKont.forList`/`.forDict` | module scope | yes |
| **`Kont.forList`/`.forDict`** | an ORDINARY `def` — **the commonest path of all** | **NO** |

The third is `Monadic/Prim.lean`'s `Kont`, a *different record* from the script
shell's `SKont`, and its dict arm sat one screen below the one I patched. A
census that had stopped at "grep the refusal messages" would have shipped a
cursor that worked in generators and at module scope and refused in every
ordinary function — and the diff_test battery would NOT have caught it,
because the trunk refuses those rows too, so trunk/monadic parity holds while
both are wrong.

**The witness was written to exercise `break` and `continue` through the new
frame, and it earned its place twice over: it caught a missing ENTRY PATH, not
the flow control it was aimed at.** §L14's law again — a statement-level count
is not an ingestion verdict; run the thing.

### RED 2 — rung 3b never reached the rebuild, and the merge is where it was lost

25 divergences, every one a `keys_*` or `star_dict` row: **the trunk
implements the draining consumers and the rebuild does not.** Rung 3b landed
on the trunk (2026-08-22-pycomplete-1) while the monadic branch was already
cut, and the merge carried the trunk's arms without carrying the capability
across the presentation boundary. That is a defect on master that predates
this inch; the gate run is what surfaced it.

**The fix is ONE line, and the reason is the rebuild's own factoring.** The
trunk pays rung 3b seven times — one arm per consumer, each beside its own
`.list` arm. The rebuild has `iterValues`, the single dispatch `sum`/`tuple`/
`list`/`set`/`any`/`all` all share, so the same capability is one arm there.
`sorted`/`max`/`min` needed nothing at all: they route through the SHARED
trunk workers (`sortedValH`/`extremumValH`), which is `Monadic/Substrate.lean`'s
"maximal trunk" claim paying off in a measurable way — those four rows were
already green in the red run.

### What did NOT need changing

The census expectations were already right: the four `mono=` divergences and
the trunk column both stated the intended end state, so the fixes made the
recorded expectations true rather than the expectations being edited to match
the code. **That is the direction a scoreboard has to move in**, and it is
only possible because the expectations were written from CPython's measured
behaviour (§L53) rather than from the model's.

## 2026-08-23-pycomplete-7 — the second ticket: 25 divergences → 1, and the last one was a NAME that stopped being true

Ticket 2: build green, `diff_test` 1427/0/118, both `script_corpus` runs
65/0/50/15, trunk census 0 drifts, **monadic gate 1425/1427 parity with 1
CAPABILITY OPENING** (`iter_dict` — the `OPENED` bucket firing exactly as
designed: trunk refuses, rebuild runs, CPython agrees). The two fixes worked.

Two remainders, and they were the same fact reaching two instruments:

* the gate's last divergence — `keys_for_is_still_loud(7)`
* the census's two whitelist drifts — `iter_dict` and
  `keys_for_is_still_loud` "whitelisted but the model answered ok"

**`keys_for_is_still_loud` is a row I wrote in rung 3b**, whose comment read
*"the LIVE cursor is a separate inch (3a) and stays refused"*. Inch 3a landed
it. The row did not break — **its NAME made a claim that stopped being true**,
and the instruments correctly convicted the name.

It is renamed `keys_for_live_cursor`: it names the CONSTRUCT rather than a
verdict, which is the durable choice, and its comment now records that the
trunk refuses it by the ruling while the rebuild runs it. A name that asserts
a verdict has a shelf life; a name that asserts a construct does not.

### The whitelist half of the census gains the column the grammar half had

`MONO_OPENED` — whitelisted rows (the TRUNK refuses them) EXPECTED to answer
under `--monadic`. The split that keeps it honest is explicit: **the census
records intent and never adjudicates**, because it runs one interpreter and
never sees CPython's answer for those rows; proving the rebuild RIGHT is
`monadic_gate`'s job, whose `OPENED` bucket counts a row only when the rebuild
matches the oracle. Census records, gate adjudicates.

That is the fourth instrument this lane has had to teach a new legitimate
state, after `DIVERGE`/`DIVERGED`, the census's grammar column and the gate's
`OPENED`. The pattern is now unmistakable: **during a re-founding, every
two-sided check needs a vocabulary for "these differ on purpose", and the
default vocabulary never has one.**

## 2026-08-23-pycomplete-8 — INCH 3c's CENSUS: a view is a LIVE OBJECT, and the three views are not one construct

Measured on CPython 3.9.19 before any design. The headline is that
`.keys()`/`.values()`/`.items()` are **not** three spellings of one thing, and
the differences are exactly where a reasonable-looking model would be silently
wrong.

### What a view IS

| probe | CPython |
| --- | --- |
| `type(d.keys())` | `dict_keys` — an OBJECT, not a list |
| `k = d.keys(); d[2] = 'b'; list(k)` | `[1, 2]` — **LIVE**, it still sees the dict |
| `len(d.keys())` after growth | tracks the dict |
| `d.keys()[0]` | `TypeError: 'dict_keys' object is not subscriptable` |
| `list(reversed(d.keys()))` | works (3.8+) |

### THE TRAP, and it is the finding of this census

| probe | CPython | why it matters |
| --- | --- | --- |
| `d.keys() == {1, 2}` | **True** | keys compare as a SET |
| `d.items() & {(1,'a')}` | `{(1, 'a')}` | items are set-like too |
| `d.values() & {1}` | **TypeError** | values are NOT set-like |
| `d.values() == d.values()` | **False** | a values view defines NO equality, so it falls back to IDENTITY |

**`d.values() == d.values()` being False is the row to keep.** Two views of the
same dict, compared, answer False — and a model that treated the three views
uniformly (or that made a view compare by contents) would answer True. That is
the silently-wrong direction, and it is also the intuitive one, which is what
makes it worth a witness rather than a sentence.

### Mutation during view iteration is 3a's regime, unchanged

Growth during `.keys()` iteration raises the same
`RuntimeError: dictionary changed size during iteration`; a value update
during `.values()` iteration is fine. So 3c inherits 3a's guards rather than
inventing any — `dictStep` already decides all three regimes.

### `enumerate(d)` needs nothing new either

`enumerate(d)` is `[(0, k₀), (1, k₁), …]` over the keys, `enumerate(d, 5)`
starts at 5, and growth mid-iteration raises the same `RuntimeError`. It is the
key cursor with an index — 3a's frame with `enumSeq`'s counter.

### The split, and it is the same shape as 3b/3a

* **3c-i — views in CONSUMING position.** `for k, v in d.items():`,
  `list(d.keys())`, `sorted(d.values())`, `sum(d.values())`,
  `enumerate(d)`/`enumerate(d.items())`, `dict(d.items())`, `tuple(d.items())`.
  **The view never escapes**, so it needs no object: the call is FUSED with its
  consumer, exactly as the script shell already fuses
  `for … in d.items():`. This is nearly all real usage.
* **3c-ii — views as FIRST-CLASS VALUES.** `k = d.keys()` held across
  statements, set algebra, `==` against a set, `reversed`. This needs an
  `Obj.dictView` carrying the dict's address and the view KIND, plus a
  set-algebra inventory for keys/items and the identity-equality rule for
  values. `dict.view-escapes` is its marker witness.

**3c-i is the inch; 3c-ii is a tier.** Splitting them is not deferral: the
consuming forms are what stdlib and application code actually write, and they
cost no new heap kind.

### Where the refusals live, and the instrument constraint

Two SHARED sites carry almost all of it — `Semantics.lean:2920` (the dict
attribute-call plan, which admits `.get`/`.clear` and refuses the rest) and
`Semantics.lean:3805` (`enumerate()` over a dict). Both are pure workers on
the "maximal trunk", so admitting them serves BOTH presentations, exactly as
rung 3b's `sortedValH`/`extremumValH` already did.

Per the arch lane's end-condition, **3c adds nothing to `harness/monadic_gate.py`**:
the two-model window is closing, so new expectations go in the census's
CPython-written column and in `diff_test`, both of which survive the collapse.
`MONO_OPENED` and the monadic census column are window vocabulary and retire
with the window; when the successor's delete/modify conflict arrives on
`monadic_gate.py`, **the resolution is DELETE** — those +38 lines are
scaffolding, and its two `OPENED` rows become ordinary `diff_test` rows once
there is one interpreter and the differential's other side is CPython.

### Battery

Five new witnesses, all REFUSE today: `dict.values`, `dict.items-consumed`
(3c-i's targets), `dict.view-escapes` (3c-ii's marker),
`dict.values-identity-eq` and `dict.keys-set-algebra` (the two traps). 111
witnesses.

## 2026-08-23-pycomplete-9 — 3c-i CANNOT live in the shared pure workers, and the reason is the doctrine's own trap

The sequencing note asked that 3c-i's footprint stay "inside the two shared
pure workers + witnesses", so the successor's re-merge would be trivially
textual. **That footprint is not achievable for a CORRECT 3c-i**, and the
census already contains the proof. Recording it before a ticket is spent on it.

### Why the shared-worker route is a silent wrong answer

The two shared sites are `Semantics.lean`'s dict attribute-call PLAN (admits
`.get`/`.clear`) and `enumerate()`-over-a-dict. Admitting `.keys()`/
`.values()`/`.items()` in the plan means the call must ANSWER something, and
the only thing a pure plan can answer is a value. A snapshot is the obvious
one — and a snapshot is measurably wrong:

    d = {1: 'a'};  k = d.keys();  d[2] = 'b';  print(list(k))
    CPython: [1, 2]        a snapshot would print: [1]

That is `dict.view-escapes`, already a witness (§pycomplete-8). So the
shared-worker route buys 3c-i by installing exactly the failure the loudness
doctrine exists to prevent, in the one shape the census had already measured.
**The constraint and correctness point in opposite directions, and correctness
wins.**

### What the code says the real footprint is

Fusion is CONTROL, and the repo already knows it: the only view form in tier
today is recognised SYNTACTICALLY at the statement level —
`Monadic/Script.lean`'s `.forStmt target (.call (.attribute d "items" …) …)`
arm. Every consumer (`sum`/`tuple`/`list`/`set`/`any`/`all` via `iterValues`,
`sorted`/`max`/`min` via `sortedValH`/`extremumValH`) receives an ALREADY
EVALUATED `RVal`, so no pure worker can tell `list(d.keys())` from
`k = d.keys()`. Only the call site can.

### The corrected split — and the first piece is genuinely small

* **3c-i-a — `for` over a view, at every scope.** `for k in d.keys():`,
  `for v in d.values():`, `for k, v in d.items():`. **This is one FIELD on
  3a's frame**: `GenFrame.forDict` already carries
  `(target, addr, i, n, sv, body)`, so adding a view KIND turns
  `for k in d` and all three view loops into the SAME cursor, with
  `dictStep`'s `yieldKey` generalised to yield the key, the value, or the
  `(k, v)` tuple. Three cursor paths to touch — the same three 3a taught us
  to check — plus the syntactic recognition. **`for k, v in d.items():` at
  FUNCTION scope is the single most common dict idiom in real Python, and
  today it refuses** (`dict.items-in-function`).
* **3c-i-b — consuming CALLS.** `list(d.keys())`, `sorted(d.values())`,
  `sum(d.values())`, `tuple(d.items())`, `dict(d.items())`. Needs one
  argument-evaluation helper that recognises the view call before evaluating
  it, wired at the consumer sites.
* **3c-i-c — `enumerate(d)`.** Live, so it needs its own frame like `forDict`
  — it cannot ride a snapshot either.

### The recommendation

Take **3c-i-a** as the next ticket. It is the dominant idiom, it is one field
plus arms on machinery inch 3a just landed and verified, and its footprint is
`Runtime.lean` + monadic control + witnesses — the same shape the ruling
already sanctioned for 3a, and about as textual for the successor to re-merge
as anything that touches control can be. 3c-i-b and 3c-i-c follow separately.

**Nothing here touches `harness/monadic_gate.py`**, per the end-condition; the
new witnesses' expectations go in the census's CPython-written column and
`diff_test`.

## 2026-08-23-pycomplete-10 — 3c-i-b hits a STRUCTURAL wall, and the fix is an ingestion rewrite, not a call-site fusion

3c-i-b was built as designed — fuse the consuming call at the ONE site where a
named call's args meet its plan, recognising the view BEFORE evaluating it —
and it does not compile. The verdict is **RED**, the cause is structural, and
it redesigns the inch. Implementation reverted; this entry is the finding.

### The wall

`Monadic/Eval.lean`'s expression half is **structural on `Expr`**. The fused
arm has to evaluate the view's RECEIVER, and the receiver arrives out of a
pure recognizer (`viewArgOf plan args.toList`) — so the equation compiler
cannot see it as a subterm and the block stops being structurally recursive:

    error: LeanModels/Python/Monadic/Eval.lean:631:0: failed to infer structural recursion

**The file says so itself**, three lines above where the fusion went, and the
comment predates this inch:

> the free-scrutinee discipline … is load-bearing twice over — it is also what
> keeps this block structurally recursive, since a mutual member taking the
> SAME `List Expr` is not a decrease.

Checked rather than assumed: every `evalOpen` in that block is applied to a
DIRECTLY MATCHED subterm (`recv`, `iter`, `test`), and the file's only
`match args.toList` — the trace clock's — inspects ARITY and never evaluates a
matched element. There is no precedent for evaluating an `Expr` pulled out of
`args`, because there cannot be one.

### The finding, and it is the mirror of the walker law

§3a recorded that `execGen` MUST fork on a pure plan or `simp only` never
fires. Here the pure plan is what BREAKS the definition: the fuel-free half is
structural on the syntax, so a plan that HIDES the subterm relation costs
exactly what a plan that EXPOSES the constructor bought.

**The rule, for both halves at once: a pure plan may decide WHAT to do, but
never supply a term the definition then RECURSES on.** In the fueled half the
plan is free because fuel is the measure; in the fuel-free half the measure IS
the syntax, and the plan erases it.

### The corrected design — fuse at INGESTION, which the repo already does

Rewrite the ARGUMENT, not the call. At ingestion, when a consuming builtin's
sole argument is syntactically `d.keys()`/`.values()`/`.items()`, rewrite that
argument to a synthetic builtin call over the receiver:

    list(d.keys())   ⇢   list(<dictkeys>(d))

Then the evaluator's existing path evaluates `d` as an ORDINARY argument —
structural, because `d` sits in `args` and rides `evalOpenList` — and
`applyBuiltin` gains one arm answering the element sequence for
`<dictkeys>`/`<dictvalues>`/`<dictitems>`.

This is the repo's own established mechanism, not a new one: `ListComp`
desugars to `list(genexp)` and `yield from <genexp>` inlines, both at
ingestion, both for the same reason — the evaluator should meet a shape it
already handles.

What it costs, and why it is cheaper than what failed:

* **no new `Expr` constructor** — the rewrite lands inside the existing call
  shape, so `Ast.lean` and every walker are untouched;
* **no structural risk** — nothing new is recursed on;
* **no `Mono.lean` cost** — one arm under an existing shape, which the merge's
  measured rule says is free;
* **soundness unchanged** — the rewrite fires only when the view is the
  argument of a consuming call, so `k = d.keys()` is never rewritten and
  `dict.view-escapes` still refuses. The snapshot stays licensed by the SHAPE.

### Cost of this red, recorded honestly

Three tickets. Two were my own defect and the same one twice — a declaration
inserted between a doc comment and its `def`, which Lean reports as a bare
parse error far from the cause. **I had written a scanner for exactly that
after the first, and did not run it on the file I had just edited.** The scan
is now over every changed `.lean` in the diff, not the files I remember
touching. The third ticket is this finding, which no amount of care at the
edit would have avoided — only building it.

One process note worth carrying: a triad's enqueue-tree gate correctly refused
a run after I amended the commit post-enqueue. **Do not touch the tree between
enqueue and acquire** — the amend cost a full queue slot (83 minutes) for a
one-line index regeneration that should have preceded the ticket.

**Provenance.** This entry was WRITTEN on 2026-08-23 and never landed: it lived only on the unlanded branch `pyc-3cib` (`4aa12f7`), while the redesign it produced landed as §pycomplete-11 — which cites it. A citation whose target is on a branch is a dangling citation, and the remedy for a provenance gap is provenance. Recovered here VERBATIM; the `Monadic/Eval.lean` comment it quotes still resolves BY CONTENT (*“a mutual member taking the SAME `List Expr` is not a decrease”*).

## 2026-08-23-pycomplete-11 — 3c-i-b, rebuilt as an INGESTION rewrite, and the third decision site named

`list(d.keys())`, `sorted(d.values())`, `sum(d.values())`, `len(d.keys())`,
`tuple`/`set`/`any`/`all`/`max`/`min` over a view all run — by rewriting the
ARGUMENT at ingestion rather than fusing at the call site:

    list(d.keys())   ⇢   list(<dictkeys>(d))

The evaluator then meets a shape it already handles: `d` rides the ordinary
argument path, so nothing new is recursed on and §pycomplete-10's structural
wall is not approached. `applyBuiltin` gains one arm answering the element
sequence; `callNamePlan` admits the synthetic names.

### THE THIRD PLACE A CONSTRUCT'S MEANING IS DECIDED

A capability audit that reads the extractor and the interpreter will not find
this rewrite, because it is in neither. **Ingestion is a third decision site**,
and it already holds two other constructs:

| construct | decided at ingestion | recorded in |
| --- | --- | --- |
| `ListComp` | desugars to `list(<genexp>)` | docs/memory-model.md §list comprehensions |
| `yield from <genexp>` | inlined into the enclosing body | docs/memory-model.md §yield from |
| **dict views in consuming position** | **rewritten to `<dictkeys>`/`<dictvalues>`/`<dictitems>`** | **here, and `Ast.lean` §the dict-view ingestion rewrite** |

The vocabulary lives in `Ast.lean` (which is what ingestion can see) with a
header naming the precedent, so the next audit finds it from either end.

### The synthetic names are deliberately NOT builtins

`<dictkeys>` and its siblings use the `<genexpr@n>` convention — angle
brackets make them unspellable in Python, so they cannot collide with a user
binding. They are checked in `callNamePlan` BEFORE `isBuiltinName` and kept
OUT of it: that list is the pinned CPython `dir(builtins)` and every arm that
may decide a `NameError` consults it, so adding a synthetic name there would
move a real decision (the §2026-08-15 silent-wrong-answer fix's own lesson).

### The battery is written in the SOURCE spelling, which is the point

Ten new `dict_lab` rows spell `d.keys()`, never `<dictkeys>(d)`. CPython sees
the source text, and **the rewrite is what is under test** — a row written in
the lowered form would exercise the evaluator and skip the pass that produced
it. Two of the ten are the boundary:

* `view_escape_still_loud` — `k = d.keys()` then use. Not a consuming
  position, so ingestion leaves it alone and the tier refuses. CPython
  answers 1; the refusal is what keeps the snapshot honest.
The `view_arg_not_alone_still_loud` spelling now matches: the consuming
`list(d.keys())` call is the sole view argument, and its resulting list slice
is live. Only the escaping-view shape remains loud here.

**The shape is what licenses the snapshot**, and these two rows are how that
claim is falsifiable rather than asserted.

## 2026-08-23-pycomplete-12 — the audit's §python triage

`docs/quality-audit-2026-08-23.md` §python, 14 rows. Fixed in this pass, folded
into 3c-i-b rather than stopping it. Each fix cites the audit.

### The two HIGHs

**`bench_bisect/spec.lean` — the stated reason was FALSE, and it cost the two
functions their oracle.** The block claimed `cases.json` rows were
"inexpressible … `leanmodels-run` parses CLI args as ints only". The runner has
taken canonical typed values for as long as the batch protocol has existed, and
the whole corpus uses them. **Measured before writing anything**: nine value
rows across `bisect_left`/`bisect_right` — including every line of the vendored
docstring's authenticity block — are answered by the model today and agree with
CPython. They are now `cases.json` rows. The ONE row the oracle cannot reach is
`lo < 0`, whose `raise ValueError(…)` is outside the exception tier; it is
whitelisted with that reason. **A false blanket claim was hiding a real,
one-shape gap** — which is the more interesting half: the gap was smaller than
the claim, and the claim is why nobody looked.

**`pins_genmoves.lean` — re-labelled, and the real fix delegated.** The
thirteen boards' expected lists said "Every expected list below IS CPython's
own answer, in CPython's order", present tense, while `gen_moves` appears in
ZERO `cases.json` rows — nothing re-derives them. The wording now says what is
true: TRANSCRIBED from CPython when the reference was written, with a date, and
nothing regenerates them.

The real fix is a generator that survives — the fourteen boards moved to one
data file that both the pin and a Python script read. **Not taken here**: the
boards are defined in the sunfish campaign's own proof files, so it belongs
with whoever owns them. Noted, not claimed.

### The mediums fixed

* **`Monadic.lean`'s header was stated-vs-actual, inverted by the collapse.**
  It said the trunk stays authoritative and the rebuild is merely
  build-checked via a `--monadic` shim. Checked: `Main.lean` now calls
  `callInMono`/`runScriptClockMono` UNCONDITIONALLY, and `--monadic` and
  `monadic_gate` are gone — while `LeanModels/Python.lean` still imports
  `Semantics.lean`. The header now states the actual split: **executable
  behaviour is the rebuild's, proved behaviour is still the trunk's**, held
  together by the pure workers they share. That split is worth stating
  plainly — it is why a capability opening here reaches the harnesses at once
  and the proof layer not at all.
* **`refusal_census.py` printed the ROW count as a PRODUCTION count** — "113
  productions" for a grammar of 81, because edge rows and per-construct
  witnesses are extra witnesses for productions already counted. It says
  `witnesses` now, and the header says "a witness per production, plus
  measured edge rows".
* **`script_corpus.py`'s `default_oracle` degraded silently** `python3.9` →
  `python3` → `sys.executable`, which its own docstring calls the trap. The
  fallbacks stay — a box without the pin should still run it — but each
  degradation now WARNS in the same voice the re-exec warning uses.
* **`docs/completeness.md`'s counts are derivable and were stale.** They are
  marked AS TAKEN, with the instrument named authoritative and the command to
  get live numbers. The taken-tables are deliberately kept: they are what each
  rung was PRICED against, and rewriting them would erase the pricing they
  justify.

### Not fixed, with reasons

* **`PayloadBlind.lean`'s cited line ranges, stale by ~350 lines.** Real, and
  a line-number citation goes stale on every insertion above it — that is the
  defect, not the current offset. Worth one pass converting them to lemma
  NAMES, which do not drift; noted for whoever next edits that file, since
  fixing offsets without changing the form buys one landing of accuracy.

## 2026-08-23-pycomplete-13 — INCH 3c-i-c's CENSUS: `enumerate(d)` is a GENERATOR FRAME, so the Kont record is not touched at all

Measured on CPython 3.9.19 before any design, and read against the tree
before any price. Two findings, and both correct a standing expectation.

### What CPython does — the ORACLE's column, in the SOURCE spelling

| probe | CPython 3.9.19 |
| --- | --- |
| `for i, k in enumerate(d):` | `0 x` / `1 y` — the index rides the KEYS |
| `list(enumerate(d, 5))` | starts at 5 |
| `list(enumerate(d, -3))` | starts at −3 — the start is an `int`, never a `Nat` |
| `enumerate(d, 1.5)` | `TypeError: 'float' object cannot be interpreted as an integer` |
| `list(enumerate(d, start=5))` | works — the KEYWORD spelling is a second shape |
| `next(enumerate(d))` | `(0, 'x')` — it is an ITERATOR OBJECT, not a sequence |
| `list(enumerate(d))` | `[(0, 'x'), (1, 'y')]` |
| `dict(enumerate(d))` | `{0: 'x', 1: 'y'}` |
| `list(enumerate(d.items()))` | `[(0, ('x', 1)), (1, ('y', 2))]` |
| `list(enumerate(d.values()))` | `[(0, 1), (1, 2)]` |
| `len(enumerate(d))` | `TypeError: object of type 'enumerate' has no len()` |
| `list(reversed(enumerate(d)))` | `TypeError: 'enumerate' object is not reversible` |
| `enumerate(d) == enumerate(d)` | `False` — identity equality, exactly `d.values()`'s row |
| `e = enumerate(d)` alone | binds SILENTLY — no output, no error |
| `print(type(e).__name__)` | `enumerate` |
| `print(e)` | `<enumerate object at 0x…>` — an ADDRESS, so unusable as an expectation |
| `e = enumerate(d)`; `d[2]='b'`; nothing | still no error — the guard is on the STEP, not the bind |
| `e = enumerate(d)`; `list(e)`; `d[2]='b'`; `list(e)` | `[(0, 'a')]` then `[]` — an EXHAUSTED enumerate stops checking |

### THE TRAP, and it is §pycomplete-8's, pointing the other way

    d = {1: 'a'};  e = enumerate(d);  d[2] = 'b';  print(list(e))
    CPython: RuntimeError: dictionary changed size during iteration
    a snapshot would print: [(0, 1)]

An escaped `enumerate(d)` **is live**. §pycomplete-8 measured a view answering
`[1, 2]` where a snapshot answers `[1]` — a wrong VALUE. Here a snapshot
answers where CPython RAISES — a wrong OUTCOME. Same trap, opposite direction,
and the second direction is the one a model reaches for first, because
"enumerate materialises its argument" is the intuitive reading. Growth inside
the loop and `del d[k]` inside the loop raise the same `RuntimeError`; a value
update of an existing key is fine (`{1: 'z', 2: 'z'}`) — so all three regimes
are 3a's, unchanged, and `dictStep` already decides them.

### THE STRUCTURAL FINDING: this inch does not touch `Kont`

The sequencing note expected 3c-i-c to be the PAYING case — "its own `Kont`
frame", with the four `Kont`-record touch points in `Monadic/Mono.lean` that
the `fuelMono` maintenance rule charges for a new field. **The code refutes
it.** `enumerate` in this tier is not a loop cursor: `applyBuiltin`'s
`enumerate` arm (`Monadic/Eval.lean`) builds a `GenFrame` through `enumFrame`
and heap-pushes `.generator "<enumerate>" [] [fr] .suspended`, so the object is
first-class ALREADY and every consumer reaches it through `stepIter`,
`execGen` and `forGen` — **all three of which are existing `Kont` fields**.

So: no new field, no new `KontLe` conjunct, no growth in the sixteen
`obtain ⟨…⟩ := hK` destructurings, nothing in `KontLe.bottom` or `kontMono`.
`Mono.lean` is untouched. The maintenance rule does not fire, and the reason it
looked like it would is that `for k in d` (§3a) and `for i, k in enumerate(d)`
LOOK like the same construct and are not: the first is a loop the interpreter
drives, the second is an object the loop consumes.

### The site is a SHARED pure worker, and this time that is CORRECT

`enumFrame` (`Semantics.lean`) is called by BOTH presentations — the rebuild at
`Monadic/Eval.lean`'s `enumerate` arm and the trunk at its own — and its dict
arm is today's refusal (*"enumerate() over a dict iterates its keys — outside
the tier"*). §pycomplete-9 ruled the shared-worker route a silently wrong
answer for the VIEWS, and that ruling **does not extend here** — the reason is
the RETURN TYPE. A pure plan admitting `.keys()` can only answer a VALUE, and
the only value available is a snapshot. `enumFrame` answers a **`GenFrame`** —
an address plus a cursor — which *is* the live object. The constraint and
correctness pointed in opposite directions for 3c-i-b; here they point the
same way.

### The price, by the `enumList` precedent — the frame it is modelled on

`enumDict (i : Int) (a : Addr) (cur n sv : Nat)` sits beside `enumList`, which
is already the live-cursor-over-an-address frame, and `n`/`sv` are 3a's two
guards. `enumList` is not a hypothetical sibling: `gen_lab::enum_list` walks
`for i, v in enumerate(xs)` over a HEAP LIST today, through `forGen` over a
heap-pushed `.generator "<enumerate>"`. The dict case is that path with a
different step decision.

| site | file | what |
| --- | --- | --- |
| constructor | `Runtime.lean` §generator continuations | one arm beside `enumList` |
| well-formedness | `Runtime.lean` `GenFrame` addr guard | `a < h.size` |
| ingestion | `Semantics.lean` `enumFrame` | the dict arm, replacing the refusal |
| classifiers ×2 | `Semantics.lean` (the two `Option.none` GenCont rows) | one pattern each |
| step | `Monadic/Eval.lean` `execGen` | reuse `dictStep … .keys` — all three regimes already decided; the `(i, k)` tuple is the FRAME's, not the cursor's, so `DictViewKind` gains nothing |
| step (trunk) | `Semantics.lean` `stepIter` | one arm, REFUSING — the `.forDict` template sits directly above it |
| `PayloadBlind` / `ClockErase` / `Obs` | one arm each | mechanical; the obligations are checked below and all four are free |
| `VCGen` | `GenSteps` / `GenSilent` | two transition theorems, if `enumList`'s precedent is kept |

**Where the executable capability lands, and where it does not.** The
rebuild's `execGen` STEPS the frame; the trunk's `stepIter` REFUSES it — the
arrangement §pycomplete-5 sanctioned for 3a, and the one the current split
states outright (*executable behaviour is the rebuild's, proved behaviour is
still the trunk's*). The template is already at the very site the new arm lands
beside: *"this interpreter never CONSTRUCTS a `forDict` frame … the arm exists
to compile and to refuse, and gains no consumers"*. One definition of
`enumFrame`, one place that steps it, and no duplicated decision.

**The trunk-side proof obligations were CHECKED, not assumed**, because
ruling (c) below makes the trunk BUILD the frame and `enumFrame` is a heap
reader. Every consumer of `enumFrame` was read, and all four are free:

* `PayloadBlind.enumFrame_swapAt` proves the frame blind, and the new dict arm
  reads `es.size` and `shapeVersion` out of a heap object — payload, on the
  face of it. It still closes with the proof it already has: `PayloadTwin o₀ o`
  requires BOTH sides to be `.generator q _ _ .running`, so
  `Heap.get?_swapAt_twin`'s twin branch lands on `enumFrame`'s GENERATOR arm on
  both sides, and the dict arm is reachable only in the branch where the two
  lookups are literally equal. **The swapped slot can never hold a dict** —
  §pycomplete-1's rung-3b argument, unchanged, at a different worker.
* `ClockErase` and `PayloadBlind` reach the `enumerate` arm through
  `cases … : enumFrame …`, which splits on the `Res` RESULT, not on the
  receiver's constructor. A new arm returning `.ok` adds no goal; it lands in
  the `.ok` branch that already exists.
* `Monadic/Spec.lean` owes nothing either: `dictStepM_spec` is stated for an
  arbitrary `kind` and arbitrary `(a i n sv)`, so the new frame's step inherits
  the `@[spec]` lemma — *"a cursor step must not disturb the dict it is
  walking"* — the moment it is written in terms of `dictStepM`.
* `Obs` never reaches it at all: `enumerate` is carved out of the `heapFree`
  fragment SYNTACTICALLY (`(fname == "enumerate") = false`), beside `sorted`,
  `next`, `count`, `any` and `all`.

So the §pycomplete-1 law does not fire at the CONSTRUCTION site, and the
reason is worth keeping: the law charges for a refusal OTHER PROOFS WERE
STANDING ON. These four were standing on the frame's SHAPE (`Res`, and a twin
that cannot be a dict), not on its refusal — and shape is what the new arm
preserves. The law WOULD fire at the STEP site, which is exactly why the
trunk's `stepIter` keeps refusing: three walkers stand on that one.

### THE DECISION THE CENSUS SURFACED — RULED, and the ruling is (c)

`.forDict`'s template is not a perfect fit, and the difference had to be
settled before a ticket was spent on it. The trunk never BUILDS a `forDict`
frame; it WOULD build an `.enumDict` one, because `enumFrame` is shared. So a
trunk `e = enumerate(d)` that is never stepped answers an object where it
refuses today, and only the first step refuses. Three ways out were on the
table: (a) decide in the trunk too — the three real proof arms above;
(b) refuse in the `enumerate` builtin arm BEFORE `enumFrame`; (c) accept the
delta and WITNESS it.

**Ruled (c).** The reasons, in the order that decides them:

* **The delta is a capability OPENING, not a regression.** CPython answers an
  object at `e = enumerate(d)` too — measured: binding is silent, `type(e)` is
  `'enumerate'`, and growing the dict afterwards raises NOTHING until a step.
  A tier that starts answering there moves TOWARD the oracle. There is nothing
  to defend against; there is a row to write.
* **(b) is §pycomplete-9's warned shape.** A refusal placed before
  `enumFrame` is a SECOND decision site for one construct — the defect that
  entry exists to name, and the same defect §pycomplete-11 had to name a third
  decision site to avoid hiding.
* **(a) buys nothing the oracle does not already answer.** Three trunk proof
  arms is §pycomplete-1's real price, and it is worth paying for a case where
  the trunk's answer is the one under proof. Here the oracle answers, the
  rebuild is what executes, and the arms would certify a decision no runner
  reaches.

So the delta is DECLARED and CARRIED BY A WITNESS, not suppressed — which is
the same move `dict.view-escapes` made for 3c-ii and `star_dict` made for
rung 3b: the boundary is falsifiable rather than asserted.

**The witness cannot be `print(e)`** — CPython answers
`<enumerate object at 0x109333e00>`, an ADDRESS, and printing a value the tier
cannot render exactly is already `set.order`'s refusal class. The spellings
that carry the ruling and are address-free are `print(type(e).__name__)` →
`enumerate`, and the never-stepped mutation row, which prints its own marker
and must NOT raise.

### What 3c-i-c does NOT cover, named so it is not silently assumed

* `enumerate(d.items())` / `enumerate(d.values())` — 3c-i-b's
  `consumesViewArg` deliberately EXCLUDES `enumerate`, because an `enumerate`
  object outlives its call and the rewrite's snapshot is licensed by the shape.
  Composing the view kind with this cursor is its own inch.
* `dict(d.items())` — `dict` is likewise absent from `consumesViewArg`;
  §pycomplete-8 listed it as a 3c-i target and §pycomplete-11 did not land it.
* `enumerate(d, start=5)` — the keyword spelling. `enumStart` reads positional
  arguments only, so this stays `kwargs.callee-kind`.
* `enumerate(d) == enumerate(d)`, `len`, `reversed` — 3c-ii's first-class
  territory, and the identity-equality row is `d.values()`'s row again.

### Battery — FIVE rows, named by CONSTRUCT, expectations written by the ORACLE

Every source below is the SPELLING a program would contain, and every
expectation is CPython 3.9.19's own.

| witness | source | CPython | after the inch |
| --- | --- | --- | --- |
| `dict.enumerate` (exists, the marker) | `for i, k in enumerate(d): print(i, k)` | `0 x` / `1 y` | REFUSE → **MATCH** |
| `dict.enumerate-start` | `print(list(enumerate(d, 5)))`, and `-3` beside it | starts at 5 / at −3 | **MATCH** — the start is an `int` |
| `dict.enumerate-escapes` | `e = enumerate(d)` / `d[2] = 'b'` / `print(type(e).__name__)` | `enumerate`, and NO error | **MATCH** — this row IS the ruled delta |
| `dict.enumerate-resize` | `e = enumerate(d)` / `d[2] = 'b'` / `print(next(e))` | `RuntimeError: dictionary changed size during iteration` | **MATCH** — raises, never snapshots |
| `dict.enumerate-of-items` | `print(list(enumerate(d.items())))` | `[(0, ('x', 1)), (1, ('y', 2))]` | **MATCH** — the enum cursor carries the live `.items()` view kind |

`dict.enumerate-escapes` and `dict.enumerate-resize` are the SAME two
statements with a different third line, and that is deliberate: the pair is
what makes the ruling falsifiable. Binding and mutating must be silent;
STEPPING after the mutation must raise. A model that guarded at bind time
would pass the second and fail the first, and a model that snapshotted would
pass the first and fail the second. Neither can pass both by accident.

One further measurement, recorded because it constrains the step arm and is
satisfied BY CONSTRUCTION rather than by a guard: after exhaustion the size
check stops applying — `e = enumerate(d); list(e); d[2] = 'b'; list(e)` answers
`[(0, 'a')]` then `[]`, not a `RuntimeError`. The frame is popped at
exhaustion, so an exhausted generator never re-reads the dict. A model that
kept `n` live past the end would raise where CPython answers `[]`.

## 2026-08-23-pycomplete-14 — INCH 3c-i-c BUILT: `enumerate(d)` runs, and the census's price held exactly

`for i, k in enumerate(d)`, `enumerate(d, 5)`, `enumerate(d, -3)` and the
escaped-then-stepped forms all run, on a new `GenFrame.enumDict` frame beside
`enumList`. §pycomplete-13 priced this at nine sites and ZERO new `Kont`
machinery; the price held, and two further sites turned out to owe nothing.

### What landed, against the censused site list

| site | what |
| --- | --- |
| `Runtime.lean` | `enumDict (i : Int) (a : Addr) (cur n sv : Nat)`, and its `a < h.size` WF arm |
| `Semantics.lean` `enumFrame` | the dict arm DECIDES — `.ok (.enumDict i a 0 es.size sv)` |
| `Semantics.lean` ×2 | `genBreak`/`genContinue`: a builtin-iterator frame is never a LOOP frame |
| `Monadic/Eval.lean` `execGen` | the step: `dictStepM ad cur n sv .keys`, tuple wrapped at the frame |
| `Semantics.lean` `stepIter` | the trunk REFUSES the step (ruling (c)) |
| `PayloadBlind` / `ClockErase` / `Obs` | one refusal-is-blind arm each |

### The two sites that owed NOTHING, and why that is the interesting half

* **`Monadic/Script.lean` needs no `SKont` field.** A module-level
  `for i, k in enumerate(d)` routes `S.forGen → K.stepIter → execGen` and
  lands on the new arm. §pycomplete-13 said `enumerate` is an OBJECT the loop
  consumes rather than a loop the interpreter drives; the script shell is the
  second record that would have paid for the other reading, and it pays
  nothing. **The finding generalised further than it was stated.**
* **`VCGen.lean` owes no transition theorem.** `genSteps_enumListCons` and
  `genSilent_enumListDone` exist because the trunk STEPS an `enumList` frame.
  The trunk refuses to step `enumDict`, so there is no transition to state —
  a refusal has no `GenSteps` and no `GenSilent`. The censused "optional" is
  now decided: not optional, INAPPLICABLE.

### A witness that would have tested the wrong construct

§pycomplete-13's battery spelled the never-stepped row
`print(type(e).__name__)`. **`type` is in `isPyBuiltinName` and NOT in
`isBuiltinName`** — CPython binds it, the model does not implement it — so
that row would have refused at `type` and been recorded as evidence about
`enumerate`. Caught by reading the two tables before the ticket rather than
by a red build. Re-spelled as `print('bound')`: reaching the print IS the
observation, because CPython's guard is on the step and binding is silent.
**A witness must fail for the reason it names**, and the census's own rule —
witnesses named by CONSTRUCT — does not by itself guarantee that; the
spelling has to be in tier too.

For the same reason `enum_dict_grow_is_loud` was renamed
`enum_dict_grow_then_step` before landing: it named a VERDICT, and the
verdict it named was wrong — the tier REPRODUCES CPython's `RuntimeError`
here (as `dict.grow-during-iter` already did for the bare cursor) rather than
refusing it.

### THE ENVELOPE OUTGREW THE ELABORATOR, and the error did not look like itself

`load_program` builds the module as a LITERAL through the derived `ToExpr`
instances, so the elaborator's recursion depth scales with the ENVELOPE.
`dict_lab` is now the largest in the tree — **611 KB, 101 functions**, against
`gen_lab`'s 272 KB and 53 — and it crossed the default `maxRecDepth` of 512
somewhere between §pycomplete-18's 85 functions (green) and this inch's 101.
Fixed with `set_option maxRecDepth 65536 in` at the `load_program`, the
established precedent (`clock_lab`, `sf_order` use 100000).

**The diagnosis cost far more than the fix, and the reason generalises.** The
recursion limit is hit at the `load_program` line; `dict_lab` is then added
UNCOMPILED; and all ~44 downstream `#guard`/`#py_check` lines report
*"depends on 'dict_lab', which is 'noncomputable'"*. **The visible errors are a
different failure class than the cause**, and they are individually plausible —
they read as "something in the new Python is noncomputable", which sent this
lane hunting generator expressions and `ToExpr` instances. The only error naming
the cause is the FIRST one.

> **A cascade's first error is the causal one, and every later error is
> evidence about the cascade rather than about the defect.**

**AND THE TRIAD'S SUMMARY OMITTED IT** — a finding for the tool, measured
against the kept full log. The summary announced *"first 8 of 46"* and listed
six errors at `spec.lean:102-139`. The full log's FIRST error is
`spec.lean:24:0: maximum recursion depth has been reached`; its LAST are
`spec.lean:140-143`. **The summary showed neither the head nor the tail, and
dropped the only line of a different class.** Truncation would have been
harmless; a labelled-but-unfaithful sample is not, because the surviving lines
are a coherent wrong story. The recommendation is one line: whatever else it
samples, the summary must print the FIRST error verbatim.

### Census deltas

* grammar census **113 → 117 witnesses**; `dict.enumerate` flips
  **REFUSE → MATCH**, joined by `dict.enumerate-start`,
  `dict.enumerate-escapes` and `dict.enumerate-resize` (MATCH) and
  `dict.enumerate-of-items` (MATCH — the enum cursor carries the live view kind).
* `harness/cases.json` **655 → 660 rows**, all five `match`, so
  `diff_test` goes **1456 → 1464 cases** (`1337 → 1345 matched`) with
  `119 whitelisted-unsupported` UNCHANGED — this inch adds capability
  without adding a gap.

  **That number was predicted WRONG before the ticket, and the verdict
  corrected it: 1461 was the prediction, 1464 is the measurement.** A ROW is
  not a CASE — a row carries an `args` LIST, and `diff_test` runs one case per
  arg-tuple, so three of the five rows are two cases each. Same shape as the
  conflation `6b91a8d` recorded when the model's §5.2 `class` was compared
  against `WHITELIST_CLASS`: two counts sharing a noun are not the same count.
  Recorded rather than quietly edited, because §5.4a's rule is that a
  published number is a second artifact — and the corrected one is the
  measurement, not the arithmetic.
* the whitelist census stays **119 rows in 46 classes** and the script census
  **15 rows in 10 classes**, for the same reason.

### What did NOT move

`enumerate(d.items())` still refuses: 3c-i-b's `consumesViewArg` excludes
`enumerate` because the object outlives its call. `dict(d.items())` is still
unlanded. `enumerate(d, start=5)` is still `kwargs.callee-kind`. The
first-class rows — `enumerate(d) == enumerate(d)`, `len`, `reversed` — remain
3c-ii's. And sunfish is untouched: its `enumObj` is `.enumSeq` over a string
snapshot, a different frame entirely.

**§pycomplete-13's "its dict arm is today's refusal" is superseded by this
entry**, and the date on each is what separates them.

## 2026-08-23-pycomplete-15 — THE FLAGSHIP LADDER's CENSUS: `del d[k]` makes a refusal REQUIRED that was only inherited

The R-track measured `bound()`'s AST down to **two refused constructs, both
`TABLE_SIZE` eviction lines**, and both are this lane's live-dict-iteration
family:

    541:  del self.tp_score[next(iter(self.tp_score))]
    511:  del self.tp_move[next(k for k in self.tp_move if k != self.root)]

Both are `del d[<expr>]`, so **inch (1) is the shared dependency** and the
other two are the two ways of producing the key. Censused on CPython 3.9.19
before any design, in the source spelling.

### THE FINDING, and it fires a cross-rung note written two rungs ago

§pycomplete-1 recorded that the same-size KEY-SET CHURN regime *"is
unreachable today only because `del d[k]` refuses first, and becomes REQUIRED
the day dict deletion lands."* **That day is inch (1), and the census now
proves the refusal must stay.**

| churn shape (same size: one `del`, one insert, mid-iteration) | CPython 3.9.19 |
| --- | --- |
| churn at the middle key of 3 | `RuntimeError: dictionary keys changed during iteration` |
| churn at the **first** key of 3 | **no error — the loop completes** |
| churn at the last key of 3 | `RuntimeError: dictionary keys changed…` |
| `del d[2]; d[2] = 9` (same key back) | **no error** |
| 1-key dict, del + add | `RuntimeError: dictionary keys changed…` |
| 8-key dict, churn at key 3 | `RuntimeError: dictionary keys changed…` |
| churn then `break` immediately | **no error**, `[1, 3]` |

**The first probe raised, and a one-probe census would have concluded the
regime is a faithful second `RuntimeError` and told the inch to reproduce
it.** Four shapes later it does not raise at all, and what separates them is
the entries-array layout and the compaction schedule — exactly what
`Semantics.lean`'s `rekeyed` arm already says is not guessable. So the
existing refusal is CONFIRMED BY MEASUREMENT rather than merely inherited,
and inch (1) must keep it while making it reachable for the first time.
*A regime that only ever raised in the probe you happened to write is the
most dangerous kind of green.*

### `del d[k]` — the rest of the oracle's column

| probe | CPython |
| --- | --- |
| `d = {1:'a',2:'b'}; del d[1]` | `{2: 'b'}` |
| `del d[9]` (absent) | `KeyError: 9` — and twice-deleted, and on `{}`, likewise |
| `del d[2]; d[2] = 'z'` | `[1, 3, 2]` — **reinsertion APPENDS**; deletion does not hold the slot |
| `del d[k]` inside `for k in d` | `RuntimeError: dictionary changed size during iteration` |
| `e = d; del e[1]` | `{2: 'b'}` — mutation through the alias, the heap shape the tier already has |

So the value semantics are cheap: remove the entry, and reinsertion is
`dictStore`'s existing append. **`shapeVersion` is the load-bearing half** —
deletion must BUMP it, or the churn guard above cannot fire (a `del` + insert
pair leaves the size unchanged, and size is the only guard that fires today).

### The price: inch (1) touches all THREE decision sites

`delStmt (names : Array String)` cannot represent a subscript target, and the
refusal is upstream of the AST: `Json.lean`'s `"Delete"` arm reads a plain
string array because **the EXTRACTOR's clause 4 admits BARE NAMES only** and
ships everything else as `Unsupported`. So this inch is the extractor, the
ingestion, and the evaluator — the first inch to touch all three sites
§pycomplete-11 named. The additive shape keeps the existing tier untouched: a
new `delSubscript (recv key : Expr)` beside `delStmt names`, so no landed
`del` behaviour moves. `del_lab::del_sub` is the witness that flips.

### Inches (2) and (3) — cheaper, and the 3c-i-c precedent transfers whole

| probe | CPython |
| --- | --- |
| `next(iter(d))` on `{2:'b',1:'a'}` | `2` — insertion order |
| `it = iter(d); next(it), next(it)` | `2 1` |
| `next(iter({}))` | `StopIteration` |
| `next(iter(d), -1)` on `{}` | `-1` — the 2-arg form |
| `type(iter(d)).__name__` | `dict_keyiterator` |
| `it = iter(d); d[2]='b'; print('bound')` | `bound` — **silent** |
| `it = iter(d); d[2]='b'; next(it)` | `RuntimeError: dictionary changed size…` |
| `next(k for k in d if k != root)` | `2`; no match → `StopIteration`; with default → the default |
| `g = (k for k in d); d[3]='c'; next(g)` | `RuntimeError` — the genexp is LAZY and LIVE over the dict |

**That bind-silent / step-raises pair is `dict.enumerate-escapes` and
`dict.enumerate-resize` again, unchanged**, so 3c-i-c's frame is the
precedent for both: an `iterDict` frame is `enumDict` without the index, and
the genexp already has a cursor class. Two cheap notes: `next` ALREADY
implements both the 1-arg and 2-arg forms, so inch (2) gets `next(it, d)`
free; and **`iter` is in `isPyBuiltinName` but NOT in `isBuiltinName`** — the
same two-table gap §pycomplete-14 was caught by — so inch (2) must add it to
the implemented list, deliberately and with the `NameError` consequence in
view.

### The sequencing, and why the flagship's own lines are SAFE

In both flagship lines the `next(...)` is evaluated to a key and the iterator
is then ABANDONED before `del` runs, so the mutation never meets a live
cursor. `del d[next(iter(d))]` answers `{2: 'b'}` and `del d[next(k for k in
d if k != root)]` answers `{1: 'a'}` — measured. The hazard the guards exist
for is real but is not on the flagship's path, which is the honest reason
these are inches rather than walls.

## 2026-08-23-pycomplete-16 — `del d[k]` LANDS as an ingestion rewrite, and the churn guard becomes REQUIRED

`del d[k]` runs, on the flagship's two eviction lines' shared dependency. The
census (§pycomplete-15) priced a `delSubscript` statement constructor; the
re-census before building priced the **`Stmt`-constructor tax** and the design
changed.

### The re-census that changed the shape, and the number that forced it

A new `Stmt` constructor is not one site. **`delStmt` has 28 occurrences
across 9 files; `assertStmt`, the closest precedent, has 22 across 8** — arms
in `heapFree`, the size/termination measure, span extraction, kind naming,
lowering, parsing, plus `Obs`/`PayloadBlind`/`ClockErase`. All mechanical, and
**none of them decide anything.**

So `del d[k]` lowers to **`<dictdel>(d, k)` under an `exprStmt`** — the THIRD
DECISION SITE this lane named in §pycomplete-11, reused. Six sites instead of
twenty-five: the extractor's clause 4, the ingestion arm, the synthetic name,
`callNamePlan`, `applyBuiltin`, and the two pure workers. **Zero `Stmt`
constructors, zero walker arms.** `del` is a statement with NO VALUE and
`exprStmt` DISCARDS the value, so the lowering is exact rather than
approximate, and the name can never appear in expression position because
ingestion emits it only from a `Delete` node — the same argument that licenses
`<dictkeys>`.

*"Re-census when the plan becomes expensive" earned its keep here: the rule
fired on a 4× price difference and the answer was already in this lane's own
toolkit.*

### THE CHURN GUARD IS NOW REQUIRED, and a one-probe census would have inverted it

§pycomplete-1 predicted that same-size key-set churn *"becomes REQUIRED the
day dict deletion lands."* That day is this inch. **The first churn shape
measured raised** `RuntimeError: dictionary keys changed during iteration` — a
faithful second message the tier could plausibly reproduce. Three shapes later
it does not raise at all:

| shape | CPython | tier |
| --- | --- | --- |
| churn at MIDDLE key | `RuntimeError: keys changed` | REFUSE |
| churn at FIRST key | **silent**, answers 102 | REFUSE |
| `del d[2]; d[2]=9` | **silent**, answers 3 | REFUSE |
| churn then `break` | silent, answers 1 | **MATCH** |

What separates them is the entries-array layout and compaction schedule, so
the regime stays LOUD and `dict.keyset-churn` is its class. **The three silent
shapes are honest REFUSEs**: the model refusing where CPython answers is a
witnessed capability gap, and CPython's answer is recorded in each row's
comment so the expectation column stays oracle-written. A MATCH there would
require answering through an unguessable layout — the snapshot sin again.

**The one MATCH is `del_churn_then_break`, and not because CPython was
silent.** `dictStepM` runs at the TOP of each iteration, so the guard fires
only on RE-ENTRY; `break` exits before the cursor re-reads and the guard is
never reached. *Two rows can agree with CPython for entirely different
reasons, and the row that says which is the one worth keeping.*

### `shapeVersion` is the load-bearing half

Deletion bumps it UNCONDITIONALLY, where `heapStore` bumps only on growth, and
the why is in the code: `del d[x]` followed by `d[y] = v` in one loop body
leaves `es.size` exactly as it was, so SIZE — the only guard that fires today
— stays silent and the churn would be walked as if nothing happened. Value
semantics are cheap by comparison: deletion does not hold the slot, so
reinsertion APPENDS (`del d[2]; d[2]='z'` lists `[1, 3, 2]`) and the entries
array stays exactly the insertion sequence every cursor in the file reads.

### The boundary is falsifiable

The rewrite is SYNTACTIC — it lowers `del o[k]` for any receiver — so the type
check lands in the arm, as it does for the view builtins.
`dict_lab::del_list_item` is now the witness for the landed H2 list
deletion path: CPython deletes the item and the tier mutates the heap list.
Negative indices and the faithful `IndexError`/non-integer `TypeError` are
covered by the adjacent battery rows. `del xs[1:]` is excluded
at extraction: a slice deletes a RANGE, a different operation.

### An inherited wart, named rather than replicated silently

A synthetic name reaching the TRUNK's name resolution is in neither
`isBuiltinName` nor `isPyBuiltinName`, so at module scope with complete
globals the trunk would decide a `NameError` CPython never has. This is
**inherited from §pycomplete-11**, not introduced here — `<dictkeys>` has had
it since 3c-i-b — and it is unobserved because the trunk is not the runner and
no proof exercises it. Recorded so the next audit finds it from either end;
the fix is one arm in the trunk's resolution, and it belongs to whichever inch
next has reason to open that file.

### Census deltas

* grammar census **117 → 122 witnesses**: `del.dict-key`,
  `del.dict-missing`, `del.dict-reinsert-order` (MATCH), `del.dict-churn` and
  `del.non-dict-receiver` (now MATCH).
* `harness/cases.json` **660 → 674 rows**. `del_lab::del_sub` FLIPS
  `unsupported → match` and LEAVES `WHITELIST_CLASS`; four new gaps join it —
  `del.non-dict-receiver` now MATCHES, with three new list deletion
  differential rows and three `dict.keyset-churn` refusals.
* `docs/memory-model.md` updated in three places: the H1 dict inventory, the
  `del` construct paragraph, and the cross-rung churn note that predicted
  this inch.

## 2026-08-24-pycomplete-17 — INCH (2)'s CENSUS: `iter(d)` arrives at the EVALUATOR, and it is the THIRD generator allocator

Inch (2) of the flagship ladder is `iter(d)` + `next` over dict keys — the key
half of `del self.tp_score[next(iter(self.tp_score))]` (sunfish.py:541), whose
`del` half landed as §pycomplete-16. Censused on CPython 3.9.19 and against the
tree before any design.

### THE FIRST FINDING, and it inverts inch (1)'s shape

Inch (1)'s answer was an INGESTION REWRITE: `del d[k]` could not arrive any
other way, because `delStmt` admits bare names and the refusal was upstream of
the AST. **Inch (2) is the opposite, and the extracted envelope says so
outright.** `iter(d)` comes out of the extractor as an ordinary
`Call(Name "iter", [Name "d"])` — no `call_unsupported`, no new node kind —
and `Json.lean` ingests it unchanged. The construct arrives at the
**EVALUATOR**, and the whole inch is one builtin arm plus one frame.

The reason is worth keeping, because it is the rule and not the accident:
**an ingestion rewrite is available exactly when the construct's meaning is
decided by SYNTAX.** `del o[k]` names its receiver syntactically and `del` has
no value, so `<dictdel>(o, k)` is exact. `iter` is a SHADOWABLE name whose
meaning depends on its argument's runtime TYPE — `list_iterator`,
`str_iterator`, `dict_keyiterator`, or the generator itself — and ingestion
sees neither the binding nor the type. A rewrite there would be a guess.
*The third decision site is a tool, not a default.*

### THE SECOND FINDING, and it is the one that would have gone wrong

`Expr.genAllocFree`'s docstring reads *"Only two shapes can allocate an
`Obj.generator` … a call of `enumerate` or `count`"*. **`iter` is the third**,
and nothing in the §pycomplete-15 price sheet predicted it. The consequence is
not a missing feature but a WRONG LOUD ANSWER: `moduleGenFree` would classify a
module holding an `iter` cursor as generator-FREE, and

    d = {2: 'b', 1: 'a'}
    for k in iter(d):
        print(k)

would report ordinary Python as *"internal: a generator object in a module
with no generator defs (heap well-formedness violation — report this)"* — the
2026-08-13 `tools/leanpy` incident, verbatim, at a new builtin. The witness
`dict.iter-for` exists to convict exactly that, and it is a MATCH only because
the census read the docstring that names the closed list.

`Expr.heapFree` needed the same carve-out for a DIFFERENT reason, and the two
must not be conflated. The trunk refuses `iter` entirely, so world-preservation
is safe there; but `funsHeapFree` is also the guard `callNamePlan` reads to
conclude that *a local holding a `.ref` in a heap-free module must be a DICT*
(closures allocate, so there can be none). An `it = iter(d)` that left the
fragment intact would falsify that, and `it(0)` would name the wrong type in an
otherwise faithful `TypeError`. **Two allocator censuses, two arguments, one
line each.**

### The oracle's column, in the source spelling

| probe | CPython 3.9.19 |
| --- | --- |
| `next(iter({2:'b',1:'a'}))` | `2` — insertion order |
| `it = iter(d); next(it), next(it)` | `2 1` — ONE cursor |
| `next(iter({}))` / `next(iter({}), -1)` | `StopIteration` / `-1` |
| `type(iter(d)).__name__` | `dict_keyiterator` |
| `it = iter(d); d[2]='b'; print('bound')` | `bound` — **silent** |
| `it = iter(d); d[2]='b'; next(it)` | `RuntimeError: dictionary changed size…` |
| `it = iter(d); del d[1]; next(it)` | the same `RuntimeError` — shrink is size too |
| `it=iter(d); jt=it; next(it), next(jt)` | `1 2` — identity, one shared cursor |
| `for k in iter(d)` / `list(iter(d))` | `2 1` / `[2, 1]` |
| `del d[next(iter(d))]` | `{2: 'b'}` — **the flagship line** |
| `iter([7,8])`, `iter('xy')`, `iter((5,6))`, `iter(range(3,9))`, `iter({4})` | all answer, each a DIFFERENT iterator type |
| `iter(g) is g` | `True` — a generator is its own iterator |
| `iter(3)` | `TypeError: 'int' object is not iterable` |
| `iter()` | `TypeError: iter expected at least 1 argument, got 0` |
| `iter(d, 0)` | `TypeError: iter(v, w): v must be callable` |
| `iter(lambda: 1, 1)` | a `callable_iterator` — a second OBJECT KIND |

### THE THIRD FINDING: the churn regime is TWO CPython rules, and now both are named

§pycomplete-15 measured the same-size key-set churn regime through a `for`
loop and concluded *"the entries-array layout is what separates them"*. Driving
the SAME regime through an explicit `iter`/`next` cursor splits that sentence
into two facts, because the cursor can be positioned anywhere:

| shape (`d = {1,2,3}`, one `del`, one insert, size unchanged) | CPython 3.9.19 |
| --- | --- |
| churn after yielding key **1** | `1, 3, 9` — **silent** |
| churn after yielding key **2** | `1, 2, 3` then `RuntimeError: dictionary keys changed…` |
| churn **before** any `next` | `2, 3, 9` — **silent** |
| churn, then the iterator RUNS OFF the end | `RuntimeError: dictionary keys changed…` |
| 8-key dict, churn at key 3 | `0,1,2,4` — silent |

`dictiter_iternextkey` raises *"changed size"* on `di_used != ma_used` — a SIZE
check the model has — and raises *"keys changed"* at the point CPython's own
source comments *"We found an element (key), but did not expect it"*: `di_len`
has reached **zero** while a live entry still lies ahead of the cursor. So the
`for` table's four shapes were four samples of one two-part rule, and the
`iter` spelling is what made the parts separable.

**The refusal is therefore not a coarse approximation of one rule; it is the
honest answer to two.** A model carrying `di_len` alone would answer where
CPython is silent; one carrying the tombstoned array alone would be silent
where CPython raises. Both, together, or LOUD — and LOUD is what stays.
*A regime you have only ever probed from one cursor position is a regime you
have measured once.*

### A fourth measurement, recorded because it constrains the frame

Exhaustion is **discovered, not implied**:

    d = {1:'a'};  it = iter(d);  next(it)   # yields 'the last key'
    d[2] = 'b';   next(it, -1)              # RuntimeError — the iterator is STILL LIVE

    d = {1:'a'};  it = iter(d);  next(it);  next(it, -1)   # RUNS OFF: -1
    d[2] = 'b';   next(it, -2)                             # -2 — silent, it is DEAD

CPython clears `di_dict` at the step that finds the end, and only then stops
guarding. A frame popped at the LAST YIELD would answer `-1` where CPython
raises; one never popped would raise where CPython answers `-2`. The
`enumDict` precedent already pops on `.done`, so both fall out — but they fall
out of WHERE the pop happens, which is why the pair is a witness and not a
comment.

### THE PRICE — nine frame sites, and the two that were not on the sheet

| site | file | what |
| --- | --- | --- |
| constructor | `Runtime.lean` §generator continuations | `iterDict (a cur n sv)` beside `enumDict` |
| well-formedness | `Runtime.lean` `GenFrame.WF` | `a < h.size` |
| classifiers ×2 | `Semantics.lean` `genBreak`/`genContinue` | one pattern each |
| worker | `Semantics.lean` `iterFrame` | new, beside `enumFrame` |
| step (rebuild) | `Monadic/Eval.lean` `execGen` | `dictStepM … .keys`, yielding the BARE key |
| step (trunk) | `Semantics.lean` `execGen` | one arm, REFUSING |
| `PayloadBlind`/`ClockErase`/`Obs` | one arm each | mechanical, and all three are the `enumDict` arm verbatim |
| builtin arm | `Monadic/Eval.lean` `applyBuiltin` | `iter` |
| builtin table | `Ast.lean` `isBuiltinName` | `+ "iter"`, 22 → **23 names** |
| **allocator census 1** | `Semantics.lean` `Expr.genAllocFree` | **not on the sheet** — see above |
| **allocator census 2** | `Semantics.lean` `Expr.heapFree` (+ the one `Obs.lean` destructuring) | **not on the sheet** — see above |
| lowering table | `Json.lean` `lowerBuiltins` | `+ "iter"`, the two-table gap closed at the third table too |

**`VCGen` owes nothing** and `Mono.lean` owes nothing, for §pycomplete-13's
reason unchanged: the frame is consumed through `stepIter`/`execGen`/`forGen`,
all of which are existing `Kont` fields, and the trunk refuses to step it, so
there is no transition theorem to state. `Monadic/Spec.lean` owes nothing
either — `dictStepM_spec` is stated for an arbitrary `kind` and arbitrary
`(a i n sv)`, so the new frame inherits it the moment it is written in terms of
`dictStepM`.

### The ruling §pycomplete-13 had to make, and why this inch has nothing to rule

3c-i-c had to choose between three ways of handling a TRUNK that builds a frame
it will not step, because `enumFrame` is SHARED. Here the trunk has **no `iter`
arm at all** — `iter` falls through its positional chain to `isPyBuiltinName`
and refuses as an unmodelled builtin, exactly as it did before this inch. So
`iterFrame` has one caller, the trunk never constructs the frame, and its step
arm is `forDict`'s: *"exists to compile and to refuse, and gains no consumers"*.
No capability delta, no witness to carry one, no `Obs.lean` branch to rewrite
away. **The cheaper arrangement was available because the trunk was silent, and
the census is what noticed the difference rather than transliterating (c).**

### What inch (2) does NOT cover, named so it is not silently assumed

* `iter` over a **list / str / tuple / range / set** — CPython answers, with a
  distinct iterator TYPE and a distinct mutation regime for each.
  `dict.iter-of-list` is the falsifiable witness; each is its own inch.
* `iter(g)` over a generator — CPython answers `g` ITSELF (`iter(g) is g`).
  Cheap, exact, and still out: it is a different RETURN (a `.ref`, not a
  frame), so it would be a second shape in one arm.
* `iter(d.keys())` — `consumesViewArg` excludes `iter` for `enumerate`'s
  reason: the cursor OUTLIVES the call, so the rewrite's snapshot is not
  licensed. Composing the view kind with this cursor is its own inch.
* `iter(v, sentinel)` — a `callable_iterator`, a second object kind.
* An ERROR-STATE gap, inherited and named below.

### AN INHERITED WART, MEASURED: CPython's iterator error state is STICKY

    d = {1:'a'};  it = iter(d);  d[2] = 'b'
    try:    next(it)
    except RuntimeError: pass
    next(it, 'DEFAULT')      # CPython: RuntimeError AGAIN. The model: 'DEFAULT'.

`dictiter_iternextkey` sets `di_used = -1` and CPython's own comment calls it
*"sticky"*; the model's `stepIterAt` CLOSES the generator when an exception
propagates out, and a closed generator answers `next`'s default. **"Dead" and
"poisoned" are different states, and the model has only one of them.** This is
**inherited from §pycomplete-14** — `enumDict` has had it since 3c-i-c and it
was not measured then — not introduced here; the fix is a `GenStatus`
constructor, which is a `Kont`-adjacent price and belongs to whichever inch has
reason to open that file. Recorded rather than replicated silently, and
deliberately NOT given a witness row: the census records measured verdicts, and
a row here would be a `DIVERGE`.
Interestingly the OTHER message is not sticky — after *"keys changed"* CPython
clears `di_dict` and the iterator merely dies — so the two RuntimeErrors differ
in aftermath as well as in cause.

### Battery — sixteen typed-call rows and ten witnesses, expectations ORACLE-written

Every source is the SPELLING a program would contain and every expectation is
CPython 3.9.19's own. Three rows are REFUSES and each names what CPython
answers: `iter_churn_still_loud` (CPython answers 4, silently),
`iter_list_recv_still_loud` (CPython answers 7), `iter_sentinel_still_loud`
(CPython raises `TypeError`). The falsifiable PAIRS are
`iter_bind_then_grow`/`iter_grow_then_step` (the guard is on the step) and
`iter_last_key_then_grow`/`iter_ran_off_then_grow` (exhaustion is discovered).

## 2026-08-24-pycomplete-18 — INCH (2) BUILT: `iter(d)` + `next` runs, and the price held except where the census caught it

`next(iter(d))` runs, and with it `for k in iter(d)`, `list(iter(d))`, the
aliased cursor, and **the flagship's whole line** — `del d[next(iter(d))]`
answers `{2: 'b'}`, which is inch (1) and inch (2) meeting on sunfish.py:541.

### What landed, against the censused site list

Nine frame sites, the builtin arm, the builtin table — all as priced. The two
sites the price sheet did NOT have are the two allocator censuses
(`Expr.genAllocFree`, `Expr.heapFree`), and they are the whole reason this inch
was censused against the tree rather than transliterated from `enumDict`.
**The `enumerate` precedent transfers at the FRAME and not at the MODULE.** A
new frame is nine mechanical arms; a new ALLOCATOR is two closed lists that
name their members, and a docstring is the only thing that says so.

### Three consumers that owed nothing, and that is the interesting half

`next`, `for`, and the draining consumers all reach the frame through
`stepIter`, and none needed a line:

* `next(it)` and `next(it, d)` — `next` already implemented both forms, so the
  sentinel came free with the frame, which is what §pycomplete-15 predicted.
* `for k in iter(d)` — the `.ref`-to-generator arm of the `for` dispatch, which
  routes to `forGen`. Free at function scope; at MODULE scope it is free only
  because `genAllocFree` was fixed, which is what makes `dict.iter-for` the
  witness for that site rather than for the cursor.
* `list(iter(d))` — `iterValues`' generator arm, draining unguarded because
  `list` allocates.

*The generator-frame design keeps paying: one stepper, and every consumer that
already reached `enumerate` reaches this too.*

### The churn guard, kept and now UNDERSTOOD

`iter_churn_still_loud` is the same `.rekeyed` refusal §pycomplete-16 made
required, reached through a different spelling — and the census (above) is what
turned "the entries-array layout" into two named CPython rules. The guard did
not move; the ARGUMENT for it got stronger, and a stronger argument for an
existing refusal is the cheapest kind of progress this lane makes.

### Census deltas

* grammar census **122 → 132 witnesses**: `dict.iter-next`, `dict.iter-steps`,
  `dict.iter-empty`, `dict.iter-escapes`, `dict.iter-resize`,
  `dict.iter-exhausted`, `dict.iter-for` and `del.dict-next-iter` (MATCH);
  `dict.iter-churn` and `dict.iter-of-list` (REFUSE).
* `harness/cases.json` **670 → 686 rows**, sixteen `dict_lab::iter_*`; three
  are new gaps and join `WHITELIST_CLASS` — one `dict.keyset-churn` and two
  new classes, `iter.non-dict-receiver` and `iter.sentinel-form`.
* `isBuiltinName` **22 → 23 names**; `Monadic/Eval.lean`'s count comment moved
  with it, because a comment that states a number is a claim.
* `docs/memory-model.md` updated in three places: the H1 dict inventory, the
  cross-rung churn note (now carrying the `di_len` mechanism), and a new
  §`iter(d)` cursor paragraph.

### §9.0 after this inch

**2 of 3 flagship-serving pyc surfaces.** `del d[k]` (§pycomplete-16) and
`iter(d)` + `next` (here); the third is `next(<genexp over keys with a
filter>)`, the other eviction line's key expression, and §pycomplete-15's
census of it stands unchanged — *"the genexp already has a cursor class"*.

## 2026-08-24-pycomplete-19 — INCH (3): the flagship's LAST refused line was already retired, and the inch is the MEASUREMENT that proves it

`bound()`'s two `TABLE_SIZE` eviction lines were the R-track's whole refused
census. §pycomplete-16 landed the `del`, §pycomplete-18 landed
`next(iter(...))`, and this inch went to build the third surface —
`next(<genexp over dict keys with a filter>)`, the `tp_move` line's key. **The
census before building found the price is ZERO model sites.**

### THE RE-CENSUS, and it is §pycomplete-16's law firing in the other direction

§pycomplete-16 re-censused an expensive design and found it four times cheaper.
Here the re-census found the design already BUILT, and every piece of it was
landed for another reason:

| the line needs | where it came from |
| --- | --- |
| `del d[k]` | §pycomplete-16 (inch 1) |
| `next(...)`, both arities | pre-existing (H4) |
| a genexp with a FILTER lowered to a generator function | pre-existing — `gen_lab::first_over` witnesses `next((x for x in upto(n) if x > k), -1)` today |
| `for k in <dict>` **inside a generator body** | §3a's cursor — `execGen`'s `.ref`-to-dict arm builds a `forDict` frame |
| the three mutation regimes | §3a, unchanged |

**Measured, not assumed.** The genexp at `sunfish.py:511` captures exactly one
name — `self` — and `self` is a parameter of `bound` that the body never
assigns, so the lowering's STRICT admission
(`ctx.params.contains n && !ctx.assigned.contains n`) passes with no `drainOk`
and no change to `drainingBuiltins`. The other three genexps in `bound` were
computed the same way; the one at line 444 fails admission and is a different
construct's problem.

> **`bound`'s unsupported census is ZERO.** It was two at §L14 and three at
> §L13. The flagship chain's rung 9 closes, and it closes on a measurement.

### WHAT WAS ACTUALLY MISSING WAS EVIDENCE, NOT CAPABILITY

Every genexp witness in the tree iterates a `range`, a generator, or a tuple.
**Not one iterates a DICT.** The composition — a genexp whose `for` walks a live
dict cursor, under a filter, stepped once by `next` — had never been run. So
this inch is seven typed-call rows and five witnesses, and the honest headline
is that it BUYS NO CAPABILITY: it converts a believed capability into a
measured one. *A surface nobody has run is a surface nobody knows the tier has.*

### THE PAIR THAT PREVENTS THE WRONG CONCLUSION

The naive witness for this surface REFUSES:

    root = 1                      # a body-assigned LOCAL
    return next(k for k in d if k != root)      # REFUSED

and a lane that wrote only that row would have concluded the dict-genexp
surface is out of tier. It is not. `genexp_next_key(a, root)` is the SAME
construct with `root` a PARAMETER and it MATCHES. **What refuses is the capture
admission, and it has nothing to do with dicts**: a by-value snapshot of a
body-assigned local could go stale, so the lowering refuses it unless the
genexp is immediately drained. The two rows are filed together for exactly that
reason.

**And the refusal was CONSERVATIVE rather than principled**, which is worth
saying because it names a separable inch. `next` was not in
`drainingBuiltins`, but a one-argument genexp passed directly to `next` has a
lifetime strictly SHORTER than a drained one — one step, with no user code
between creation and step — so the snapshot cannot go stale. The two-argument
form is different: its default is evaluated before the step and can rebind the
captured local. `pycomplete-199` admits only the one-argument form and keeps a
walrus-default witness loud.

### THE CLAIM WAS FALSE, AND THE CLAIM IS EXACTLY WHY I DID NOT LOOK

This entry first said the tier *"cannot witness"* a dict genexp's liveness,
because binding a genexp to a name supposedly refuses. **The gate convicted
both halves**, and the correction is the inch's real product.

**Binding does not refuse.** The lowering's strict admission passes on a
PARAMETER capture regardless of `drainOk`, so `g = (k for k in d if k != root)`
lowers and `next(g)` answers 2 — agreeing with CPython.
Before pycomplete-200, `gen_lab::gen_assigned_lazy` refused because it
captured a body-assigned `lim`, **not** because it bound. The new item fuses
that immediate-drain shape; the negative companion keeps the rebind window
loud. *That is this entry's own §5.2 finding — a refusal names a SITE, not its
cause — and the later admission preserves it.*

**And the liveness IS witnessable — which is how the tier's first fully
probeable DIVERGENCE was found.** `g = (k for k in d)` / `d[3] = 'c'` /
`next(g)` raises in CPython and answers `1` here: PEP 289 calls `iter()` on the
outermost iterable when the genexp OBJECT is created, while this tier does not
push the cursor frame until the first resume, so the guard compares the dict
against itself. Filed as **`pyc-div-2`**, and unlike `pyc-div-1` its probe RUNS
both sides every time.

> **A false blanket claim hides the real gap, and the claim is why nobody
> looked.** The gap here was not smaller than the claim — it was a DIVERGE, and
> the sentence asserting unwitnessability is the reason it sat one edit away
> from being shipped as a REFUSE row.

### THE CONSTRUCTION-SITE CENSUS, and it corrected the question that ordered it

§5.2's ruling (`bf3f33f`) made "the trunk never constructs this frame" a
MEASURABLE claim rather than a docstring. Run over the three frames this lane
had called unreachable:

| frame | construction sites | trunk-reachable? |
| --- | --- | --- |
| `.forDict` | `Monadic/Eval.lean` ×3, `Monadic/Script.lean` ×3 — **zero trunk sites** | no |
| `.enumDict` | `Semantics.lean` `enumFrame` — **which the trunk's `enumerate` arm calls** | **YES** |
| `.iterDict` | `Semantics.lean` `iterFrame` — sole caller is the rebuild's `applyBuiltin` | no |

**`enumDict`'s trunk step arm is a LIVE path**, not an unreachable one: §3c-i-c
ruling (c) had the trunk BUILD the frame and refuse at the step, so a trunk
`e = enumerate(d); next(e)` reaches it. The lane asked for a ruling about
"three unreachable refusals" and **only two of them were unreachable** — the
census caught it on its first run, which is what it was ordered for.

Type-level discharge (`nomatch`, or narrowing the frame type) is **not
available at a price anyone would pay**: the frames live inside `Obj.generator`
on a SHARED heap, so narrowing means indexing the heap by presentation, which
ripples through `Obj`, `Heap.WF`, `PayloadBlind`, `ClockErase` and `Obs`. So
refusal-form stands for the two, with the claim gated by this census.

### THE DECLARED-DIVERGENCE REGISTER, FOUNDED

§5.0a's canonical shape is DATA per-tier, CHECKER shared, PROBE per-tier. This
tier builds the **checker** — `harness/divergence_register.py` — and files the
**data** (`docs/python-declared-divergences.json`) and its **probe**
(`harness/pyc_divergence_probe.py`) alongside it.

* **It validates SV's file UNMODIFIED**, today: 2 tier files, 3 rows, 6 guards,
  all held. Cross-tier validation is the acceptance test and it did not have to
  wait for a second filer.
* **It asks only tier-independent questions** — fields present, kind in the
  ruled two, guards exactly two and distinct, `declared` dateable, retirement
  condition not WAITING-shaped, probe exists, probe ran, every guard held.
  Nothing semantic is decided there; MEAS-28.
* **The guard set is checked BOTH ways.** A row naming a guard the probe lacks
  is UNGATED; a probe guard no row names is ORPHANED — the shape a deleted row
  leaves behind, and the one hole a build cannot see.
* **`--self-test` exercises the checker's own defect detection** against ten
  mutated copies of a real file. A checker that only ever passes is a claim,
  and the rules that matter are the ones that have never fired on real data.
* **The empty-register check is kept although it is now unreachable** (sv and
  python have both filed). It is a fact about today, not about the design, and
  removing it would buy a silent green.

### `pyc-div-1`, and the honest thing about its guards

The row is the sticky dict-iterator error state: CPython poisons
(`di_used = -1`, its own comment says sticky) and re-raises on every later
`next`; the model CLOSES the generator, so `next(it, x)` answers `x`.
`KIND: semantic`, `INHERITED FROM: enumDict / §pycomplete-14` — not blank,
because blank is the heavier ORIGINATED claim and it would be false.

**THE DIVERGENCE IS NOT REACHABLE BY AN IN-TIER PROGRAM**, and the probe says so
instead of implying a run it cannot make. Observing it needs the first
`RuntimeError` survived, which needs `except RuntimeError:` — and
`exc_lab::except_builtin` is a whitelisted refusal. So the ORACLE half is a
genuine run every time, and the MODEL half is pinned where the divergence
actually lives: the ABSENCE of a poisoned `GenStatus` constructor. That is not a
weaker guard than a program would be — **it fires on exactly the event that must
retire the row**, which is a poisoned state landing.

The widening metric is the count of synthetic iterators whose frame carries a
dict guard: `<enumerate>` and `<iter>`, two. `<count>` is allocated the same way
and deliberately NOT counted — its frame carries no dict guard, so it can never
raise the sticky error, and a metric that counted it would fire on an unrelated
feature.

### THE STALE PROSE, REPAIRED — and why nothing caught it

`sbEvict_lit`'s docstring said `del d[k]` *"ingests as `Stmt.unsupported`"* and
that `bound`'s unsupported census is two. Both were false the moment inch (1)
landed. **Nothing broke, because `sbEvict_lit` quantifies the body
existentially (`∃ b : Array Stmt`) and `evict_dead` earns its result by showing
the guard is `.bool false` and never opening the body.** The proof was immune to
the change; the prose was not, and prose cannot fail.

`BoundWF.room`'s rationale is rewritten to the falsifiable form: dropping it no
longer produces a refusal, it produces a WRONG WORLD — `evict_dead` proves
`.ok ⟨w, e⟩ .next` with the SAME `w`, and with the guard TRUE the body now
removes a key and bumps `shapeVersion`, answering `.ok ⟨w', e⟩ .next`. **The
hypothesis is unchanged and still needed; what changed is that its violation is
now SILENT**, and observability is not a property any instrument here measures.
It is reclassified TIER → MODELLING (§5.0a's taxonomy): the honest retirement is
to model the eviction, not to widen the tier.

### Census deltas

* grammar census **132 → 136 witnesses**: `dict.genexp-next`,
  `dict.genexp-nomatch`, `dict.genexp-default`, `dict.genexp-drain`, all MATCH.
  `dict.genexp-bound-is-loud` was written as a fifth and measured **DIVERGE**;
  it does not belong in this census's vocabulary and moved to the register,
  whose probe runs it both ways — strictly more gating than a census row.
* `harness/cases.json` **686 → 693 rows**; **one** new gap joins
  `WHITELIST_CLASS` (`genexp.lowering-admission` — the CAPTURE rule, not the
  dict cursor). A second was predicted and the gate refused it:
  `genexp_bound_still_loud` MATCHES.
* **declared-divergences: 0 → 2** — the third standing quantity, beside the
  coverage number and never folded into it. `pyc-div-2` is the register's first
  row whose probe runs BOTH sides.
* Three prose sites repaired in `Examples/python/sunfish/`; zero theorems moved.

### §9.0 after this inch

**3 of 3 flagship-serving pyc surfaces. `declared-divergences: 2`.**
Rung 9's dependency on this lane is discharged: `bound()` has no refused
construct left — **and the discharge is SCOPED, measured rather than assumed.**
Of `bound()`'s four generator expressions exactly one iterates a dict
(`sunfish.py:511`), and it creates and steps its cursor inside a single
expression, so real play never enters `pyc-div-2`'s create-to-first-resume
window. The `tp_score` line uses `iter()`, which snapshots at creation and is
unaffected. Had real play entered the window, this discharge would not stand.

## 2026-08-24-pycomplete-20 — the cursor moves to CONSTRUCTION, pyc-div-2 retires by its own condition, and the census that gates the claim corrected itself twice

§pycomplete-19 declared `pyc-div-2`: a genexp's dict cursor was built at FIRST
RESUME where PEP 289 builds it when the genexp OBJECT is made, so
`g = (k for k in d)` / mutate `d` / `next(g)` answered where CPython raised.
The fix lands, the row retires, and the retirement was ANNOUNCED BY ITS OWN
GUARD rather than by anyone deciding it was time.

### THE PROBE THAT NARROWED THE FIX, and its negative half is the load-bearing one

| shape | CPython 3.9.19 |
| --- | --- |
| **genexp**, mutate after create, before first `next` | `RuntimeError` |
| **generator FUNCTION**, same mutation | **`1`** — no error |
| generator function, then drained | **`[3]`** — it walks the GROWN dict |
| `(x for x in boom())` | raises **at creation** — outermost iterable is eager |
| `(x for x in d for y in boom())` | constructs — **inner clauses stay lazy** |

**So "make generator cursors eager" would have been the wrong fix.** Calling a
generator FUNCTION runs no code, so CPython has called no `iter()`; the tier's
deferred behaviour there is CORRECT and a blanket fix would have broken it.
Eagerness is a **genexp** rule, for the **outermost** clause only. And of the
receivers only a dict carries a snapshot — `forList` re-reads live, value
sequences are immutable, `forGen` holds no counts — so no other receiver can
show the difference.

That narrowing is why the fix is one worker and one call site:
`genInitCont` (`Semantics.lean`, beside `iterFrame`) seeds a synthesized
`<genexpr@n>`'s continuation with its cursor already pushed; `callInM` uses it;
everything else — including every user `def` with a `yield` — still gets
`[.block body]`. `genExpPrefix`/`genExpArgName` move to `Ast.lean` beside
`dictDelBuiltinName`, because ingestion mints those names and the evaluator now
has to recognise them, and a name spelled twice is a name that will drift.

`dict_lab::genfun_mutate_after_create` and `genfun_drain_after_create` are the
NEIGHBOUR rows, filed beside the fix precisely so a later blanket change flips
them. This is the `gen_closes` pattern's third use: *the row that proves the
fix did not fix the wrong thing.*

### THE RETIREMENT WAS ANNOUNCED BY THE GUARD, which is the half nobody designs for

`pyc_div_2_still_divergent` began FAILING the moment the fix compiled. §5.0a's
paired-guard law is usually read in one direction — *has the divergence
widened?* — and this is the other one paying out: **the divergence is gone, and
the declaration is now a false claim about the tier that reads as diligence.**
The row left the register on that evidence, not on anyone's say-so, which is
exactly what its retirement condition demanded (*"the row retires by the
behaviour changing and cannot be closed by assertion"*).

> **A register that only ever grows is a list. This one shrank, on a failing
> guard.**

The witness moved with it: `dict.genexp-bound-is-loud` measured DIVERGE at
§pycomplete-19, moved OUT of the census into the register, and **comes back as
a MATCH**. A row that leaves for the register and returns to the census is the
whole mechanism working, and the witness is the receipt.

### THE CONSTRUCTION-SITE CENSUS, gated — and it corrected itself twice

§5.2's ruling made *"the trunk never constructs this frame"* measurable rather
than a docstring. `harness/frame_construction_census.py` pins it:

| frame | route | trunk callers |
| --- | --- | --- |
| `iterDict` | `iterFrame` | **0** — MEASURED unreachable |
| `enumDict` | `enumFrame` | **1** (`Semantics.lean`) — POSITIVE, the correction |
| `forDict` | `genInitCont` / `K.forDict` / `S.forDict` | **0** |

**Its first draft reported two FALSE drifts, and both said the same thing.** It
counted `ClockErase`/`PayloadBlind` as trunk callers of `enumFrame` when those
files only REASON about the trunk; and it flagged a `forDict` construction in
`Semantics.lean` that is **this inch's own `genInitCont`** — a worker living in
a trunk file with only rebuild callers. So the measure had to become
**caller-based, not file-based**, which is the very distinction the enumDict
correction turned on. *A census whose first run convicts the lane's newest line
is a census pointed at the right thing.* The `enumDict` row is pinned as a
POSITIVE expectation so the correction cannot be lost the way the belief was.

### THE SHARED CHECKER GREW A SECOND PROBE SHAPE, and a migration clause

ES's row merged, so the acceptance test finally binds — and it FAILED: ES files
`declared-divergences-0.1`, no `probe` key, guards as
`"<path>: <name>"` Lean theorems, and a blank `inherited_from`. None of that is
wrong; it is a second legitimate shape in which **the build is the run**, and a
Lean theorem that stops holding fails the tenure — a stronger gate than a
script, not a weaker one.

* `probe` is now OPTIONAL; absent, guards name declarations and the checker
  verifies they exist. Both shapes satisfy §5.0a's *"named in the row"*.
* `declared-divergences-0.1` and blank `inherited_from` are accepted with
  MIGRATION WARNINGS that do not change exit status — §9.5a's old-valid clause
  applied to schemas: *a shape a lane shipped in good faith cannot become a
  failure the day the canon lands.* The schema earned its migration clause on
  day two.
* **The schema is written down ONCE**, as a docstring block in the shared
  checker, so the next tier reads it instead of inferring it from a neighbour's
  file — which is how the divergence arose.
* The checker now validates all three tiers' files UNMODIFIED: **4 rows, 8
  guards, 2 migration warnings, exit 0.**

**And a self-referential trap, caught by the self-test's own expectation.** The
new declaration-shape case first pointed its fake guard names at
`divergence_register.py` itself — and the substring existence check duly FOUND
them, passing a file it should have rejected. *A grep-based existence check is
self-referential when aimed at its own source.* Self-test: 10 → **13** defect
classes.

### Census deltas

* grammar census **136 → 138 witnesses**: `dict.genexp-bound-is-loud` returns
  as MATCH, and `dict.genfun-mutate-after-create` joins it as the negative half.
* `harness/cases.json` **693 → 697 rows**, four new `match` rows; no new gaps.
* **declared-divergences: 2 → 1** for this tier (4 across all three).
* new gate `harness/frame_construction_census.py`; `harness/divergence_register.py`
  extended for both probe shapes.

### §9.0 after this inch

**3 of 3 flagship-serving pyc surfaces · `declared-divergences: 1`.**
The scope qualifier on rung 9's discharge WEAKENS as predicted: with the cursor
built at construction, `pyc-div-2`'s create-to-first-resume window no longer
exists, so the claim that real play never enters it is moot rather than
load-bearing. What remains is `pyc-div-1`, whose retirement is blocked upstream
on `exc_lab::except_builtin`.

## 2026-08-24-pycomplete-21 — a substring is not a declaration: the register's declaration shape gets an anchor, and the fixture needs no fixture

ES retired its lane-local checker into the shared one and flagged what the
shared one was missing on the way out. The declaration-shape branch asked
`gname not in text` — **a plain substring test** — so a guard whose `def` had
been DELETED but whose name survived in a comment still passed.

**This is the third time this instrument has been bitten by the same shape.**
The self-test's own first draft aimed its fake guard names at
`divergence_register.py` and the checker FOUND them (§pycomplete-20); QoL hit
the self-matching row; and now a name in prose reads as a declaration. *A
grep-based existence check answers "is this string here", and the question was
"is this thing declared".*

### What the tightening requires, and why BOTH halves

ES's retired checker required `def <name>` **and** a matching `#guard <name>`,
and that pair is now the shared instrument's:

* `def <name>` at a line start — the declaration exists, rather than the name
  appearing in prose;
* `#guard <name>` at a line start — and the build actually EVALUATES it.

A `def` nobody `#guard`s is **a guard in name only**: the build compiles it and
nothing ever checks it. A `#guard` with no `def` cannot elaborate. Comments are
stripped (`/- -/` and `--`) before matching, because anchoring alone is not
enough — `^\s*def foo` matches happily inside a block comment, which is exactly
the deleted-declaration case.

### THE FIXTURES NEEDED NO FIXTURE FILE, and that is the nice part

Both new self-test cases point at REAL repository files, so there is nothing to
create, stage or clean up:

| case | fixture | why it must refuse |
| --- | --- | --- |
| name only mentioned | `docs/es-declared-divergences.json: es_div_1_still_divergent` | the name is in ES's own register as DATA and is declared nowhere — **the old substring test returned `True` for exactly this** |
| `def` without `#guard` | `LeanModels/Python/Ast.lean: isBuiltinName` | a real `def`, genuinely never `#guard`ed |

The first is the sharpest fixture available anywhere in the tree: the string
that proves the bug is the guard's own name, sitting in the register file that
names it. Self-test **13 → 15** defect classes.

### The fleet after this

Two probe shapes, both live and both gated: SCRIPT (`python`, `sv`) and
DECLARATION (`es`, `def` + `#guard`). Schema stable at
`declared-divergences-1` fleet-wide, **zero migration warnings** — the
migration clause did its job and is now dormant rather than load-bearing, which
is the outcome §9.5a's old-valid law is for. Register: 3 files, 4 rows, 8
guards. `declared-divergences: 1` for this tier.

**Class note.** This landed `docs`-class — no Lean elaborates — but the changed
file is a GATE, and a gate that lands without being run is the §5.4b shape
again. So the instrument was added to `--gates` explicitly rather than relying
on the class floor, which runs only `docs_check`.

## 2026-08-24-pycomplete-22 — `except <builtin>:` lands as a SUBSUMPTION TABLE, and a docstring that argued a case away expires with it

`exc_lab::except_builtin` was the whitelisted refusal upstream-blocking
`pyc-div-1`'s witness: a program-level probe of the sticky dict-iterator needs
`except RuntimeError:`, and the tier's admitted handler shape named user
classes only.

### THE FLAGSHIP DOES NOT CARE, measured before anything else

`bound()` contains **zero** `try` statements. All of `sunfish.py` has exactly
one, and its handler is `Stop` — a user class already in tier. So rung 9 is
untouched either way, and this inch is paying down a DEBT rather than serving
the flagship.

### BLAST RADIUS — AND I SCOPED IT WRONG TWICE, at two different scales

The first census enumerated handlers in `exc_lab.py` and found two builtin
classes (`ZeroDivisionError`, `Exception`). **The gate found a third**:
`assert_lab::catch_assert` catches `AssertionError`, and I had never looked
outside the file the row I was fixing happened to live in.

Re-scoped to `Examples/python/*/*.py` and re-ticketed. **The gate found a
fourth**: the grammar witness `stmt.Try` catches `ValueError` — and the grammar
census's witnesses are not files at all, they are Python source embedded as
STRING LITERALS inside `harness/refusal_census.py`.

> **A blast-radius census must span every corpus that RUNS the language, and
> this repository has three in three different shapes** — typed-call witnesses
> in `Examples/python/*/*.py`, grammar witnesses as inline source inside
> `refusal_census.py`, and whole programs in `harness/scripts/*.py`. Scoping to
> the file where the defect lives finds one; scoping to the obvious corpus
> finds most; only enumerating all three finds them all.

Two red tenures for one error at two scales. The complete enumeration:

| corpus | site | handler | disposition |
| --- | --- | --- | --- |
| Examples | `exc_lab` | `ZeroDivisionError`, `Exception` | FLIP to match |
| Examples | `assert_lab` | `AssertionError` | FLIP — missed by census 1 |
| Examples | `import_lab` ×3 | `ImportError` | unaffected — `importErrorHandlerMatch` is checked first |
| Census | `stmt.Try` | `ValueError` | FLIP — missed by census 2 |
| Scripts | 3 files | `ImportError` | unaffected, same reason |

**And two of the flipping rows were vacuous.** `except_builtin` passed `n=1`,
which never divides by zero, and `stmt.Try`'s program never raises at all —
both would have flipped to `match` WITHOUT ENTERING A HANDLER. The flip adds
`n=0` to the first; the second keeps its verdict, but its note now says plainly
what it does and does not prove, because a grammar row is a lower bound on
coverage and never evidence about the catch.

### WHY IT IS A TABLE, AND WHY IT IS DATA

Three facts make a name-to-constructor equality wrong:

* **`RecursionError <- RuntimeError`** in CPython's MRO, so the WIDER handler
  name must catch the narrower error. This pair alone makes it a subsumption
  relation.
* **`except Exception:` is universal** — every builtin the tier raises, and
  every admitted user class too.
* **`ZeroDivisionError` is TWO constructors** — see below.

So the relation lives in `Ast.lean` as three explicit tables
(`admittedBuiltinExc`, `refusedAncestorExc`, `builtinExcCatches`) rather than
as logic inside the matcher — **because the matcher exists twice**, at function
scope and at module scope, and a rule spelled twice is a rule that drifts.
**Nothing is inferred**: every pair is one this tier can actually exhibit, and
an ancestor the tier could compute but has not measured is refused BY NAME.

### THE DOCSTRING THAT EXPIRED, and it is the third of its shape

`PyErr.zeroDivisionPow`'s own docstring justified splitting the constructor
partly on this:

> *"`except ZeroDivisionError:` needs no update: builtin exception names are
> not matchable at all … so the two cannot be told apart by any program in the
> tier."*

True when written — and a claim about a LIMITATION rather than about the split,
so the inch that lifted the limitation falsified it, and **no proof noticed
because no proof depended on it.** Had the table mapped only
`zeroDivisionError`, `0 ** -1` would silently escape a handler CPython
catches: *a wrong answer, not a missing feature.* Both constructors map, and
the docstring is repaired in the same commit as the code that invalidated it.

> **Third instance of one shape: a docstring that argues a case away on the
> strength of a limitation the next inch removes.** `sbEvict_lit`'s "ingests as
> `Stmt.unsupported`" (§pycomplete-20), this lane's own "cannot be witnessed"
> (§pycomplete-19), and now this. The common factor is not carelessness — each
> was true when written. It is that **an argument resting on what the tier
> CANNOT do has an expiry date that nothing in the tree tracks.**

### The frontier names itself

`ArithmeticError`, `LookupError`, `BaseException`, `OSError`,
`EnvironmentError` are refused BY NAME with a message saying why — admitting
them would claim a catch set the model has never enumerated.
`exc_lab::except_ancestor_still_loud` is the falsifiable witness (CPython
answers −1 through `ArithmeticError`); it joins `WHITELIST_CLASS` as
`exc.ancestor-class`, so the frontier is a row rather than a belief.

**And the subsumption witness had to move.** Its first draft used a nested
recursive `def` — which is `closure_lab::rec_nested_name`'s whitelisted
refusal, so it would have refused for a reason having nothing to do with
exceptions. Its second problem was worse: the tier reaches `.recursionError`
at exactly ONE site, `heapEq`'s active-pair check, so deep recursion exhausts
FUEL instead. The witness lives in `dict_lab` on the two-self-cyclic-dicts
shape, which is the only place the pair is reachable at all.

### Census deltas

* `harness/cases.json` **697 → 699 rows**; `except_builtin`,
  `except_exception` and `assert_lab::catch_assert` FLIP
  `unsupported → match` and leave `WHITELIST_CLASS`; one new gap joins it
  (`exc.ancestor-class`). Grammar census: `stmt.Try` flips `REFUSE → MATCH`.
* `docs/backlog/python-completeness.md`'s INBOUND heading re-spelled id-first.
  The index derives an entry's id from the heading's FIRST TOKEN, so the old
  spelling rendered the row as ``| `INBOUND` | INBOUND | … |`` — present but
  unaddressable. Six of six now conform.

### What this unblocks

`pyc-div-1`'s retirement condition named `exc_lab::except_builtin` leaving the
whitelist as its blocker. **It has left.** The debt's witness
(`dict_lab::iter_sticky_after_resize`) is now writable, so the row's probe can
gain its program-level form and the retirement becomes fully exercisable — the
next inch, not this one, because writing the witness is where that debt's
measurement belongs.

**§9.0: `3 of 3` flagship-serving pyc surfaces · `declared-divergences: 1`.**

## 2026-08-24-pycomplete-23 — pyc-div-1's probe gains its second side, and the instrument's own claim expires with it

`pyc-div-1` said CPython POISONS a dict iterator whose size guard fired
(`di_used = -1`, sticky) while this tier merely CLOSES the generator, so a later
`next(it, x)` answers `x`. Filed at §pycomplete-19 with **one side running**:
the oracle half executed, the model half was pinned at the absence of a
poisoned `GenStatus` constructor. Honest, and weaker than a run.

### THE BLOCKER WAS NAMED, AND IT WENT AWAY

The row's `blocked_on` said the witness needs `except RuntimeError:` to survive
the first raise, and that `exc_lab::except_builtin` was a whitelisted refusal.
§pycomplete-22 admitted builtin handler classes; the refusal left the
whitelist; the blocker resolved. **The row's retirement condition is now fully
exercisable**, which is the whole point of having written the blocker down
rather than leaving it as "when someone models it".

The field is kept as `was_blocked_on` rather than deleted, because a blocker
that silently disappears leaves the instrument describing a world that no
longer exists — which is exactly what happened next.

### THE PROBE'S OWN DOCSTRING EXPIRED — fifth of the shape, first inside an instrument

`pyc_divergence_probe.py` opened with:

> **THE DIVERGENCE IS NOT REACHABLE BY AN IN-TIER PROGRAM.**

True for a day and a half, and false the moment §pycomplete-22 landed. It is
the **fifth** claim in this lane to expire that way — after `sbEvict_lit`'s
"ingests as `Stmt.unsupported`", this lane's "cannot be witnessed",
`zeroDivisionPow`'s "builtin exception names are not matchable at all", and
`catch_assert`'s "the recorded gap" — and the first found **inside an
instrument** rather than a docstring, a witness or a proof.

> Every one was TRUE when written. The common factor is that each rested on
> what the tier **could not do**, and a premise of that shape has an expiry
> date that nothing in the tree tracks. An instrument carrying one is worse
> than a comment carrying one, because the instrument is what a reader trusts
> when the comments disagree.

### What the guards do now

* `pyc_div_1_still_divergent` RUNS the witness under CPython and under
  `tools/leanpy` and compares: the oracle must print `first-raised` and then
  DIE re-raising, the model must print `first-raised` and then answer
  `DEFAULT`. The `GenStatus` check stays alongside, because a poisoned state
  landing is the fact the retirement condition names.
* `pyc_div_1_has_not_widened` gains a real control: **a FRESH cursor over the
  same dict, made after the poisoning, must work on BOTH sides** (CPython
  answers 1). The row describes one poisoned OBJECT — not a poisoned dict, and
  not a poisoned interpreter. The source-level counts
  (`DICT_GUARDED_ITERATORS`, `STICKY_CAPABLE_RAISES`) stay pinned above,
  because "could a THIRD site inherit this row" is a question no program can
  ask.

The first control drafted for this was `raise ValueError` inside the `try` —
and **raising a builtin class is itself a whitelisted refusal**, so it would
have refused for a reason having nothing to do with iterators. Caught before
ticketing this time, by asking what the program needs rather than what it
looks like.

### Blast radius — three corpora, checked FIRST

Per §pycomplete-22's law, and applied before the ticket rather than after two
red tenures. The change touches `harness/pyc_divergence_probe.py` and
`docs/python-declared-divergences.json`; **zero references to either exist in
any of the three corpora** that run Python (`Examples/python/*/*.py`, the
inline grammar witnesses in `refusal_census.py`, `harness/scripts/*.py`). No
witness moves, and none may: this row is a DIVERGENCE, so a census row for it
would be a `DIVERGE` — it lives in the register precisely so the scoreboard
never sees it.

### And what a failing guard would mean here

If `pyc_div_1_still_divergent` fails on this landing, the honest readings are
two and both are useful: either the model no longer diverges — in which case
**the row must retire** and the guard has done its job in the direction §5.0a
cares most about — or the witness is wrong. The detail line prints both sides'
exit status and output, so the tenure distinguishes them without a rerun.

**§9.0: `3 of 3` flagship-serving pyc surfaces · `declared-divergences: 1`**
for this tier, now with both sides measured.

## 2026-08-25-pycomplete-24 — the pins pair is SHARDED, and one of the two barely benefits

`pins_bound` (18.9 min) and `pins_clock` (19.0 min) are together ~85% of every
full spine build's elaboration. A single module elaborates SERIALLY, so the
probes inside each — independent `#guard`s — cannot overlap. This is a TOPOLOGY
change and nothing else: **no probe dropped, no fuel changed, every expected
value byte-identical.**

### The census corrected the mental model before any edit

Both files are **~250 lines**. The cost is not size, not guard count, but what
each `#guard` KERNEL-EVALUATES — the interpreter running sunfish at depth. So
shards must be balanced by guard cost, and "split the big file" was never the
right description of the problem.

Three facts made the split safe, and all three were measured first:

* **`globs = ["Examples.+"]`** — a new file under `Examples/` is a default
  target automatically. No lakefile edit, and coverage is unchanged *by
  construction* rather than by inspection.
* **Both files are LEAVES.** Nothing imports either, so splitting them cannot
  disturb another module.
* **`pins_common` already exported** `board0`/`posH`/`sp0`/`searcherW`; only
  `boundProbe` (and, for the clock file, `searcherWT`/`boundProbeT`) needed
  lifting, each moved verbatim.

### `pins_bound` — five leaves, and the boundary names the board

| shard | board | guards |
| --- | --- | --- |
| `pins_bound_h` | opening `posH 0`, depths 1–3 | 8 |
| `pins_bound_mid` | midgame `posMid` | 6 |
| `pins_bound_tac` | tactical `posTac` + quiet-pawn `posPend` | 5 |
| `pins_bound_end` | rook endgame `posEnd` | 4 |
| `pins_bound_searcher` | the trace-clock frontier | 3 |

`pins_bound.lean` survives as the prose home and a facade importing the five —
the capstone's 23-pair narrative stays in one place, and the module name keeps
resolving.

### `pins_clock` — three leaves, AND THE SHARDING BUYS LITTLE, which is the finding

`transport` (the ∀-trace theorem, 0 guards), `probe` (5 guards), `walk`
(1 guard). **That one guard is the module**: a 13-step search generator at fuel
4 000 000 that crosses node 2048.

> **A certificate cannot be split without changing it.** Splitting the walk in
> two would re-run its first twelve steps in both halves — doubling the work to
> halve the wall, which is not a trade. So `_walk` stays whole and stays the
> critical path.

The win here is real but smaller and differently shaped: `_walk` now overlaps
`pins_bound`'s five leaves instead of queueing behind the rest of its own file.
**Amdahl was predicted before the edit and confirmed by the structure**, which
is why this entry states it rather than leaving a future reader to wonder why
the second file did not halve.

### `genmoves_ray` is NOT included, and the reason is measured

It is not a leaf: `genmoves_scan`, `genmoves_drain` and `sf_order/transport`
all `open` it and consume its 173 theorems. Sharding it needs a re-exporting
facade — a materially riskier change that should be priced on its own rather
than bundled with a pair that splits cleanly.

### The certificates did not move, and that is CHECKED

Every `#guard` BLOCK (several span a dozen lines) was extracted from the
pre-shard file and from the shards, sorted, and compared:

    pins_bound   guards 26 -> 26  identical=True
    pins_clock   guards  6 ->  6  identical=True | theorems 1 -> 1 identical=True

A topology change that cannot prove its certificates are untouched is a
refactor with a story attached, and this lane has enough of those.

### Ride-along: the checker's own SyntaxWarning

`harness/divergence_register.py`'s `_strip_lean_comments` docstring QUOTES a
regex — ``^\s*def foo`` — in a plain string, so `\s` is an invalid escape:
a `DeprecationWarning` on 3.9 and a **`SyntaxWarning` on 3.14, emitted on every
gate run**. Now an r-string. *Prose that quotes code is still code to the
lexer* — and an instrument that warns on every invocation trains its readers to
ignore its output.

### And a note for the checker's ledger, from the fleet red this week

Master's register gate is red on rows using kinds outside §5.0a's enum. The
root cause is not the rows: **that tier's tenure floor never ran the register
gate at all, so its data was never exercised** — the corpus-exercise law, one
layer up, at the GATE rather than at the witness. The checker was right and
stays exactly as strict as it is; a checker loosened to accommodate unexercised
data would have converted a loud red into a silent wrong claim.

## 2026-08-25-pycomplete-25 — the midgame board splits by DEPTH, and the field-collision sweep returns a clean negative

Two items, and the first is the previous inch's own profile turned back on itself.

### `pins_bound_mid` was 74% of its family, and the axis was DEPTH

The five-way shard measured `_mid` at **875 s — 74% of the whole bound
family**, capping its win at **1.3×** where 2× was hoped. Balancing by guard
COUNT was the wrong axis; so was balancing by FAMILY. The cost follows depth,
and **the certificates print the evidence themselves** — each guard's expected
pair carries its node count:

| depth | guards | nodes | share | predicted |
| --- | --- | ---: | ---: | ---: |
| `_mid_d1` | `0 1`, `60 1` | 71 | 4.6% | ~40 s |
| `_mid_d2` | `0 2`, `60 2` | 826 | 53.3% | ~466 s (7.8 min) |
| `_mid_d3` | `0 3`, `60 3` | 653 | 42.1% | ~369 s (6.1 min) |

> **PREDICTION, stated before the tenure:** the bound family's critical path
> falls **14.6 → ~7.8 min (1.88×)**, set by the `_mid_d2` pair. Not the even
> thirds a guard count would suggest — 53/42/5 is what the node counts say.

**An even split was available and NOT taken.** Mixing depths across shards
(`0 2` alone; `0 3`+`60 2`; the rest) would balance to ~42% and shave a further
~1.7 min. It muddies what a red names — the whole point of the boundary — and
**the fleet floor is `pins_clock_walk` at 19.1 min either way**, so the extra
balance buys nothing that matters. Optimising below the floor is motion, not
progress.

`posMid` lifted to `pins_common` verbatim, as `boundProbe` did. Certificates
re-checked across the whole bound family: **26 → 26, identical**.

### THE FLEET FLOOR, named so nobody re-derives it

`pins_clock_walk` at **19.1 min is irreducible** — one certificate, and a
certificate cannot be split without changing it. Nothing to do but know it.
`genmoves_ray` (5.9 min) stays priced separately: it is not a leaf, so it needs
a re-exporting facade.

### The field-collision sweep: a clean NEGATIVE, checked rather than assumed

The fleet sweep asks whether any field this tier's instrument writes into an
envelope could be overwritten by the source when properties merge (ES's defect:
the node type in `kind`, silently beaten by the source's own `kind`).

**Impossible by construction here, because the pyc extractor is hand-built
rather than merge-based.** Verified mechanism by mechanism:

* no `.update()` on any emitted node — the two in the file operate on
  name-census *sets*;
* no `vars(node)`, no `node.__dict__`, no `{**…}` dict-unpack anywhere;
* `ast.iter_fields` appears **once**, inside `_replace_node`, an AST→AST
  rewrite (`type(root)(**fields)`) for the hoisted filter — never envelope
  construction.

**And the specific hazard was real.** CPython's `ast.Constant` *does* own a
field named `kind` — the string prefix, `'u'` for `u"abc"`. Measured:
`u"abc"` gives `value='abc', kind='u'`; `"abc"` gives `value='abc', kind=None`.
The extractor **never reads `node.kind`**, emitting `{"kind": "Constant", …}`
hand-built, so the source's `kind` is dropped rather than merged — and dropping
it loses nothing, the `u` prefix being lexical only in Python 3.

**The transferable half:** in `unsupported()` this tier already does what ES's
fix requires —

    "kind":    "Unsupported",
    "py_kind": py_kind if py_kind is not None else type(node).__name__,

the source-derived node type gets a **different field name**. *When an
instrument records what the source IS, the field must not be one the source
also owns.* Disjoint by naming, not by luck.

### And a process correction, recorded because it is my own law

`pyc-del` was never pushed; the coordinator had to fetch from the worktree.
Inch 1's rule — *push when the thing you would have to redo becomes green* —
includes the push, and I had been treating "committed and reported" as done.
The claim sequence is now **verdict → verify tree → commit → PUSH → report**.
## 2026-08-25-pycomplete-26 — the register's three clauses, and a probe that was starting UNLOCKED BUILDS

§5.0a's empty-register ruling (`52e9c4b`) lands in the shared checker, which
this lane owns. **A file's legality is decided by its CLAIM, not its LENGTH.**

1. `rows: []` is LEGAL iff `retired_rows` is non-empty — the claim being *"no
   LIVE debts, and here is how each one closed."*
2. `rows: []` **and** `retired_rows: []` is an ERROR whose message says to
   DELETE the file: it makes no claim at all, and an empty ledger reads as
   diligence while asserting nothing.
3. Every retired row must name a guard whose **EXISTENCE** the checker
   verifies.

### Clause 3 inverts the retirement discipline, and that is the point

**EXISTENCE, NOT PASSAGE** — and the distinction carries the design. A retired
row's `still_divergent` should now FAIL; that failure is the signal the
divergence has come back. Asserting it *holds* would invert the meaning;
asserting nothing would let the guard be deleted along with the row and take
the watch with it. So the checker requires the guard to exist, does not
require it to pass, and excludes retired guards from the ORPHAN rule.

**This corrects my own retirement of `pyc-div-2`** (§pycomplete-20), where I
deleted the row *and* its guards precisely to avoid the orphan error. Under the
ruled contract that was the wrong move: retirement moves a row to the archive,
it does not end the watch. Restoring `pyc-div-2` as a retired row with its
guards live is owed and is not in this commit — it is a data change to this
tier's own file, and the checker lands first so the fleet has one instrument.

### Blast radius, measured before landing

| tier | result |
| --- | --- |
| `es` | 0 problems |
| `python` | 0 schema problems (its probe is post-build) |
| `sv` | **2 problems** — `sv-div-2`'s two retired guards do not exist |

C's file is absent from master pending its restore, so **clause 3 reds SV, not
C** — and SV has no dispatch. Reported rather than softened: the migration
clause was for shapes shipped before a canon, and these guards were *deleted*,
which is the thing clause 3 exists to catch.

### AND THE PROBE WAS STARTING UNLOCKED LEAN BUILDS — my defect, found by tripping it

Running the shared checker in a fresh worktree kicked off a **`lake build` with
no tenure**, competing with the lane that held the lock. Cause: §pycomplete-23
made `pyc_div_1`'s probe two-sided, so it calls `tools/leanpy` — and `leanpy`
BUILDS when `.lake` is cold. Every tier whose floor runs the shared checker
would have paid that, in whatever clone they happened to be in.

> **Making a probe two-sided turned a Lean-free check into a Lean-executing
> one, and the instrument is shared.** The blast radius of a probe change is
> every lane that runs the checker, not just the tier that owns the row.

The probe now checks for `.lake/build/bin/leanmodels-run` and, when it is
absent, FAILS with the post-build-gate message instead of building. That file's
docstring already *claimed* it "runs as a POST-BUILD gate"; this is the claim
made true rather than asserted — a guard that cannot run must fail, never skip,
and never build.

Self-test: **15 defect classes + 3 clause cases**, the clause fixtures built
explicitly rather than mutated from a neighbour's file so they stay
deterministic as tiers come and go.

## 2026-08-25-pycomplete-27 — pyc-div-2 goes back on the watch, and the watch gains the alarm it was missing

§5.0a clause 3 shipped, so this tier's own file gets corrected against the
instrument rather than against my memory of it.

### The correction

At §pycomplete-20 I retired `pyc-div-2` by deleting the row **and its two
guards** — deliberately, to avoid the checker's ORPHAN error. Clause 3 ruled
that wrong: **retirement moves a row to the archive; it does not end the
watch.** The row is now in `retired_rows` with `retired`/`retired_by`, and
`pyc_div_2_still_divergent` / `pyc_div_2_has_not_widened` are live again in the
probe, reporting FAIL and not gating.

The `LIVE_GUARDS` / `RETIRED_GUARDS` partition is copied from
`sv_divergence_probe.py` deliberately — **one shape for a third tier to copy,
not two.**

### AND THE WATCH COULD NOT RAISE AN ALARM

Unit-testing the partition surfaced the case nobody had covered. For a retired
row the polarity of `still_divergent` **inverts**: FAIL means the divergence is
gone (healthy), and `ok` means it **came back**. Measured on the shipped shape:

| live | retired | rc | meaning |
| --- | --- | ---: | --- |
| pass | FAIL | 0 | healthy archive — correct |
| FAIL | FAIL | 1 | live guard gates — correct |
| pass | **ok** | **0** | **the divergence RETURNED, and nothing went red** |

The third row is the one the archive exists for, and it was **silent** — the
guard prints a cheerful `ok`, does not appear in the "reporting not-held"
summary, and the probe exits 0. SV's file names the event in prose (*"it
flipping to `ok` is the event worth looking at"*) and does not gate on it
either, so this is a fleet-wide gap rather than a local slip.

> **A watch whose most important signal produces no alarm is not a watch.**
> Keeping the guard alive was the ruled half; making its regression *fire* is
> the half that makes the guard worth keeping.

So a retired `*_still_divergent` that HOLDS now sets `rc = 1` with an explicit
REGRESSION message saying the row must leave the archive and become a live debt
again. **This does not contradict "existence, not passage"** — that rule
governs what the shared CHECKER may assert about another tier's row. What a
tier's own probe does about its own regression is the tier's business, and a
silent regression is precisely the failure the archive was created to prevent.

All three states are unit-tested by stubbing the two guard sets, so the
polarity cannot drift unnoticed — the test asserts `rc` for each, including the
regression case that has never yet occurred.

## 2026-08-25-pycomplete-28 — `watch` is not `FAIL`, and the polarity table becomes a file

Two ruled adoptions, both small, both closing gaps the previous inch opened.

### One word, two severities

With the regression alarm live, `FAIL` meant **opposite things** in the same
column: on a LIVE guard it gates, on a RETIRED one it is the archive behaving.
A reader scanning a column of `FAIL`s could not tell which was which. Ruled
fleet-wide and adopted verbatim from `sv_divergence_probe.py`: the healthy
retired state prints **`watch`**.

    pyc_div_1_still_divergent  FAIL   …              ← gates
    pyc_div_2_still_divergent  watch  …  [retired row] ← the archive working

*A status word that means "stop" in one row and "carry on" in the next is not a
status word.*

### The three-state table is now a file, not a stub I ran once

`harness/test_divergence_probe.py`, runnable against **any** tier's probe and
defaulting to all of them. Stubs the guard callables, runs no Lean, touches no
register file, and asserts:

| live | retired | rc | meaning |
| --- | --- | ---: | --- |
| pass | not-held | 0 | healthy archive |
| FAIL | not-held | 1 | a live guard gates, as always |
| pass | **HELD** | **1** | **REGRESSION — the divergence returned** |

The third row is the one worth having in a file. It has **never occurred in any
tier**, and a case that has never occurred is exactly the one nobody notices is
missing — it was silent in two tiers simultaneously until it was stubbed and
asserted. **The empty-container law pointed forwards: do not wait for the event
to find out whether the alarm is wired.**

A probe that has not adopted the LIVE/RETIRED partition FAILS the test rather
than being skipped, so the shape spreads by measurement. Both restored tiers
pass today; C inherits the test with its restoration.

### AN INSTRUMENT LIVES IN THE SPACE IT SEARCHES — third instance

The new test is named `test_divergence_probe.py`, which **ends in
`_divergence_probe.py`**, so its own glob matched itself and reported it "NOT
PARTITIONED". That is the third time this family has bitten the register work:

* a grep-based existence check that found its fake guard names **in its own
  source** (§pycomplete-20);
* a substring test that found a name in **its own fixture file**
  (§pycomplete-21);
* now a glob that found **its own file**.

> **Every pattern an instrument writes must exclude the instrument on purpose.**
> The bug is never the pattern being wrong about the world; it is the pattern
> being right about a world that contains the pattern.

## 2026-08-25-pycomplete-29 — the zero-live pole: my own test was asymmetric about a legality my own ruling created

C's restoration is the polarity test's first real subject, and it found the
place the test was **wrong** rather than the place C was.

### The defect was mine, and it was an asymmetry

`c_divergence_probe.py` has `LIVE_GUARDS = {}` — four retired rows, no live
ones. That is the pole §5.0a clause 1 made legal (`rows: []` beside a non-empty
archive), and C names it sharply: *rc comes entirely from the regression alarm;
the probe cannot report anything except a return.* My test printed **"no live
guards to stub"** and counted C as not honouring the table. **Master's fleet
test went red on a correct probe.**

The shape of the mistake is worth more than the fix. One inch earlier I had
written an explicit, labeled `n/a` for the **zero-retired** case, with a
sentence about why a skip would be dishonest. I did not give the **mirror**
case the same treatment — and the mirror case is one *my own clause-1 reading
had just made legal*.

> **An instrument that handles one pole explicitly and the other by accident is
> not symmetric — it is untested at the second pole.** Having written the
> careful branch, I stopped looking for its twin.

### The zero-live expectation, as ruled

Stub only the retired set; assert `rc = 0` with all retired not-held, and
`rc = 1` + alarm with any retired HELD. Printed as its own labeled state:

    c_divergence_probe.py    ZERO-LIVE retired=not-held  rc=0  ok — no live rows; rc is the alarm alone
                             ZERO-LIVE live=FAIL         n/a  no live guards to fail — vacuous, not unmet
                             any retired=HELD            rc=1  ok (regression alarm rang)

**Vacuous, not unmet** — states 1–2 have no live guard to exercise, which is a
different fact from failing them, and the line says which.

Fleet result: **all three probes honour the table.**

### The two failure branches are exercised, not asserted

A test about unexercised cases must not ship unexercised branches. Both new
rejection paths were run against synthetic probes: `NO GUARDS AT ALL` (both
sets empty — a probe that asserts nothing is not a probe) and `NOT PARTITIONED`
(no `LIVE_GUARDS`/`RETIRED_GUARDS` at all). Both fail as intended.

### The same bug, twice in one inch — and I pushed on the second one

Committing the fix above, the register self-test died with `IndexError: list
index out of range`. **I pushed anyway**, because I read the gate output
instead of gating on its exit code — the exact failure being corrected one
level up in the same hour.

The cause is the zero-live pole *again*, one layer down. The self-test builds
its 15 fixtures by mutating `rows[0]` of `sorted(glob(PATTERN))[0]`, and C's
file — legally `rows: []` under clause 1 — sorts first. The moment it landed,
every fixture in the shared checker's self-test broke.

> **Pick by the PROPERTY the fixture needs, never by sort order.** `base[0]` was
> never asking for "a file with a live row to mutate"; it was asking for "any
> file", and got one that could not serve.

Now selected by `rows` being non-empty, with a loud failure if no file has one
— because "no fixture base available" must not read as "passed".

**Three occurrences of one root cause in a single inch**: the test's zero-live
blindness, the self-test's `rows[0]`, and my own review missing both until the
interpreter and the coordinator caught them. The legality clause 1 introduced
has a blast radius through every instrument that assumed a non-empty ledger,
and that radius was not swept when the clause landed.

## 2026-08-25-pycomplete-30 — OPS-148 named negative for the checker, the probe and the polarity test

Per OPS-148 (arch, 9b72995), the four spellings, greped across the three
instruments this lane owns: `harness/divergence_register.py` (the shared
checker), `harness/pyc_divergence_probe.py`, `harness/test_divergence_probe.py`.
**Named negative, not "looks fine": 48 sites, one real defect, one named
dependency.**

### (a) First-element access — 19 sites, **1 real defect, fixed here**

| shape | n | verdict |
|---|---|---|
| `d["rows"][0][...]` fixture mutators | 13 | safe *now* — base guaranteed non-empty, and every file exercised |
| `with_rows[0]` fixture base | 1 | **DEFECT — fixed** |
| `label[0]`/`label[1]`, `declared_as_guard(...)[0]` | 4 | fixed-arity tuples, not growable collections |
| `problems[0][:70] if problems else ""` | 1 | explicitly guarded |

The defect is the one **my own fix for the IndexError left behind**. Selecting
the first file that *has* rows cured the crash but left the subject floating:
when ES filed its register, the 15 defect classes silently stopped being
exercised against the tier that wrote them and began testing **ES's document**.
No crash, no message — a change of subject.

> Sort order was never the property being asked for. The cure is not a better
> pick but **no pick**: the fixtures now run against *every* register file with
> a row — 15 × 3 = 45, and coverage grows with the fleet.

This is arch's generalization at one remove: adding ES to the register set
changed which document an aggregate *selected*, exactly as adding a category
changes every fold.

### (b) `if rows` as a proxy for "this tier has a register" — 6 sites, **0 defects**

`rows = doc.get("rows") or []` normalizes; `for row in doc.get("rows", [])`
iterates; `hasattr(LIVE_GUARDS/RETIRED_GUARDS)` tests partition *presence*, not
population. `if not rows and not retired` is the clause-2 both-empty error and
is deliberately **and**-ed — the clause-1-correct spelling. No site treats a
non-empty `rows` as a proxy for participation.

### (c) Aggregates with unstated identity — 9 sites, 0 defects, **1 named dependency**

- **`ok = True; ok &= …`** (polarity test). Identity `True` means a probe
  entering *neither* branch passes **vacuously**. The only thing preventing
  that is the `NO GUARDS AT ALL` rejection above it — **that guard is now
  load-bearing for the fold's soundness**, recorded so a future edit that
  removes it knows what it is removing.
- `all(… for x in g)` over an empty guards list would be vacuously true, but
  `len(g) != 2` short-circuits first in the same `or` chain: `[]` is rejected
  as "not two".
- `any(needle in p for p in problems)` over empty → `False` → reports NOT
  REJECTED. Correct polarity: empty means fail, not pass.
- `sum(…)` report folds → 0; reporting only.

### (d) Empty-collection messages that read as verdicts — 14 sites, **1 defect, found by RUNNING the thing**

Every one already discriminates: *"no probes found — nothing asserted"* → FAIL;
*"A register checker with no data is vacuous. FAIL."*; *"no register file has a
live row … which is not the same as passing"*; and the two `n/a` lines say
**"vacuous, not unmet"** and *"asserted the day one is archived"*. Watch item:
`held = sum(…)` prints 0 as "none held", which would read as good news over an
empty guard set — unreachable in a valid file only because of the both-empty
rejection.

**And then I ran the probe, and spelling (d) was in it.** Ninety seconds after
filing "(d) 0 defects", `pyc_divergence_probe.py` printed **`FAIL`** in a cold
clone — because `.lake` was cold, the post-build guard correctly declined to
run, and *"nothing was compared"* was folded into the same `False` as *"the
divergence regressed"*. Identical word, identical exit code, opposite meanings:
**a statement about the ENVIRONMENT wearing the costume of a verdict about the
MODEL.**

> **A named negative produced by grep is a claim about text, not about
> behaviour.** The sweep read four spellings across three files and certified
> the one instrument whose defect only appears when it *runs*. Grep cannot see
> a value folded into the wrong state at runtime.

Fixed with a third state: guards return `held is None` for "could not compare",
which prints `no-run` per guard and closes with **`COULD NOT VERIFY (no
comparison ran — not a model verdict)`**. Live guards still fail **closed** —
rc stays 1, unverified never counts as passed — and `_still_divergent`
regression detection reads `held`, so an unverified guard cannot raise a false
alarm either.

### ES's OPS-148 item — named negative, 3 sites, **0 live**

The pre-ruling sentence *"a register file with nothing in it is a claim that the
tier has no debts, and should be deleted rather than filed empty"* survives at
exactly three places, **none of them a live assertion**: `docs/backlog/c.md`
(C's own record of the ruling that superseded it) and
`docs/family-architecture.md:4394` (the ruling quoting the old canon in order to
amend it — *"The canon said …"*). The shared checker's live text already carries
the ruled form verbatim: `rows: []` beside a non-empty `retired_rows` is *"a
real and useful claim … so it is LEGAL"*, and `DELETE IT` fires only on
`not rows and not retired`. **Code and text agree; no edit made.** Confirmed
before ES's row retires rather than on the day it does.

### Recorded from the landing

> **A category added to a set changes every aggregate over that set — every
> fold written before the ruling silently treats the new kind as the old one.**
> Relay norm: **the first tier through a new ruling publishes the traps, not
> just the code.**

The `with_rows[0]` defect is the sharpest evidence for the first half: the fold
did not fail, it quietly redirected.

## 2026-08-25-pycomplete-31 — exit 143: the RSS discipline is machine-scoped in its claim and lane-scoped in its mechanism

pyc9's depth-split tenure died at 13:30:31 after 41 minutes of build:

    ✖ [884/911] Building Examples.python.sunfish.genmoves_ray (547s)
    error: Lean exited with code 143
    [13:30:31] GATES NOT RUN (build red — aborted triad)

**It was not a red build, and `genmoves_ray` is a file this commit never
touches.**

### Ruling out the fleet's own guard, by mechanism not by guess

triad's A16 guard kills with **`kill -9`** (→ exit **137**) and prints
**`RSS KILL LINE (A16, per-process)`** before it does. The log contains
**zero** KILL LINEs, and 143 is **SIGTERM**, not SIGKILL. So the guard did not
fire — which also means `lean` stayed **under** the 5 GB/proc cap. Nothing the
fleet measures was exceeded.

### What was actually true of the box

| | at failure |
|---|---|
| physical free | **~56 MB** |
| swap | **12002 M / 13312 M used (90%)** |
| load (2 cores) | **15.40** |
| `genmoves_ray` | **547 s**, against **18 s** in `lm_build.log` — **30×** |

And the cause is **outside the fleet entirely**: `lake build
AlgebraicComplexity …` out of `~/repos/matrix-m…`, a different repository,
running throughout and still running after.

*Honest limit on this claim*: I could not find a jetsam record naming the
`lean` process, so an OS-level memory kill is **inference from convergent
evidence** (SIGTERM, no KILL LINE, 30× slowdown on an untouched file, 90% swap),
not a log citation.

### The finding, and it is in triad's own header two rules apart

> line 110 — *"the lock, the ticket, the RSS discipline are about **THE
> MACHINE**, not about the repository"*
> base rule 6 — *"never kill another lane's processes — kills by **PARENTAGE**
> only"*

Both are right, and together they leave a gap:

> **The RSS discipline protects the machine FROM a lane; it cannot protect a
> lane FROM the machine.** Its claim is machine-scoped, its measurement is
> subtree-scoped, and a resource is only as governed as it is *measured*.

Base rule 6 should not change — never killing another lane's processes is
correct, and doubly so when the competitor is another repository whose work is
none of the fleet's business.

### The word was wrong, and it is the defect I fixed in my own probe an hour ago

`GATES NOT RUN (build red — aborted triad)` — **the build was not red, it was
killed.** triad already distinguishes *"resource kill, not a red build"*
(header line 21), but **only for kills it performs itself**. A kill from
outside lands in the same channel as a genuine compile error.

That is precisely the shape I fixed in `pyc_divergence_probe.py` at
`8e4ebaf`: *a statement about the ENVIRONMENT wearing the costume of a verdict
about the code.* Same defect, one level up, in the instrument every lane trusts.

**Proposed (arch's call, not mine):** on a nonzero build exit whose code is
signal-shaped (**137/143**) with **no KILL LINE of our own**, sample machine
memory and report `BUILD KILLED FROM OUTSIDE — box at N MB free, swap X%` rather
than `build red`. The distinction is worth real time: this cost one tenure plus
a **4593 s** queue wait, and any lane can lose the same.

### Re-queued, not retried blind

Rebased onto master tip `9c5b3f8` first (safe to do: the lock was released, and
master now carries **both** C's `rows: []` register **and** the fixed checker,
so the self-test gate passes for the right reason). Verified before enqueue:
self-test green at **15 × 3**, and the six certificates **byte-identical** to
pre-split after the rebase. Ticket `…-21614-pyc9`, tree `4a4501494f46`.

## 2026-08-25-pycomplete-32 — genmoves_ray DOES shard; my earlier "no" came from a substring grep

`genmoves_ray` killed pyc9's first tenure (pycomplete-31). Re-censused it while
the re-run built, and **the verdict I gave the coordinator was wrong.**

### What I reported before, and what is actually true

I reported *"`genmoves_ray` is not a leaf — `genmoves_scan`, `genmoves_drain`
and `sf_order/transport` all `open` it, so it does not shard naturally without
a facade."* That came from `grep -rln 'genmoves_ray'` — **a substring match,
which counts a prose mention as a dependency.** Anchored on real syntax:

| file | relationship |
|---|---|
| `genmoves_scan.lean` | **the only true `import`** |
| `genmoves_drain.lean`, `sf_order/transport.lean` | `open` the namespace, reached transitively |
| `genmoves_theorem.lean`, `LeanModels/Python/PayloadBlind.lean` | **prose mentions only — not dependents** |

> **I made the exact error the register checker was hardened against.** ES
> flagged the substring test one day ago; I replaced it with anchored `def` +
> `#guard` and wrote a fixture where the name lives only in a comment. Then I
> ran a census whose evidence was a bare `grep -rln` — and two of its five hits
> were names living only in a comment.
>
> **Hardening an instrument does not harden the hand that reaches past it.**

### It shards, and the constraint is the NAMESPACE, not the import

One direct importer makes a facade trivial. The real constraint is the two
transitive `open`ers: `open Examples.python.sunfish.genmoves_ray` must keep
resolving, so **the shards must declare INTO the parent namespace** rather than
into their own. Lean permits many modules to contribute to one namespace, so
every current `open` and `import` site stays byte-identical.

Seams are already there — 173 theorems in clean families:

    pB 36 | rayBody 21 | ray 20 | cast 22 (rCast 8 + castH 7 + castA 7)
    pawn 18 (pawn 11 + pProm 7) | remainder ~56

with the 31 `def`s lifting into a `genmoves_ray_common.lean` exactly as
`boundProbe`/`posMid` lifted into `pins_common.lean`.

### And the reason to do it is MEMORY, not minutes

The sharding task was dispatched on **build time**. `genmoves_ray` is the case
where it is **build survivability**: a 3740-line module elaborating 173
theorems in ONE `lean` process is the fleet's memory cliff, and splitting it
lowers peak RSS per process whether or not it saves a second of CPU. **A shard
that saves no time and prevents an OOM is still worth landing** — which is not
what the original framing would have predicted, and is the reason to revisit a
target that was correctly de-prioritised on speed alone.

## 2026-08-25-pycomplete-33 — genmoves_ray shard: the prediction, registered before the tenure

### The family split, named

Full prefix census of the 173 theorems (the earlier "top 8" truncated prefixes
and undercounted `pB*` and `cast*`):

| shard | families | theorems |
|---|---|---|
| `genmoves_ray_pB` | `pB0` 10, `pB1` 11, `pB2` 9, `pB3` 5, `pB3Test` | ~36 |
| `genmoves_ray_ray` | `ray` 20, `rYield`/`rPawn`/`rCrawl`/`rStop`/`rRest`/`rYieldVal`/`rPawnTest` | ~32 |
| `genmoves_ray_cast` | `castH` 7, `castA` 7, `rCastH` 3, `rCastA` 3, `cH`/`cA`/`cHVal`/`cAVal`, tests | ~26 |
| `genmoves_ray_pawn` | `pawn` 11, `pawnQ`, `pawnBody`, `prom*` 7, `pProm*` 6 | ~25 |
| `genmoves_ray_rayBody` | `rayBody` | 21 |
| `genmoves_ray_common` | the 31 `def`s + shared `open Ref` blocks | — |
| `genmoves_ray` (facade) | imports the five; keeps the 37 `#guard`s | — |

~30 structural singletons (`Heap`, `heapEq`, `flatten`, `absInt`, `RayLocals`,
`RayFrame`, `SlotOnly`, …) land in `_common` or the facade **by a dependency
census at the inch, not by this table** — I have not verified which are
infrastructure for the families and will not guess.

**Namespace continuity is the load-bearing constraint**: every shard declares
into `Examples.python.sunfish.genmoves_ray`, so `genmoves_scan`'s `import` and
`genmoves_drain`/`transport`'s `open` stay byte-identical.

### The memory prediction, and it points TWO ways

> **Largest single-process peak: DOWN. Concurrent aggregate: UP or flat.**

Not a hedge — a consequence. Each new `lean` process **re-pays Lean's constant
import baseline**, so the per-process peak falls only by the *module-specific*
portion (never by 1/6), while N shards building concurrently can cost **more**
in aggregate than one large module. Under a per-process cap that is a win;
**on a starved box, which is what actually killed pyc9, it could be a loss.**
Registering both directions is what makes the inch falsifiable rather than
self-confirming.

### The evidence — and why neither named proxy can supply it

Both proxies the dispatch offered are **too weak for this claim**, and saying so
is the point:

- **Job count** (911 → ~917) is uninformative about memory *by construction*.
- **Largest module's elaboration time** is a *weak* proxy: Lean modules can be
  slow-and-small (deep unification, little allocation) or fast-and-large.

So I am supplying the missing instrument rather than reading a proxy that
cannot answer. `/private/tmp/rss_sampler.py` samples `ps` every 10 s, attributes
by **tree path** (excluding the external `AlgebraicComplexity` build competing
for the same RAM), and records **per-module peak** *and* **concurrent
aggregate** — the two numbers the prediction splits on. It is not Lean
execution, so it touches no lock, and it writes nothing to the frozen tree.

**The baseline is being captured NOW, during this unsharded run** — that window
closes when the build ends and cannot be reopened without another tenure.
First samples: `genmoves_ray.lean` **469.59 MB** and climbing.

Two caveats recorded beside every figure rather than discovered later:

1. A sampled maximum misses spikes shorter than the interval — **every number
   is a lower bound.**
2. **Under swap pressure RSS measures what the OS *let* the process keep, not
   what it wanted.** A before/after comparison across different pressure
   regimes is therefore *not fair*, so load and swap are recorded at every
   peak, and a cross-regime comparison will be reported as **inconclusive**
   rather than quietly averaged.

## 2026-08-25-pycomplete-34 — the depth-split verdict, and the memory premise falsified by my own instrument

### The verdict: the critical path prediction holds

`pins_bound_*` elaboration, from the killed run's log (it built these before it
died, and the green re-run reused their `.olean`s):

| shard | nodes | time | s/node |
|---|---|---|---|
| `pins_bound_mid_d1` | 71 | **65 s** | 0.92 |
| `pins_bound_mid_d2` | 826 | **515 s** | 0.62 |
| `pins_bound_mid_d3` | 653 | **454 s** | 0.69 |
| `pins_bound_h` | — | 277 s | |
| `pins_bound_tac` / `searcher` / `end` | — | 51 / 26 / 10 s | |

**Predicted critical path ~7.8 min (468 s) set by `_mid_d2`; actual 515 s —
within 10%.** The node-count model (71/826/653) predicted the split well;
s/node is near-constant, which is why counting nodes beat counting guards.

### And the cost the prediction ALSO named: the total went up

`65 + 515 + 454 = 1034 s` against the **875 s** previously measured for the
unsplit `posMid` — **~18% more total CPU**. Splitting lowers the critical path
and *raises* the total, because each shard re-pays the import cost. That is the
**same mechanism I registered for memory** hours earlier, showing up in time.
*Soft*: 875 s came from a different run under different load, so this is a
cross-regime comparison and I am reporting it as directional, not exact.

`_d3` at 454 s is nearly `_d2`'s equal, so the split is **not balanced** — a
further win needs the d2/d3 pair split again, not a fourth sibling.

### THE MEMORY PREMISE IS FALSIFIED — and my own instrument did it

Peak RSS, sampled during the green run (**scope: only the ~15 modules this run
actually rebuilt**, since `.lake` was warm — not the full 911):

     1989.88 MB  bound_depth.lean
     1590.55 MB  move_gate.lean
     1465.55 MB  move_residue.lean
     1383.64 MB  genmoves_drain.lean
     1318.58 MB  value_bound.lean
      ...
      589.94 MB  genmoves_ray.lean

> **`genmoves_ray` is not the memory cliff. `bound_depth` is 3.4× larger in the
> same run, same regime — a fair comparison.**

`genmoves_ray` died in the first tenure not because it is the largest, but
because it was **the module that happened to be running when the box ran out**.

> **Under machine-wide starvation the victim is chosen by TIMING, not by SIZE.**
> Every "this module is the fragile one" conclusion drawn from *which module
> died* is an artifact of scheduling.

### And the lane never had a memory problem at all

Concurrent aggregate peak **2301.78 MB** against a **10240 MB** chain cap and a
**5120 MB** per-process cap. The lane used **22%** of its chain budget at peak.
**No topology change to any fleet file would have prevented that kill** — it was
external oversubscription by another repository, and sharding cannot fix a
machine-wide shortage.

### So the approved justification is wrong, and I have to say so

I reframed the `genmoves_ray` shard as **"survivability, not minutes"** and it
was approved on that basis. **The measurement refutes the reframe.** But the
same run makes the *original* case strongly: `genmoves_ray` took **962 s** — the
single largest elaboration in the tree, ahead of `_mid_d2`'s 515 s.

**The inch survives; its justification reverts to the one I talked us out of.**
Minutes, not survivability. Worth stating plainly rather than quietly letting an
approved-but-wrong premise carry a tenure — the prediction discipline worked
exactly as intended, falsifying a claim *within the hour* and *before* the
tenure was spent on it.

## 2026-08-25-pycomplete-35 — genmoves_ray does NOT shard: a naming convention is not a dependency structure

The dependency census I promised to run **at** the inch rather than guess in the
registered table **falsifies the inch**. Recording it before a tenure was spent,
which is what the census was for.

### The registered table read families off NAME PREFIXES

I proposed `pB` ~36, `ray` ~32, `cast` ~26, `pawn` ~25, `rayBody` 21 and a cheap
`_common` holding "the 31 `def`s". Every one of those numbers came from
counting **name prefixes**. The reference graph tells a different story.

### First, a flaw in my own split rule, caught before generating files

I classified a declaration as shared when **≥2 families** referenced it. Wrong:
a declaration used by exactly **one other** family would stay family-local while
a different file needed it. The correct rule is *referenced by any family other
than its own* — and it moves the numbers enormously:

| bucket | ≥2-family rule | correct rule |
|---|---|---|
| `_common` | 1008 lines (27.6%) | **2549 lines (69.8%)** |
| largest family (`ray`) | 851 | 346 |
| `_common` declarations | 52 of 205 | **123 of 198** |

### And then the real obstacle: the families are CYCLIC

`X -> Y` = X uses Y. **11 mutual pairs among 6 families**:

    ray <-> rayBody (53/2)   cast <-> misc (80/11)   cast <-> pB (4/10)
    cast <-> pawn (4/18)     cast <-> ray (3/10)     pB  <-> pawn (3/36)
    pawn <-> ray (29/12)     misc <-> ray (23/74)    misc <-> pawn (6/66)
    misc <-> pB (1/54)       pawn <-> rayBody (1/1)

**Lean modules cannot import cyclically.** The family split is therefore not
merely suboptimal, it is **structurally impossible as designed**. Collapsing
every cycle into `_common` is the only legal version, and that is the 69.8%
figure: critical path `2549 + 346 = 2895` lines = **79.2%**, a paper **1.26×**
that the import tax (**+18%** measured on the pins 1→3 split, and this is 1→7)
would erase completely.

### The law

> **A naming convention is not a dependency structure.** `pB`, `ray`, `cast`,
> `pawn` are how a human grouped 173 theorems for reading. The reference graph
> says they are **one organism**, and the graph is what the compiler obeys.

This is today's third instance of one root: **text-shaped evidence standing in
for structural evidence** — the substring grep that invented `genmoves_ray`'s
importers, the `rows[0]` fold that picked a file by sort order, and now a shard
plan built from name prefixes. Each time the text was easy to read and wrong.

### Consequence

**The genmoves_ray shard is withdrawn, on the census, before the tenure.** Its
962 s is topologically irreducible: no arrangement of files makes that theorem
web cheaper, because the web is the cost. A win there needs **proof-level** work
(cheaper tactics, weaker lemmas), not file moves — a different kind of inch,
priced separately.

**The d2/d3 pair-split becomes the next inch.** At 515 s it is smaller than 962 s,
but it is *known-splittable* — the depth axis is a real parameter, and the
landing already measured its shards as independent. **A 1.7× on a splittable
515 s beats a 1.26× on an unsplittable 962 s**, and the sequencing argument that
put genmoves_ray first (962 > 515) assumed a splittability the census has now
refuted.

## 2026-08-25-pycomplete-36 — pricing the d2/d3 pair-split: take the exit, and the reason is stronger than the threshold

### The local numbers, per the discipline

Fitting `time = import + nodes x rate` on the **three d-shards measured in one
run** (65 s/71, 515 s/826, 454 s/653):

> **per-node 0.6144 s · per-file import 27.2 s**

Pair-split halves: **d2 → 2 x 281 s**, **d3 → 2 x 228 s**. New family path is
`max(281, 228, 277, 65, 51, 26, 10)` = **281 s**, so **515 → 281 = 1.83x**,
above the 1.3x line. Import-tax increment is **+2 files x 27.2 s = +54 s** of
total CPU — on the books, as noted.

**Imbalance target**: the family floor is not d2 at all, it is **`pins_bound_h`
at 277 s**. Splitting d2/d3 below ~280 s buys nothing, so the family's best
achievable is **1.86x** no matter how finely the depths divide.

### And it does not matter, because these modules are LEAVES

| module | time |
|---|---|
| **`pins_clock_walk`** | **1336 s** ← the ceiling |
| `genmoves_ray` | 547 s |
| `pins_bound_mid_d2` | 515 s |
| `pins_bound_h` | 277 s |

`pins_bound_*` are **leaf modules — nothing imports them.** A leaf is never on
the dependency critical path: it can always be scheduled beside other work
whenever a worker is free. **For a leaf, only its TOTAL CPU matters, and
sharding increases that.**

Both load regimes agree, which is what makes this robust rather than a
one-measurement artifact:

- **Latency-bound** (12 cores, quiet box): floor is `pins_clock_walk` at
  **1336 s**. The bound family sits at 515 s, already **2.6x below the
  ceiling** → splitting saves **exactly zero**.
- **Throughput-bound** (measured: 4447 s elaboration / 2474 s wall = **1.80
  effective workers** under contention): splitting adds 54 s CPU ≈ **+30 s
  wall** → **negative**.

> **Zero in one regime, negative in the other. The exit is the right call.**

### The corollary I have to state about the split I just landed

The same argument applies **retroactively**. The depth split delivered its
predicted 1.88x on the *family's* critical path — but the bound family was
**already below the fleet ceiling**, and it is a leaf. So that 1.88x bought
**no wall-clock time**, while costing **+18% CPU (+159 s)**.

The dispatch's premise — *"pins_clock and pins_bound together are ~85% of every
full spine build's elaboration"* — is a **throughput** statement. Sharding is a
**latency** instrument. It improves the quantity that was not binding and
worsens the one that was.

> **Sharding a leaf optimises a number that cannot be on the critical path.**
> If 85% of elaboration lives in two families, the throughput fix is to make
> those proofs *cheaper*, not to spread them across more files.

### Where the remaining win actually is

**`pins_clock_walk` at 1336 s** — the ceiling, 2.6x the next module. In the
latency-bound regime it *alone* sets the floor, so it is the only module whose
improvement is guaranteed to move the build. Whether it is splittable is
**unknown and must be censused before it is priced** — `genmoves_ray` looked
splittable by name and was not.

**Recommendation: stop the sharding program here**, and re-aim at proof cost
(throughput) or at `pins_clock_walk` (the one binding latency).

## 2026-08-25-pycomplete-37 — pins_clock_walk census: NOT splittable, and the blocker is cost, not soundness

Bounded question: can the 13-step fuel-4M walk be checkpointed into k
certificates whose composition implies the original claim? **No.** Two
independent grounds, either of which is fatal.

### The file, and the checkpoint pattern it already contains

127 lines, two private defs, **one** `#guard` — the 1336 s *is* that one
certificate. And it already checkpoints **in-file**: it runs
`searchStepsW sa g 12 w` to get `(rows, w12)`, asserts `w12.clock == [0,0]`,
then runs `searchStepsW sa g 1 w12` for step 13. The structure the dispatch
asks for exists. The question is only whether it can cross a **module**
boundary.

### Ground 1 — the atomic step is 61% of the walk

Node deltas from the guard's own cumulative counts:

    step  6: + 238    step 11: + 190    step 12: +  99
    step 13: +1258   <- 61.3% of 2053, in ONE `stepIter` call

Step 13 runs the generator to its next yield; **nothing can subdivide it.** So
even a *free, perfect* split caps the win at `2053/1258` = **1.63x**
(1336 s → ~819 s). Every checkpoint scheme is bidding against that ceiling
before it pays for anything.

### Ground 2 — the checkpoint state cannot be written down

To host step 13, another module needs `w12`. Lean modules communicate through
**terms**, so there are exactly two options:

1. **Recompute `w12`** — file 2 pays 12 steps *plus* step 13 while file 1 pays
   12 steps: **25 steps against the current 13.** Strictly worse.
2. **Pin `w12` as a literal.** But `w12` is a whole `World`: the searcher's heap
   after **795 nodes**, including `tp_score` (keyed `(pos, depth)`) and
   `tp_move` (keyed `pos`) — dictionaries whose keys are Position objects each
   carrying a **120-character board string**. Hundreds of entries.

And a `def w12 := …` exported from file 1 does **not** rescue option 2: kernel
reduction in the consuming module **unfolds the definition and recomputes it**.
There is no cross-module memoisation of kernel evaluation, so anything short of
a true normal-form literal is option 1 wearing a different hat.

> **A checkpoint saves work only if the checkpoint state is cheaper to WRITE
> than to RECOMPUTE.** For a whole-machine state — a heap mid-search — it never
> is.

### Seed-splittable vs checkpoint-splittable

This is the clean distinction the two targets draw between them:

- `pins_bound_mid` **split by SEED**: every shard re-derives its state from
  `posMid`, a *tiny board literal*. Cheap to write, so the split was legal and
  free.
- `pins_clock_walk` has **no seed at step 12**. Its intermediate state *is* the
  accumulated search. There is nothing small to write down.

**The obstacle is cost, not soundness.** Pinning `w12` explicitly would be a
*stronger* conjunction, exactly as the dispatch allows — the certificate would
improve. It is simply unwritable.

### Not priced, per instruction

`price only if yes` → **not priced.** For the record of what is being given up:
the 1.63 x ceiling would drop the fleet floor 1336 s → ~819 s, and since
`pins_clock_walk` is the *ceiling* it is the one module where a split provably
moves the build. That ~517 s is real and is blocked by an unwritable checkpoint,
not by a missing lemma.

**Anchored-check correction**: `pins_clock_walk` has **one** real importer
(`pins_clock.lean:47`); `pins_bound_mid.lean` only names it in prose. A
substring grep would have reported two — the `genmoves_ray` error, avoided by
running the anchored check first this time.

### Remaining lever

Unchanged and now sole: **proof cost inside step 13.** That is throughput work
on the ray/bound web, priced separately by whoever takes it, and it starts from
this census rather than from scratch.

## 2026-08-25-pycomplete-38 — the refusal frontier, re-derived from the tree

Re-run rather than re-quoted, per the standing correction that analog's law
applies to one's own ledger. Fresh against the tree at `81fe4ae`:

    GRAMMAR   138 witnesses: 106 MATCH, 32 REFUSE, 0 other
    WHITELIST 124 rows in 51 classes (unsupported=117, boundary-freeze=7)
    SCRIPT     15 rows in 10 classes
    oracle Python 3.9.19 — 0 drifts

**32 of 138 productions refuse.** Grouped by *what kind of thing blocks them*,
which is the only grouping that tells you what an inch would cost:

| group | n | blocker |
|---|---|---|
| **A. Layout-dependent** — 3 dict-churn rows, `Set`, `SetComp` | 5 | **permanent**: entries-array layout / hash order |
| **B. Async** — `AsyncFunctionDef`, `AsyncFor`, `AsyncWith`, `Await` | 4 | coroutines + event loop; one coherent large project |
| **C. Numerics** — `float`, `complex`, `bytes`, `Div`, `Pow-negative`, `MatMult` | 6 | IEEE-754; the fleet's `softfloat` lane's tier, not this one |
| **D. Module system** — `Import`, `ImportFrom` | 2 | real imports vs. the tier's static whitelist binding |
| **E. Scoping** — `Global`, `Nonlocal` | 2 | pure scoping semantics, no layout dependence |
| **F. Dict views** — `.keys`, `.values`, `.items`, keys-set-algebra | 4 | a new object kind; set algebra re-enters group A |
| **G. Near-term** — `iter`-of-list, `del` non-dict, `DictComp`, `With`, `Raise`-expr, 2x `AnnAssign`, `ellipsis`, `RShift`-budget | 9 | ordinary modelling work |

**Group A is the floor.** Five of thirty-two are not "not yet" but "not ever
without guessing layout" — the honest REFUSEs the charter protects. The
reachable surface is therefore **27**, not 32.

### The next inch, priced against the tree

**`iter()` over a list** (`dict.iter-of-list` in grammar; `iter.non-dict-receiver`
in whitelist — **one change, two rows**). Evidence it is small:

- `GenFrame.forList (target) (a : Addr) (i : Nat)` **already exists** — a live
  index cursor over a list at an address. `enumList` exists too.
- `iterDict` was built as *"`enumerate`'s frame without the index"*. `iterList`
  is the same subtraction applied to `enumList`, and the stepper already serves
  every consumer through `stepIter`.
- The current refusal says the blocker is that *"CPython's `list_iterator` is
  its own cursor"* — an object-kind gap, **not** an undecidability.

**And it opens no debt, which is why it goes first.** The dict cursor forced
`pyc-div-1`/`pyc-div-2` because dict iteration under mutation depends on the
entries array. A `list_iterator` holds a plain `it_index` and yields
`seq[it_index]` while `it_index < len(seq)`: its behaviour under mutation is
**fully determined by index against current length**. So this closes a frontier
row *without* declaring a divergence — the opposite of the last cursor inch.

Census-first still applies at the inch: the arm placement and the `heapFree` /
`genAllocFree` allocator censuses must be re-derived before any edit, exactly as
`iter`-over-dict required two independent census updates.

## 2026-08-25-pycomplete-39 — `iter()` over a list: one change, two rows, no debt

### Census first, and it produced a named negative

Arm placement came from the **15 `iterDict` sites** (the shape to mirror) and
the **`enumList` sites** (the address+index shape a list cursor needs). Nine
edits: the constructor and its `WF` arm (`Runtime`), `iterFrame` plus
`genBreak`/`genContinue`/trunk-`execGen` (`Semantics`), the stepper
(`Monadic/Eval`), and the three proof-side arms (`Obs`, `ClockErase`,
`PayloadBlind`).

**Allocator census — checked, no change needed.** `iter`-over-dict required two
independent updates (`Expr.heapFree`, `Expr.genAllocFree`), so I checked both
rather than assume this inch was lighter: **both already exclude `"iter"`**
(`Semantics.lean:4221`, `:4379`). The builtin *name* is unchanged; only its
accepted receiver widens. A named negative beats a guess in either direction.

### The stepper is `enumList` with the tuple taken off

Exactly as `iterDict` is `enumDict` with the tuple off. `Heap.get?` re-reads
the list every step and `cur < xs.size` compares against its **current** size —
precisely `list_iterator.__next__`'s `it_index < PyList_GET_SIZE(seq)`.

### Why this opens no debt

The dict cursor owed `pyc-div-1`/`pyc-div-2` because dict iteration under
mutation depends on the entries array. **A list cursor consults no layout**:
its behaviour is determined by index against current length. The row closes
with **zero** register rows added — the opposite of the last cursor inch.

### Witnesses, and the one honest gap

Three rows, all against the pinned oracle (**CPython 3.9.19**, values measured
not reasoned):

| witness | oracle |
|---|---|
| `iter_list_recv(7)` | **7** |
| `iter_list_grew(7)` — append after the cursor exists | **16** |
| `iter_list_exhausted(7)` — dead cursor, `next(it, 100)` | **107** |

**NOT witnessed: the SHRINK direction**, and the reason is upstream rather than
oversight — writing that witness needs `del xs[i]`, which is *itself* a refused
frontier row (`del.non-dict-receiver`). The arm handles it by construction, but
no test reaches it until that row lands, exactly as `pyc-div-1`'s witness waited
on `except_builtin`. **Named in both docstrings so the gap has an owner rather
than a hope** — a claim resting on untested code is the defect this lane has
now catalogued six times.

The lab function was renamed `iter_list_recv_still_loud` → `iter_list_recv`: it
is no longer loud, and a name that says otherwise is a false claim about the
tier.

### Frontier movement

`dict.iter-of-list` (grammar) and `iter.non-dict-receiver` (whitelist) —
**one change, two rows**. Reachable surface **27 → 26**; group A's permanent
five unchanged.

## 2026-08-25-pycomplete-40 — the gate caught a step I did not know existed, and the corpus has five more of it

`pyc10` came back **BUILD GREEN, gates RED**: `diff_test` failed with

    iter_list_recv(7)       ok: 7    exn: NameError   MISMATCH
    iter_list_grew(7)       ok: 16   exn: NameError   MISMATCH
    iter_list_exhausted(7)  ok: 107  exn: NameError   MISMATCH

Oracle right, model `NameError` — **the model could not see the functions at
all.** The cause is a pipeline step my census never reached: a lab's Python is
not read by the model. `AGENTS.md` step 1 dumps it to a JSON envelope
(`extractors/python/extract.py`), and `spec.lean:39` does
`load_program dict_lab from "…/dict_lab.json"`. **I edited the `.py` and left
the `.json` a day stale**, so the Lean side still held
`iter_list_recv_still_loud` and had never heard of the three new functions.

> **A census of "every site that mentions `iterDict`" cannot find a step that
> mentions nothing.** My arm-placement census was correct and complete for the
> question it asked, and the missing step was invisible to it because it lives
> in a *different pipeline stage*, not in a different file.

Regenerated: `−iter_list_recv_still_loud`, `+3` functions, 108 → 110 top-level
nodes. It also corrected the envelope's **frontend stamp `3.14.5` → `3.9.19`** —
beyond the inch's scope, but a wrong CPython stamp on a tier that models 3.9.19
is not something to leave once seen.

### And the corpus has five more, found by asking

Re-extracting all **61** `.py`/`.json` pairs and diffing:

| file | drift |
|---|---|
| `assert_lab`, `del_lab`, `exc_lab` | **frontend stamp only** — extracted with CPython **3.14.5**, content identical |
| `bench_heapq_sift` | **content** — a node `kind` differs |
| `sunfish` | **content** — current `extract.py` emits a `key` field at `sunfish.py:511` that the committed envelope predates |

`sunfish.py:511` is `del self.tp_move[next(k for k in self.tp_move if k != self.root)]` — the genexp-del line. Both content drifts are **extractor
evolution, not source drift**: the `.py` files are unmodified in git.

**Nothing gates any of this.** A generated artifact is checked in beside its
source and nothing checks they still agree; `mtime` is useless (a fresh clone
randomises it), so the test must be *re-extract and compare content, ignoring
the frontend stamp*. That is 61 files in seconds. **Not done here** — it would
red on five files today, and fixing those is someone's inch with its own
review, not a rider on mine. **Flagged for QoL** as the same shape as the
`backlog-index --check` hole: a fleet-wide corpus with no gate.


### Correction to pycomplete-38's grouping (softfloat verification, 2026-08-25)

**My group C was wrong, and the defect is worse than the count.** I placed
`const.bytes`, `const.complex` and `op.MatMult` under "Numerics" because they
*look* numeric. That is grouping by **name**, not by **blocker** — the exact
error named one entry earlier ("a naming convention is not a dependency
structure"), committed *inside the instrument offered as its fix*. Proposing
blocker-kind grouping and then populating it by name is the finding here.

`docs/completeness.md:84` settles `MatMult`: it *"costs a program nothing — no
operand type in CPython too."* Nothing to do with IEEE-754.

**And a correction back up the chain.** Grepping all three corpora for a
float-printing refusal returns **nothing**, and it cannot: `const.float`
refuses, so no float can be constructed to print. The `str()`/`repr()`-of-float
item is therefore **not a row omitted from the 32** — it is a **latent row**
that comes into existence only once floats can be constructed. The honest form
for softfloat's §9.0 is **3 existing pyc rows + 1 latent requirement**, not 4
named rows: landing float arithmetic *without* decimal printing closes three
and creates the fourth.

| group | n | change |
|---|---|---|
| A. Layout-dependent | 5 | — |
| B. Async | 4 | — |
| **C. IEEE-754 → softfloat** | **3** | was 6 |
| **Payload types** — `bytes`, `complex`, `ellipsis` | **3** | new group |
| D. Module system | 2 | — |
| E. Scoping | 2 | — |
| F. Dict views | 4 | — |
| G. Near-term | 9 | −`ellipsis`, +`MatMult` |

Sums to 32, checked. **Flag for group G**: `MatMult` closes trivially and buys
nothing — admitting it moves the count without moving the capability, which is
"optimising below the floor is motion, not progress" in frontier form. Take it
last, or knowingly as bookkeeping.

### And the exit-143 metric, corrected by the gate it produced

triad's new pressure gate (`acquire_check`) descends from that finding, and its
comment rejects the metric the finding led with: *"NEVER `vm.swapusage` … a
high-water mark … a gate keyed on it would defer forever on any box that has
ever swapped … 90% swap against a kernel level of 2, disagreeing in KIND."*
That 90% was my headline number. **The finding stands; the metric in it does
not** — the condition was real, the instrument was wrong, and only measuring
both side by side caught it.

## 2026-08-26-pycomplete-41 — the envelope cleanup is not cleanup: it is the delivery step for four earlier inches

### Priced before doing, and the price changed once measured

`envelope_fresh --tier python` on master: **FRESH 59, STALE 2**. The three
stamp-only files pass it already (the manifest excludes stamp keys), so the
gate's blocking set was two files. What those two contain is the whole story:

| envelope | transition | count |
|---|---|---|
| `bench_heapq_sift` | `Unsupported → BinOp` | 1 |
| `sunfish` | **`Unsupported → DeleteSubscript`** | **2** |

**These are not cosmetic.** A stale envelope was recording *supported* syntax as
`Unsupported`, so regenerating is a **capability change**, not a refresh.

### And the two sunfish nodes are my own inches' lines

    line 511  del self.tp_move[next(k for k in self.tp_move if k != self.root)]
    line 541  del self.tp_score[next(iter(self.tp_score))]

Line 541 is the `iter(d)`+`next` flagship line (`bdd96d7`); line 511 is the
genexp-over-keys eviction (`cf13932`). **The tier gained both capabilities and
the flagship's envelope never picked them up** — the model has been ingesting
both eviction lines as `Unsupported` the entire time, while the corpus rows in
`dict_lab` exercised the capability and passed.

> **A capability is not delivered when the model supports it. It is delivered
> when the artifact the model actually loads is re-extracted.** Four inches
> landed green against a flagship that never saw them.

### Why no certificate can move, and it is checkable

Both statements sit inside `if len(self.tp_move) > TABLE_SIZE` /
`if len(self.tp_score) > TABLE_SIZE`, and **`TABLE_SIZE = 10**6`**. The deepest
pinned walk reaches **2053 nodes**, so neither branch is reachable by any
certificate in the tree. The model's refusal is demonstrably **lazy**, not
eager: the pins battery already runs `bound()` today with those `Unsupported`
nodes inside it.

**Falsifiable prediction: every certificate is byte-identical after this
change.** If one moves, this argument was wrong and the inch stops.

Corroborating: **zero** `Unsupported` mentions anywhere in `Examples/python/sunfish/*.lean`, so no proof pattern-matches the stale shape.

### The price

- **Work**: 5 envelopes regenerated (2 content, 3 stamp), gate wired. Mechanical.
- **Build**: a **full SPINE tenure** — `sunfish.json` feeds `pins_common.lean`,
  which has **13 direct importers** (the whole pins battery, `pins_clock_walk`
  at 1336 s included).
- **Risk**: low *and argued*, not asserted — see the reachability argument.
- **Value**: corrective rather than capability-adding. No *new* certificate
  becomes provable: witnessing an eviction needs 10⁶ table entries, which
  kernel evaluation will never reach. What it buys is **the model matching the
  program**, which is a standing law here, plus it unblocks `--tier python`.

Result after cleanup: **FRESH 61, STALE 0, exit 0.**

### A third instance of the under-specified selector

Verifying `source_file`, my `find Examples -name "sunfish.json" | head -1`
matched **the C tier's** envelope and reported `tools/ctwin/sunfish.c` — a
false alarm on my own change. There are two `sunfish.json` files. Same shape as
the substring grep that invented `genmoves_ray`'s importers and the `rows[0]`
fold that picked a file by sort order: **a selector that does not say which one
it means will eventually mean the wrong one.**

### Correction: the trap was documented at the exact site I edited

My "discovery" that `load_program` is an untracked build input was a
**rediscovery**. `pins_common.lean:17` has said so all along:

> *ENVELOPE NOTE (the standing trap): `load_program` does not track its JSON as
> a build input and lake hashes CONTENT — after re-extracting `sunfish.json`,
> make a real edit HERE (this comment is the place); the import chain then
> rebuilds every pin file.*

There is even a numbered **re-extraction log** to append to, and `proof.lean`
carries per-pass notes saying *"this comment is the content edit that forces
re-elaboration."* The convention exists, names its own place, and I regenerated
the envelope without reading the file that loads it.

> **Census-first means reading the file you are about to invalidate, not only
> the files you are about to edit.** My blast-radius census found the three
> loaders and counted their importers — and did not read what they said.

So layer 3 is not "nobody knew". It is **a documented convention with no gate**,
which is the weaker and more interesting claim: the trap was written down by
someone who hit it, and writing it down did not stop the next person hitting it.
That is the case for QoL's mechanism (a) or (b) rather than a third prose note.

This pass is logged as **pass 9** in both loaders, and it is a different KIND
from passes 7–8: those were re-pins to a new engine `sunfish.py`; this one has
an unchanged source and a changed **extractor**.

## 2026-08-26-pycomplete-42 — the prediction was WRONG, and the forced rebuild is what proved it

I predicted **"every certificate is byte-identical after this change; if one
moves, the argument was wrong and the inch stops."** Three moved. The inch
stops here, re-priced.

    error: Examples/python/sunfish/spec.lean:63:0      #guard sunfish.functions.map (f.name, f.argsOk, f.localsOk)
    error: Examples/python/sunfish/spec.lean:128:0     #guard sunfish.functions.map (f.name, f.isGenerator)
    error: Examples/python/sunfish/init_chain.lean:1671:0

Exit **1**, not 143 — real elaboration failures, on attempt 2 after the box
killed attempt 1.

### Why the argument failed, precisely

My reachability argument was sound *about what it covered*: both `del`
statements sit behind `len(...) > 10**6` and no pinned walk reaches 2053 nodes,
so **no runtime value can change**. That is still true. What it missed:

> **Unreachable at runtime is not invisible to the model.** The certificates
> that moved are **structural** — they census the module's *function table*,
> which changes the moment a statement lowers, whether or not it ever executes.

`spec.lean:63` pins `(name, argsOk, localsOk)` for every lowered function.
Lowering line 511 adds one. No execution required.

### And the sharp edge: genexp indices are POSITIONAL, so they RENUMBER

| index | OLD site | NEW site |
|---|---|---|
| `@0`–`@6` | 85, 86, 96, 239, 313, 444, 449 | **unchanged** |
| **`@7`** | **line 515** | **line 511** ← *different construct, same name* |
| `@8` | — | line 515 |

The `del` at 511 was an `Unsupported` leaf carrying source text, so its genexp
was **not a node at all**. Lowering it inserts a node *before* line 515's and
shifts everything after.

> **A certificate that still elaborates but now names a different construct is
> worse than one that fails.** `@0`–`@6` are safe; **`@7` silently changes
> meaning**, and the tree has **4 mentions** of it.

### Re-price: this is a renumbering migration, not a cleanup

Third pricing of the same inch, each one larger, each from measurement:

1. *cleanup* → wrong: it is a capability change
2. *capability delivery* → wrong: it is also a structural census change
3. **renumbering migration** — what it actually is

Scope: **128 `genexpr@n` mentions across 10 `Examples` files**, of which
`@7`'s **4** must be audited for meaning-shift, plus three censuses re-pinned
to **measured** values (measuring needs a tenure, so this iterates).

**Branch held unmerged.** The envelope regeneration is correct and the tier
wants it; landing it requires the migration, which is its own inch with its own
review — exactly the "someone's inch, not a rider on mine" line I drew for the
other four envelopes, now applying to my own.

### What worked

The forcing edit did its job: attempt 1 rebuilt `pins_bound_mid_d3` and 48
minutes of real spine before the box killed it, and attempt 2 reached the
failure. **pyc13's 5-second green would have merged this silently** — a broken
tree behind a green tenure, discovered by whoever next touched the pins.

## 2026-08-26-pycomplete-43 — the migration's own premise was derived, not measured; and the structural fix is priced NO

### First, a correction to my own re-price

I reported *"`@7` was line 515, now line 511"*. **That is not established.** I
derived it by walking `GeneratorExp` nodes in document order. The model does
not do that: `Json.lean:1197` mints the name from a **state-monad counter
threaded through the LOWERING traversal** (`let (n, fns) ← get`), which visits
in its own order and consumes indices under its own conditions — which is why
the committed census reads `@0, @1, @3, @4, @5, @6, @7` with **a gap at `@2`**
that document order cannot explain.

The proof that it disagrees is already in the tree: `pins_init.lean:121`
describes `<genexpr@7>` as *"the drained **module-scope** genexp"* doing
`tuple(...(range(120)))`, but line 515 — my derived `@7` — sits at indent 8
inside `Searcher.bound`. **My mapping contradicts the tree's own prose.**

> **The renumbering is proven (three certificates moved). The index→site
> mapping is not.** I made the derived-not-measured error *inside the inch
> whose whole lesson was that a prediction must be tested — one entry after
> writing it down.

**Consequence for the plan**: the migration cannot begin from a derived
mapping. Step one is a **measuring tenure** — a temporary
`#eval sunfish.functions.map (fun f => (f.name, f.span))` — because the model's
own answer is the only admissible source. Replicating the lowering in Python to
derive it would repeat this exact mistake with more machinery.

### The structural fix, priced: NO, and the census says why

| scheme | insertion-stable? | verdict |
|---|---|---|
| **positional** (today) | no | the proven hazard |
| **span** (`line:col`) | no — *any* edit above shifts it | **strictly worse** |
| **scope + ordinal** (`<genexpr@Searcher.bound#1>`) | **no** | readable, and **does not fix this case** |
| **content hash of the genexp text** | yes | unreadable; needs a collision policy |

The scope census kills the readable candidate outright: lines **511 and 515 are
both in `Searcher.bound`**, so inserting 511 renumbers 515 *within its own
scope*. Scoping shrinks the blast radius; it does not retire the hazard — and
`<module>` likewise holds three.

That leaves content-hashing as the only scheme that actually works, and it buys
insertion-stability with **unreadable certificate names** plus a collision
policy for genexps with identical text (9 sites here, and identical short
comprehensions are entirely plausible).

> **Taking it: MIGRATION-ONLY.** A naming redesign whose sole working variant
> degrades every certificate's readability is not a rider on a migration that
> has already falsified one prediction and one mapping. It is its own inch,
> with its own review, and it should be decided when someone can weigh
> unreadable names against a hazard whose true frequency we now know how to
> measure.

**Stated cost of that choice**: if a structural fix later lands, the affected
mentions are touched twice. I am accepting that rather than bundling an
unsettled naming decision into a migration — the same call I made for the other
four envelopes, and the same one I applied against myself at pycomplete-42.

### The plan, in order

1. **Measuring tenure** — temporary `#eval` of `(name, span)` per lowered
   function, before and after the envelope swap. Yields the *real* index→site
   map and the *real* shift set.
2. **`@7` audit** against that map, per site: `spec.lean:103` and `:136` are
   whole-table enumerations (they gain a row, no meaning-shift);
   `pins_init.lean:121` and `init_chain.lean:1285` name a *specific* construct
   and must be checked for which one they intend.
3. **Re-pin the three censuses** to measured values, sweep only the mentions the
   map says moved — not all 128 on principle.

## 2026-08-26-pycomplete-44 — PARKED (indefinite). Read this first on resumption.

The python-completeness lane is parked at Thomas's instruction. No ticket, no
tenure, no Lean process outstanding — the measuring tenure named below **never
started**. This entry is the resumption contract.

### 1. Frontier: LANDED and green

    138 witnesses: 107 MATCH, 31 REFUSE, 0 other

`iter()` over a list landed at `6a88769` (merged) — one change, two rows
(`dict.iter-of-list`, `iter.non-dict-receiver`), **zero divergence-register
rows added**, because a `list_iterator` is an index cursor with no layout to
guess. Reachable surface **26**; group A's five (3 dict-churn, `Set`,
`SetComp`) are the permanent floor — *not ever without guessing layout*, which
is the charter's honest-REFUSE discipline, not a shortfall.

Next inch per charter was **`expr.DictComp`**, uncensused. Nothing started.

### 2. The envelope migration: PROVEN hazard, UNMEASURED mapping

**Held unmerged**: `a8d7e85` (the failed prediction, recorded) and `49025db`
(the correction + pricing). `de105c6` carries the envelope regeneration itself.
**Do not merge any of them without the migration.**

*What is established*: regenerating `sunfish.json` lowers two `del` statements
(lines 511, 541) that the stale envelope recorded as `Unsupported`, which
**renumbers genexp indices** and moved three certificates —
`spec.lean:63`, `spec.lean:128`, `init_chain.lean:1671`. Exit 1, measured.

*What is NOT established*: **the index→site mapping.** My document-order
derivation contradicts the tree's own prose (`pins_init.lean:121` calls
`<genexpr@7>` the module-scope genexp; my derivation put it inside
`Searcher.bound`). `Json.lean:1197` mints indices from a state-monad counter in
the LOWERING traversal, not document order — hence the unexplained `@2` gap.

**Resume here, in this order:**

1. **Measuring tenure** — temporary `#eval sunfish.functions.map (fun f => (f.name, f.span))`, before and after the envelope swap. The model's own answer
   is the only admissible source. *Do not re-derive it in Python.*
2. **`@7` audit** (4 mentions): `spec.lean:103` and `:136` are whole-table
   enumerations — they gain a row, no meaning-shift. `pins_init.lean:121` and
   `init_chain.lean:1285` name a **specific** construct and need an intent
   verdict against the measured map.
3. **Re-pin** the three censuses to measured values; sweep only the mentions the
   map says moved — **not** all 128 on principle.

**Structural fix priced NO** (`49025db`): span-addressing is strictly worse;
scope+ordinal is readable but *does not fix this case* (511 and 515 share
`Searcher.bound`); content-hashing works but costs readability plus a collision
policy. Accepted cost: a later structural fix touches those mentions twice.

### 3. Envelope tracking: the pending test

`envelope_fresh --tier python` reports **FRESH 61** on the regenerated corpus
and is wired into the lane's gate list — but **it has never gated a green
build**, because the only tenure that reached the gates (`pyc13`) had a vacuous
5-second build. Its first real exercise is whichever tenure resumes this.

The deeper gap is **layer 3, still open**: `load_program` is an untracked build
input, so an envelope edit does not invalidate its dependents. The convention
(`pins_common.lean:17` — *"make a real edit HERE"*) is documented and ungated;
I used it (pass 9 notes in `pins_common.lean` and `proof.lean`), and that is
what turned pyc13's silent green into pyc14's honest red. QoL holds the
mechanism decision.

### 4. Standing corrections carried out of this session

- Group C of the frontier is **3 existing IEEE-754 rows + 1 latent**
  (`str`/`repr`-of-float cannot be a row until floats can be constructed) —
  not 4 named rows. Softfloat's downstream count should read that way.
- The exit-143 finding stands; **the metric in it does not** — `vm.swapusage`
  is a high-water mark and would defer forever. triad's gate correctly uses the
  kernel pressure level.
- `MatMult` closes trivially and **buys nothing** (`completeness.md:84`); take
  it last or knowingly as bookkeeping.

## 2026-08-26-pycomplete-45 — the migration, on a MEASURED map (resumed)

### The map, from the model itself

Measured by `check.sh` SCRATCH — a file that `load_program`s each envelope
directly and `#eval`s `(name, span.lineno)`, so neither envelope needed a
rebuild and nothing was derived:

| index | OLD site | NEW site | |
|---|---|---|---|
| `@0` `@1` `@3` | 313, 444, 449 | same | unchanged |
| — | — | **511** | **new `@4`** (the `del`) |
| `@4` | 515 | → `@5` | shifts |
| `@5` | 85 | → `@6` | shifts |
| `@6` | 86 | → `@7` | shifts |
| `@7` | 96 | → `@8` | shifts |

**My document-order derivation was wrong in kind, not degree.** The model's
lowering traversal takes *function bodies first, then module scope*, so
`@5`–`@7` are the module-scope genexps (85, 86, 96) — which is exactly what
`pins_init.lean:121` said when it called `<genexpr@7>` *"the drained
module-scope genexp"*. **The tree's prose was right and my derivation was
wrong**; it also disproves my earlier claim that only `@7` moved. **Four
indices shift, not one.** `@2` is consumed but never lowered, which is the gap
the census always showed and document order could never explain.

### The sweep, and it is smaller than the 128 I feared

Only **3 files** hold a shifting index — all sunfish-module, which matters
because `gen_lab` and `sf_order` carry their *own* `genexpr@n` namespaces that
must not be touched:

    spec.lean        @4=2 @5=2 @6=2 @7=2
    pins_init.lean                  @7=1
    init_chain.lean       @5=54 @6=6 @7=1

**70 mentions**, shifted **descending** (`@7→@8`, `@6→@7`, `@5→@6`, `@4→@5`) so
no name is shifted twice. The other 58 mentions are `@0`–`@3` or other modules
and were correctly left alone — *sweeping all 128 on principle would have
corrupted two other tiers' certificates.*

### The two censuses, re-pinned to MEASURED values

`spec.lean:63` and `:128` each gain `("<genexpr@4>", true, true)` and
`("<genexpr@4>", true)` — values read off `#eval`, not inferred from the
neighbours.

### qol-83's pending evidence rides along

The lakefile now declares `Examples/python` as an `input_dir`, so the
forcing-edit ritual is history — I **removed** my pass-9 notes from
`pins_common.lean` and `proof.lean` rather than keep obsolete instructions.
Both loaders are therefore **byte-identical to master**, and the tenure's
Built-not-Replayed on those two is the falsifiable test qol-83 asked for: an
envelope changed with zero `.lean` changes *to those files*.

## 2026-08-27-pycomplete-46 — two operational notes bought by a mass deletion

### The worktree location is a hazard, and the fix is for resumption

Mid-loop, **563 tracked files vanished** from this clone's working tree. Caught
because the enqueue line printed a tree hash that did not match the eight
previous cycles (`8d64d6b2eb64` against `45cf4215b596`) — the ticket carrying
the corrupted tree was killed by pid before it reached the front, and
`git checkout -- .` restored everything losslessly (563 pure deletions, 0
modified, 0 untracked).

The campaign's own history supplies the hypothesis without needing a new
mechanism: this clone lives under **`/private/tmp`**, which macOS purges by
access time, and the campaign has lost work to that three times before.
The signature fits — files no build had read since seeding went, while
recently-written files (the four migration files, `.git`, every session log)
stayed.

**Checked, and it neither confirms nor refutes**: every `/private/tmp`
artifact of mine survived, including logs with atimes up to 37 hours old. A
purge threshold above 37 h that still took the repo files requires those files
to have been untouched since seeding — plausible for `Examples/go/…` under a
python-tier build, but the restore reset every atime, so the discriminating
evidence is gone. **Recorded as unproven.**

> **Fix on resumption, not mid-loop: move this clone out of `/private/tmp` to
> `~/repos`,** where wasm's and Ada's already live. The hazard is the LOCATION;
> nothing hostile is required.

### The tree hash at enqueue is a real check, not a decoration

Eight cycles printed `tree at enqueue: 45cf4215b596`. The ninth printed
something else, and that single line is the entire reason a corrupted tree did
not reach a builder.

> **Compare the enqueue tree hash against the last known-good one every cycle.**
> A re-queue loop re-enqueues *whatever is on disk*, so the thing that never
> varies is exactly the thing worth asserting — and it costs one `grep`.

Push-on-green is what made the blast radius zero: `fe45bb4` was already on the
remote, so the worst case was re-cloning, never re-doing the migration.

## 2026-10-21-pycomplete-47 — starred assignment targets land

The measured wrong-answer frontier `x, *y = value` is now implemented. The
extractor admits one flat starred plain-name target as `UnpackAssign`; the
interpreter drains the right-hand side before binding and allocates the middle
slice as a heap list. Tuple, list, string, range, short-input, and non-iterable
rows are covered by `Examples/python/unpack_lab`; module-scope execution is
pinned by `harness/scripts/unpack_script.py`. Starred `for` targets, nested or
multiple stars, and starred call arguments remain loud by design.

## 2026-10-21-pycomplete-48 — first-class dictionary views retain their source

The escaped-view boundary from §2026-08-23-pycomplete-8 is now live on the
executable monadic surface. `.keys()`, `.values()`, and `.items()` allocate an
`Obj.dictView` containing the original dictionary address and view kind. Length,
truthiness, membership, and consuming iteration read the dictionary at the time
they run, so a mutation between `k = d.keys()` and `list(k)` is visible. The
same address survives an escaped view through the supported consuming paths;
`dict_items` membership follows CPython by requiring a two-element tuple-like
probe and checking key hashability before equality.

The measured boundaries remain loud: view set algebra/equality, indexing, and
rendering are not guessed, and the trunk proof interpreter still refuses view
allocation while the monadic runner is the acceptance surface. The focused
battery is 26 rows (23 matches, 3 intentional refusals), and
`harness/scripts/dict_view_script.py` covers mutation after each view kind is
escaped.

## 2026-10-23-pycomplete-56 — string joins consume generators

The monadic runner now admits `separator.join(generator_expression)` for a
heap generator. It drains the generator through the existing stateful cursor,
then applies the same indexed string-element checks as other `str.join`
operands, so generator effects and consumption remain observable and faithful
to CPython. `str_lab.join_generator` is now a concrete `#py_check` and a
differential MATCH row. The trunk proof interpreter remains intentionally
loud for generator state, so this extension is confined to the executable
monadic surface.

## 2026-10-24-pycomplete-99 — NaN equality

Immediate binary64 NaN equality now matches CPython: every NaN compares
unequal, including with itself, and `!=` is the corresponding negation. The
comparison is independent of payload/sign, so it does not consume the
separate arithmetic payload oracle. The `float_lab` concrete check and proof
cover the canonical quiet NaN; NaN ordering and hash-key behavior remain
loud.

| Measurement | Result |
|---|---|
| Focused check | `nan_equality_still_loud(0x7ff8000000000000) = False` |
| Full executable differential | 3,680 rows: 3,561 matched, 119 whitelisted, 0 failed |
| Full proof differential | 3,680 rows: 3,451 matched, 229 refused, 0 failed |
| Grammar census | 145 witnesses: 133 MATCH / 12 REFUSE, 0 drift |
| Script census | 12 recorded loud rows in 8 classes, 0 drift |

DECIDED: admit NaN `==`/`!=` only; retain NaN ordering and hashing boundaries.

## 2026-10-24-pycomplete-100 — NaN ordering

Strict float ordering now follows CPython for binary64 NaNs: `<` returns
`False` whenever either operand is NaN. The stable insertion sort consumes the
same relation, so NaNs retain their input position without a fabricated total
order. Hash-key behavior remains loud.

| Measurement | Result |
|---|---|
| Focused check | `nan_sort_still_loud(0x7ff8000000000000)` returns `[2.0, nan, 1.0]` |
| Full executable differential | 3,680 rows: 3,562 matched, 118 whitelisted, 0 failed |
| Full proof differential | 3,680 rows: 3,452 matched, 228 refused, 0 failed |
| Grammar census | 145 witnesses: 133 MATCH / 12 REFUSE, 0 drift |
| Script census | 12 recorded loud rows in 8 classes, 0 drift |

DECIDED: admit unordered NaN comparisons and sorting; retain NaN hashing as a
separate boundary.

## 2026-10-25-pycomplete-113 — public baseline inventory

The first master baseline was measured before choosing the next semantic slice.
The executable harness is green on the existing runner: all 3,693 closed-call
rows and all 142 script rows agree with CPython 3.9, with zero divergences.
The script survey runs 198 of 219 oracle-comparable files to matching output
(90.4%); 21 refuse. Its 21 refusal walls are 9 class-creation, 3
source-order, and one each for function-value aliasing, shadowed builtin
raise, three `del` forms, non-top-level import, exact set rendering, and
handler rebinding. The 142-script corpus has 130 matches and 12 loud rows.
The refusal census records 98 closed-call rows in 29 classes and 12 script rows
in 8 classes, with zero drift. The CPython 3.9 library subset contributes 8
class-creation refusals; no differential mismatch was found.

Static census ranking (an upper bound because an unsupported node hides its
subtree) is 52,259/52,512 nodes in tier (99.5%). The largest visible walls are
`Import` (59 nodes, 12 files), `ImportFrom` (40, 9), `Lambda` (36, 5),
`Starred` (26, 3), `Delete` (25, 3), value-less `AnnAssign` (16, 4), and
`AsyncFunctionDef` (9, 2). The sole-blocker view has 2 import-only files and
1 class-creation-only file; 10 refusing files have no statically visible sole
wall because admission order or dynamic checks stop them first.

The documentation and coverage checks are fresh. A clean scoped build from
current master is red in `LeanModels.Python.ClockErase`: 17 stale proof errors
begin at `ClockErase.lean:1222` after the recent semantic additions, so the
curated proof-axiom check cannot run (`ClockErase.olean` is absent). The
notebook gate is unavailable in this environment because `nbformat` is not
installed. These are recorded as environment/build gaps, not semantic
mismatches.

| Priority | Next gap | Evidence | First useful slice |
|---|---|---|---|
| 0 | `ClockErase` proof build red | fresh `tools/triad.sh` build: first error at line 1222, 17 errors total | rebase the clock-erasure walker against current `Semantics` before any tier extension |
| 1 | module imports | 2 sole blockers; 59 `Import` + 40 `ImportFrom` nodes | measure a Python-only closure and admit only a proved, explicit registry |
| 2 | class creation | 1 sole blocker; 9 dynamic refusals and 8 CPython-library refusals | admit one creation-pure base/decorator shape with differential coverage |
| 3 | lambdas and first-class callable values | 36 `Lambda` nodes; aliasing row still loud | choose a closed, non-escaping lambda shape and prove its boundary |
| 4 | starred syntax | 26 nodes across 3 files | extend only measured target/argument forms, preserving evaluation order |
| 5 | async and remaining statement walls | 9 `AsyncFunctionDef`, plus `Yield`/`YieldFrom` | census coroutine scheduling and require an explicit oracle decision |

DECIDED: baseline inventory is complete; the next turn repairs the red
`ClockErase` proof module, then resumes construct work in the measured order.

## 2026-10-25-pycomplete-114 — import closure repriced on the current interpreter

The first useful slice for the import wall was already present as the static
closure walker, so it was rerun against the pinned CPython 3.9.25 rather than
admitting an unmeasured module registry. The controls remain green: the
synthetic closure has 0/13 failures and the four real-table controls have
0/4 failures.

| Scope | no import | pure | C-reaching | nearest C |
|---|---:|---:|---:|---|
| import-time module bodies | 12 | 0 | 154 | 131 at one hop, 23 at two |
| unconditional direct children | 19 | 1 | 146 | 121 at one hop, 23 at two, 2 at three |
| whole program | 10 | 0 | 156 | 137 at one hop, 19 at two |

The import-time closure reaches 61 distinct C modules; 146 of the 154
refusing seeds reach an operating-system, I/O, thread, or interpreter module,
and only 8 reach computational C modules alone. The closure contains 207
distinct pure-Python modules, but even granting every C module natively only
19 of 154 importing seeds have an all-in-tier pure closure. A Python-only
module registry therefore has no measured import-time payoff on this corpus,
while remaining a future requirement for third-party pure-Python packages.

DECIDED: keep imports loud for now; preserve the measured closure and its
controls, and move to the next higher-payoff construct rather than admitting
an unproved registry.

## 2026-10-25-pycomplete-115 — class creation priced before extension

The class wall was measured with the extractor's own `creation_effects` and
the existing class census controls before choosing a new creation rule. The
controls cover bases, body statements, decorators, slots, exception
ancestors, and real-file reconciliation with 0 failures.

| Measurement | Result |
|---|---|
| Stdlib seeds | 152 files, 116 define top-level classes, 88 hit class creation |
| Classes | 569 top-level classes; 338 have creation effects |
| Sole class-creation blockers | 0 in the stdlib sweep; 1 in the 219-file survey (`cls_deco_script.py`) |
| Survey | 198 MATCH / 21 REFUSE / 0 DIVERGE |
| Controls | 21 synthetic fixtures + graphlib/opcode/bisect, 0 failures |

The sole corpus witness deliberately uses a user decorator that prints while
the class statement executes. Admitting decorators as a blanket rule would
reintroduce the skipped class-creation effect that the current loud refusal
was added to prevent; the other nine survey refusals also have imports or
later walls. The class census therefore supplies no measured flip for a
creation tier on the current corpus.

DECIDED: retain loud class-creation refusal for effectful decorators and
unsupported class construction; do not add a decorator protocol without a
measured, semantically closed shape. Move to the next higher-payoff syntax
wall while keeping this census as the admission gate for future class work.

## 2026-10-25-pycomplete-116 — validate the closed lambda slice

The lambda priority was already implemented by the H7 nested-definition
lowering: a direct single-target assignment becomes a synthetic nested
function, with literal defaults, a simple return body, and either no capture
or the admitted frame-cell capture. Calls through the local callable use the
same closure path as nested `def`; aliases remain ordinary first-class closure
references, while escaping cells, unsupported defaults, nested scopes, and
late generator captures remain loud.

| Measurement | Result |
|---|---|
| Direct lambda probes | capture-free call, captured call, and alias call all match CPython 3.9 |
| Existing acceptance | `closure_lab.lam_basic`, `lam_capture`, and `lam_rebound` are checked in the shipped H7 spec |
| Survey lambda nodes | 36 nodes in 5 vendored files; every row also has class/import or other walls, 0 lambda-only refusals |
| Formatting | `git diff --check` passed |

DECIDED: keep the closed, non-escaping lambda lowering as the supported slice;
retain loud failure for first-class callable forms whose capture or boundary
semantics are not represented, and move to starred syntax next.

## 2026-10-25-pycomplete-117 — close the starred-syntax audit

The starred syntax priority is already covered at its two landed expression
and target sites. Starred displays lower through immediate tuple construction
and an outer fresh `list`, preserving evaluation order and copy semantics;
flat one-star assignment targets drain the source before allocating the middle
slice. The `star_script` and `unpack_script` harness programs match CPython
3.9, including stdout ordering and short-input behavior.

| Measurement | Result |
|---|---|
| Display and target scripts | 2/2 model/oracle matches |
| Static nodes | 26 nodes in 3 files; two in-repo rows are already MATCH, the remaining vendored rows have class/import walls |
| Remaining shape | starred call arguments remain loud through `call_unsupported`; no corpus row is star-only |
| Formatting | `git diff --check` passed |

DECIDED: retain the landed display and flat-target forms and keep starred call
arguments loud until a callable-argument expansion shape has a sole measured
payoff; move to the remaining statement walls next.

## 2026-10-25-pycomplete-118 — price async scheduling before syntax work

The remaining async grammar is a scheduler boundary, not an isolated AST
case. The current survey sees 9 `AsyncFunctionDef` nodes in two vendored
files, alongside `AsyncFor`, `AsyncWith`, `Await`, and async generator forms;
both files already refuse on class creation/import and neither has an
async-only payoff. The in-tier generator rows are synchronous and already
covered by the H4 stepper. The ordinary remaining statement walls in the
survey (flat starred targets, value-less annotations, list comprehensions,
`del`, and synchronous `yield`) are either landed or deliberately covered by
existing loud boundaries.

| Measurement | Result |
|---|---|
| Async nodes | 9 `AsyncFunctionDef` nodes in 2 files; no async-only refusal |
| In-repo async rows | 0; all async nodes are in vendored grammar tests |
| Existing synchronous generator coverage | `gen_lab` matches and its `yield` boundary is proven |
| Formatting | `git diff --check` passed |

An async implementation needs a coroutine object, await protocol, task/event
loop scheduling, cancellation, and an explicit environment model. Choosing
those effects is a semantic and oracle decision that cannot be inferred from
the current synchronous frame machine.

DECIDED: do not silently exclude async, and do not invent scheduler behavior;
keep the async constructs loud until an explicit coroutine/event-loop model is
chosen. Continue with any remaining synchronous statement wall that has a
measured sole payoff.

## 2026-10-25-pycomplete-119 — admit ordinary shadowing after a def alias

The module-level def-aliasing census now records admitted alias names
separately from direct definitions. An ordinary later assignment may shadow
an alias in the live module frame; static function dispatch remains available
only until that shadow is published. Direct definition names and a second
function-valued assignment remain loud, preserving the source-order boundary
without introducing runtime function objects. `alias_rebound.py` therefore
matches CPython's `7`, while `alias_before_def.py` and the existing alias
battery retain their previous outcomes.

| Measurement | Result |
|---|---|
| Focused alias differential | 4/4 rows agree (rebound, happy path, forward refusal, bisect shape) |
| Script corpus | 131 matched / 11 loud / 0 failed (142 rows; +1 match) |
| Python package build | `lake build LeanModels.Python` passed |
| Formatting | `git diff --check` passed |

DECIDED: allow one later ordinary shadow of an admitted module-level alias;
keep function-valued re-aliases, direct-definition rebinding, and first-class
callable reads loud. Move to the next remaining synchronous wall.

## 2026-10-25-pycomplete-120 — render the deterministic integer-set slice

Set construction and order-blind readers were already live, but printing a
set was loud because general hash-table iteration order is not represented.
The renderer now admits only the exact deterministic shape whose heap set
contains integer elements in strictly increasing order (and the empty set),
matching CPython 3.9's `repr`; reverse insertion, mixed kinds, and all other
hash orders remain loud. The existing `print_set.py` row is now a differential
match.

| Measurement | Result |
|---|---|
| Focused set differential | `print_set.py` matches CPython 3.9 (`3` then `{1, 2, 3}`) |
| Scope | Pure `reprVal` extension; no heap or proof geometry changes |
| Formatting | `git diff --check` passed |

DECIDED: admit increasing integer and empty-set rendering only; retain loud
failure for arbitrary hash order and mixed set elements. Move to the next
remaining synchronous wall.

## 2026-10-25-pycomplete-121 — thread deterministic set rendering through derived channels

The deterministic integer-set renderer now reaches the two existing consumers
that share `printOne`: f-string fields and assertion messages. Their stale
example envelopes had retained the old `Set` unsupported nodes, so they were
regenerated from the Python sources; both rows now match CPython 3.9. The
arbitrary set iteration frontier remains loud.

| Measurement | Result |
|---|---|
| Focused differential | `assert_lab.msg_set(-1)` and `fstring_lab.set_field(3)` both match |
| Full differential | `3693 cases: 0 failed, 95 whitelisted-unsupported, 3598 matched` |
| Refusal census | 95 rows, 0 drifts; `set.order` now has 3 rows |
| Generated artifacts | `assert_lab.json` and `fstring_lab.json` regenerated with the current extractor |
| Formatting | `git diff --check` passed |

DECIDED: share the exact increasing-integer set renderer across `print`,
f-strings, and assertion messages; retain loud failure for arbitrary hash order.
Move to the next remaining synchronous wall.

## 2026-10-25-pycomplete-122 — align proof semantics for literal exception payloads

The monadic runner already preserved one-string payloads for admitted builtin
and user exception constructors, but the fuel-based proof interpreter still
refused every constructor form. Its `raise N("literal")` slice now returns
`PyErr.userMessage` or the corresponding builtin payload error. The argument is
restricted to a string literal on this proof surface, keeping the raise arm
fuel-free and preserving the existing `fuelMono`, `worldInv`, clock-erasure,
and payload-blind proof geometry; expression-valued arguments remain loud.

| Measurement | Result |
|---|---|
| Proof-facing guards | 4/4 agree: user payload, `ValueError`, `TypeError`, and a matching handler |
| Python differential | 3,693 cases: 0 failed, 95 whitelisted-unsupported, 3,598 matched |
| Focused builds | `LeanModels.Python.Obs`, `LeanModels.Python.ClockErase`, and `leanmodels-run` pass |
| Refusal census | 95 rows, 0 drifts; the runner's existing wide payload rows remain matches |
| Formatting | `git diff --check` passed |

DECIDED: admit literal one-string payloads on the closed proof surface and keep
non-literal, keyword, starred, multi-argument, and unmodelled exception
constructors loud until their evaluation and proof obligations are measured.
Move to the next remaining synchronous wall.

## 2026-10-25-pycomplete-123 — make `del` rebinding path-aware

The closed `del` runtime already handled a later local rebinding correctly,
but the extractor's static census used a whole-function name-set intersection:
any load of a name that appeared in a `del` was refused. That over-approximated
CPython for `rebind_after` and for the loop-body pattern in `loop_del`.

The census now tracks names that may be deleted through the supported statement
shapes. A store clears the name on that path; branches and loops join with a
union, so a read remains loud whenever one path can still reach it after the
delete. The true `read_after` case and runtime partial-delete cases remain
loud. The generated `del_lab` envelope and differential expectations now make
the two repaired rows executable.

| Measurement | Result |
|---|---|
| Focused differential | 4/4 rows agree: `read_after` and `double_del` remain loud; `rebind_after` and `loop_del` match |
| Full executable differential | 3,693 cases: 0 failed, 93 whitelisted-unsupported, 3,600 matched |
| Full proof differential | 3,693 cases: 0 failed, 199 refused, 3,494 matched |
| Refusal census | 93 rows, 0 drifts; `del.name-set-census` reduced from 6 to 4 |
| Formatting | `git diff --check` passed |

DECIDED: keep the `del` census conservative at control-flow joins while
admitting definite straight-line and loop-body rebinding. Move to the next
remaining synchronous wall.

## 2026-10-25-pycomplete-124 — admit no-op `finally: pass`

The exceptions tier still refused every `finally` clause, but the
`exc_lab.finally_clause` witness has a literal `pass` finalizer. A pass suite
has no observable effect on normal return, propagated exceptions, or control
flow, so ingestion now lowers exactly that shape to its `try` body. Finalizers
with any effect remain structured-but-loud; the `exc_handlers_lab` mutation
row continues to pin that boundary.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab.finally_clause(1)` matches in both interpreters |
| Full executable differential | 3,693 cases: 0 failed, 92 whitelisted-unsupported, 3,601 matched |
| Full proof differential | 3,693 cases: 0 failed, 198 refused, 3,495 matched |
| Refusal census | 92 rows, 0 drifts; `exc.finally` retains only the effectful row |
| Extractor tests | 133/133 passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the exact no-op finalizer lowering and retain loud failure
for effectful finalization until the frame's all-flow cleanup semantics is
priced and proved.

## 2026-10-25-pycomplete-125 — admit finite float dictionary and set keys

The float tier already had exact binary64 equality and ordering, but the
dict/set key gate rejected every float before those relations could be used.
Finite floats are now hashable in the linear key model, with the same
float/int/bool equality and signed-zero behavior as Python. Tuple keys recurse
through the finite gate, and set membership uses the same relation. NaN and
infinity keys remain loud because an immediate float cannot model CPython's
identity shortcut for a NaN key; mixed tuples containing a non-finite float
retain that boundary.

| Measurement | Result |
|---|---|
| Focused differential | `finite_keys`, `nested_finite_keys`, and `set_finite_keys`: 3/3 MATCH in both interpreters |
| Full executable differential | 3,694 cases: 0 failed, 90 whitelisted-unsupported, 3,604 matched |
| Full proof differential | 3,694 cases: 0 failed, 196 refused, 3,498 matched |
| Refusal census | 90 rows, 0 drifts; `float.hashing` removed |
| Example proof | `lake build Examples.python.float_lab.spec` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit finite float keys and their tuple/set consumers; retain loud
failure for non-finite float keys until immediate-value identity semantics are
priced separately.

## 2026-10-25-pycomplete-126 — admit tuple exception handlers

The exception tier previously retained only one plain handler name. The
extractor now recognizes a tuple of plain names and stores its ordered members
in the existing handler field; a reducible scanner keeps the representation
kernel-computable. Both interpreters validate every member against the same
shadowing and admission rules as a single handler, then match the first member
whose builtin or admitted user-class table catches the retained exception.
Dynamic exception expressions, shadowed tuple names, and multiple handler
bodies remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab.tuple_handler(1)` → 1 and `exc_handlers_lab.tuple_handler()` → 13; 2/2 MATCH in both interpreters |
| Full executable differential | 3,694 cases: 0 failed, 88 whitelisted-unsupported, 3,606 matched |
| Full proof differential | 3,694 cases: 0 failed, 194 refused, 3,500 matched |
| Refusal census | 88 rows, 0 drifts; both tuple-handler rows removed |
| Extractor tests | 134/134 passed |
| Proof/example build | `Examples.python.exc_handlers_lab.proof` and `spec` pass |
| Formatting | `git diff --check` passed |

DECIDED: admit tuples of plain admitted exception names through the existing
retained-state handler path; retain loud failure for dynamic, shadowed, and
multi-suite handler forms.

## 2026-10-25-pycomplete-127 — admit the decimal `int(str)` limit error

The decimal `int(str)` parser now returns CPython's pinned 4300-digit
`ValueError` when the normalized input exceeds the fixed conversion budget,
matching the existing rendering boundary. The error is preserved through the
ordinary builtin call and the proof interpreter; malformed inputs within the
budget retain their exact `invalid literal` errors, while bytes and other
unpriced conversion paths remain unchanged.

| Measurement | Result |
|---|---|
| Focused differential | 53 `int_string.parse_decimal` cases: 0 failed, 53 matched in both interpreters |
| Boundary witness | 4301 decimal zeroes raise `decimalLimitError` / CPython `ValueError` |
| Example proof | `lake build Examples.python.int_string.spec` passed |
| Refusal census | 88 rows, 0 drifts; `int_string.parse_decimal` removed from the `builtin.int-of-str` whitelist |
| Formatting | `git diff --check` passed |

DECIDED: admit the pinned decimal conversion-limit exception for `int(str)`;
retain loud failure for unpriced conversion boundaries and host-configurable
limits.

## 2026-10-25-pycomplete-128 — admit `raise N from None`

The exceptions tier carries class identity and an optional measured message,
but no observable `__cause__` payload. A literal `None` cause therefore has
the same behavior as an ordinary class-identity raise on this surface. Ingest
now lowers exactly `raise N from None` to `raise N`; expression-valued causes
remain structured and loud, preserving evaluation and chaining boundaries.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab.raise_from(1)` and `builtin_raise_lab.chained()` match in both interpreters |
| Lean build | `lake build LeanModels.Python.Json` and `lake build leanmodels-run` pass |
| Refusal census | `exc_lab.raise_from` removed from `exc.raise`; the remaining dynamic/bare raise rows stay loud |
| Formatting | `git diff --check` passed |

DECIDED: admit only literal-`None` exception chaining through ingestion
lowering; retain loud failure for dynamic causes and bare re-raise until their
context payload semantics are separately priced.

## 2026-10-25-pycomplete-129 — extend the fixed rendering depth

The caller-independent `reprFuel` budget rises from 256 to 512 levels, which
admits the existing `repr_lab.deep(257)` witness on both interpreter surfaces.
The budget remains separate from call fuel, and `deep(513)` stays loudly
refused so an arbitrarily recursive renderer is never introduced.

| Measurement | Result |
|---|---|
| Focused differential | `repr_lab.deep(257)` matches in both interpreters; `deep(513)` remains refused by the proof guard |
| Refusal census | 84 rows, 0 drifts; `render.depth-limit` is removed |
| Formatting | `git diff --check` passed |

DECIDED: spend a larger fixed rendering budget for ordinary nested containers;
keep the budget caller-independent and retain loud refusal beyond 512 levels.

## 2026-10-25-pycomplete-130 — admit the direct class-identity re-raise

The exceptions tier now lowers the exact shape `try: raise N; except N:
raise` when the protected body is only the matching class-identity raise.
The handler can therefore re-raise the known `N` without adding an active
exception payload to `FrameState`; retained state and the existing class
matching path remain unchanged. Broad handlers, tuple handlers, nested
control-flow re-raises, and dynamic active-exception values remain loud.

| Measurement | Result |
|---|---|
| Focused differential | `exc_lab.raise_bare(1)` matches in both interpreters as `Stop` |
| Refusal census | 83 rows, 0 drifts; the direct `exc.raise` witness is removed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the statically known direct class-identity re-raise;
retain the general active-exception payload boundary until it is represented
in the frame state and proved.

## 2026-10-25-pycomplete-131 — admit literal f-string format specifications

F-string fields with a one-part literal format specification now lower to a
synthetic format worker. The admitted rung is CPython's integer/Boolean `d`,
right-aligned width `>5`, and zero-padded decimal `03d` forms; the default
conversion passes the raw field so numeric formatting is preserved. Dynamic or
multi-part specs and the rest of the format mini-language remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 99 f-string cases: 0 failed, 98 matched, 1 boundary refusal in both interpreters |
| Full executable differential | 3,694 cases: 0 failed, 81 whitelisted-unsupported, 3,613 matched |
| Full proof differential | 3,694 cases: 0 failed, 187 refused, 3,507 matched |
| Refusal census | 81 rows, 0 drifts; `fstring_lab::format_spec` and `format_spec_num` removed |
| Extractor tests | 135/135 passed |
| Lean build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the measured literal numeric format forms through the
shared worker; retain loud failure for dynamic, multi-part, and richer format
specifications until their grammar and protocols are priced.

## 2026-10-25-pycomplete-132 — admit faithful `float()` heap TypeErrors

`float()` now distinguishes an ordinary heap value with no admitted numeric
protocol from an unresolved conversion protocol. Lists, dictionaries, sets,
generators, closures, and default-protocol instances raise CPython's exact
non-numeric `TypeError` using the heap type name; custom `__float__` protocols
remain loud because the class tier excludes those dunders.

| Measurement | Result |
|---|---|
| Focused differential | `float_lab.constructor_heap()` matches in native and proof interpreters |
| Refusal census | 80 rows, 0 drifts; `float.constructor-protocols` removed |
| Lean build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the faithful non-numeric heap error; retain loud failure
for future user-defined conversion protocols.

## 2026-10-25-pycomplete-133 — admit the non-callable `iter(v, sentinel)` error

The two-argument `iter` spelling now evaluates its arguments left to right and
raises CPython's exact `TypeError: iter(v, w): v must be callable` when the
first value is a known non-callable heap object or immediate. The one-argument
dict/list cursor behavior is unchanged. A callable first value remains loud,
because CPython returns a `callable_iterator`, a distinct object kind whose
call protocol is not yet modeled; arity above two now uses CPython's ordinary
arity error.

| Measurement | Result |
|---|---|
| Focused differential | `iter_sentinel_still_loud()` matches; existing dict/list iterator rows remain matches |
| Full executable differential | 3,694 cases: 0 failed, 79 whitelisted-unsupported, 3,615 matched |
| Full proof differential | 3,694 cases: 0 failed, 186 refused, 3,508 matched |
| Refusal census | 79 rows, 0 drifts; `dict_lab::iter_sentinel_still_loud` removed |
| Lean build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the measured non-callable sentinel error; retain loud
failure for callable-iterator construction.

## 2026-10-26-pycomplete-164 — erase unread module-function values

An exact two-statement local assignment of an admitted module function is now
erased when its target is never observed: `f = scale2; return 0`. The rewrite
runs after module-level alias recognition, so direct definitions and admitted
aliases are covered. Parameter shadowing, returned-target references, and
function values that are actually observed remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 20 cases: 0 failed, 19 matched, 1 whitelisted refusal |
| Full executable differential | 3,695 cases: 0 failed, 44 whitelisted refusals, 3,651 matched |
| Full proof differential | 3,695 cases: 0 failed, 153 refusals, 3,542 matched |
| Refusal census | 44 rows, 0 drifts; no new refusal class |
| Lean build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: erase only unread assignments of admitted module functions, including
recognized aliases; retain loud failure for returned or otherwise observed
function values and shadowed names.

## 2026-10-26-pycomplete-165 — admit the immediate local `repr` alias

The existing two-statement local-builtin alias rewrite now includes `repr`:
`f = repr; return f(value)` lowers to the ordinary builtin call. Argument
evaluation and the shared renderer are unchanged. Returning `repr` itself,
shadowing it with a parameter, and other first-class callable forms remain
loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,698 cases: 0 failed, 44 whitelisted refusals, 3,654 matched |
| Full proof differential | 3,698 cases: 0 failed, 153 refusals, 3,545 matched |
| Refusal census | 44 rows, 0 drifts; no new refusal class |
| Lean build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `repr` alias call; retain loud
failure for returned or general first-class callable values.

## 2026-10-26-pycomplete-166 — admit the immediate local `len` alias

The local-builtin alias rewrite now includes `len`: `constructor = len;
return constructor(value)` lowers to the ordinary builtin call. Tuple, list,
and string arguments preserve their existing length semantics and boundary
behavior. Returning `len` itself, shadowing it, and general first-class
callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,701 cases: 0 failed, 44 whitelisted refusals, 3,657 matched |
| Full proof differential | 3,701 cases: 0 failed, 153 refusals, 3,548 matched |
| Refusal census | 44 rows, 0 drifts; no new refusal class |
| Lean build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `len` alias call; retain loud failure
for returned or general first-class callable values.

## 2026-10-26-pycomplete-167 — admit the immediate local `sorted` alias

The local-builtin alias rewrite now includes `sorted`: `f = sorted;
return f(values)` lowers to the existing sorted worker. Tuple and list inputs
retain their fresh-list results and current comparison behavior. Returning
`sorted` itself, shadowing it, and general first-class callable forms remain
loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,703 cases: 0 failed, 44 whitelisted refusals, 3,659 matched |
| Full proof differential | 3,703 cases: 0 failed, 153 refusals, 3,550 matched |
| Refusal census | 44 rows, 0 drifts; no new refusal class |
| Lean build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `sorted` alias call; retain loud
failure for returned or general first-class callable values.

## 2026-10-27-pycomplete-168 — admit the immediate local `max` alias

The local-builtin alias rewrite now includes `max`: `f = max; return
f(values)` lowers to the existing max worker. Tuple and list inputs retain
their scalar maximum behavior. Returning `max` itself, shadowing it, and
general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,705 cases: 0 failed, 44 whitelisted refusals, 3,661 matched |
| Full proof differential | 3,705 cases: 0 failed, 153 refusals, 3,552 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `max` alias call; retain loud failure
for returned or general first-class callable values.

## 2026-10-27-pycomplete-169 — admit the immediate local `min` alias

The local-builtin alias rewrite now includes `min`: `f = min; return
f(values)` lowers to the existing min worker. Tuple and list inputs retain
their scalar minimum behavior. Returning `min` itself, shadowing it, and
general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,707 cases: 0 failed, 44 whitelisted refusals, 3,663 matched |
| Full proof differential | 3,707 cases: 0 failed, 153 refusals, 3,554 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `min` alias call; retain loud failure
for returned or general first-class callable values.

## 2026-10-27-pycomplete-170 — admit the immediate local `abs` alias

The local-builtin alias rewrite now includes `abs`: `f = abs; return
f(value)` lowers to the existing scalar absolute-value worker. Integer, zero,
and Boolean inputs preserve their current results. Returning `abs`, shadowing it,
and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,710 cases: 0 failed, 44 whitelisted refusals, 3,666 matched |
| Full proof differential | 3,710 cases: 0 failed, 153 refusals, 3,557 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Focused surface | three `#py_check` rows passed with `LeanModels.Python.Surface` |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `abs` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-27-pycomplete-171 — admit the immediate local `int` alias

The local-builtin alias rewrite now includes `int`: `f = int; return
f(value)` lowers to the existing integer-conversion worker. String, integer, and
Boolean inputs preserve their current conversion and error semantics. Returning
`int`, shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,713 cases: 0 failed, 44 whitelisted refusals, 3,669 matched |
| Full proof differential | 3,713 cases: 0 failed, 153 refusals, 3,560 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Focused surface | three `#py_check` rows passed with `LeanModels.Python.Surface` |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `int` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-27-pycomplete-172 — admit the immediate local `float` alias

The local-builtin alias rewrite now includes `float`: `f = float; return
f(value)` lowers to the existing binary64 constructor worker. Integer, string, and
Boolean inputs preserve their current conversion and error semantics. Returning
`float`, shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,716 cases: 0 failed, 44 whitelisted refusals, 3,672 matched |
| Full proof differential | 3,716 cases: 0 failed, 153 refusals, 3,563 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Focused surface | three `#py_check` rows passed with `LeanModels.Python.Surface` |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `float` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-27-pycomplete-173 — admit the immediate local `all` alias

The local-builtin alias rewrite now includes `all`: `f = all; return
f(values)` lowers to the existing short-circuit truth scan. Empty, all-true, and
mixed Boolean iterables preserve their current results. Returning `all`,
shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,719 cases: 0 failed, 44 whitelisted refusals, 3,675 matched |
| Full proof differential | 3,719 cases: 0 failed, 153 refusals, 3,566 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Focused surface | three `#py_check` rows passed with `LeanModels.Python.Surface` |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `all` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-174 — admit the immediate local `any` alias

The local-builtin alias rewrite now includes `any`: `f = any; return
f(values)` lowers to the existing short-circuit truth scan. Mixed, empty, and
all-false Boolean iterables preserve their current results. Returning `any`,
shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,722 cases: 0 failed, 44 whitelisted refusals, 3,678 matched |
| Full proof differential | 3,722 cases: 0 failed, 153 refusals, 3,569 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Focused surface | three `#py_check` rows passed with `LeanModels.Python.Surface` |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `any` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-175 — admit the immediate local `str` alias

The local-builtin alias rewrite now includes `str`: `f = str; return
f(value)` lowers to the existing string conversion worker. Integer, Boolean,
and string inputs preserve their current rendering behavior. Returning `str`,
shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,725 cases: 0 failed, 44 whitelisted refusals, 3,681 matched |
| Full proof differential | 3,725 cases: 0 failed, 153 refusals, 3,572 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Focused surface | three `#py_check` rows passed with `LeanModels.Python.Surface` |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `str` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-176 — admit the immediate local `sum` alias

The local-builtin alias rewrite now includes `sum`: `f = sum; return
f(values, start)` lowers to the existing summation worker. Integer, empty-list
with a nonzero start, and Boolean iterable inputs preserve their current
results. Returning `sum`, shadowing it, and general first-class callable forms
remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 3 cases: 0 failed, 3 matched on both interpreters |
| Full executable differential | 3,728 cases: 0 failed, 44 whitelisted refusals, 3,684 matched |
| Full proof differential | 3,728 cases: 0 failed, 153 refusals, 3,575 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `sum` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-177 — admit the immediate local `tuple` alias

The local-builtin alias rewrite now includes `tuple`: `f = tuple; return
f(value)` lowers to the existing tuple conversion worker. List and string
inputs preserve their current immutable sequence results. Returning `tuple`,
shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,730 cases: 0 failed, 44 whitelisted refusals, 3,686 matched |
| Full proof differential | 3,730 cases: 0 failed, 153 refusals, 3,577 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `tuple` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-178 — admit the immediate local `list` alias

The local-builtin alias rewrite now includes `list`: `f = list; return
f(value)` lowers to the existing fresh-list constructor. Tuple and string
inputs preserve their current list results. Returning `list`, shadowing it,
and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,732 cases: 0 failed, 44 whitelisted refusals, 3,688 matched |
| Full proof differential | 3,732 cases: 0 failed, 153 refusals, 3,579 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `list` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-179 — admit the immediate local `ord` alias

The local-builtin alias rewrite now includes `ord`: `f = ord; return f(value)`
lowers to the existing character-code worker. ASCII character inputs preserve
their current integer results. Returning `ord`, shadowing it, and general
first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,734 cases: 0 failed, 44 whitelisted refusals, 3,690 matched |
| Full proof differential | 3,734 cases: 0 failed, 153 refusals, 3,581 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `ord` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-180 — admit the immediate local `chr` alias

The local-builtin alias rewrite now includes `chr`: `f = chr; return f(value)`
lowers to the existing integer-to-character worker. ASCII integer inputs
preserve their current string results. Returning `chr`, shadowing it, and
general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,736 cases: 0 failed, 44 whitelisted refusals, 3,692 matched |
| Full proof differential | 3,736 cases: 0 failed, 153 refusals, 3,583 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `chr` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-181 — admit the immediate local `pow` alias

The local-builtin alias rewrite now includes `pow`: `f = pow; return
f(base, exponent)` lowers to the existing power worker. Ordinary positive
integer exponents and the zero exponent preserve their current results.
Returning `pow`, shadowing it, and general first-class callable forms remain
loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,738 cases: 0 failed, 44 whitelisted refusals, 3,694 matched |
| Full proof differential | 3,738 cases: 0 failed, 153 refusals, 3,585 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `pow` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-182 — admit the immediate local `round` alias

The local-builtin alias rewrite now includes `round`: `f = round; return
f(value)` lowers to the existing integer/Boolean rounding worker. Integer and
Boolean inputs preserve their current results. Returning `round`, shadowing it,
and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,740 cases: 0 failed, 44 whitelisted refusals, 3,696 matched |
| Full proof differential | 3,740 cases: 0 failed, 153 refusals, 3,587 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `round` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-183 — admit the immediate local `ascii` alias

The local-builtin alias rewrite now includes `ascii`: `f = ascii; return
f(value)` lowers to the existing ASCII rendering worker. Integer and Unicode
string inputs preserve their current escaped results. Returning `ascii`,
shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,742 cases: 0 failed, 44 whitelisted refusals, 3,698 matched |
| Full proof differential | 3,742 cases: 0 failed, 153 refusals, 3,589 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `ascii` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-184 — admit the immediate local `hex` alias

The local-builtin alias rewrite now includes `hex`: `f = hex; return f(value)`
lowers to the existing integer hexadecimal renderer. Positive and negative
integer inputs preserve their current results. Returning `hex`, shadowing it,
and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,744 cases: 0 failed, 44 whitelisted refusals, 3,700 matched |
| Full proof differential | 3,744 cases: 0 failed, 153 refusals, 3,591 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `hex` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-185 — admit the immediate local `oct` alias

The local-builtin alias rewrite now includes `oct`: `f = oct; return f(value)`
lowers to the existing integer octal renderer. Positive and negative integer
inputs preserve their current results. Returning `oct`, shadowing it, and
general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,746 cases: 0 failed, 44 whitelisted refusals, 3,702 matched |
| Full proof differential | 3,746 cases: 0 failed, 153 refusals, 3,593 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `oct` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-186 — admit the immediate local `bin` alias

The local-builtin alias rewrite now includes `bin`: `f = bin; return f(value)`
lowers to the existing integer binary renderer. Positive and negative integer
inputs preserve their current results. Returning `bin`, shadowing it, and
general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,748 cases: 0 failed, 44 whitelisted refusals, 3,704 matched |
| Full proof differential | 3,748 cases: 0 failed, 153 refusals, 3,595 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `bin` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-187 — admit the immediate local `format` alias

The local-builtin alias rewrite now includes `format`: `f = format; return
f(value)` lowers to the existing scalar format worker. Integer and Boolean
inputs preserve their current string results. Returning `format`, shadowing it,
and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,750 cases: 0 failed, 44 whitelisted refusals, 3,706 matched |
| Full proof differential | 3,750 cases: 0 failed, 153 refusals, 3,597 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `format` alias call; retain loud
failure for returned or general first-class callable values. Rebase and publish
this item after the full measurements, then reread the inbox before the next
gap.

## 2026-10-28-pycomplete-188 — admit the immediate local `range` alias

The local-builtin alias rewrite now includes `range`: `f = range; return
f(value)` lowers to the existing immediate range constructor. Positive and
empty integer stops preserve their current `Val.range` results. Returning
`range`, shadowing it, and general first-class callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,752 cases: 0 failed, 44 whitelisted refusals, 3,708 matched |
| Full proof differential | 3,752 cases: 0 failed, 153 refusals, 3,599 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `range` alias call; retain loud
failure for returned or general first-class callable values. Rebase and publish
this item after the full measurements, then reread the inbox before the next
gap.

## 2026-10-28-pycomplete-189 — admit the immediate local `next` alias

The local-builtin alias rewrite now includes `next`: `f = next; return
f((x for x in range(value)), -1)` lowers to the existing generator cursor
worker. The inline generator's first value and the empty-generator default
preserve their current results. Returning `next`, shadowing it, and general
first-class callable forms remain loud; `iter(range(...))` remains outside the
tier as before.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,754 cases: 0 failed, 44 whitelisted refusals, 3,710 matched |
| Full proof differential | 3,754 cases: 0 failed, 153 refusals, 3,601 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `next` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-190 — admit the immediate local `print` alias

The local-builtin alias rewrite now includes `print`: `f = print; return
f(value)` lowers to the ordinary stdout builtin. Integer and Boolean arguments
preserve the existing `None` return; stdout remains observable on stateful
script/call surfaces. Returning `print`, shadowing it, and general first-class
callable forms remain loud.

| Measurement | Result |
|---|---|
| Focused differential | 2 cases: 0 failed, 2 matched on both interpreters |
| Full executable differential | 3,756 cases: 0 failed, 44 whitelisted refusals, 3,712 matched |
| Full proof differential | 3,756 cases: 0 failed, 153 refusals, 3,603 matched |
| Lean runner build | `lake build leanmodels-run` passed |
| Coverage freshness | `python3 harness/coverage_page.py` passed |
| Formatting | `git diff --check` passed |

DECIDED: admit only the immediate local `print` alias call; retain loud failure
for returned or general first-class callable values. Rebase and publish this
item after the full measurements, then reread the inbox before the next gap.

## 2026-10-28-pycomplete-191 — repair the cached-identity regression guard

The Python full check had a stale guard left behind by the cached immediate
identity tier: `1 is 1` is now a decided CPython 3.9 small-integer identity,
not an `Unsupported` result. Updated `LeanModels/Python/Tests.lean` to assert
`.ok (.bool true)` while preserving the loud guard for implementation-dependent
string identity.

| Measurement | Result |
|---|---|
| Focused Lean test | `lake env lean LeanModels/Python/Tests.lean` passed |
| Scope | One stale regression guard; no runtime or coverage changes |
| Formatting | `git diff --check` passed |

DECIDED: publish this CI repair, verify the hosted full check, then perform the
overdue fifth-turn Python release pass before selecting another construct.

## 2026-10-28-pycomplete-193 — repair the Boolean range-render proof

The hosted full check exposed a stale symbolic proof in
`Examples/python/range_render/proof.lean` after the range renderer began
retaining Boolean constructor fields. The theorem's `py_simp` recipe now
reduces the heap-freedom and builtin-dispatch guards explicitly, evaluates the
bounded `range(0, bool)` rendering path, and closes the structural boundary
freeze for the resulting string. A small `intDecimal 1` lemma complements the
existing zero lemma; the statement and the runtime semantics are unchanged.

| Measurement | Result |
|---|---|
| Focused proof | `lake env lean Examples/python/range_render/proof.lean` passes; no `sorryAx` in `#print axioms` |
| Example surface | `lake env lean Examples/python/range_render/spec.lean` passes |
| Differential scope | unchanged: 3,756 native rows and 3,756 proof rows, previously 0 failed |
| Formatting | `git diff --check` passes |

DECIDED: commit this proof repair, regenerate/check the backlog index, then
rebase and publish it before taking the next hosted Python proof failure.

## 2026-10-28-pycomplete-194 — repair the exception-handler proof normalization

The hosted proof for `exc_handlers_lab` had become stale as the interpreter's
exception, starred-call, heap-freedom, generator-allocation, and boundary
freezing guards evolved. Its two total-correctness theorems now expose the
current guard walkers and retained `Run` combinators to `py_simp`; the first
handler theorem closes the final public freeze definitionally and the tuple
handler theorem normalizes directly. Runtime semantics and the theorem
statements are unchanged.

| Measurement | Result |
|---|---|
| Focused proof | `lake env lean Examples/python/exc_handlers_lab/proof.lean` passes; no `sorryAx` in the theorem axioms |
| Scope | Two existing exception-handler theorems; no runtime or harness changes |
| Formatting | `git diff --check` passes |

DECIDED: publish this proof repair, inspect exact-SHA CI, then reread the
inbox before taking the next hosted Python proof failure.

## 2026-10-28-pycomplete-195 — repair the decimal-render proof

The hosted check's decimal-render theorem had become stale after builtin-name
resolution grew synthetic guards and function-frame local analysis. Its proof
now supplies the current late-raise/unbound-local walkers, synthetic builtin
names, starred-call marker equalities, and value/heap string rendering
normalization. The bounded `intDecimal` witness is retained and closes the
final public run after one explicit rewrite and definitional reduction.

| Measurement | Result |
|---|---|
| Focused proof | `lake build Examples.python.decimal_render.proof` passed; theorem has no `sorryAx` |
| Example surface | `lake env lean Examples/python/decimal_render/spec.lean` passed |
| Scope | Existing scalar decimal theorem only; runtime semantics unchanged |
| Formatting | `git diff --check` passed |

DECIDED: publish this proof repair, inspect exact-SHA CI, then reread the
inbox before taking the next hosted Python proof failure.

## 2026-10-28-pycomplete-196 — repair the exception-ancestor proof

The hosted proof for `exc_ancestors_lab` had fallen back to the generic
`py_prove` recipe and now timed out while normalizing the expanded exception
and builtin-resolution guards. Its arithmetic-ancestor theorem now uses the
explicit `callIn`/`py_simp` route with the current handler matching,
heap/generator guard, local-analysis, synthetic builtin, and retained-state
normalizers. The theorem statement and runtime semantics are unchanged.

| Measurement | Result |
|---|---|
| Focused proof | `lake env lean Examples/python/exc_ancestors_lab/proof.lean` passes; no `sorryAx` |
| Scope | One existing exception-ancestor theorem; no runtime or harness changes |
| Formatting | `git diff --check` passes |

DECIDED: commit and publish this proof repair after the current exact-SHA CI
reaches a terminal result, then inspect the new run and continue with its first
remaining Python failure.

## 2026-10-28-pycomplete-197 — repair the Boolean conversion proofs

The hosted check's two `bool_lab` theorems had outgrown the generic
`py_prove` recipe: the module now contains allocation-producing classes,
generators, and mutation examples, so the recipe left the Boolean conversion
state unresolved. Both symbolic theorems now use the explicit `callIn` route
and normalize the current builtin marker, local-analysis, heap/generator,
starred-call, and retained-state paths. Statements and runtime semantics are
unchanged.

| Measurement | Result |
|---|---|
| Focused proof | `lake env lean Examples/python/bool_lab/proof.lean` passes; no `sorryAx` |
| Scope | Two existing Boolean conversion theorems; no runtime or harness changes |
| Formatting | `git diff --check` passes |

DECIDED: commit and publish this proof repair after the current exact-SHA run
settles, then inspect the resulting CI and continue with its first remaining
Python failure.

## 2026-10-28-pycomplete-198 — repair the repr proof and stale custom guard

The hosted check's `repr_lab` proof had become stale after the renderer and
literal `__repr__` path grew additional heap, generator, builtin, and retained
state normalization. Both symbolic repr theorems now use a staged
`callIn`/`py_simp` recipe that exposes those walkers and closes the decimal
overflow and public-freeze paths. The same semantic change had left one stale
spec guard expecting `custom()` to refuse; it now checks the admitted
`"custom"` result. Runtime semantics and theorem statements are unchanged.

| Measurement | Result |
|---|---|
| Focused proof | `lake env lean Examples/python/repr_lab/proof.lean` passed; `lake build Examples.python.repr_lab.proof` passed |
| Example surface | `lake env lean Examples/python/repr_lab/spec.lean` passed |
| Axioms | both theorem outputs have no `sorryAx` |
| Hygiene | `git diff --check` passed |

DECIDED: commit this proof/spec repair, regenerate/check the backlog index,
then rebase and publish it before inspecting the new exact-SHA CI and taking
the next hosted Python failure.

## 2026-10-29-pycomplete-199 — admit body-local captures in one-argument `next`

The generator-expression capture gate now treats a genexp passed as the sole
argument to `next` as immediately consumed. A body-assigned local captured by
the synthesized generator is therefore observed before the enclosing frame can
run again, making the existing by-value lowering exact. The two-argument form
stays loud: Python evaluates its default before resuming the generator, so a
default-side walrus can make a by-value snapshot stale.

| Measurement | Result |
|---|---|
| Focused differential | 13 cases: 12 matches and 1 whitelisted refusal; all neighboring dict/genexp cursor rows unchanged |
| Proof interpreter | 13 refusals, 0 failures; this remains a runner-only admission until the proof interpreter's generator tier is widened |
| Refusal census | 44 rows in 12 classes; the old local-capture row left `genexp.lowering-admission`, and the walrus-default witness replaces it |
| Lean validation | `lake build LeanModels.Python` and `lake build leanmodels-run` pass; `git diff --check` passes |

DECIDED: admit only the one-argument `next` capture shape; retain the
two-argument default witness and all escaping/rebound captures as loud.

## 2026-10-29-pycomplete-200 — fuse immediately drained named genexps

The capture admission now also handles the exact local-generator shape
`g = (x for x in it if c); return all(g)` (and the other existing draining
consumers). Ingestion removes the unobserved local alias and feeds the original
genexp directly to the consumer, so the existing immediate-drain capture gate
can prove a body-assigned local is observed before the enclosing frame runs
again. This adds no runtime alias value or new generator semantics.

The negative companion `gen_assigned_rebound_still_loud` rebinds the captured
local between creation and consumption; it remains loud because a by-value
capture would be stale. Conditional binding (`drain_unbound`) remains loud as
well.

| Measurement | Result |
|---|---|
| Focused differential | 8 cases: 6 matches and 2 expected refusals; 0 failures |
| Full native differential | 3,758 cases: 3,714 matches, 44 recorded refusals, 0 failures |
| Refusal census | 44 rows in 12 classes, 0 drifts; the old `gen_assigned_lazy` row left the whitelist and the rebinding companion replaced it |
| Lean validation | `lake build leanmodels-run` passed; `git diff --check` passed |

DECIDED: fuse only an unobserved named genexp immediately consumed by a
draining builtin; preserve loud failure across rebinding, conditional binding,
and any intervening observation.

## 2026-10-29-pycomplete-202 — admit heap-backed list repetition in the proof interpreter

The fuel-based proof interpreter now follows the executable interpreter for
heap-list repetition. `list * int` and `int * list` allocate a fresh heap list,
including for zero and negative counts; `list *= int` updates the existing
address so aliases observe the mutation. The workers retain the shared
index-sized overflow, `seqBudget`, Boolean-count, and non-integral `TypeError`
behavior. Since repetition can allocate or mutate, `BinOp.mult` and `*=` are
excluded from the conditional `worldInv` fragment; scalar multiplication still
runs through the ordinary pure worker outside that theorem's assumptions.

| Measurement | Result |
|---|---|
| Focused proof differential | 8 cases: 8 MATCH, 0 refused, 0 failures (`repeat_live_list`, `repeat_aug_live_list`) |
| Full proof differential | 3,758 cases: 3,613 matched, 145 expected refusals, 0 failures |
| Build | `lake build leanmodels-run`, `lake build LeanModels.Python.Obs`, and `lake build Examples.python.string_repeat.spec` pass |
| Generated docs | `docs/python-coverage.md` refreshed from 3,605 to 3,613 proof matches; `git diff --check` passes |
| Clock erasure | Standalone legacy file still has unrelated pre-existing errors outside the supported build; new branches mirror the stateful worker paths |

DECIDED: admit heap-backed list repetition on the proof surface while keeping
allocation and mutation outside `worldInv`; retain list concatenation and other
unmodeled heap operations as loud boundaries.

## 2026-10-30-pycomplete-203 — admit range slices

Range subscripting now accepts a `slice` and returns the exact immutable range
that CPython constructs. The implementation normalizes omitted and negative
bounds against the source range length, composes the source and slice steps,
and preserves the source slice boundary for the resulting stop. It preserves
the shared slice validation messages for non-index bounds and zero steps and
does not materialize the range.

| Measurement | Result |
|---|---|
| Differential cases | Four new `seq_lab` rows: forward, reverse-step, empty, and zero-step error |
| Proof surface | Four new `#py_check` guards for `Val.range` results and the faithful `ValueError` |
| Hygiene | extractor envelope regenerated with pinned CPython 3.9 |

DECIDED: admit immediate range slices; keep range-valued formatting and
attribute access loud.

## 2026-10-31-pycomplete-204 — repair payload-blind TypeError census proof

The TypeError handler census landed with a heap-swapped-frame proof gap in
`PayloadBlind.pbExecStmt_succ`: the new shadow predicate has equivalent but
non-definitional conditions on the original and swapped frames. A two-condition
payload-blind `ite` bridge now carries that equivalence explicitly, restoring
the proof target and its dependent quickstart theorem.

| Measurement | Result |
|---|---|
| Focused Lean build | `LeanModels.Python.PayloadBlind` passed (14 jobs) |
| Hosted failure reproduced | `PayloadBlind.lean:4309` type mismatch; dependent `VCTests` and tri quickstarts failed |
| Scope | Proof repair only; no interpreter behavior change |

DECIDED: keep the handler census semantics and repair the frame proof with an
explicit equivalent-condition bridge.

## 2026-10-31-pycomplete-205 — refresh clock erasure after handler and range drift

The stateful clock-erasure induction now matches the current interpreter after
the cached function-scope `TypeError` handler census and immediate range-slice
support. Synthetic `TypeErrorHandler` markers are erased as ordinary no-op
statements, and the built-in exception branch transports the retained frame's
static-local and dynamic-shadow checks before deciding whether to enter the
handler. Existing range-slice state transport remains clock-free.

| Measurement | Result |
|---|---|
| Focused managed build | `lake build LeanModels.Python.ClockErase`: passed, 12 jobs |
| Scope | Proof layer only; interpreter behavior unchanged |
| Hygiene | `git diff --check` passed |

DECIDED: keep the handler census and range-slice semantics, with clock erasure
tracking their stateful proof paths; continue with the next measured Python
gap after dependent targets pass.

## 2026-10-31-pycomplete-206 — admit bare import exception identities

The exception table now admits bare `raise ImportError` and
`raise ModuleNotFoundError` as the existing `.builtinException` identities.
They are therefore caught by the already-modelled `except Exception`
hierarchy, while payload-bearing constructors and the separate direct
`except ImportError:` import-error path remain unchanged and loud where their
identity cannot be represented by the pinned `.importError` payload.

| Measurement | Result |
|---|---|
| New differential rows | Four rows: two bare raises and two `except Exception` catches |
| Proof guards | Four `#py_check` rows in `builtin_raise_lab` |
| Scope | Existing builtin exception identity; no new runtime representation |

DECIDED: admit only bare import exception identities and their admitted
`Exception` ancestor catch; retain the separate import-error and payload
boundaries until measured independently.

## 2026-10-31-pycomplete-207 — canonicalize OSError exception aliases

The admitted exception table now includes CPython's `EnvironmentError` and
`IOError` aliases. Bare raises and handler matching canonicalize both names to
the existing `OSError` identity, while import-error payloads and other
constructor forms remain unchanged.

| Measurement | Result |
|---|---|
| New differential rows | Four rows: two alias raises and two exact alias catches (eight argument cases) |
| Focused proof/native harnesses | 8/8 MATCH in each interpreter; no refusals or divergences |
| Full differential | 3,778 rows: 3,741 native matches, 3,640 proof matches, 0 failures |
| Script/refusal census | 142 scripts: 140 matches, 2 registered loud refusals; 37 call refusals and 2 script refusals, 0 drift |
| Scope | Exception identity aliases only; payload-bearing OSError constructors remain loud |

DECIDED: canonicalize the two historical OSError aliases; retain loud
behavior for payload and OS-derived exception constructors.

## 2026-10-31-pycomplete-208 — admit bare `StopAsyncIteration`

The builtin exception table now admits the leaf `StopAsyncIteration` identity.
A bare `raise StopAsyncIteration` therefore uses the existing
`.builtinException` representation and participates in the already-modelled
`except Exception:` hierarchy, while payload-bearing constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Exception` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,782 cases: 3,745 matched / 37 recorded refusals / 0 failed |
| Full proof differential | 3,782 cases: 3,644 matched / 138 refusals / 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; 37 call rows in 12 classes and 2 script rows, 0 drifts |
| Build and checks | Managed `lake build leanmodels-run`, extractor tests (150), generated coverage/progress/backlog checks, and `git diff --check` passed |

DECIDED: admit only the payload-free `StopAsyncIteration` class identity and its
ordinary `Exception` catch; retain loud behavior for payload constructors and
async execution constructs.

## 2026-10-31-pycomplete-209 — fix admitted exception coverage reporting

The coverage generator now reads `admittedBuiltinExc` directly when rendering
the exception-name table. This includes the three identities handled by the
generic exact-match fallback (`SystemExit`, `KeyboardInterrupt`, and
`GeneratorExit`) alongside the explicit matcher arms, so the generated page no
longer calls admitted names refused.

| Measurement | Result |
|---|---|
| Generated table | 23 admitted exception names and 44 refused CPython builtin names; the three previously misclassified identities moved to the admitted list |
| Freshness | `coverage_page.py --check`, docs check, language-progress check, backlog index, and `git diff --check` pass |
| Scope | Documentation generator and generated coverage page only; interpreter behavior unchanged |

DECIDED: derive the exception coverage list from the admission table rather
than the syntactic shape of the matcher, preserving accurate generated status
when generic fallback arms admit additional identities.
## 2026-10-31-pycomplete-210 — report import-error handler identities

The coverage generator now unions the two-name `importErrorHandlerMatch` table
from `Semantics.lean` with `admittedBuiltinExc`. The generated exception table
therefore counts `ImportError` and `ModuleNotFoundError` as admitted handler
identities instead of mentioning them only in prose.

| Measurement | Result |
|---|---|
| Generated table | 25 admitted exception names and 42 refused CPython builtin names; the separate import-error handler pair is now counted |
| Freshness | `coverage_page.py --check`, language-progress check, backlog index, docs check, and `git diff --check` pass |
| Scope | Documentation generator and generated coverage page only; interpreter behavior unchanged |

DECIDED: derive the coverage exception list from both semantic handler tables,
keeping the status page aligned with every accepted `except` identity.
## 2026-10-31-pycomplete-211 — admit bare `Warning`

The builtin exception table now admits the leaf `Warning` identity. A bare
`raise Warning` therefore uses the existing `.builtinException` representation
and participates in the already-modelled `except Exception:` hierarchy, while
payload-bearing constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Exception` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,786 cases: 3,749 matched / 37 recorded refusals / 0 failed |
| Full proof differential | 3,786 cases: 3,648 matched / 138 refusals / 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; extractor 150/150; generated docs, docs check, and `git diff --check` passed |

DECIDED: admit only the payload-free `Warning` class identity and its ordinary
`Exception` catch; retain loud behavior for warning payload constructors.

## 2026-10-31-pycomplete-212 — admit bare `UnicodeError`

The builtin exception table now admits the leaf `UnicodeError` identity. A
bare `raise UnicodeError` therefore uses the existing `.builtinException`
representation and participates in the already-modelled `except Exception:`
hierarchy, while payload-bearing Unicode error constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Exception` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,790 cases: 3,753 matched / 37 recorded refusals / 0 failed |
| Full proof differential | 3,790 cases: 3,652 matched / 138 refusals / 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; extractor 150/150; generated coverage/progress and `git diff --check` passed |

DECIDED: admit only the payload-free `UnicodeError` class identity and its
ordinary `Exception` catch; retain loud behavior for payload constructors.

## 2026-10-31-pycomplete-213 — admit bare `UnicodeWarning`

The builtin exception table now admits the leaf `UnicodeWarning` identity. A
bare `raise UnicodeWarning` uses the existing `.builtinException`
representation, and the warning hierarchy now lets `except Warning:` catch it
faithfully; payload-bearing warning constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Warning` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,794 cases: 3,757 matched / 37 recorded refusals / 0 failed |
| Full proof differential | 3,794 cases: 3,656 matched / 138 refusals / 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; extractor 150/150; generated coverage/progress and differential checks passed |

DECIDED: admit only the payload-free `UnicodeWarning` class identity and its
measured `Warning` hierarchy catch; retain loud behavior for payload
constructors.

## 2026-10-31-pycomplete-214 — admit bare `UserWarning`

The builtin exception table now admits the leaf `UserWarning` identity. A bare
`raise UserWarning` uses the existing `.builtinException` representation, and
the warning hierarchy now lets `except Warning:` catch it faithfully;
payload-bearing warning constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Warning` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,798 cases: 3,761 matched / 37 recorded refusals / 0 failed |
| Full proof differential | 3,798 cases: 3,660 matched / 138 refusals / 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; extractor 150/150; generated coverage/progress and differential checks passed |

DECIDED: admit only the payload-free `UserWarning` class identity and its
measured `Warning` hierarchy catch; retain loud behavior for payload
constructors.

## 2026-10-31-pycomplete-215 — admit bare `RuntimeWarning`

The builtin exception table now admits the leaf `RuntimeWarning` identity. A
bare `raise RuntimeWarning` uses the existing `.builtinException`
representation, and the warning hierarchy now lets `except Warning:` catch it
faithfully; payload-bearing warning constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Warning` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,802 cases: 3,765 decided and matched, 0 failed, and 37 recorded refusals |
| Full proof differential | 3,802 cases: 3,664 matched, 138 recorded refusals, and 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; generated coverage/progress and differential checks passed |

DECIDED: admit only the payload-free `RuntimeWarning` class identity and its
measured `Warning` hierarchy catch; retain loud behavior for payload
constructors.

## 2026-10-31-pycomplete-216 — admit bare `DeprecationWarning`

The builtin exception table now admits the leaf `DeprecationWarning` identity.
A bare `raise DeprecationWarning` uses the existing `.builtinException`
representation, and the warning hierarchy now lets `except Warning:` catch it
faithfully; payload-bearing warning constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Warning` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,806 cases: 3,769 decided and matched, 0 failed, and 37 recorded refusals |
| Full proof differential | 3,806 cases: 3,668 matched, 138 recorded refusals, and 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; generated coverage/progress and differential checks passed |

DECIDED: admit only the payload-free `DeprecationWarning` class identity and
its measured `Warning` hierarchy catch; retain loud behavior for payload
constructors.

## 2026-10-31-pycomplete-217 — admit bare `FutureWarning`

The builtin exception table now admits the leaf `FutureWarning` identity. A
bare `raise FutureWarning` uses the existing `.builtinException`
representation, and the warning hierarchy now lets `except Warning:` catch it
faithfully; payload-bearing warning constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Warning` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,810 cases: 3,773 decided and matched, 0 failed, and 37 recorded refusals |
| Full proof differential | 3,810 cases: 3,672 matched, 138 recorded refusals, and 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; generated coverage/progress and differential checks passed |

DECIDED: admit only the payload-free `FutureWarning` class identity and its
measured `Warning` hierarchy catch; retain loud behavior for payload
constructors.

## 2026-10-31-pycomplete-218 — admit bare `ImportWarning`

The builtin exception table now admits the leaf `ImportWarning` identity. A
bare `raise ImportWarning` uses the existing `.builtinException`
representation, and the warning hierarchy now lets `except Warning:` catch it
faithfully; payload-bearing warning constructors remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Warning` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,814 cases: 3,777 decided and matched, 0 failed, and 37 recorded refusals |
| Full proof differential | 3,814 cases: 3,676 matched, 138 recorded refusals, and 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; generated coverage/progress and differential checks passed |

DECIDED: admit only the payload-free `ImportWarning` class identity and its
measured `Warning` hierarchy catch; retain loud behavior for payload
constructors.

## 2026-10-31-pycomplete-219 — admit bare `PendingDeprecationWarning`

The builtin exception table now admits the leaf `PendingDeprecationWarning`
identity. A bare `raise PendingDeprecationWarning` uses the existing
`.builtinException` representation, and the warning hierarchy now lets
`except Warning:` catch it faithfully; payload-bearing warning constructors
remain loud.

| Measurement | Result |
|---|---|
| Focused differential | Four rows (bare raise and `except Warning` catch): 4/4 MATCH in native and proof interpreters |
| Full executable differential | 3,818 cases: 3,781 decided and matched, 0 failed, and 37 recorded refusals |
| Full proof differential | 3,818 cases: 3,680 matched, 138 recorded refusals, and 0 failed |
| Scripts and refusal census | 142 scripts: 140 matched and 2 registered loud refusals; refusal census 0 drift |
| Build and checks | Managed `leanmodels-run` and `builtin_raise_lab.spec` build passed; generated coverage/progress and differential checks passed |

DECIDED: admit only the payload-free `PendingDeprecationWarning` class
identity and its measured `Warning` hierarchy catch; retain loud behavior for
payload constructors.
