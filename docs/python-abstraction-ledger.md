# Python abstraction ledger

This ledger records every deliberate simplification in the Python tier that
can be observed by a supported program. A row is either exact on a stated
domain, an explicit input, or a loud refusal. The protocol implementation and
the evidence row are named together so a new admission cannot silently widen
an abstraction.

## Semantic abstractions

| Abstraction | Observers | Boundary or decision | Evidence |
|---|---|---|---|
| Immediate values do not have CPython object identity | `is`, container equality, membership, ordering, dict/set key probes | `None`, refs, and the admitted bool/int cases are exact; other immediate identity and non-finite container comparisons refuse | `foundation_probe` NaN rows; `docs/python-protocol-census.md` RichCompareBool row |
| Heap identity is represented by `Addr` | `is`, aliasing mutation, recursive equality, generators, instances | heap refs use address identity; public boundary freeze is a snapshot and does not promise sharing | `sf_hist`, dict/list alias batteries, `memory-model.md` identity section |
| Fuel bounds interpreter recursion and stepping | every fueled mutual function, generator drain, recursive equality | fuel exhaustion is `.timeout`; it never becomes `.unsupported` and never fabricates a value | `fuelMono`, `foundation_cases.json` deep rows |
| CPython recursion depth is normalized in `World.callDepth` | function/closure calls, argument diagnostics, builtin C frames, generator resumption, comparison | pinned entry depth and limit 1000; unsupported sites remain loud until their `Py_EnterRecursiveCall` path is modeled | `arity_recursion`, `generator_recursion`, `round_recursion`, `sorted_recursion`, `foundation_cases.json` |
| Binary64 is stored as a 64-bit word | float arithmetic, parsing, rendering, identity-sensitive NaN behavior | IEEE binary64 words and pinned CPython 3.9 behavior are exact where workers state it; platform-dependent `pow`, complex, and unresolved NaN payload paths refuse | `docs/python-floats.md`, `float64_test.py`, `foundation_probe` |
| Python integers are unbounded, while C index conversions are bounded | list/range length, list `pop`/`insert`, repetition, slicing | raising conversion uses signed 64-bit `Py_ssize_t`; clamping conversion clips before sequence clamping; allocation-dependent overflow remains loud | `foundation_cases.json` ssize rows; `docs/python-protocol-census.md` index rows |
| Hash-table layout and hash randomization are not modeled | set iteration, set construction order, identity-hashed keys | finite numeric/tuple key slice is admitted; process-order and identity-hash observations refuse | `set` order rows, `docs/memory-model.md` set section |
| Allocation cannot fail inside the modeled heap | list/dict/set/class/generator allocation | fixed materialization budgets and unsupported boundaries replace environment-dependent memory exhaustion; no fabricated result is returned | range/list/set/dict differential rows; `memory-model.md` allocation rules |
| Wall-clock values are not guessed | `time.time()` and clock-dependent code | the trace is an explicit `World.clock` input, but the current integer trace cannot represent CPython binary64 readings, so a consumed read refuses; dead reads remain exact | clock battery and `memory-model.md` trace-clock section |
| Rendering tables are finite and explicit | `str`, `repr`, `print`, container rendering | admitted scalar/container forms use the shared renderer; sets, identity objects, unsupported Unicode rendering, and unbounded recursion remain loud | `repr_script`, `print_set`, `print_nonascii`, `docs/python-protocol-census.md` rendering row |
| Two interpreter surfaces observe the same structured domain | Every differential row is run by the runner and, where the proof tier admits it, by `Semantics.lean` | the runner currently observes 4,968 rows and the proof interpreter 4,845; a refusal in the narrower proof tier is evidence of its declared boundary, never a disagreement | `harness/interpreter_ledger.py`, `harness/diff_test.py --proof-interpreter` |
| Measured opaque imported modules | import binding, attribute read, call, truthiness, comparison, iteration, identity, rendering and argument passing | the eleven entries in `docs/python-opaque-imports.json` are admitted only as opaque names after a fresh CPython 3.9.25 import is silent, non-raising and leaves the builtins dictionary unchanged; every observation refuses with the module/attribute named, and an unlisted module stays loud. Definition-time annotations that traverse an opaque binding are refused by the frontend; `rsa_inverse` records its `typing.Tuple[...]` observation separately. | `tools/python_opaque_imports.py`, `docs/python-opaque-imports.json`, `Examples/python/opaque_import_lab`; annotation refusal is measured in the generated rsa envelope |

## Platform and oracle assumptions

| Input or platform choice | Pinned value or treatment | What would observe it | Evidence / consequence |
|---|---|---|---|
| Language implementation | CPython 3.9.25 for both AST frontend and default oracle | parsing, diagnostics, builtins, Unicode tables | `tools/leanpy`, `harness/diff_test.py`; missing or foreign Python 3.9 is a refusal |
| Word size for `Py_ssize_t` | signed 64-bit range `[-2^63, 2^63-1]` | indices, lengths, repetition and allocation checks | shared `pySsizeRaising`/`pySsizeClamping`; out-of-range rows pin errors or loudness |
| Float representation | IEEE 754 binary64 | float conversion and arithmetic | `Float64` word model; non-portable libm results refuse |
| Unicode database | CPython 3.9's Unicode 13.0.0 tables | decimal parsing, whitespace, case and rendering | float/text differential batteries; unsupported Unicode rendering stays loud |
| Recursion limit | 1000 at the oracle boundary | all recursive call and C-call sites | `World.callDepth`, `recursion_limit` and builtin recursion batteries |
| C library `pow` / libm | not selected as a hidden host dependency | floating `**` outside portable special cases | `float_power_special` admits only portable cases; general platform `pow` refuses |
| Hash seed and table layout | not selected | set order and identity hash | set-order and identity-key paths refuse rather than replay one process |
| Locale, filesystem, OS modules, threads and real time | no implicit host observation | imports and environmental effects | structured import admission and explicit clock trace; unsupported effects refuse |

## Maintenance rule

Every new decided row must name the abstraction it observes and add an edge
case at its boundary in both interpreter modes. If the CPython path consults a
platform choice that is not listed here, the implementation must introduce an
explicit input or refuse before it can return a value. The protocol census in
`docs/python-protocol-census.md` is the call-site inventory; this page records
why each shared worker is sound on its admitted domain.
