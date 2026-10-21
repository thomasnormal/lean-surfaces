# Class declarations — repricing boundary

`ClassType` marks an IEEE class declaration that the legacy envelope cannot
lower into its scalar module store. Classes may be virtual or interface
classes, extend another class, carry methods and extern declarations, and hold
random properties and constraints. Those features describe object identity,
allocation, inheritance, method activation and constrained-random state; they
are not procedural blocks that can be copied into a module.

## Why class declarations remain a boundary

The current loader has no class table, object heap, constructor/destructor
lifetime, virtual dispatch or method frame. A class body can also contain
constraint and random-property declarations whose legality and behavior depend
on inheritance and a randomization engine. Treating a class as an ordinary
module would erase object identity and method state; dropping the class body
would change elaboration and diagnostics. Compile-error rows intentionally
retain the frontend's class span rather than becoming an executable partial
design.

The public tier therefore keeps every `ClassType` declaration loud. A future
class tier must add a typed object representation and method/constraint rules
that call the existing scheduler where blocking behavior requires it. No
syntactic class-to-module rewrite, guessed random answer or second scheduler
is introduced. Nested class declarations have their own
`ClassType:ClassType` boundary and are not counted by the top-level
declaration repricing below.

## 2026-10-21 census and decision

The fresh 22,043-path census records `ClassType` in **1,328** files: **109**
class-only and **1,219** co-occurring. The class-only files contain **161**
class spans:

| class header shape | instances | files |
|---|---:|---:|
| ordinary `class` | 95 | 92 |
| `class extends` | 29 | 28 |
| `interface class` | 32 | 19 |
| `virtual class` | 5 | 5 |

Feature rows overlap when a class span contains several declarations:

| source feature | instances | files |
|---|---:|---:|
| methods (`function`/`task`) | 100 | 66 |
| random fields (`rand`/`randc`) | 44 | 42 |
| constraints | 29 | 26 |
| `extern` declarations | 4 | 4 |
| `typedef` members | 3 | 3 |

These labels describe the recovered source span, not an admission claim. No
class shape is independently admissible. Reproduce the table with:

```text
python3.9 extractors/sv/class_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its counts are telemetry for the object-model boundary, not a class
evaluator.

## Nested class declarations — 2026-10-21

`ClassType:ClassType` is emitted when a class declaration is a member of a
module. It is distinct from the top-level `ClassType` marker even though both
need the same object representation. The fresh 22,043-path census records
this marker in **509** files: **49** are class-use-only and **460** co-occur
with another wall. The sole files contain **65** nested class spans:

| class header shape | instances | files |
|---|---:|---:|
| ordinary `class` | 43 | 42 |
| `class extends` | 14 | 12 |
| `interface class` | 6 | 5 |
| `virtual class` | 2 | 2 |

The recovered spans have overlapping feature labels:

| source feature | instances | files |
|---|---:|---:|
| methods (`function`/`task`) | 25 | 20 |
| constraints | 22 | 19 |
| random fields (`rand`/`randc`) | 18 | 18 |
| virtual/interface mentions | 16 | 12 |
| `extends` | 17 | 15 |
| covergroups | 5 | 3 |

These rows describe source text only. A nested class still requires object
identity, allocation, inheritance, method frames and (for the overlapping
rows) randomization or coverage state; it is not flattened into its containing
module. Reproduce the table with:

```text
python3.9 extractors/sv/class_use_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only and leaves every nested class shape loud.
