# C++ integral object statements

`IntegralObjectStatements.lean` adds a small statement layer above integral
object expressions. An expression statement observes the current store without
changing it; an initialization evaluates a source before beginning an object's
lifetime; default initialization begins a scalar lifetime without publishing a
value; an assignment evaluates its source before applying the existing
profile-checked object conversion; a conditional evaluates an integral context
and executes exactly one branch; a sequence publishes the first statement's
store before executing the second; `whileLoop` re-evaluates its integral
condition after each body execution. Explicit fuel bounds every statement and
expression recursion. `forLoop` runs a supplied initializer once, then uses
the same state-threaded condition/body/step discipline.

`break_` exits the nearest admitted loop and is refused at the public
statement boundary when no loop consumes it.

Errors remain loud and typed: object/lifetime failures, invalid values,
undefined integral operations, unsupported operations and fuel exhaustion are
not collapsed into a fabricated value. Aliases therefore observe earlier
writes, while a stale access refuses at the point of use.

Object allocation and declaration binding remain outside this fragment; the
caller supplies an allocated `ObjectId`. The admitted loops are integral
`whileLoop` and preallocated-object `forLoop`; `break_` is the only admitted
loop transfer; calls, `do`/`while`, pointers,
classes, floating values,
overload resolution and general C++ execution remain outside the fragment.

## Checks

```sh
lake build LeanModels.Cpp.IntegralObjectStatementTests
python3 extractors/cpp/test_integral_objects.py
```

Kernel guards cover initialization and default initialization, sequencing,
conditional true/false selection, terminating and empty `whileLoop` cases,
`forLoop` initialization/step order, and loop-local/public `break_` behavior,
alias-visible order, division-by-zero, stale-access and const-write refusals,
plus statement, sequence and loop fuel exhaustion. The independent integral object
and conversion Clang suites remain the value oracle; this statement layer makes
no whole-program execution claim. The statement harness compares 1,734 safe
add, branch, loop, `forLoop`, `break_` and sequence traces against C++23
compiled with Clang at `-O0` and `-O2` under UBSan.
