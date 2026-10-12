# C++ integral object statements

`IntegralObjectStatements.lean` adds a small statement layer above integral
object expressions. An expression statement observes the current store without
changing it; an initialization evaluates a source before beginning an object's
lifetime; default initialization begins a scalar lifetime without publishing a
value; an assignment evaluates its source before applying the existing
profile-checked object conversion; a conditional evaluates an integral context
and executes exactly one branch; a sequence publishes the first statement's
store before executing the second. Explicit fuel bounds every statement and
expression recursion.

Errors remain loud and typed: object/lifetime failures, invalid values,
undefined integral operations, unsupported operations and fuel exhaustion are
not collapsed into a fabricated value. Aliases therefore observe earlier
writes, while a stale access refuses at the point of use.

Object allocation and declaration binding remain outside this fragment; the
caller supplies an allocated `ObjectId`. It does not admit loops, calls,
pointers, classes, floating values, overload resolution or general C++ execution.

## Checks

```sh
lake build LeanModels.Cpp.IntegralObjectStatementTests
```

Kernel guards cover initialization and default initialization, sequencing,
conditional true/false selection,
alias-visible order, division-by-zero, stale-access and const-write refusals,
plus statement and sequence fuel exhaustion. The independent integral object
and conversion Clang suites remain the value oracle; this statement layer makes
no whole-program execution claim.
