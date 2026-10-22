# Defparam overrides — repricing boundary

IEEE §§6.20, 23.10 and 23.10.4 apply a `defparam` override during hierarchy
elaboration. The target is a parameter selected through an instance path,
possibly through several nested instances or an instance-array element. The
elaborator resolves all overrides before generate decisions; when several
overrides name one parameter, the last source-order assignment wins. A single
statement may contain several overrides, and the RHS is a constant expression
whose parameter references are resolved in the declaring module's scope.

## Why defparam remains a boundary

The public envelope has no hierarchy-wide parameter environment, instance-path
resolver, override precedence table, source-order update pass or generate
re-evaluation state. Replacing a `defparam` with an inline module-instance
parameter loses deep-path and array-element targeting, and applying a local
constant after generate elaboration changes which scopes exist. The tier
therefore keeps `DefParamSymbol:DefParam` loud, including invalid cross-array
targets; it does not add a second elaborator or scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `DefParamSymbol:DefParam` in **49** files:
**23** are defparam-only and **26** co-occur with another wall. Repricing the
sole files finds **33** spans: all **33** have hierarchical targets, **13**
use deep paths, **4** select instance-array elements, **9** exercise
last-wins source order, **6** put several overrides in one statement, **2**
reference a parameter on the RHS, **1** uses RHS arithmetic, **2** exercise
instance-override precedence, **1** depends on applying the value before a
generate decision, **2** are invalid cross-array diagnostics, **1** tests a
dependent-parameter chain and **1** is a chapter-37 type form (features
overlap).

Reproduce the table with:

```text
python3.9 extractors/sv/defparam_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it classifies target paths and source shapes
without resolving an instance, changing a parameter or running elaboration.
