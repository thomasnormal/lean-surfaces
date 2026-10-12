import LeanModels.Python

set_option maxRecDepth 65536

/-!
# with_lab — the synchronous context-manager slice

The admitted shape is deliberately narrow: one direct constructor item,
an implicit constructor, `__enter__`/`__exit__`, and normal body flow.
Multiple items, explicit constructors, and `async with` stay loud until
their exception and async protocols are represented.
-/

open LeanModels LeanModels.Python

load_program with_lab from "Examples/python/with_lab/with_lab.json"

#py_check with_lab.bound_value() = 42
#py_check with_lab.unbound_value() = 7
#py_check with_lab.fallthrough() = 40

#guard callFunction with_lab "multiple_items" #[] 4096 matches .unsupported _
#guard callFunction with_lab "explicit_init" #[] 4096 matches .unsupported _
#guard callFunction with_lab "extra_dunder" #[] 4096 matches .unsupported _
