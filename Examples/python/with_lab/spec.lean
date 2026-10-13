import LeanModels.Python

set_option maxRecDepth 65536

/-!
# with_lab — the synchronous context-manager slice

The admitted shape is deliberately narrow: one direct constructor item,
an implicit or supported explicit constructor, `__enter__`/`__exit__`, and
normal body flow. Body exceptions are admitted when `__exit__` is transparent
(`pass` or `return None`/`False`) or a literal `return True` suppression;
argument-sensitive suppression and `async with` stay loud.
-/

open LeanModels LeanModels.Python

load_program with_lab from "Examples/python/with_lab/with_lab.json"

#py_check with_lab.bound_value() = 42
#py_check with_lab.unbound_value() = 7
#py_check with_lab.fallthrough() = 40
#py_check with_lab.explicit_init() = 0
#py_check with_lab.multiple_items() = 0
#py_check with_lab.body_exception() raises .zeroDivisionError
#py_check with_lab.body_exception_target() raises .zeroDivisionError
#py_check with_lab.suppressed_exception() = 7

#guard callFunction with_lab "extra_dunder" #[] 4096 matches .unsupported _
