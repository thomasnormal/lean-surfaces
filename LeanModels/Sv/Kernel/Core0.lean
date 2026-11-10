import LeanModels.Sv.Kernel.Core0E

/-!
# E-core-0 compatibility import

The authoritative definitions live in `Core0E`. This historical module name
re-exports that same core, so standalone E backends and older proof modules
share the same store, body evaluator, scheduler, and behaviour relation.
Legacy transport proofs import their own dependencies explicitly.
-/
