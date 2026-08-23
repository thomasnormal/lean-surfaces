import Lean

/-!
# The `@[go_spec]` attribute

Its own module, and that is forced rather than tidy: an attribute
registered by `register_label_attr` becomes available at an IMPORT
boundary, so it cannot be used in the file that declares it. The ES lane's
`es_spec` and the Python lane's `py_spec` have the same shape.

`LeanModels/Go/Spec.lean` is where the lemmas live.
-/

namespace LeanModels.Go

/-- The Go tier's specification-lemma registry, kept per-lane so it can
never be confused with a sibling's (`py_spec`, `es_spec`). -/
register_label_attr go_spec

end LeanModels.Go
