import Lean

/-!
# The `@[es_spec]` attribute

Its own module, and that is forced rather than tidy: an attribute
registered by `register_label_attr` becomes available at an IMPORT
boundary, so it cannot be used in the file that declares it. The Python
lane's `py_spec` has the same shape.

`LeanModels/Es/Spec.lean` is where the lemmas live.
-/

namespace LeanModels.Es

/-- The ES tier's specification-lemma registry — the arrow-form registry
this DSL's vcgen will consult, kept per-lane so it can never be confused
with a sibling's (`py_spec`, and whatever the C lane registers). -/
register_label_attr es_spec

end LeanModels.Es
