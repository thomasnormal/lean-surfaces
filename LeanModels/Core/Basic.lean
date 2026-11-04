namespace LeanModels

/-- A source span. Field names mirror CPython's `ast` attributes
(`lineno`, `col_offset`, `end_lineno`, `end_col_offset`); lines are 1-based,
columns 0-based, end positions exclusive, exactly as CPython reports them. -/
structure Span where
  lineno : Nat
  colOffset : Nat
  endLineno : Nat
  endColOffset : Nat
deriving Repr, DecidableEq, Inhabited

end LeanModels
