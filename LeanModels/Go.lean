import LeanModels.Go.SpecAttr
import LeanModels.Go.Value
import LeanModels.Go.Sem
import LeanModels.Go.Stmt
import LeanModels.Go.Spec

/-!
# The Go tier

`docs/go-charter.md` is the founding charter; `docs/backlog/go.md` is the
lane's record. Importing this module pulls the whole lane in.

M1 inch 1 (`docs/backlog/go.md` §G2): values, the substrate by shape,
rung 1's abstract syntax and its first statement walker, and the
specification lemmas — split spec half from interpreter half per STMT-65.
-/
