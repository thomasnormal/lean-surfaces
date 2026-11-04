import LeanModels.Sv.Loop2

/-!
# Values of expressions and the slice-write primitive (WS3) — *provisional over `run2`*

The backend-neutral expression view `valE` (`evalPure2_valE`: it is `evalPure2` on the simple
expressions loop bodies use), the frame facts `sig_set_self`/`sig_set_ne`, the seam primitive
`Denotes.assignSliceE` (the only lemma here that meets `evalExpr2`, through
`evalExpr2_eq_evalPure2`), and what Bridge S consumes of a body (`SingleBody` over `BoundAll`). The
recognizer and its tactics are `Loop2Frag.lean`.
-/

namespace LeanModels.Sv.Loop2

/-! ## The value of an expression (backend-neutral) -/

/-- The value of an expression on a state, each identifier read as its bound value (`sig`): the
total view of `evalPure2` on the expression forms loop bodies use (`simpleExpr`). -/
def valE (st : SvState) : Expr2 → LVec
  | .lit v => v
  | .ident x => sig st x
  | .unary op a => evalUnaryOp op (valE st a)
  | .binary op l r => evalBinOp op (valE st l) (valE st r)
  | .slice a lo w => (valE st a).extract lo w
  | .resize w a => (valE st a).resizeU w
  | .reduce op a => .ofLogic (evalRedOp op (valE st a))
  | _ => default

/-- The expression forms `valE` covers. -/
def simpleExpr : Expr2 → Bool
  | .lit _ | .ident _ => true
  | .unary _ a | .slice a _ _ | .resize _ a | .reduce _ a => simpleExpr a
  | .binary _ l r => simpleExpr l && simpleExpr r
  | _ => false

/-- **`valE` is `evalPure2`** on a simple expression whose identifiers are bound. -/
theorem evalPure2_valE {st : SvState} : ∀ {e : Expr2}, simpleExpr e = true →
    (∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v) → evalPure2 st e = .ok (valE st e)
  | .lit _, _, _ => rfl
  | .ident x, _, hb => by
      obtain ⟨v, hv⟩ := hb x (by simp [Expr2.idents])
      simp [readSignal, valE, sig, hv]
  | .unary _ a, hs, hb => by
      rw [evalPure2_unary, evalPure2_valE (e := a) (by simpa [simpleExpr] using hs)
        (by simpa [Expr2.idents] using hb)]; rfl
  | .binary _ l r, hs, hb => by
      simp only [simpleExpr, Bool.and_eq_true] at hs
      have hb' : ∀ x ∈ l.idents ++ r.idents, ∃ v, SvState.lookup st x = some v := by
        simpa [Expr2.idents] using hb
      rw [evalPure2_binary, evalPure2_valE hs.1 fun x hx => hb' x (List.mem_append_left _ hx),
        evalPure2_valE hs.2 fun x hx => hb' x (List.mem_append_right _ hx)]; rfl
  | .slice a _ _, hs, hb => by
      rw [evalPure2_slice, evalPure2_valE (e := a) (by simpa [simpleExpr] using hs)
        (by simpa [Expr2.idents] using hb)]; rfl
  | .resize _ a, hs, hb => by
      rw [evalPure2_resize, evalPure2_valE (e := a) (by simpa [simpleExpr] using hs)
        (by simpa [Expr2.idents] using hb)]; rfl
  | .reduce _ a, hs, hb => by
      rw [evalPure2_reduce, evalPure2_valE (e := a) (by simpa [simpleExpr] using hs)
        (by simpa [Expr2.idents] using hb)]; rfl
  | .resizeSigned _ _, hs, _ | .squash2 _, hs, _ | .scmp _ _ _, hs, _ | .logical _ _ _, hs, _
  | .ternary _ _ _, hs, _ | .concat _, hs, _ | .index _ _ _, hs, _ | .repl _ _, hs, _
  | .unsupported _ _, hs, _ => by simp [simpleExpr] at hs

@[simp] theorem sig_set_self (st : SvState) (n : String) (v : LVec) :
    sig (SvState.set st n v) n = v := by
  simp [sig]

@[simp] theorem sig_set_ne (st : SvState) {n x : String} (v : LVec) (h : x ≠ n) :
    sig (SvState.set st n v) x = sig st x := by
  simp [sig, CombGuard.lookup_set_ne _ _ h]

/-! ## The backend seam: one slice-writing trip -/

/-- **One generic trip** `n[lo +: w] = e` on the states `I`, through the fuel-free `valE` (the only
lemma here that meets `evalExpr2`). -/
theorem Denotes.assignSliceE {I : SvState → Prop} {n : String} {lo w : Nat} {e : Expr2}
    (hs : simpleExpr e = true)
    (hb : ∀ st, I st → ∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v)
    (hn : ∀ st, I st → ∃ v, SvState.lookup st n = some v) :
    Denotes I (.blockingAssign (.slice n lo w) e) fun st =>
      SvState.set st n ((sig st n).insertAt lo ((valE st e).resizeU w)) :=
  Denotes.assignSlice ⟨e.size + 1, fun st hst _ hf => by
    rw [evalExpr2_eq_evalPure2 (by omega), evalPure2_valE hs (hb st hst)]⟩ hn

/-! ## What a body must give Bridge S -/

/-- Every name of `ns` is bound. -/
def BoundAll (ns : List String) (st : SvState) : Prop := ∀ x ∈ ns, ∃ v, SvState.lookup st x = some v

theorem BoundAll.set {ns : List String} {st : SvState} (h : BoundAll ns st) (n : String) (v : LVec) :
    BoundAll ns (SvState.set st n v) := fun x hx => by
  by_cases hxn : x = n
  · subst hxn; exact ⟨v, CombGuard.lookup_set_self ..⟩
  · rw [CombGuard.lookup_set_ne _ _ hxn]; exact h x hx

/-- What Bridge S needs of a body: it denotes `f` on `I`, `f` keeps `I`, `f` is idempotent. -/
def SingleBody (I : SvState → Prop) (body : Stmt2) (f : SvState → SvState) : Prop :=
  Denotes I body f ∧ (∀ st, I st → I (f st)) ∧ ∀ st, f (f st) = f st

end LeanModels.Sv.Loop2

#pin_axioms LeanModels.Sv.Loop2.evalPure2_valE LeanModels.Sv.Loop2.sig_set_self
  LeanModels.Sv.Loop2.sig_set_ne LeanModels.Sv.Loop2.Denotes.assignSliceE
  LeanModels.Sv.Loop2.BoundAll.set
