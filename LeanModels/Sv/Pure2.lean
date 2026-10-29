import LeanModels.Sv.Sem2

/-!
# The fuel-free expression evaluator of the semantic tier (`LeanModels.Sv`)

`evalExpr2` (`Sem2.lean`) is FUELED: it matches fuel first and passes the
decremented fuel to every child, and its `concat` arm walks the parts through
the mutual `evalExprs2`, which spends one more fuel unit per list cell. That
is the right shape for an executable interpreter and the wrong one for
reasoning about a single expression: every spec over `run2` would otherwise
carry fuel arithmetic down into each right-hand side. This file is the
foundation of the Design2 proof layer: it removes fuel from expression
evaluation once and for all.

## Design laws

* **Same clauses.** `evalPure2` is `evalExpr2` with the fuel match deleted
  and nothing else changed: the same `Res`-monad sequencing (children left to
  right, BOTH ternary arms evaluated, both `index` operands evaluated before
  the range test), the same `.unsupported` message, `readSignal` for
  identifiers, and `concat` through the list helper `evalPures2`, the
  fuel-free twin of `evalExprs2`. No clause is "simplified"; the adequacy
  proofs below are clause-by-clause syntactic matches after unfolding, which
  is what keeps the twin honest.
* **Structural recursion.** Both `evalPure2` and `Expr2.size` recurse
  structurally over the nested inductive `Expr2` (the `Array` in `concat` is
  reached through `parts.toList`, mutual with a `List Expr2` helper), so they
  are kernel-reducible and their equation lemmas are ordinary `rfl` facts.
* **Adequacy, both directions.**
  * `evalExpr2_eq_evalPure2`: with ANY fuel strictly above `e.size`, the
    fueled run equals the fuel-free one (so a proof may pick fuel once,
    globally, from a size bound).
  * `evalPure2_of_evalExpr2_ok`: a successful fueled run at ANY fuel already
    is the fuel-free value (fuel can only cut a run short, never change a
    decided value). This direction needs no size hypothesis and is what a
    soundness proof consumes when it is handed an `.ok` from the interpreter.
* **Size accounts for the list cells.** `Expr2.size` is the recursion depth
  of `evalExpr2` INCLUDING `evalExprs2`'s per-cell fuel unit: a part list of
  length `n` costs `n + 1` levels (the `[]` cell still needs one unit, since
  `evalExprs2 0 _ [] = .timeout`). Leaves have size `0`, so `0 < fuel`
  suffices for them — matching `evalExpr2 0 = .timeout`.
* **Well-formedness ⇒ success.** `evalPure2` can only fail on an
  `.unsupported` node or an unbound identifier (`readSignal`): with neither
  (`Expr2.unsupportedFree`, `Expr2.idents` all bound) it returns `.ok`
  (`evalPure2_ok_of_wf`). There is no timeout arm to rule out.
  `Expr2.unsupportedFree` is provably the negation of `Sem2`'s own loud-node
  scan (`Expr2.exprHas_eq_not_unsupportedFree`), so a profile may state the
  condition either way.
* **Frame at signal granularity.** `evalPure2_congr`: two states that agree
  on every identifier the expression mentions evaluate it identically.
  Window-granular framing (a slice reads only its bits) belongs to the comb
  layer, which builds on this.

## Simp interface

One `@[simp]` equation lemma per constructor (`evalPure2_lit`,
`evalPure2_ident`, …, `evalPure2_concat` stated through `evalPures2`, plus
`evalPures2_nil`/`evalPures2_cons`), in the same `do` shape as the
definition; `evalPure2_ident_of_lookup` is the identifier arm on a bound
name (cite it with the lookup fact). To step the binds, this file carries
its own copy of the `Res` normalization lemmas under the `Pure2.` prefix
(`Pure2.res_ok_bind`, …): `Obs.lean` has the same facts as `Res.ok_bind`
etc., but this module imports only `Sem2.lean` (the fuel-free evaluator
needs nothing from M0's fuel layer), and distinct names keep the two
importable together. The `simp` workflow is exemplified at the end of the
file, after the `#guard` agreement table that replays `Sem2`'s pinned rows
through both evaluators.
-/

namespace LeanModels.Sv

/-! ## `Res` normalization (local copies; see the module docstring) -/

namespace Pure2

/-- `pure` on `Res` is `Res.ok` (do-notation normalization). -/
@[simp] theorem res_pure_eq {α : Type} (a : α) : (pure a : Res α) = .ok a := rfl

/-- Bind on an `ok` result steps into the continuation. -/
@[simp] theorem res_ok_bind {α β : Type} (a : α) (f : α → Res β) :
    (Res.ok a >>= f) = f a := rfl

/-- Timeouts short-circuit bind. -/
@[simp] theorem res_timeout_bind {α β : Type} (f : α → Res β) :
    ((Res.timeout : Res α) >>= f) = .timeout := rfl

/-- `unsupported` short-circuits bind. -/
@[simp] theorem res_unsupported_bind {α β : Type} (msg : String) (f : α → Res β) :
    ((Res.unsupported msg : Res α) >>= f) = .unsupported msg := rfl

/-- Inversion of a successful bind: the intermediate result must itself be
`ok`. -/
@[simp] theorem res_bind_eq_ok {α β : Type} {x : Res α} {f : α → Res β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

end Pure2

/-! ## Size: the fuel an expression needs -/

mutual

/-- Fuel sufficient for `evalExpr2`: strictly greater than the recursion
depth INCLUDING the `evalExprs2` list cells of `concat` (each list cell costs
one fuel unit). Leaves are `0`; every node adds one level over its deepest
child; a `concat` adds one level over its part list's `Expr2.listSize`.
See `evalExpr2_eq_evalPure2`. -/
def Expr2.size : Expr2 → Nat
  | .lit _ | .ident _ | .unsupported _ _ => 0
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a
  | .slice a _ _ => a.size + 1
  | .binary _ l r | .scmp _ l r | .logical _ l r | .index l r _ =>
      max l.size r.size + 1
  | .ternary c t f => max c.size (max t.size f.size) + 1
  | .concat parts => Expr2.listSize parts.toList + 1
termination_by structural e => e

/-- Fuel sufficient for `evalExprs2` on a part list: one level per list cell
(the empty list included) over the deepest element. -/
def Expr2.listSize : List Expr2 → Nat
  | [] => 0
  | e :: es => max e.size (Expr2.listSize es) + 1
termination_by structural es => es

end

/-! ## The fuel-free evaluator -/

mutual

/-- Fuel-free twin of `evalExpr2`: SAME clauses, same `Res`-monad sequencing
(both ternary arms evaluated, left-to-right), same `.unsupported` messages,
structural recursion on `Expr2` (the `concat` parts go through `evalPures2`,
the twin of `evalExprs2`). Adequacy: `evalExpr2_eq_evalPure2`,
`evalPure2_of_evalExpr2_ok`. -/
def evalPure2 (st : SvState) : Expr2 → Res LVec
  | .lit v => .ok v
  | .ident name => readSignal st name
  | .unary op a => do
      return evalUnaryOp op (← evalPure2 st a)
  | .resizeSigned width operand => do
      return (← evalPure2 st operand).resizeSigned width
  | .squash2 operand => do
      return (← evalPure2 st operand).toTwoState
  | .binary op l r => do
      let a ← evalPure2 st l
      let b ← evalPure2 st r
      return evalBinOp op a b
  | .scmp op l r => do
      let a ← evalPure2 st l
      let b ← evalPure2 st r
      match a.toInt?, b.toInt? with
      | some x, some y =>
          return .ofLogic (match op with
            | .lt => if x < y then .l1 else .l0
            | .le => if x ≤ y then .l1 else .l0
            | .gt => if x > y then .l1 else .l0
            | .ge => if x ≥ y then .l1 else .l0
            | _ => .lx)  -- non-order op: outside the constructor contract
      | _, _ => return .ofLogic .lx
  | .logical isAnd l r => do
      let a ← evalPure2 st l
      let b ← evalPure2 st r
      let res : Logic :=
        if isAnd then
          if a.isKnownZero || b.isKnownZero then .l0
          else if a.condTrue && b.condTrue then .l1
          else .lx
        else
          if a.condTrue || b.condTrue then .l1
          else if a.isKnownZero && b.isKnownZero then .l0
          else .lx
      return .ofLogic res
  | .ternary c t f => do
      let cv ← evalPure2 st c
      let tv ← evalPure2 st t
      let fv ← evalPure2 st f
      return LVec.ternary cv tv fv
  | .concat parts => do
      let vs ← evalPures2 st parts.toList
      return LVec.concatMany vs.toArray
  | .slice base lo w => do
      return (← evalPure2 st base).extract lo w
  | .index base idx elemW => do
      let bv ← evalPure2 st base
      let iv ← evalPure2 st idx
      match iv.toNat? with
      | some i =>
          if (i + 1) * elemW ≤ bv.width then
            return bv.extract (i * elemW) elemW
          else
            return LVec.xVec elemW      -- out-of-range read: all-x (W05)
      | none => return LVec.xVec elemW  -- x/z index read: all-x (R02/R03/R05)
  | .repl n a => do
      return LVec.replVec n (← evalPure2 st a)
  | .reduce op a => do
      return .ofLogic (evalRedOp op (← evalPure2 st a))
  | .resize w a => do
      return (← evalPure2 st a).resizeU w
  | .unsupported svKind _ => .unsupported s!"unsupported expression '{svKind}'"
termination_by structural e => e

/-- Fuel-free twin of `evalExprs2`: evaluate a part list left to right,
first failure wins. -/
def evalPures2 (st : SvState) : List Expr2 → Res (List LVec)
  | [] => .ok []
  | e :: rest => do
      let v ← evalPure2 st e
      let vs ← evalPures2 st rest
      return v :: vs
termination_by structural es => es

end

/-! ## Equation lemmas (one per constructor, `simp`-ready) -/

@[simp] theorem evalPure2_lit (st : SvState) (v : LVec) :
    evalPure2 st (.lit v) = .ok v := rfl

@[simp] theorem evalPure2_ident (st : SvState) (name : String) :
    evalPure2 st (.ident name) = readSignal st name := rfl

/-- The identifier arm on a bound name (not `@[simp]`: `v` is not determined
by the left-hand side; cite it with the lookup fact). -/
theorem evalPure2_ident_of_lookup {st : SvState} {name : String} {v : LVec}
    (h : SvState.lookup st name = some v) : evalPure2 st (.ident name) = .ok v := by
  simp only [evalPure2, readSignal, h]

@[simp] theorem evalPure2_unary (st : SvState) (op : UnaryOp) (a : Expr2) :
    evalPure2 st (.unary op a) = (do return evalUnaryOp op (← evalPure2 st a)) := rfl

@[simp] theorem evalPure2_resizeSigned (st : SvState) (width : Nat) (a : Expr2) :
    evalPure2 st (.resizeSigned width a) =
      (do return (← evalPure2 st a).resizeSigned width) := rfl

@[simp] theorem evalPure2_squash2 (st : SvState) (a : Expr2) :
    evalPure2 st (.squash2 a) = (do return (← evalPure2 st a).toTwoState) := rfl

@[simp] theorem evalPure2_binary (st : SvState) (op : BinOp) (l r : Expr2) :
    evalPure2 st (.binary op l r) = (do
      let a ← evalPure2 st l
      let b ← evalPure2 st r
      return evalBinOp op a b) := rfl

@[simp] theorem evalPure2_scmp (st : SvState) (op : BinOp) (l r : Expr2) :
    evalPure2 st (.scmp op l r) = (do
      let a ← evalPure2 st l
      let b ← evalPure2 st r
      match a.toInt?, b.toInt? with
      | some x, some y =>
          return .ofLogic (match op with
            | .lt => if x < y then .l1 else .l0
            | .le => if x ≤ y then .l1 else .l0
            | .gt => if x > y then .l1 else .l0
            | .ge => if x ≥ y then .l1 else .l0
            | _ => .lx)
      | _, _ => return .ofLogic .lx) := rfl

@[simp] theorem evalPure2_logical (st : SvState) (isAnd : Bool) (l r : Expr2) :
    evalPure2 st (.logical isAnd l r) = (do
      let a ← evalPure2 st l
      let b ← evalPure2 st r
      let res : Logic :=
        if isAnd then
          if a.isKnownZero || b.isKnownZero then .l0
          else if a.condTrue && b.condTrue then .l1
          else .lx
        else
          if a.condTrue || b.condTrue then .l1
          else if a.isKnownZero && b.isKnownZero then .l0
          else .lx
      return .ofLogic res) := rfl

@[simp] theorem evalPure2_ternary (st : SvState) (c t f : Expr2) :
    evalPure2 st (.ternary c t f) = (do
      let cv ← evalPure2 st c
      let tv ← evalPure2 st t
      let fv ← evalPure2 st f
      return LVec.ternary cv tv fv) := rfl

@[simp] theorem evalPure2_concat (st : SvState) (parts : Array Expr2) :
    evalPure2 st (.concat parts) = (do
      let vs ← evalPures2 st parts.toList
      return LVec.concatMany vs.toArray) := rfl

@[simp] theorem evalPure2_slice (st : SvState) (base : Expr2) (lo w : Nat) :
    evalPure2 st (.slice base lo w) = (do return (← evalPure2 st base).extract lo w) := rfl

@[simp] theorem evalPure2_index (st : SvState) (base idx : Expr2) (elemW : Nat) :
    evalPure2 st (.index base idx elemW) = (do
      let bv ← evalPure2 st base
      let iv ← evalPure2 st idx
      match iv.toNat? with
      | some i =>
          if (i + 1) * elemW ≤ bv.width then
            return bv.extract (i * elemW) elemW
          else
            return LVec.xVec elemW
      | none => return LVec.xVec elemW) := rfl

@[simp] theorem evalPure2_repl (st : SvState) (n : Nat) (a : Expr2) :
    evalPure2 st (.repl n a) = (do return LVec.replVec n (← evalPure2 st a)) := rfl

@[simp] theorem evalPure2_reduce (st : SvState) (op : RedOp) (a : Expr2) :
    evalPure2 st (.reduce op a) = (do return .ofLogic (evalRedOp op (← evalPure2 st a))) :=
  rfl

@[simp] theorem evalPure2_resize (st : SvState) (w : Nat) (a : Expr2) :
    evalPure2 st (.resize w a) = (do return (← evalPure2 st a).resizeU w) := rfl

@[simp] theorem evalPure2_unsupported (st : SvState) (svKind text : String) :
    evalPure2 st (.unsupported svKind text) =
      .unsupported s!"unsupported expression '{svKind}'" := rfl

@[simp] theorem evalPures2_nil (st : SvState) : evalPures2 st [] = .ok [] := rfl

@[simp] theorem evalPures2_cons (st : SvState) (e : Expr2) (rest : List Expr2) :
    evalPures2 st (e :: rest) = (do
      let v ← evalPure2 st e
      let vs ← evalPures2 st rest
      return v :: vs) := rfl

/-! ## Adequacy: fueled = fuel-free above the size bound -/

/-- Both halves at once, by induction on fuel (the nested `concat` list is
handled by the `evalExprs2` conjunct, so no nested induction principle is
needed). -/
private theorem adequacy_aux (st : SvState) : ∀ fuel : Nat,
    (∀ e : Expr2, e.size < fuel → evalExpr2 fuel st e = evalPure2 st e) ∧
    (∀ es : List Expr2, Expr2.listSize es < fuel → evalExprs2 fuel st es = evalPures2 st es)
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | fuel + 1 => by
    obtain ⟨ihE, ihL⟩ := adequacy_aux st fuel
    refine ⟨fun e he => ?_, fun es hes => ?_⟩
    · -- `scmp`/`index` keep a `match` whose matcher constant differs between
      -- the two definitions (same `casesOn` body): closed by `rfl`.
      cases e <;> simp only [Expr2.size] at he <;>
        simp (disch := omega) only [evalExpr2, evalPure2, ihE, ihL] <;> rfl
    · cases es <;> simp only [Expr2.listSize] at hes <;>
        simp (disch := omega) only [evalExprs2, evalPures2, ihE, ihL]

/-- **Adequacy.** With any fuel strictly above `e.size`, the fueled
interpreter computes exactly the fuel-free value (including the same
`.unsupported` outcomes; `.timeout` is impossible). -/
theorem evalExpr2_eq_evalPure2 {fuel : Nat} {st : SvState} {e : Expr2}
    (h : e.size < fuel) : evalExpr2 fuel st e = evalPure2 st e :=
  (adequacy_aux st fuel).1 e h

/-- List twin of `evalExpr2_eq_evalPure2` (the `concat` part walk). -/
theorem evalExprs2_eq_evalPures2 {fuel : Nat} {st : SvState} {es : List Expr2}
    (h : Expr2.listSize es < fuel) : evalExprs2 fuel st es = evalPures2 st es :=
  (adequacy_aux st fuel).2 es h

/-! ## Adequacy: a decided fueled run is the fuel-free value -/

/-- `OkImp x y`: every `.ok` outcome of `x` is an `.ok` outcome of `y` (the
`.ok`-fragment of the flat fuel order). Private proof device. -/
private def OkImp {α : Type} (x y : Res α) : Prop := ∀ a, x = .ok a → y = .ok a

private theorem OkImp.refl {α : Type} (x : Res α) : OkImp x x := fun _ h => h

private theorem OkImp.bind {α β : Type} {x y : Res α} {f g : α → Res β}
    (hx : OkImp x y) (hf : ∀ a, OkImp (f a) (g a)) : OkImp (x >>= f) (y >>= g) := by
  intro b h
  cases x with
  | ok a => rw [hx a rfl]; exact hf a b h
  | timeout => simp at h
  | unsupported m => simp at h

/-- Both halves at once, by induction on fuel: every `.ok` of the fueled
interpreter is an `.ok` of the fuel-free one. -/
private theorem okImp_aux (st : SvState) : ∀ fuel : Nat,
    (∀ e : Expr2, OkImp (evalExpr2 fuel st e) (evalPure2 st e)) ∧
    (∀ es : List Expr2, OkImp (evalExprs2 fuel st es) (evalPures2 st es))
  | 0 => ⟨fun _ _ h => by simp [evalExpr2] at h, fun _ _ h => by simp [evalExprs2] at h⟩
  | fuel + 1 => by
    obtain ⟨ihE, ihL⟩ := okImp_aux st fuel
    refine ⟨fun e => ?_, fun es => ?_⟩
    · cases e <;> simp only [evalExpr2, evalPure2] <;>
        repeat (first
          | exact OkImp.refl _
          | exact ihE _
          | refine OkImp.bind (ihE _) fun _ => ?_
          | refine OkImp.bind (ihL _) fun _ => ?_)
    · cases es <;> simp only [evalExprs2, evalPures2] <;>
        repeat (first
          | exact OkImp.refl _
          | refine OkImp.bind (ihE _) fun _ => ?_
          | refine OkImp.bind (ihL _) fun _ => ?_)

/-- **Adequacy, decided direction.** A successful fueled run (at ANY fuel)
is the fuel-free value: fuel can only cut a run short, never change a
decided value. No size hypothesis. -/
theorem evalPure2_of_evalExpr2_ok {fuel : Nat} {st : SvState} {e : Expr2} {v : LVec}
    (h : evalExpr2 fuel st e = .ok v) : evalPure2 st e = .ok v :=
  (okImp_aux st fuel).1 e v h

/-- List twin of `evalPure2_of_evalExpr2_ok`. -/
theorem evalPures2_of_evalExprs2_ok {fuel : Nat} {st : SvState} {es : List Expr2}
    {vs : List LVec} (h : evalExprs2 fuel st es = .ok vs) : evalPures2 st es = .ok vs :=
  (okImp_aux st fuel).2 es vs h

/-! ## Well-formedness ⇒ success -/

mutual

/-- No `.unsupported` node anywhere in the expression (structural; the
expression-level half of `Design2.hasUnsupported`). -/
def Expr2.unsupportedFree : Expr2 → Bool
  | .unsupported _ _ => false
  | .lit _ | .ident _ => true
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a
  | .slice a _ _ => a.unsupportedFree
  | .binary _ l r | .scmp _ l r | .logical _ l r | .index l r _ =>
      l.unsupportedFree && r.unsupportedFree
  | .ternary c t f => c.unsupportedFree && t.unsupportedFree && f.unsupportedFree
  | .concat parts => Expr2.listUnsupportedFree parts.toList
termination_by structural e => e

/-- `Expr2.unsupportedFree` of every element of a part list. -/
def Expr2.listUnsupportedFree : List Expr2 → Bool
  | [] => true
  | e :: es => e.unsupportedFree && Expr2.listUnsupportedFree es
termination_by structural es => es

end

mutual

/-- Every identifier the expression reads (source order, with repeats). -/
def Expr2.idents : Expr2 → List String
  | .ident n => [n]
  | .lit _ | .unsupported _ _ => []
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a
  | .slice a _ _ => a.idents
  | .binary _ l r | .scmp _ l r | .logical _ l r | .index l r _ => l.idents ++ r.idents
  | .ternary c t f => c.idents ++ t.idents ++ f.idents
  | .concat parts => Expr2.listIdents parts.toList
termination_by structural e => e

/-- `Expr2.idents` of a part list, concatenated. -/
def Expr2.listIdents : List Expr2 → List String
  | [] => []
  | e :: es => e.idents ++ Expr2.listIdents es
termination_by structural es => es

end

/-- `IsOk x`: `x` is decided `.ok`. Private proof device. -/
private def IsOk {α : Type} (x : Res α) : Prop := ∃ a, x = .ok a

private theorem IsOk.bind {α β : Type} {x : Res α} {f : α → Res β}
    (hx : IsOk x) (hf : ∀ a, IsOk (f a)) : IsOk (x >>= f) := by
  obtain ⟨a, rfl⟩ := hx
  exact hf a

private theorem ok_of_wf_aux (st : SvState) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → e.unsupportedFree = true →
      (∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v) → IsOk (evalPure2 st e)) ∧
    (∀ es : List Expr2, Expr2.listSize es < n → Expr2.listUnsupportedFree es = true →
      (∀ x ∈ Expr2.listIdents es, ∃ v, SvState.lookup st x = some v) →
        IsOk (evalPures2 st es))
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ihE, ihL⟩ := ok_of_wf_aux st n
    refine ⟨fun e hs hu hb => ?_, fun es hs hu hb => ?_⟩
    · cases e with
      | ident name =>
          obtain ⟨v, hv⟩ := hb name (by simp [Expr2.idents])
          exact ⟨v, by simp [evalPure2, readSignal, hv]⟩
      | unsupported => simp [Expr2.unsupportedFree] at hu
      | _ =>
          simp only [Expr2.size] at hs
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [evalPure2]
          repeat (first
            | exact ⟨_, rfl⟩
            | refine IsOk.bind (ihE _ (by omega) (by simp_all)
                (fun x hx => hb x (by simp [Expr2.idents, hx]))) fun _ => ?_
            | refine IsOk.bind (ihL _ (by omega) (by simp_all)
                (fun x hx => hb x (by simp [Expr2.idents, hx]))) fun _ => ?_
            | split)
    · cases es with
      | nil => exact ⟨_, rfl⟩
      | cons e rest =>
          simp only [Expr2.listSize] at hs
          simp only [Expr2.listUnsupportedFree, Bool.and_eq_true] at hu
          simp only [evalPures2]
          refine IsOk.bind (ihE _ (by omega) hu.1
            (fun x hx => hb x (by simp [Expr2.listIdents, hx]))) fun _ => ?_
          refine IsOk.bind (ihL _ (by omega) hu.2
            (fun x hx => hb x (by simp [Expr2.listIdents, hx]))) fun _ => ?_
          exact ⟨_, rfl⟩

/-- **Well-formedness ⇒ success.** With no `.unsupported` node and every
identifier bound in `st`, the fuel-free evaluator decides `.ok` (the only
failure sources are `readSignal`'s unknown-identifier refusal and the
`.unsupported` node; there is no timeout arm). -/
theorem evalPure2_ok_of_wf {st : SvState} {e : Expr2}
    (hu : e.unsupportedFree = true)
    (hb : ∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v) :
    ∃ v, evalPure2 st e = .ok v :=
  (ok_of_wf_aux st (e.size + 1)).1 e (Nat.lt_succ_self _) hu hb

/-- List twin of `evalPure2_ok_of_wf`. -/
theorem evalPures2_ok_of_wf {st : SvState} {es : List Expr2}
    (hu : Expr2.listUnsupportedFree es = true)
    (hb : ∀ x ∈ Expr2.listIdents es, ∃ v, SvState.lookup st x = some v) :
    ∃ vs, evalPures2 st es = .ok vs :=
  (ok_of_wf_aux st (Expr2.listSize es + 1)).2 es (Nat.lt_succ_self _) hu hb

/-! ## Bridges and structural facts -/

private theorem exprHas_aux : ∀ n : Nat,
    (∀ e : Expr2, e.size < n →
      Design2.hasUnsupported.exprHas e = !e.unsupportedFree) ∧
    (∀ es : List Expr2, Expr2.listSize es < n →
      es.any Design2.hasUnsupported.exprHas = !Expr2.listUnsupportedFree es)
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ihE, ihL⟩ := exprHas_aux n
    refine ⟨fun e hs => ?_, fun es hs => ?_⟩
    · cases e with
      | concat parts =>
          simp only [Expr2.size] at hs
          simp only [Design2.hasUnsupported.exprHas, Expr2.unsupportedFree]
          rw [Array.any_subtype (g := Design2.hasUnsupported.exprHas) (fun _ _ => rfl)
            (by simp), Array.unattach_attach, ← Array.any_toList, ihL _ (by omega)]
      | _ =>
          simp only [Expr2.size] at hs
          simp (disch := omega) [Design2.hasUnsupported.exprHas, Expr2.unsupportedFree, ihE]
    · cases es <;> simp only [Expr2.listSize] at hs <;>
        simp (disch := omega) [Expr2.listUnsupportedFree, ihE, ihL]

/-- `Expr2.unsupportedFree` is exactly the negation of `Sem2`'s loud-node
scan `Design2.hasUnsupported.exprHas` (so a profile may state the
no-`unsupported` condition with either). -/
theorem Expr2.exprHas_eq_not_unsupportedFree (e : Expr2) :
    Design2.hasUnsupported.exprHas e = !e.unsupportedFree :=
  (exprHas_aux (e.size + 1)).1 e (Nat.lt_succ_self _)

/-- An element of a part list is strictly smaller than the list's size. -/
theorem Expr2.size_lt_listSize_of_mem {e : Expr2} {es : List Expr2} (h : e ∈ es) :
    e.size < Expr2.listSize es := by
  induction es with
  | nil => cases h
  | cons a rest ih =>
      simp only [Expr2.listSize]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := ih h; omega

/-- A `concat` part is strictly smaller than the `concat`. -/
theorem Expr2.size_lt_concat {e : Expr2} {parts : Array Expr2} (h : e ∈ parts.toList) :
    e.size < (Expr2.concat parts).size := by
  have := Expr2.size_lt_listSize_of_mem h
  simp only [Expr2.size]; omega

/-- A successful part walk returns one value per part. -/
theorem evalPures2_ok_length {st : SvState} {es : List Expr2} {vs : List LVec}
    (h : evalPures2 st es = .ok vs) : vs.length = es.length := by
  induction es generalizing vs with
  | nil => cases h; rfl
  | cons e rest ih =>
      simp only [evalPures2_cons, Pure2.res_bind_eq_ok, Pure2.res_pure_eq] at h
      obtain ⟨v, -, vs', hr, h⟩ := h
      cases h
      simp [ih hr]

/-- A successful part walk is pointwise: the `i`-th value is the `i`-th
part's value. -/
theorem evalPures2_ok_getElem {st : SvState} {es : List Expr2} {vs : List LVec}
    (h : evalPures2 st es = .ok vs) {i : Nat} (hi : i < es.length) (hv : i < vs.length) :
    evalPure2 st es[i] = .ok vs[i] := by
  induction es generalizing vs i with
  | nil => cases hi
  | cons e rest ih =>
      simp only [evalPures2_cons, Pure2.res_bind_eq_ok, Pure2.res_pure_eq] at h
      obtain ⟨v, he, vs', hr, h⟩ := h
      cases h
      cases i with
      | zero => exact he
      | succ i => exact ih hr (by simpa using hi) (by simpa using hv)

/-- `evalPures2` on a list of parts with known values. -/
theorem evalPures2_map {st : SvState} {es : List Expr2} {g : Expr2 → LVec}
    (h : ∀ e ∈ es, evalPure2 st e = .ok (g e)) : evalPures2 st es = .ok (es.map g) := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      simp only [evalPures2_cons, h e (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), Pure2.res_ok_bind,
        Pure2.res_pure_eq, List.map_cons]

private theorem congr_aux (st st' : SvState) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n →
      (∀ x ∈ e.idents, SvState.lookup st x = SvState.lookup st' x) →
        evalPure2 st e = evalPure2 st' e) ∧
    (∀ es : List Expr2, Expr2.listSize es < n →
      (∀ x ∈ Expr2.listIdents es, SvState.lookup st x = SvState.lookup st' x) →
        evalPures2 st es = evalPures2 st' es)
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ihE, ihL⟩ := congr_aux st st' n
    refine ⟨fun e hs hb => ?_, fun es hs hb => ?_⟩
    · cases e with
      | ident name =>
          simp only [evalPure2, readSignal, hb name (by simp [Expr2.idents])]
      | _ =>
          simp only [Expr2.size] at hs
          simp only [Expr2.idents, List.mem_append] at hb
          simp (disch := first | omega | (intro x hx; apply hb; simp [hx]))
            only [evalPure2, ihE, ihL]
    · cases es with
      | nil => rfl
      | cons e rest =>
          simp only [Expr2.listSize] at hs
          simp only [Expr2.listIdents, List.mem_append] at hb
          simp (disch := first | omega | (intro x hx; apply hb; simp [hx]))
            only [evalPures2, ihE, ihL]

/-- **Frame (whole-signal granularity).** `evalPure2` reads the state only
through the identifiers the expression mentions. (Window-granular
refinements — a slice reads only its bits — are built on top of this in the
comb layer.) -/
theorem evalPure2_congr {st st' : SvState} {e : Expr2}
    (h : ∀ x ∈ e.idents, SvState.lookup st x = SvState.lookup st' x) :
    evalPure2 st e = evalPure2 st' e :=
  (congr_aux st st' (e.size + 1)).1 e (Nat.lt_succ_self _) h

/-- List twin of `evalPure2_congr`. -/
theorem evalPures2_congr {st st' : SvState} {es : List Expr2}
    (h : ∀ x ∈ Expr2.listIdents es, SvState.lookup st x = SvState.lookup st' x) :
    evalPures2 st es = evalPures2 st' es :=
  (congr_aux st st' (Expr2.listSize es + 1)).2 es (Nat.lt_succ_self _) h

/-! ## Agreement table (`#guard` twins of `Sem2`'s pinned rows)

Every row evaluates the SAME expression with the fueled interpreter (at the
fuel `Sem2`'s own table uses) and with `evalPure2`, and checks both against
the pinned value. The last block pins the size bound's tightness on a
`concat`: fuel `= size` times out (the `[]` list cell), `size + 1` agrees. -/

private def pv86 : LVec := .lit "10100110"
private def pm4x8 : LVec := .lit "10100001101100101100001111010100"  -- 32'hA1B2C3D4

/-- One agreement row: the two evaluators coincide and hit `expected`. -/
private def agrees (fuel : Nat) (st : SvState) (e : Expr2) (expected : Res LVec) : Bool :=
  evalExpr2 fuel st e == evalPure2 st e && evalPure2 st e == expected

-- pin1 R01–R03: dynamic bit select; x/z index reads x.
#guard agrees 32 [] (.index (.lit pv86) (.lit (.ofNat 3 2)) 1) (.ok (.lit "1"))
#guard agrees 32 [] (.index (.lit pv86) (.lit (.lit "xxx")) 1) (.ok (.lit "x"))
#guard agrees 32 [] (.index (.lit pv86) (.lit (.lit "01x")) 1) (.ok (.lit "x"))
-- pin1 R04–R05: 2D element select; x index → all-x.
#guard agrees 32 [] (.index (.lit pm4x8) (.lit (.ofNat 2 3)) 8) (.ok (.lit "10100001"))
#guard agrees 32 [] (.index (.lit pm4x8) (.lit (.lit "xx")) 8) (.ok (.lit "xxxxxxxx"))
-- pin2a W05: out-of-range dynamic read → x.
#guard agrees 32 [] (.index (.lit pv86) (.lit (.ofNat 4 9)) 1) (.ok (.lit "x"))
-- pin1 R06: constant part select v[6:3].
#guard agrees 32 [] (.slice (.lit pv86) 3 4) (.ok (.lit "0100"))
-- pin1 R07 / pin4 Z06: replication.
#guard agrees 32 [] (.repl 3 (.lit (.lit "10"))) (.ok (.lit "101010"))
#guard agrees 32 [] (.repl 2 (.lit (.lit "1x"))) (.ok (.lit "1x1x"))
-- pin4 S01–S05: signed vs unsigned comparison.
#guard agrees 32 [] (.scmp .lt (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))) (.ok (.lit "1"))
#guard agrees 32 [] (.binary .lt (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))) (.ok (.lit "0"))
#guard agrees 32 [] (.scmp .ge (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))) (.ok (.lit "0"))
#guard agrees 32 [] (.scmp .lt (.lit (.ofNat 8 0x80)) (.lit (.ofNat 8 0x7F))) (.ok (.lit "1"))
#guard agrees 32 [] (.scmp .lt (.lit (.lit "x1111111")) (.lit (.ofNat 8 0x7F))) (.ok (.lit "x"))
-- pin5 L01–L12: logical && / ||.
#guard agrees 8 [] (.logical true (.lit (.lit "00")) (.lit (.lit "xx"))) (.ok (.lit "0"))
#guard agrees 8 [] (.logical true (.lit (.lit "10")) (.lit (.lit "xx"))) (.ok (.lit "x"))
#guard agrees 8 [] (.logical false (.lit (.lit "xx")) (.lit (.lit "01"))) (.ok (.lit "1"))
#guard agrees 8 [] (.logical false (.lit (.lit "xx")) (.lit (.lit "00"))) (.ok (.lit "x"))
-- pin4 Z01–Z04: bitwise resize keeps x bits.
#guard agrees 32 [] (.resize 12 (.lit (.lit "x1x0"))) (.ok (.lit "00000000x1x0"))
#guard agrees 32 [] (.resize 4 (.lit (.lit "1x000101"))) (.ok (.lit "0101"))

-- Gate-level shapes (the multiplier/adder profile): slices of identifiers,
-- `& | ^`, concatenation (first part = MSB), reduction, ternary.
private def gst : SvState := [("a", .lit "1011"), ("b", .lit "0110"), ("c", .lit "1")]
#guard agrees 32 gst
  (.binary .xor (.binary .xor (.slice (.ident "a") 1 1) (.slice (.ident "b") 1 1))
    (.ident "c")) (.ok (.lit "1"))
#guard agrees 32 gst
  (.binary .or (.binary .and (.slice (.ident "a") 0 1) (.slice (.ident "b") 0 1))
    (.binary .and (.ident "c") (.binary .xor (.slice (.ident "a") 0 1)
      (.slice (.ident "b") 0 1)))) (.ok (.lit "1"))
#guard agrees 32 gst
  (.concat #[.slice (.ident "a") 2 2, .ident "c", .slice (.ident "b") 0 3])
  (.ok (.lit "101110"))
#guard agrees 32 gst (.concat #[]) (.ok (LVec.concatMany #[]))
#guard agrees 32 gst (.reduce .xor (.ident "a")) (.ok (.lit "1"))
#guard agrees 32 gst (.ternary (.ident "c") (.ident "a") (.ident "b")) (.ok (.lit "1011"))
-- Loud outcomes coincide too: unknown identifier, unsupported node (BOTH
-- ternary arms are evaluated, so a loud untaken arm is still loud).
#guard agrees 32 gst (.ident "nope")
  (.unsupported "unknown identifier 'nope' (not a declared signal)")
#guard agrees 32 gst (.ternary (.ident "c") (.ident "a") (.unsupported "Foo" "foo"))
  (.unsupported "unsupported expression 'Foo'")

-- Size tightness on `concat` (two leaves: size 3; the list cells cost fuel).
#guard (Expr2.concat #[.ident "a", .ident "b"]).size == 3
#guard evalExpr2 3 gst (.concat #[.ident "a", .ident "b"]) == .timeout
#guard agrees 4 gst (.concat #[.ident "a", .ident "b"]) (.ok (.lit "10110110"))
#guard (Expr2.slice (.binary .and (.ident "a") (.ident "b")) 0 1).size == 2
#guard evalExpr2 2 gst (.slice (.binary .and (.ident "a") (.ident "b")) 0 1) == .timeout
#guard agrees 3 gst (.slice (.binary .and (.ident "a") (.ident "b")) 0 1) (.ok (.lit "0"))

/-- Kernel-reducibility witness: `evalPure2` is structural, so a concrete
evaluation closes by `decide` (kernel evaluation, no `native_decide`). -/
example : evalPure2 [("a", LVec.ofNat 4 11)] (.slice (.ident "a") 1 2) =
    .ok (LVec.ofNat 2 1) := by decide

/-- The `simp` workflow on a symbolic state: equation lemmas + the `Pure2.`
bind normalizers + the lookup facts reduce a gate-level expression to one
`.ok` value (no fuel, no unfolding of `evalExpr2`). -/
example (st : SvState) (a b : LVec) (ha : SvState.lookup st "a" = some a)
    (hb : SvState.lookup st "b" = some b) :
    evalPure2 st (.concat #[.binary .xor (.slice (.ident "a") 0 1) (.slice (.ident "b") 0 1),
        .ident "b"]) =
      .ok (LVec.concatMany #[evalBinOp .xor (a.extract 0 1) (b.extract 0 1), b]) := by
  simp [evalPure2_ident_of_lookup ha, evalPure2_ident_of_lookup hb]

end LeanModels.Sv
