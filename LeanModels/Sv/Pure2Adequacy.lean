import LeanModels.Sv.Pure2
import LeanModels.Sv.Sem2Run

namespace LeanModels.Sv

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
