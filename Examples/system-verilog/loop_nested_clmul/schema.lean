import LeanModels.Sv.Ingest2
import LeanModels.Sv.Loop2
import LeanModels.Sv.PinAxioms

/-!
# The nested `clmul` loops: their trip schema (WS3, gate G-L0) — *provisional over `run2`*

`proc_nested_for.sv` is byte-identical to `svgolf/tests/clmul/attacks/proc_nested_for.sv`:

```systemverilog
always_comb begin
  p = '0;
  for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++)
      p[i+j] = p[i+j] ^ (a[i] & b[j]);
end
```

The envelope (`python3.12 extractors/sv/extract.py --top clmul_n …`) retains both loops as `For`
nodes (`symbolic_for_parameter`). `headers` reads the two headers off it by `rfl`; `nest_agrees`
proves, at a symbolic `N` (any environment binding the parameter `N < 2^31`), that the nest's trip
schema is `TripSchema2.mk (arith 0 1 N) (fun _ => arith 0 1 N)` in 32-bit `int` arithmetic, the
inner header evaluated with the outer iterator bound (`instStmt2`'s discipline). The inner schema
is indexed by the outer trip; here it happens not to depend on it.
-/

namespace Examples.«system-verilog».loop_nested_clmul.schema

open LeanModels.Sv LeanModels.Sv.Loop2

load_design_sv2 clmul_n from "Examples/system-verilog/loop_nested_clmul/proc_nested_for.sv.json"

abbrev iR : PExpr := .genvarRef "i"
abbrev jR : PExpr := .genvarRef "j"
abbrev nR : PExpr := .paramRef "N" none

/-- The inner loop's body: `p[i+j] = p[i+j] ^ (a[i] & b[j]);` (one statement in a block). -/
def tripBody : PStmt :=
  .block [.blockingAssignL (.bitSel "p" (.binary (.m0 .add) iR jR))
    (.binary (.m0 .xor) (.bitSel (.ident "p") (.binary (.m0 .add) iR jR))
      (.binary (.m0 .and) (.bitSel (.ident "a") iR) (.bitSel (.ident "b") jR)))]

/-- **The source**, read off the envelope (`rfl`): one `always_comb`, `p = '0`, then the nest. -/
theorem source : clmul_n.pdesign.processes =
    [.alwaysComb (.block [.blockingAssign "p" (.fill .l0),
      .forLoop "i" (.int 0) (.binary Cmp.lt.op iR nR) (.unary .inc iR)
        (.block [.forLoop "j" (.int 0) (.binary Cmp.lt.op jR nR) (.unary .inc jR) tripBody])])] :=
  rfl

/-- **The nest's trip schema at a symbolic `N`**: `N` outer trips, and `N` inner trips at every
outer trip, `0, 1, …, N-1` each, read in 32-bit `int`. -/
theorem nest_agrees {env : IEnv} {N : Nat} (hN : env.vals.lookup "N" = some (N : Int))
    (h32 : N < 2147483648) :
    (TripSchema2.mk (TripSchema.arith 0 1 N) fun _ => TripSchema.arith 0 1 N).HeaderAgrees env
      "i" (.int 0) (.binary Cmp.lt.op iR nR) (.unary .inc iR)
      "j" (.int 0) (.binary Cmp.lt.op jR nR) (.unary .inc jR) := by
  -- one header, at any environment binding `N` and any iterator name other than `N`
  have one : ∀ (e : IEnv) (it : String), e.vals.lookup "N" = some (N : Int) → "N" ≠ it →
      (TripSchema.arith 0 1 N).HeaderAgrees e it (.int 0) (.binary Cmp.lt.op (.genvarRef it) nR)
        (.unary .inc (.genvarRef it)) := by
    intro e it he hne
    have hlk : ∀ v, (e.bindVal it v).vals.lookup "N" = some (N : Int) := fun v => by
      rw [vals_lookup_bindVal_ne v hne, he]
    have h := headerAgrees_canon (c := .lt) (B := N) (evalInt_int 0) (procStepDelta2_inc e it)
      (fun v _ => guard_canon .lt (fun v => isInt_paramRef_of (hlk v))
        (fun v => evalInt_paramRef_of (hlk v)) v)
      (canonCount_lt_one (n := N) (by rw [int32_zero]; omega) ⟨by omega, by omega⟩)
    rwa [int32_zero] at h
  exact ⟨one env "i" hN (by decide), fun k =>
    one _ "j" (by rw [vals_lookup_bindVal_ne _ (by decide), hN]) (by decide)⟩

/-- The trip schema is unique: any schema of this nest is `N × N`. -/
theorem nest_unique {env : IEnv} {N : Nat} (hN : env.vals.lookup "N" = some (N : Int))
    (h32 : N < 2147483648) {S : TripSchema2}
    (hS : S.HeaderAgrees env "i" (.int 0) (.binary Cmp.lt.op iR nR) (.unary .inc iR)
      "j" (.int 0) (.binary Cmp.lt.op jR nR) (.unary .inc jR)) :
    S = TripSchema2.mk (TripSchema.arith 0 1 N) fun _ => TripSchema.arith 0 1 N :=
  hS.unique (nest_agrees hN h32)

/-- The computed schema (`headerSchema`, fuel-free) of the outer header is `0, …, N-1`. -/
theorem outer_computed {env : IEnv} {N : Nat} (hN : env.vals.lookup "N" = some (N : Int))
    (h32 : N < 2147483648) :
    headerSchema env "i" (.int 0) (.binary Cmp.lt.op iR nR) (.unary .inc iR) =
      .ok (TripSchema.arith 0 1 N) := by
  have hb : boundAt? env "i" nR = some (N : Int) := by simp [boundAt?, hN]
  simp only [headerSchema, evalInt_int, procStepDelta2_inc, Cmp.op, Cmp.ofOp?, hb, if_true,
    int32_zero, canonCount_lt_one (n := N) (by omega : (N : Int) = 0 + N) ⟨by omega, by omega⟩]
  rfl

/-- The derived list views: the outer trips are `intRange 0 N`. -/
theorem outer_list (N : Nat) : (TripSchema.arith 0 1 N).toList = intRange 0 N :=
  TripSchema.toList_arith_one 0 N

/-! ## Axioms -/

#pin_axioms source nest_agrees nest_unique outer_computed outer_list

end Examples.«system-verilog».loop_nested_clmul.schema
