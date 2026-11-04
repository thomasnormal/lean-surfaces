import LeanModels.Sv.Ingest2
import LeanModels.Sv.Loop2
import LeanModels.Sv.PinAxioms

/-!
# Trip schemas of the endpoint headers (WS3, gate G-L0) — *provisional over `run2`*

`loop_edges.sv` has one `always_comb` per header shape, every bound a parameter so the extractor
retains the loop as a `For` node. This file reads each header off the envelope (`headers`, by `rfl`:
the source header, not a hand copy), and proves which trip schema agrees with it, at a symbolic
parameter point (an environment binding `N` and `C`), in 32-bit `int` arithmetic
(`LeanModels/Sv/Loop2.lean`). Agreement determines the schema (`TripSchema.HeaderAgrees.unique`),
so each theorem names THE trips of its header.

| header | trips | theorem |
|---|---|---|
| `for (int i = 0; i < N; i++)` | `0, 1, …, N-1` (0 trips at `N = 0`, 1 at `N = 1`, 126, 127, 200) | `lt_agrees`, `lt_at` |
| `for (int i = 0; i <= N; i++)` | `0, …, N` | `le_agrees` |
| `for (int i = N - 1; i >= 0; i--)` | `N-1, …, 0` | `desc_agrees` |
| `for (int i = 0; i < N; i += C)` | `0, C, 2C, …` (`⌈N/C⌉`) | `step_agrees` |
| `for (int i = -C; i < N; i++)` | `-C, …, N-1` | `neg_agrees` |
| `for (int i = 0; i < C; i++) for (int i = 0; i < N; i++)` | outer `0..C-1`, inner `0..N-1` (the inner `i` shadows the outer) | `shadow_agrees` |
| `for (int N = 0; N < C; N++)` | `0..C-1` (the iterator shadows the parameter `N`) | `pshadow_agrees` |
| `for (int i = 0; i < N; i++) for (int j = 0; j < i; j++)` | inner schema of outer trip `k` is `0..k-1` | `tri_agrees` (hand header: the extractor does not retain the inner loop, see the end of the file) |

The legacy instantiation (`forValues2`, at the fuel master's `forFuel2` derives) agrees with the
computed schema on every header and point checked; the old fixed fuel 128 timed out from 127 trips on
(replayed by a guard).
-/

namespace Examples.«system-verilog».loop_edges.schema

open LeanModels.Sv LeanModels.Sv.Loop2

load_design_sv2 loop_edges from "Examples/system-verilog/loop_edges/loop_edges.sv.json"

/-! ## The headers, read off the envelope -/

/-- The header of the `for` that is the second statement of an `always_comb` block. -/
def hdr? : PProcess → Option (String × PExpr × PExpr × PExpr)
  | .alwaysComb (.block [_, .forLoop it i c s _]) => some (it, i, c, s)
  | _ => none

/-- The inner header of a directly nested `for … for …`. -/
def hdr2? : PProcess → Option (String × PExpr × PExpr × PExpr)
  | .alwaysComb (.block [_, .forLoop _ _ _ _ (.forLoop it i c s _)]) => some (it, i, c, s)
  | _ => none

abbrev iR : PExpr := .genvarRef "i"
abbrev nR : PExpr := .paramRef "N" none
abbrev cR : PExpr := .paramRef "C" none

/-- **The source headers**, in process order (`rfl` on the envelope). -/
theorem headers : loop_edges.pdesign.processes.map hdr? =
    [some ("i", .int 0, .binary Cmp.lt.op iR nR, .unary .inc iR),
     some ("i", .int 0, .binary Cmp.le.op iR nR, .unary .inc iR),
     some ("i", .binary (.m0 .sub) nR (.int 1), .binary Cmp.ge.op iR (.int 0), .unary .dec iR),
     some ("i", .int 0, .binary Cmp.lt.op iR nR, .binary (.m0 .add) iR cR),
     some ("i", .unary (.m0 .neg) cR, .binary Cmp.lt.op iR nR, .unary .inc iR),
     some ("i", .int 0, .binary Cmp.lt.op iR cR, .unary .inc iR),
     some ("N", .int 0, .binary Cmp.lt.op (.genvarRef "N") cR, .unary .inc (.genvarRef "N"))] := rfl

/-- The inner header of the shadowing nest (process 5): `for (int i = 0; i < N; i++)`. -/
theorem shadow_inner : (loop_edges.pdesign.processes.map hdr2?)[5]? =
    some (some ("i", .int 0, .binary Cmp.lt.op iR nR, .unary .inc iR)) := rfl

/-! ## The environment: `N` and `C` bound, as `instantiate2` binds them -/

variable {env : IEnv} {N C : Nat}

theorem nR_int (hN : env.vals.lookup "N" = some (N : Int)) (it : String) (h : "N" ≠ it) (v : Int) :
    nR.isInt (env.bindVal it v) = true :=
  isInt_paramRef_of (by rw [vals_lookup_bindVal_ne v h, hN])

theorem nR_val (hN : env.vals.lookup "N" = some (N : Int)) (it : String) (h : "N" ≠ it) (v : Int) :
    evalInt (env.bindVal it v) nR = .ok N :=
  evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne v h, hN])

theorem cR_int (hC : env.vals.lookup "C" = some (C : Int)) (it : String) (h : "C" ≠ it) (v : Int) :
    cR.isInt (env.bindVal it v) = true :=
  isInt_paramRef_of (by rw [vals_lookup_bindVal_ne v h, hC])

theorem cR_val (hC : env.vals.lookup "C" = some (C : Int)) (it : String) (h : "C" ≠ it) (v : Int) :
    evalInt (env.bindVal it v) cR = .ok C :=
  evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne v h, hC])


/-! ## The trip schemas -/

/-- `for (int i = 0; i < N; i++)`: `0, …, N-1`. -/
theorem lt_agrees (hN : env.vals.lookup "N" = some (N : Int)) (h32 : N < 2147483648) :
    (TripSchema.arith 0 1 N).HeaderAgrees env "i" (.int 0) (.binary Cmp.lt.op iR nR)
      (.unary .inc iR) := by
  have h := headerAgrees_canon (c := .lt) (B := N) (evalInt_int 0) (procStepDelta2_inc env "i")
    (fun v _ => guard_canon .lt (nR_int hN "i" (by decide)) (nR_val hN "i" (by decide)) v)
    (canonCount_lt_one (n := N) (by rw [int32_zero]; omega) ⟨by omega, by omega⟩)
  rwa [int32_zero] at h

/-- The endpoint values of `N`: `0, 1, 126, 127, 200` trips. -/
theorem lt_at (hN : env.vals.lookup "N" = some (N : Int)) (hv : N ∈ [0, 1, 126, 127, 200]) :
    (TripSchema.arith 0 1 N).HeaderAgrees env "i" (.int 0) (.binary Cmp.lt.op iR nR)
      (.unary .inc iR) ∧ (TripSchema.arith 0 1 N).count = N :=
  ⟨lt_agrees hN (by simp at hv; omega), rfl⟩

/-- `for (int i = 0; i <= N; i++)`: `0, …, N`. -/
theorem le_agrees (hN : env.vals.lookup "N" = some (N : Int)) (h32 : N + 1 < 2147483648) :
    (TripSchema.arith 0 1 (N + 1)).HeaderAgrees env "i" (.int 0) (.binary Cmp.le.op iR nR)
      (.unary .inc iR) := by
  have h := headerAgrees_canon (c := .le) (B := N) (evalInt_int 0) (procStepDelta2_inc env "i")
    (fun v _ => guard_canon .le (nR_int hN "i" (by decide)) (nR_val hN "i" (by decide)) v)
    (canonCount_le_one (n := N + 1) (by rw [int32_zero]; omega) ⟨by omega, by omega⟩)
  rwa [int32_zero] at h

/-- `for (int i = N - 1; i >= 0; i--)`: `N-1, N-2, …, 0`. -/
theorem desc_agrees (hN : env.vals.lookup "N" = some (N : Int)) (h32 : N < 2147483648) :
    (TripSchema.arith ((N : Int) - 1) (-1) N).HeaderAgrees env "i"
      (.binary (.m0 .sub) nR (.int 1)) (.binary Cmp.ge.op iR (.int 0)) (.unary .dec iR) := by
  have hinit : evalInt env (.binary (.m0 .sub) nR (.int 1)) = .ok ((N : Int) - 1) :=
    evalInt_sub_of (isInt_paramRef_of hN) rfl (evalInt_paramRef_of hN) rfl
  have hi : int32 ((N : Int) - 1) = (N : Int) - 1 := int32_of_inInt32 ⟨by omega, by omega⟩
  have h := headerAgrees_canon (c := .ge) (B := 0) hinit (procStepDelta2_dec env "i")
    (fun v _ => guard_canon .ge (rhs := .int 0) (B := 0) (fun _ => rfl) (fun _ => rfl) v)
    (canonCount_ge_dec (n := N) (by rw [hi]; omega) ⟨by omega, by omega⟩)
  rwa [hi] at h

/-- `for (int i = 0; i < N; i += C)` with `C > 0`: `0, C, 2C, …`, `⌈N/C⌉` trips. -/
theorem step_agrees (hN : env.vals.lookup "N" = some (N : Int)) (hC : env.vals.lookup "C" = some (C : Int))
    (hC0 : 0 < C) (h32 : N + C < 2147483648) :
    (TripSchema.arith 0 C (ascCount 0 C N)).HeaderAgrees env "i" (.int 0)
      (.binary Cmp.lt.op iR nR) (.binary (.m0 .add) iR cR) := by
  have hstep : procStepDelta2 env "i" (.binary (.m0 .add) iR cR) = .ok C :=
    procStepDelta2_add (evalInt_paramRef_of hC) (by omega)
  have hexit := ascCount_exit (s := 0) (B := N) (δ := C) (by omega)
  have hrun : ∀ k, k < ascCount 0 C N → (0 : Int) + k * C < N :=
    fun k hk => ascCount_run (by omega) hk
  have hcount : canonCount .lt 0 C N = .ok (ascCount 0 C N) := by
    by_cases h0 : N = 0
    · have hz : ascCount 0 C N = 0 := by
        rcases Nat.eq_zero_or_pos (ascCount 0 C N) with h | h
        · exact h
        · have := hrun 0 h; simp at this; omega
      rw [hz]
      exact canonCount_none (by simp [Cmp.sign, Cmp.bound]; omega)
    · -- the last trip is below `N`, so the exit value is below `N + C`
      have hlast : (0 : Int) + ((ascCount 0 C N : Nat) : Int) * C < N + C := by
        have hpos : 0 < ascCount 0 C N := by
          rcases Nat.eq_zero_or_pos (ascCount 0 C N) with h | h
          · rw [h] at hexit; simp at hexit; omega
          · exact h
        have := hrun (ascCount 0 C N - 1) (by omega)
        rw [show (((ascCount 0 C N - 1 : Nat)) : Int) = ((ascCount 0 C N : Nat) : Int) - 1 by
          omega, Int.sub_mul, Int.one_mul] at this
        omega
      exact canonCount_up (c := .lt) rfl (by omega) (by simp [Cmp.sign, Cmp.bound]; omega)
        ⟨by have := Int.mul_nonneg (Int.natCast_nonneg (ascCount 0 C N)) (Int.natCast_nonneg C)
            simp only [Cmp.bound]; omega, by simp only [Cmp.bound]; omega⟩
  have h := headerAgrees_canon (c := .lt) (B := N) (evalInt_int 0) hstep
    (fun v _ => guard_canon .lt (nR_int hN "i" (by decide)) (nR_val hN "i" (by decide)) v)
    (by rw [int32_zero]; exact hcount)
  rwa [int32_zero] at h

/-- `for (int i = -C; i < N; i++)`: `-C, …, N-1`. -/
theorem neg_agrees (hN : env.vals.lookup "N" = some (N : Int)) (hC : env.vals.lookup "C" = some (C : Int))
    (h32 : N + C < 2147483648) :
    (TripSchema.arith (-(C : Int)) 1 (N + C)).HeaderAgrees env "i" (.unary (.m0 .neg) cR)
      (.binary Cmp.lt.op iR nR) (.unary .inc iR) := by
  have hinit : evalInt env (.unary (.m0 .neg) cR) = .ok (-(C : Int)) := by
    simp [evalInt, hC, Gen2.except_ok_bind]
  have hi : int32 (-(C : Int)) = -(C : Int) := int32_of_inInt32 ⟨by omega, by omega⟩
  have h := headerAgrees_canon (c := .lt) (B := N) hinit (procStepDelta2_inc env "i")
    (fun v _ => guard_canon .lt (nR_int hN "i" (by decide)) (nR_val hN "i" (by decide)) v)
    (canonCount_lt_one (n := N + C) (by rw [hi]; omega) ⟨by omega, by omega⟩)
  rwa [hi] at h

/-- **Iterator shadowing**: `for (int i = 0; i < C; i++) for (int i = 0; i < N; i++)` — the
inner header is evaluated with the outer `i` bound, and its own `i` shadows it. -/
theorem shadow_agrees (hN : env.vals.lookup "N" = some (N : Int)) (hC : env.vals.lookup "C" = some (C : Int))
    (h32 : N < 2147483648) (hC32 : C < 2147483648) :
    (TripSchema2.mk (TripSchema.arith 0 1 C) fun _ => TripSchema.arith 0 1 N).HeaderAgrees env
      "i" (.int 0) (.binary Cmp.lt.op iR cR) (.unary .inc iR)
      "i" (.int 0) (.binary Cmp.lt.op iR nR) (.unary .inc iR) := by
  refine ⟨?_, fun k => ?_⟩
  · have h := headerAgrees_canon (c := .lt) (B := C) (evalInt_int 0) (procStepDelta2_inc env "i")
      (fun v _ => guard_canon .lt (cR_int hC "i" (by decide)) (cR_val hC "i" (by decide)) v)
      (canonCount_lt_one (n := C) (by rw [int32_zero]; omega) ⟨by omega, by omega⟩)
    rwa [int32_zero] at h
  · -- the outer binding of `i` is invisible under the inner one; `N` is read through both
    have hN' : (env.bindVal "i" ((TripSchema.arith 0 1 C).value k)).vals.lookup "N" = some (N : Int) := by
      rw [vals_lookup_bindVal_ne _ (by decide), hN]
    exact lt_agrees hN' h32

/-- **A parameter shadowed by the iterator**: `for (int N = 0; N < C; N++)`. -/
theorem pshadow_agrees (hC : env.vals.lookup "C" = some (C : Int)) (h32 : C < 2147483648) :
    (TripSchema.arith 0 1 C).HeaderAgrees env "N" (.int 0)
      (.binary Cmp.lt.op (.genvarRef "N") cR) (.unary .inc (.genvarRef "N")) := by
  have h := headerAgrees_canon (c := .lt) (B := C) (evalInt_int 0) (procStepDelta2_inc env "N")
    (fun v _ => guard_canon .lt (cR_int hC "N" (by decide)) (cR_val hC "N" (by decide)) v)
    (canonCount_lt_one (n := C) (by rw [int32_zero]; omega) ⟨by omega, by omega⟩)
  rwa [int32_zero] at h

/-- **A nested dependent bound** (hand header, the form the extractor would emit if it kept the
inner loop): `for (int i = 0; i < N; i++) for (int j = 0; j < i; j++)`. The inner schema of outer
trip `k` is `0, …, k-1`. -/
theorem tri_agrees (hN : env.vals.lookup "N" = some (N : Int)) (h32 : N < 2147483648) :
    (TripSchema2.mk (TripSchema.arith 0 1 N) fun k => TripSchema.arith 0 1 k).HeaderAgrees env
      "i" (.int 0) (.binary Cmp.lt.op iR nR) (.unary .inc iR)
      "j" (.int 0) (.binary Cmp.lt.op (.genvarRef "j") iR) (.unary .inc (.genvarRef "j")) := by
  refine ⟨lt_agrees hN h32, fun k => ?_⟩
  have hk : (k : Nat) < 2147483648 := by have := k.2; simp at this; omega
  have hval : (TripSchema.arith 0 1 N).value k = (k : Nat) := by
    show (0 : Int) + ((k : Nat) : Int) * 1 = ((k : Nat) : Int); omega
  show (TripSchema.arith 0 1 (k : Nat)).HeaderAgrees (env.bindVal "i" ((TripSchema.arith 0 1 N).value k))
    "j" _ _ _
  rw [hval]
  have hi : ∀ w : Int, evalInt (((env.bindVal "i" (k : Nat)).bindVal "j" w)) iR = .ok (k : Nat) :=
    fun w => evalInt_genvarRef_of (by rw [vals_lookup_bindVal_ne w (by decide)]; simp)
  have h := headerAgrees_canon (c := .lt) (B := (k : Nat)) (evalInt_int 0)
    (procStepDelta2_inc _ "j") (fun v _ => guard_canon .lt (fun _ => rfl) hi v)
    (canonCount_lt_one (n := k) (by rw [int32_zero]; omega) ⟨by omega, by omega⟩)
  rwa [int32_zero] at h

/-! ## The legacy instantiation at the endpoint points

`forValues2` runs the iteration `forValuesFuel2` at the fuel master's `forFuel2` derives from the
header (`c64ebdac`). Before that it used a fixed fuel of 128, which the last two guards replay:
from 127 trips on, the old cap timed out (and `instStmt2` built a loud node). -/

private def envN (n : Nat) : IEnv := { vals := [("N", (n : Int))] }

#guard [0, 1, 126, 127, 200].all fun n =>
  forValues2 (envN n) "i" (.int 0) (.binary .slt iR nR) (.unary .inc iR) ==
    .ok (TripSchema.arith 0 1 n).toList
#guard forValuesFuel2 (envN 126) "i" (.int 0) (.binary .slt iR nR) (.unary .inc iR) 128 ==
  .ok (TripSchema.arith 0 1 126).toList
#guard forValuesFuel2 (envN 127) "i" (.int 0) (.binary .slt iR nR) (.unary .inc iR) 128 == .timeout

/-- The bridge at 200 trips: the instantiation's iteration IS the schema's list. -/
theorem legacy_200 :
    forValues2 (envN 200) "i" (.int 0) (.binary Cmp.lt.op iR nR) (.unary .inc iR) =
      .ok (TripSchema.arith 0 1 200).toList := by
  rw [TripSchema.toList_arith_one]
  exact forValues2_upto (fun v => nR_int (N := 200) rfl "i" (by decide) v)
    (fun v => nR_val (N := 200) rfl "i" (by decide) v) rfl

/-! ## The computed schema against the legacy unrolling, at concrete points (`#guard`)

`headerSchema` (fuel-free, closed form) and the legacy `forValues2` (fuel derived by `forFuel2`) on every
envelope header at the endpoint points: the same trip lists. -/

/-- The environment at `N`, `C`, as `instantiate2` binds INT parameters. -/
private def envNC (n c : Nat) : IEnv := { vals := [("N", (n : Int)), ("C", (c : Int))] }

/-- New meaning vs legacy unrolling, on the `k`-th envelope header at `N = n`, `C = c`. -/
private def agreeAt (k n c : Nat) : Bool :=
  match (loop_edges.pdesign.processes.map hdr?)[k]? with
  | some (some (it, i, cnd, st)) =>
      match headerSchema (envNC n c) it i cnd st, forValues2 (envNC n c) it i cnd st with
      | .ok S, .ok l => S.toList == l
      | _, _ => false
  | _ => false

#guard (List.range 7).all fun k =>
  [(0, 3), (1, 3), (2, 1), (5, 2), (126, 3), (127, 3), (200, 7), (200, 200)].all fun (n, c) =>
    agreeAt k n c

-- The shadowing nest's inner header, under each outer binding of `i`: the inner `i` wins.
#guard [0, 1, 2].all fun v =>
  match headerSchema ((envNC 5 3).bindVal "i" v) "i" (.int 0) (.binary .slt iR nR) (.unary .inc iR) with
  | .ok S => S.toList == [0, 1, 2, 3, 4]
  | _ => false

-- The triangular nest's inner header (hand header), under the outer binding `i = 4`: `0..3`.
#guard match headerSchema ((envNC 5 3).bindVal "i" 4) "j" (.int 0)
    (.binary .slt (.genvarRef "j") iR) (.unary .inc (.genvarRef "j")) with
  | .ok S => S.toList == [0, 1, 2, 3]
  | _ => false

-- Refused, loudly: a header whose 32-bit iterator wraps (`i <= 2147483647` never exits in a
-- simulator), one that runs away from its bound, one whose bound reads its own iterator.
#guard headerSchema {} "i" (.int 0) (.binary .sle iR (.int 2147483647)) (.unary .inc iR) matches .error _
#guard headerSchema {} "i" (.int 0) (.binary .slt iR (.int 10)) (.unary .dec iR) matches .error _
#guard headerSchema {} "i" (.int 0) (.binary .slt iR iR) (.unary .inc iR) matches .error _
-- … while the legacy unbounded reading unrolls the wrapping one (fuel permitting): the recorded
-- `int32` restriction, now visible.
#guard (forValues2 {} "i" (.int 2147483640) (.binary .sle iR (.int 2147483647)) (.unary .inc iR))
  matches .ok _

/-! ## The nested dependent bound, as the extractor emits it today: refused

MEASURED (2026-11-02, `python3.12 extractors/sv/extract.py --top loop_tri …` on
`always_comb begin y = '0; for (int i = 0; i < N; i++) for (int j = 0; j < i; j++) y[i*8+j] = a[j]; end`):
the outer loop is retained (`symbolic_for_parameter`), the inner one is not — its bound reads the
outer iterator, not a parameter — and the envelope carries a `LocalDecl` for `j` and a loud
`Unsupported` `ForLoopStatement` in its place. `load_design_sv2` then refuses the envelope
outright: `unknown statement kind "LocalDecl"`. So `tri_agrees` above reads a hand-written header;
the extractor-side retention of a dependent inner bound is an extractor item (EXECUTION-PLAN §5,
"retain-mode twins"), not a representation problem of the schema. -/

/-! ## Axioms -/

#pin_axioms headers shadow_inner nR_int nR_val cR_int cR_val lt_agrees lt_at le_agrees desc_agrees
  step_agrees neg_agrees shadow_agrees pshadow_agrees tri_agrees legacy_200

end Examples.«system-verilog».loop_edges.schema
