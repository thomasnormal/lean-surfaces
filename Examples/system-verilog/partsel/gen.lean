import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2

/-!
# `partsel` — indexed part-selects with parameter and genvar bases

`partsel.sv` exercises IEEE 1800-2023 §11.5.1's indexed part-selects
`x[b +: w]` / `x[b -: w]` (and a range select `x[hi:lo]`) whose base and
bounds are ELABORATION-TIME constant expressions over the parameters `N`,
`W` and the genvar `i` — as continuous-assign targets and as reads — plus
selects that leave the vector at some parameter points (out-of-range bits
read x; writes to them do nothing, both msb- and lsb-side) and selects whose
base is a RUN-TIME signal (`v[sel +: 4]`, `a[sel*W +: W]`). The extractor
keeps every one of them symbolic (`ArraySel` nodes; nothing folded at the
default parameters), and `Param2.lean` resolves them at each instantiation:
`arrayPartGeom`/`arrayPartTarget`/`arrayPartRead` for constant bases,
`dynPartPlan`/`dynPartRead` for run-time ones.

This file pins the lane-reversal generate block of the envelope and proves,
for EVERY `N` and every `W ≥ 1` — symbolically, nothing unrolled — that it
instantiates to the family of `W`-bit window copies

```
for i < N:   rev_up[i*W +: W]       = a[(N-1-i)*W +: W]   ↦  slice copy
             rev_dn[(i+1)*W-1 -: W] = a[(N-i)*W-1 -: W]   ↦  the same copy
```

(`partsel_rev_expand` at any environment carrying `N`, `W` and the three
vectors' evaluated geometry `[N*W-1:0]`; `partsel_rev_instantiated` at the
environment `instantiate2` builds). Route: `Gen2`'s
`arrayPartTarget_up_desc0`/`…_down_desc0` and
`fitExpr2_arrayPart_up_desc0`/`…_down_desc0` per cell, and
`GenItem.expand2_genFor_ascending_processes` for the loop.

Differential rows (`harness/sv/cases2.json`): `partsel` (N=4, W=3),
`partsel_n2_w5`, `partsel_n6_w2`, `partsel_n5_w1`, `partsel_n1_w4`, every
one `run2` = Icarus 12.0 on every printed signal, including the
out-of-range reads and writes and x/z run-time bases.
-/

namespace Examples.«system-verilog».partsel.gen

open LeanModels.Sv

load_design_sv2 partsel from "Examples/system-verilog/partsel/partsel.sv.json"

/-! ## The envelope's lane templates (pinned by `rfl`) -/

/-- `rev_up[i*W +: W] = a[(N-1-i)*W +: W]` — target and read are both
`ArraySel` paths with symbolic labels. -/
def revUpT : PProcess :=
  .assignL (.arrayPart "rev_up" [] .up (.binary .mul (.genvarRef "i") (.paramRef "W" none))
      (.paramRef "W" none))
    (.arrayPart "a" [] .up
      (.binary .mul (.binary (.m0 .sub) (.binary (.m0 .sub) (.paramRef "N" none) (.int 1))
        (.genvarRef "i")) (.paramRef "W" none))
      (.paramRef "W" none))

/-- `rev_dn[(i+1)*W-1 -: W] = a[(N-i)*W-1 -: W]` — the same copy with `-:`. -/
def revDnT : PProcess :=
  .assignL (.arrayPart "rev_dn" [] .down
      (.binary (.m0 .sub) (.binary .mul (.binary (.m0 .add) (.genvarRef "i") (.int 1))
        (.paramRef "W" none)) (.int 1))
      (.paramRef "W" none))
    (.arrayPart "a" [] .down
      (.binary (.m0 .sub) (.binary .mul (.binary (.m0 .sub) (.paramRef "N" none) (.genvarRef "i"))
        (.paramRef "W" none)) (.int 1))
      (.paramRef "W" none))

/-- The generate block `for (i = 0; i < N; i++) begin : g_rev … end`. -/
def revGen : GenItem :=
  .genFor (some "g_rev") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 4) ([revUpT, revDnT].map GenItem.process)

theorem partsel_generates : partsel.pdesign.generates = [revGen] := rfl

/-- `a`, `rev_up` and `rev_dn` are declared `[N*W-1:0]`. -/
def laneDims : List PDim :=
  [⟨.binary (.m0 .sub) (.binary .mul (.paramRef "N" none) (.paramRef "W" none)) (.int 1), .int 0⟩]

/-- … evaluated at `(N, W)`: the geometry-table entry. -/
def laneGeom (N W : Nat) : List (Int × Int) := [((N : Int) * W - 1, 0)]

theorem partsel_a_dims : partsel.pdesign.packedDims.lookup "a" = some laneDims := rfl
theorem partsel_rev_up_dims : partsel.pdesign.packedDims.lookup "rev_up" = some laneDims := rfl
theorem partsel_rev_dn_dims : partsel.pdesign.packedDims.lookup "rev_dn" = some laneDims := rfl

/-! ## One lane -/

/-- Lane `i`'s two cells: both copy `a`'s lane `N-1-i` (the `W`-bit window
at `(N-1-i)*W`) into lane `i` (the window at `i*W`). -/
def revCells (N W i : Nat) : List Process2 :=
  [.assign (.slice "rev_up" (i * W) W) (.slice (.ident "a") ((N - 1 - i) * W) W),
   .assign (.slice "rev_dn" (i * W) W) (.slice (.ident "a") ((N - 1 - i) * W) W)]

/-- The lane arithmetic both cells need: lane `i` and lane `N-1-i` end at
or below the vector's `N*W` bits. -/
private theorem lane_bounds (N W i : Nat) (hi : i < N) :
    ((i : Int) + 1) * W ≤ (N : Int) * W ∧ ((N - 1 - i : Nat) : Int) * W + W ≤ (N : Int) * W := by
  have h1 : (i + 1) * W ≤ N * W := Nat.mul_le_mul_right W hi
  have h2 : (N - 1 - i + 1) * W ≤ N * W := Nat.mul_le_mul_right W (by omega)
  refine ⟨by exact_mod_cast h1, ?_⟩
  have h2' : (((N - 1 - i + 1) * W : Nat) : Int) ≤ ((N * W : Nat) : Int) := by exact_mod_cast h2
  push_cast at h2'
  rw [Int.add_mul, Int.one_mul] at h2'
  exact h2'

/-- **The `+:` template at an in-range lane** (any environment binding `N`,
`W` and the two vectors' evaluated geometry). -/
theorem revUp_inst (env : IEnv) (elems : List (String × Nat)) (N W i : Nat)
    (hNv : env.vals.lookup "N" = some (N : Int)) (hWv : env.vals.lookup "W" = some (W : Int))
    (hdy : env.dims.lookup "rev_up" = some (laneGeom N W))
    (hda : env.dims.lookup "a" = some (laneGeom N W)) (hW : 0 < W) (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems revUpT =
      .assign (.slice "rev_up" (i * W) W) (.slice (.ident "a") ((N - 1 - i) * W) W) := by
  have hNb : (env.bindVal "i" i).vals.lookup "N" = some (N : Int) := by simp [List.lookup, hNv]
  have hWb : (env.bindVal "i" i).vals.lookup "W" = some (W : Int) := by simp [List.lookup, hWv]
  have hib : (env.bindVal "i" i).vals.lookup "i" = some (i : Int) := by simp
  obtain ⟨hrow, hrow2⟩ := lane_bounds N W i hi
  have hiW : (0 : Int) ≤ (i : Int) * W := Int.mul_nonneg (by omega) (by omega)
  have hsub : (N : Int) - 1 - i = ((N - 1 - i : Nat) : Int) := by omega
  have iN := isInt_paramRef_of hNb
  have iW := isInt_paramRef_of hWb
  have hevt := evalInt_mul_of rfl iW (evalInt_genvarRef_of hib) (evalInt_paramRef_of hWb)
  have hevs := evalInt_mul_of (isInt_binary_of rfl (isInt_binary_of rfl iN rfl) rfl) iW
    (evalInt_sub_of (isInt_binary_of rfl iN rfl) rfl
      (evalInt_sub_of iN rfl (evalInt_paramRef_of hNb) (evalInt_int 1))
      (evalInt_genvarRef_of hib)) (evalInt_paramRef_of hWb)
  rw [hsub] at hevs
  rw [Int.add_mul, Int.one_mul] at hrow
  have hT := arrayPartTarget_up_desc0 (arrayDims_of (by simpa [laneGeom] using hdy)) (by omega)
    hevt (evalInt_paramRef_of hWb) (by omega) (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hR := fitExpr2_arrayPart_up_desc0 (elems := elems)
    (arrayDims_of (by simpa [laneGeom] using hda)) (by omega) hevs (evalInt_paramRef_of hWb)
    (by omega) (Int.mul_nonneg (by omega) (by omega)) (by omega)
  rw [revUpT, instProcess2_assignL _ (by rw [instLhs2_arrayPart]; exact hT), hR]
  simp only [← Int.natCast_mul, Int.toNat_natCast]

/-- **The `-:` template at an in-range lane**: the same window copy. -/
theorem revDn_inst (env : IEnv) (elems : List (String × Nat)) (N W i : Nat)
    (hNv : env.vals.lookup "N" = some (N : Int)) (hWv : env.vals.lookup "W" = some (W : Int))
    (hdy : env.dims.lookup "rev_dn" = some (laneGeom N W))
    (hda : env.dims.lookup "a" = some (laneGeom N W)) (hW : 0 < W) (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems revDnT =
      .assign (.slice "rev_dn" (i * W) W) (.slice (.ident "a") ((N - 1 - i) * W) W) := by
  have hNb : (env.bindVal "i" i).vals.lookup "N" = some (N : Int) := by simp [List.lookup, hNv]
  have hWb : (env.bindVal "i" i).vals.lookup "W" = some (W : Int) := by simp [List.lookup, hWv]
  have hib : (env.bindVal "i" i).vals.lookup "i" = some (i : Int) := by simp
  obtain ⟨hrow, hrow2⟩ := lane_bounds N W i hi
  have hsub : (N : Int) - i = ((N - 1 - i : Nat) : Int) + 1 := by omega
  have hiW : (0 : Int) ≤ (i : Int) * W := Int.mul_nonneg (by omega) (by omega)
  have hjW : (0 : Int) ≤ ((N - 1 - i : Nat) : Int) * W := Int.mul_nonneg (by omega) (by omega)
  have iN := isInt_paramRef_of hNb
  have iW := isInt_paramRef_of hWb
  have hevt := evalInt_sub_of (isInt_binary_of rfl rfl iW) rfl
    (evalInt_mul_of rfl iW (evalInt_add_of rfl rfl (evalInt_genvarRef_of hib)
      (evalInt_int 1)) (evalInt_paramRef_of hWb)) (evalInt_int 1)
  have hevs := evalInt_sub_of (isInt_binary_of rfl (isInt_binary_of rfl iN rfl) iW) rfl
    (evalInt_mul_of (isInt_binary_of rfl iN rfl) iW (evalInt_sub_of iN rfl
      (evalInt_paramRef_of hNb) (evalInt_genvarRef_of hib)) (evalInt_paramRef_of hWb))
    (evalInt_int 1)
  rw [hsub] at hevs
  rw [Int.add_mul, Int.one_mul] at hevt hevs hrow
  have hT := arrayPartTarget_down_desc0 (arrayDims_of (by simpa [laneGeom] using hdy))
    (by omega) hevt (evalInt_paramRef_of hWb) (by omega) (by omega) (by omega)
  have hR := fitExpr2_arrayPart_down_desc0 (elems := elems)
    (arrayDims_of (by simpa [laneGeom] using hda)) (by omega) hevs (evalInt_paramRef_of hWb)
    (by omega) (by omega) (by omega)
  rw [revDnT, instProcess2_assignL _ (by rw [instLhs2_arrayPart]; exact hT), hR]
  have e1 : (i : Int) * W + W - 1 - W + 1 = ((i * W : Nat) : Int) := by push_cast; omega
  have e2 : ((N - 1 - i : Nat) : Int) * W + W - 1 - W + 1 = (((N - 1 - i) * W : Nat) : Int) := by
    push_cast; omega
  rw [e1, e2]
  simp only [Int.toNat_natCast]

/-! ## The whole block, for every `N` and `W ≥ 1` -/

/-- The loop bound `N` survives the genvar binding. -/
private theorem n_bound (env : IEnv) (N : Nat) (h : env.vals.lookup "N" = some (N : Int))
    (i : Int) : evalInt (env.bindVal "i" i) (.paramRef "N" none) = .ok (N : Int) :=
  evalInt_paramRef_of (by simp [List.lookup, h])

/-- … and stays in the INT class (bound in `vals`). -/
private theorem n_bound_int (env : IEnv) (N : Nat) (h : env.vals.lookup "N" = some (N : Int))
    (i : Int) : (PExpr.paramRef "N" none).isInt (env.bindVal "i" i) = true :=
  isInt_paramRef_of (v := (N : Int)) (by simp [List.lookup, h])

/-- **The lane-reversal block, for every `N` and every `W ≥ 1`** (any
environment binding `N`, `W` and the evaluated geometry of `a`, `rev_up`,
`rev_dn`; any fuel past `N`): lane by lane, the two `W`-bit window copies. -/
theorem partsel_rev_expand (env : IEnv) (elems : List (String × Nat)) (N W F : Nat)
    (hW : 0 < W) (hF : N < F)
    (hNv : env.vals.lookup "N" = some (N : Int)) (hWv : env.vals.lookup "W" = some (W : Int))
    (hda : env.dims.lookup "a" = some (laneGeom N W))
    (hdu : env.dims.lookup "rev_up" = some (laneGeom N W))
    (hdd : env.dims.lookup "rev_dn" = some (laneGeom N W)) :
    revGen.expand2 env elems F = .ok ((List.range N).flatMap (revCells N W)) := by
  rw [revGen, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (n_bound_int env N hNv) (n_bound env N hNv) (by simpa using hF)]
  simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
    List.map_nil]
  congr 1
  simp only [List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [revUp_inst env elems N W i hNv hWv hdu hda hW (List.mem_range.mp hi),
    revDn_inst env elems N W i hNv hWv hdd hda hW (List.mem_range.mp hi)]
  rfl

/-! ## At the environment `instantiate2` builds -/

/-- The declaration scope of `partsel` at `(N, W)`: both parameters bound,
their declared `int` types 32 bits. -/
def psScope (N W : Int) : IEnv :=
  { vals := [("N", N), ("W", W)], pwidths := [("N", 32), ("W", 32)] }

/-- The parameter environment of `partsel` (by `rfl`): the declaration scope
plus the geometry table evaluated in it. -/
def psEnv (N W : Int) : IEnv :=
  { psScope N W with dims := dimTable (psScope N W) partsel.pdesign.decls }

theorem partsel_paramEnv (N W : Int) : partsel.pdesign.paramEnv2 [N, W] = .ok (psEnv N W) := rfl

/-- `[N*W-1:0]` evaluated in the declaration scope, at any width table. -/
private theorem lane_evalDims (N W : Nat) (ws : List (String × Nat)) :
    evalDims { psScope N W with widths := ws } laneDims = .ok (laneGeom N W) :=
  evalDims_cons_of
    (evalInt_sub_of (isInt_binary_of rfl (isInt_paramRef_of (v := (N : Int)) (by simp [psScope]))
        (isInt_paramRef_of (v := (W : Int)) (by simp [psScope, List.lookup]))) rfl
      (evalInt_mul_of (isInt_paramRef_of (v := (N : Int)) (by simp [psScope]))
        (isInt_paramRef_of (v := (W : Int)) (by simp [psScope, List.lookup]))
        (evalInt_paramRef_of (by simp [psScope]))
        (evalInt_paramRef_of (by simp [psScope, List.lookup]))) (evalInt_int 1))
    (evalInt_int 0) evalDims_nil

/-- The geometry table's entries for the three lane vectors: `[N*W-1:0]`. -/
theorem psEnv_a (N W : Nat) : (psEnv N W).dims.lookup "a" = some (laneGeom N W) :=
  PDesign.dimTable_lookup_of partsel_a_dims (lane_evalDims N W)

theorem psEnv_rev_up (N W : Nat) : (psEnv N W).dims.lookup "rev_up" = some (laneGeom N W) :=
  PDesign.dimTable_lookup_of partsel_rev_up_dims (lane_evalDims N W)

theorem psEnv_rev_dn (N W : Nat) : (psEnv N W).dims.lookup "rev_dn" = some (laneGeom N W) :=
  PDesign.dimTable_lookup_of partsel_rev_dn_dims (lane_evalDims N W)

/-- **The lane-reversal block of the instantiated design, for every `N` and
every `W ≥ 1`** — at the declaration environment of ANY declaration list and
element-width table, at the surface fuel `instantiateD2` uses. -/
theorem partsel_rev_instantiated (N W : Nat) (hW : 1 ≤ W) (decls : List Decl)
    (elems : List (String × Nat)) :
    revGen.expand2 ((psEnv N W).withDecls decls) elems
        (PDesign.surfaceFuel [(N : Int), (W : Int)]) =
      .ok ((List.range N).flatMap (revCells N W)) := by
  have hF : N < PDesign.surfaceFuel [(N : Int), (W : Int)] := by
    have := Nat.le_mul_self (N + W + 2)
    simp [PDesign.surfaceFuel]
    omega
  exact partsel_rev_expand _ elems N W _ hW hF (by simp [psEnv, psScope])
    (by simp [psEnv, psScope, List.lookup])
    (by simpa using psEnv_a N W) (by simpa using psEnv_rev_up N W)
    (by simpa using psEnv_rev_dn N W)

#print axioms partsel_rev_expand
#print axioms partsel_rev_instantiated

/-! ## Concrete agreement (non-vacuity)

Nine static processes then two cells per lane; nothing loud at any of the
differential rows' parameter points. -/

#guard (partsel.sem 4 3).processes.size == 9 + 2 * 4
#guard [(4, 3), (2, 5), (6, 2), (5, 1), (1, 4)].all fun (n, w) => !(partsel.sem n w).hasUnsupported

/-- Process `k` of `partsel` at `(N, W)` as a continuous assign, if it is one. -/
private def assignAt (N W k : Nat) : Option (Lhs2 × Expr2) :=
  match (partsel.sem N W).processes[k]? with
  | some (.assign l e) => some (l, e)
  | _ => none

/-- The blocking target of the second statement of always_comb process `k`. -/
private def combTargetAt (N W k : Nat) : Option Lhs2 :=
  match (partsel.sem N W).processes[k]? with
  | some (.alwaysComb (.block body)) =>
      match (body[1]? : Option Stmt2) with
      | some (.blockingAssign l _) => some l
      | _ => none
  | _ => none

-- `top = a[N*W-1 -: N]` at (4, 3): the 4-bit window at 8.
#guard assignAt 4 3 0 == some (.ident "top", .slice (.ident "a") 8 4)
-- `ov_lo = a[W-2 -: 4]` at W = 3: two in-range bits over two x bits.
#guard assignAt 4 3 2 == some (.ident "ov_lo",
  .concat #[.slice (.ident "a") 0 2, .lit (LVec.xVec 2)])
-- `dyn_lane = a[sel*W +: W]`: the run-time base keeps its 32-bit product,
-- read as a two's-complement `int` (what Icarus and Yosys do with a 32-bit
-- index: `dynPartRead32`).
#guard assignAt 4 3 6 == some (.ident "dyn_lane",
  dynPartRead32 "a" 3 0 12 (.binary .mul (.resize 32 (.ident "sel")) (.lit (LVec.ofInt 32 3))))
-- `w_hi[N+3 +: 4] = b` at N = 4: the msb overhang clips to bit 7;
-- `w_lo[N-3 -: 4] = b` at N = 4: the lsb overhang is a concat whose low
-- leaf is the sink past bit 7 (writes nothing).
#guard combTargetAt 4 3 7 == some (.slice "w_hi" 7 1)
#guard combTargetAt 4 3 8 == some (.concat [.slice "w_lo" 0 2, .slice "w_lo" 8 2])
-- At N = 6 the lsb-side write is in range; at N = 2 it is fully below (a no-op).
#guard combTargetAt 6 2 8 == some (.slice "w_lo" 0 4)
#guard combTargetAt 2 5 8 == some (.slice "w_lo" 0 0)

end Examples.«system-verilog».partsel.gen
