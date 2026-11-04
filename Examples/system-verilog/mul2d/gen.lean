import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# `mul2d` — nested packed-array selects through the Design2 generate layer

`mul2d.sv` is an `N×N → 2N` array multiplier written the natural way: its
partial products, row sums, carries and propagates live in 2-D packed arrays
(`logic [N-1:0][N-1:0] pp;`, `logic [N-1:0][N:0] s, c;`) and every cell is a
nested select (`assign pp[i][j] = a[j] & b[i];`,
`s[i-1][j+1] ^ pp[i][j]`, `s[N-1][N:1]`). The extractor emits each select
chain as ONE `ArraySel` node with the raw declared labels, and
`Param2.lean` lowers it against the declaration's symbolic dimensions to a
flat window of the declared vector.

This file pins the envelope's templates and proves, for EVERY `N ≥ 1` —
symbolically, nothing unrolled — the whole instantiated process list
(`mul2d_processes`: four static assigns, the partial products, rows
`1 … N-1`, the low output bits). In particular the partial-product block
instantiates to the `i`-major family of 1-bit cells

```
for i < N, j < N:   pp[i*N + j] = a[j] & b[i]
```

as `Process2.assign (.slice "pp" (i*N+j) 1) (.binary .and (.slice (.ident
"a") j 1) (.slice (.ident "b") i 1))` — the same flat `slice` vocabulary
the ripple-carry acceptance (`ripple_add/gen.lean`) feeds to the comb settle
theorem. Route: `GenItem.expand2_genFor_ascending_flatMap` for the two
loops (the range facts `i, j < N` survive into each cell, which is what the
per-dimension range check of a nested select needs), and the select-path
lemmas of `Gen2.lean` (`arrayDims_of`, `walkIndices_desc0_cons`,
`arrayElemTarget_of_inRange`) for the cell. `mul2d_pp_expand` is stated for
any environment carrying the parameter and `pp`'s EVALUATED geometry
`[N-1:0][N-1:0]` (`ppGeom N` — the declaration-scope table `instantiate2`
builds once, before any genvar is bound); `mul2d_pp_instantiated`
discharges those at the environment `instantiate2` builds, at every
`N ≥ 1` (`PDesign.dimTable_lookup_of`).

The envelope is not a tracked build input (as for `ripple_add`): force a
rebuild of this module after re-extracting `mul2d.sv.json`.
-/

namespace Examples.«system-verilog».mul2d.gen

open LeanModels.Sv

load_design_sv2 mul2d from "Examples/system-verilog/mul2d/mul2d.sv.json"

/-! ## The envelope's shape (pinned by `rfl`) -/

/-- The symbolic bound `N-1`. -/
def nM1 : PExpr := .binary (.m0 .sub) (.paramRef "N" none) (.int 1)

/-- The partial-product template `assign pp[i][j] = a[j] & b[i];` — the
target is ONE select path over `pp` with the genvar labels `[i, j]`. -/
def ppT : PProcess :=
  .assignL (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"])
    (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "j"))
      (.bitSel (.ident "b") (.genvarRef "i")))

/-- The partial-product generate block: `for (i …) for (j …) <ppT>`. -/
def ppGen : GenItem :=
  .genFor (some "g_pp") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 4)
    [.genFor (some "g_pp_j") "j" (.int 0) (.binary .slt (.genvarRef "j") (.paramRef "N" none))
      (.unary .inc (.genvarRef "j")) (some 4) ([ppT].map GenItem.process)]

/-- `pp`'s declared dimensions `[N-1:0][N-1:0]`, symbolic. -/
def ppDims : List PDim := [⟨nM1, .int 0⟩, ⟨nM1, .int 0⟩]

/-- … evaluated at `N`: the geometry-table entry (`(msb, lsb)` labels). -/
def ppGeom (N : Nat) : List (Int × Int) := [((N : Int) - 1, 0), ((N : Int) - 1, 0)]

/-- The first generate item of the envelope is the partial-product block. -/
theorem mul2d_pp_source : mul2d.pdesign.generates.head? = some ppGen := rfl

/-- The source of the geometry table records `pp` as `[N-1:0][N-1:0]`. -/
theorem mul2d_pp_dims : mul2d.pdesign.packedDims.lookup "pp" = some ppDims := rfl

/-! ## The instantiated cell -/

/-- Cell `(i, j)`: `pp[i*N + j] = a[j] & b[i]` on the flat `N*N`-bit vector. -/
def ppCell (N i j : Nat) : Process2 :=
  .assign (.slice "pp" (i * N + j) 1)
    (.binary .and (.slice (.ident "a") j 1) (.slice (.ident "b") i 1))

/-- The nested select `pp[i][j]` over `[N-1:0][N-1:0]` with in-range genvar
labels is the 1-bit window at `i*N + j`. -/
theorem pp_window (E : IEnv) (N i j : Nat) (hN : 1 ≤ N) (hi : i < N) (hj : j < N)
    (hiv : E.vals.lookup "i" = some (i : Int))
    (hjv : E.vals.lookup "j" = some (j : Int)) (hd : E.dims.lookup "pp" = some (ppGeom N)) :
    arrayElemWindow E "pp" [.genvarRef "i", .genvarRef "j"] =
      .ok (((i * N + j : Nat) : Int), 1, true) := by
  have hm0 : (0 : Int) ≤ (N : Int) - 1 := by omega
  have hdims := arrayDims_of hd
  have hwj := walkIndices_desc0_cons (ds := []) hm0 (evalInt_genvarRef_of hjv)
    (by omega) (by omega) (walkIndices_nil (env := E) [])
  have hwi := walkIndices_desc0_cons hm0 (evalInt_genvarRef_of hiv) (by omega) (by omega) hwj
  rw [arrayElemWindow_of hdims hwi]
  have hc : dimsStride [((N : Int) - 1, 0)] = N := by
    simp only [dimsStride, dimCount]
    omega
  simp [hc]

/-- **The partial-product template at in-range genvars** (any environment
binding `N`, `pp`'s dimensions, and 1-bit element widths for `a`, `b`). -/
theorem pp_inst (env : IEnv) (elems : List (String × Nat)) (N i j : Nat) (hN : 1 ≤ N)
    (hi : i < N) (hj : j < N) (hd : env.dims.lookup "pp" = some (ppGeom N))
    (ha : elems.lookup "a" = some 1) (hb : elems.lookup "b" = some 1) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems ppT = ppCell N i j := by
  have hw := pp_window ((env.bindVal "i" i).bindVal "j" j) N i j hN hi hj
    (by simp [IEnv.bindVal, List.lookup])
    (by simp [IEnv.bindVal]) (by simpa using hd)
  have hiv : evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])
  have hjv : evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "j") = .ok (j : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  rw [ppT, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hw]),
    fitExpr2_binary, instExpr2_and, fitExpr2_bitSel_ident ha hjv (by omega),
    fitExpr2_bitSel_ident hb hiv (by omega)]
  have hidx : ((i : Int) * (N : Int) + (j : Int)).toNat = i * N + j := by
    rw [← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast]
  simp [ppCell, hidx]

/-- The loop bound `N` survives genvar bindings (genvars never shadow `N`). -/
private theorem n_bound (env : IEnv) (N : Nat) (h : env.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (i : Int) :
    evalInt (env.bindVal g i) (.paramRef "N" none) = .ok (N : Int) := by
  apply evalInt_paramRef_of
  simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)]

/-- … and `N` stays in the INT class there (`PExpr.isInt`: bound in `vals`). -/
private theorem n_bound_int (env : IEnv) (N : Nat) (h : env.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (i : Int) :
    (PExpr.paramRef "N" none).isInt (env.bindVal g i) = true := by
  exact isInt_paramRef_of (v := (N : Int))
    (by simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)])

/-- **The partial-product generate block, for every `N ≥ 1`**: the
`i`-major family of 1-bit cells `pp[i*N + j] = a[j] & b[i]`. -/
theorem mul2d_pp_expand (env : IEnv) (elems : List (String × Nat)) (N F : Nat) (hN : 1 ≤ N)
    (hF : N < F) (hNv : env.vals.lookup "N" = some (N : Int))
    (hd : env.dims.lookup "pp" = some (ppGeom N))
    (ha : elems.lookup "a" = some 1) (hb : elems.lookup "b" = some 1) :
    ppGen.expand2 env elems F =
      .ok ((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j) := by
  rw [ppGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [ppT].map (instProcess2 ((env.bindVal "i" v).bindVal "j" w) elems))
      (evalInt_int 0) (n_bound_int env N hNv "i" (by decide)) (n_bound env N hNv "i" (by decide)) (by simpa using hF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
      List.map_nil, Gen2.flatMap_singleton_map]
    congr 1
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply List.map_congr_left
    intro j hj
    exact pp_inst env elems N i j hN (List.mem_range.mp hi) (List.mem_range.mp hj) hd ha hb
  · intro v _ _
    apply expandList2_singleton_ok
    rw [GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (n_bound_int _ N (by simp [IEnv.bindVal, List.lookup, hNv]) "j" (by decide))
      (n_bound _ N (by simp [IEnv.bindVal, List.lookup, hNv]) "j" (by decide)) (by simpa using hF)]
    simp

/-! ## At the environment `instantiate2` builds -/

/-- The declaration scope of `mul2d` at `N`: `N` bound, its declared `int`
type 32 bits. -/
def mulScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment of `mul2d` at `N` (by `rfl`): the declaration
scope plus the geometry table evaluated in it. -/
def mulEnv (N : Int) : IEnv := { mulScope N with dims := dimTable (mulScope N) mul2d.pdesign.decls }

theorem mul2d_paramEnv (N : Int) : mul2d.pdesign.paramEnv2 [N] = .ok (mulEnv N) := rfl

/-- `N - 1` in the declaration scope, at any declared-width table. -/
theorem mulScope_nM1 (N : Int) (ws : List (String × Nat)) :
    evalInt { mulScope N with widths := ws } nM1 = .ok (N - 1) :=
  evalInt_sub_of (by simp [mulScope]) rfl (evalInt_paramRef_of (by simp [mulScope])) (evalInt_int 1)

/-- The geometry table's `pp` entry: `[N-1:0][N-1:0]` evaluated. -/
theorem mulEnv_pp (N : Nat) : (mulEnv N).dims.lookup "pp" = some (ppGeom N) :=
  PDesign.dimTable_lookup_of mul2d_pp_dims fun ws =>
    evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0)
      (evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0) evalDims_nil)

/-- **The partial-product block of the instantiated multiplier, for every
`N ≥ 1`** — at the declaration environment of ANY declaration list and any
element-width table giving the 1-D ports `a`, `b` 1-bit elements (what
`buildElems` computes for them), at the surface fuel. -/
theorem mul2d_pp_instantiated (N : Nat) (hN : 1 ≤ N) (decls : List Decl)
    (elems : List (String × Nat)) (ha : elems.lookup "a" = some 1)
    (hb : elems.lookup "b" = some 1) :
    ppGen.expand2 ((mulEnv N).withDecls decls) elems (PDesign.surfaceFuel [(N : Int)]) =
      .ok ((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j) :=
  mul2d_pp_expand _ elems N _ hN
    (by
      have := Nat.le_mul_self (N + 2)
      simp [PDesign.surfaceFuel]
      omega)
    (by simp [mulEnv, mulScope]) (by simpa using mulEnv_pp N) ha hb

/-! ## The whole instantiated multiplier

The same route over the remaining templates — the four static assigns, the
row block (`c[i][0]`, then `t/s/c` per bit, then `s[i][N]`) and the output
block — gives the complete process list for every `N ≥ 1`
(`mul2d_processes`). Reads of `s[i-1][j+1]` (the previous row's sum,
shifted one bit) are windows of the `[N-1:0][N:0]` array at
`(i-1)*(N+1) + (j+1)`; the label arithmetic is discharged once per
template by `win_sq`/`win_rect`. -/

/-- `t`, `pp`: `[N-1:0][N-1:0]`; `s`, `c`: `[N-1:0][N:0]`. -/
def rectDims : List PDim := [⟨nM1, .int 0⟩, ⟨.paramRef "N" none, .int 0⟩]

theorem mul2d_t_dims : mul2d.pdesign.packedDims.lookup "t" = some ppDims := rfl
theorem mul2d_s_dims : mul2d.pdesign.packedDims.lookup "s" = some rectDims := rfl
theorem mul2d_c_dims : mul2d.pdesign.packedDims.lookup "c" = some rectDims := rfl

/-- `[N-1:0][N:0]` evaluated at `N`. -/
def rectGeom (N : Nat) : List (Int × Int) := [((N : Int) - 1, 0), ((N : Int), 0)]

/-- The geometry table's `t`/`s`/`c` entries. -/
theorem mulEnv_t (N : Nat) : (mulEnv N).dims.lookup "t" = some (ppGeom N) :=
  PDesign.dimTable_lookup_of mul2d_t_dims fun ws =>
    evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0)
      (evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0) evalDims_nil)

private theorem rect_eval (N : Nat) (ws : List (String × Nat)) :
    evalDims { mulScope N with widths := ws } rectDims = .ok (rectGeom N) :=
  evalDims_cons_of (d := ⟨nM1, .int 0⟩) (mulScope_nM1 N ws) (evalInt_int 0)
    (evalDims_cons_of (d := ⟨.paramRef "N" none, .int 0⟩)
      (evalInt_paramRef_of (by simp [mulScope])) (evalInt_int 0) evalDims_nil)

theorem mulEnv_s (N : Nat) : (mulEnv N).dims.lookup "s" = some (rectGeom N) :=
  PDesign.dimTable_lookup_of mul2d_s_dims (rect_eval N)

theorem mulEnv_c (N : Nat) : (mulEnv N).dims.lookup "c" = some (rectGeom N) :=
  PDesign.dimTable_lookup_of mul2d_c_dims (rect_eval N)

/-- `2*N-1`, the msb label of `p`. -/
def pMsb : PExpr := .binary (.m0 .sub) (.binary .mul (.int 2) (.paramRef "N" none)) (.int 1)

/-- `p`: `[2*N-1:0]`. -/
theorem mul2d_p_dims : mul2d.pdesign.packedDims.lookup "p" = some [⟨pMsb, .int 0⟩] := rfl

/-- `2*N-1` at `N`, in any environment binding `N`. -/
theorem evalInt_pMsb {E : IEnv} {N : Int} (hN : E.vals.lookup "N" = some N) :
    evalInt E pMsb = .ok (2 * N - 1) :=
  evalInt_sub_of (by simp [PExpr.isInt, SymBinOp.intArith, hN]) rfl
    (evalInt_mul_of rfl (by simp [PExpr.isInt, hN]) (evalInt_int 2) (evalInt_paramRef_of hN))
    (evalInt_int 1)

/-- The geometry table's `p` entry. -/
theorem mulEnv_p (N : Nat) : (mulEnv N).dims.lookup "p" = some [(2 * (N : Int) - 1, 0)] :=
  PDesign.dimTable_lookup_of mul2d_p_dims fun _ =>
    evalDims_cons_of (d := ⟨pMsb, .int 0⟩) (evalInt_pMsb (by simp [mulScope])) (evalInt_int 0)
      evalDims_nil

/-- The 1-bit literal `1'b0`. -/
def zero1 : LVec := LVec.ofNat 1 0

/-- `s[0] = {1'b0, pp[0]}`. -/
def s0T : PProcess :=
  .assignL (.arrayElem "s" [.int 0]) (.concat [.lit zero1, .arrayElem "pp" [.int 0]])
/-- `c[0] = '0`. -/
def c0T : PProcess := .assignL (.arrayElem "c" [.int 0]) (.fill .l0)
/-- `t[0] = '0`. -/
def t0T : PProcess := .assignL (.arrayElem "t" [.int 0]) (.fill .l0)
/-- `p[2*N-1:N] = s[N-1][N:1]` — a row part-select read. Both selects have
static labels over parameter-dependent ranges, so both are `ArraySel` paths
(labels normalized against the declared range at every point). -/
def pHiT : PProcess :=
  .assignL (.arrayPart "p" [] .range pMsb (.paramRef "N" none))
    (.arrayPart "s" [nM1] .range (.paramRef "N" none) (.int 1))

theorem mul2d_static_source : mul2d.pdesign.processes = [s0T, c0T, t0T, pHiT] := rfl

/-- `c[i][0] = 1'b0`. -/
def cRowT : PProcess := .assignL (.arrayElem "c" [.genvarRef "i", .int 0]) (.lit zero1)
/-- `t[i][j] = s[i-1][j+1] ^ pp[i][j]`. -/
def tT : PProcess :=
  .assignL (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])
    (.binary (.m0 .xor)
      (.arrayElem "s" [.binary (.m0 .sub) (.genvarRef "i") (.int 1),
        .binary (.m0 .add) (.genvarRef "j") (.int 1)])
      (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))
/-- `s[i][j] = t[i][j] ^ c[i][j]`. -/
def sT : PProcess :=
  .assignL (.arrayElem "s" [.genvarRef "i", .genvarRef "j"])
    (.binary (.m0 .xor) (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])
      (.arrayElem "c" [.genvarRef "i", .genvarRef "j"]))
/-- `c[i][j+1] = (s[i-1][j+1] & pp[i][j]) | (c[i][j] & t[i][j])`. -/
def cT : PProcess :=
  .assignL (.arrayElem "c" [.genvarRef "i", .binary (.m0 .add) (.genvarRef "j") (.int 1)])
    (.binary (.m0 .or)
      (.binary (.m0 .and)
        (.arrayElem "s" [.binary (.m0 .sub) (.genvarRef "i") (.int 1),
          .binary (.m0 .add) (.genvarRef "j") (.int 1)])
        (.arrayElem "pp" [.genvarRef "i", .genvarRef "j"]))
      (.binary (.m0 .and) (.arrayElem "c" [.genvarRef "i", .genvarRef "j"])
        (.arrayElem "t" [.genvarRef "i", .genvarRef "j"])))
/-- `s[i][N] = c[i][N]`. -/
def sTopT : PProcess :=
  .assignL (.arrayElem "s" [.genvarRef "i", .paramRef "N" none])
    (.arrayElem "c" [.genvarRef "i", .paramRef "N" none])

/-- The row block: `for (i = 1; i < N; i++) { c[i][0]; for (j …) {t; s; c}; s[i][N] }`. -/
def rowGen : GenItem :=
  .genFor (some "g_row") "i" (.int 1) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 3)
    [.process cRowT,
     .genFor (some "g_bit") "j" (.int 0) (.binary .slt (.genvarRef "j") (.paramRef "N" none))
       (.unary .inc (.genvarRef "j")) (some 4) ([tT, sT, cT].map GenItem.process),
     .process sTopT]

/-- `p[i] = s[i][0]`. -/
def outT : PProcess := .assignL (.bitSel "p" (.genvarRef "i")) (.arrayElem "s" [.genvarRef "i", .int 0])

/-- The output block `for (i = 0; i < N; i++) p[i] = s[i][0];`. -/
def outGen : GenItem :=
  .genFor (some "g_out") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) (some 4) ([outT].map GenItem.process)

theorem mul2d_generates : mul2d.pdesign.generates = [ppGen, rowGen, outGen] := rfl

/-! ### The instantiated vocabulary -/

def s0Proc (N : Nat) : Process2 :=
  .assign (.slice "s" 0 (N + 1)) (.concat #[.lit zero1, .slice (.ident "pp") 0 N])
def c0Proc (N : Nat) : Process2 := .assign (.slice "c" 0 (N + 1)) (.lit (LVec.replicate (N + 1) .l0))
def t0Proc (N : Nat) : Process2 := .assign (.slice "t" 0 N) (.lit (LVec.replicate N .l0))
/-- `p[2N-1:N] = s[N-1][N:1]`: the row part-select starts at bit
`(N-1)*(N+1) + 1 = N*N` of the flat `s`. -/
def pHiProc (N : Nat) : Process2 :=
  .assign (.slice "p" N N) (.slice (.ident "s") (N * N) N)

def cRowCell (N i : Nat) : Process2 := .assign (.slice "c" (i * (N + 1)) 1) (.lit zero1)
def tCell (N i j : Nat) : Process2 :=
  .assign (.slice "t" (i * N + j) 1)
    (.binary .xor (.slice (.ident "s") ((i - 1) * (N + 1) + (j + 1)) 1)
      (.slice (.ident "pp") (i * N + j) 1))
def sCell (N i j : Nat) : Process2 :=
  .assign (.slice "s" (i * (N + 1) + j) 1)
    (.binary .xor (.slice (.ident "t") (i * N + j) 1) (.slice (.ident "c") (i * (N + 1) + j) 1))
def cCell (N i j : Nat) : Process2 :=
  .assign (.slice "c" (i * (N + 1) + (j + 1)) 1)
    (.binary .or
      (.binary .and (.slice (.ident "s") ((i - 1) * (N + 1) + (j + 1)) 1)
        (.slice (.ident "pp") (i * N + j) 1))
      (.binary .and (.slice (.ident "c") (i * (N + 1) + j) 1) (.slice (.ident "t") (i * N + j) 1)))
def sTopCell (N i : Nat) : Process2 :=
  .assign (.slice "s" (i * (N + 1) + N) 1) (.slice (.ident "c") (i * (N + 1) + N) 1)
def outCell (N i : Nat) : Process2 := .assign (.slice "p" i 1) (.slice (.ident "s") (i * (N + 1)) 1)

/-- Row `i` (`1 ≤ i < N`): its carry-in, the bit cells, its top sum bit. -/
def rowCells (N i : Nat) : List Process2 :=
  cRowCell N i :: ((List.range N).flatMap fun j => [tCell N i j, sCell N i j, cCell N i j])
    ++ [sTopCell N i]

/-- **The instantiated multiplier**: static assigns, the partial products,
rows `1 … N-1`, the low output bits. -/
def mulProcs (N : Nat) : List Process2 :=
  [s0Proc N, c0Proc N, t0Proc N, pHiProc N]
    ++ ((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j)
    ++ ((List.range (N - 1)).flatMap fun k => rowCells N (k + 1))
    ++ (List.range N).map (outCell N)

/-! ### Windows of the 2-D arrays -/

/-- The environment facts every template reads: `N`, and the evaluated
geometry of the four arrays. -/
structure MulEnvOk (E : IEnv) (N : Nat) : Prop where
  n : E.vals.lookup "N" = some (N : Int)
  pp : E.dims.lookup "pp" = some (ppGeom N)
  t : E.dims.lookup "t" = some (ppGeom N)
  s : E.dims.lookup "s" = some (rectGeom N)
  c : E.dims.lookup "c" = some (rectGeom N)

theorem MulEnvOk.bind {E : IEnv} {N : Nat} (h : MulEnvOk E N) (g : String) (hg : g ≠ "N")
    (v : Int) : MulEnvOk (E.bindVal g v) N :=
  ⟨by simp [IEnv.bindVal, List.lookup, h.n, beq_false_of_ne (Ne.symm hg)],
   by simpa using h.pp, by simpa using h.t, by simpa using h.s, by simpa using h.c⟩

theorem MulEnvOk.nM1 {E : IEnv} {N : Nat} (h : MulEnvOk E N) :
    evalInt E nM1 = .ok ((N : Int) - 1) :=
  evalInt_sub_of (by simp [h.n]) rfl (evalInt_paramRef_of h.n) (evalInt_int 1)

/-- A path `x[i][j]` over `[N-1:0][N-1:0]` (`pp`, `t`). -/
theorem win_sq {E : IEnv} {N : Nat} {n : String} (hd : E.dims.lookup n = some (ppGeom N))
    (hN : 1 ≤ N) {ie je : PExpr} {i j : Nat}
    (hi : evalInt E ie = .ok (i : Int)) (hj : evalInt E je = .ok (j : Int)) (hiN : i < N)
    (hjN : j < N) :
    arrayElemWindow E n [ie, je] = .ok (((i * N + j : Nat) : Int), 1, true) := by
  rw [arrayElemWindow_desc0_2 hd
    (by omega) (by omega) hi (by omega) (by omega) hj (by omega) (by omega)]
  have : (i : Int) * ((N : Int) - 1 + 1) + (j : Int) = ((i * N + j : Nat) : Int) := by simp
  rw [this]

/-- A path `x[i][j]` over `[N-1:0][N:0]` (`s`, `c`). -/
theorem win_rect {E : IEnv} {N : Nat} {n : String} (hd : E.dims.lookup n = some (rectGeom N))
    (hN : 1 ≤ N) {ie je : PExpr} {i j : Nat}
    (hi : evalInt E ie = .ok (i : Int)) (hj : evalInt E je = .ok (j : Int)) (hiN : i < N)
    (hjN : j ≤ N) :
    arrayElemWindow E n [ie, je] = .ok (((i * (N + 1) + j : Nat) : Int), 1, true) := by
  rw [arrayElemWindow_desc0_2 hd
    (by omega) (by omega) hi (by omega) (by omega) hj (by omega) (by omega)]
  have : (i : Int) * ((N : Int) + 1) + (j : Int) = ((i * (N + 1) + j : Nat) : Int) := by simp
  rw [this]

/-- An in-range 1-bit path read in a 1-bit context: the flat `slice`. -/
theorem read1 {E : IEnv} {elems : List (String × Nat)} {n : String} {is : List PExpr} {k : Nat}
    (h : arrayElemWindow E n is = .ok ((k : Int), 1, true)) :
    fitExpr2 E elems (some 1) (.arrayElem n is) = .slice (.ident n) k 1 := by
  rw [fitExpr2_arrayElem_of h, arrayElemRead_of_inRange h, Int.toNat_natCast]

/-- An in-range 1-bit path target. -/
theorem target1 {E : IEnv} {elems : List (String × Nat)} {n : String} {is : List PExpr} {k : Nat}
    (h : arrayElemWindow E n is = .ok ((k : Int), 1, true)) :
    instLhs2 E elems (.arrayElem n is) = .ok (.slice n k 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange h, Int.toNat_natCast]

/-! ### The templates at in-range genvars -/

section cells

variable {env : IEnv} {elems : List (String × Nat)} {N : Nat}

private theorem gv_i (env : IEnv) (i j : Int) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "i") = .ok i :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal, List.lookup])

private theorem gv_j (env : IEnv) (i j : Int) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.genvarRef "j") = .ok j :=
  evalInt_genvarRef_of (by simp [IEnv.bindVal])

private theorem gv_im1 (env : IEnv) (i : Nat) (j : Int) (hi : 1 ≤ i) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.binary (.m0 .sub) (.genvarRef "i") (.int 1)) =
      .ok ((i - 1 : Nat) : Int) := by
  rw [evalInt_sub_of rfl rfl (gv_i env i j) (evalInt_int 1)]
  congr 1
  omega

private theorem gv_jp1 (env : IEnv) (i : Int) (j : Nat) :
    evalInt ((env.bindVal "i" i).bindVal "j" j) (.binary (.m0 .add) (.genvarRef "j") (.int 1)) =
      .ok ((j + 1 : Nat) : Int) := by
  rw [evalInt_add_of rfl rfl (gv_j env i j) (evalInt_int 1)]
  simp

theorem cRow_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i : Nat) (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems cRowT = cRowCell N i := by
  have hi' : evalInt (env.bindVal "i" i) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  have hw := win_rect (n := "c") (by simpa using h.c) hN hi'
    (evalInt_int 0) (j := 0) hi (by omega)
  have hz : zero1.width = 1 := LVec.width_ofNat 1 0
  rw [cRowT, instProcess2_assignL _ (target1 hw), fitExpr2_lit, if_pos hz]
  simp [cRowCell]

theorem t_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i j : Nat) (hi1 : 1 ≤ i) (hi : i < N)
    (hj : j < N) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems tT = tCell N i j := by
  have h' := (h.bind "i" (by decide) i).bind "j" (by decide) j
  have hwT := win_sq (n := "t") h'.t hN (gv_i env i j) (gv_j env i j) hi hj
  have hwS := win_rect (n := "s") h'.s hN (gv_im1 env i j hi1) (gv_jp1 env i j) (by omega)
    (by omega)
  have hwP := win_sq (n := "pp") h'.pp hN (gv_i env i j) (gv_j env i j) hi hj
  rw [tT, instProcess2_assignL _ (target1 hwT), fitExpr2_binary, instExpr2_xor, read1 hwS,
    read1 hwP]
  rfl

theorem s_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i j : Nat) (hi : i < N) (hj : j < N) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems sT = sCell N i j := by
  have h' := (h.bind "i" (by decide) i).bind "j" (by decide) j
  have hwS := win_rect (n := "s") h'.s hN (gv_i env i j) (gv_j env i j) hi (by omega)
  have hwT := win_sq (n := "t") h'.t hN (gv_i env i j) (gv_j env i j) hi hj
  have hwC := win_rect (n := "c") h'.c hN (gv_i env i j) (gv_j env i j) hi (by omega)
  rw [sT, instProcess2_assignL _ (target1 hwS), fitExpr2_binary, instExpr2_xor, read1 hwT,
    read1 hwC]
  rfl

theorem c_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i j : Nat) (hi1 : 1 ≤ i) (hi : i < N)
    (hj : j < N) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) elems cT = cCell N i j := by
  have h' := (h.bind "i" (by decide) i).bind "j" (by decide) j
  have hwC1 := win_rect (n := "c") h'.c hN (gv_i env i j) (gv_jp1 env i j) hi (by omega)
  have hwS := win_rect (n := "s") h'.s hN (gv_im1 env i j hi1) (gv_jp1 env i j) (by omega)
    (by omega)
  have hwP := win_sq (n := "pp") h'.pp hN (gv_i env i j) (gv_j env i j) hi hj
  have hwC := win_rect (n := "c") h'.c hN (gv_i env i j) (gv_j env i j) hi (by omega)
  have hwT := win_sq (n := "t") h'.t hN (gv_i env i j) (gv_j env i j) hi hj
  rw [cT, instProcess2_assignL _ (target1 hwC1), fitExpr2_binary, instExpr2_or, fitExpr2_binary,
    instExpr2_and, fitExpr2_binary, instExpr2_and, read1 hwS, read1 hwP, read1 hwC, read1 hwT]
  rfl

theorem sTop_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (i : Nat) (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems sTopT = sTopCell N i := by
  have h' := h.bind "i" (by decide) i
  have hi' : evalInt (env.bindVal "i" i) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  have hwS := win_rect (n := "s") h'.s hN hi' (evalInt_paramRef_of h'.n) hi (Nat.le_refl N)
  have hwC := win_rect (n := "c") h'.c hN hi' (evalInt_paramRef_of h'.n) hi (Nat.le_refl N)
  rw [sTopT, instProcess2_assignL _ (target1 hwS), read1 hwC]
  rfl

theorem out_inst (h : MulEnvOk env N) (hN : 1 ≤ N) (hp : elems.lookup "p" = some 1) (i : Nat)
    (hi : i < N) :
    instProcess2 (env.bindVal "i" i) elems outT = outCell N i := by
  have h' := h.bind "i" (by decide) i
  have hi' : evalInt (env.bindVal "i" i) (.genvarRef "i") = .ok (i : Int) :=
    evalInt_genvarRef_of (by simp [IEnv.bindVal])
  have hwS := win_rect (n := "s") h'.s hN hi' (evalInt_int 0) (j := 0) hi (by omega)
  rw [outT, instProcess2_assignL _ (instLhs2_bitSel hp hi' (by omega)), read1 hwS]
  simp [outCell]

end cells

/-! ### The generate blocks -/

theorem mul2d_row_expand (env : IEnv) (elems : List (String × Nat)) (N F : Nat) (hN : 1 ≤ N)
    (hF : N < F) (h : MulEnvOk env N) :
    rowGen.expand2 env elems F =
      .ok ((List.range (N - 1)).flatMap fun k => rowCells N (k + 1)) := by
  rw [rowGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => rowCells N (v.toNat))
      (evalInt_int 1) (n_bound_int env N h.n "i" (by decide)) (n_bound env N h.n "i" (by decide)) (by omega)]
  · congr 1
    have hcnt : ((N : Int) - 1).toNat = N - 1 := by omega
    rw [hcnt, intRange_eq_map, List.flatMap_map]
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro k _
    show rowCells N (1 + (k : Int)).toNat = rowCells N (k + 1)
    congr 1
    omega
  · intro v hv1 hvN
    obtain ⟨i, rfl⟩ : ∃ i : Nat, v = (i : Int) := ⟨v.toNat, by omega⟩
    have hi1 : 1 ≤ i := by omega
    have hiN : i < N := by omega
    have hb := h.bind "i" (by decide) i
    have hinner : (GenItem.genFor (some "g_bit") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "N" none)) (.unary .inc (.genvarRef "j")) (some 4)
        ([tT, sT, cT].map GenItem.process)).expand2 (env.bindVal "i" i) elems F =
        .ok ((List.range N).flatMap fun j => [tCell N i j, sCell N i j, cCell N i j]) := by
      rw [GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
          (f := fun w => [tCell N i w.toNat, sCell N i w.toNat, cCell N i w.toNat])
          (evalInt_int 0) (n_bound_int _ N hb.n "j" (by decide)) (n_bound _ N hb.n "j" (by decide)) (by omega)]
      · congr 1
        rw [intRange_zero, List.flatMap_map]
        simp
      · intro w hw0 hwN
        obtain ⟨j, rfl⟩ : ∃ j : Nat, w = (j : Int) := ⟨w.toNat, by omega⟩
        have hjN : j < N := by omega
        rw [expandList2_processes]
        simp only [List.map_cons, List.map_nil, Int.toNat_natCast]
        rw [t_inst h hN i j hi1 hiN hjN, s_inst h hN i j hiN hjN, c_inst h hN i j hi1 hiN hjN]
    rw [expandList2_cons_ok (GenItem.expand2_process _)
      (expandList2_cons_ok hinner (expandList2_singleton_ok (GenItem.expand2_process _)))]
    rw [cRow_inst h hN i hiN, sTop_inst h hN i hiN]
    simp [rowCells]

theorem mul2d_out_expand (env : IEnv) (elems : List (String × Nat)) (N F : Nat) (hN : 1 ≤ N)
    (hF : N < F) (h : MulEnvOk env N) (hp : elems.lookup "p" = some 1) :
    outGen.expand2 env elems F = .ok ((List.range N).map (outCell N)) := by
  rw [outGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => [outCell N v.toNat])
      (evalInt_int 0) (n_bound_int env N h.n "i" (by decide)) (n_bound env N h.n "i" (by decide)) (by simpa using hF)]
  · congr 1
    rw [intRange_zero, List.flatMap_map]
    simp only [Int.sub_zero, Int.toNat_natCast]
    exact Gen2.flatMap_singleton_map (outCell N) (List.range N)
  · intro v hv0 hvN
    obtain ⟨i, rfl⟩ : ∃ i : Nat, v = (i : Int) := ⟨v.toNat, by omega⟩
    rw [expandList2_processes]
    simp only [List.map_cons, List.map_nil, Int.toNat_natCast]
    rw [out_inst h hN hp i (by omega)]

/-! ### Assembling `instantiate2` -/

/-- Element widths (`buildElems`) for `N ≥ 1`. -/
def mulElems (N : Nat) : List (String × Nat) :=
  [("a", 1), ("b", 1), ("p", 1), ("pp", N), ("s", N + 1), ("c", N + 1), ("t", N)]

private theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem mul2d_elems (N : Nat) (hN : 1 ≤ N) :
    buildElems (mulEnv N) mul2d.pdesign.decls = .ok (mulElems N) := by
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  simp [mul2d.pdesign, buildElems, PType.width_packed_cons, PType.elemWidth, PDim.width,
    evalInt, mulEnv, mulScope, List.lookup, mulElems, Gen2.except_ok_bind, hv, List.foldlM_cons,
    except_pure]

theorem mul2d_decls_ok (N : Int) : ∃ decls, buildDecls (mulEnv N) mul2d.pdesign.decls = .ok decls := by
  simp [mul2d.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt, mulEnv,
    mulScope, List.lookup, Gen2.except_ok_bind]

theorem mulEnvOk (N : Nat) (decls : List Decl) : MulEnvOk ((mulEnv N).withDecls decls) N :=
  ⟨by simp [mulEnv, mulScope], by simpa using mulEnv_pp N, by simpa using mulEnv_t N,
   by simpa using mulEnv_s N, by simpa using mulEnv_c N⟩

/-- An unbased-unsized fill in a context of width `w`. -/
private theorem instExpr2_fill_ctx {env : IEnv} {elems : List (String × Nat)} {w : Nat}
    {b : Logic} : instExpr2 env elems (some w) (.fill b) = .lit (LVec.replicate w b) := by
  simp [instExpr2]

theorem mul2d_static (N : Nat) (hN : 1 ≤ N) (decls : List Decl) :
    mul2d.pdesign.processes.map (instProcess2 ((mulEnv N).withDecls decls) (mulElems N)) =
      [s0Proc N, c0Proc N, t0Proc N, pHiProc N] := by
  have E := mulEnvOk N decls
  rw [mul2d_static_source]
  -- `p[2*N-1:N]`: the target window (a static-label `ArraySel` path over
  -- `[2*N-1:0]`) and the row part-select read.
  have hm : evalInt ((mulEnv N).withDecls decls) pMsb = .ok (2 * (N : Int) - 1) :=
    evalInt_pMsb E.n
  have hpd : ((mulEnv N).withDecls decls).dims.lookup "p" = some [(2 * (N : Int) - 1, 0)] := by
    simpa using mulEnv_p N
  have hgp := arrayPartGeom_range_of (is := []) (a := pMsb) (b := .paramRef "N" none)
    (arrayDims_of hpd) (walkIndices_nil (env := (mulEnv N).withDecls decls) _) hm
    (evalInt_paramRef_of E.n)
    (by rw [labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega),
      labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega)]; omega)
  rw [labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega) (N : Int),
    labelOffset_desc0 (m := 2 * (N : Int) - 1) (by omega) (2 * (N : Int) - 1)] at hgp
  have hcp := dimCount_desc0 (by omega : (0 : Int) ≤ 2 * (N : Int) - 1)
  have hP := arrayPartTarget_of_inRange hgp (by omega) (by omega)
  have hpw : (2 * (N : Int) - 1 - N + 1).toNat * dimsStride [] = N := by simp; omega
  have hpl : ((0 : Int) + (N : Int) * ((dimsStride [] : Nat) : Int)).toNat = N := by simp
  rw [hpw, hpl] at hP
  have hwalk := walkIndices_desc0_cons (env := (mulEnv N).withDecls decls) (ds := [((N : Int), 0)])
    (by omega : (0 : Int) ≤ (N : Int) - 1) E.nM1 (by omega) (Int.le_refl _)
    (walkIndices_nil (env := (mulEnv N).withDecls decls) [((N : Int), 0)])
  have hgeom := arrayPartGeom_range_of (a := .paramRef "N" none) (b := .int 1)
    (arrayDims_of E.s) hwalk (evalInt_paramRef_of E.n) (evalInt_int 1)
    (by rw [labelOffset_desc0 (m := (N : Int)) (by omega),
      labelOffset_desc0 (m := (N : Int)) (by omega)]; omega)
  rw [labelOffset_desc0 (m := (N : Int)) (by omega) (N : Int),
    labelOffset_desc0 (m := (N : Int)) (by omega) 1] at hgeom
  have hc := dimCount_desc0 (by omega : (0 : Int) ≤ (N : Int))
  have hread := arrayPartRead_of_inRange hgeom (by omega) (by omega)
  have hsw := selfWidth2_arrayPart_of (elems := mulElems N) hgeom
  have hwid : ((N : Int) - 1 + 1).toNat * dimsStride [] = N := by simp
  rw [hwid] at hsw hread
  have hs : dimsStride [((N : Int), 0)] = N + 1 := by
    simp only [dimsStride_cons, dimsStride_nil, Nat.mul_one]
    omega
  have hoff : (((N : Int) - 1) * ((dimsStride [((N : Int), 0)] : Nat) : Int) + 0
      + 1 * ((dimsStride [] : Nat) : Int)).toNat = N * N := by
    rw [hs, dimsStride_nil]
    have hsq : ((N : Int) - 1) * ((N + 1 : Nat) : Int) + 0 + 1 * ((1 : Nat) : Int) =
        ((N * N : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_add, Int.mul_one,
        Int.one_mul, Int.add_zero, Int.natCast_one]
      omega
    rw [hsq, Int.toNat_natCast]
  rw [hoff] at hread
  -- `s[0]`, `c[0]`, `t[0]`, `pp[0]`: the first row of a `[N-1:0][…]` array.
  have hrow : ∀ {n : String} {m : Int} (hd : ((mulEnv N).withDecls decls).dims.lookup n =
      some [((N : Int) - 1, 0), (m, 0)]),
      arrayElemWindow ((mulEnv N).withDecls decls) n [.int 0] = .ok (0, dimCount m 0, true) := by
    intro n m hd
    rw [arrayElemWindow_of (arrayDims_of hd) (walkIndices_desc0_cons (by omega) (evalInt_int 0)
      (Int.le_refl 0) (by omega) (walkIndices_nil _))]
    simp [dimsStride]
  have hcN : dimCount ((N : Int) - 1) 0 = N := by unfold dimCount; omega
  have hcN1 : dimCount (N : Int) 0 = N + 1 := by unfold dimCount; omega
  have hwS := hrow (n := "s") E.s
  have hwC := hrow (n := "c") E.c
  have hwT := hrow (n := "t") E.t
  have hwP := hrow (n := "pp") E.pp
  rw [hcN1] at hwS hwC
  rw [hcN] at hwT hwP
  simp only [List.map_cons, List.map_nil]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, ?_⟩⟩⟩
  · have hz : zero1.width = 1 := LVec.width_ofNat 1 0
    have h1 : selfWidth2 ((mulEnv N).withDecls decls) (mulElems N) (.lit zero1) = some 1 := by
      rw [selfWidth2_lit, hz]
    have hsum : selfWidthSum2 ((mulEnv N).withDecls decls) (mulElems N)
        [.lit zero1, .arrayElem "pp" [.int 0]] = some (N + 1) := by
      rw [selfWidthSum2_cons_of h1 (selfWidthSum2_cons_of
        (selfWidth2_arrayElem_of hwP) selfWidthSum2_nil), Option.some.injEq]
      omega
    rw [s0T, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hwS]),
      fitExpr2_concat hsum, if_pos rfl, instParts2_cons, instParts2_cons, instParts2_nil,
      instExpr2_lit, instExpr2_arrayElem, arrayElemRead_of_inRange hwP]
    simp only [s0Proc, Int.toNat_zero]
  · rw [c0T, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hwC]),
      fitExpr2_of_not_rigid (N + 1) rfl, instExpr2_fill_ctx]
    simp only [c0Proc, Int.toNat_zero]
  · rw [t0T, instProcess2_assignL _ (by rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hwT]),
      fitExpr2_of_not_rigid N rfl, instExpr2_fill_ctx]
    simp only [t0Proc, Int.toNat_zero]
  · rw [pHiT, instProcess2_assignL _ (by rw [instLhs2_arrayPart]; exact hP),
      fitExpr2_of_rigid_eq rfl hsw, instExpr2_arrayPart _ (dynPartPlan_of_geom hgeom), hread]
    rfl

theorem mul2d_gens (N : Nat) (hN : 1 ≤ N) (decls : List Decl) :
    expandList2 ((mulEnv N).withDecls decls) (mulElems N) (PDesign.surfaceFuel [(N : Int)])
      mul2d.pdesign.generates =
      .ok (((List.range N).flatMap fun i => (List.range N).map fun j => ppCell N i j)
        ++ (((List.range (N - 1)).flatMap fun k => rowCells N (k + 1))
        ++ (List.range N).map (outCell N))) := by
  have hF : N < PDesign.surfaceFuel [(N : Int)] := by
    have := Nat.le_mul_self (N + 2)
    simp [PDesign.surfaceFuel]
    omega
  have E := mulEnvOk N decls
  rw [mul2d_generates]
  exact expandList2_cons_ok (mul2d_pp_instantiated N hN decls _ (by simp [mulElems])
      (by simp [mulElems, List.lookup]))
    (expandList2_cons_ok (mul2d_row_expand _ _ N _ hN hF E)
      (expandList2_singleton_ok
        (mul2d_out_expand _ _ N _ hN hF E (by simp [mulElems, List.lookup]))))

/-! ### The one-driver rule, for every `N`

`mul2d.sem N` is `instantiateGD2`: the instantiated design under the
one-driver rule (`Hier2.lean`, "Drivers" — a flat top is checked at every
parameter point since 2026-10-28). It holds for every `N`, by the
process-list recipe of `Hier2Gen.lean`. Each partial-product row and each
adder row is stated over its BASE offsets (`q = i*N` into `pp`/`t`,
`r = i*(N+1)` into `s`/`c`), so every disjointness inside a row is linear
for `omega`; `rowMajor_le` orders the bases of two rows. -/

theorem mul2d_declNames : mul2d.pdesign.declNames = ["a", "b", "p", "pp", "s", "c", "t"] := rfl

theorem mul2d_inputNames : mul2d.pdesign.inputNames = ["a", "b"] := rfl

/-- Partial-product row `i`'s windows over its base `q = i*N`. -/
def ppWins (N q : Nat) : List DrvWin := (List.range N).flatMap fun j => [("pp", some (q + j, 1))]

/-- Adder row `i`'s windows over its bases `r = i*(N+1)` (`s`, `c`) and
`q = i*N` (`t`): the carry-in, the bit cells, the top sum bit. -/
def rowWins (N r q : Nat) : List DrvWin :=
  ("c", some (r, 1)) :: ((List.range N).flatMap fun j =>
    [("t", some (q + j, 1)), ("s", some (r + j, 1)), ("c", some (r + (j + 1), 1))])
    ++ [("s", some (r + N, 1))]

/-- The four static windows: `s[0]`, `c[0]`, `t[0]` (whole rows) and
`p[2N-1:N]`. -/
def staticWins (N : Nat) : List DrvWin :=
  [("s", some (0, N + 1)), ("c", some (0, N + 1)), ("t", some (0, N)), ("p", some (N, N))]

/-- The low output bits `p[i]`. -/
def outWins (N : Nat) : List DrvWin := (List.range N).flatMap fun i => [("p", some (i, 1))]

/-- The continuous-driver windows of the instantiated multiplier. -/
theorem mul2d_driverWins (N : Nat) :
    driverWins ["a", "b", "p", "pp", "s", "c", "t"] (mulProcs N) =
      staticWins N ++ (List.range N).flatMap (fun i => ppWins N (i * N))
        ++ (List.range (N - 1)).flatMap (fun k => rowWins N ((k + 1) * (N + 1)) ((k + 1) * N))
        ++ outWins N := by
  have hp : ["a", "b", "p", "pp", "s", "c", "t"].contains "p" = true := by decide
  have hpp : ["a", "b", "p", "pp", "s", "c", "t"].contains "pp" = true := by decide
  have hs : ["a", "b", "p", "pp", "s", "c", "t"].contains "s" = true := by decide
  have hc : ["a", "b", "p", "pp", "s", "c", "t"].contains "c" = true := by decide
  have ht : ["a", "b", "p", "pp", "s", "c", "t"].contains "t" = true := by decide
  simp only [mulProcs, rowCells, driverWins_append, driverWins_cons, driverWins_nil,
    driverWins_flatMap, driverWins_map, s0Proc, c0Proc, t0Proc, pHiProc, ppCell, cRowCell, tCell,
    sCell, cCell, sTopCell, outCell, Process2.drvWins, Lhs2.drvWins, List.filter_cons,
    List.filter_nil, hp, hpp, hs, hc, ht, ↓reduceIte, List.cons_append, List.nil_append,
    List.append_nil, staticWins, ppWins, rowWins, outWins]

/-- Two windows of different signals never overlap. -/
private theorem ov_names {n n' : String} {l w l' w' : Nat} (h : n ≠ n') :
    DrvWin.overlaps (n, some (l, w)) (n', some (l', w')) = false :=
  DrvWin.overlaps_some_eq_false.mpr (Or.inl h)

/-- A partial-product row's windows are pairwise disjoint. -/
theorem ppWins_pairwise (N q : Nat) :
    (ppWins N q).Pairwise fun a b => a.overlaps b = false :=
  pairwise_flatMap_range (fun _ _ => List.pairwise_singleton _ _)
    fun j k hjk _ a ha b hb => by
      simp only [List.mem_singleton] at ha hb
      subst ha hb
      exact DrvWin.overlaps_some_eq_false.mpr (Or.inr (Or.inr (by omega)))

/-- Two partial-product rows with bases `q + N ≤ q'` are disjoint. -/
theorem ppWins_cross {N q q' : Nat} (h : q + N ≤ q') :
    ∀ a ∈ ppWins N q, ∀ b ∈ ppWins N q', a.overlaps b = false := by
  intro a ha b hb
  simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at ha hb
  obtain ⟨j, hj, rfl⟩ := ha
  obtain ⟨k, hk, rfl⟩ := hb
  exact DrvWin.overlaps_some_eq_false.mpr (Or.inr (Or.inr (by omega)))

/-- Membership in an adder row. -/
theorem mem_rowWins {N r q : Nat} {a : DrvWin} :
    a ∈ rowWins N r q ↔ a = ("c", some (r, 1)) ∨ a = ("s", some (r + N, 1)) ∨
      ∃ j < N, a = ("t", some (q + j, 1)) ∨ a = ("s", some (r + j, 1)) ∨
        a = ("c", some (r + (j + 1), 1)) := by
  simp only [rowWins, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false]
  constructor
  · rintro ((h | ⟨j, hj, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨j, hj, h⟩)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | ⟨j, hj, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨j, hj, h⟩)

/-- An adder row's windows are pairwise disjoint. -/
theorem rowWins_pairwise (N r q : Nat) :
    (rowWins N r q).Pairwise fun a b => a.overlaps b = false := by
  rw [rowWins, List.pairwise_append, List.pairwise_cons]
  refine ⟨⟨fun b hb => ?_, pairwise_flatMap_range (fun j _ => ?_)
    fun j k hjk _ a ha b hb => ?_⟩, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    obtain ⟨j, hj, rfl | rfl | rfl⟩ := hb <;> simp [DrvWin.overlaps]
  · simp [DrvWin.overlaps]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp [DrvWin.overlaps] <;> omega
  · simp only [List.mem_singleton] at hb
    subst hb
    simp only [List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at ha
    rcases ha with rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> simp [DrvWin.overlaps] <;> omega

/-- Two adder rows with bases `r + (N+1) ≤ r'`, `q + N ≤ q'` are disjoint. -/
theorem rowWins_cross {N r q r' q' : Nat} (hr : r + (N + 1) ≤ r') (hq : q + N ≤ q') :
    ∀ a ∈ rowWins N r q, ∀ b ∈ rowWins N r' q', a.overlaps b = false := by
  intro a ha b hb
  rw [mem_rowWins] at ha hb
  rcases ha with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;>
    rcases hb with rfl | rfl | ⟨k, hk, rfl | rfl | rfl⟩ <;> simp [DrvWin.overlaps] <;> omega

/-- **The one-driver rule holds for every `N`.** -/
theorem mul2d_driversOk (N : Nat) :
    driversOk mul2d.pdesign.declNames mul2d.pdesign.inputNames (mulProcs N) = true := by
  rw [mul2d_declNames, mul2d_inputNames]
  apply driversOk_of_continuous
  · rw [List.flatMap_eq_nil_iff]
    intro p hp
    simp only [mulProcs, rowCells, List.mem_append, List.mem_cons, List.mem_flatMap,
      List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hp
    rcases hp with (((rfl | rfl | rfl | rfl) | ⟨i, -, j, -, rfl⟩) |
      ⟨k, -, (rfl | ⟨j, -, rfl | rfl | rfl⟩) | rfl⟩) | ⟨i, -, rfl⟩ <;> rfl
  · rw [mul2d_driverWins]
    simp only [List.pairwise_append]
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · simp [staticWins, DrvWin.overlaps]
    · exact pairwise_flatMap_range (fun i _ => ppWins_pairwise N (i * N))
        fun i i' hii' _ => ppWins_cross (rowMajor_le hii')
    · intro a ha b hb
      simp only [staticWins, List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at hb
      obtain ⟨i, -, j, -, rfl⟩ := hb
      rcases ha with rfl | rfl | rfl | rfl <;> exact ov_names (by decide)
    · exact pairwise_flatMap_range (fun k _ => rowWins_pairwise N _ _)
        fun k k' hkk' _ => rowWins_cross (rowMajor_le (by omega)) (rowMajor_le (by omega))
    · intro a ha b hb
      simp only [List.mem_append] at ha
      simp only [List.mem_flatMap, List.mem_range] at hb
      obtain ⟨k, -, hb⟩ := hb
      have hr : 0 * (N + 1) + (N + 1) ≤ (k + 1) * (N + 1) := rowMajor_le (by omega)
      have hq : 0 * N + N ≤ (k + 1) * N := rowMajor_le (by omega)
      rw [mem_rowWins] at hb
      rcases ha with ha | ha
      · simp only [staticWins, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> simp [DrvWin.overlaps] <;> omega
      · simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at ha
        obtain ⟨i, -, j, -, rfl⟩ := ha
        rcases hb with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> exact ov_names (by decide)
    · exact pairwise_flatMap_range (fun _ _ => List.pairwise_singleton _ _)
        fun i i' hii' _ a ha b hb => by
          simp only [List.mem_singleton] at ha hb
          subst ha hb
          exact DrvWin.overlaps_some_eq_false.mpr (Or.inr (Or.inr (by omega)))
    · intro a ha b hb
      simp only [outWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · simp only [staticWins, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simp [DrvWin.overlaps] <;> omega
      · simp only [ppWins, List.mem_flatMap, List.mem_range, List.mem_singleton] at ha
        obtain ⟨i', -, j, -, rfl⟩ := ha
        exact ov_names (by decide)
      · simp only [List.mem_flatMap, List.mem_range] at ha
        obtain ⟨k, -, ha⟩ := ha
        rw [mem_rowWins] at ha
        rcases ha with rfl | rfl | ⟨j, hj, rfl | rfl | rfl⟩ <;> exact ov_names (by decide)
  · intro w hw
    rw [mul2d_driverWins] at hw
    simp only [List.mem_append, staticWins, ppWins, outWins, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap, List.mem_range] at hw
    rcases hw with (((rfl | rfl | rfl | rfl) | ⟨i, -, j, -, rfl⟩) | ⟨k, -, hw⟩) | ⟨i, -, rfl⟩
    all_goals first
      | rfl
      | (rw [mem_rowWins] at hw
         rcases hw with rfl | rfl | ⟨j, -, rfl | rfl | rfl⟩ <;> rfl)

/-- **`mul2d`'s instantiated process list, for every `N ≥ 1`** (nothing
unrolled): the static assigns, the `N×N` partial products, rows `1 … N-1`,
and the low output bits — every nested select a flat 1-bit window. -/
theorem mul2d_processes (N : Nat) (hN : 1 ≤ N) :
    (mul2d.sem N).processes.toList = mulProcs N := by
  obtain ⟨decls, hdecls⟩ := mul2d_decls_ok N
  have h := PDesign.instantiate2_of_ok (d := mul2d.pdesign) (args := [(N : Int)]) rfl
    (mul2d_paramEnv N) hdecls (mul2d_elems N hN) (mul2d_gens N hN decls)
  have hothers : mul2d.pdesign.others = [] := rfl
  have hD : (mul2d.pdesign.instantiateD2 [(N : Int)]).processes.toList = mulProcs N := by
    rw [PDesign.instantiateD2_of_ok h, PDesign.assemble2_processes, mul2d_static N hN decls,
      hothers]
    simp [mulProcs]
  -- `mul2d.sem N` is `instantiateGD2`; its one-driver guard passes.
  show (mul2d.pdesign.instantiateGD2 [(N : Int)]).processes.toList = mulProcs N
  rw [PDesign.instantiateGD2_of_driversOk (by rw [hD]; exact mul2d_driversOk N), hD]

#print axioms mul2d_pp_expand
#print axioms mul2d_pp_instantiated
#print axioms mul2d_driversOk
#print axioms mul2d_processes

/-! ## Concrete agreement (non-vacuity at the default `N = 4`) -/

#guard (mul2d.sem 4).processes.size == 4 + 16 + 3 * (2 + 3 * 4) + 4
#guard (mul2d.sem 4).decls.toList.map (·.width) == [4, 4, 8, 16, 20, 20, 16]
#guard !(mul2d.sem 4).hasUnsupported

end Examples.«system-verilog».mul2d.gen
