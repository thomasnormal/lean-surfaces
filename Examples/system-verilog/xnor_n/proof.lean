import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Known2
import LeanModels.Sv.Hier2Gen

/-!
# `xnor_n` — the native XNOR operator `~^`, for every width (WP-L2, 2026-10-30)

`xnor_n.sv` is `assign y = a ~^ b;` over `N`-bit vectors. The extractor lowers the binary XNOR
(`~^` and its spelling `^~`: one slang operator) to `~(a ^ b)`, the two nodes the symbolic tier
already has, so there is no new operator in the semantics: this file proves that the lowered
expression has the IEEE 1800-2023 value, for every width.

1. **The table (Table 11-14).** `xnorTable` is the 4 x 4 table of the standard written out (`0 ~^ 0 = 1`,
   `0 ~^ 1 = 0`, `1 ~^ 0 = 0`, `1 ~^ 1 = 1`, every other pair, any x or z operand, `x`), independent
   of the semantics' `Logic.not` and `Logic.xor`; `xnor_table` proves they agree on all 16 pairs.
2. **Every width, every 4-state vector.** `xnor_vec`: for any two vectors of one width the lowered
   expression is the bitwise `xnorTable` of the operand bits, so an x or z bit in either operand gives
   x in exactly that bit (`xnor_vec_unknown`) and nothing else; known vectors give the bit-vector
   `~~~(x ^^^ y)` (`xnor_known`, Known2's `xor_ofBitVec` and `not_ofBitVec`).
3. **The evaluated design expression.** `xnor_eval`: the evaluator's value of the lowered expression
   over a state that binds `a` and `b` is that vector.
4. **The design.** `xnor_n.sem N` has the one process `y = ~(a ^ b)` for every `N` (`xnor_n_processes`),
   so 2 and 3 are about the design for every `N`.
-/

namespace Examples.«system-verilog».xnor_n.proof

open LeanModels.Sv

load_design_sv2 xnor_n from "Examples/system-verilog/xnor_n/xnor_n.sv.json"

/-! ## 1. The table of the standard -/

/-- IEEE 1800-2023 Table 11-14, bitwise XNOR (`~^`, `^~`). -/
def xnorTable : Logic → Logic → Logic
  | .l0, .l0 => .l1
  | .l0, .l1 => .l0
  | .l1, .l0 => .l0
  | .l1, .l1 => .l1
  | _, _ => .lx

/-- The semantics' `~` over `^` is Table 11-14 on all 16 pairs. -/
theorem xnor_table (a b : Logic) : (a.xor b).not = xnorTable a b := by
  cases a <;> cases b <;> rfl

/-- Any x or z operand bit gives x. -/
theorem xnorTable_unknown {a b : Logic} (h : a.isKnown = false ∨ b.isKnown = false) :
    xnorTable a b = .lx := by
  cases a <;> cases b <;> simp_all [xnorTable, Logic.isKnown]

/-- Known bits: 1 exactly when they are equal. -/
theorem xnorTable_ofBool (a b : Bool) :
    xnorTable (Logic.ofBool a) (Logic.ofBool b) = Logic.ofBool (a == b) := by
  cases a <;> cases b <;> rfl

/-! ## 2. Every width -/

/-- **The lowered expression, bit by bit.** For vectors of one width, `~(a ^ b)` is the bitwise
Table 11-14 of the operand bits. -/
theorem xnor_vec (a b : LVec) (hw : a.width = b.width) :
    evalUnaryOp .bnot (evalBinOp .xor a b) = ⟨Array.zipWith xnorTable a.bits b.bits⟩ := by
  have hw' : a.bits.size = b.bits.size := hw
  simp only [evalUnaryOp, evalBinOp, LVec.not, LVec.xor, LVec.zipWith, LVec.width, hw', if_true]
  congr 1
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [Array.getElem_zipWith, xnor_table]

/-- The width is kept. -/
theorem xnor_width (a b : LVec) (hw : a.width = b.width) :
    (evalUnaryOp .bnot (evalBinOp .xor a b)).width = a.width := by
  have hw' : a.bits.size = b.bits.size := hw
  rw [xnor_vec a b hw]
  simp [LVec.width, Array.size_zipWith, hw']

/-- **x/z propagation, every width**: bit `i` of the result is x as soon as bit `i` of either operand
is x or z. -/
theorem xnor_vec_unknown (a b : LVec) (hw : a.width = b.width) (i : Nat) (ha : i < a.width)
    (h : a.bits[i]?.map Logic.isKnown = some false ∨ b.bits[i]?.map Logic.isKnown = some false) :
    (evalUnaryOp .bnot (evalBinOp .xor a b)).bits[i]? = some .lx := by
  have hb : i < b.width := hw ▸ ha
  have ha' : i < a.bits.size := ha
  have hb' : i < b.bits.size := hb
  rw [xnor_vec a b hw]
  show (Array.zipWith xnorTable a.bits b.bits)[i]? = some Logic.lx
  rw [Array.getElem?_zipWith, Array.getElem?_eq_getElem ha', Array.getElem?_eq_getElem hb']
  rw [Array.getElem?_eq_getElem ha', Array.getElem?_eq_getElem hb'] at h
  simp only [Option.map_some, Option.some.injEq] at h
  show some (xnorTable a.bits[i] b.bits[i]) = some Logic.lx
  rw [xnorTable_unknown h]

/-- **Known vectors**: the bit-vector `~~~(x ^^^ y)`, for every width. -/
theorem xnor_known {w : Nat} (x y : BitVec w) :
    evalUnaryOp .bnot (evalBinOp .xor (LVec.ofBitVec x) (LVec.ofBitVec y)) =
      LVec.ofBitVec (~~~(x ^^^ y)) := by
  simp [evalUnaryOp, evalBinOp]

/-- … and bit `i` of it is `a_i == b_i` (the equality of the operand bits). -/
theorem xnor_known_bit {w : Nat} (x y : BitVec w) (i : Nat) (hi : i < w) :
    (evalUnaryOp .bnot (evalBinOp .xor (LVec.ofBitVec x) (LVec.ofBitVec y))).bits[i]? =
      some (Logic.ofBool (x.getLsbD i == y.getLsbD i)) := by
  rw [xnor_known]
  simp [LVec.getElem?_ofBitVec, hi]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> rfl

/-! ## 3. The evaluated design expression -/

/-- The right-hand side `xnor_n` instantiates to. -/
def xnorExpr : Expr2 := .unary .bnot (.binary .xor (.ident "a") (.ident "b"))

/-- **The evaluator on a state binding `a` and `b`** (fuel-free evaluator `evalPure2`): the lowered
expression's value is `xnor_vec`'s vector. -/
theorem xnor_eval (st : SvState) (a b : LVec) (ha : SvState.lookup st "a" = some a)
    (hb : SvState.lookup st "b" = some b) :
    evalPure2 st xnorExpr = .ok (evalUnaryOp .bnot (evalBinOp .xor a b)) := by
  simp [xnorExpr, evalPure2, readSignal, ha, hb, Res.ok_bind]

/-! ## 4. The design -/

/-- The declaration scope: `N` bound, an `int` parameter. -/
def xnorScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment (with the packed-array geometry table, as `instantiate2` carries it). -/
def xnorEnv (N : Int) : IEnv :=
  { xnorScope N with dims := dimTable (xnorScope N) xnor_n.pdesign.decls }

/-- Declarations at raw width `|N-1| + 1` (all three ports are `[N-1:0]`). -/
def xnorDeclsRaw (wv : Nat) : List Decl :=
  [{ name := "a", width := wv, isInput := true },
   { name := "b", width := wv, isInput := true },
   { name := "y", width := wv, isOutput := true }]

def xnorElems : List (String × Nat) := [("a", 1), ("b", 1), ("y", 1)]

theorem xnor_paramEnv (N : Int) : xnor_n.pdesign.paramEnv2 [N] = .ok (xnorEnv N) := rfl

theorem xnor_decls (N : Int) :
    buildDecls (xnorEnv N) xnor_n.pdesign.decls = .ok (xnorDeclsRaw ((N - 1).natAbs + 1)) := by
  simp [xnor_n.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    xnorEnv, xnorScope, List.lookup, xnorDeclsRaw, Gen2.except_ok_bind]

theorem xnor_elems (N : Int) :
    buildElems (xnorEnv N) xnor_n.pdesign.decls = .ok xnorElems := by
  simp [xnor_n.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, xnorEnv,
    xnorScope, List.lookup, xnorElems, Gen2.except_ok_bind]

/-- The one source process, instantiated at any width. -/
theorem xnor_static (N : Nat) (wv : Nat) :
    xnor_n.pdesign.processes.map
        (instProcess2 ((xnorEnv N).withDecls (xnorDeclsRaw wv)) xnorElems) =
      [.assign (.ident "y") xnorExpr] := by
  sv2_inst_simp [xnor_n.pdesign, xnorEnv, xnorScope, xnorDeclsRaw, xnorElems, xnorExpr, dimTable,
    dimTableStep, PType.width_packed_cons, PDim.width, Int.lt_add_one_iff, rigidMax2,
    selfWidth2, IEnv.withDecls, List.lookup]

/-- **`instantiate2` at symbolic `N`**: succeeds (no generate items), and is the assembled design. -/
theorem xnor_instantiate2 (N : Nat) :
    xnor_n.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (xnor_n.pdesign.assemble2 (xnorEnv N) (xnorDeclsRaw (((N : Int) - 1).natAbs + 1))
        xnorElems []) :=
  PDesign.instantiate2_of_ok rfl (xnor_paramEnv N) (xnor_decls N) (xnor_elems N) (by
    rw [show xnor_n.pdesign.generates = [] from rfl]
    exact expandList2_nil)

/-- **The instantiated process list, for every `N`**: the one assignment `y = ~(a ^ b)`. -/
theorem xnor_processes (N : Nat) :
    (xnor_n.pdesign.instantiateD2 [(N : Int)]).processes.toList = [.assign (.ident "y") xnorExpr] := by
  rw [PDesign.instantiateD2_of_ok (xnor_instantiate2 N), PDesign.assemble2_processes, xnor_static]
  simp [xnor_n.pdesign]

/-- The one-driver rule holds for every `N`: `y` is driven once, by a continuous assignment, and
is not an input port. -/
theorem xnor_driversOk :
    driversOk xnor_n.pdesign.declNames xnor_n.pdesign.inputNames
      [.assign (.ident "y") xnorExpr] = true := by
  have hd : xnor_n.pdesign.declNames = ["a", "b", "y"] := rfl
  have hi : xnor_n.pdesign.inputNames = ["a", "b"] := rfl
  rw [hd, hi]
  apply driversOk_of_continuous
  · rfl
  · simp [driverWins, Process2.drvWins, Lhs2.drvWins, DrvWin.overlaps]
  · intro w hw
    simp [driverWins, Process2.drvWins, Lhs2.drvWins] at hw
    subst hw
    rfl

/-- **`xnor_n.sem N` is the instantiated design**, for every `N`. -/
theorem xnor_sem_eq (N : Nat) :
    xnor_n.sem N = xnor_n.pdesign.instantiateD2 [(N : Int)] := by
  show xnor_n.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [xnor_processes]
  exact xnor_driversOk

/-- **The design is `y = ~(a ^ b)` for every `N`**: with `xnor_eval` and `xnor_vec` the settled value of
`y` is the bitwise Table 11-14 of `a` and `b` at every width. -/
theorem xnor_n_processes (N : Nat) :
    (xnor_n.sem N).processes.toList = [.assign (.ident "y") xnorExpr] := by
  rw [xnor_sem_eq]
  exact xnor_processes N

-- non-vacuity: the default point, concretely
#guard (xnor_n.sem 4).processes.size == 1
#guard (xnor_n.sem 4).decls.toList.map (·.width) == [4, 4, 4]

/-- info: 'Examples.«system-verilog».xnor_n.proof.xnor_n_processes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xnor_n_processes

/-- info: 'Examples.«system-verilog».xnor_n.proof.xnor_vec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xnor_vec

/-- info: 'Examples.«system-verilog».xnor_n.proof.xnor_vec_unknown' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xnor_vec_unknown

/-- info: 'Examples.«system-verilog».xnor_n.proof.xnor_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xnor_known

end Examples.«system-verilog».xnor_n.proof
