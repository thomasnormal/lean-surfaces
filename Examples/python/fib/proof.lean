/-
Proof module for `Examples/python/fib/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.fib.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication. `fibSpec` is deliberately defined at the ROOT
namespace here (not duplicated in spec.lean): the twin statements must
mention the *same* constant — a recursive definition, unlike the program
literals, would not bridge by unfolding.
-/
import LeanModels

namespace Examples.python.fib.proof

open LeanModels LeanModels.Python

load_program fib from "Examples/python/fib/fib.json"

/-- Mathematical Fibonacci: `0, 1, 1, 2, 3, 5, …`. -/
def _root_.fibSpec : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec (n + 1) + fibSpec n

private def fibBound : Nat → Nat
  | 0 => 1
  | n + 1 => n + 1

/-! Recursive calls execute one frame below their caller.  This helper keeps
the active depth explicit; the public arrow below is obtained by instantiating
it at depth zero and applying the ordinary boundary wrapper. -/
set_option maxHeartbeats 1200000 in
private theorem fib_depth (d n : Nat)
    (hlim : d + fibBound n + 1 < pythonRecursionLimit) :
    ∃ f₀, ∀ F, f₀ ≤ F →
      callIn fib F ({heap := #[], globals := [], callDepth := d} : World)
        "fib" #[.int (n : Int)] =
      .ok ({heap := #[], globals := [], callDepth := d} : World)
        (.int (fibSpec n)) := by
  induction n using Nat.strongRecOn generalizing d with
  | ind n ih =>
    match n with
    | 0 | 1 =>
      by_cases hz : d = 0
      · subst d
        refine ⟨32, ?_⟩
        intro F hF
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hF
        subst hc
        rw [Nat.add_comm, callIn.eq_2]
        py_simp [fib, fibSpec, pythonTopCallDepth, pythonRecursionLimit,
          Run.finishCallAt, Run.leaveCallDepth, Run.toPublic,
          Run.toPublic_ok, RVal.freezeB]
      · have hd : 0 < d := by omega
        have htop : d ≠ pythonTopCallDepth := by
          intro h; simp [pythonTopCallDepth, pythonRecursionLimit] at h hlim; omega
        have hguard : ¬ (999 ≤ d) := by
          simp [fibBound, pythonRecursionLimit] at hlim ⊢; omega
        have hcompare : ¬ (998 ≤ d) := by
          simp [fibBound, pythonRecursionLimit] at hlim; omega
        refine ⟨32, ?_⟩
        intro F hF
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hF
        subst hc
        rw [Nat.add_comm, callIn.eq_2]
        py_simp [fib, fibSpec, hz, hd, htop, hguard, hcompare,
          pythonTopCallDepth, pythonRecursionLimit, Run.finishCallAt,
          Run.leaveCallDepth, Run.toPublic, Run.toPublic_ok, RVal.freezeB]
    | n + 2 =>
      have hstep : d + 1 + fibBound n + 1 < pythonRecursionLimit := by
        cases n with
        | zero => simp [fibBound] at hlim ⊢; omega
        | succ n => simp [fibBound] at hlim ⊢; omega
      obtain ⟨f₁, h₁⟩ := ih (n + 1) (by omega) (d + 1) (by
        simp [fibBound] at hlim ⊢; omega)
      obtain ⟨f₂, h₂⟩ := ih n (by omega) (d + 1) hstep
      by_cases hz : d = 0
      · have hz0 : d = 0 := hz
        refine ⟨f₁ + f₂ + 32, ?_⟩
        intro F hF
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hF
        subst hc
        rw [Nat.add_comm]
        have hs : c + (f₁ + f₂ + 32) = Nat.succ (c + (f₁ + f₂ + 31)) := by omega
        rw [hs, callIn.eq_2]
        have hn1 : (n : Int) + 2 - 1 = (n : Int) + 1 := by omega
        have hn2 : (n : Int) + 2 - 2 = (n : Int) := by omega
        have h₁' := h₁ (c + (f₁ + f₂ + 26)) (by omega)
        have h₂' := h₂ (c + (f₁ + f₂ + 26)) (by omega)
        simp only [fib] at h₁' h₂'
        have h₁'' : callIn fib (c + (f₁ + f₂ + 26))
            ({heap := #[], globals := [], callDepth := 1} : World)
            "fib" #[.int ((n : Int) + 1)] =
            .ok ({heap := #[], globals := [], callDepth := 1} : World)
            (.int (fibSpec (n + 1))) := by simpa [fib, Nat.zero_add, hz0] using h₁'
        have h₂'' : callIn fib (c + (f₁ + f₂ + 26))
            ({heap := #[], globals := [], callDepth := 1} : World)
            "fib" #[.int (n : Int)] =
            .ok ({heap := #[], globals := [], callDepth := 1} : World)
            (.int (fibSpec n)) := by simpa [fib, Nat.zero_add, hz0] using h₂'
        simp only [fib] at h₁'' h₂''
        py_simp [fib, fibSpec, hz0, hn1, hn2,
          show ¬((n : Int) + 2 < 2) by omega, h₁'', h₂'',
          pythonTopCallDepth, pythonRecursionLimit, Run.finishCallAt,
          Run.leaveCallDepth, Run.toPublic, Run.toPublic_ok, RVal.freezeB,
          evalBinOpH, PyVCGen.binOpBeqBitAnd, PyVCGen.binOpBeqMult,
          setLikeRefH, funsHeapFree, FunctionDefn.heapFree,
          Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList,
          Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
          moduleGenFree, funsGenAllocFree, Stmt.genAllocFree,
          Stmt.genAllocFreeList, Run.bind, Run.liftRes,
          starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
          fstringFormatBuiltinName, flattenStarRun, flattenStarCallArgs,
          RVal.thawList, RVal.thawList_eq_map, RVal.thawArgs,
          List.flatMap, List.map, Array.mk]
      · have hd : 0 < d := by omega
        have htop : d ≠ pythonTopCallDepth := by
          intro h; simp [pythonTopCallDepth, pythonRecursionLimit] at h hlim; omega
        have htopb : (d == pythonTopCallDepth) = false :=
          beq_eq_false_iff_ne.mpr htop
        have htop1001 : d ≠ 1001 := by
          intro h; apply htop; simpa [pythonTopCallDepth, pythonRecursionLimit] using h
        have hguard : ¬ (999 ≤ d) := by
          have hd2 : d + 2 < pythonRecursionLimit := by
            cases n with
            | zero => simp [fibBound] at hlim ⊢; omega
            | succ n => simp [fibBound] at hlim ⊢; omega
          simp [pythonRecursionLimit] at hd2 ⊢; omega
        have hcompare : ¬ (998 ≤ d) := by
          cases n with
          | zero => simp [fibBound, pythonRecursionLimit] at hlim; omega
          | succ n => simp [fibBound, pythonRecursionLimit] at hlim; omega
        refine ⟨f₁ + f₂ + 32, ?_⟩
        intro F hF
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hF
        subst hc
        rw [Nat.add_comm]
        have hs : c + (f₁ + f₂ + 32) = Nat.succ (c + (f₁ + f₂ + 31)) := by omega
        rw [hs, callIn.eq_2]
        have hn1 : (n : Int) + 2 - 1 = (n : Int) + 1 := by omega
        have hn2 : (n : Int) + 2 - 2 = (n : Int) := by omega
        have h₁' := h₁ (c + (f₁ + f₂ + 26)) (by omega)
        have h₂' := h₂ (c + (f₁ + f₂ + 26)) (by omega)
        simp only [fib] at h₁' h₂'
        have h₁'' : callIn fib (c + (f₁ + f₂ + 26))
            ({heap := #[], globals := [], callDepth := d + 1} : World)
            "fib" #[.int ((n : Int) + 1)] =
            .ok ({heap := #[], globals := [], callDepth := d + 1} : World)
            (.int (fibSpec (n + 1))) := by simpa [fib] using h₁'
        have h₂'' : callIn fib (c + (f₁ + f₂ + 26))
            ({heap := #[], globals := [], callDepth := d + 1} : World)
            "fib" #[.int (n : Int)] =
            .ok ({heap := #[], globals := [], callDepth := d + 1} : World)
            (.int (fibSpec n)) := by simpa [fib] using h₂'
        simp only [fib] at h₁'' h₂''
        py_simp [fib, fibSpec, hz, hd, htop, htopb, htop1001, hguard, hcompare, hn1, hn2,
          show ¬((n : Int) + 2 < 2) by omega,
          pythonTopCallDepth, pythonRecursionLimit, Run.finishCallAt,
          Run.leaveCallDepth, Run.toPublic, Run.toPublic_ok, RVal.freezeB,
          evalBinOpH, PyVCGen.binOpBeqBitAnd, PyVCGen.binOpBeqMult,
          setLikeRefH, funsHeapFree, FunctionDefn.heapFree,
          Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList,
          Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
          moduleGenFree, funsGenAllocFree, Stmt.genAllocFree,
          Stmt.genAllocFreeList, Run.bind, Run.liftRes,
          starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
          fstringFormatBuiltinName, flattenStarRun, flattenStarCallArgs,
          RVal.thawList, RVal.thawList_eq_map, RVal.thawArgs,
          List.flatMap, List.map, Array.mk]
        py_simp [evalExprs, evalExpr, RVal.thawList, RVal.thawList_eq_map,
          flattenStarRun, flattenStarCallArgs, Run.bind, Run.withLocals,
          h₁'', h₂'',
          Run.toWorld, Run.liftRes]

-- H7 note: the `.call` arm's equation now carries the keyword tier and
-- the guarded closure dispatch; fib's whole-body symbolic step crosses
-- it twice, which pushed this proof past the default heartbeat budget
-- (a constant-factor cost, not a loop).
set_option maxHeartbeats 800000 in
set_option warning.simp.varHead false in
/-- **Total correctness**, by strong induction on the mathematical argument
(never on fuel). The base cases are straight-line runs (`py_prove`); in the
step case `py_lift` puts the two IH runs in fuel-threshold form
(`CallsTo.at_least`, i.e. FuelMono), so a single symbolic execution of the
body closes the goal by conditional rewriting. -/
theorem fib_total (k : Nat) (hk : k + 1 < pythonRecursionLimit) : fib(k) ==> fibSpec k := by
  obtain ⟨f₀, hf⟩ := fib_depth 0 k (by
    cases k with
    | zero => simp [fibBound, pythonRecursionLimit]
    | succ k => simpa [fibBound] using hk)
  refine ⟨f₀, ?_⟩
  unfold callFunction
  have hinit : initWorld fib = ({heap := #[], globals := []} : World) := by rfl
  have hargs : RVal.thawArgs #[ToVal.toVal k] = #[.int (k : Int)] := by rfl
  rw [hinit, hargs]
  rw [hf f₀ (Nat.le_refl f₀)]
  simp [pythonTopCallDepth, pythonRecursionLimit, Run.finishCallAt,
    Run.leaveCallDepth, Run.toPublic, Run.toPublic_ok, RVal.freezeB]

set_option warning.simp.varHead false in
/-- Determinism corollary of `fib_total` — one `py_corollary`
(Surface.lean), instantiated at `n.toNat` (the total theorem is
`Nat`-indexed). -/
theorem fib_spec (n : Int) (hn : 0 ≤ n)
    (hnDepth : n.toNat + 1 < pythonRecursionLimit) {fuel : Nat} {r : Val}
    (h : callFunction fib "fib" #[.int n] fuel = .ok r) :
    r = .int (fibSpec n.toNat) := by
  py_corollary [fib_total n.toNat hnDepth]

set_option warning.simp.varHead false in
/-- The typed surface form, another `py_corollary` of `fib_total`. -/
theorem fib_correct (n r : PyInt) (hn : 0 ≤ n)
    (hnDepth : n.toNat + 1 < pythonRecursionLimit) (h : fib(n) ⇓ r) :
    r = fibSpec n.toNat := by
  py_corollary [fib_total n.toNat hnDepth]

end Examples.python.fib.proof
