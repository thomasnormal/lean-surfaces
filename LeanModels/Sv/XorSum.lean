import LeanModels.Sv.Known2
import LeanModels.Sv.PinAxioms

/-!
# The XOR-sum calculus (WS3 plan item E): untrusted library lemmas

What a proof about an XOR-accumulating loop (carry-less products, parities, GF(2) arithmetic) keeps
re-proving: `bx f n`, the XOR of `f 0, …, f (n-1)`, its `List.range` fold, and the value of one
XOR-accumulate trip on known vectors (`andBit_known`, `xorBit_known`: bit `k` flips by the known
bit). Generic: nothing here mentions a design. Imported by nothing in `LeanModels`.
-/

namespace LeanModels.Sv.XorSum

/-- `bx f n`: the XOR of `f 0, …, f (n-1)`. -/
def bx (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bx f n ^^ f n

/-- A `List.range` XOR fold is `bx`. -/
theorem foldl_xor (f : Nat → Bool) (n : Nat) (acc : Bool) :
    (List.range n).foldl (fun acc i => acc ^^ f i) acc = (acc ^^ bx f n) := by
  induction n generalizing acc with
  | zero => simp [bx]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    simp only [bx]
    cases acc <;> cases bx f n <;> cases f n <;> rfl

/-- The AND of two known bits, read off two known vectors. -/
theorem andBit_known {N M : Nat} (x : BitVec N) (y : BitVec M) {i j : Nat} (hi : i < N) (hj : j < M) :
    evalBinOp .and ((LVec.ofBitVec x).extract i 1) ((LVec.ofBitVec y).extract j 1) =
      LVec.ofBitVec (BitVec.ofBool (x.getLsbD i && y.getLsbD j)) := by
  rw [evalBinOp_and, LVec.extract_one_ofBitVec x hi, LVec.extract_one_ofBitVec y hj,
    LVec.and_ofBitVec]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  obtain rfl : k = 0 := by omega
  simp

/-- **XOR-accumulating a known bit into bit `k`** of a known vector (`v[k] = v[k] ^ b`): bit `k`
flips by `b`, every other bit stays. -/
theorem xorBit_known {W : Nat} (z : BitVec W) {k : Nat} (hk : k < W) (b : Bool) :
    ∃ z' : BitVec W, (LVec.ofBitVec z).insertAt k ((evalBinOp .xor ((LVec.ofBitVec z).extract k 1)
        (LVec.ofBitVec (BitVec.ofBool b))).resizeU 1) = LVec.ofBitVec z' ∧
      ∀ m, m < W → z'.getLsbD m = if m = k then (z.getLsbD m ^^ b) else z.getLsbD m := by
  refine ⟨bvInsertAt z k ((BitVec.ofBool (z.getLsbD k) ^^^ BitVec.ofBool b).setWidth 1), ?_,
    fun m hm => ?_⟩
  · simp only [evalBinOp_xor, LVec.extract_one_ofBitVec z hk, LVec.xor_ofBitVec,
      LVec.resizeU_ofBitVec, LVec.insertAt_ofBitVec]
  · rw [getLsbD_bvInsertAt _ _ _ hm]
    by_cases h : m = k
    · subst h; simp
    · rw [if_neg (by omega), if_neg h]

end LeanModels.Sv.XorSum

#pin_axioms LeanModels.Sv.XorSum.foldl_xor LeanModels.Sv.XorSum.andBit_known
  LeanModels.Sv.XorSum.xorBit_known
