import Lean
import LeanModels.Sv.CombView

/-!
# `sv_structure`: the condition of a conditional generate construct, as the instantiation evaluates it

`GenItem.expand2` selects an arm of `if (c) … else …` by `evalGenGuard env c` (`Param.lean`): the condition typed
(`ctype`) and evaluated at its type (`evalAt`), IEEE 1800-2023 §11.6.1, §11.8.2. For a comparison `l op r` of two `int`
operands (a guard, `guardOf?`) that is the comparison of the operands evaluated at the signed 32-bit type, each
operation wrapped to 32 bits; `guard_eval` shows it is the guard's comparison of the operands' affine values, where the
genvars and parameters the operands read have their values in the environment and every subterm's affine value is a
32-bit value (`Guard.rngs`, owed by `AutoObl`). Nothing about the instantiation is assumed: the lemmas compute
`evalGenGuard` itself.

`evalAt` computes through helpers that `Param.lean` keeps private (`constArith`, `constCompare`, `b2i`, the signedness
checks of a comparison); `unfold_param_private` unfolds them definitionally by name, as the tactics' `liftCond` does.
-/

namespace LeanModels.Sv
namespace CombView

open Lean Meta Elab Tactic in
/-- Unfold, definitionally, the private helpers of `Param.lean` that `evalAt` computes through: the arithmetic and the
comparison of a constant expression and the signedness checks of a comparison. -/
elab "unfold_param_private" : tactic => do
  let nms := [`LeanModels.Sv.constArith, `LeanModels.Sv.constCompare, `LeanModels.Sv.b2i,
      `LeanModels.Sv.SymBinOp.signedOrder, `LeanModels.Sv.SymBinOp.unsignedOrder].map fun n =>
    Name.append ((`_private ++ `LeanModels.Sv.Param).num 0) n
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (pre := fun e => do
    if nms.any (e.isAppOf ·) then
      if let some e' ← unfoldDefinition? e then return .visit (← whnfCore e')
    return .continue)
  replaceMainGoal [← g.change t']

theorem canonInt_emod32 (v : Int) : canonInt 32 true (v.emod ((2 : Int) ^ 32)) = canonInt 32 true v := by
  have e : Int.emod (Int.emod v ((2 : Int) ^ 32)) ((2 : Int) ^ 32) = Int.emod v ((2 : Int) ^ 32) :=
    Int.emod_emod v _
  unfold canonInt
  rw [e]

theorem canonInt32_id {v : Int} (h : -2147483648 ≤ v ∧ v < 2147483648) : canonInt 32 true v = v :=
  canonInt32_of_range h

/-- A 32-bit value converted to the signed 32-bit type is itself. -/
theorem convertConst32 {v : Int} (h : -2147483648 ≤ v ∧ v < 2147483648) : convertConst 32 32 true v = v := by
  unfold convertConst
  simp only [if_true, canonInt_emod32, canonInt32_id h]

/-- A 0/1 value converted to the 1-bit unsigned type is itself. -/
theorem convertConst1_ite (p : Prop) [Decidable p] :
    convertConst 1 1 false (if p then 1 else 0) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, convertConst, canonInt] <;> decide

/-- **An affine operand evaluates to its affine value at the signed 32-bit type**, where the genvars it reads are bound
in `vals`, the parameters agree, and every subterm's value is a 32-bit value. -/
theorem opd_eval {E : IEnv} {σ : String → Int} :
    ∀ (e : PExpr) (a : Aff) (rs : List Aff), opdAffs? e = some (a, rs) →
      (∀ n ∈ e.gvLeaves, E.vals.lookup n = some (σ n)) → (∀ n ∈ e.pLeaves, E.intVal? n = some (σ n)) →
      (∀ r ∈ rs, -2147483648 ≤ r.eval σ ∧ r.eval σ < 2147483648) →
      ctype E e = .ok (32, true) ∧ evalAt E (32, true) e = .ok (a.eval σ)
  | .int v, a, rs, h, _, _, hr => by
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := hr _ (List.mem_singleton_self _)
      simp only [Aff.eval_const] at hv ⊢
      refine ⟨rfl, ?_⟩
      simp only [evalAt, convertConst32 hv]
  | .genvarRef n, a, rs, h, hg, _, hr => by
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := hr _ (List.mem_singleton_self _)
      simp only [Aff.eval_var] at hv ⊢
      have hl := hg n (by simp [PExpr.gvLeaves])
      refine ⟨rfl, ?_⟩
      simp only [evalAt, hl, convertConst32 hv]
  | .paramRef n none, a, rs, h, _, hp, hr => by
      simp only [opdAffs?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hv := hr _ (List.mem_singleton_self _)
      simp only [Aff.eval_var] at hv ⊢
      have hi := hp n (by simp [PExpr.pLeaves])
      cases hx : E.vals.lookup n with
      | some x =>
          have : x = σ n := by simpa [IEnv.intVal?, hx] using hi
          subst this
          exact ⟨by simp [ctype, hx], by simp [evalAt, hx, convertConst32 hv]⟩
      | none =>
          rcases IEnv.intVal?_cases hi with hl | ⟨w, s, hn, rfl, rfl⟩
          · rw [hx] at hl; cases hl
          · exact ⟨by simp [ctype, hx, hn], by simp [evalAt, hx, hn, convertConst32 hv]⟩
  | .binary op l r, a, rs, h, hg, hp, hr => by
      simp only [opdAffs?] at h
      rcases hla : opdAffs? l with _ | ⟨al, ral⟩
      · simp [hla] at h
      rcases hra : opdAffs? r with _ | ⟨ar, rar⟩
      · simp [hla, hra] at h
      simp only [hla, hra] at h
      have hgl : ∀ n ∈ l.gvLeaves, E.vals.lookup n = some (σ n) :=
        fun n hn => hg n (by simp [PExpr.gvLeaves, hn])
      have hgr : ∀ n ∈ r.gvLeaves, E.vals.lookup n = some (σ n) :=
        fun n hn => hg n (by simp [PExpr.gvLeaves, hn])
      have hpl : ∀ n ∈ l.pLeaves, E.intVal? n = some (σ n) :=
        fun n hn => hp n (by simp [PExpr.pLeaves, hn])
      have hpr : ∀ n ∈ r.pLeaves, E.intVal? n = some (σ n) :=
        fun n hn => hp n (by simp [PExpr.pLeaves, hn])
      -- the operands' subterms are among `rs`
      have hsub : ∀ {c : Aff}, rs = ral ++ rar ++ [c] →
          (ctype E l = .ok (32, true) ∧ evalAt E (32, true) l = .ok (al.eval σ)) ∧
          (ctype E r = .ok (32, true) ∧ evalAt E (32, true) r = .ok (ar.eval σ)) ∧
          (-2147483648 ≤ c.eval σ ∧ c.eval σ < 2147483648) := by
        intro c hrs
        subst hrs
        exact ⟨opd_eval l al ral hla hgl hpl (fun x hx => hr x (by simp [hx])),
          opd_eval r ar rar hra hgr hpr (fun x hx => hr x (by simp [hx])),
          hr c (by simp)⟩
      cases op with
      | m0 bop =>
          cases bop with
          | add =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, hrs⟩ := h
              obtain ⟨⟨hcl, hel⟩, ⟨hcr, her⟩, hc⟩ := hsub hrs.symm
              rw [Aff.eval_add] at hc ⊢
              refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
              simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
              unfold_param_private
              rw [canonInt32_id hc]
          | sub =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, hrs⟩ := h
              obtain ⟨⟨hcl, hel⟩, ⟨hcr, her⟩, hc⟩ := hsub hrs.symm
              rw [Aff.eval_sub] at hc ⊢
              refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
              simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
              unfold_param_private
              rw [canonInt32_id hc]
          | mul =>
              rcases hm : affMul al ar with _ | c
              · simp [hm] at h
              simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, hrs⟩ := h
              obtain ⟨⟨hcl, hel⟩, ⟨hcr, her⟩, hc⟩ := hsub hrs.symm
              rw [affMul_eval σ hm] at hc ⊢
              refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
              simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
              unfold_param_private
              rw [canonInt32_id hc]
          | _ => simp at h
      | mul =>
          rcases hm : affMul al ar with _ | c
          · simp [hm] at h
          simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, hrs⟩ := h
          obtain ⟨⟨hcl, hel⟩, ⟨hcr, her⟩, hc⟩ := hsub hrs.symm
          rw [affMul_eval σ hm] at hc ⊢
          refine ⟨by simp only [ctype, SymBinOp.constClass, hcl, hcr]; rfl, ?_⟩
          simp only [evalAt, SymBinOp.constClass, hel, her, Gen2.except_ok_bind]
          unfold_param_private
          rw [canonInt32_id hc]
      | _ => simp at h
  | .paramRef _ (some _), _, _, h, _, _, _ => by simp [opdAffs?] at h
  | .lit _, _, _, h, _, _, _ | .ident _, _, _, h, _, _, _ | .enumRef .., _, _, h, _, _, _
  | .unary .., _, _, h, _, _, _ | .ternary .., _, _, h, _, _, _ | .bitSel .., _, _, h, _, _, _
  | .partSel .., _, _, h, _, _, _ | .arrayElem .., _, _, h, _, _, _ | .arrayPart .., _, _, h, _, _, _
  | .fill _, _, _, h, _, _, _ | .concat _, _, _, h, _, _, _ | .repl .., _, _, h, _, _, _
  | .reduce .., _, _, h, _, _, _ | .resize .., _, _, h, _, _, _ | .signedResize .., _, _, h, _, _, _
  | .squash2 .., _, _, h, _, _, _ | .sysCall .., _, _, h, _, _, _ | .cast .., _, _, h, _, _, _
  | .unsupported .., _, _, h, _, _, _ | .functionCall .., _, _, h, _, _, _ => by simp [opdAffs?] at h

/-- **The instantiation's value of a generate condition** (`evalGenGuard`): `1` where the guard holds, `0` where it
does not, when the genvars its operands read are bound in `vals`, the parameters agree, and every subterm of the
operands is a 32-bit value. -/
theorem guard_eval {E : IEnv} {σ : String → Int} {c : PExpr} {g : Guard} (hg : guardOf? c = some g)
    (hgv : ∀ n ∈ c.gvLeaves, E.vals.lookup n = some (σ n)) (hpv : ∀ n ∈ c.pLeaves, E.intVal? n = some (σ n))
    (hr : ∀ a ∈ g.rngs, -2147483648 ≤ a.eval σ ∧ a.eval σ < 2147483648) :
    evalGenGuard E c = .ok (if g.holds σ then 1 else 0) := by
  cases c with
  | binary op l r =>
      simp only [guardOf?] at hg
      rcases hc : gcmpOf? op with _ | cmp
      · simp [hc] at hg
      rcases hla : opdAffs? l with _ | ⟨al, ral⟩
      · simp [hc, hla] at hg
      rcases hra : opdAffs? r with _ | ⟨ar, rar⟩
      · simp [hc, hla, hra] at hg
      simp only [hc, hla, hra, Option.some.injEq] at hg
      subst hg
      obtain ⟨hcl, hel⟩ := opd_eval l al ral hla (fun n hn => hgv n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hpv n (by simp [PExpr.pLeaves, hn])) (fun x hx => hr x (by simp [hx]))
      obtain ⟨hcr, her⟩ := opd_eval r ar rar hra (fun n hn => hgv n (by simp [PExpr.gvLeaves, hn]))
        (fun n hn => hpv n (by simp [PExpr.pLeaves, hn])) (fun x hx => hr x (by simp [hx]))
      cases op with
      | slt =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : al.eval σ < ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | sle =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : al.eval σ ≤ ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | sgt =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : ar.eval σ < al.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | sge =>
          simp only [gcmpOf?, Option.some.injEq] at hc
          subst hc
          simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
          unfold_param_private
          simp only [hel, her, Gen2.except_ok_bind]
          by_cases h : ar.eval σ ≤ al.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
      | m0 bop =>
          cases bop with
          | eq =>
              simp only [gcmpOf?, Option.some.injEq] at hc
              subst hc
              simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
              unfold_param_private
              simp only [hel, her, Gen2.except_ok_bind]
              by_cases h : al.eval σ = ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
          | ne =>
              simp only [gcmpOf?, Option.some.injEq] at hc
              subst hc
              simp only [evalGenGuard, ctype, evalAt, SymBinOp.constClass, hcl, hcr]
              unfold_param_private
              simp only [hel, her, Gen2.except_ok_bind]
              by_cases h : al.eval σ = ar.eval σ <;> simp [h, hel, her, Gen2.except_ok_bind, Guard.holds, GCmp.holds, convertConst, canonInt] <;> rfl
          | _ => simp [gcmpOf?] at hc
      | _ => simp [gcmpOf?] at hc
  | _ => simp [guardOf?] at hg

end CombView
end LeanModels.Sv
