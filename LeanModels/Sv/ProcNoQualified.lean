import LeanModels.Sv.Hier2Gen

/-!
# No qualified `case` in a design family `X.sem N`

`Runs2.lowerComb_iff` and the theorems built on it (`Terminates2.of_lowerComb_acyclic`,
`Models2.of_combProc_inputs`, …, `Comb2Proc.lean`) ask for

    hnq : d.processes.toList.any Process2.hasQualifiedCase = false

about the SOURCE design `d` (since qualified `case` violations are loud, `run2` validates
`unique`/`unique0`/`priority` cases first when a design has one). For a hand-built design that is
`rfl`; for a design family `X.sem N = X.pdesign.instantiateGD2 [↑N]` the process list depends on
`N` (generate loops), so it does not reduce. This module derives `hnq` at EVERY parameter point
from a static check on the parametric design:

* `NoQ.pdQ d` — every `case` statement of every process and generate item of `d` is a plain one
  (`check = .none`); a closed Boolean on the literal `X.pdesign`, decided by `decide` (or
  `decide +kernel` for a large body);
* `NoQ.sem_noQ` — `pdQ d = true → (d.instantiateGD2 args).processes.toList.any
  Process2.hasQualifiedCase = false`, for all `args`.

The proof follows the instantiation: a statement keeps its `case` checks (`instStmt2`), a process
keeps its body or becomes loud (`instProcess2`, `combGuardProc`), generate expansion only collects
instantiated processes (`GenItem.expand2`), and the error design and the driver guard add only
`unsupported` processes. The proofs use `simp only` with explicit lemma lists.
-/

namespace LeanModels.Sv
namespace NoQ

/-! ## The static check -/

mutual
/-- Every `case` in a parametric statement is plain (`check = .none`). -/
def stmtQ : PStmt → Bool
  | .ifStmt _ t e => stmtQ t && optQ e
  | .block b => listQ b
  | .forLoop _ _ _ _ b => stmtQ b
  | .caseStmt _ its dflt _ check => check == .none && itemsQ its && optQ dflt
  | _ => true
/-- `stmtQ` of an optional statement. -/
def optQ : Option PStmt → Bool
  | none => true
  | some s => stmtQ s
/-- `stmtQ` of a statement list. -/
def listQ : List PStmt → Bool
  | [] => true
  | s :: ss => stmtQ s && listQ ss
/-- `stmtQ` of the bodies of `case` items. -/
def itemsQ : List (List PExpr × PStmt) → Bool
  | [] => true
  | (_, s) :: rest => stmtQ s && itemsQ rest
end

/-- `stmtQ` of a process body (assigns and loud processes have none). -/
def procQ : PProcess → Bool
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b | .alwaysFFR _ _ b => stmtQ b
  | _ => true

mutual
/-- `procQ` of every process of a generate item. -/
def genQ : GenItem → Bool
  | .process p => procQ p
  | .genFor _ _ _ _ _ _ b => gensQ b
  | .genIf _ t e => gensQ t && gensQ e
  | _ => true
/-- `genQ` of a generate item list. -/
def gensQ : List GenItem → Bool
  | [] => true
  | it :: rest => genQ it && gensQ rest
end

/-- **The static check of a parametric design**: no qualified `case` in any process or generate
item. -/
def pdQ (d : PDesign) : Bool := d.processes.all procQ && gensQ d.generates

/-! ## Instantiation keeps it -/

theorem listHQ : ∀ {l : List Stmt2}, (∀ s ∈ l, s.hasQualifiedCase = false) →
    Stmt2.listHasQualifiedCase l = false
  | [], _ => rfl
  | s :: ss, h => by
      have ih : Stmt2.listHasQualifiedCase ss = false :=
        listHQ fun t ht => h t (List.mem_cons_of_mem s ht)
      simp only [Stmt2.listHasQualifiedCase, h s (List.mem_cons_self ..), ih, Bool.or_false]

mutual
theorem stmtQ_inst (elems : List (String × Nat)) : ∀ (env : IEnv) (s : PStmt), stmtQ s = true →
    (instStmt2 env elems s).hasQualifiedCase = false
  | env, .ifStmt c t none, h => by
      simp only [stmtQ, optQ, Bool.and_true] at h
      simp only [instStmt2, Stmt2.hasQualifiedCase, stmtQ_inst elems env t h, Bool.or_false]
  | env, .ifStmt c t (some e), h => by
      simp only [stmtQ, optQ, Bool.and_eq_true] at h
      simp only [instStmt2, Stmt2.hasQualifiedCase, stmtQ_inst elems env t h.1,
        stmtQ_inst elems env e h.2, Bool.or_false]
  | env, .block b, h => by
      simp only [instStmt2, Stmt2.hasQualifiedCase]
      exact listQ_inst elems env b h
  | env, .forLoop it i c st b, h => by
      simp only [instStmt2]; split
      · simp only [Stmt2.hasQualifiedCase]
        exact listHQ (by simp only [List.mem_map]; rintro _ ⟨v, -, rfl⟩; exact stmtQ_inst elems _ b h)
      all_goals rfl
  | env, .caseStmt subj its none mode check, h => by
      simp only [stmtQ, optQ, Bool.and_true, Bool.and_eq_true] at h
      simp only [instStmt2]; split
      · rfl
      · simp only [Stmt2.hasQualifiedCase, bne, h.1, Bool.not_true,
          itemsQ_inst elems env _ its h.2, Bool.or_false]
  | env, .caseStmt subj its (some d) mode check, h => by
      simp only [stmtQ, optQ, Bool.and_eq_true] at h
      simp only [instStmt2]; split
      · rfl
      · simp only [Stmt2.hasQualifiedCase, bne, h.1.1, Bool.not_true,
          itemsQ_inst elems env _ its h.1.2, stmtQ_inst elems env d h.2, Bool.or_false]
  | env, .blockingAssignL l v, _ | env, .nbaAssignL l v, _ => by simp only [instStmt2]; split <;> rfl
  | _, .blockingAssign .., _ | _, .nbaAssign .., _ | _, .unsupported .., _ => rfl
theorem listQ_inst (elems : List (String × Nat)) : ∀ (env : IEnv) (b : List PStmt), listQ b = true →
    Stmt2.listHasQualifiedCase (instStmts2 env elems b) = false
  | _, [], _ => rfl
  | env, s :: ss, h => by
      simp only [listQ, Bool.and_eq_true] at h
      simp only [instStmts2, Stmt2.listHasQualifiedCase, stmtQ_inst elems env s h.1,
        listQ_inst elems env ss h.2, Bool.or_false]
theorem itemsQ_inst (elems : List (String × Nat)) : ∀ (env : IEnv) (sctx : Option Nat)
    (its : List (List PExpr × PStmt)), itemsQ its = true →
    CaseItem2.listHasQualifiedCase (instItems2 env elems sctx its) = false
  | _, _, [], _ => rfl
  | env, sctx, (ps, s) :: rest, h => by
      simp only [itemsQ, Bool.and_eq_true] at h
      simp only [instItems2, CaseItem2.listHasQualifiedCase, stmtQ_inst elems env s h.1,
        itemsQ_inst elems env sctx rest h.2, Bool.or_false]
end

theorem procQ_inst (env : IEnv) (elems : List (String × Nat)) (p : PProcess) (h : procQ p = true) :
    (instProcess2 env elems p).hasQualifiedCase = false := by
  cases p <;> simp only [procQ] at h <;> simp only [instProcess2, combGuardProc] <;>
    (try split) <;> (try split) <;> simp only [Process2.hasQualifiedCase] <;>
    exact stmtQ_inst elems env _ h

/-! ## Generate expansion keeps it -/

theorem itersQ {env : IEnv} {elems : List (String × Nat)} {F : Nat} {g : String} {body : List GenItem}
    (hb : ∀ env ps, expandList2 env elems F body = .ok ps → ∀ p ∈ ps, p.hasQualifiedCase = false) :
    ∀ (vs : List Int) ps, expandIters2 env elems F g vs body = .ok ps →
      ∀ p ∈ ps, p.hasQualifiedCase = false
  | [], ps, h => by
      rw [expandIters2_nil] at h; cases h; exact fun p hp => (List.not_mem_nil hp).elim
  | v :: vs, ps, h => by
      rw [expandIters2_cons] at h
      simp only [Res.bind_eq_ok] at h
      obtain ⟨a, ha, b, hb', hab⟩ := h
      cases hab
      exact fun p hp => (List.mem_append.mp hp).elim (hb _ a ha p) (itersQ hb vs b hb' p)

mutual
theorem genQ_expand {elems : List (String × Nat)} {F : Nat} : ∀ (it : GenItem) (env : IEnv) ps,
    genQ it = true → it.expand2 env elems F = .ok ps → ∀ p ∈ ps, p.hasQualifiedCase = false
  | .process p, env, ps, h, he => by
      rw [GenItem.expand2_process] at he; cases he
      intro q hq; rw [List.mem_singleton] at hq; subst hq; exact procQ_inst env elems p h
  | .unsupported .., _, ps, _, he => by
      rw [GenItem.expand2_unsupported] at he; cases he
      intro q hq; rw [List.mem_singleton] at hq; subst hq; rfl
  | .inst i, _, ps, _, he => by
      rw [GenItem.expand2] at he; cases he
      intro q hq; rw [List.mem_singleton] at hq; subst hq; rfl
  | .genIf c t e, env, ps, h, he => by
      simp only [genQ, Bool.and_eq_true] at h
      rw [GenItem.expand2] at he
      split at he
      · cases he
      · split at he
        · exact gensQ_expand t _ ps h.1 he
        · exact gensQ_expand e _ ps h.2 he
  | .genFor l g i b s rc body, env, ps, h, he => by
      rw [GenItem.expand2] at he
      split at he
      · simp only [Res.bind_eq_ok] at he
        obtain ⟨vs, -, he⟩ := he
        exact itersQ (fun env ps h' => gensQ_expand body env ps h h') vs ps he
      all_goals cases he
theorem gensQ_expand {elems : List (String × Nat)} {F : Nat} : ∀ (l : List GenItem) (env : IEnv) ps,
    gensQ l = true → expandList2 env elems F l = .ok ps → ∀ p ∈ ps, p.hasQualifiedCase = false
  | [], _, ps, _, he => by
      rw [expandList2_nil] at he; cases he; exact fun p hp => (List.not_mem_nil hp).elim
  | it :: rest, env, ps, h, he => by
      simp only [gensQ, Bool.and_eq_true] at h
      rw [expandList2_cons] at he
      simp only [Res.bind_eq_ok] at he
      obtain ⟨a, ha, b, hb, hab⟩ := he
      cases hab
      exact fun p hp => (List.mem_append.mp hp).elim (genQ_expand it env a h.1 ha p)
        (gensQ_expand rest env b h.2 hb p)
end

/-! ## The design family -/

/-- **No qualified `case` in `d.instantiateGD2 args`, at every parameter point**, from the static
check `pdQ d` (the `hnq` hypothesis of `Runs2.lowerComb_iff` and its consumers for `X.sem N`). -/
theorem sem_noQ {d : PDesign} (hq : pdQ d = true) (args : List Int) :
    (d.instantiateGD2 args).processes.toList.any Process2.hasQualifiedCase = false := by
  simp only [pdQ, Bool.and_eq_true, List.all_eq_true] at hq
  have h : ∀ p ∈ (d.instantiateD2 args).processes.toList, p.hasQualifiedCase = false := by
    unfold PDesign.instantiateD2
    split
    · rename_i m hm
      obtain ⟨-, env, decls, elems, gens, -, -, -, h4, rfl⟩ := PDesign.instantiate2_eq_ok_iff.mp hm
      simp only [PDesign.assemble2_processes, List.mem_append, List.mem_map]
      rintro p ((⟨q, hq', rfl⟩ | hp) | ⟨_, -, rfl⟩)
      · exact procQ_inst _ _ q (hq.1 q hq')
      · exact gensQ_expand _ _ _ hq.2 h4 p hp
      · rfl
    all_goals
      intro p hp
      simp only [Design2.errorDesign, List.toList_toArray, List.mem_singleton] at hp
      subst hp
      rfl
  rw [PDesign.instantiateGD2_eq_driverGuard]
  simp only [PDesign.driverGuard, Design2.driverGuard]
  split
  · exact List.any_eq_false.mpr fun p hp => by
      simp only [h p hp, Bool.false_eq_true, not_false_eq_true]
  · refine List.any_eq_false.mpr fun p hp => ?_
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · simp only [h p hp, Bool.false_eq_true, not_false_eq_true]
    · simp only [Process2.hasQualifiedCase, Bool.false_eq_true, not_false_eq_true]

/--
info: 'LeanModels.Sv.NoQ.sem_noQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sem_noQ

end NoQ
end LeanModels.Sv
