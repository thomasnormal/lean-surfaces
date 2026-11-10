import LeanModels.Sv.PinAxioms
import LeanModels.Sv.CombProc

/-!
# `always_comb` bodies in the `sv_comb` fragment, S1b gate b: bodies of several windows at the template level

`CombProcStmt.lean` (gate a) proves the semantic core: a body that is a list of segments (`Seg`: a tree over its own
window) lowers to ONE assign of all its windows (`lower_body`). This file is the template side, and changes nothing
that exists:

* **The recognizer** `multiSegs?` reads a block of several statements as SEGMENTS: consecutive statements writing the
  same window form one segment (a first tree that assigns the window on every path, then `if (c) tree;` overrides:
  `treeStmt?` and `ovrStmt?` of `CombProc.lean`), a statement that starts a tree for ANOTHER window starts the next
  segment. Refused, each with its message: a second unconditional assignment of the window being built, a window
  written in two separate groups (interleaving: `y = a; z = b; if (c) y = d;`), a latch, an override of another
  window, a nested `begin … end` with several statements. `bodyP2` is the statement the segments stand for;
  `multiSegs?_spec` is the inversion (`bodyP2 segs = .block ss`, every segment passed its checks, the targets are
  pairwise distinct accesses). A block that `treeStmt?` already reads (one window, `more = []`) comes out as ONE
  segment (`multiSegs?_of_treeStmt`), so the single-window behaviour, messages included, is the old one.
* **The instantiation** `segsOf` (the `Seg`s of the instantiated body), `instStmt2_body` (the instantiated statement IS
  `bodyStmt (segsOf …)`), `proc_body_eq` (the guard admits it, so the instantiated process is that body) and
  `lower_body_site` (the lowering of the instantiated process is the single assign of all its windows): the several-window
  versions of `instStmt2_tree`, `proc_site_eq` and `lower_site`. The hypotheses are the summary's: every access in range
  and declared, no read overlapping ANY window of the body (`hself`), the windows positive and pairwise disjoint
  (the within-site disjointness obligation of S1b gate c).

Nothing here is wired into the summary: `siteOfP?` still reads `treeStmt?`, so a multi-window body is still refused with
the C1 text (`sv_structure`). No axiom is added (pins at the end).
-/

namespace LeanModels.Sv
namespace CombProc
open CombView CombEq CombGuard

/-! ## 1. The recognizer -/

/-- The refusal of a body that writes a window in two separate groups of statements. -/
def interleaveMsg : String :=
  "an always_comb body writes a window in two separate groups of statements (outside the second fragment: put the statements of one window together)"

/-- The statements of the segments, in order. -/
def bodyP2 (segs : List (Acc × PTR)) : PStmt :=
  .block (segs.flatMap fun s => s.2.pt.stmtsP)

/-- The segments of a block, one statement at a time: `tg`/`cur` is the segment being built, `done` the finished ones. -/
def segFold? (ds : List DeclT) :
    Acc → PTR → List (Acc × PTR) → List PStmt → Except String (List (Acc × PTR))
  | tg, cur, done, [] => .ok (done ++ [(tg, cur)])
  | tg, cur, done, s :: rest =>
      match s with
      | .ifStmt _ th none =>
          match ovrStmt? ds tg cur s with
          | .ok cur' => segFold? ds tg cur' done rest
          | .error e =>
              match treeStmt? ds th with
              | .ok (t1, _) =>
                  if done.any (fun x => decide (x.1 = t1)) then
                    .error interleaveMsg
                  else .error e
              | .error _ => .error e
      | _ =>
          match treeStmt? ds s with
          | .error e => .error e
          | .ok (tg', p) =>
              if p.pt.isOvr then
                .error "a `begin … end` with several statements as a statement of a block (outside the second fragment: write its statements in the outer block)"
              else if tg' = tg then
                .error "a second unconditional assignment of the target in an always_comb block (outside the second fragment: only `if (c) …;` overrides can follow the first statement)"
              else if done.any (fun x => decide (x.1 = tg')) then
                .error interleaveMsg
              else segFold? ds tg' p (done ++ [(tg, cur)]) rest
termination_by structural _ _ _ ss => ss

/-- **The segments of a block of several statements** (S1b gate b). -/
def multiSegs? (ds : List DeclT) : PStmt → Except String (List (Acc × PTR))
  | .block (s :: s2 :: rest) =>
      match treeStmt? ds s with
      | .error e => .error e
      | .ok (t, b) =>
          if b.pt.isOvr then
            .error "a `begin … end` with several statements as a statement of a block (outside the second fragment: write its statements in the outer block)"
          else segFold? ds t b [] (s2 :: rest)
  | _ => .error "not a block of several statements"

theorem segFold?_spec (ds : List DeclT) :
    ∀ (rest : List PStmt) (tg : Acc) (cur : PTR) (done segs : List (Acc × PTR)),
      segFold? ds tg cur done rest = .ok segs → cur.Ok ds tg → (∀ s ∈ done, s.2.Ok ds s.1) →
      (done.map Prod.fst ++ [tg]).Nodup →
      segs.flatMap (fun s => s.2.pt.stmtsP) =
        (done ++ [(tg, cur)]).flatMap (fun s => s.2.pt.stmtsP) ++ rest ∧
      (∀ s ∈ segs, s.2.Ok ds s.1) ∧ (segs.map Prod.fst).Nodup
  | [], tg, cur, done, segs, h, hc, hd, hn => by
      simp only [segFold?, Except.ok.injEq] at h
      subst h
      refine ⟨by simp, ?_, by simpa using hn⟩
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hd s hs
      · rw [List.mem_singleton.mp hs]; exact hc
  | s :: rest, tg, cur, done, segs, h, hc, hd, hn => by
      simp only [segFold?] at h
      split at h
      · -- an override `if (c) tree;` of the segment being built
        rename_i c th
        split at h
        · rename_i cur' hcur
          obtain ⟨e1, e2, o1⟩ := ovrStmt?_spec ds _ tg cur cur' hcur
          obtain ⟨k1, k2, k3⟩ := segFold?_spec ds rest tg cur' done segs h (o1 hc) hd hn
          refine ⟨?_, k2, k3⟩
          rw [k1]
          simp [e1]
        · split at h <;> (try split at h) <;> simp at h
      · -- the first tree of the next segment
        split at h
        · simp at h
        · rename_i t1 p ht
          obtain ⟨e1, o1⟩ := treeStmt?_spec ds _ t1 p ht
          split at h
          · simp at h
          · rename_i hno
            split at h
            · simp at h
            · rename_i hne
              split at h
              · simp at h
              · rename_i hnd
                have hst : p.pt.stmtsP = [s] := by
                  unfold PT.stmtsP; rw [if_neg hno, e1]
                have hnd' : ∀ x ∈ done, x.1 ≠ t1 := by
                  intro x hx hx1
                  apply hnd
                  simp only [List.any_eq_true, decide_eq_true_eq]
                  exact ⟨x, hx, hx1⟩
                have hn' : ((done ++ [(tg, cur)]).map Prod.fst ++ [t1]).Nodup := by
                  rw [List.map_append, List.map_singleton, List.nodup_append]
                  refine ⟨by simpa [List.map_append] using hn, (by simp), ?_⟩
                  intro a ha b hb
                  rw [List.mem_singleton] at hb
                  subst hb
                  rcases List.mem_append.mp ha with ha | ha
                  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
                    exact hnd' x hx
                  · rw [List.mem_singleton] at ha
                    subst ha
                    exact fun h' => hne h'.symm
                obtain ⟨k1, k2, k3⟩ := segFold?_spec ds rest t1 p (done ++ [(tg, cur)]) segs h o1
                  (by
                    intro x hx
                    rcases List.mem_append.mp hx with hx | hx
                    · exact hd x hx
                    · rw [List.mem_singleton.mp hx]; exact hc) hn'
                refine ⟨?_, k2, k3⟩
                rw [k1]
                simp [hst, List.append_assoc]

theorem multiSegs?_spec (ds : List DeclT) (b : PStmt) (segs : List (Acc × PTR))
    (h : multiSegs? ds b = .ok segs) :
    ∃ ss, b = .block ss ∧ bodyP2 segs = .block ss ∧ (∀ s ∈ segs, s.2.Ok ds s.1) ∧
      (segs.map Prod.fst).Nodup := by
  unfold multiSegs? at h
  split at h
  · rename_i s s2 rest
    split at h
    · simp at h
    · rename_i t b0 hb0
      obtain ⟨e1, o1⟩ := treeStmt?_spec ds _ t b0 hb0
      split at h
      · simp at h
      · rename_i hno
        have hst : b0.pt.stmtsP = [s] := by
          unfold PT.stmtsP; rw [if_neg hno, e1]
        obtain ⟨k1, k2, k3⟩ := segFold?_spec ds (s2 :: rest) t b0 [] segs h o1
          (by simp) (by simp)
        refine ⟨s :: s2 :: rest, rfl, ?_, k2, k3⟩
        simp only [bodyP2]
        rw [k1]
        simp [hst]
  · simp at h

theorem ovrStmt?_shape (ds : List DeclT) (tg : Acc) (base : PTR) :
    ∀ (s : PStmt) (q : PTR), ovrStmt? ds tg base s = .ok q → ∃ c th, s = .ifStmt c th none
  | .ifStmt c th none, q, _ => ⟨c, th, rfl⟩
  | .ifStmt _ _ (some _), q, h => by simp [ovrStmt?] at h
  | .blockingAssignL t v, q, h => by
      unfold ovrStmt? at h
      split at h
      · simp at h
      · split at h <;> simp at h
  | .blockingAssign n v, q, h => by
      unfold ovrStmt? at h
      split at h
      · simp at h
      · split at h <;> simp at h
  | .nbaAssign .., q, h => by simp [ovrStmt?] at h
  | .nbaAssignL .., q, h => by simp [ovrStmt?] at h
  | .block .., q, h => by simp [ovrStmt?] at h
  | .caseStmt .., q, h => by simp [ovrStmt?] at h
  | .forLoop .., q, h => by simp [ovrStmt?] at h
  | .unsupported .., q, h => by simp [ovrStmt?] at h

/-- A block that `treeStmt?` reads (one window) is ONE segment: the tail of overrides is the same fold. -/
theorem segFold?_of_ovrFold (ds : List DeclT) (tg : Acc) :
    ∀ (rest : List PStmt) (base p : PTR), ovrFold? ds tg base rest = .ok p →
      segFold? ds tg base [] rest = .ok [(tg, p)]
  | [], base, p, h => by
      simp only [ovrFold?, Except.ok.injEq] at h
      subst h
      simp [segFold?]
  | s :: rest, base, p, h => by
      unfold ovrFold? at h
      split at h
      · simp at h
      · rename_i q hq
        obtain ⟨c, th, rfl⟩ := ovrStmt?_shape ds tg base s q hq
        simp only [segFold?, hq]
        exact segFold?_of_ovrFold ds tg rest q p h

theorem multiSegs?_of_treeStmt (ds : List DeclT) (b : PStmt) (t : Acc) (p : PTR)
    (hb : ∃ s s2 rest, b = .block (s :: s2 :: rest)) (h : treeStmt? ds b = .ok (t, p)) :
    multiSegs? ds b = .ok [(t, p)] := by
  obtain ⟨s, s2, rest, rfl⟩ := hb
  unfold treeStmt? at h
  unfold treeStmts? at h
  split at h
  · simp at h
  · rename_i t0 b0 hb0
    split at h
    · simp at h
    · rename_i hno
      split at h
      · simp at h
      · rename_i p' hp'
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        unfold multiSegs?
        simp only [hb0, hno, Bool.false_eq_true, if_false]
        exact segFold?_of_ovrFold ds _ _ b0 p' hp'

/-! ## 2. The instantiation -/

/-- The `Seg`s of the instantiated body: each segment's lowered target, its window and its instantiated tree. -/
def segsOf (σ : String → Int) (dw : String → Nat) (E : IEnv) (elems : List (String × Nat))
    (segs : List (Acc × PTR)) : List Seg :=
  segs.map fun s => ⟨s.1.lhs σ, s.1.win σ dw, s.2.pt.low E elems (s.1.win σ dw).2.2⟩

/-- The statements of an instantiated segment template. -/
theorem instStmts2_stmtsP {E : IEnv} {elems : List (String × Nat)} {tgt : Lhs2} {w : Nat} (pt : PT)
    (h : pt.Tgt E elems tgt w) :
    instStmts2 E elems pt.stmtsP = (pt.low E elems w).baseL ((pt.low E elems w).toStmt tgt) := by
  have hb := instStmt2_tree pt h
  unfold PT.stmtsP PTree.baseL
  rw [low_isOvr]
  split
  · rename_i ho
    cases pt <;> simp [PT.isOvr] at ho
    have := congrArg Stmt2.unblock hb
    simpa [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, PStmt.unblock, Stmt2.unblock] using this
  · simp [instStmts2, hb]

theorem instStmts2_flatMap {E : IEnv} {elems : List (String × Nat)} {σ : String → Int}
    {dw : String → Nat} :
    ∀ segs : List (Acc × PTR),
      (∀ s ∈ segs, s.2.pt.Tgt E elems (s.1.lhs σ) (s.1.win σ dw).2.2) →
      instStmts2 E elems (segs.flatMap fun s => s.2.pt.stmtsP) =
        bodyStmts (segsOf σ dw E elems segs)
  | [], _ => by simp [instStmts2, bodyStmts, segsOf]
  | s :: rest, h => by
      simp only [List.flatMap_cons, instStmts2_append, segsOf, List.map_cons, bodyStmts, Seg.stmts]
      rw [instStmts2_stmtsP s.2.pt (h s (List.mem_cons_self ..))]
      have := instStmts2_flatMap (E := E) (elems := elems) (σ := σ) (dw := dw) rest
        (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [segsOf] at this
      rw [this]

/-- **The instantiated statement of a body of segments IS the body of the instantiated segments.** -/
theorem instStmt2_body {E : IEnv} {elems : List (String × Nat)} {σ : String → Int} {dw : String → Nat}
    (segs : List (Acc × PTR))
    (h : ∀ s ∈ segs, s.2.pt.Tgt E elems (s.1.lhs σ) (s.1.win σ dw).2.2) :
    instStmt2 E elems (bodyP2 segs) = bodyStmt (segsOf σ dw E elems segs) := by
  simp only [bodyP2, instStmt2, bodyStmt]
  rw [instStmts2_flatMap segs h]

section site
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- The `BodyOk` facts of the instantiated body, from the recognizer's and the summary's. -/
theorem body_ok (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {ds : List DeclT} (segs : List (Acc × PTR))
    (hatg : ∀ s ∈ segs, AccOK σ DW DG EW ns s.1)
    (hin : ∀ s ∈ segs, (s.1.win σ dw).2.1 + (s.1.win σ dw).2.2 ≤ dw s.1.name)
    (hok : ∀ s ∈ segs, s.2.Ok ds s.1) (hacc : ∀ s ∈ segs, ∀ a ∈ s.2.rds, AccOK σ DW DG EW ns a)
    (hself : ∀ s ∈ segs, ∀ a ∈ s.2.rds, ∀ s' ∈ segs, (a.rd σ).overlaps (s'.1.win σ dw) = false)
    (hpos : ∀ s ∈ segs, 0 < (s.1.win σ dw).2.2)
    (hdisj : Win.allDisjoint (segs.map fun s => s.1.win σ dw) = true) :
    BodyOk d (fun n => E.widths.lookup n) (segsOf σ dw E elems segs) := by
  have hW : bodyWins (segsOf σ dw E elems segs) = segs.map fun s => s.1.win σ dw := by
    simp [bodyWins, segsOf, List.map_map, Function.comp_def]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V hV
    rw [hW] at hV
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hV
    exact hpos s hs
  · rw [hW]; exact hdisj
  · intro sg hsg
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsg
    obtain ⟨hsw, hm, hr⟩ := tgt_facts C hdw hd (hatg s hs) (hin s hs)
    refine ⟨hsw, low_wf C hd s.2 (hok s hs) (hacc s hs) _, low_idxFree C hdw s.2 (hok s hs) (hacc s hs) _, ?_, ?_⟩
    · intro V hV
      rw [hW] at hV
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hV
      exact low_noRead C (s'.1.win σ dw) s.2 (hok s hs) (hacc s hs) (fun a ha => hself s hs a ha s' hs') _
    · rw [hW]; exact List.mem_map_of_mem hs
  · intro sg hsg
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsg
    exact (tgt_facts C hdw hd (hatg s hs) (hin s hs)).2.1
  · intro sg hsg
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsg
    exact (tgt_facts C hdw hd (hatg s hs) (hin s hs)).2.2

/-- **The instantiated process of a body of several windows IS the guarded body** (the guard admits it), the several-window
`proc_site_eq`. -/
theorem proc_body_eq (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {ds : List DeclT} (segs : List (Acc × PTR))
    (hatg : ∀ s ∈ segs, AccOK σ DW DG EW ns s.1)
    (hin : ∀ s ∈ segs, (s.1.win σ dw).2.1 + (s.1.win σ dw).2.2 ≤ dw s.1.name)
    (hok : ∀ s ∈ segs, s.2.Ok ds s.1) (hacc : ∀ s ∈ segs, ∀ a ∈ s.2.rds, AccOK σ DW DG EW ns a)
    (hself : ∀ s ∈ segs, ∀ a ∈ s.2.rds, ∀ s' ∈ segs, (a.rd σ).overlaps (s'.1.win σ dw) = false)
    (hpos : ∀ s ∈ segs, 0 < (s.1.win σ dw).2.2)
    (hdisj : Win.allDisjoint (segs.map fun s => s.1.win σ dw) = true) :
    instProcess2 E elems (.alwaysComb (bodyP2 segs)) =
      .alwaysComb (bodyStmt (segsOf σ dw E elems segs)) := by
  have hb := body_ok C hdw hd segs hatg hin hok hacc hself hpos hdisj
  have ht : ∀ s ∈ segs, s.2.pt.Tgt E elems (s.1.lhs σ) (s.1.win σ dw).2.2 :=
    fun s hs => tree_tgt C hdw (hatg s hs) s.2 (hok s hs)
  simp only [instProcess2]
  rw [instStmt2_body segs ht]
  exact combGuardProc_of_admits (combAdmits_body d _ _ hb)

/-- **The lowering of an instantiated body of several windows is ONE assign of all of them** (the several-window
`lower_site`). -/
theorem lower_body_site (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {ds : List DeclT} (segs : List (Acc × PTR))
    (hatg : ∀ s ∈ segs, AccOK σ DW DG EW ns s.1)
    (hin : ∀ s ∈ segs, (s.1.win σ dw).2.1 + (s.1.win σ dw).2.2 ≤ dw s.1.name)
    (hok : ∀ s ∈ segs, s.2.Ok ds s.1) (hacc : ∀ s ∈ segs, ∀ a ∈ s.2.rds, AccOK σ DW DG EW ns a)
    (hself : ∀ s ∈ segs, ∀ a ∈ s.2.rds, ∀ s' ∈ segs, (a.rd σ).overlaps (s'.1.win σ dw) = false)
    (hpos : ∀ s ∈ segs, 0 < (s.1.win σ dw).2.2)
    (hdisj : Win.allDisjoint (segs.map fun s => s.1.win σ dw) = true) :
    Process2.lowerComb d (instProcess2 E elems (.alwaysComb (bodyP2 segs))) =
      some (.assign (.concat ((segs.map fun s => s.1.win σ dw).map Win.lhs))
        (.concat (segs.map fun s =>
          (s.2.pt.low E elems (s.1.win σ dw).2.2).low (s.1.win σ dw).2.2).toArray)) := by
  have hb := body_ok C hdw hd segs hatg hin hok hacc hself hpos hdisj
  rw [proc_body_eq C hdw hd segs hatg hin hok hacc hself hpos hdisj]
  have := lower_body_plain d (segsOf σ dw E elems segs) (bodyWins (segsOf σ dw E elems segs)) hb.pos
    hb.disj hb.seg (fun sg hsg => (hb.seg sg hsg).nr)
  simpa [bodyWins, segsOf, List.map_map, Function.comp_def] using this

/-- The driven windows of the instantiated body are those of its segments' targets (the within-site part of
`driversOk`, gate c). -/
theorem drvWins_body {dw : String → Nat} (segs : List (Acc × PTR)) :
    ∀ x ∈ (bodyStmt (segsOf σ dw E elems segs)).drvWins, ∃ s ∈ segs, x ∈ (s.1.lhs σ).drvWins := by
  intro x hx
  simp only [bodyStmt, Stmt2.drvWins] at hx
  obtain ⟨sg, hsg, hxs⟩ := drvWins_bodyStmts _ x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsg
  exact ⟨s, hs, hxs⟩

end site

/-! ## 3. Non-vacuity: the bit cell of `add_proc_m.sv`, and what the recognizer refuses -/

/-- `s[i]` as a template target. -/
def sumLhs : PLhs := .bitSel "s" (.genvarRef "i")

/-- `if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i]; s[i] = p[i] ^ c[i];` (the two-window body of the fixture). -/
def cellBody : PStmt :=
  .block [.ifStmt (.bitSel (.ident "p") (.genvarRef "i"))
      (.blockingAssignL carryLhs (.bitSel (.ident "c") (.genvarRef "i")))
      (some (.blockingAssignL carryLhs (.bitSel (.ident "a") (.genvarRef "i")))),
    .blockingAssignL sumLhs (.binary (.m0 .xor) (.bitSel (.ident "p") (.genvarRef "i"))
      (.bitSel (.ident "c") (.genvarRef "i")))]

private def refusal2 (p : PStmt) : String :=
  match multiSegs? apDecls p with
  | .ok _ => "accepted"
  | .error m => m

-- the cell is two segments: the carry window `c[i+1]` and the sum window `s[i]`, in source order
#guard match multiSegs? apDecls cellBody with
  | .ok segs => segs.map Prod.fst == [.bit "c" ⟨[("i", 1)], 1, []⟩, .bit "s" ⟨[("i", 1)], 0, []⟩] &&
      segs.map (fun s => s.2.rds.length) == [3, 2]
  | .error _ => false

-- … while the one-window recognizer still refuses it with the C1 text (the summary is unchanged)
#guard (match treeStmt? apDecls cellBody with | .ok _ => "accepted" | .error m => m) ==
  "always_comb block with several statements (outside the first fragment: write one if/else tree that assigns the target on every path)"

private def pp2 : PExpr := .bitSel (.ident "p") (.genvarRef "i")
private def cc2 : PExpr := .bitSel (.ident "c") (.genvarRef "i")
private def aa2 : PExpr := .bitSel (.ident "a") (.genvarRef "i")

-- a default-then-override on the second window is accepted
#guard refusal2 (.block [.blockingAssignL carryLhs aa2, .blockingAssignL sumLhs cc2,
    .ifStmt pp2 (.blockingAssignL sumLhs aa2) none]) == "accepted"
-- interleaving: the first window again after the second
#guard refusal2 (.block [.blockingAssignL carryLhs aa2, .blockingAssignL sumLhs cc2,
    .ifStmt pp2 (.blockingAssignL carryLhs cc2) none]) ==
  "an always_comb body writes a window in two separate groups of statements (outside the second fragment: put the statements of one window together)"
#guard refusal2 (.block [.blockingAssignL carryLhs aa2, .blockingAssignL sumLhs cc2,
    .blockingAssignL carryLhs cc2]) ==
  "an always_comb body writes a window in two separate groups of statements (outside the second fragment: put the statements of one window together)"
-- a second assignment of the window being built
#guard refusal2 (.block [.blockingAssignL carryLhs aa2, .blockingAssignL carryLhs cc2,
    .blockingAssignL sumLhs cc2]) ==
  "a second unconditional assignment of the target in an always_comb block (outside the second fragment: only `if (c) …;` overrides can follow the first statement)"
-- a latch: an `if` without `else` for a window that has no default
#guard refusal2 (.block [.blockingAssignL carryLhs aa2, .ifStmt pp2 (.blockingAssignL sumLhs cc2) none]) ==
  "always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)"
-- a nested block with several statements as the first statement of a segment
#guard refusal2 (.block [.block [.blockingAssignL carryLhs aa2, .ifStmt pp2 (.blockingAssignL carryLhs cc2) none],
    .blockingAssignL sumLhs cc2]) ==
  "a `begin … end` with several statements as a statement of a block (outside the second fragment: write its statements in the outer block)"
-- one window with overrides: ONE segment, the same tree as `treeStmt?`
#guard match multiSegs? apDecls (.block [.blockingAssignL carryLhs aa2, .ifStmt pp2 (.blockingAssignL carryLhs cc2) none]),
    treeStmt? apDecls (.block [.blockingAssignL carryLhs aa2, .ifStmt pp2 (.blockingAssignL carryLhs cc2) none]) with
  | .ok [(t, p)], .ok (t', p') => t == t' && p.pt.toPStmt == p'.pt.toPStmt
  | _, _ => false

-- the instantiated, lowered cell at `N = 4`, `i = 1` (ground evaluation of `lower_body_site`'s left-hand side):
-- ONE assign of the two windows `{c[2], s[1]}`, in source order, whose right-hand side is two elements
private def cellEnv : IEnv := { vals := [("i", 1)] }

private def cellLowered : Option Process2 :=
  match multiSegs? apDecls cellBody with
  | .ok segs => Process2.lowerComb (apDesign 4)
      (instProcess2 cellEnv [("a", 1), ("c", 1), ("p", 1), ("s", 1)] (.alwaysComb (bodyP2 segs)))
  | .error _ => none

#guard match cellLowered with
  | some (.assign (.concat ws) (.concat es)) =>
      ws == [Lhs2.slice "c" 2 1, Lhs2.slice "s" 1 1] && es.size == 2
  | _ => false

/-! ## Axiom pins (standard axioms only) -/

#pin_axioms segFold?_spec multiSegs?_spec segFold?_of_ovrFold multiSegs?_of_treeStmt instStmts2_stmtsP
  instStmts2_flatMap instStmt2_body body_ok proc_body_eq lower_body_site drvWins_body

end CombProc
end LeanModels.Sv
