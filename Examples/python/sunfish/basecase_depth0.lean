/-
**THE ASSEMBLY'S BASE CASE, leaf one: the STALE-TABLE PROBE HIT** — the section
of the `RecursionStep` campaign that depends on none of R1–R5
(docs/backlog.md §L25, *"The assembly's base case — its own program"*).

`BoundRefines V 0` (`bound_depth.lean` §7) quantifies over an ARBITRARY position
and an ARBITRARY table satisfying `TableAt`, and owes four things out: the run,
`TableAt`, `SubtreeWrites` at every greater depth, and `Report`.
`qs_stand_pat_closed` is ONE leaf of it — the cleared-table, stand-pat-CUT case.
This file opens the leaf §L25 priced as the cheapest: the probe HITS, one of the
two bound returns fires, and `bound()` answers out of the table without ever
reaching `moves()`.

It is the cheapest for a reason worth stating: **the whole run is the head**, and
`Report` is not earned by a fold at all — it is READ OFF the table invariant.
`TableAt` says the stored entry brackets `V pos 0`; a lower return is above
`gamma`, an upper return below it; those are exactly `Report`'s two disjuncts. So
the leaf spends §6's `sf_probe` and nothing of §3's `fold`.

**And it is where the rule's own statement was found to be FALSE.** §7 below
refutes `BoundRefines V d` outright — it quantifies over an arbitrary
`pos : RVal`, and at a non-`Position` the shipped `bound()` refuses, so the
existential cannot be met at any depth — and because `RecursionStep` is a STRONG
induction over exactly that proposition, the STEP the whole campaign is priced to
prove is now vacuously true, in one line. Two more holes in the same statement
are measured beside it. `BoundRefinesP` (§8) is the repair, and
`boundRefinesP_zero` is the base case's four-way split assembled on it, with two
of the four leaves proved here and the other two named as one hypothesis.

**MEASURED FIRST, on the shipped engine** (§L24's exit law, and §5 below keeps
every number where it cannot rot):

* a stale `Entry(20, 900)` at `(posH 0, 0)` with `gamma = 5` makes `bound()`
  answer **20**, and `Entry(-MATE_UPPER, -30)` with the same `gamma` answers
  **-30** — the two arms, both real;
* the run is heap-SIZE-free (**70 → 70**, against 70 → 2409 for the stand-pat
  path that reaches `moves()`), and the only slot whose CONTENTS change is the
  receiver's — which is why `SubtreeWrites`' `.other` arm alone discharges the
  third conjunct, with no `.alloc`;
* the minimum fuel for the whole `callIn` is **18** — so no gate below pins a
  numeral it has not measured, and every fuel here is a parameter anyway.
-/
import Examples.python.sunfish.bound_depth

namespace Examples.python.sunfish.basecase_depth0

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.bound_depth

set_option maxRecDepth 100000

/-! ## §1 The escape engine

`execStmts_append` (§L21) composes a segment that FALLS THROUGH with whatever
follows it. A returning head needs the other half: a segment that does not fall
through decides the concatenation on its own, because the tail is never reached.
Four lines of the same case analysis, and it is what makes a `return` inside
statement 5 a statement about all eighteen. -/

/-- **A segment that ESCAPES decides the whole concatenation.** The mirror of
`execStmts_append`: there the first run must be `.next`, here it must not be. -/
theorem execStmts_append_escape {m : Module} {l₁ l₂ : List Stmt} {st st' : FrameState}
    {flow : RFlow} (hne : flow ≠ .next)
    (h1 : ∃ f, execStmts m f st l₁ = .ok st' flow) :
    ∃ f, execStmts m f st (l₁ ++ l₂) = .ok st' flow := by
  induction l₁ generalizing st with
  | nil =>
    obtain ⟨f, hf⟩ := h1
    match f, hf with
    | f + 1, hf =>
      rw [execStmts] at hf
      exact absurd ((Run.ok.inj hf).2).symm hne
  | cons s l₁' ih =>
    obtain ⟨f, hf⟩ := h1
    match f, hf with
    | f + 1, hf =>
      rw [execStmts] at hf
      cases hx : execStmt m f st s with
      | ok st₁ fl =>
        rw [hx, Run.bind] at hf
        cases fl with
        | next =>
          obtain ⟨g, hg⟩ := ih ⟨f, hf⟩
          refine ⟨(f + g) + 1, ?_⟩
          rw [List.cons_append, execStmts,
            execStmt_mono hx (by simp) (f + g) (by omega), Run.bind]
          exact execStmts_mono hg (by simp) _ (by omega)
        | brk => exact ⟨f + 1, by rw [List.cons_append, execStmts, hx, Run.bind]; exact hf⟩
        | cont => exact ⟨f + 1, by rw [List.cons_append, execStmts, hx, Run.bind]; exact hf⟩
        | ret v => exact ⟨f + 1, by rw [List.cons_append, execStmts, hx, Run.bind]; exact hf⟩
      | exn st₁ er => rw [hx, Run.bind] at hf; exact absurd hf (by simp)
      | timeout => rw [hx, Run.bind] at hf; exact absurd hf (by simp)
      | unsupported msg => rw [hx, Run.bind] at hf; exact absurd hf (by simp)

/-! ## §2 The probe block over a table that is NOT cleared

§4's `probe_misses`/`probe_lower_passes`/`probe_upper_passes` are the
cleared-table gates: the dict is `.dict #[] sv`, the answer is the shipped
default, and both returns are unreachable. The stale case needs all three at an
ARBITRARY dict, and the two returns need their firing arms as well — five gates,
none of which the cleared-table three specialize to.

That is the one correction this file owes §L25's plan, which priced the leaf as
*"HEAD-only and reuses `probe_block_runs` unchanged"*. Head-only is right;
`probe_block_runs` is not reusable, because its `hdict` premise pins `.dict #[]`
and its conclusion pins `.next`. The five gates below cost about as much as the
prediction implied — the shape is the same — but they are new text. -/

/-- **GATE — the probe reads WHATEVER the table holds.** `probe_misses` at an
arbitrary dict: `entry = self.tp_score.get((pos, depth), Entry(-MATE_UPPER,
MATE_UPPER))` binds `entry` to the `.get`'s own answer.

Stated in the COMPUTED shape (§L20's law): `heapGet` inlines to
`(dictFind es.toList k).getD dflt`, so the premise is about that term and not
about `heapGet`. Heap-free — a `.get` allocates nothing, measured in §8. -/
theorem probe_reads (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf d : Int) (pv : RVal) (es : Array (RVal × RVal)) (sv : Nat) (ev : RVal)
    (F : Nat)
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int d))
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hnomu : Env.lookup e "MATE_UPPER" = Option.none)
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hk : hashableKey pv = true)
    (hfind : (dictFind es.toList (tpKey pv d)).getD entryDefault = ev) :
    execStmts sunfish (F + 16) ⟨w, e⟩ [sbEntry]
      = .ok ⟨w, Env.set e "entry" ev⟩ .next := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, hen⟩ := sbEntry_lit
  obtain ⟨sp, hnt⟩ := entryNTAux
  simp only [tpKey, entryDefault, mateUpper] at hfind
  simp only [Heap.get?] at hobj hdict
  rw [hen]
  py_simp [-globalsFold, -globalsStep, hslf, hpos, hd, hnoe, hmu, hnomu, muG,
    entryG, entryNotFun, entryClsAux, hnt, hobj, hdict, searcherObj, entryDefault,
    hk, mateUpper, hfind]

/-- **GATE — the lower-bound return FIRES.** `if entry.lower >= gamma: return
entry.lower` at a stored entry the window is at or below. This is the arm
`probe_lower_passes` (§4) proves unreachable at the DEFAULT, and it is reachable
at every entry the store ever wrote. -/
theorem probe_lower_returns (w : World) (e : REnv) (gamma lo up : Int) (F : Nat)
    (hen : Env.lookup e "entry" = some (entryOf lo up))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hge : gamma ≤ lo) :
    execStmts sunfish (F + 8) ⟨w, e⟩ [sbLo] = .ok ⟨w, e⟩ (.ret (.int lo)) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, h⟩ := sbLo_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hen, hg, entryOf, entryClsAux]
  rw [if_pos (show (gamma ≤ lo) from hge)]
  py_simp [-globalsFold, -globalsStep, hen, entryOf, entryClsAux]

/-- **GATE — and it does not fire below the window**, at an arbitrary entry
rather than at the default. -/
theorem probe_lower_passes_at (w : World) (e : REnv) (gamma lo up : Int) (F : Nat)
    (hen : Env.lookup e "entry" = some (entryOf lo up))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hlt : lo < gamma) :
    execStmts sunfish (F + 8) ⟨w, e⟩ [sbLo] = .ok ⟨w, e⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, h⟩ := sbLo_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hen, hg, entryOf, entryClsAux]
  rw [if_neg (show ¬ (gamma ≤ lo) by omega)]
  py_simp [-globalsFold, -globalsStep]

/-- **GATE — the upper-bound return FIRES.** `if entry.upper < gamma: return
entry.upper`, the fail-low half of the same read. -/
theorem probe_upper_returns (w : World) (e : REnv) (gamma lo up : Int) (F : Nat)
    (hen : Env.lookup e "entry" = some (entryOf lo up))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hlt : up < gamma) :
    execStmts sunfish (F + 8) ⟨w, e⟩ [sbUp] = .ok ⟨w, e⟩ (.ret (.int up)) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, h⟩ := sbUp_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hen, hg, entryOf, entryClsAux]
  rw [if_pos (show (up < gamma) from hlt)]
  py_simp [-globalsFold, -globalsStep, hen, entryOf, entryClsAux]

/-- **GATE — and it does not fire above it.** The pair of pass gates is what the
FALL-THROUGH leaves (stand-pat cut, fail-low) will need over a stale table, so
they land here beside the returns rather than when they are first spent. -/
theorem probe_upper_passes_at (w : World) (e : REnv) (gamma lo up : Int) (F : Nat)
    (hen : Env.lookup e "entry" = some (entryOf lo up))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hge : gamma ≤ up) :
    execStmts sunfish (F + 8) ⟨w, e⟩ [sbUp] = .ok ⟨w, e⟩ .next := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, h⟩ := sbUp_lit
  rw [h]
  py_simp [-globalsFold, -globalsStep, hen, hg, entryOf, entryClsAux]
  rw [if_neg (show ¬ (up < gamma) by omega)]
  py_simp [-globalsFold, -globalsStep]

/-- **THE PROBE BLOCK, RETURNING.** `if not root:` runs, the `.get` HITS, and one
of the two bound returns fires — which one is `harm`'s business, so the two arms
compose once rather than twice. The repetition test is never reached in either.

`harm` is the disjunction in the order the shipped code tests it: the lower
return wins ties, and the upper return is only reachable once the lower has
passed. -/
theorem probe_block_returns (w : World) (e : REnv) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma lo up r : Int) (pv : RVal) (es : Array (RVal × RVal)) (sv : Nat)
    (hroot : Env.lookup e "root" = some (.bool false))
    (hslf : Env.lookup e "self" = some (.ref sa))
    (hpos : Env.lookup e "pos" = some pv)
    (hd : Env.lookup e "depth" = some (.int 0))
    (hg : Env.lookup e "gamma" = some (.int gamma))
    (hnoe : Env.lookup e "Entry" = Option.none)
    (hnomu : Env.lookup e "MATE_UPPER" = Option.none)
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hobj : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hk : hashableKey pv = true)
    (hfind : (dictFind es.toList (tpKey pv 0)).getD entryDefault = entryOf lo up)
    (harm : (gamma ≤ lo ∧ r = lo) ∨ (lo < gamma ∧ up < gamma ∧ r = up)) :
    ∃ f, execStmts sunfish f ⟨w, e⟩ [sbProbe]
      = .ok ⟨w, Env.set e "entry" (entryOf lo up)⟩ (.ret (.int r)) := by
  obtain ⟨p0, p1, p2, hpr⟩ := sbProbe_lit
  have hc : ∀ k : Nat, evalExpr sunfish (k + 4) ⟨w, e⟩ (.unaryOp .not (.name "root" p0) p1)
      = .ok ⟨w, e⟩ (.bool true) := by
    intro k
    py_simp [-globalsFold, -globalsStep, hroot]
  have hen : Env.lookup (Env.set e "entry" (entryOf lo up)) "entry" = some (entryOf lo up) := by
    simp [Env.lookup_set_self]
  have hg' : Env.lookup (Env.set e "entry" (entryOf lo up)) "gamma" = some (.int gamma) := by
    simp [Env.lookup_set_ne, hg]
  have hE : ∃ f, execStmts sunfish f ⟨w, e⟩ [sbEntry]
      = .ok ⟨w, Env.set e "entry" (entryOf lo up)⟩ .next :=
    ⟨16, probe_reads w e ci sa ts tm hs n dl sf 0 pv es sv (entryOf lo up) 0
      hslf hpos hd hnoe hnomu hmu hobj hdict hk hfind⟩
  have hB : ∃ f, execStmts sunfish f ⟨w, e⟩ sbProbeB
      = .ok ⟨w, Env.set e "entry" (entryOf lo up)⟩ (.ret (.int r)) := by
    rw [sbProbeB_split]
    rcases harm with ⟨hge, hr⟩ | ⟨hlt, hup, hr⟩ <;> rw [hr]
    · exact execStmts_append hE
        (execStmts_append_escape (by simp)
          ⟨8, probe_lower_returns w (Env.set e "entry" (entryOf lo up)) gamma lo up 0
            hen hg' hge⟩) (by simp)
    · exact execStmts_append
        (execStmts_append hE
          ⟨8, probe_lower_passes_at w (Env.set e "entry" (entryOf lo up)) gamma lo up 0
            hen hg' hlt⟩ (by simp))
        (execStmts_append_escape (by simp)
          ⟨8, probe_upper_returns w (Env.set e "entry" (entryOf lo up)) gamma lo up 0
            hen hg' hup⟩) (by simp)
  obtain ⟨f, hf⟩ := hB
  refine ⟨(f + 4) + 2, ?_⟩
  rw [hpr]
  refine execStmts_singleton_flow (F := f + 4) ?_
  rw [execStmt_if_true (hc f) rfl, show sbProbeB.toArray.toList = sbProbeB from rfl]
  exact execStmts_mono hf (by simp) _ (by omega)

/-! ## §3 The head, RETURNING, and the boundary

Statements 0–5 with the probe escaping, then the remaining twelve skipped by
§1's engine, then `callIn_of_body` (§4). The frame chain is `head_runs`' —
`bound_enters`, `depth_refloors`, `mate_check_passes` — and every one of its
lookups is `rfl` for the same reason (§L21): `sbEnv0` is a concrete five-element
list over literal keys. -/

/-- **THE WHOLE BODY, at a probe hit.** Eighteen statements of the shipped
`Searcher.bound`, of which six run: the twelve after the probe are unreachable,
and `execStmts_append_escape` is what says so. -/
theorem body_returns_probe_hit (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc lo up r : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (es : Array (RVal × RVal)) (sv : Nat) (h' : Heap)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hts : ts ≠ sa)
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hsc : -mateLower < sc)
    (hfind : (dictFind es.toList (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)).getD entryDefault
      = entryOf lo up)
    (harm : (gamma ≤ lo ∧ r = lo) ∨ (lo < gamma ∧ up < gamma ∧ r = up)) :
    ∃ f, execStmts sunfish f
        ⟨w, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ sbB
      = .ok ⟨W1 w h',
              Env.set (EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) "entry" (entryOf lo up)⟩
          (.ret (.int r)) := by
  have hobj' : Heap.get? h' sa = some (searcherObj ci ts tm hs (n + 1) dl sf) :=
    Heap.get?_update_self hupd
  have hdict' : Heap.get? h' ts = some (.dict es sv) :=
    (Heap.get?_update_ne hupd hts).trans hdict
  have hD : execStmts sunfish 8
      ⟨W1 w h', sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ [sbDepth]
      = .ok ⟨W1 w h', EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma⟩ .next := by
    have := depth_refloors (W1 w h')
      (sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0) 0 rfl rfl
    simpa [EA, show max (0 : Int) 0 = 0 from by omega] using this
  have hA : ∃ f, execStmts sunfish f
      ⟨w, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ [sbDoc, sbNodes, sbClock]
        = .ok ⟨W1 w h', sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ .next :=
    ⟨16, bound_enters w ci sa ts tm hs n dl sf gamma 0
      (posOf b sc wc0 wc1 bc0 bc1 ep kp) h' hself hupd hclk⟩
  have hAB := execStmts_append hA ⟨8, hD⟩ (by simp)
  have hABC := execStmts_append hAB
    ⟨8, mate_check_passes (W1 w h') (EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)
      b sc wc0 wc1 bc0 bc1 ep kp rfl rfl hml hsc⟩ (by simp)
  have hHead := execStmts_append hABC
    (probe_block_returns (W1 w h') (EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)
      ci sa ts tm hs (n + 1) dl sf gamma lo up r (posOf b sc wc0 wc1 bc0 bc1 ep kp) es sv
      rfl rfl rfl rfl rfl rfl rfl hmu hobj' hdict'
      (posOf_hashable b sc wc0 wc1 bc0 bc1 ep kp) hfind harm) (by simp)
  rw [sbB_split]
  exact execStmts_append_escape (by simp) hHead

/-- **The threshold form**, and the world out: the entry world with the node
counter bumped, and NOTHING else — the store is below the return. -/
theorem bound_probe_hit (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc lo up r : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (es : Array (RVal × RVal)) (sv : Nat) (h' : Heap)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hts : ts ≠ sa)
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hsc : -mateLower < sc)
    (hfind : (dictFind es.toList (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)).getD entryDefault
      = entryOf lo up)
    (harm : (gamma ≤ lo ∧ r = lo) ∨ (lo < gamma ∧ up < gamma ∧ r = up)) :
    ∃ t, ∀ F ≥ t, callIn sunfish F w "Searcher.bound"
      #[.ref sa, posOf b sc wc0 wc1 bc0 bc1 ep kp, .int gamma, .int 0]
        = .ok (W1 w h') (.int r) := by
  obtain ⟨f, hf⟩ := body_returns_probe_hit w ci sa ts tm hs n dl sf gamma sc lo up r
    b wc0 wc1 bc0 bc1 ep kp es sv h' hself hupd hclk hts hdict hml hmu hsc hfind harm
  refine ⟨f + 1, fun F hF => ?_⟩
  obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
  exact callIn_of_body (execStmts_mono hf (by simp) F' hF')

/-! ## §4 The spec half — `Report` READ OFF the table

The probe-hit leaf is the one place in `bound()` where the contract is not
earned by a search: the entry that answers already claims `lo ≤ V pos 0 ≤ up`,
because that is what `TableAt` means. The two returns then land on `Report`'s two
disjuncts by arithmetic alone. -/

/-- **What the probe's answer says about the value.** `sf_probe` (§6) at the
shipped `Entry` spelling, with the two halves separated: either the read is the
DEFAULT (nothing was stored under this key) or the stored entry brackets the
value. `-MATE_UPPER`/`MATE_UPPER` is the default's own reading, so the left arm
is a claim about the numbers and not about provenance — which is what lets the
window refute it. -/
theorem sf_probe_brackets {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    {h : Heap} {a : Addr} {p : RVal} {d lo up : Int}
    (ht : (sfBracket V).TableAt h a)
    (hg : heapGet h a (tpKey p d) entryDefault = .ok (entryOf lo up)) :
    (lo = -mateUpper ∧ up = mateUpper) ∨ (lo ≤ V p d ∧ V p d ≤ up) := by
  rcases sf_probe hV ht hg with hdef | hh
  · left
    have h2 : (#[RVal.int lo, RVal.int up] : Array RVal).toList
        = (#[RVal.int (-mateUpper), RVal.int mateUpper] : Array RVal).toList :=
      congrArg Array.toList (by simpa [entryOf, entryDefault] using hdef)
    simpa using h2
  · right
    refine hh.le (entryBounds_entryOf lo up) ?_
    show (pairKey (tpKey p d)).map (fun pd => V pd.1 pd.2) = some (V p d)
    rw [pairKey_tpKey]; rfl

/-- **The probe's own `heapGet`, in the shape the gates compute.** The dict slot
and the key's hashability decide it, and `probe_reads`' premise is the same
term — so one fact feeds the interpreter half and the calculus half at once. -/
theorem heapGet_of_find {h : Heap} {a : Addr} {es : Array (RVal × RVal)} {sv : Nat}
    {p : RVal} {d : Int} {ev : RVal}
    (hdict : Heap.get? h a = some (.dict es sv)) (hk : hashableKey p = true)
    (hfind : (dictFind es.toList (tpKey p d)).getD entryDefault = ev) :
    heapGet h a (tpKey p d) entryDefault = .ok ev := by
  have hkk : hashableKey (tpKey p d) = true := by
    simp [tpKey, hashableKey, hashableKeyList, hk]
  simp only [heapGet, hdict, if_pos hkk, hfind]

/-- **The four conjuncts `BoundRefines` owes, at ONE world, table, window and
position** — `BoundRefines V d`'s own body, named so the leaves can be stated
separately and the case split can assemble them. `boundRefines_eq` below is the
receipt that nothing was restated: the two are the same proposition. -/
def RefinesAt (V : RVal → Int → Int) (d : Int) (w : World) (sa ts : Addr)
    (gamma : Int) (pos : RVal) : Prop :=
  ∃ (w' : World) (r : Int) (t : Nat),
    (∀ F ≥ t, callIn sunfish F w "Searcher.bound"
        #[.ref sa, pos, .int gamma, .int d] = .ok w' (.int r))
    ∧ (sfBracket V).TableAt w'.heap ts
    ∧ (∀ e : Int, d < e → (sfBracket V).SubtreeWrites ts e w.heap w'.heap)
    ∧ Report gamma r (V pos d)

/-- **`BoundRefines` IS `RefinesAt` under its hypotheses**, definitionally. So a
leaf proved at `RefinesAt` is consumed by the rule unchanged — including by the
STRONG-induction restatement §L25's R4 says the null-move recursion at
`depth - 7` will force, which changes the STEP and never the base case. -/
theorem boundRefines_eq (V : RVal → Int → Int) (d : Int) :
    BoundRefines V d =
      ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int) (pos : RVal),
        Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf) →
        (sfBracket V).TableAt w.heap ts →
        -mateUpper < gamma → gamma ≤ mateUpper →
        RefinesAt V d w sa ts gamma pos := rfl

/-- **THE STALE-TABLE LEAF.** Everything `BoundRefines V 0` owes, at a position
whose entry answers the probe. Four conjuncts, and the cheapest possible proof of
each:

* the RUN is `bound_probe_hit` — six statements, no `moves()`, no fold;
* `TableAt` OUT is the invariant IN, because the only write is the node counter
  (`TableAt.update_ne`, at `sa ≠ ts`);
* `SubtreeWrites` at every `e` is that same write, in one `.other` step — no
  `.alloc` arm, which is the measurement §8 keeps: the run's heap does not grow;
* `Report` is READ OFF the entry, by `sf_probe_brackets` and one `omega`.

The premises are the honest minimum: `hupd` comes from `update_exists`, `ts ≠ sa`
from `dict_ne_instance`, and the key's hashability from `posOf_hashable`, so none
of the three appears. What is left is the receiver, the table, the clock, the two
globals, the king-capture precondition, the window, and the arm. -/
theorem refinesAt_probe_hit {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc lo up : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (es : Array (RVal × RVal)) (sv : Nat)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hdict : Heap.get? w.heap ts = some (.dict es sv))
    (ht : (sfBracket V).TableAt w.heap ts)
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hsc : -mateLower < sc)
    (hlo : -mateUpper < gamma) (hup : gamma ≤ mateUpper)
    (hfind : (dictFind es.toList (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)).getD entryDefault
      = entryOf lo up)
    (harm : gamma ≤ lo ∨ up < gamma) :
    RefinesAt V 0 w sa ts gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) := by
  have hts : ts ≠ sa := dict_ne_instance hself hdict
  obtain ⟨h', hupd⟩ := update_exists (o' := searcherObj ci ts tm hs (n + 1) dl sf) hself
  have hk := posOf_hashable b sc wc0 wc1 bc0 bc1 ep kp
  -- the bracket the entry carries, with the DEFAULT arm refuted by the window
  have hbr : lo ≤ V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0
      ∧ V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0 ≤ up := by
    rcases sf_probe_brackets hV ht (heapGet_of_find hdict hk hfind) with ⟨hl, hu⟩ | hb
    · exact absurd harm (by rcases harm with h | h <;> omega)
    · exact hb
  -- which arm fires, once, in the shape the block gate consumes
  have harm' : (gamma ≤ lo ∧ (if gamma ≤ lo then lo else up) = lo)
      ∨ (lo < gamma ∧ up < gamma ∧ (if gamma ≤ lo then lo else up) = up) := by
    by_cases hc : gamma ≤ lo
    · exact Or.inl ⟨hc, if_pos hc⟩
    · rcases harm with h | h
      · omega
      · exact Or.inr ⟨by omega, h, if_neg hc⟩
  obtain ⟨t, htF⟩ := bound_probe_hit w ci sa ts tm hs n dl sf gamma sc lo up
    (if gamma ≤ lo then lo else up) b wc0 wc1 bc0 bc1 ep kp es sv h'
    hself hupd hclk hts hdict hml hmu hsc hfind harm'
  refine ⟨W1 w h', (if gamma ≤ lo then lo else up), t, htF, ?_, ?_, ?_⟩
  · exact Bracket.TableAt.update_ne (Ne.symm hts) hupd ht
  · exact fun e _ => Bracket.SubtreeWrites.other (Ne.symm hts) hupd Bracket.SubtreeWrites.nil
  · by_cases hc : gamma ≤ lo
    · rw [if_pos hc]; exact Or.inr ⟨hc, hbr.1⟩
    · rw [if_neg hc]
      rcases harm with h | h
      · omega
      · exact Or.inl ⟨h, hbr.2⟩

/-! ## §5 Non-vacuity — the leaf's premises, RECOMPUTED on the shipped engine

§L24's finding 1 is the standing law here: *a premise is not paid until something
DISCHARGES it*, and two of that pass's three defects were premises no world could
satisfy. Three of this leaf's would-be premises are discharged inside it
(`hupd`, `ts ≠ sa`, hashability); the rest are checked below by BUILDING the
world they describe and running the shipped `bound()` on it.

`staleW` is a real `Searcher()` over the real `initWorld` with ONE entry written
into `tp_score` through the interpreter's own `heapStore` — not a table typed out
here. -/

/-- The fixture: a fresh `Searcher()` whose `tp_score` already holds
`Entry(lo, up)` at `(posH 0, 0)`, with the receiver and table addresses. -/
private def staleW (lo up : Int) : Option (World × Addr × Addr) :=
  match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance _ attrs) =>
       (match attrs.toList with
        | ("tp_score", .ref ts) :: _ =>
          (match heapStore w.heap ts (tpKey (posH 0) 0) (entryOf lo up) with
           | .ok h' => some ({ w with heap := h' }, a, ts)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

/-- Every interpreter-side premise of `refinesAt_probe_hit`, recomputed on that
world, plus the ANSWER and the world delta the leaf claims. -/
private def leafCheck (lo up gamma r : Int) (F : Nat) : Bool :=
  match staleW lo up with
  | some (w, sa, ts) =>
    (match Heap.get? w.heap sa, Heap.get? w.heap ts with
     | some (.instance ci attrs), some (.dict es sv) =>
       -- hself: the receiver is the shape the gates read
       (match attrs.toList with
        | [("tp_score", .ref ts'), ("tp_move", .ref tm), ("history", .ref hs),
           ("nodes", .int n), ("deadline", .int dl), ("soft", .int sft)] =>
          ts' == ts
            && (Heap.get? w.heap sa == some (searcherObj ci ts tm hs n dl sft))
            -- hclk
            && !((n + 1).fmod 2048 == 0)
            -- hdict / hfind: the probe HITS, at the entry the store wrote
            && (sv == sv)
            && ((dictFind es.toList (tpKey (posH 0) 0)).getD entryDefault == entryOf lo up)
            -- the two globals
            && (Env.lookup w.globals "MATE_LOWER" == some (.int mateLower))
            && (Env.lookup w.globals "MATE_UPPER" == some (.int mateUpper))
            -- hsc, the window, and the arm
            && (-mateLower < (0 : Int)) && (-mateUpper < gamma) && (gamma ≤ mateUpper)
            && (gamma ≤ lo || up < gamma)
            -- ts ≠ sa, which the leaf DERIVES; checked anyway
            && !(ts == sa)
            -- and the conclusion: the answer, and the world out
            && (match callIn sunfish F w "Searcher.bound"
                  #[.ref sa, posH 0, .int gamma, .int 0] with
                | .ok w' (.int ans) =>
                  ans == r
                    && w'.heap.size == w.heap.size
                    && ((List.range w.heap.size).all
                          (fun i => i == sa || Heap.get? w.heap i == Heap.get? w'.heap i))
                    && (Heap.get? w'.heap sa == some (searcherObj ci ts tm hs (n + 1) dl sft))
                | _ => false)
        | _ => false)
     | _, _ => false)
  | Option.none => false

/-! **The LOWER arm.** `Entry(20, 900)` with `gamma = 5`: every premise holds, the
shipped `bound()` answers **20**, and the only slot that moves is the receiver's
node counter — which is exactly the `.other`-then-`.nil` `SubtreeWrites` the leaf
builds, and exactly the `TableAt.update_ne` it spends. -/
#guard leafCheck 20 900 5 20 1000

/-! **The UPPER arm.** `Entry(-MATE_UPPER, -30)` with the same window: the lower
return passes, the upper fires, and the answer is **-30**. -/
#guard leafCheck (-69290) (-30) 5 (-30) 1000

/-! **The fuel, MEASURED rather than assumed** (§L25's law 2). Eighteen decides
both arms and seventeen decides neither — so `bound_probe_hit`'s threshold is a
real number and not a guess. Every gate above takes its fuel as a parameter, so
nothing in the file DEPENDS on these; they are what makes the threshold form
honest. -/
#guard leafCheck 20 900 5 20 18
#guard leafCheck (-69290) (-30) 5 (-30) 18
#guard !(leafCheck 20 900 5 20 17)
#guard !(leafCheck (-69290) (-30) 5 (-30) 17)

/-! **And the leaf is a DIFFERENT run from the stand-pat one.** The same board
and window on a CLEARED table answers 4 and grows the heap by 2339 objects
(`moves()`, the generator, the sorted list); the stale table answers 20 and grows
it by none. If the probe-hit arm were unreachable this guard would read 4. -/
#guard (match searcherW with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound"
        #[.ref a, posH 0, .int 5, .int 0] with
     | .ok w' (.int r) => r == 4 && w.heap.size == 70 && w'.heap.size == 2409
     | _ => false)
  | Option.none => false)

/-! **The default is NOT an entry the arms can fire on** — the refutation
`refinesAt_probe_hit` performs internally, as a number. A cleared table reads
`Entry(-MATE_UPPER, MATE_UPPER)`, whose lower is below every legal `gamma` and
whose upper is at or above every legal `gamma`, so neither return is reachable
and the run must fall through to the other two leaves. -/
#guard entryBounds entryDefault == some (-mateUpper, mateUpper)
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance _ attrs) =>
       (match Env.lookup attrs.toList "tp_score" with
        | some (.ref ts) =>
          (match Heap.get? w.heap ts with
           | some (.dict es _) =>
             (dictFind es.toList (tpKey (posH 0) 0)).getD entryDefault == entryDefault
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)

/-! ## §6 THE KING-CAPTURE LEAF — the arm §L25's plan does not name

`if pos.score <= -MATE_LOWER: return -MATE_UPPER`, statement 4, which fires
BEFORE the probe. Every leaf above and below carries `-MATE_LOWER < pos.score`
as a premise precisely because this arm is the other side of it, so the base
case's split is not complete without it — three leaves is one short.

It is the cheapest of the four: three statements, and the run never reaches the
table at all. **Measured on the fixture:** `pos.score = -MATE_LOWER` answers
`-69290 = -MATE_UPPER`, heap 70 → 70, minimum fuel **11**, and the only slot
that moves is the receiver's.

What it needs that no other leaf does is a MODEL-side fact: the docstring
promises an EXACT value here (*"our own king already captured: r =
-MATE_UPPER"*), not a bracket, so `Report` cannot be read off the table. `hmateV`
is that obligation, and it belongs to `formal/`'s depth-0 leaf. -/

/-- **GATE — the king-capture check FIRES.** `mate_check_passes` (§4) is this
statement's other arm; between them the head's statement 4 is total. -/
theorem mate_check_returns (w : World) (e : REnv) (b : String) (sc : Int)
    (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (F : Nat)
    (hpos : Env.lookup e "pos" = some (posOf b sc wc0 wc1 bc0 bc1 ep kp))
    (hnoml : Env.lookup e "MATE_LOWER" = Option.none)
    (hnomu : Env.lookup e "MATE_UPPER" = Option.none)
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hsc : sc ≤ -mateLower) :
    execStmts sunfish (F + 8) ⟨w, e⟩ [sbMate]
      = .ok ⟨w, e⟩ (.ret (.int (-mateUpper))) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, hm⟩ := sbMate_lit
  rw [hm]
  py_simp [-globalsFold, -globalsStep, hpos, hnoml, hnomu, hml, hmu, mlG, muG, posOf, posCAux,
    posCls_methods]
  rw [if_pos (show (sc ≤ -mateLower) from hsc)]
  py_simp [-globalsFold, -globalsStep, hnomu, hmu, muG]

/-- **The whole body, at a captured king.** Statements 0–4 run; the probe and
everything under it are unreachable. -/
theorem body_returns_king_capture (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) (h' : Heap)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hsc : sc ≤ -mateLower) :
    ∃ f, execStmts sunfish f
        ⟨w, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ sbB
      = .ok ⟨W1 w h', EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma⟩
          (.ret (.int (-mateUpper))) := by
  have hD : execStmts sunfish 8
      ⟨W1 w h', sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ [sbDepth]
      = .ok ⟨W1 w h', EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma⟩ .next := by
    have := depth_refloors (W1 w h')
      (sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0) 0 rfl rfl
    simpa [EA, show max (0 : Int) 0 = 0 from by omega] using this
  have hA : ∃ f, execStmts sunfish f
      ⟨w, sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ [sbDoc, sbNodes, sbClock]
        = .ok ⟨W1 w h', sbEnv0 (.ref sa) (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma 0⟩ .next :=
    ⟨16, bound_enters w ci sa ts tm hs n dl sf gamma 0
      (posOf b sc wc0 wc1 bc0 bc1 ep kp) h' hself hupd hclk⟩
  have hAB := execStmts_append hA ⟨8, hD⟩ (by simp)
  have hABC := execStmts_append hAB
    ⟨8, mate_check_returns (W1 w h') (EA sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)
      b sc wc0 wc1 bc0 bc1 ep kp 0 rfl rfl rfl hml hmu hsc⟩ (by simp)
  rw [sbB_split]
  exact execStmts_append_escape (by simp) hABC

/-- **THE KING-CAPTURE LEAF.** All four conjuncts, at a position whose own score
says the king is gone. `hmateV` is the only model-side premise anywhere in this
file, and it is the one the docstring's EXACT promise forces. -/
theorem refinesAt_king_capture {V : RVal → Int → Int}
    (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (ht : (sfBracket V).TableAt w.heap ts)
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hsc : sc ≤ -mateLower)
    (hlo : -mateUpper < gamma)
    (hmateV : V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0 ≤ -mateUpper) :
    RefinesAt V 0 w sa ts gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) := by
  obtain ⟨es, ver, hdict, hok⟩ := ht
  have hts : ts ≠ sa := dict_ne_instance hself hdict
  obtain ⟨h', hupd⟩ := update_exists (o' := searcherObj ci ts tm hs (n + 1) dl sf) hself
  obtain ⟨f, hf⟩ := body_returns_king_capture w ci sa ts tm hs n dl sf gamma sc
    b wc0 wc1 bc0 bc1 ep kp h' hself hupd hclk hml hmu hsc
  refine ⟨W1 w h', -mateUpper, f + 1, fun F hF => ?_, ?_, ?_, Or.inl ⟨hlo, hmateV⟩⟩
  · obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
    exact callIn_of_body (execStmts_mono hf (by simp) F' hF')
  · exact Bracket.TableAt.update_ne (Ne.symm hts) hupd ⟨es, ver, hdict, hok⟩
  · exact fun e _ => Bracket.SubtreeWrites.other (Ne.symm hts) hupd Bracket.SubtreeWrites.nil

/-! ## §7 `BoundRefines` AS RECORDED IS FALSE — proved, not suspected

§L24 finding 5: *`searcherObj`-style injectivity turns a suspicion into a
refutation, and the theorem is what stops the next lane re-introducing it.* This
section is that, applied to the rule the whole campaign runs on.

`BoundRefines V d` (§7 of `bound_depth.lean`) quantifies over an **arbitrary
`pos : RVal`** and asks for `∃ w' r t, ∀ F ≥ t, callIn … = .ok w' (.int r)`. At
`pos := .int 5` the shipped `bound()` reaches `pos.score` and REFUSES — attribute
access on an `int` is outside the tier — so no such `w'` exists and the
proposition is false. Not vacuous: FALSE, at every depth, for every `V`. The
induction `RecursionStep` runs cannot start, and no amount of interpreter work on
the leaves would ever have closed it.

It was found the way §L24 says these are found: by trying to DISCHARGE the
statement's hypotheses at a leaf rather than by reading them. -/

/-- The interpreter's own words when an attribute is read off an `int`. -/
def intAttrRefusal : String :=
  "attribute access on 'int' is outside the tier (heap receivers only; docs/memory-model.md)"

/-- **GATE — the king-capture check REFUSES at a non-`Position`.** The third arm
of statement 4, and the one no leaf can pay. -/
theorem mate_check_refuses (w : World) (e : REnv) (k : Int) (F : Nat)
    (hpos : Env.lookup e "pos" = some (.int k)) :
    execStmts sunfish (F + 8) ⟨w, e⟩ [sbMate] = .unsupported intAttrRefusal := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, hm⟩ := sbMate_lit
  rw [hm]
  py_simp [-globalsFold, -globalsStep, hpos, intAttrRefusal, RVal.typeName]
  rfl

/-- And the refusal is the whole body's, because `execStmts_append` propagates
any non-timeout result — the same engine the leaves compose with. -/
theorem body_refuses_int (w : World) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma d k : Int) (h' : Heap)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0)) :
    ∃ f, execStmts sunfish f ⟨w, sbEnv0 (.ref sa) (.int k) gamma d⟩ sbB
      = .unsupported intAttrRefusal := by
  have hA : ∃ f, execStmts sunfish f ⟨w, sbEnv0 (.ref sa) (.int k) gamma d⟩
      [sbDoc, sbNodes, sbClock]
      = .ok ⟨W1 w h', sbEnv0 (.ref sa) (.int k) gamma d⟩ .next :=
    ⟨16, bound_enters w ci sa ts tm hs n dl sf gamma d (.int k) h' hself hupd hclk⟩
  have hD : execStmts sunfish 8 ⟨W1 w h', sbEnv0 (.ref sa) (.int k) gamma d⟩ [sbDepth]
      = .ok ⟨W1 w h',
              Env.set (sbEnv0 (.ref sa) (.int k) gamma d) "depth" (.int (max d 0))⟩ .next :=
    depth_refloors (W1 w h') (sbEnv0 (.ref sa) (.int k) gamma d) d rfl rfl
  have hM := mate_check_refuses (W1 w h')
    (Env.set (sbEnv0 (.ref sa) (.int k) gamma d) "depth" (.int (max d 0))) k 0 rfl
  rw [sbB_split]
  exact execStmts_append (execStmts_append hA ⟨8, hD⟩ (by simp)) ⟨8, hM⟩ (by simp)

/-- `callIn_of_body`'s refusal twin: the boundary carries a refusal out too. -/
theorem callIn_of_body_unsupported {w : World} {sa : Addr} {pv : RVal} {gamma d : Int}
    {msg : String} {F : Nat}
    (h : execStmts sunfish F ⟨w, sbEnv0 (.ref sa) pv gamma d⟩ sbB = .unsupported msg) :
    callIn sunfish (F + 1) w "Searcher.bound" #[.ref sa, pv, .int gamma, .int d]
      = .unsupported msg := by
  obtain ⟨hfind, hargs, hloc, hgen, hbody, harity⟩ := sbF_lit
  rw [callIn, hfind]
  simp only [hargs, hloc, hgen, Bool.not_true, Bool.false_eq_true, if_neg,
    not_false_eq_true, hbody, sbCallEnv, h, Run.bind, Run.toWorld,
    show (#[RVal.ref sa, pv, RVal.int gamma, RVal.int d] : Array RVal).size = 4 from rfl,
    sbArity]

/-! The witness: two slots, a receiver and its (empty, valid) table. Every
hypothesis `BoundRefines` states is met on it — so the refutation is about the
CONCLUSION and cannot be dismissed as an unsatisfiable antecedent. -/

private def refHeap : Heap := #[searcherObj 0 1 1 1 0 0 0, .dict #[] 0]
private def refWorld : World := { heap := refHeap, globals := [] }

theorem refWorld_self : Heap.get? refWorld.heap 0 = some (searcherObj 0 1 1 1 0 0 0) := rfl

theorem refWorld_table (V : RVal → Int → Int) : (sfBracket V).TableAt refWorld.heap 1 :=
  ⟨#[], 0, rfl, Bracket.TableOK.nil _⟩

/-- **`BoundRefines V d` IS FALSE, at every depth and every value function.**
The repair is `BoundRefinesP` below; this theorem is what stops the next lane
re-introducing the statement it repairs. -/
theorem not_boundRefines (V : RVal → Int → Int) (d : Int) : ¬ BoundRefines V d := by
  intro hBR
  obtain ⟨h', hupd⟩ := update_exists (o' := searcherObj 0 1 1 1 (0 + 1) 0 0) refWorld_self
  obtain ⟨f, hbody⟩ := body_refuses_int refWorld 0 0 1 1 1 0 0 0 0 d 5 h'
    refWorld_self hupd (by decide)
  obtain ⟨w', r, t, hrun, -⟩ := hBR refWorld 0 0 1 1 1 0 0 0 0 (.int 5)
    refWorld_self (refWorld_table V) (by decide) (by decide)
  have h1 := hrun (max t (f + 1)) (Nat.le_max_left _ _)
  have h2 : callIn sunfish (max t (f + 1)) refWorld "Searcher.bound"
      #[.ref 0, .int 5, .int 0, .int d] = .unsupported intAttrRefusal := by
    have := callIn_of_body_unsupported
      (execStmts_mono hbody (by simp) (max t (f + 1) - 1)
        (by have := Nat.le_max_right t (f + 1); omega))
    rw [show max t (f + 1) - 1 + 1 = max t (f + 1) by
      have := Nat.le_max_right t (f + 1); omega] at this
    exact this
  rw [h1] at h2
  simp at h2

/-- **AND THE STEP IS VACUOUS.** `RecursionStep` is now a STRONG induction, so
its hypothesis is `∀ e, 0 ≤ e → e < d → BoundRefines V e` — and that is false at
`e = 0` for every `d ≥ 1`. So `RecursionStep V` holds for every value function,
in one line, with no interpreter and no fold. §L25's whole R1–R5 program is
priced to prove a theorem that is already true and says nothing.

This is the sharpest form of the finding, and the reason the repair belongs
before the campaign rather than after it: the campaign cannot fail loudly. -/
theorem recursionStep_vacuous (V : RVal → Int → Int) : RecursionStep V :=
  fun d hd hIH => absurd (hIH 0 (by omega) (by omega)) (not_boundRefines V 0)

/-! ### Two MORE holes in the same statement, measured rather than proved

The `pos` hole alone refutes it, so these two are recorded as measurements —
they matter because a lane that repairs only `pos` still has a false statement.
Both are the same shape: `BoundRefines` quantifies over something the shipped
code constrains and the statement does not.

**(b) THE CLOCK.** `n` is arbitrary, and `self.nodes % 2048 == 0 and time.time()
> self.deadline` reads the trace when the bump lands on a multiple. `BoundRefines`'
own docstring says it *"deliberately does not say"* anything about the clock —
but by saying nothing it admits `n = 2047`, where the default empty trace refuses
LOUDLY. `pins_search`'s frontier is about which traces suffice; this is about
whether the statement is true at all. -/
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance ci attrs) =>
       (match attrs.toList with
        | [("tp_score", .ref ts), ("tp_move", .ref tm), ("history", .ref hs),
           ("nodes", .int _), ("deadline", .int dl), ("soft", .int sft)] =>
          (match Heap.update w.heap a (searcherObj ci ts tm hs 2047 dl sft) with
           | some h' =>
             (match callIn sunfish 100000 { w with heap := h' } "Searcher.bound"
                 #[.ref a, posH 0, .int 0, .int 0] with
              | .unsupported _ => true      -- the trace underruns
              | _ => false)
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)

/-! And one below the multiple decides, so the guard above is about the CLOCK and
not about the fixture being broken. -/
#guard (match searcherW with
  | some (w, a) =>
    (match callIn sunfish 100000 w "Searcher.bound"
        #[.ref a, posH 0, .int 0, .int 0] with
     | .ok _ (.int r) => r == 0
     | _ => false)
  | Option.none => false)

/-! **(c) THE ENTRY SPELLING.** `TableAt` is `entryBounds`-shaped, and
`entryBounds` matches `.ntuple _ _ #[.int lo, .int up]` at ANY class name and ANY
field names — deliberately, because `DictCalc` is the general layer. But
`bound()` reads `entry.lower` and `entry.upper` BY NAME. So a table satisfying
`TableAt` can hold an entry the shipped code cannot read, and the probe raises
`AttributeError` instead of answering.

`Foo(a=20, b=900)` is such an entry: `entryBounds` decodes it to `(20, 900)`, so
`Bracket.Holds` and `TableAt` accept it, and `bound()` dies on it. The repair is
the `hspell` premise of `BoundRefinesP`. -/
#guard entryBounds (.ntuple "Foo" #["a", "b"] #[.int 20, .int 900]) == some (20, 900)
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance _ attrs) =>
       (match Env.lookup attrs.toList "tp_score" with
        | some (.ref ts) =>
          (match heapStore w.heap ts (tpKey (posH 0) 0)
              (.ntuple "Foo" #["a", "b"] #[.int 20, .int 900]) with
           | .ok h' =>
             (match callIn sunfish 100000 { w with heap := h' } "Searcher.bound"
                 #[.ref a, posH 0, .int 5, .int 0] with
              | .exn _ .attributeError => true
              | _ => false)
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)

/-! ## §8 `BoundRefinesP` — the repaired rule, and the base case's SPLIT

Four repairs, each named where it came from: the position is a `Position` (§7's
theorem), the node count does not land on the clock (§7 (b)), the table's entries
are the shipped SPELLING (§7 (c)), and the two mate constants are in the live
globals — which every head gate demands and `BoundRefines` never offered.

Nothing else moves: the four conjuncts out are `RefinesAt`, unchanged, so the
strong-induction restatement §L25's R4 forces still consumes this base case
as written. -/

/-- **The rule, with the premises the shipped code actually forces.** -/
def BoundRefinesP (V : RVal → Int → Int) (d : Int) : Prop :=
  ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int)
    (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (es : Array (RVal × RVal)) (sv : Nat),
    Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf) →
    Heap.get? w.heap ts = some (.dict es sv) →
    (sfBracket V).TableAt w.heap ts →
    (∀ p ∈ es.toList, ∃ lo up, p.2 = entryOf lo up) →
    ¬ ((n + 1).fmod 2048 = 0) →
    Env.lookup w.globals "MATE_LOWER" = some (.int mateLower) →
    Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper) →
    -mateUpper < gamma → gamma ≤ mateUpper →
    RefinesAt V d w sa ts gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp)

/-- **The probe always answers something the code can READ**, once the table's
entries are spelled — including on a miss, because the shipped default IS an
`entryOf`. This is the one derivation the spelling premise is for. -/
theorem probe_answer_spelled {es : Array (RVal × RVal)} {p : RVal} {d : Int}
    (hspell : ∀ q ∈ es.toList, ∃ lo up, q.2 = entryOf lo up) :
    ∃ lo up, (dictFind es.toList (tpKey p d)).getD entryDefault = entryOf lo up := by
  cases hf : dictFind es.toList (tpKey p d) with
  | none => exact ⟨-mateUpper, mateUpper, rfl⟩
  | some v =>
    obtain ⟨k', hmem, -⟩ := dictFind_sound es.toList hf
    obtain ⟨lo, up, hv⟩ := hspell (k', v) hmem
    exact ⟨lo, up, hv⟩

/-- **THE BASE CASE'S CASE SPLIT.** Four leaves, two of them proved here and two
supplied — and the two supplied ones are exactly what `qs_stand_pat_closed`
(§L23/§L24) and the unwritten fail-low leaf owe.

The split itself is arithmetic on `(pos.score, lo, up, gamma)` and it is TOTAL:
the king capture on `sc ≤ -MATE_LOWER`, then the lower return on `gamma ≤ lo`,
then the upper return on `up < gamma`, and what is left is `lo < gamma ≤ up` —
the fall-through, which is where `moves()` finally runs. If a fifth arm existed
this theorem would not elaborate. -/
theorem boundRefinesP_zero {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    (hmateV : ∀ (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int),
      sc ≤ -mateLower → V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0 ≤ -mateUpper)
    (hfall : ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int)
        (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
        (es : Array (RVal × RVal)) (sv : Nat) (lo up : Int),
      Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf) →
      Heap.get? w.heap ts = some (.dict es sv) →
      (sfBracket V).TableAt w.heap ts →
      ¬ ((n + 1).fmod 2048 = 0) →
      Env.lookup w.globals "MATE_LOWER" = some (.int mateLower) →
      Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper) →
      -mateUpper < gamma → gamma ≤ mateUpper → -mateLower < sc →
      (dictFind es.toList (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)).getD entryDefault
        = entryOf lo up →
      lo < gamma → gamma ≤ up →
      RefinesAt V 0 w sa ts gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp)) :
    BoundRefinesP V 0 := by
  intro w ci sa ts tm hs n dl sf gamma b sc wc0 wc1 bc0 bc1 ep kp es sv
    hself hdict ht hspell hclk hml hmu hlo hup
  by_cases hmate : sc ≤ -mateLower
  · exact refinesAt_king_capture w ci sa ts tm hs n dl sf gamma sc b wc0 wc1 bc0 bc1 ep kp
      hself ht hclk hml hmu hmate hlo (hmateV b sc wc0 wc1 bc0 bc1 ep kp hmate)
  · obtain ⟨lo, up, hfind⟩ :=
      probe_answer_spelled (p := posOf b sc wc0 wc1 bc0 bc1 ep kp) (d := 0) hspell
    by_cases hA : gamma ≤ lo
    · exact refinesAt_probe_hit hV w ci sa ts tm hs n dl sf gamma sc lo up
        b wc0 wc1 bc0 bc1 ep kp es sv hself hdict ht hclk hml hmu (by omega) hlo hup hfind
        (Or.inl hA)
    · by_cases hB : up < gamma
      · exact refinesAt_probe_hit hV w ci sa ts tm hs n dl sf gamma sc lo up
          b wc0 wc1 bc0 bc1 ep kp es sv hself hdict ht hclk hml hmu (by omega) hlo hup hfind
          (Or.inr hB)
      · exact hfall w ci sa ts tm hs n dl sf gamma b sc wc0 wc1 bc0 bc1 ep kp es sv lo up
          hself hdict ht hclk hml hmu hlo hup (by omega) hfind (by omega) (by omega)

/-! ### The axioms -/

#print axioms execStmts_append_escape
#print axioms probe_reads
#print axioms probe_lower_returns
#print axioms probe_lower_passes_at
#print axioms probe_upper_returns
#print axioms probe_upper_passes_at
#print axioms probe_block_returns
#print axioms body_returns_probe_hit
#print axioms bound_probe_hit
#print axioms sf_probe_brackets
#print axioms heapGet_of_find
#print axioms boundRefines_eq
#print axioms refinesAt_probe_hit
#print axioms mate_check_returns
#print axioms body_returns_king_capture
#print axioms refinesAt_king_capture
#print axioms mate_check_refuses
#print axioms body_refuses_int
#print axioms callIn_of_body_unsupported
#print axioms not_boundRefines
#print axioms recursionStep_vacuous
#print axioms probe_answer_spelled
#print axioms boundRefinesP_zero

/-! ## What the base case still owes — ONE hypothesis, in two halves

`boundRefinesP_zero` is the assembly, and after it the base case's whole
remaining debt is `hfall`: the leaf at `lo < gamma ≤ up`, where the probe answers
nothing decisive and `moves()` finally runs. It splits once more, on
`gamma ≤ pos.score`:

1. **the stand-pat CUT** — `qs_stand_pat_closed` (§L23/§L24) is this leaf over a
   CLEARED table, and consuming it needs three things it does not have. Its
   conclusion HIDES the world (`∃ w' t, …`), so `TableAt`/`SubtreeWrites` cannot
   be stated about it — the fix is to re-close `body_runs` (public, and it names
   the world `T1 (W4 …) ts …`) rather than to reprove anything. Its `hdict`
   pins `.dict #[]`, so `head_runs` needs `probe_reads` +
   `probe_lower_passes_at`/`probe_upper_passes_at` (all three above, and the two
   pass gates land here unspent for exactly this). And `mid_runs` pins
   `Heap.get? w.heap tm = some (.dict #[] svm)` — **the KILLER table**, which
   `BoundRefinesP` constrains no more than `BoundRefines` did. `tp_move` is read
   on every path (statement 6), so either the rule owes a `tp_move` premise or
   `killer_misses` owes a `killer_reads` generalisation, exactly as
   `probe_misses` owed `probe_reads`. Measured: at `gamma ≤ pos.score` a killer
   in `tp_move` does NOT change the answer (both 0, both heap 74) because the
   stand-pat yield precedes the killer test — so the leaf is true and the proof
   is what needs the generalisation. At `gamma > pos.score` it changes the run
   (heap 2882 against 2409), so the fail-low leaf needs it for real.
2. **the FAIL-LOW leaf** — the fold runs out and the store takes its other arm.
   The only leaf of the four that needs a fold, the only one that needs
   `fold_report`'s fail-low half, and the only one where `SubtreeWrites`' `.alloc`
   arm is finally spent — the two head leaves proved above never needed it, which
   is why they were the ones to do first.

`SubtreeWrites` at both is the same shape as here plus allocation: the counter
bump, the generator and sorted-list pushes, and the store — `.other`, `.alloc`
and `.store` in that order, and `trans` composes them. -/

end Examples.python.sunfish.basecase_depth0
