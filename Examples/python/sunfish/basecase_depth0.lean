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
are measured beside it, and a fourth after them. `BoundWF` + `BoundRefinesW`
(§8) is the repair, and `boundRefinesW_zero` is the base case's four-way split
assembled on it, with two of the four leaves proved here and the other two named
as one hypothesis.

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
The repair is `BoundRefinesW` below; this theorem is what stops the next lane
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
`BoundWF.spelled`. -/
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

/-! **(d) THE KILLER TABLE.** `tp_move` is read on EVERY path (statement 6,
`killer = self.tp_move.get(pos)`) and neither statement constrains it. At
`gamma ≤ pos.score` a killer is harmless — the `depth == 0` stand-pat yield
precedes the killer test, so the fold cuts first and the answer is the same
either way. At `gamma > pos.score` the fold REACHES the test, and
`pos.value(killer)` unpacks the killer: an `int` there raises `TypeError:
cannot unpack non-iterable int object`. So the statement is false a fourth time,
on the fall-through leaf. `BoundWF.killer` is the repair. -/
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance _ attrs) =>
       (match Env.lookup attrs.toList "tp_move" with
        | some (.ref tm) =>
          (match heapStore w.heap tm (posH 0) (.int 7) with
           | .ok h' =>
             -- harmless below the stand-pat, fatal above it
             (match callIn sunfish 1000000 { w with heap := h' } "Searcher.bound"
                 #[.ref a, posH 0, .int 0, .int 0] with
              | .ok _ (.int r) => r == 0
              | _ => false)
             && (match callIn sunfish 1000000 { w with heap := h' } "Searcher.bound"
                 #[.ref a, posH 0, .int 40, .int 0] with
              | .exn _ (.typeError _) => true
              | _ => false)
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)

/-! ## §8 `BoundWF` and `BoundRefinesW` — the repaired rule, and the base case's SPLIT

**One named predicate, `BoundWF`, and one added hypothesis, `IsPosition`.** That
is deliberately the whole delta: the four conjuncts out are `RefinesAt`,
unchanged (`boundRefines_eq` is the `rfl` receipt), and `pos` stays a free
`RVal` rather than becoming eight quantifiers — so re-expressing `RecursionStep`
over `BoundRefinesW` is a rename of one hypothesis and not a restructuring, and
the strong induction §L25's R4 forces consumes this base case as written.

`BoundWF` is *"the receiver and its three tables are what `Searcher.__init__`
builds, and the node count is not on the clock guard"*. Every conjunct is a fact
about the SHIPPED objects — `#guard`ed below on a real `Searcher()` — and every
one is a value the shipped `bound()` refuses without:

| conjunct | what refuses without it | evidence |
|---|---|---|
| `self` | nothing runs | §4's gates |
| `score` + `table` | the calculus has nothing to say | `BoundRefines` had both |
| `spelled` | `entry.lower` raises `AttributeError` | §7 (c) |
| `killer` | `pos.value(killer)` raises `TypeError: cannot unpack non-iterable int object` — measured at `gamma > pos.score`, where the fold reaches the killer test | §7 (d) |
| `history` | `pos in self.history` at `depth ≥ 1` | not read at depth 0 (short-circuit), so the base case never spends it; the STEP will |
| `clock` | the trace underruns | §7 (b) |
| `ml` / `mu` | `-MATE_LOWER` is a `NameError`; both constants are statically POISONED (`mlG`/`muG`), so the live globals decide | every head gate's premise list |

**Which leaves consume what.** `refinesAt_king_capture` spends `self`, `table`,
`clock`, `ml`, `mu`. `refinesAt_probe_hit` spends those plus `score` and — through
`probe_answer_spelled` — `spelled`. Neither spends `killer` or `history`: both
return before `moves()` is called, which is exactly why they were the two leaves
to prove first. The `hfall` hypothesis is where `killer` is spent, and the
depth-≥1 step is where `history` is.

**And the honest limit of this predicate.** `BoundWF` is COMPLETE for the two
leaves below — every premise each of them needs is discharged from it, which is
what `boundRefinesW_zero` typechecking says. For `hfall` and for the depth-≥1
step it is a best ESTIMATE, arrived at the way §L24's premise list was: by
reading the shipped body. §L24's own law governs what happens next — *a premise
is not paid until something DISCHARGES it* — so expect `hfall`'s proof to demand
a conjunct this structure does not have, and add it there rather than trusting
this list. The constants the fall-through reads (`QS_A`, `NULL_MARGIN`,
`EVAL_ROUGHNESS`, `TABLE_SIZE`) are the first place to look: unlike the two mate
constants they are statically resolvable (`nmarG`, `tsG`), so they need nothing
here — a claim to RE-CHECK when the fold's gates are composed, not one to
assume. -/

/-- **The shipped `Position` VALUE shape, as a predicate on a free `RVal`.**
`posOf` is the constructor; this is the same fact stated so a rule can keep
quantifying over `RVal` and constrain it, rather than replacing `pos` with the
eight fields. `not_boundRefines` (§7) is what makes it necessary. -/
def IsPosition (pos : RVal) : Prop :=
  ∃ (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int),
    pos = posOf b sc wc0 wc1 bc0 bc1 ep kp

/-- A shipped `Move`, as the fold unpacks it. -/
def mvOf (i j : Int) (prom : String) : RVal :=
  .ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str prom]

/-- **THE WELL-FORMEDNESS PREDICATE the repaired rule quantifies over.** Named
so the strong-induction step and the eventual assembly can both speak it. -/
structure BoundWF (V : RVal → Int → Int) (w : World) (ci : ClassId)
    (sa ts tm hs : Addr) (n dl sf : Int) (es : Array (RVal × RVal)) (sv : Nat) : Prop where
  /-- The receiver is the six-attribute instance `__init__` builds. -/
  self : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf)
  /-- `tp_score` is a dict, and these are its contents. -/
  score : Heap.get? w.heap ts = some (.dict es sv)
  /-- …satisfying the bracket schema. -/
  table : (sfBracket V).TableAt w.heap ts
  /-- …and every entry is the shipped `Entry` SPELLING, which `entry.lower` and
  `entry.upper` read BY NAME. `TableAt` alone does not say this (§7 (c)). -/
  spelled : ∀ p ∈ es.toList, ∃ lo up, p.2 = entryOf lo up
  /-- `tp_move` is a dict of shipped `Move`s. Read on EVERY path (statement 6)
  and unpacked by `Position.value` in the fold (§7 (d)). -/
  killer : ∃ (ms : Array (RVal × RVal)) (svm : Nat),
    Heap.get? w.heap tm = some (.dict ms svm)
      ∧ ∀ p ∈ ms.toList, ∃ i j prom, p.2 = mvOf i j prom
  /-- `history` is the set `__init__` builds. Not read at depth 0 — the
  repetition test short-circuits on `depth > 0` — and read at every depth above. -/
  history : ∃ items : Array RVal, Heap.get? w.heap hs = some (.pyset items)
  /-- The bump does not land on the clock guard (§7 (b)). -/
  clock : ¬ ((n + 1).fmod 2048 = 0)
  /-- Both mate constants are live; both are statically POISONED. -/
  ml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower)
  /-- ditto. -/
  mu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper)

/-- **THE REPAIRED RULE.** `BoundRefines` with `hself`/`TableAt` folded into
`BoundWF` and `IsPosition pos` added. Everything else is character-identical. -/
def BoundRefinesW (V : RVal → Int → Int) (d : Int) : Prop :=
  ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int) (pos : RVal)
    (es : Array (RVal × RVal)) (sv : Nat),
    BoundWF V w ci sa ts tm hs n dl sf es sv →
    IsPosition pos →
    -mateUpper < gamma → gamma ≤ mateUpper →
    RefinesAt V d w sa ts gamma pos

/-- **The probe always answers something the code can READ**, once the table's
entries are spelled — including on a miss, because the shipped default IS an
`entryOf`. This is the one derivation `BoundWF.spelled` is for. -/
theorem probe_answer_spelled {es : Array (RVal × RVal)} {p : RVal} {d : Int}
    (hspell : ∀ q ∈ es.toList, ∃ lo up, q.2 = entryOf lo up) :
    ∃ lo up, (dictFind es.toList (tpKey p d)).getD entryDefault = entryOf lo up := by
  cases hf : dictFind es.toList (tpKey p d) with
  | none => exact ⟨-mateUpper, mateUpper, rfl⟩
  | some v =>
    obtain ⟨k', hmem, -⟩ := dictFind_sound es.toList hf
    obtain ⟨lo, up, hv⟩ := hspell (k', v) hmem
    exact ⟨lo, up, hv⟩

/-- **THE BASE CASE'S CASE SPLIT.** Four leaves, two proved here and two supplied
as `hfall` — and the two supplied ones are exactly what `qs_stand_pat_closed`
(§L23/§L24) and the unwritten fail-low leaf owe.

The split is arithmetic on `(pos.score, lo, up, gamma)` and it is TOTAL: the king
capture on `sc ≤ -MATE_LOWER`, then the lower return on `gamma ≤ lo`, then the
upper return on `up < gamma`, and what is left is `lo < gamma ≤ up` — where
`moves()` finally runs. If a fifth arm existed this theorem would not
elaborate. -/
theorem boundRefinesW_zero {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    (hmateV : ∀ (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int),
      sc ≤ -mateLower → V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0 ≤ -mateUpper)
    (hfall : ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int)
        (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
        (es : Array (RVal × RVal)) (sv : Nat) (lo up : Int),
      BoundWF V w ci sa ts tm hs n dl sf es sv →
      -mateUpper < gamma → gamma ≤ mateUpper → -mateLower < sc →
      (dictFind es.toList (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)).getD entryDefault
        = entryOf lo up →
      lo < gamma → gamma ≤ up →
      RefinesAt V 0 w sa ts gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp)) :
    BoundRefinesW V 0 := by
  intro w ci sa ts tm hs n dl sf gamma pos es sv hwf hpos hlo hup
  obtain ⟨b, sc, wc0, wc1, bc0, bc1, ep, kp, rfl⟩ := hpos
  by_cases hmate : sc ≤ -mateLower
  · exact refinesAt_king_capture w ci sa ts tm hs n dl sf gamma sc b wc0 wc1 bc0 bc1 ep kp
      hwf.self hwf.table hwf.clock hwf.ml hwf.mu hmate hlo
      (hmateV b sc wc0 wc1 bc0 bc1 ep kp hmate)
  · obtain ⟨lo, up, hfind⟩ :=
      probe_answer_spelled (p := posOf b sc wc0 wc1 bc0 bc1 ep kp) (d := 0) hwf.spelled
    by_cases hA : gamma ≤ lo
    · exact refinesAt_probe_hit hV w ci sa ts tm hs n dl sf gamma sc lo up
        b wc0 wc1 bc0 bc1 ep kp es sv hwf.self hwf.score hwf.table hwf.clock hwf.ml hwf.mu
        (by omega) hlo hup hfind (Or.inl hA)
    · by_cases hB : up < gamma
      · exact refinesAt_probe_hit hV w ci sa ts tm hs n dl sf gamma sc lo up
          b wc0 wc1 bc0 bc1 ep kp es sv hwf.self hwf.score hwf.table hwf.clock hwf.ml hwf.mu
          (by omega) hlo hup hfind (Or.inr hB)
      · exact hfall w ci sa ts tm hs n dl sf gamma b sc wc0 wc1 bc0 bc1 ep kp es sv lo up
          hwf hlo hup (by omega) hfind (by omega) (by omega)

/-! ### `BoundWF` IS SATISFIED by the shipped engine

The repaired statement is worth nothing if its own premise cannot be met, and
`BoundWF` has nine conjuncts. Every one of them, recomputed on a real
`Searcher()` over the real `initWorld` — with a stale entry written through the
interpreter's own `heapStore` and a killer written into `tp_move`, so the two
CONTENTS conjuncts are checked against a populated table rather than an empty
one. -/
private def wfCheck : Bool :=
  match staleW 20 900 with
  | some (w, sa, ts) =>
    (match Heap.get? w.heap sa with
     | some (.instance ci attrs) =>
       (match attrs.toList with
        | [("tp_score", .ref ts'), ("tp_move", .ref tm), ("history", .ref hs),
           ("nodes", .int n), ("deadline", .int dl), ("soft", .int sft)] =>
          (match heapStore w.heap tm (posH 0) (mvOf 84 64 "") with
           | .ok h2 =>
             (match Heap.get? h2 ts, Heap.get? h2 tm, Heap.get? h2 hs with
              | some (.dict es sv), some (.dict ms _), some (.pyset _) =>
                -- self, score
                (ts' == ts)
                  && (Heap.get? h2 sa == some (searcherObj ci ts tm hs n dl sft))
                  && (sv == sv)
                  -- spelled: every tp_score value is an `entryOf`
                  && es.toList.all (fun p =>
                       match p.2 with
                       | .ntuple "Entry" #["lower", "upper"] #[.int lo, .int up] =>
                         p.2 == entryOf lo up
                       | _ => false)
                  -- killer: every tp_move value is an `mvOf`
                  && ms.toList.all (fun p =>
                       match p.2 with
                       | .ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str pr] =>
                         p.2 == mvOf i j pr
                       | _ => false)
                  && (es.size == 1) && (ms.size == 1)
                  -- clock, ml, mu
                  && !((n + 1).fmod 2048 == 0)
                  && (Env.lookup w.globals "MATE_LOWER" == some (.int mateLower))
                  && (Env.lookup w.globals "MATE_UPPER" == some (.int mateUpper))
              | _, _, _ => false)
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false

#guard wfCheck

/-! And `TableAt` — the one conjunct a `#guard` cannot check, because it mentions
the value function — holds on that table for `V = fun _ _ => 20`, which is what
`entryBounds (entryOf 20 900) = some (20, 900)` and `20 ≤ 20 ≤ 900` say. -/
#guard entryBounds (entryOf 20 900) == some (20, 900)
#guard pairKey (tpKey (posH 0) 0) == some (posH 0, 0)

/-! **And `IsPosition` is met by the fixture's own board**, which is what makes
§7's refutation a statement about `BoundRefines` and not about `RefinesAt`. -/
#guard posH 0 == (.ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
  #[.str board0, .int 0, .tuple #[.bool true, .bool true],
    .tuple #[.bool true, .bool true], .int 0, .int 0])

/-! ## §9 THE STAND-PAT CUT LEAF, with its world VISIBLE

§L23's `qs_stand_pat` and §L24's `qs_stand_pat_closed` both conclude
`∃ w' t, …` — they HIDE the world, so nothing about `TableAt w'.heap ts` or
`SubtreeWrites ts e w.heap w'.heap` can be stated about them, and a rule that
owes two conjuncts about the world cannot consume them. The repair needs no
reproving: **`body_runs` is public and NAMES its world**
(`T1 (W4 …) ts es sv pos sc hlt`), so re-closing the boundary on it recovers
what the `∃` threw away.

This section is that, plus the two world conjuncts, at a CLEARED table — and it
is where `SubtreeWrites`' `.alloc` arm is finally spent and where §L20's join
(`sf_store_from_report`) is finally applied at a real store.

**The heap chain, read off the world definitions rather than guessed:**

    w.heap  --(.other)-->  h'                    the node counter
            --(.alloc)-->  push guardCell        the cell (statement 7)
            --(.alloc)-->  push closure          the `moves` closure
            --(.alloc*)-->  ++ ext                the calm genexp (§L24)
            --(.alloc)-->  push generator        the `moves()` call and its step
            --(.store)-->  set ts                the table store (statement 15)

Six links, three constructors, and the `.store` link is legal at every `e > 0`
because the key's depth is `0`. -/

/-- One `push` is one `alloc` step. -/
theorem sw_push {S : Bracket} {a : Addr} {e : Int} {h : Heap} {o : Obj}
    (hlt : a < h.size) : S.SubtreeWrites a e h (h.push o) :=
  .alloc (h := h) (o := o) (b := h.size) rfl (Nat.ne_of_lt hlt) .nil

/-- A push keeps a live slot live. -/
theorem lt_size_push {a : Addr} {h : Heap} {o : Obj} (hlt : a < h.size) :
    a < (h.push o).size := by
  rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt

/-- So does an append. -/
theorem lt_size_append {a : Addr} {h ext : Heap} (hlt : a < h.size) :
    a < (h ++ ext).size := by
  rw [Array.size_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)

/-- **An arbitrary APPEND is a run of allocations.** `sbW3`'s `++ ext` (§L24's
repair for the calm genexp) is not a `Heap.update` and not one `Heap.alloc` — it
is `ext.size` of them, and this is the induction that says so. Without it the
genexp's world change cannot enter `SubtreeWrites` at all. -/
theorem sw_append {S : Bracket} {a : Addr} {e : Int} :
    ∀ (ext : Array Obj) {h : Heap}, a < h.size → S.SubtreeWrites a e h (h ++ ext)
  | ⟨[]⟩, h, _ => by simpa using Bracket.SubtreeWrites.nil
  | ⟨o :: os⟩, h, hlt => by
      have hstep : S.SubtreeWrites a e h (h.push o) := sw_push hlt
      have hrest : S.SubtreeWrites a e (h.push o) ((h.push o) ++ ⟨os⟩) :=
        sw_append ⟨os⟩ (lt_size_push hlt)
      have hcat : (h.push o) ++ (⟨os⟩ : Array Obj) = h ++ (⟨o :: os⟩ : Array Obj) := by
        apply Array.ext'; simp [Array.push]
      exact hcat ▸ hstep.trans hrest

/-- **The store, as `heapStore` rather than as the computed `.set`.** §L20's law
says a store gate must CONCLUDE with the computed heap, and §6's calculus is
stated over `heapStore` — so somebody has to bridge them, and this is the one
place it is owed. Both sides are the shipped `sbStored`. -/
theorem store_bridge {w4 : World} {ts : Addr} {es : Array (RVal × RVal)} {sv : Nat}
    {pv : RVal} {sc : Int} (hlt : ts < w4.heap.size)
    (hdict : Heap.get? w4.heap ts = some (.dict es sv)) (hk : hashableKey pv = true) :
    heapStore w4.heap ts (tpKey pv 0) (entryOf sc mateUpper)
      = .ok (T1 w4 ts es sv pv sc hlt).heap := by
  have hkk : hashableKey (tpKey pv 0) = true := by
    simp [tpKey, hashableKey, hashableKeyList, hk]
  simp only [heapStore, hdict, if_pos hkk, sbStored, T1, Heap.update, dif_pos hlt]

/-- **THE ALLOCATION CHAIN, before the store.** Links 1–5: the node counter and
the four allocations. It holds at EVERY `e` without a side condition — `.other`
and `.alloc` say nothing about depths — which is why it is the half that also
carries the invariant into `sf_store_from_report`. -/
theorem subtree_pre_store {V : RVal → Int → Int} {w : World} {h' : Heap}
    {ci : ClassId} {sa ts tm hs : Addr} {n dl sf gamma : Int} {pv : RVal}
    {av : Bool} {ext : Array Obj} {sv : Nat} {e : Int}
    (hts : ts ≠ sa)
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hdict1 : Heap.get? h' ts = some (.dict #[] sv)) :
    (sfBracket V).SubtreeWrites ts e w.heap (W4 w h' gamma pv av ext).heap := by
  have hlt0 : ts < h'.size := Heap.lt_size_of_get? hdict1
  have hlt1 := lt_size_push (o := guardCell) hlt0
  have hlt2 := lt_size_push (o := sbMovesClosure h'.size gamma 0 .none pv) hlt1
  have hlt3 := lt_size_append (ext := ext) hlt2
  have k1 : (sfBracket V).SubtreeWrites ts e w.heap h' := .other (Ne.symm hts) hupd .nil
  have k2 : (sfBracket V).SubtreeWrites ts e h' (h'.push guardCell) := sw_push hlt0
  have k3 : (sfBracket V).SubtreeWrites ts e (h'.push guardCell)
      ((h'.push guardCell).push (sbMovesClosure h'.size gamma 0 .none pv)) := sw_push hlt1
  have k4 : (sfBracket V).SubtreeWrites ts e
      ((h'.push guardCell).push (sbMovesClosure h'.size gamma 0 .none pv))
      (((h'.push guardCell).push (sbMovesClosure h'.size gamma 0 .none pv)) ++ ext) :=
    sw_append ext hlt2
  have k5 : (sfBracket V).SubtreeWrites ts e
      (((h'.push guardCell).push (sbMovesClosure h'.size gamma 0 .none pv)) ++ ext)
      (W4 w h' gamma pv av ext).heap := sw_push hlt3
  exact ((k1.trans k2).trans k3).trans (k4.trans k5)

/-- **THE WHOLE CHAIN**, at every depth an ancestor can probe. Link 6 is the
store, and it is the only link that needs `0 ≠ e` — the QS node keys at depth
`0`, so every ancestor probing above it is blind to the write. -/
theorem subtree_of_stand_pat {V : RVal → Int → Int} {w : World} {h' : Heap}
    {ci : ClassId} {sa ts tm hs : Addr} {n dl sf gamma sc : Int} {pv : RVal}
    {av : Bool} {ext : Array Obj} {sv : Nat} {e : Int}
    (hne : (0 : Int) ≠ e)
    (hts : ts ≠ sa)
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hdict1 : Heap.get? h' ts = some (.dict #[] sv))
    (hk : hashableKey pv = true)
    (hlt : ts < (W4 w h' gamma pv av ext).heap.size)
    (hlo : sc ≤ V pv 0) (hband : V pv 0 ≤ mateUpper) :
    (sfBracket V).SubtreeWrites ts e w.heap
      (T1 (W4 w h' gamma pv av ext) ts #[] sv pv sc hlt).heap := by
  have hdict4 : Heap.get? (W4 w h' gamma pv av ext).heap ts = some (.dict #[] sv) :=
    W4_get w h' gamma pv av ext hdict1
  have hholds : (sfBracket V).Holds (tpKey pv 0) (entryOf sc mateUpper) :=
    ⟨sc, mateUpper, V pv 0, entryBounds_entryOf sc mateUpper,
      by show (pairKey (tpKey pv 0)).map (fun pd => V pd.1 pd.2) = some (V pv 0)
         rw [pairKey_tpKey]; rfl,
      hlo, hband⟩
  exact (subtree_pre_store (V := V) (gamma := gamma) (pv := pv) (av := av) (ext := ext)
    hts hupd hdict1).trans (.store hne hholds (store_bridge hlt hdict4 hk) .nil)

set_option linter.unusedVariables false in
/-- **THE STAND-PAT CUT LEAF, world-visible.** `qs_stand_pat_closed`'s run with
its world named, plus the three conjuncts the `∃` made unstateable.

`TableAt` OUT is where §L20's join finally runs on a real store: the fold's
report IS the lower bound the stored `Entry(best, MATE_UPPER)` claims, and
`sf_store_from_report` is the theorem that says so. `hband` (`V pos 0 ≤
MATE_UPPER`) and `hsval` (`pos.score ≤ V pos 0` — the stand-pat is a LOWER bound
on the QS value) are the two model-side premises; both belong to `formal/`'s
depth-0 leaf, and `hband` is the one §L20 named and left open on purpose.

`hgen` and `hband'` are §L24's own residue, unchanged and open BY DESIGN: over a
free board nothing decides the calmness genexp, and the depth-0 window does not
imply the `±750` band. `hmove` (an empty `tp_move`) is `mid_runs`' premise, not
this leaf's choice — see the file tail. -/
theorem refinesAt_stand_pat {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    (w : World) (h' : Heap) (ci : ClassId) (sa ts tm hs : Addr)
    (n dl sf gamma sc : Int) (b : String) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (av : Bool) (ext : Array Obj) (Fg : Nat) (sv svm : Nat)
    (hself : Heap.get? w.heap sa = some (searcherObj ci ts tm hs n dl sf))
    (hupd : Heap.update w.heap sa (searcherObj ci ts tm hs (n + 1) dl sf) = some h')
    (hclk : ¬ ((n + 1).fmod 2048 = 0))
    (hdict : Heap.get? w.heap ts = some (.dict #[] sv))
    (ht : (sfBracket V).TableAt w.heap ts)
    (hmove : Heap.get? w.heap tm = some (.dict #[] svm))
    (hml : Env.lookup w.globals "MATE_LOWER" = some (.int mateLower))
    (hmu : Env.lookup w.globals "MATE_UPPER" = some (.int mateUpper))
    (hsc : -mateLower < sc) (hlo : -mateUpper < gamma) (hup : gamma ≤ mateUpper)
    (hband' : -750 < sc ∧ sc < 750) (hFg : 5 ≤ Fg)
    (hgen : evalExpr sunfish Fg
        ⟨sbW2 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp),
         G4 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)⟩ calmG
      = .ok ⟨sbW3 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) ext,
             G4 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma)⟩ (.bool av))
    (hge : gamma ≤ sc) (hmus : -mateUpper < sc)
    (hsval : sc ≤ V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)
    (hbandV : V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0 ≤ mateUpper) :
    RefinesAt V 0 w sa ts gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) := by
  have hts : ts ≠ sa := dict_ne_instance hself hdict
  have htm : tm ≠ sa := dict_ne_instance hself hmove
  have hk := posOf_hashable b sc wc0 wc1 bc0 bc1 ep kp
  have hobj1 : Heap.get? (W1 w h').heap sa = some (searcherObj ci ts tm hs (n + 1) dl sf) :=
    Heap.get?_update_self hupd
  have hdict1 : Heap.get? (W1 w h').heap ts = some (.dict #[] sv) :=
    (Heap.get?_update_ne hupd hts).trans hdict
  have hmove1 : Heap.get? (W1 w h').heap tm = some (.dict #[] svm) :=
    (Heap.get?_update_ne hupd htm).trans hmove
  -- the generator half, discharged exactly as `qs_stand_pat_closed` does
  have hev := moves_call_creates
    (sbW3 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) ext)
    (G9 (W1 w h') (FH sa (posOf b sc wc0 wc1 bc0 bc1 ep kp) gamma) av sc)
    (W1 w h').heap.size gamma .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) av Option.none
    (by simp [G9, G8, G7, G6, G5, G4, sbEnvDef, Env.lookup_set_ne, Env.lookup_set_self])
    (sbW3_cell (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) ext)
    (sbW3_closure (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) ext)
    (by simp [G9, G8, G7, G6, Env.lookup_set_ne, Env.lookup_set_self])
  have hyield := moves_first_iter
    (sbW3 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) ext)
    gamma .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) av
  have hobj4 : Heap.get? (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext).heap sa
      = some (searcherObj ci ts tm hs (n + 1) dl sf) :=
    W4_get w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext hobj1
  have hdict4 : Heap.get? (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext).heap ts
      = some (.dict #[] sv) :=
    W4_get w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext hdict1
  have hlt : ts < (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext).heap.size :=
    Heap.lt_size_of_get? hdict4
  have hu : Heap.update (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext).heap ts
      (sbStored #[] sv (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc)
      = some (T1 (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext) ts #[] sv
          (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt).heap := by
    simp only [Heap.update, T1, dif_pos hlt]
  have hobj5 := (Heap.get?_update_ne hu (Ne.symm hts)).trans hobj4
  have hdict5 := Heap.get?_update_self hu
  -- THE RUN, with the world named
  obtain ⟨f, hf⟩ := body_runs w
    (W3 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext)
    (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext) h'
    (sbW3 (W1 w h') gamma 0 .none (posOf b sc wc0 wc1 bc0 bc1 ep kp) ext).heap.size
    ci sa ts tm hs n dl sf gamma sc b wc0 wc1 bc0 bc1 ep kp av ext Fg sv svm
    #[] (dictStore ([] : List (RVal × RVal)) (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)
          (entryOf sc mateUpper)).1.toArray
    sv (if (dictStore ([] : List (RVal × RVal)) (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)
          (entryOf sc mateUpper)).2 = true then sv + 1 else sv)
    hlt hself hupd hclk hts hdict hml hmu hk hsc hlo hup
    hobj1 hmove1 hmu hband' hFg hgen hev
    (W3_gen w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext) hyield
    hobj4 hdict4 hobj5 hdict5 (by show ((1 : Nat) : Int) ≤ tableSize; decide) hge hmus
  refine ⟨T1 (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext) ts #[] sv
      (posOf b sc wc0 wc1 bc0 bc1 ep kp) sc hlt, sc, f + 1, fun F hF => ?_, ?_, ?_,
      Or.inr ⟨hge, hsval⟩⟩
  · obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧ f ≤ F' := ⟨F - 1, by omega, by omega⟩
    exact callIn_of_body (execStmts_mono hf (by simp) F' hF')
  · -- TableAt OUT: §L20's join, at the computed store
    refine sf_store_from_report hV (h := (W4 w h' gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp) av ext).heap)
      ?_ (Or.inr ⟨hge, hsval⟩) hge hbandV
      (store_bridge hlt hdict4 hk)
    -- the invariant survives the allocations the body made before the store
    exact sf_subtree_tableAt (e := (1 : Int)) hV
      (subtree_pre_store (V := V) (gamma := gamma)
        (pv := posOf b sc wc0 wc1 bc0 bc1 ep kp) (av := av) (ext := ext) hts hupd hdict1) ht
  · intro e he
    exact subtree_of_stand_pat (V := V) (e := e) (by omega) hts hupd hdict1 hk hlt hsval hbandV

/-! ### §9's chain, CORROBORATED slot by slot on the shipped engine

The proof's six links are a claim about the shape of the run's heap effect, and
the shipped engine answers it exactly. At `gamma = 0` on the opening board the
depth-0 cut run:

* **allocates four objects, in this order** — `cell`, `closure`, `generator`,
  `generator`. Those are `subtree_pre_store`'s links 2–5: the `<cell>guard`, the
  `moves` closure, the calm genexp's own generator (so `ext.size = 1`, which is
  §L24's 70 → 71 measurement seen from here), and the `moves()` generator;
* **moves exactly two live slots** — the receiver (the node counter, link 1's
  `.other`) and `tp_score` (the store, link 6's `.store`).

Six links, four allocations, two updates. If the chain had a link too many or
too few this guard would say so. -/
#guard (match searcherW with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound" #[.ref a, posH 0, .int 0, .int 0] with
     | .ok w' _ =>
       w.heap.size == 70 && w'.heap.size == 74
         && ((List.range w.heap.size).filter
              (fun i => Heap.get? w.heap i != Heap.get? w'.heap i) == [66, 67])
         && ((List.range' w.heap.size 4).map
              (fun i => match Heap.get? w'.heap i with
                        | some (.cell _) => "cell"
                        | some (.closure ..) => "closure"
                        | some (.generator ..) => "generator"
                        | _ => "other")
             == ["cell", "closure", "generator", "generator"])
     | _ => false)
  | Option.none => false)

/-! And the entry the store leaves is `sbStored`'s own — `Entry(best, MATE_UPPER)`
at `(pos, 0)`, one entry, which is what `store_bridge` claims and what
`sf_store_from_report` brackets. -/
#guard (match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance _ attrs) =>
       (match Env.lookup attrs.toList "tp_score" with
        | some (.ref ts) =>
          (match callIn sunfish 1000000 w "Searcher.bound"
              #[.ref a, posH 0, .int 0, .int 0] with
           | .ok w' _ => Heap.get? w'.heap ts == some (sbStored #[] 0 (posH 0) 0)
           | _ => false)
        | _ => false)
     | _ => false)
  | Option.none => false)

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
#print axioms boundRefinesW_zero
#print axioms sw_append
#print axioms store_bridge
#print axioms subtree_pre_store
#print axioms subtree_of_stand_pat
#print axioms refinesAt_stand_pat

/-! ## What the base case still owes — and why it is NOT one more leaf

Three of the four arms are proved: the king capture, the stale-table probe hit
(both returns), and now the stand-pat CUT. `boundRefinesW_zero` is still stated
against `hfall` rather than unconditionally, and the reasons are worth being
exact about, because two of the three are statement-level and one is structural.

**(1) THE FAIL-LOW ARM IS NOT A LEAF — it is a SECOND INDUCTION.** This is the
structural one, and `bound_depth.lean` already contains its proof in two pieces.
`qs_child_depth_eq` says `max (moveDepth 0 false false) 0 = 0`: at depth 0 a
searched real move recurses at depth 0 — *"a QS node's children store under the
QS node's OWN key"* — and §8's guards measure it, `bd_probe (posH 0) 40 0 =
some (4, 34)` against `bd_probe (posH 0) 0 0 = some (0, 1)`. **34 nodes.** So the
fail-low arm's `Report` consumes a report from a depth-0 CHILD, which is
`BoundRefinesW V 0` itself — circular. No amount of interpreter work closes it;
what closes it is a second induction on the QS termination measure (calmness,
not depth), which is what `formal/`'s fuel model exists for. §L25's plan lists
this as one of three sibling leaves; it is not a sibling.

The good news is that everything ELSE the fail-low arm needs is now built: its
`SubtreeWrites` is `subtree_pre_store` plus one `.store` plus the children's own
subtrees composed by `trans`, and the children's stores are at depth `0 ≠ e` for
every `e > 0` exactly as link 6 is.

**(2) The cut leaf is CLEARED-table.** `hfall` is stated at an arbitrary `es`,
and `refinesAt_stand_pat` needs `es = #[]`. Two shipped gates are why, and both
are `probe_misses → probe_reads` again:

* `mid_runs` pins `Heap.get? w.heap tm = some (.dict #[] svm)` — an empty
  `tp_move`. Owed: `killer_reads`, and `mid_runs` recomposed at it.
* `store_runs`/`tail_runs` pin `Env.lookup e "entry" = some entryDefault`,
  because the store's fail-high arm reads `entry.upper`: over a stale table the
  shipped line writes `Entry(best, up)` and not `Entry(best, MATE_UPPER)`. Owed:
  `store_runs` at an arbitrary entry, with `sbStored` carrying `up`.
  **The calculus side of that is already free** — `sf_store_from_report` would
  then need `V pos 0 ≤ up`, which is exactly what `sf_probe_brackets` reads off
  the probed entry. The stale entry's own upper bound is what validates the new
  one.

**(3) Two premises are open BY DESIGN and always were** (§L18, §L24): the
calmness genexp `hgen` over a free board, and the `±750` band. They are
`QSStandPatB`'s residue, they are not this lane's to close, and they ride into
`refinesAt_stand_pat` unchanged.

**And the two model-side premises are named, not hidden.** `hbandV`
(`V pos 0 ≤ MATE_UPPER`, the mate band — §L20 named it and left it open) and
`hsval` (`pos.score ≤ V pos 0`, the stand-pat is a LOWER bound on the QS value).
Both belong to `formal/`'s depth-0 leaf, beside `hmateV`'s exact
`V pos 0 ≤ -MATE_UPPER` at a captured king. Three model facts, one per arm, and
no arm needs anything else from the model. -/

end Examples.python.sunfish.basecase_depth0
