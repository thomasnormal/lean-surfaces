import LeanModels.Sv.CombViewMain

/-!
# `sv_structure`: diagnostics (pure functions, no proofs depend on them)

* `Summary.describe`    — the `sv_structure?` hint: declarations, sites, loops, windows, reads
  and the rank relation a rank certificate has to satisfy (site identities as in design
  principle 13).
* `Summary.structProblems` — the specific reason a structural check fails.
* `Summary.*Counterexample` — concrete small-`N` refutations of the player obligations
  (a SAMPLE for the error message only; they never discharge anything: the leftover goals are
  still the symbolic ones).
-/

namespace LeanModels.Sv
namespace CombView

/-! ## Printing -/

/-- Print an affine form, renaming variables (the second loop index is shown as `i'`). -/
def Aff.showR (a : Aff) (rn : String → String) : String :=
  let ts := a.terms.map fun (n, k) => if k == 1 then rn n else s!"{k}*{rn n}"
  let parts := ts ++ (if a.c != 0 || ts.isEmpty then [toString a.c] else [])
  (" + ".intercalate parts).replace "+ -" "- "

def Aff.show (a : Aff) : String := a.showR id

/-- A localparam's definition, printed with the minimal parentheses (`0`: anywhere; `1`: an operand
of a product or a quotient on the left, or the right operand of a sum; `2`: the right operand of a
product). -/
def CE.showP : Nat → CE → String
  | _, .lit v => if v < 0 then s!"({v})" else toString v
  | _, .ref n => n
  | p, .add a b => let t := s!"{a.showP 0} + {b.showP 1}"; if p ≥ 1 then s!"({t})" else t
  | p, .sub a b => let t := s!"{a.showP 0} - {b.showP 1}"; if p ≥ 1 then s!"({t})" else t
  | p, .mul a b => let t := s!"{a.showP 1} * {b.showP 2}"; if p ≥ 2 then s!"({t})" else t
  | p, .divK a k => let t := s!"{a.showP 1} / {k}"; if p ≥ 2 then s!"({t})" else t
  | p, .modK a k => let t := s!"{a.showP 1} % {k}"; if p ≥ 2 then s!"({t})" else t

def CE.show (c : CE) : String := c.showP 0

/-- The module parameters (the constants `args` binds), without the localparams. -/
def Summary.pnames (s : Summary) : List String := s.params.take (s.params.length - s.lps.length)

/-- An access, with its index variables renamed. -/
def Acc.showR (rn : String → String) : Acc → String
  | .whole n => n
  | .bit n a => s!"{n}[{a.showR rn}]"
  | .cell1 n a => s!"{n}[{a.showR rn}]"
  | .row n _ r => s!"{n}[{r.showR rn}]"
  | .cell2 n _ r c => s!"{n}[{r.showR rn}][{c.showR rn}]"
  | .part1 n hi lo => s!"{n}[{hi.showR rn}:{lo.showR rn}]"
  | .part2 n _ r hi lo => s!"{n}[{r.showR rn}][{hi.showR rn}:{lo.showR rn}]"

def Acc.show (a : Acc) : String := a.showR id

/-- An access at a valuation (indices evaluated). -/
def Acc.showVal (σ : String → Int) : Acc → String
  | .whole n => n
  | .bit n a => s!"{n}[{a.eval σ}]"
  | .cell1 n a => s!"{n}[{a.eval σ}]"
  | .row n _ r => s!"{n}[{r.eval σ}]"
  | .cell2 n _ r c => s!"{n}[{r.eval σ}][{c.eval σ}]"
  | .part1 n hi lo => s!"{n}[{hi.eval σ}:{lo.eval σ}]"
  | .part2 n _ r hi lo => s!"{n}[{r.eval σ}][{hi.eval σ}:{lo.eval σ}]"

def SiteId.show : SiteId → String
  | .plain p => s!"plain#{p}"
  | .fam l p idx => s!"{l}#{p}[{", ".intercalate (idx.map toString)}]"

/-- A rank key, printed as a triple. -/
def showKey (k : Key) : String := s!"({k.1}, {k.2.1}, {k.2.2})"

def showWin (w : Win) : String :=
  let (n, lo, wd) := w
  if wd == 1 then s!"{n}[{lo}]" else s!"{n}[{lo} +: {wd}]"

def DeclT.show (dt : DeclT) : String :=
  let dir := if dt.isInput then "input " else if dt.isOutput then "output" else "      "
  let dims := " ".intercalate (dt.dims.map fun p => s!"[{p.2.1.show} : {p.2.2.show}]")
  if dt.dims.isEmpty then s!"{dir} {dt.name}" else s!"{dir} {dt.name} {dims}"

def TSite.show (st : TSite) (id : String) : String :=
  s!"{id} : drives {st.tgt.show}   reads [{", ".intercalate (st.rds.map Acc.show)}]"

/-- The printed name of a located site, loop indices renamed. -/
def LSite.label (ls : LSite) (rn : String → String) : String :=
  if ls.hdrs.isEmpty then s!"plain#{ls.site.pos}"
  else s!"{ls.blk}#{ls.site.pos}[{", ".intercalate (ls.hdrs.map fun h => rn h.g)}]"

/-- The `sv_structure?` text. -/
def Summary.describe (s : Summary) : String := Id.run do
  let mut out := s!"sv_structure: parameters {s.pnames}\n"
  if !s.lps.isEmpty then
    out := out ++ "localparams:\n"
    for (n, c) in s.lps do
      out := out ++ s!"  {n} = {c.show}\n"
  out := out ++ "declarations:\n"
  for dt in s.decls do
    out := out ++ s!"  {dt.show}\n"
  out := out ++ "plain sites (module-level assigns):\n"
  for st in s.statics do
    out := out ++ s!"  {st.show s!"plain#{st.pos}"}\n"
  if s.fams.isEmpty then
    out := out ++ "families: none\n"
  for f in s.fams do
    out := out ++ s!"family `{f.hdr.name}`: for {f.hdr.g} in [{f.hdr.c0}, {f.hdr.bound.show}):\n"
    for it in f.body do
      match it with
      | .site st =>
          out := out ++ s!"  {st.show s!"{f.hdr.name}#{st.pos}[{f.hdr.g}]"}\n"
      | .loop l =>
          out := out ++ s!"  inner family `{l.hdr.name}`: for {l.hdr.g} in [{l.hdr.c0}, {l.hdr.bound.show}):\n"
          for st in l.body do
            out := out ++ s!"    {st.show s!"{l.hdr.name}#{st.pos}[{f.hdr.g}, {l.hdr.g}]"}\n"
  out := out ++ "rank relation a certificate must satisfy (writer < reader whenever the read window\n"
  out := out ++ "overlaps the written window; ranks are functions of the site identity):\n"
  for a in s.lsites do
    for r in a.site.rds do
      for b in s.lsites do
        if b.site.tgt.name == r.name then
          let rnW := fun n => if b.hdrs.any (·.g == n) then n ++ "'" else n
          let rid := a.label id
          let wid := b.label rnW
          out := out ++ s!"  rank({wid}) < rank({rid})   [{rid} reads {r.show}; {wid} drives {b.site.tgt.showR rnW}]\n"
  return out

/-! ## Structural problems -/

def Summary.structProblems (s : Summary) : List String := Id.run do
  let mut ps : List String := []
  unless s.declNames.Nodup do
    ps := ps ++ ["declaration names are not pairwise distinct"]
  for ls in s.lsites do
    let id := ls.label id
    for n in ls.site.names do
      unless s.declNames.contains n do
        ps := ps ++ [s!"site `{id}` mentions the undeclared signal `{n}`"]
    if s.inputNames.contains ls.site.tgt.name then
      ps := ps ++ [s!"site `{id}` drives the input port `{ls.site.tgt.name}`"]
    for n in ls.site.affNames do
      unless (ls.hdrs.map (·.g) ++ s.params).contains n do
        ps := ps ++ [s!"site `{id}`: index mentions `{n}`, which is neither a parameter nor an enclosing loop variable"]
    for a in ls.site.tgt :: ls.site.rds do
      unless s.accOk a do
        ps := ps ++ [s!"site `{id}`: the access `{a.show}` does not match the declaration of `{a.name}` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)"]
  for p in s.hdrPaths do
    unless (p.map (·.g) ++ s.params).Nodup do
      ps := ps ++ [s!"loop variables {p.map (·.g)} are not distinct from each other and from the parameters {s.params}"]
    for h in p do
      for n in h.bound.names do
        unless s.params.contains n do
          ps := ps ++ [s!"loop `{h.name}`: the bound mentions `{n}`, which is not a parameter"]
      if h.c0 < 0 then
        ps := ps ++ [s!"loop `{h.name}`: the loop starts at a negative value {h.c0}"]
  let keys := s.lsites.map LSite.key
  for i in [0:keys.length] do
    for j in [i+1:keys.length] do
      if keys[i]! == keys[j]! then
        let a := s.lsites[i]!
        let b := s.lsites[j]!
        ps := ps ++ [s!"two sites share the identity (`{a.label id}` and `{b.label id}`): generate blocks need distinct labels"]
  for dt in s.decls do
    for n in dt.affNames do
      unless s.params.contains n do
        ps := ps ++ [s!"declaration `{dt.name}`: bound mentions `{n}`, which is not a parameter"]
  return ps

/-! ## Small-`N` counterexamples to the player obligations -/

/-- Every (located site, valuation) pair of the closed-form enumeration. -/
def Summary.instPairs (s : Summary) (σ : String → Int) : List (LSite × (String → Int)) :=
  s.enum (fun ls σ' _ => (ls, σ')) σ {}

def firstOverlapPair : List SiteInst → Option (SiteInst × SiteInst)
  | [] => none
  | a :: rest =>
      match rest.find? (fun b => Win.overlaps a.win b.win) with
      | some b => some (a, b)
      | none => firstOverlapPair rest

/-- Two sites drive one bit. -/
def Summary.disjCounterexample (s : Summary) (σ : String → Int) : Option String :=
  match firstOverlapPair (s.insts σ) with
  | none => none
  | some (a, b) =>
      some s!"the one-driver rule fails: `{a.id.show}` drives {showWin a.win} and `{b.id.show}` drives {showWin b.win}, which share a bit"

/-- A write window outside its declared signal (the flat check). -/
def Summary.rangeCounterexample (s : Summary) (σ : String → Int) : Option String :=
  (s.insts σ).findSome? fun a =>
    match s.DW σ a.win.1 with
    | none => some s!"`{a.id.show}` drives the undeclared signal `{a.win.1}`"
    | some dw =>
        if a.win.2.1 + a.win.2.2 ≤ dw then none
        else some s!"`{a.id.show}` drives {showWin a.win}, outside `{a.win.1}` which is only {dw} bit(s) wide"

/-- The in-range facts of an access, as a `Bool` (mirrors `Summary.InR`). -/
def Summary.inRBool (s : Summary) (σd σs : String → Int) : Acc → Bool
  | .whole _ => true
  | .bit _ a => decide (0 ≤ a.eval σs)
  | .cell1 n a => decide (0 ≤ a.eval σs ∧ a.eval σs ≤ s.dm σd n 0)
  | .row n _ r => decide (0 ≤ r.eval σs ∧ r.eval σs ≤ s.dm σd n 0)
  | .cell2 n _ r c =>
      decide (0 ≤ r.eval σs ∧ r.eval σs ≤ s.dm σd n 0 ∧ 0 ≤ c.eval σs ∧ c.eval σs ≤ s.dm σd n 1)
  | .part1 n hi lo => decide (0 ≤ lo.eval σs ∧ lo.eval σs ≤ hi.eval σs ∧ hi.eval σs ≤ s.dm σd n 0)
  | .part2 n _ r hi lo =>
      decide (0 ≤ r.eval σs ∧ r.eval σs ≤ s.dm σd n 0 ∧ 0 ≤ lo.eval σs ∧ lo.eval σs ≤ hi.eval σs ∧
        hi.eval σs ≤ s.dm σd n 1)

/-- An access outside the declared dimensions of its signal (a negative index, a row or column past
the end). -/
def Summary.accCounterexample (s : Summary) (σ : String → Int) : Option String :=
  (s.instPairs σ).findSome? fun (ls, σ') =>
    (ls.site.tgt :: ls.site.rds).findSome? fun a =>
      if s.inRBool σ σ' a then none
      else
        let dims := (s.dimsOf' a.name).getD []
        let shape := "".intercalate (dims.map fun p => s!"[{p.1.eval σ}:{p.2.eval σ}]")
        some s!"`{ls.label (fun n => toString (σ' n))}` accesses {a.showVal σ'}, outside `{a.name}` which is declared {shape}"

/-- A read whose driver does not have a smaller rank. `lt w r` says writer `w` is ranked below
reader `r`; `showRank` prints a rank (or key). -/
def Summary.rankCounterexample (s : Summary) (σ : String → Int) (lt : SiteId → SiteId → Bool)
    (showRank : SiteId → String) : Option String :=
  let is := s.insts σ
  is.findSome? fun a =>
    is.findSome? fun b =>
      a.rd.findSome? fun r =>
        if ReadWin.overlaps r b.win && !(lt b.id a.id) then
          some s!"the rank does not decrease along a read: `{a.id.show}` (rank {showRank a.id}) reads a window of `{r.name}` driven by `{b.id.show}` (rank {showRank b.id}, window {showWin b.win}); a driver must have a SMALLER rank than its reader"
        else none

/-- The read that forms the edge `rankCounterexample` reports, in source form with its indices evaluated
(`t[1][0]`): the second line of the message `sv_structure` prints for a rank that does not decrease. It
walks the sites, drivers and reads in the order `rankCounterexample` does, so it names the same edge. -/
def Summary.rankReadNote (s : Summary) (σ : String → Int) (lt : SiteId → SiteId → Bool) :
    Option String :=
  let is := s.insts σ
  (is.zip (s.instPairs σ)).findSome? fun (a, ls, σ') =>
    is.findSome? fun b =>
      (a.rd.zip ls.site.rds).findSome? fun (r, acc) =>
        if ReadWin.overlaps r b.win && !(lt b.id a.id) then
          some s!"\n  the read that forms the edge: `{acc.showVal σ'}` of `{a.id.show}`, written by `{b.id.show}` (window {showWin b.win})"
        else none

end CombView
end LeanModels.Sv
