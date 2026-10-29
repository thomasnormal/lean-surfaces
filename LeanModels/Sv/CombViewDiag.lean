import LeanModels.Sv.CombViewMain

/-!
# `sv_structure`: diagnostics (pure functions, no proofs depend on them)

* `Summary.describe`    — the `sv_structure?` hint: declarations, sites, families, windows, reads
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

def TTgt.showR (rn : String → String) : TTgt → String
  | .whole n => n
  | .bit n a => s!"{n}[{a.showR rn}]"
  | .arr n a => s!"{n}[{a.showR rn}]"

def TTgt.show (t : TTgt) : String := t.showR id

def TRd.show : TRd → String
  | .whole n => n
  | .bit n a => s!"{n}[{a.show}]"
  | .arr n a => s!"{n}[{a.show}]"

def SiteId.show : SiteId → String
  | .plain p => s!"plain#{p}"
  | .fam l p idx => s!"{l}#{p}[{", ".intercalate (idx.map toString)}]"

def showWin (w : Win) : String :=
  let (n, lo, wd) := w
  if wd == 1 then s!"{n}[{lo}]" else s!"{n}[{lo} +: {wd}]"

def DeclT.show (dt : DeclT) : String :=
  let dir := if dt.isInput then "input " else if dt.isOutput then "output" else "      "
  match dt.dim with
  | none => s!"{dir} {dt.name}"
  | some (_, m, l) => s!"{dir} {dt.name} [{m.show} : {l.show}]"

def TSite.show (st : TSite) (id : String) : String :=
  s!"{id} : drives {st.tgt.show}   reads [{", ".intercalate (st.rds.map TRd.show)}]"

/-- The `sv_structure?` text. -/
def Summary.describe (s : Summary) : String := Id.run do
  let mut out := s!"sv_structure: parameters {s.params}\ndeclarations:\n"
  for dt in s.decls do
    out := out ++ s!"  {dt.show}\n"
  out := out ++ "plain sites (module-level assigns):\n"
  for st in s.statics do
    out := out ++ s!"  {st.show s!"plain#{st.pos}"}\n"
  match s.fam with
  | none => out := out ++ "families: none\n"
  | some f =>
      out := out ++ s!"family `{f.label}`: for {f.g} in [{f.c0}, {f.bound.show}):\n"
      for st in f.body do
        out := out ++ s!"  {st.show s!"{f.label}#{st.pos}[{f.g}]"}\n"
  out := out ++ "rank relation a certificate must satisfy (writer < reader whenever the read window\n"
  out := out ++ "overlaps the written window; ranks are functions of the site identity):\n"
  -- (site name for a reader, site name for a writer, site)
  let readers : List (String × TSite) :=
    s.statics.map (fun st => (s!"plain#{st.pos}", st)) ++
    (match s.fam with
     | none => []
     | some f => f.body.map (fun st => (s!"{f.label}#{st.pos}[{f.g}]", st)))
  let writers : List (String × String × TSite) :=
    s.statics.map (fun st => (s!"plain#{st.pos}", "", st)) ++
    (match s.fam with
     | none => []
     | some f => f.body.map (fun st => (s!"{f.label}#{st.pos}[{f.g}']", f.g, st)))
  for (rid, rst) in readers do
    for r in rst.rds do
      for (wid, wg, wst) in writers do
        if wst.tgt.name == r.name then
          let rn := fun n => if n == wg && wg != "" then n ++ "'" else n
          out := out ++ s!"  rank({wid}) < rank({rid})   [{rid} reads {r.show}; {wid} drives {wst.tgt.showR rn}]\n"
  return out

/-! ## Structural problems -/

def Summary.structProblems (s : Summary) : List String := Id.run do
  let mut ps : List String := []
  unless s.declNames.Nodup do
    ps := ps ++ ["declaration names are not pairwise distinct"]
  let sid (st : TSite) (isFam : Bool) : String :=
    match s.fam with
    | some f => if isFam then s!"{f.label}#{st.pos}" else s!"plain#{st.pos}"
    | none => s!"plain#{st.pos}"
  let check (st : TSite) (isFam : Bool) (allowed : List String) : List String := Id.run do
    let mut qs : List String := []
    for n in st.names do
      unless s.declNames.contains n do
        qs := qs ++ [s!"site `{sid st isFam}` mentions the undeclared signal `{n}`"]
    if s.inputNames.contains st.tgt.name then
      qs := qs ++ [s!"site `{sid st isFam}` drives the input port `{st.tgt.name}`"]
    for n in st.affNames do
      unless allowed.contains n do
        qs := qs ++ [s!"site `{sid st isFam}`: index mentions `{n}`, which is neither a parameter nor the loop variable"]
    for n in st.arrNames do
      unless s.arrOk n do
        qs := qs ++ [s!"site `{sid st isFam}`: array select on `{n}` needs `{n}` declared as a zero-based descending vector `[hi:0]`"]
    return qs
  for st in s.statics do
    ps := ps ++ check st false s.params
  match s.fam with
  | none => pure ()
  | some f =>
      for st in f.body do
        ps := ps ++ check st true (f.g :: s.params)
      for n in f.bound.names do
        unless s.params.contains n && n != f.g do
          ps := ps ++ [s!"family `{f.label}`: the bound mentions `{n}`, which is not a parameter"]
      if f.c0 < 0 then
        ps := ps ++ [s!"family `{f.label}`: the loop starts at a negative value {f.c0}"]
  for dt in s.decls do
    for n in dt.affNames do
      unless s.params.contains n do
        ps := ps ++ [s!"declaration `{dt.name}`: bound mentions `{n}`, which is not a parameter"]
  return ps

/-! ## Small-`N` counterexamples to the player obligations -/

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

/-- A write window outside its declared signal (or at a negative index). -/
def Summary.rangeCounterexample (s : Summary) (σ : String → Int) : Option String :=
  (s.insts σ).findSome? fun a =>
    match s.DW σ a.win.1 with
    | none => some s!"`{a.id.show}` drives the undeclared signal `{a.win.1}`"
    | some dw =>
        if a.win.2.1 + a.win.2.2 ≤ dw then none
        else some s!"`{a.id.show}` drives {showWin a.win}, outside `{a.win.1}` which is only {dw} bit(s) wide"

/-- A read at a negative index. -/
def Summary.negCounterexample (s : Summary) (σ : String → Int) : Option String :=
  let neg (_i : Int) (σs : String → Int) (st : TSite) (id : String) : Option String :=
    (st.rds.findSome? fun r =>
      match r with
      | .bit n a => if a.eval σs < 0 then some s!"`{id}` reads {n}[{a.eval σs}], a negative index" else none
      | _ => none)
  (s.statics.findSome? fun st => neg 0 σ st s!"plain#{st.pos}") <|>
  (match s.fam with
   | none => none
   | some f => (f.range σ).findSome? fun i =>
       f.body.findSome? fun st => neg i (bindσ f.g i σ) st s!"{f.label}#{st.pos}[{i}]")

/-- A read whose driver does not have a smaller rank. -/
def Summary.rankCounterexample (s : Summary) (σ : String → Int) (ρ : SiteId → Nat) :
    Option String :=
  let is := s.insts σ
  is.findSome? fun a =>
    is.findSome? fun b =>
      a.rd.findSome? fun r =>
        if ReadWin.overlaps r b.win && !(decide (ρ b.id < ρ a.id)) then
          some s!"the rank does not decrease along a read: `{a.id.show}` (rank {ρ a.id}) reads a window of `{r.name}` driven by `{b.id.show}` (rank {ρ b.id}, window {showWin b.win}); a driver must have a SMALLER rank than its reader"
        else none

end CombView
end LeanModels.Sv
