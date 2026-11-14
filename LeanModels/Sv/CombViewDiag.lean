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
  let qs := a.qs.map fun (n, k, d) => if k == 1 then s!"{rn n}/{d}" else s!"{k}*({rn n}/{d})"
  let ts := ts ++ qs
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
  | _, .clog2 a | _, .clog2S a => s!"$clog2({a.showP 0})"
  -- a shift binds less tightly than `+` and `-` (IEEE 1800-2023 Table 11-2): its operands are parenthesized unless atomic
  | p, .shl a b => let t := s!"{a.showP 1} << {b.showP 1}"; if p ≥ 1 then s!"({t})" else t
  | p, .shr a b => let t := s!"{a.showP 1} >> {b.showP 1}"; if p ≥ 1 then s!"({t})" else t
  | p, .ashr a b => let t := s!"{a.showP 1} >>> {b.showP 1}"; if p ≥ 1 then s!"({t})" else t
  -- `**` binds more tightly than `*` (Table 11-2): its operands are parenthesized unless atomic
  | p, .pow a b => let t := s!"{a.showP 3} ** {b.showP 3}"; if p ≥ 3 then s!"({t})" else t
  | p, .cmp k a b =>
      let o := match k with
        | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .eq => "==" | .ne => "!="
      let t := s!"{a.showP 1} {o} {b.showP 1}"; if p ≥ 1 then s!"({t})" else t
  | p, .cond c a b => let t := s!"{c.showP 1} ? {a.showP 1} : {b.showP 1}"; if p ≥ 1 then s!"({t})" else t

def CE.show (c : CE) : String := c.showP 0

/-- The signed 32-bit range. -/
def inInt32 (v : Int) : Bool := decide (-2147483648 ≤ v) && decide (v < 2147483648)

/-- (Refusal text only.) The operand `a` of `c` (`/`, `%`, `$clog2`) outside the range. -/
def CE.operandDiag (σ : String → Int) (c a : CE) : Option String :=
  let v := a.eval σ
  if inInt32 v then none
  else some s!"the operand `{a.show}` of `{c.show}` is {v} at these parameters, outside the signed 32-bit range [-2147483648, 2147483647]: the instantiation wraps it to {canonInt 32 true v} first (IEEE 1800-2023 §11.4, §11.6.1, §11.8.1: every operand and result of an `int` expression is 32 bits wide) and the summary reads the unbounded value, so a definition that divides, takes a remainder of or the `$clog2` of a value outside the range is outside the fragment"

/-- (Refusal text only.) The operations of a definition where the summary and the instantiation read an operand or a
result differently, innermost first (`CE.wrapDiag`): an operand of `/`, `%` or `$clog2` outside the 32-bit range (the
summary reads it unbounded, the instantiation at its 32-bit value), and a `>>>` of a negative `int` by a negative amount
(below). `+ - *` and the shifts read their operands as 32-bit patterns or values already (`CE.eval`), and the
instantiation's `<<` and `>>` agree with IEEE 1800-2023 §11.4.10 on every amount (a negative one, an unsigned amount of
2^31 or more, shifts every bit out: 0), so for them only the RESULT's range matters, at the root.

The `>>>` case: §11.4.10 reads the amount as an unsigned number, so a negative 32-bit amount shifts every bit out and the
arithmetic shift of a negative `int` fills the result with its sign bit, -1 (`CE.eval`; local Icarus Verilog 12.0 and
Verilator 5.042 print -1 for `-8 >>> -1`, provisional rows), while the instantiation gives 0 for every negative amount
(`evalIntExactRec`'s `.ashr`; the semantics owners have the finding). Only the operands' 32-bit values are evaluated here,
not the shift itself. -/
def CE.opDiag (σ : String → Int) : CE → Option String
  | .lit _ | .ref _ => none
  | .add a b | .sub a b | .mul a b | .shl a b | .shr a b => a.opDiag σ <|> b.opDiag σ
  -- the exponent's value and the comparison's operands are read whole by the summary and at 32 bits by the
  -- instantiation; the arm `?:` selects is read by both alike (only the condition's value decides)
  | .pow a b => a.opDiag σ <|> b.opDiag σ <|> CE.operandDiag σ (.pow a b) b
  | .cmp k a b => a.opDiag σ <|> b.opDiag σ <|> CE.operandDiag σ (.cmp k a b) a <|> CE.operandDiag σ (.cmp k a b) b
  | .cond c a b =>
      c.opDiag σ <|> CE.operandDiag σ (.cond c a b) c <|> (if c.eval σ = 0 then b.opDiag σ else a.opDiag σ)
  | .divK a k => a.opDiag σ <|> CE.operandDiag σ (.divK a k) a
  | .modK a k => a.opDiag σ <|> CE.operandDiag σ (.modK a k) a
  | .clog2 a => a.opDiag σ <|> CE.operandDiag σ (.clog2 a) a
  | .clog2S a => a.opDiag σ <|> CE.operandDiag σ (.clog2S a) a
  | .ashr a b =>
      a.opDiag σ <|> b.opDiag σ <|>
        (let va := canonInt 32 true (a.eval σ)
         let vb := canonInt 32 true (b.eval σ)
         if va < 0 ∧ vb < 0 then
           some s!"`{(CE.ashr a b).show}` shifts the negative `int` {va} right by the negative amount {vb}: IEEE 1800-2023 §11.4.10 reads the amount as the unsigned {vb % 4294967296}, which shifts every bit out and fills the result with the sign bit (the value -1), and the instantiation gives 0 for every negative amount (`evalIntExactRec`; the semantics owners have the finding); an arithmetic shift of a negative `int` by a negative amount is outside the fragment"
         else none)

/-- A `>>>` occurs in the definition. -/
def CE.hasAshr : CE → Bool
  | .ashr _ _ => true
  | .add a b | .sub a b | .mul a b | .shl a b | .shr a b | .pow a b | .cmp _ a b => a.hasAshr || b.hasAshr
  | .cond c a b => c.hasAshr || a.hasAshr || b.hasAshr
  | .divK a _ | .modK a _ | .clog2 a | .clog2S a => a.hasAshr
  | _ => false

/-- (Refusal text only.) What a statement at a symbolic parameter needs for a definition with a `>>>` (`CE.opDiag`'s
case, which a symbolic point cannot evaluate). -/
def CE.ashrHint (c : CE) : String :=
  if c.hasAshr then " (the definition has a `>>>`: of a negative `int` by a negative amount it is -1 under IEEE 1800-2023 §11.4.10, every bit shifted out and the sign bit filled in, and 0 in the instantiation, `evalIntExactRec`; a statement needs premises that keep its amount or its operand non-negative; the semantics owners have the finding)"
  else ""

/-- (Refusal text only; no theorem reads it.) **Where a localparam's definition leaves its reading** at the valuation
`σ`: an operation whose operand the two readings take differently (`CE.opDiag`), else the definition's value itself outside
the signed 32-bit range (the instantiation's value is its 32-bit wrap). `none`: the two readings agree. -/
def CE.wrapDiag (σ : String → Int) (c : CE) : Option String :=
  c.opDiag σ <|>
    (let v := c.eval σ
     if inInt32 v then none
     else some s!"the value of the definition `{c.show}` is {v} at these parameters, outside the signed 32-bit range [-2147483648, 2147483647]: the instantiation's value is its 32-bit wrap {canonInt 32 true v} (IEEE 1800-2023 §11.4, §11.6.1, §11.8.1: every result of an `int` expression is 32 bits wide), and the summary reads the unbounded value, so a localparam whose value leaves the range is outside the fragment")

/-! Where the readings part (`(N * 1000000) / 1000000` at `N = 10000`: the product is 10000000000, which the
instantiation wraps to 1410065408 before it divides, so the quotient is 1410; and `(1 << 31) - 1`, which does NOT part:
`1 << 31` wraps to `-2^31` and the difference back to `2^31 - 1`). `(N - 16) >> 1` does not part either: at `N = 8` both
read the pattern of -8 shifted with a zero, 2147483644 (the instantiation's reading since master 853147a63); `(N - 16) >> 0`
there is the pattern itself, 4294967288 in the summary and -8 in the instantiation, a value out of range: -/
#guard (CE.wrapDiag (fun _ => 10000) (.divK (.mul (.ref "N") (.lit 1000000)) 1000000)).isSome
#guard (CE.wrapDiag (fun _ => 1000) (.divK (.mul (.ref "N") (.lit 1000000)) 1000000)).isNone
#guard (CE.wrapDiag (fun _ => 8) (.shr (.sub (.ref "N") (.lit 16)) (.lit 1))).isNone
#guard (CE.wrapDiag (fun _ => 20) (.shr (.sub (.ref "N") (.lit 16)) (.lit 1))).isNone
#guard (CE.wrapDiag (fun _ => 8) (.shr (.sub (.ref "N") (.lit 16)) (.lit 0))).isSome
/-! `(N - 16) >>> (N - 9)` at `N = 8`, -8 by -1: IEEE -1, the instantiation 0 (`opDiag`, which evaluates the operands
only: the shift by the unsigned amount 2^32 - 1 is never computed); at `N = 20` (4 by 11) the readings agree, and so they
do for a non-negative operand by a negative amount (`N = 16`: 0 by -7): -/
#guard (CE.opDiag (fun _ => 8) (.ashr (.sub (.ref "N") (.lit 16)) (.sub (.ref "N") (.lit 9)))).isSome
#guard (CE.opDiag (fun _ => 20) (.ashr (.sub (.ref "N") (.lit 16)) (.sub (.ref "N") (.lit 9)))).isNone
#guard (CE.opDiag (fun _ => 16) (.ashr (.sub (.ref "N") (.lit 16)) (.sub (.ref "N") (.lit 9)))).isNone
#guard (CE.wrapDiag (fun _ => 32) (.sub (.shl (.lit 1) (.sub (.ref "E") (.lit 1))) (.lit 1))).isNone
#guard (CE.wrapDiag (fun _ => 33) (.sub (.shl (.lit 1) (.sub (.ref "E") (.lit 1))) (.lit 1))).isSome

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
  let more := if st.more.isEmpty then "" else s!" and {", ".intercalate (st.more.map Acc.show)}"
  s!"{id} : drives {st.tgt.show}{more}   reads [{", ".intercalate (st.rds.map Acc.show)}]"

/-- The printed name of a located site, loop indices renamed. -/
def LSite.label (ls : LSite) (rn : String → String) : String :=
  if ls.hdrs.isEmpty then s!"plain#{ls.site.pos}"
  else s!"{ls.blk}#{ls.site.pos}[{", ".intercalate (ls.hdrs.map fun h => rn h.g)}]"

def GCmp.show : GCmp → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">=" | .eq => "==" | .ne => "!="

def Guard.show (g : Guard) : String := s!"{g.a.show} {g.op.show} {g.b.show}"

mutual
/-- The `sv_structure?` lines of an item of a loop body under the loops `pre`, in the block `blk` (indent `ind`). -/
def showItem (ind : String) (pre : List Hdr) (blk : String) : TItem → String
  | .site st => s!"{ind}{st.show s!"{blk}#{st.pos}[{", ".intercalate (pre.map (·.g))}]"}\n"
  | .loop h _ body =>
      s!"{ind}inner family `{h.name}`: for {h.g} in [{h.c0}, {h.bound.show}):\n" ++
        showItems (ind ++ "  ") (pre ++ [h]) h.name body
  | .cond _ g thn els =>
      s!"{ind}if {g.show}:\n" ++ showItems (ind ++ "  ") pre blk thn ++
        s!"{ind}else:\n" ++ showItems (ind ++ "  ") pre blk els

def showItems (ind : String) (pre : List Hdr) (blk : String) : List TItem → String
  | [] => ""
  | it :: rest => showItem ind pre blk it ++ showItems ind pre blk rest
end

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
    out := out ++ showItems "  " [f.hdr] f.hdr.name f.body
  out := out ++ "rank relation a certificate must satisfy (writer < reader whenever the read window\n"
  out := out ++ "overlaps the written window; ranks are functions of the site identity):\n"
  for a in s.lsites do
    for r in a.site.rds do
      for b in s.lsites do
        for t in b.site.tgt :: b.site.more do
          if t.name == r.name then
            let rnW := fun n => if b.hdrs.any (·.g == n) then n ++ "'" else n
            let rid := a.label id
            let wid := b.label rnW
            out := out ++ s!"  rank({wid}) < rank({rid})   [{rid} reads {r.show}; {wid} drives {t.showR rnW}]\n"
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
    for t in ls.site.tgt :: ls.site.more do
      if s.inputNames.contains t.name then
        ps := ps ++ [s!"site `{id}` drives the input port `{t.name}`"]
    for n in ls.site.affNames do
      unless (ls.hdrs.map (·.g) ++ s.params).contains n do
        ps := ps ++ [s!"site `{id}`: an index or a shift amount mentions `{n}`, which is neither a parameter nor an enclosing loop variable"]
    for a in ls.site.tgt :: (ls.site.more ++ ls.site.rds) do
      unless s.accOk a do
        ps := ps ++ [s!"site `{id}`: the access `{a.show}` does not match the declaration of `{a.name}` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)"]
  for p in s.hdrPaths do
    unless (p.map (·.g) ++ s.params).Nodup do
      ps := ps ++ [s!"loop variables {p.map (·.g)} are not distinct from each other and from the parameters {s.params}"]
    for h in p do
      for n in h.bound.names do
        unless s.params.contains n || ((p.map (·.g)).contains n && n != h.g) do
          ps := ps ++ [s!"loop `{h.name}`: the bound mentions `{n}`, which is neither a parameter nor the genvar of an enclosing loop"]
      if h.c0 < 0 then
        ps := ps ++ [s!"loop `{h.name}`: the loop starts at a negative value {h.c0}"]
  for c in s.condSteps do
    for n in c.2.1.gvLeaves do
      unless (c.1.map (·.g)).contains n do
        ps := ps ++ [s!"generate condition `{c.2.2.show}`: it reads `{n}`, which is not the genvar of an enclosing loop"]
    for n in c.2.1.pLeaves do
      unless s.params.contains n do
        ps := ps ++ [s!"generate condition `{c.2.2.show}`: it reads `{n}`, which is not a parameter"]
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

/-- The first pair of windows of two different instances that overlap (every window of an instance counts). -/
def firstOverlapPair : List SiteInst → Option (SiteInst × Win × SiteInst × Win)
  | [] => none
  | a :: rest =>
      match rest.findSome? (fun b => a.wins.findSome? fun wa => b.wins.findSome? fun wb =>
          if Win.overlaps wa wb then some (a, wa, b, wb) else none) with
      | some r => some r
      | none => firstOverlapPair rest

/-- Two windows of ONE instance (a body that writes several windows) that overlap. -/
def firstSelfOverlap : List SiteInst → Option (SiteInst × Win × Win)
  | [] => none
  | a :: rest =>
      match (a.wins.zipIdx.findSome? fun (wa, i) =>
          (a.wins.drop (i + 1)).findSome? fun wb => if Win.overlaps wa wb then some (a, wa, wb) else none) with
      | some r => some r
      | none => firstSelfOverlap rest

/-- Two sites drive one bit (or one body writes a bit twice). -/
def Summary.disjCounterexample (s : Summary) (σ : String → Int) : Option String :=
  match firstOverlapPair (s.insts σ) with
  | some (a, wa, b, wb) =>
      some s!"the one-driver rule fails: `{a.id.show}` drives {showWin wa} and `{b.id.show}` drives {showWin wb}, which share a bit"
  | none =>
      match firstSelfOverlap (s.insts σ) with
      | some (a, wa, wb) =>
          some s!"`{a.id.show}` writes {showWin wa} and {showWin wb} in one always_comb body, which share a bit"
      | none => none

/-- A write window outside its declared signal (the flat check). -/
def Summary.rangeCounterexample (s : Summary) (σ : String → Int) : Option String :=
  (s.insts σ).findSome? fun a => a.wins.findSome? fun w =>
    match s.DW σ w.1 with
    | none => some s!"`{a.id.show}` drives the undeclared signal `{w.1}`"
    | some dw =>
        if w.2.1 + w.2.2 ≤ dw then none
        else some s!"`{a.id.show}` drives {showWin w}, outside `{w.1}` which is only {dw} bit(s) wide"

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
    (ls.site.tgt :: (ls.site.more ++ ls.site.rds)).findSome? fun a =>
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
        match b.wins.find? (ReadWin.overlaps r) with
        | some wb =>
            if !(lt b.id a.id) then
              some s!"the rank does not decrease along a read: `{a.id.show}` (rank {showRank a.id}) reads a window of `{r.name}` driven by `{b.id.show}` (rank {showRank b.id}, window {showWin wb}); a driver must have a SMALLER rank than its reader"
            else none
        | none => none

/-- The read that forms the edge `rankCounterexample` reports, in source form with its indices evaluated
(`t[1][0]`): the second line of the message `sv_structure` prints for a rank that does not decrease. It
walks the sites, drivers and reads in the order `rankCounterexample` does, so it names the same edge. -/
def Summary.rankReadNote (s : Summary) (σ : String → Int) (lt : SiteId → SiteId → Bool) :
    Option String :=
  let is := s.insts σ
  (is.zip (s.instPairs σ)).findSome? fun (a, ls, σ') =>
    is.findSome? fun b =>
      (a.rd.zip ls.site.rds).findSome? fun (r, acc) =>
        match b.wins.find? (ReadWin.overlaps r) with
        | some wb =>
            if !(lt b.id a.id) then
              some s!"\n  the read that forms the edge: `{acc.showVal σ'}` of `{a.id.show}`, written by `{b.id.show}` (window {showWin wb})"
            else none
        | none => none

end CombView
end LeanModels.Sv
