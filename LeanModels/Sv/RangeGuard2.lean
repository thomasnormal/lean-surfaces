import LeanModels.Sv.Hier2

/-!
# The legacy-select range guard (round 3 folds, 2026-10-28)

The extractor keeps a select of a declared signal in the LEGACY encoding
(`PExpr.bitSel`/`partSel`, `PLhs.bitSel`/`partSel` over an identifier)
exactly where its labels are offsets from bit 0 at the default point: a
dimension declared with lsb `0` and descending there (`logic [N-1:0] v`)
whose labels name a genvar or read a signal (`v[g]`, `v[s]`), or a
dimension with literal bounds, whose literal labels it folds to offsets.
`instExpr2`/`instLhs2` lower such a select to the window at the label's
offset (`.slice`, `.index`). That is exact at a parameter point P exactly
when every dimension of the declaration is, at P, either declared with
literal bounds (the extractor's folded offsets never move) or `[m:0]` with
`m ≥ 0` (labels ARE offsets). Anywhere else the window is wrong: at
`N = 0`, `logic [N-1:0] v` is the ascending two-bit `[-1:0]`, and `o =
v[s]` with `s = 1` reads label -1 (offset 1) where Icarus 12.0 and Yosys
0.53 read x (label 1 is out of range); `y[g] = v[g]` writes the wrong bit.

**Why a separate check, not part of `name.sem`.** The lowering lemmas
(`instExpr2_bitSel_ident`, `instExpr2_bitSel_ident_dyn`, `instLhs2_bitSel`,
…) and the instantiation lemmas (`PDesign.instantiate2_eq`,
`PDesign.instantiateG2_of_ok`, `PDesign.instantiateGD2_of_ok`,
`PDesign.instantiateH_of_rec`, `PDesign.instantiateH_flat`) are stated for
EVERY environment and design, and the ∀-N examples (`ripple_add`, `mul2d`,
`partsel`, `ripple_fa`) and the svGolf reference solutions rely on
`name.sem` being definitionally `instantiateGD2`/`instantiateHD2`. Adding
the guard to any of those definitions would falsify a recorded statement.
So the guard is a CHECK beside the semantic family, run by every consumer
that decides whether a point is admitted:

* `load_design_sv2` (`Ingest2.lean`) — at the defaults AND at every point
  of the envelope's probe sidecar (the svGolf checker always probes the
  task's probe, scoring and backstop points), refusing the envelope;
* the differential runner (`harness/sv/runner2.lean`) — at each row's
  point, refusing the row (`Select:legacy-range`);
* `PDesign.legacyRangeReport` for any other tool.

**Reached selects only.** A declaration violates the guard at P only when
some legacy select names it AND it is still mentioned by the instantiated
design at P (`Design2` processes). `ripple_add` selects `a[i]` inside a
generate loop that has no iteration at `N = 0`: nothing of `a` is reached
there, and the design is exact (its `ripple_sem_eq` holds for every
`N : Nat`), so the guard passes. "Mentioned" is conservative — a
declaration also read whole or through an `ArraySel` path at P is refused
with it (loud, never silent).

**Hierarchies.** Each module is checked at ITS point, in its own scope
(`PDesign.instantiateRecR`, the twin of `instantiateRec` that guards every
level before the child is flattened); the semantic trace still comes from
the official `instantiateH` — the twin only decides admission.

## Round 6 (2026-10-29): two more reports beside the same guard

The Xcelium audit (`docs/sv-xcelium-audit.md`) found two constructs on which
the tools split and the model had silently chosen the LRM reading. Both are
refused HERE — beside `name.sem`, for the reason above — and are reported
with their own kind by `PDesign.selectGuardReport` (which the loader and the
differential runner call; `legacyRangeReport` is the unchanged legacy half):

* `Select:partial-overhang` — a CONSTANT slice that leaves its signal
  PARTLY (`lo < W < lo + w`), the lowering of a LEGACY `partSel`
  (`v[9:6]` on `[7:0]`; `v[K+2:K]` at `K = 6`; a genvar label past the end)
  whose `.slice` x-pads silently. IEEE 1800-2023 §11.5.1 reads x in the
  out-of-range bits only and Icarus 12.0, Yosys 0.53 and slang agree;
  Xcelium 24.03 reads the whole select as x (writes: drops the whole write).
  The `ArraySel` path refuses the same overhang in `Param2.lean`
  (`ArraySel:partial-overhang`) and leaves no such slice behind. A slice wholly
  outside (x read, no-op write: every tool agrees) and a single-bit select are
  unchanged.
* `Select:wide-index` — a bit-select whose index is wider than 32 bits and
  is not an elaboration-time constant here (`v[a - P]` over a 42-bit `a`), or
  whose constant value is 2^32 or more. §11.5.1 takes the index whole (out of
  range: x; Yosys `prep; eval` agrees); Xcelium 24.03 (warning BIGWBS),
  Icarus 12.0 and Verilator 5.042 truncate it to its low 32 bits. The model
  does NOT truncate. Checked on the PExpr (`selfWidth2` is the model's own
  width authority), so a generate-local declaration the point's width table
  does not know is not judged (a recorded gap). Only code the point
  INSTANTIATES is judged (`PDesign.liveBitIdxs`: the taken `genIf` arm, the
  iterations `genvarSeq` yields, each under its genvar binding), so a wide
  index in an uninstantiated arm or a zero-iteration loop does not refuse
  (round 6 repair, verifier finding: it did while every arm was walked).
-/

namespace LeanModels.Sv

/-! ## Legacy-selected declarations -/

/-- The declared signal a legacy select chain reads (`v[i]`, `m[s][1]`,
`v[3:0]`), if its root is an identifier. -/
def PExpr.legacyRoot? : PExpr → Option String
  | .ident n => some n
  | .bitSel b _ | .partSel b _ _ | .cast _ b => b.legacyRoot?
  | _ => none

mutual
/-- Every declared signal some legacy `bitSel`/`partSel` of this expression
selects (with repeats). -/
def PExpr.legacySelNames : PExpr → List String
  | .bitSel b i => (b.legacyRoot?.toList) ++ b.legacySelNames ++ i.legacySelNames
  | .partSel b m l => (b.legacyRoot?.toList) ++ b.legacySelNames ++ m.legacySelNames
      ++ l.legacySelNames
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a
  | .reduce _ a | .cast _ a => a.legacySelNames
  | .binary _ l r | .repl l r => l.legacySelNames ++ r.legacySelNames
  | .ternary c t e => c.legacySelNames ++ t.legacySelNames ++ e.legacySelNames
  | .concat ps | .arrayElem _ ps => PExpr.legacySelNamesList ps
  | .arrayPart _ ps _ a b =>
      PExpr.legacySelNamesList ps ++ a.legacySelNames ++ b.legacySelNames
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _ | .fill _
  | .unsupported .. => []

/-- `PExpr.legacySelNames` over a list. -/
def PExpr.legacySelNamesList : List PExpr → List String
  | [] => []
  | p :: ps => p.legacySelNames ++ PExpr.legacySelNamesList ps
end

mutual
/-- … of an assignment target (its own legacy windows and its index
reads). -/
def PLhs.legacySelNames : PLhs → List String
  | .ident _ => []
  | .bitSel n i => n :: i.legacySelNames
  | .partSel n m l => n :: (m.legacySelNames ++ l.legacySelNames)
  | .concat ps => PLhs.legacySelNamesList ps
  | .arrayElem _ is => PExpr.legacySelNamesList is
  | .arrayPart _ is _ a b => PExpr.legacySelNamesList is ++ a.legacySelNames ++ b.legacySelNames

/-- `PLhs.legacySelNames` over a list. -/
def PLhs.legacySelNamesList : List PLhs → List String
  | [] => []
  | t :: ts => t.legacySelNames ++ PLhs.legacySelNamesList ts
end

mutual
/-- … of a statement. -/
def PStmt.legacySelNames : PStmt → List String
  | .blockingAssign _ v | .nbaAssign _ v => v.legacySelNames
  | .blockingAssignL t v | .nbaAssignL t v => t.legacySelNames ++ v.legacySelNames
  | .ifStmt c t e => c.legacySelNames ++ t.legacySelNames ++ PStmt.legacySelNamesOpt e
  | .block body => PStmt.legacySelNamesList body
  | .caseStmt s items d _ _ =>
      s.legacySelNames ++ PStmt.legacySelNamesItems items ++ PStmt.legacySelNamesOpt d
  | .unsupported .. => []

/-- … of an optional statement. -/
def PStmt.legacySelNamesOpt : Option PStmt → List String
  | none => []
  | some s => s.legacySelNames

/-- … of a statement list. -/
def PStmt.legacySelNamesList : List PStmt → List String
  | [] => []
  | s :: ss => s.legacySelNames ++ PStmt.legacySelNamesList ss

/-- … of `case` items (patterns and bodies). -/
def PStmt.legacySelNamesItems : List (List PExpr × PStmt) → List String
  | [] => []
  | (ps, s) :: rest =>
      PExpr.legacySelNamesList ps ++ s.legacySelNames ++ PStmt.legacySelNamesItems rest
end

/-- … of a process. -/
def PProcess.legacySelNames : PProcess → List String
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b | .alwaysFFR _ _ b => b.legacySelNames
  | .assign _ v => v.legacySelNames
  | .assignL t v => t.legacySelNames ++ v.legacySelNames
  | .unsupported .. => []

/-- … of an instance's port connections (input actuals are values of the
instantiating scope, output actuals its targets). -/
def PConn.legacySelNames : PConn → List String
  | .input _ (some e) _ => e.legacySelNames
  | .output _ (some t) => t.legacySelNames
  | _ => []

mutual
/-- … of a generate item (every branch and loop body, instantiated or
not: reachability is decided on the instantiated design). -/
def GenItem.legacySelNames : GenItem → List String
  | .process p => p.legacySelNames
  | .genFor _ _ _ _ _ _ body => GenItem.legacySelNamesList body
  | .genIf _ t e => GenItem.legacySelNamesList t ++ GenItem.legacySelNamesList e
  | .unsupported .. => []
  | .inst i => i.conns.flatMap PConn.legacySelNames

/-- … of a generate item list. -/
def GenItem.legacySelNamesList : List GenItem → List String
  | [] => []
  | g :: gs => g.legacySelNames ++ GenItem.legacySelNamesList gs
end

/-- Every declaration of `d` some legacy select names (duplicates removed,
first-occurrence order). -/
def PDesign.legacySelNames (d : PDesign) : List String :=
  (d.processes.flatMap PProcess.legacySelNames ++ GenItem.legacySelNamesList d.generates).eraseDups

/-! ## The check -/

/-- Whether the instantiated design mentions the signal `n` anywhere (a
read, a write, an index, a clock): the renaming of `n` changes it. -/
def Design2.mentions (m : Design2) (n : String) : Bool :=
  let f : String → String := fun x => if x == n then "\u0001" ++ x else x
  m.processes.any fun p => toString (repr (p.rename f f)) != toString (repr p)

/-- Whether a dimension declared with bounds `dim` is, at this point
(`(l, r)` evaluated), exact for the legacy offset encoding: literal bounds
(offsets folded by the extractor), or `[m:0]` with `m ≥ 0`. -/
def legacyDimOk (dim : PDim) (lr : Int × Int) : Bool :=
  (dim.msb.isLitBound && dim.lsb.isLitBound) || (lr.2 == 0 && decide (0 ≤ lr.1))

/-- The first legacy-selected declaration of `d` that the instantiated
design `m` still mentions and whose range at this point (`env.dims`, the
declaration scope's evaluated table) is not exact for the legacy encoding:
`(name, evaluated dimensions)`. A declaration without an evaluated entry
(an enum or struct type, a scalar) has nothing to map and passes. -/
def PDesign.legacyRangeViolation (d : PDesign) (env : IEnv) (m : Design2) :
    Option (String × List (Int × Int)) :=
  d.legacySelNames.findSome? fun n =>
    match d.decls.find? (·.name == n), env.dims.lookup n with
    | some pd, some es =>
        match pd.type with
        | .packed ds _ =>
            if ds.length == es.length && (ds.zip es).all (fun (dim, lr) => legacyDimOk dim lr)
            then none
            else if m.mentions n then some (n, es) else none
        | _ => none
    | _, _ => none

/-- The refusal message of a violation. -/
def legacyRangeMsg (mname n : String) (es : List (Int × Int)) : String :=
  let rng := String.join (es.map fun (l, r) => s!"[{l}:{r}]")
  s!"declaration '{n}' of module '{mname}' is selected with the legacy offset encoding (a genvar or run-time label, e.g. `{n}[g]`, `{n}[s]`), and its packed range at these parameters is {rng}, not [m:0] with m ≥ 0: the selected bit would be the label's offset from bit 0, not the labelled bit (an out-of-range label reads x in Icarus 12.0 and Yosys 0.53)"

/-- `m` with a loud `Select:legacy-range` process appended when the guard
fails at this point (`env` is the module's declaration-scope environment
at the point). -/
def PDesign.rangeGuard (d : PDesign) (env : IEnv) (m : Design2) : Design2 :=
  match d.legacyRangeViolation env m with
  | none => m
  | some (n, es) =>
      let loud : Process2 := .unsupported "Select:legacy-range" (legacyRangeMsg d.name n es)
      { m with processes := m.processes.push loud }

/-! ## Round 6: wide bit-select indices -/

mutual
/-- The index expression of every bit select (`v[i]`, as a value) inside an
expression, with repeats. -/
def PExpr.bitIdxs : PExpr → List PExpr
  | .bitSel b i => i :: (b.bitIdxs ++ i.bitIdxs)
  | .partSel b m l => b.bitIdxs ++ m.bitIdxs ++ l.bitIdxs
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a
  | .reduce _ a | .cast _ a => a.bitIdxs
  | .binary _ l r | .repl l r => l.bitIdxs ++ r.bitIdxs
  | .ternary c t e => c.bitIdxs ++ t.bitIdxs ++ e.bitIdxs
  | .concat ps | .arrayElem _ ps => PExpr.bitIdxsList ps
  | .arrayPart _ ps _ a b => PExpr.bitIdxsList ps ++ a.bitIdxs ++ b.bitIdxs
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _ | .fill _
  | .unsupported .. => []

/-- `PExpr.bitIdxs` over a list. -/
def PExpr.bitIdxsList : List PExpr → List PExpr
  | [] => []
  | p :: ps => p.bitIdxs ++ PExpr.bitIdxsList ps
end

mutual
/-- … of an assignment target (its own index and the indices it reads). -/
def PLhs.bitIdxs : PLhs → List PExpr
  | .ident _ => []
  | .bitSel _ i => i :: i.bitIdxs
  | .partSel _ m l => m.bitIdxs ++ l.bitIdxs
  | .concat ps => PLhs.bitIdxsList ps
  | .arrayElem _ is => PExpr.bitIdxsList is
  | .arrayPart _ is _ a b => PExpr.bitIdxsList is ++ a.bitIdxs ++ b.bitIdxs

/-- `PLhs.bitIdxs` over a list. -/
def PLhs.bitIdxsList : List PLhs → List PExpr
  | [] => []
  | t :: ts => t.bitIdxs ++ PLhs.bitIdxsList ts
end

mutual
/-- … of a statement. -/
def PStmt.bitIdxs : PStmt → List PExpr
  | .blockingAssign _ v | .nbaAssign _ v => v.bitIdxs
  | .blockingAssignL t v | .nbaAssignL t v => t.bitIdxs ++ v.bitIdxs
  | .ifStmt c t e => c.bitIdxs ++ t.bitIdxs ++ PStmt.bitIdxsOpt e
  | .block body => PStmt.bitIdxsList body
  | .caseStmt s items d _ _ =>
      s.bitIdxs ++ PStmt.bitIdxsItems items ++ PStmt.bitIdxsOpt d
  | .unsupported .. => []

/-- … of an optional statement. -/
def PStmt.bitIdxsOpt : Option PStmt → List PExpr
  | none => []
  | some s => s.bitIdxs

/-- … of a statement list. -/
def PStmt.bitIdxsList : List PStmt → List PExpr
  | [] => []
  | s :: ss => s.bitIdxs ++ PStmt.bitIdxsList ss

/-- … of `case` items (patterns and bodies). -/
def PStmt.bitIdxsItems : List (List PExpr × PStmt) → List PExpr
  | [] => []
  | (ps, s) :: rest => PExpr.bitIdxsList ps ++ s.bitIdxs ++ PStmt.bitIdxsItems rest
end

/-- … of a process. -/
def PProcess.bitIdxs : PProcess → List PExpr
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b | .alwaysFFR _ _ b => b.bitIdxs
  | .assign _ v => v.bitIdxs
  | .assignL t v => t.bitIdxs ++ v.bitIdxs
  | .unsupported .. => []

/-- … of an instance's port connections. -/
def PConn.bitIdxs : PConn → List PExpr
  | .input _ (some e) _ => e.bitIdxs
  | .output _ (some t) => t.bitIdxs
  | _ => []

mutual
/-- … of a generate item THE POINT INSTANTIATES, each index paired with the
environment it is judged in (round 6 repair, 2026-10-29): only the arm of a
`genIf` its condition selects and the iterations of a `genFor` that
`genvarSeq` yields, each under its genvar binding — the walk `expandH`
(Hier2.lean) makes, so an uninstantiated arm (`if (N == 4) … v[a] … else …`
at `N = 40`) and a loop with no iteration are not judged, as the lazily
lowered `ArraySel` refusals are not. A condition or loop header that does not
evaluate leaves the design loud in its own right (`generate if: …`); both
arms, or the body, are walked then (conservative, as before the repair). -/
def GenItem.liveBitIdxs (env : IEnv) (F : Nat) : GenItem → List (IEnv × PExpr)
  | .process p => p.bitIdxs.map fun i => (env, i)
  | .unsupported .. => []
  | .inst i => (i.conns.flatMap PConn.bitIdxs).map fun e => (env, e)
  | .genIf cond thenB elseB =>
      match evalInt env cond with
      | .ok v =>
          if v != 0 then GenItem.liveBitIdxsList env F thenB
          else GenItem.liveBitIdxsList env F elseB
      | .error _ =>
          GenItem.liveBitIdxsList env F thenB ++ GenItem.liveBitIdxsList env F elseB
  | .genFor _label g initE bound step _rc body =>
      match evalInt env initE, stepDelta g step with
      | .ok i0, .ok δ =>
          match genvarSeq env g bound δ F i0 with
          | .ok vs => GenItem.liveBitIdxsIters env F g vs body
          | _ => GenItem.liveBitIdxsList env F body
      | _, _ => GenItem.liveBitIdxsList env F body
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- `GenItem.liveBitIdxs` over a generate item list. -/
def GenItem.liveBitIdxsList (env : IEnv) (F : Nat) : List GenItem → List (IEnv × PExpr)
  | [] => []
  | it :: rest => it.liveBitIdxs env F ++ GenItem.liveBitIdxsList env F rest
  termination_by l => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- A generate-for body at each genvar value. -/
def GenItem.liveBitIdxsIters (env : IEnv) (F : Nat) (g : String) :
    List Int → List GenItem → List (IEnv × PExpr)
  | [], _ => []
  | v :: vs, body =>
      GenItem.liveBitIdxsList (env.bindVal g v) F body
        ++ GenItem.liveBitIdxsIters env F g vs body
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

/-- Every bit-select index of `d` THE POINT INSTANTIATES (its processes and the
live part of its generate items), with the environment it is judged in (`env`:
the module's own scope, `F`: the generate fuel). -/
def PDesign.liveBitIdxs (d : PDesign) (env : IEnv) (F : Nat) : List (IEnv × PExpr) :=
  (d.processes.flatMap PProcess.bitIdxs).map (fun i => (env, i))
    ++ GenItem.liveBitIdxsList env F d.generates

/-- Whether a bit-select index splits the tools at this point: a constant of
2^32 or more, or a non-constant (or not evaluable) index whose self-determined
width exceeds 32 bits (`env` carries the declared widths). -/
def wideBitIdx (env : IEnv) (elems : List (String × Nat)) (i : PExpr) : Bool :=
  match evalInt env i with
  | .ok v => decide ((4294967296 : Int) ≤ v)
  | .error _ =>
      match selfWidth2 env elems i with
      | some w => decide (32 < w)
      | none => false

/-- The refusal text of `Select:wide-index`. -/
def wideIndexMsg (mname : String) (w? : Option Nat) : String :=
  let wtxt := match w? with
    | some w => s!"{w} bits"
    | none => "a constant of 2^32 or more"
  s!"module '{mname}' selects a bit with an index of {wtxt}: IEEE 1800-2023 §11.5.1 evaluates the index whole (out of range: x, as Yosys 0.53 `prep; eval`), but Xcelium 24.03 (BIGWBS), Icarus 12.0 and Verilator 5.042 truncate it to its low 32 bits and read a defined bit; refused rather than one reading chosen"

/-- The first wide bit-select index of `d` at this point (instantiated code
only: `PDesign.liveBitIdxs`), as its refusal text. -/
def PDesign.wideIndexViolation (d : PDesign) (env : IEnv) (elems : List (String × Nat))
    (F : Nat) : Option String :=
  ((d.liveBitIdxs env F).find? fun (e, i) => wideBitIdx e elems i).map fun (e, i) =>
    wideIndexMsg d.name (match evalInt e i with
      | .ok _ => none
      | .error _ => selfWidth2 e elems i)

/-! ## Round 6: constant slices that leave their signal partly -/

/-- The first constant slice of a lowered design that leaves its signal
PARTLY (`lo < W < lo + w`, in a read or a write) or sits at an offset of
2^32 or more, as `(kind, message)`. The bases judged are declared signals
(`.slice (.ident n) …`, `Lhs2.slice n …`) — the lowering of every legacy
`partSel`; other bases have no static width here and are not judged. -/
def Design2.firstSliceViolation (d : Design2) : Option (String × String) :=
  d.processes.findSome? fun p =>
    match p with
    | .unsupported _ _ => none
    | .alwaysFF _ s | .alwaysPlain _ s | .alwaysComb s | .alwaysFFR _ _ s => stmtV s
    | .assign t e => (lhsV t).orElse fun _ => exprV e
where
  declW (n : String) : Option Nat := (d.decls.find? (·.name == n)).map (·.width)
  check (what : String) (n : String) (lo wd : Nat) : Option (String × String) :=
    if 4294967296 ≤ lo then
      some ("Select:wide-index", wideIndexMsg d.name none)
    else
      match declW n with
      | some w =>
          if lo < w && w < lo + wd then
            some ("Select:partial-overhang",
              s!"module '{d.name}': {what} of {wd} bits at offset {lo} of '{n}' ({w} bits) leaves the signal partly (a legacy part select past its end): IEEE 1800-2023 §11.5.1 reads x in the out-of-range bits only (and writes only the in-range ones), Xcelium 24.03 treats the whole select as invalid (a read is all x, a write is dropped); refused rather than one reading chosen")
          else none
      | none => none
  exprV : Expr2 → Option (String × String)
    | .unsupported _ _ | .lit _ | .ident _ => none
    | .unary _ a | .repl _ a | .reduce _ a | .resize _ a | .resizeSigned _ a | .squash2 a => exprV a
    | .binary _ a b | .scmp _ a b | .logical _ a b => (exprV a).orElse fun _ => exprV b
    | .ternary c a b => ((exprV c).orElse fun _ => exprV a).orElse fun _ => exprV b
    | .slice a lo wd =>
        (match a with
         | .ident n => check "read" n lo wd
         | _ => none).orElse fun _ => exprV a
    | .index a i _ => (exprV a).orElse fun _ => exprV i
    | .concat ps => ps.attach.findSome? fun ⟨p, _⟩ => exprV p
  lhsV : Lhs2 → Option (String × String)
    | .ident _ => none
    | .slice n lo wd => check "write" n lo wd
    | .index _ i _ => exprV i
    | .concat parts => parts.attach.findSome? fun ⟨l, _⟩ => lhsV l
  stmtV : Stmt2 → Option (String × String)
    | .unsupported _ _ => none
    | .blockingAssign t e | .nbaAssign t e => (lhsV t).orElse fun _ => exprV e
    | .ifStmt c t e =>
        ((exprV c).orElse fun _ => stmtV t).orElse fun _ =>
          (match e with | some s => stmtV s | none => none)
    | .block body => body.attach.findSome? fun ⟨s, _⟩ => stmtV s
    | .caseStmt subj items dflt _ _ =>
        ((exprV subj).orElse fun _ => items.attach.findSome? fun ⟨it, _⟩ => caseItemV it).orElse
          fun _ => (match dflt with | some s => stmtV s | none => none)
  caseItemV : CaseItem2 → Option (String × String)
    | .mk pats body =>
        (pats.attach.findSome? fun ⟨p, _⟩ => exprV p).orElse fun _ => stmtV body

/-- The first loud node of a lowered design in process order, as `(kind,
text)` — an `Unsupported` process, statement or expression, wherever it
sits (`Design2.hasUnsupported` is its yes/no twin). The differential runner
names it beside `run2`'s own message, which carries the kind of the node it
meets but never its text (a refused assignment TARGET is
`unsupported statement 'AssignL'`; the tag lives in the text). -/
def Design2.firstLoud (d : Design2) : Option (String × String) :=
  d.processes.findSome? fun p =>
    match p with
    | .unsupported k t => some (k, t)
    | .alwaysFF _ s | .alwaysPlain _ s | .alwaysComb s | .alwaysFFR _ _ s => stmtL s
    | .assign t e => (lhsL t).orElse fun _ => exprL e
where
  exprL : Expr2 → Option (String × String)
    | .unsupported k t => some (k, t)
    | .lit _ | .ident _ => none
    | .unary _ a | .repl _ a | .reduce _ a | .resize _ a | .resizeSigned _ a | .squash2 a => exprL a
    | .binary _ a b | .scmp _ a b | .logical _ a b => (exprL a).orElse fun _ => exprL b
    | .ternary c a b => ((exprL c).orElse fun _ => exprL a).orElse fun _ => exprL b
    | .slice a _ _ => exprL a
    | .index a i _ => (exprL a).orElse fun _ => exprL i
    | .concat ps => ps.attach.findSome? fun ⟨p, _⟩ => exprL p
  lhsL : Lhs2 → Option (String × String)
    | .ident _ | .slice .. => none
    | .index _ i _ => exprL i
    | .concat parts => parts.attach.findSome? fun ⟨l, _⟩ => lhsL l
  stmtL : Stmt2 → Option (String × String)
    | .unsupported k t => some (k, t)
    | .blockingAssign t e | .nbaAssign t e => (lhsL t).orElse fun _ => exprL e
    | .ifStmt c t e =>
        ((exprL c).orElse fun _ => stmtL t).orElse fun _ =>
          (match e with | some s => stmtL s | none => none)
    | .block body => body.attach.findSome? fun ⟨s, _⟩ => stmtL s
    | .caseStmt subj items dflt _ _ =>
        ((exprL subj).orElse fun _ => items.attach.findSome? fun ⟨it, _⟩ => caseItemL it).orElse
          fun _ => (match dflt with | some s => stmtL s | none => none)
  caseItemL : CaseItem2 → Option (String × String)
    | .mk pats body =>
        (pats.attach.findSome? fun ⟨p, _⟩ => exprL p).orElse fun _ => stmtL body

/-- `m` with the round-6 loud processes appended when its point holds a wide
bit-select index (`d`, `env`, `elems`, `F`: the module's own scope and generate
fuel) or a constant
slice that leaves its signal partly. -/
def PDesign.selectGuard (d : PDesign) (env : IEnv) (elems : List (String × Nat)) (F : Nat)
    (m : Design2) : Design2 :=
  let wide : List Process2 :=
    match d.wideIndexViolation env elems F with
    | some msg => [.unsupported "Select:wide-index" msg]
    | none => []
  let part : List Process2 :=
    match m.firstSliceViolation with
    | some (k, msg) => [.unsupported k msg]
    | none => []
  { m with processes := m.processes ++ (wide ++ part).toArray }

/-! ## The guarded twin of `instantiateRec` (admission only) -/

/-- `PDesign.instantiateRec` with `PDesign.rangeGuard` applied at every
level, BEFORE a child is flattened into its parent (its loud process is
then renamed and hoisted with the rest). Used only to decide admission
(`legacyRangeReport`); the semantics is `instantiateH`'s. -/
def PDesign.instantiateRecR : Nat → List PDesign → IEnv → PDesign → List Int → Nat →
    Res Design2
  | 0, _, _, d, _, _ =>
      .unsupported s!"module '{d.name}': instance hierarchy deeper than its module library (recursive instantiation is outside the tier)"
  | depth + 1, lib, envI, d, args, F =>
      if args.length != d.params.length then
        .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
      else do
        let env ← d.paramEnvH envI args
        let decls ← buildDecls env d.decls
        let elems ← buildElems env d.decls
        let envP := { env with widths := decls.map fun dc => (dc.name, dc.width) }
        let cb := childInstOf (fun c cargs => PDesign.instantiateRecR depth lib envI c cargs F) lib
          (Decl.inputNames decls)
        let (idecls, gens) ← expandListH cb envP elems F d.generates
        let m : Design2 :=
          { name := d.name
            decls := (decls ++ idecls).toArray
            processes :=
              ((d.processes.map (instProcess2 envP elems)) ++ gens
                ++ d.others.map fun (k, t) => Process2.unsupported k t).toArray }
        .ok (d.selectGuard envP elems F (d.rangeGuard env m))

/-- **The range guard at a point** (`args`, the design already brought to
the point by `PDesign.atPoint`): `none` when every module of the
hierarchy passes, else the first refusal message. An instantiation failure
is not this guard's to report (`none`: the semantic family is loud there
already). -/
def PDesign.legacyRangeReport (d : PDesign) (lib : List PDesign) (args : List Int) :
    Option String :=
  match PDesign.instantiateRecR (lib.length + 1) lib {} d args (PDesign.surfaceFuel args) with
  | .ok m =>
      m.processes.toList.findSome? fun p =>
        match p with
        | .unsupported "Select:legacy-range" msg => some msg
        | _ => none
  | _ => none

/-- **The select guards at a point, with their kinds** (round 6): the first
refusal among `Select:legacy-range`, `Select:wide-index` and
`Select:partial-overhang` as `(kind, message)` — what the loader and the
differential runner report. `legacyRangeReport` is its legacy-only half. -/
def PDesign.selectGuardReport (d : PDesign) (lib : List PDesign) (args : List Int) :
    Option (String × String) :=
  match PDesign.instantiateRecR (lib.length + 1) lib {} d args (PDesign.surfaceFuel args) with
  | .ok m =>
      m.processes.toList.findSome? fun p =>
        match p with
        | .unsupported k msg =>
            if k == "Select:legacy-range" || k == "Select:wide-index"
                || k == "Select:partial-overhang" then some (k, msg) else none
        | _ => none
  | _ => none

/-! ## Checks -/

section checks

private def wv (n : String) (msb : PExpr) : PDecl :=
  { name := n, type := .packed [⟨msb, .int 0⟩] none }

/-- `logic [N-1:0] v; input s; output o; assign o = v[s];` — the vb3 shape. -/
private def pVb3 : PDesign :=
  { name := "vb3", params := [{ name := "N", default? := some (.int 3) }]
    localParams := [], enums := []
    decls := [{ wv "v" (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)) with isInput := true },
              { name := "s", type := .packed [] none, isInput := true },
              { name := "o", type := .packed [] none, isOutput := true }]
    processes := [.assign "o" (.bitSel (.ident "v") (.ident "s"))]
    generates := [] }

#guard pVb3.legacySelNames == ["v"]
-- N ≥ 1: `[N-1:0]` is canonical — passes.
#guard pVb3.legacyRangeReport [] [3] == none
#guard pVb3.legacyRangeReport [] [1] == none
-- N = 0 and N = -1: `[-1:0]` / `[-2:0]` — refused, naming the declaration.
#guard (pVb3.legacyRangeReport [] [0]).isSome
#guard (pVb3.legacyRangeReport [] [-1]).isSome

/-- The `ripple_add` shape: the legacy select only inside a loop over
`N` — at `N = 0` nothing is reached and the guard passes. -/
private def pLoop : PDesign :=
  { name := "lp", params := [{ name := "N", default? := some (.int 4) }]
    localParams := [], enums := []
    decls := [{ wv "a" (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)) with isInput := true },
              { wv "s" (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)) with isOutput := true }]
    processes := []
    generates := [.genFor none "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
      (.unary .inc (.genvarRef "i")) none
      [.process (.assignL (.bitSel "s" (.genvarRef "i")) (.bitSel (.ident "a") (.genvarRef "i")))]] }

#guard pLoop.legacyRangeReport [] [0] == none
#guard pLoop.legacyRangeReport [] [4] == none
#guard (pLoop.legacyRangeReport [] [-1]).isNone

/-- Literal bounds: the extractor's folded offsets are exact at every point. -/
private def pLit : PDesign :=
  { name := "lit", params := [{ name := "N", default? := some (.int 4) }]
    localParams := [], enums := []
    decls := [{ name := "u", type := .packed [⟨.int 7, .int 4⟩] none, isInput := true },
              { name := "s", type := .packed [⟨.int 1, .int 0⟩] none, isInput := true },
              { name := "o", type := .packed [] none, isOutput := true }]
    processes := [.assign "o" (.bitSel (.ident "u") (.ident "s"))]
    generates := [] }

#guard pLit.legacyRangeReport [] [0] == none

/-! ### Round 6 checks -/

private def wd (n : String) (w : Nat) (inp : Bool) : PDecl :=
  { name := n, type := .packed [⟨.int ((w : Int) - 1), .int 0⟩] none, isInput := inp, isOutput := !inp }

/-- A LEGACY part select with literal labels over `[7:0]`. -/
private def pOv (msb lsb : Int) : PDesign :=
  { name := "ov", params := [], localParams := [], enums := []
    decls := [wd "v" 8 true, wd "o" 4 false]
    processes := [.assign "o" (.partSel (.ident "v") (.int msb) (.int lsb))]
    generates := [] }

-- `v[9:6]` leaves the vector partly (bits 8, 9): refused, by kind.
#guard match (pOv 9 6).selectGuardReport [] [] with
  | some ("Select:partial-overhang", _) => true
  | _ => false
-- `v[5:2]` is in range, `v[11:9]` wholly outside (x read: every tool agrees).
#guard (pOv 5 2).selectGuardReport [] [] == none
#guard (pOv 11 9).selectGuardReport [] [] == none
-- The legacy half of the report is untouched by the new kinds.
#guard (pOv 9 6).legacyRangeReport [] [] == none

/-- A bit select with an `n`-bit run-time index over `[7:0]`. -/
private def pWide (n : Nat) : PDesign :=
  { name := "wide", params := [], localParams := [], enums := []
    decls := [wd "v" 8 true, wd "a" n true, wd "o" 1 false]
    processes := [.assign "o" (.bitSel (.ident "v") (.ident "a"))]
    generates := [] }

-- A 42-bit index is refused, a 32-bit one is not (the models agree there).
#guard match (pWide 42).selectGuardReport [] [] with
  | some ("Select:wide-index", _) => true
  | _ => false
#guard (pWide 33).selectGuardReport [] [] |>.isSome
#guard (pWide 32).selectGuardReport [] [] == none
#guard (pWide 4).selectGuardReport [] [] == none

/-- … as an assignment TARGET (Xcelium truncates a wide lvalue index too). -/
private def pWideT : PDesign :=
  { name := "widet", params := [], localParams := [], enums := []
    decls := [wd "w" 8 false, wd "a" 40 true, wd "b" 1 true]
    processes := [.assignL (.bitSel "w" (.ident "a")) (.ident "b")]
    generates := [] }
#guard (pWideT.selectGuardReport [] []).isSome

/-- A parametric index width: `a` is `[N+1:0]`, the index `a - 3`; wide at
`N = 40` only. -/
private def pWideP : PDesign :=
  { name := "widep", params := [{ name := "N", default? := some (.int 7) }]
    localParams := [], enums := []
    decls := [wd "v" 8 true,
              { name := "a", type := .packed [⟨.binary (.m0 .add) (.paramRef "N" none) (.int 1), .int 0⟩] none,
                isInput := true },
              wd "o" 1 false]
    processes := [.assign "o" (.bitSel (.ident "v") (.binary (.m0 .sub) (.ident "a") (.int 3)))]
    generates := [] }
#guard pWideP.selectGuardReport [] [7] == none
#guard pWideP.selectGuardReport [] [30] == none
#guard (pWideP.selectGuardReport [] [40]).isSome

/-- Dead generate code is not judged: the wide index `v[a]` (`a` is `[N-1:0]`,
`N` bits) sits in the `N == K` arm of a generate-if, the narrow `v[a[3:0]]`
in the other. At `N = 40` with `K = 4` the wide arm is NOT instantiated. -/
private def pDeadArm (k : Int) : PDesign :=
  { name := "deadarm", params := [{ name := "N", default? := some (.int 4) }]
    localParams := [], enums := []
    decls := [wd "v" 8 true,
              { name := "a", type := .packed [⟨.binary (.m0 .sub) (.paramRef "N" none) (.int 1), .int 0⟩] none,
                isInput := true },
              wd "o" 1 false]
    processes := []
    generates := [.genIf (.binary (.m0 .eq) (.paramRef "N" none) (.int k))
      [.process (.assign "o" (.bitSel (.ident "v") (.ident "a")))]
      [.process (.assign "o" (.bitSel (.ident "v") (.partSel (.ident "a") (.int 3) (.int 0))))]] }
-- N = 4: the wide-looking arm is live but 4 bits wide; N = 40, K = 4: dead.
#guard (pDeadArm 4).selectGuardReport [] [4] == none
#guard (pDeadArm 4).selectGuardReport [] [40] == none
#guard (pDeadArm 4).selectGuardReport [] [5] == none
-- N = 40 with K = 40: the 40-bit `v[a]` IS the instantiated arm: refused.
#guard match (pDeadArm 40).selectGuardReport [] [40] with
  | some ("Select:wide-index", _) => true
  | _ => false
#guard (pDeadArm 40).selectGuardReport [] [8] == none

/-- A generate-for with `M` iterations over a 40-bit index: judged only when it
runs. -/
private def pLoopIdx (m : Int) : PDesign :=
  { name := "loopidx", params := [{ name := "M", default? := some (.int m) }]
    localParams := [], enums := []
    decls := [wd "v" 8 true, wd "a" 40 true, wd "o" 1 false]
    processes := []
    generates := [.genFor none "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "M" none))
      (.unary .inc (.genvarRef "i")) none
      [.process (.assign "o" (.bitSel (.ident "v") (.ident "a")))]] }
#guard (pLoopIdx 0).selectGuardReport [] [0] == none
#guard match (pLoopIdx 0).selectGuardReport [] [1] with
  | some ("Select:wide-index", _) => true
  | _ => false
#guard match (pLoopIdx 2).selectGuardReport [] [2] with
  | some ("Select:wide-index", _) => true
  | _ => false

-- `firstLoud` names the node (kind and text) that `run2`'s message only
-- names by kind: a refused part-select TARGET is `AssignL` with the tag in
-- its text.
#guard match (Design2.firstLoud
    { name := "t", decls := #[], processes := #[.assign (.ident "o") (.ternary (.ident "c")
        (.unsupported "X:inner" "why") (.lit (LVec.ofNat 1 0)))] }) with
  | some ("X:inner", "why") => true
  | _ => false
#guard (Design2.firstLoud
    { name := "t", decls := #[], processes := #[.alwaysComb (.block #[.blockingAssign (.ident "o")
        (.ident "a")])] }).isNone

end checks

end LeanModels.Sv
