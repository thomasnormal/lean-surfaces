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
        .ok (d.rangeGuard env m)

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

end checks

end LeanModels.Sv
