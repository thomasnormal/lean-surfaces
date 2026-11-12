import LeanModels.Sv.CombEqThm
import LeanModels.Sv.CombSigned

/-!
# The hierarchy summary: a design with module-level instances, read through its flat twin

`X.sem N` of a design that instantiates modules is `PDesign.instantiateHDAlias2 X.pdesign X.plib [N]` (`Hier2.lean`):
the hierarchical instantiation flattens every instance — the child's declarations hoisted under the instance prefix
`<inst>.`, one continuous assignment per port connection, the child's processes renamed under the prefix. The `sv_comb`
tactics summarize a FLAT design. This file builds the flat design the hierarchical instantiation produces, at the
template level, with nothing unrolled: the **flat twin** `hierTwin d lib`, whose summary is the hierarchy summary
(`summaryH`):

* the parent's own declarations, unchanged, and its processes, each its unsigned twin (`PProcess.unsign`: a design with
  signed reads is read as `PDesign.unsign` reads a flat one, `parent_proc_eqU`);
* per module-level instance `i` of a child `c` (source order), with prefix `p = i.name ++ "."`:
  - every parameter of `c` as a localparam `p ++ P` of the parent: the override expression of the instance (a
    constant expression of the parent's scope), or `c`'s default renamed under the prefix — the child parameter
    overrides become named constants of the parent, so the child's widths stay symbolic;
  - every localparam of `c`, renamed;
  - every declaration of `c`, renamed, its port flags cleared (`Decl.hoist`);
  - one continuous assignment per port, in `c`'s port order: `p ++ a = actual` for an input, `target = p ++ y` for an
    output (`connProcs`); the actual is its unsigned twin (`PExpr.unsign`), so a signed read in a connection, a select
    of a signed signal included (an unsigned value, IEEE 1800-2023 §11.8.1), is read as in a continuous assign
    (`conn_in_eq`);
  - every process of `c`, renamed (`instBodyProc`).

`instantiateHD2_twin` proves that the hierarchical instantiation IS the twin's flat instantiation, at every parameter
point where the twin's obligations hold, so every theorem the tactics prove about the twin's family is a theorem
about `X.sem N` (`instantiateHDAlias2_twin`, the form the tactics rewrite along). The proof is per process: the
instantiated form of a process of the fragment is determined by its site (`proc_shapeC`, `rhs_shapeC`,
`instLhs_acc_w`), so the real process — instantiated in the parent's environment (`parent_proc_eq`), built by
`connProcs` (`conn_in_eq`, `conn_out_eq`), or instantiated in the child's environment at its own parameter point and
renamed (`child_proc_eq`) — and the twin's process are the same expression. That needs the equation-stage fragment and
width obligations on the twin (`EqFrag`, `WidthObl`), as for a design with signed reads (`CombSigned.lean`). Nothing is
asked of a child at its own parameter point beyond its environment (`ChildEnvOk`, closed like `hag`): the facts its
sites need there are its twin copies' facts, renamed back (`Sk.widthOkC_hren`, `accGeom_of_hren`), and its one-driver
rule (applied by `childInstOf`) follows from the twin's, whose driver windows include the renamed child's after its
port connections (`child_driversOk`). The correspondence of the twin's sites with the parent's and the children's is a
decidable side condition on the summaries (`HierOk`), which the tactics decide.

## v1 scope (loud outside)

* instances at module level only: an instance inside a generate loop or branch is refused, saying why (its sites
  would be a generate family whose names carry the loop index);
* the parent has no generate block besides its instances; a child has no instance and no generate block;
* every port is connected; no connection is loud;
* every connection is exactly as wide as its port at every parameter point (`conn_in_eq`, `conn_out_eq`): a connection
  that changes width, an input actual truncated to the port or an output port zero-extended into a wider target (which
  `connProcs` lowers through `fitExpr2`/`portOut`), is outside v1. The width obligation `WidthObl` of the twin says so at
  each point; `sv_structure` samples it and names the connection (`twinWidthMsg`, `CombEqTactic.lean`).

A parent's `wire` output tiled by the instances' output ports (`.y(y[W/2-1:0])`, `.y(y[W-1:W/2])`) is read like a
variable port: the extractor checks that each instance output targets the net and that the windows cover it without
overlap at the default point, and marks it a net-as-variable; the loader reads it as an output declaration, so the twin's
assignments `target = p ++ y` are the instantiation's (`conn_out_eq`), and the one-driver rule at each parameter point is
the twin's disjointness obligation, decided like any other. Two things this does not give, both ls-sv's (reported):
* the extractor checks that the windows COVER the net at the default point only, and `driversOk` re-checks overlaps at
  every point but not holes. At a point where the windows leave a bit undriven, the output declaration starts at x and
  the bit reads x, where the standard (an undriven `wire` is z) and Icarus give z (measured: `run2` gives `y = 1010x010`,
  Icarus 12 `1010z010`, for windows `y[P-1:0]`, `y[W-1:W/2]` at `W = 8`, `P = 3`, `a = 8'hAA`). The summary states no
  equation for an undriven bit, so no theorem the tactics prove speaks of its value.
* the extractor compares the driver's text sliced from the decoded source with slang's byte offsets, so one non-ASCII
  character above the driver leaves the net the loud member `PortSymbol:net-z` (the refusal says so,
  `PDesign.netZNoteIn`; `comb_hier/neg/hier_param_utf8.sv`).
-/

namespace LeanModels.Sv

/-! ## Renaming under an instance prefix -/

mutual
/-- Every signal, parameter and genvar name of an expression of the child's scope, under the prefix. -/
def PExpr.hren (pfx : String) : PExpr → PExpr
  | .lit v => .lit v
  | .ident n => .ident (pfx ++ n)
  | .paramRef n none => .paramRef (pfx ++ n) none
  | .paramRef n (some k) => .paramRef n (some k)
  | .genvarRef n => .genvarRef (pfx ++ n)
  | .enumRef t m k => .enumRef t m k
  | .int v => .int v
  | .fill b => .fill b
  | .unary op a => .unary op (a.hren pfx)
  | .binary op l r => .binary op (l.hren pfx) (r.hren pfx)
  | .ternary c t e => .ternary (c.hren pfx) (t.hren pfx) (e.hren pfx)
  | .concat ps => .concat (PExpr.hrenL pfx ps)
  | .resize w a => .resize w (a.hren pfx)
  | .signedResize w a => .signedResize w (a.hren pfx)
  | .squash2 w a => .squash2 w (a.hren pfx)
  | .sysCall f a => .sysCall f (a.hren pfx)
  | .bitSel b i => .bitSel (b.hren pfx) (i.hren pfx)
  | .partSel b m l => .partSel (b.hren pfx) (m.hren pfx) (l.hren pfx)
  | .repl c a => .repl (c.hren pfx) (a.hren pfx)
  | .reduce op a => .reduce op (a.hren pfx)
  | .cast s a => .cast s (a.hren pfx)
  | .arrayElem n is => .arrayElem (pfx ++ n) (PExpr.hrenL pfx is)
  | .arrayPart n is m a b => .arrayPart (pfx ++ n) (PExpr.hrenL pfx is) m (a.hren pfx) (b.hren pfx)
  | .unsupported k t => .unsupported k t

/-- `PExpr.hren`, elementwise. -/
def PExpr.hrenL (pfx : String) : List PExpr → List PExpr
  | [] => []
  | e :: es => e.hren pfx :: PExpr.hrenL pfx es
end

mutual
/-- An assignment target of the child's scope, under the prefix. -/
def PLhs.hren (pfx : String) : PLhs → PLhs
  | .ident n => .ident (pfx ++ n)
  | .bitSel n i => .bitSel (pfx ++ n) (i.hren pfx)
  | .partSel n m l => .partSel (pfx ++ n) (m.hren pfx) (l.hren pfx)
  | .concat ps => .concat (PLhs.hrenL pfx ps)
  | .arrayElem n is => .arrayElem (pfx ++ n) (PExpr.hrenL pfx is)
  | .arrayPart n is m a b => .arrayPart (pfx ++ n) (PExpr.hrenL pfx is) m (a.hren pfx) (b.hren pfx)

/-- `PLhs.hren`, elementwise. -/
def PLhs.hrenL (pfx : String) : List PLhs → List PLhs
  | [] => []
  | t :: ts => t.hren pfx :: PLhs.hrenL pfx ts
end

/-- A packed dimension under the prefix. -/
def PDim.hren (pfx : String) (d : PDim) : PDim := ⟨d.msb.hren pfx, d.lsb.hren pfx⟩

/-- A declared type under the prefix (the bounds of a packed type). -/
def PType.hren (pfx : String) : PType → PType
  | .packed ds r => .packed (ds.map (PDim.hren pfx)) r
  | t => t

/-- A child declaration hoisted into the parent (`Decl.hoist` at the template level): prefixed name, renamed type,
port flags cleared. -/
def PDecl.hren (pfx : String) (pd : PDecl) : PDecl :=
  { pd with name := pfx ++ pd.name, type := pd.type.hren pfx, unpackedDims := pd.unpackedDims.map (PDim.hren pfx),
            isInput := false, isOutput := false, init := pd.init.map (PExpr.hren pfx) }

/-- A child process under the prefix (`instBodyProc` at the template level; continuous assignments only — the twin
is built for children whose summary reads every process as a continuous assignment). -/
def PProcess.hren (pfx : String) : PProcess → PProcess
  | .assign t v => .assign (pfx ++ t) (v.hren pfx)
  | .assignL l v => .assignL (l.hren pfx) (v.hren pfx)
  | p => p

/-- A child localparam under the prefix. -/
def PLocalParam.hren (pfx : String) (lp : PLocalParam) : PLocalParam :=
  { lp with name := pfx ++ lp.name, expr := lp.expr.hren pfx, type? := lp.type?.map (PType.hren pfx),
            resolved? := none }

namespace CombView

/-- An affine form over the child's names, under the prefix. -/
def Aff.hren (pfx : String) (a : Aff) : Aff :=
  { terms := a.terms.map (fun p => (pfx ++ p.1, p.2)), c := a.c, qs := a.qs.map (fun p => (pfx ++ p.1, p.2)) }

/-- An access of the child's scope under the prefix. -/
def Acc.hren (pfx : String) : Acc → Acc
  | .whole n => .whole (pfx ++ n)
  | .bit n a => .bit (pfx ++ n) (a.hren pfx)
  | .cell1 n a => .cell1 (pfx ++ n) (a.hren pfx)
  | .row n w r => .row (pfx ++ n) (w.hren pfx) (r.hren pfx)
  | .cell2 n w r c => .cell2 (pfx ++ n) (w.hren pfx) (r.hren pfx) (c.hren pfx)
  | .part1 n hi lo => .part1 (pfx ++ n) (hi.hren pfx) (lo.hren pfx)
  | .part2 n w r hi lo => .part2 (pfx ++ n) (w.hren pfx) (r.hren pfx) (hi.hren pfx) (lo.hren pfx)

/-- A declaration of the child's summary under the prefix, port flags cleared. -/
def DeclT.hren (pfx : String) (dt : DeclT) : DeclT :=
  ⟨pfx ++ dt.name, false, false, dt.isNet, dt.isSigned,
    dt.dims.map fun p => (PDim.hren pfx p.1, p.2.1.hren pfx, p.2.2.hren pfx)⟩

end CombView

namespace CombEq
open CombView

/-- A part of a concatenation of the child's scope, under the prefix. -/
def Part.hren (pfx : String) : Part → Part
  | .lit v => .lit v
  | .rd a => .rd (a.hren pfx)
  | .replit c v => .replit (c.hren pfx) v
  | .reprd c a => .reprd (c.hren pfx) (a.hren pfx)

/-- A skeleton of the child's scope, under the prefix (every access and constant renamed). -/
def Sk.hren (pfx : String) : Sk → Sk
  | .lit v => .lit v
  | .rd a => .rd (a.hren pfx)
  | .gate g l r => .gate g (l.hren pfx) (r.hren pfx)
  | .cat ps => .cat (ps.map (Part.hren pfx))
  | .fill b => .fill b
  | .bnot a => .bnot (a.hren pfx)
  | .lnot a => .lnot (a.hren pfx)
  | .red op a => .red op (a.hren pfx)
  | .land l r => .land (l.hren pfx) (r.hren pfx)
  | .lor l r => .lor (l.hren pfx) (r.hren pfx)
  | .tern c a b => .tern (c.hren pfx) (a.hren pfx) (b.hren pfx)
  | .cmp op l r => .cmp op (l.hren pfx) (r.hren pfx)
  | .ext p => .ext (p.hren pfx)
  | .add l r => .add (l.hren pfx) (r.hren pfx)
  | .sub l r => .sub (l.hren pfx) (r.hren pfx)
  | .mul l r => .mul (l.hren pfx) (r.hren pfx)
  | .const v => .const v
  | .cref a => .cref (a.hren pfx)
  | .rep p => .rep (p.hren pfx)
  | .rsz pr p => .rsz pr (p.hren pfx)
  | .sh d sg l r => .sh d sg (l.hren pfx) (r.hren pfx)
  | .scmp op a b => .scmp op (a.hren pfx) (b.hren pfx)
  | .fit sg p => .fit sg (p.hren pfx)

/-- A skeleton whose width is its context's wherever its width contract holds (`Sk.width_of_exactW`): an input
connection's actual of this shape is exactly as wide as the port, so `connProcs` takes its assignment branch. -/
def Sk.exactW : Sk → Bool
  | .lit _ | .rd _ | .cat _ | .rep _ => true
  | .gate _ l r | .add l r | .sub l r | .mul l r => l.exactW && r.exactW
  | .bnot a => a.exactW
  | .tern _ a b => a.exactW && b.exactW
  | _ => false

theorem Sk.width_of_exactW (σ : String → Int) (dw : String → Nat) :
    ∀ (sk : Sk) (tw : Nat), sk.exactW = true → sk.WidthOkC σ dw tw → sk.width σ dw = tw
  | .lit _, _, _, h => h
  | .rd _, _, _, h => h
  | .cat _, _, _, h => h
  | .rep _, _, _, h => h
  | .gate _ l r, tw, he, h => by
      simp only [Sk.exactW, Bool.and_eq_true] at he
      simp only [Sk.width, Sk.width_of_exactW σ dw l tw he.1 h.1, Sk.width_of_exactW σ dw r tw he.2 h.2,
        Nat.max_self]
  | .add l r, tw, he, h => by
      simp only [Sk.exactW, Bool.and_eq_true] at he
      simp only [Sk.width, Sk.width_of_exactW σ dw l tw he.1 h.1, Sk.width_of_exactW σ dw r tw he.2 h.2.1,
        Nat.max_self]
  | .sub l r, tw, he, h => by
      simp only [Sk.exactW, Bool.and_eq_true] at he
      simp only [Sk.width, Sk.width_of_exactW σ dw l tw he.1 h.1, Sk.width_of_exactW σ dw r tw he.2 h.2.1,
        Nat.max_self]
  | .mul l r, tw, he, h => by
      simp only [Sk.exactW, Bool.and_eq_true] at he
      simp only [Sk.width, Sk.width_of_exactW σ dw l tw he.1 h.1, Sk.width_of_exactW σ dw r tw he.2 h.2.1,
        Nat.max_self]
  | .bnot a, tw, he, h => by
      simp only [Sk.exactW] at he
      simp only [Sk.width, Sk.width_of_exactW σ dw a tw he h.1]
  | .tern _ a b, tw, he, h => by
      simp only [Sk.exactW, Bool.and_eq_true] at he
      simp only [Sk.width, Sk.width_of_exactW σ dw a tw he.1 h.2.2.1,
        Sk.width_of_exactW σ dw b tw he.2 h.2.2.2, Nat.max_self]
  | .fill _, _, he, _ => by simp [Sk.exactW] at he
  | .lnot _, _, he, _ => by simp [Sk.exactW] at he
  | .red _ _, _, he, _ => by simp [Sk.exactW] at he
  | .land _ _, _, he, _ => by simp [Sk.exactW] at he
  | .lor _ _, _, he, _ => by simp [Sk.exactW] at he
  | .cmp _ _ _, _, he, _ => by simp [Sk.exactW] at he
  | .ext _, _, he, _ => by simp [Sk.exactW] at he
  | .const _, _, he, _ => by simp [Sk.exactW] at he
  | .cref _, _, he, _ => by simp [Sk.exactW] at he
  | .rsz _ _, _, he, _ => by simp [Sk.exactW] at he
  | .sh _ _ _ _, _, he, _ => by simp [Sk.exactW] at he
  | .scmp _ _ _, _, he, _ => by simp [Sk.exactW] at he
  | .fit _ _, _, he, _ => by simp [Sk.exactW] at he

end CombEq

/-! ## The renaming commutes with the valuations -/

section rename
open CombView CombEq

theorem Aff.evalTerms_hren (σ : String → Int) (pfx : String) : ∀ ts : List (String × Int),
    Aff.evalTerms σ (ts.map fun p => (pfx ++ p.1, p.2)) = Aff.evalTerms (fun n => σ (pfx ++ n)) ts
  | [] => rfl
  | (n, k) :: ts => by simp [Aff.evalTerms, Aff.evalTerms_hren σ pfx ts]

theorem Aff.evalQs_hren (σ : String → Int) (pfx : String) : ∀ qs : List (String × Int × Int),
    Aff.evalQs σ (qs.map fun p => (pfx ++ p.1, p.2)) = Aff.evalQs (fun n => σ (pfx ++ n)) qs
  | [] => rfl
  | (n, k, d) :: qs => by simp [Aff.evalQs, Aff.evalQs_hren σ pfx qs]

@[simp] theorem Aff.eval_hren (σ : String → Int) (pfx : String) (a : Aff) :
    (a.hren pfx).eval σ = a.eval (fun n => σ (pfx ++ n)) := by
  simp only [Aff.hren, Aff.eval, Aff.evalTerms_hren, Aff.evalQs_hren]

@[simp] theorem Acc.name_hren (pfx : String) (a : Acc) : (a.hren pfx).name = pfx ++ a.name := by
  cases a <;> rfl

@[simp] theorem Acc.lo_hren (σ : String → Int) (pfx : String) (a : Acc) :
    Acc.lo σ (a.hren pfx) = Acc.lo (fun n => σ (pfx ++ n)) a := by
  cases a <;> simp [Acc.hren, Acc.lo]

@[simp] theorem Acc.wid_hren (σ : String → Int) (pfx : String) (a : Acc) :
    Acc.wid σ (a.hren pfx) = Acc.wid (fun n => σ (pfx ++ n)) a := by
  cases a <;> simp [Acc.hren, Acc.wid]

theorem Acc.win_hren (σ : String → Int) (dw : String → Nat) (pfx : String) (a : Acc) :
    (a.hren pfx).win σ dw =
      (pfx ++ (a.win (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n))).1,
        (a.win (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n))).2) := by
  cases a <;> simp [Acc.hren, Acc.win, Acc.lo, Acc.wid]

@[simp] theorem Acc.win_hren_snd (σ : String → Int) (dw : String → Nat) (pfx : String) (a : Acc) :
    ((a.hren pfx).win σ dw).2 = (a.win (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n))).2 := by
  rw [Acc.win_hren]

theorem Acc.lhs_hren (σ : String → Int) (pfx : String) (a : Acc) :
    (a.hren pfx).lhs σ = (a.lhs (fun n => σ (pfx ++ n))).rename (pfx ++ ·) := by
  cases a <;> simp [Acc.hren, Acc.lhs, Acc.lo, Acc.wid, Lhs2.rename]

theorem accExpr_hren (σ : String → Int) (pfx : String) (a : Acc) :
    accExpr σ (a.hren pfx) = (accExpr (fun n => σ (pfx ++ n)) a).rename (pfx ++ ·) := by
  cases a <;> simp [Acc.hren, accExpr, Acc.lo, Acc.wid, Expr2.rename]

theorem Expr2.renameList_eq_map (f : String → String) :
    ∀ l : List Expr2, Expr2.renameList f l = l.map (Expr2.rename f)
  | [] => rfl
  | e :: es => by simp [Expr2.renameList, Expr2.renameList_eq_map f es]

@[simp] theorem Part.wid_hren (σ : String → Int) (dw : String → Nat) (pfx : String) (p : Part) :
    (p.hren pfx).wid σ dw = p.wid (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n)) := by
  cases p <;> simp [Part.hren, Part.wid]

theorem Part.expr_hren (σ : String → Int) (pfx : String) (p : Part) :
    (p.hren pfx).expr σ = (p.expr (fun n => σ (pfx ++ n))).rename (pfx ++ ·) := by
  cases p <;> simp [Part.hren, Part.expr, accExpr_hren, Expr2.rename, Expr2.renameList]

@[simp] theorem Sk.width_hren (σ : String → Int) (dw : String → Nat) (pfx : String) :
    ∀ sk : Sk, (sk.hren pfx).width σ dw = sk.width (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n)) := by
  intro sk
  induction sk <;> simp_all [Sk.hren, Sk.width, Function.comp_def]

@[simp] theorem Sk.rmax_hren (σ : String → Int) (dw : String → Nat) (pfx : String) :
    ∀ sk : Sk, (sk.hren pfx).rmax σ dw = sk.rmax (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n)) := by
  intro sk
  induction sk <;> simp_all [Sk.hren, Sk.rmax, Function.comp_def]

@[simp] theorem Sk.selfOk_hren (σ : String → Int) (dw : String → Nat) (pfx : String) :
    ∀ sk : Sk, (sk.hren pfx).SelfOk σ dw ↔ sk.SelfOk (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n)) := by
  intro sk
  induction sk <;> simp_all [Sk.hren, Sk.SelfOk]

@[simp] theorem Sk.rok_hren (σ : String → Int) (dw : String → Nat) (pfx : String) (tw : Nat) :
    ∀ sk : Sk, (sk.hren pfx).rok σ dw tw ↔ sk.rok (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n)) tw := by
  intro sk
  induction sk <;> simp_all [Sk.hren, Sk.rok]

theorem Sk.widthOkC_hren (σ : String → Int) (dw : String → Nat) (pfx : String) :
    ∀ (sk : Sk) (tw : Nat),
      (sk.hren pfx).WidthOkC σ dw tw ↔ sk.WidthOkC (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n)) tw := by
  intro sk
  induction sk with
  | rsz pr p ih =>
      intro tw
      cases pr <;> simp only [Sk.hren, Sk.WidthOkC, Sk.width_hren] <;> (try split) <;> simp_all
  | _ => intro tw; simp_all [Sk.hren, Sk.WidthOkC, Function.comp_def]

theorem Sk.low_hren (σ : String → Int) (dw : String → Nat) (pfx : String) :
    ∀ (sk : Sk) (tw : Nat),
      (sk.hren pfx).low σ dw tw = (sk.low (fun n => σ (pfx ++ n)) (fun n => dw (pfx ++ n)) tw).rename (pfx ++ ·) := by
  intro sk
  induction sk with
  | rsz pr p ih =>
      intro tw
      cases pr <;> simp only [Sk.hren, Sk.low, Sk.width_hren] <;> (try split) <;> simp_all [Expr2.rename]
  | sh d sg l r ihl ihr =>
      intro tw
      simp only [Sk.hren, Sk.low, Sk.width_hren]
      cases d <;> cases sg <;>
        simp only [apply_ite (Expr2.rename (pfx ++ ·)), Expr2.rename, ihl, ihr, Bool.false_eq_true, if_false,
          if_true]
  | fit sg p ih =>
      intro tw
      simp only [Sk.hren, Sk.low, Sk.width_hren, ih, fitDivOperand2]
      cases sg <;> simp only [apply_ite (Expr2.rename (pfx ++ ·)), Expr2.rename, Bool.false_eq_true, if_false,
        if_true]
  | _ => intro tw; simp_all [Sk.hren, Sk.low, Expr2.rename, accExpr_hren, Part.expr_hren,
      Expr2.renameList_eq_map, Function.comp_def]

end rename

/-! ## The recognizer of declarations commutes with the renaming -/

section declren
open CombView CombEq

theorem Aff.hren_add (pfx : String) (a b : Aff) : (a.add b).hren pfx = (a.hren pfx).add (b.hren pfx) := by
  simp [Aff.hren, Aff.add]

theorem Aff.negQs_hren (pfx : String) : ∀ qs : List (String × Int × Int),
    Aff.negQs (qs.map fun p => (pfx ++ p.1, p.2)) = (Aff.negQs qs).map fun p => (pfx ++ p.1, p.2)
  | [] => rfl
  | (n, k, d) :: qs => by simp [Aff.negQs, Aff.negQs_hren pfx qs]

theorem Aff.scaleQs_hren (pfx : String) (k : Int) : ∀ qs : List (String × Int × Int),
    Aff.scaleQs k (qs.map fun p => (pfx ++ p.1, p.2)) = (Aff.scaleQs k qs).map fun p => (pfx ++ p.1, p.2)
  | [] => rfl
  | (n, m, d) :: qs => by simp [Aff.scaleQs, Aff.scaleQs_hren pfx k qs]

theorem Aff.negTerms_hren (pfx : String) : ∀ ts : List (String × Int),
    Aff.negTerms (ts.map fun p => (pfx ++ p.1, p.2)) = (Aff.negTerms ts).map fun p => (pfx ++ p.1, p.2)
  | [] => rfl
  | (n, k) :: ts => by simp [Aff.negTerms, Aff.negTerms_hren pfx ts]

theorem Aff.scaleTerms_hren (pfx : String) (k : Int) : ∀ ts : List (String × Int),
    Aff.scaleTerms k (ts.map fun p => (pfx ++ p.1, p.2)) = (Aff.scaleTerms k ts).map fun p => (pfx ++ p.1, p.2)
  | [] => rfl
  | (n, m) :: ts => by simp [Aff.scaleTerms, Aff.scaleTerms_hren pfx k ts]

theorem affMul_hren {a b c : Aff} (pfx : String) (h : affMul a b = some c) :
    affMul (a.hren pfx) (b.hren pfx) = some (c.hren pfx) := by
  unfold affMul at h ⊢
  have e1 : ((a.hren pfx).terms.isEmpty && (a.hren pfx).qs.isEmpty) = (a.terms.isEmpty && a.qs.isEmpty) := by
    simp [Aff.hren]
  have e2 : ((b.hren pfx).terms.isEmpty && (b.hren pfx).qs.isEmpty) = (b.terms.isEmpty && b.qs.isEmpty) := by
    simp [Aff.hren]
  rw [e1, e2]
  cases ha : (a.terms.isEmpty && a.qs.isEmpty) <;> cases hb : (b.terms.isEmpty && b.qs.isEmpty) <;>
    simp only [ha, hb, if_true, if_false, Bool.false_eq_true, Option.some.injEq, reduceCtorEq] at h ⊢ <;>
    subst h <;> simp [Aff.scale, Aff.hren, Aff.scaleTerms_hren, Aff.scaleQs_hren]

theorem affDiv_hren {a b c : Aff} (pfx : String) (h : affDiv a b = some c) :
    affDiv (a.hren pfx) (b.hren pfx) = some (c.hren pfx) := by
  obtain ⟨n, rfl, hbt, hbq, hbc, rfl⟩ := affDiv_cases h
  have hb' : b.hren pfx = { c := b.c } := by
    cases b; simp only at hbt hbq; subst hbt; subst hbq; rfl
  rw [hb']
  simp [affDiv, Aff.var, Aff.hren, hbc]

theorem affBin_hren {op : SymBinOp} {a b c : Aff} (pfx : String) (h : affBin op a b = some c) :
    affBin op (a.hren pfx) (b.hren pfx) = some (c.hren pfx) := by
  unfold affBin at h ⊢
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp [Aff.hren_add]
  · simp only [Option.some.injEq] at h; subst h
    simp [Aff.sub, Aff.add, Aff.neg, Aff.hren, Aff.negTerms_hren, Aff.negQs_hren]
  · exact affMul_hren pfx h
  · exact affMul_hren pfx h
  · exact affDiv_hren pfx h
  · simp at h

theorem affOf?_hren (pfx : String) : ∀ {e : PExpr} {a : Aff}, affOf? e = some a →
    affOf? (e.hren pfx) = some (a.hren pfx)
  | .int v, a, h => by
      simp only [affOf?, Option.some.injEq] at h; subst h; simp [PExpr.hren, affOf?, Aff.const, Aff.hren]
  | .genvarRef n, a, h => by
      simp only [affOf?, Option.some.injEq] at h; subst h; simp [PExpr.hren, affOf?, Aff.var, Aff.hren]
  | .paramRef n none, a, h => by
      simp only [affOf?, Option.some.injEq] at h; subst h; simp [PExpr.hren, affOf?, Aff.var, Aff.hren]
  | .binary op l r, a, h => by
      simp only [affOf?] at h
      rcases hl : affOf? l with _ | al <;> rcases hr : affOf? r with _ | ar <;>
        simp only [hl, hr, reduceCtorEq] at h
      simp only [PExpr.hren, affOf?, affOf?_hren pfx hl, affOf?_hren pfx hr]
      exact affBin_hren pfx h
  | .lit _, _, h | .ident _, _, h | .paramRef _ (some _), _, h | .enumRef .., _, h | .fill _, _, h
  | .unary .., _, h | .ternary .., _, h | .concat _, _, h | .resize .., _, h | .signedResize .., _, h
  | .squash2 .., _, h | .sysCall .., _, h | .bitSel .., _, h | .partSel .., _, h | .repl .., _, h
  | .reduce .., _, h | .cast .., _, h | .arrayElem .., _, h | .arrayPart .., _, h
  | .unsupported .., _, h => by simp [affOf?] at h

theorem dimOf?_hren (pfx nm nm' : String) {d : PDim} {p : PDim × Aff × Aff} (h : dimOf? nm d = .ok p) :
    dimOf? nm' (PDim.hren pfx d) = .ok (PDim.hren pfx p.1, p.2.1.hren pfx, p.2.2.hren pfx) := by
  unfold dimOf? at h ⊢
  rcases hm : affOf? d.msb with _ | m <;> rcases hl : affOf? d.lsb with _ | l <;> simp [hm, hl] at h
  subst h
  simp [PDim.hren, affOf?_hren pfx hm, affOf?_hren pfx hl]

theorem declOf?_hren (pfx : String) {pd : PDecl} {dt : DeclT} (h : declOf? pd = .ok dt) :
    declOf? (pd.hren pfx) = .ok (dt.hren pfx) := by
  unfold declOf? at h ⊢
  have hu : (PDecl.hren pfx pd).unpackedDims.isEmpty = pd.unpackedDims.isEmpty := by simp [PDecl.hren]
  have hi : (PDecl.hren pfx pd).init = pd.init.map (PExpr.hren pfx) := rfl
  have ht : (PDecl.hren pfx pd).twoState = pd.twoState := rfl
  have hty : (PDecl.hren pfx pd).type = pd.type.hren pfx := rfl
  rw [hu, hi, ht, hty]
  by_cases h0 : pd.unpackedDims.isEmpty = true
  · simp only [h0, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
    rcases hinit : pd.init with _ | e
    · simp only [hinit, Option.map_none] at h ⊢
      by_cases h2 : pd.twoState = true
      · simp [h2] at h
      · simp only [h2, Bool.false_eq_true, if_false] at h ⊢
        cases hty' : pd.type with
        | typeRef _ _ _ => simp [hty'] at h
        | unrecoverable _ => simp [hty'] at h
        | packed ds r =>
          simp only [hty'] at h
          rcases ds with _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, rest⟩⟩⟩
          · simp only [Except.ok.injEq] at h; subst h
            simp [PType.hren, DeclT.hren, PDecl.hren]
          · rcases hd : dimOf? pd.name d1 with e | p1 <;> simp only [hd] at h
            · simp at h
            simp only [Except.ok.injEq] at h; subst h
            simp [PType.hren, DeclT.hren, PDecl.hren, dimOf?_hren pfx pd.name _ hd]
          · rcases hd1 : dimOf? pd.name d1 with e | p1 <;> simp only [hd1] at h
            · simp at h
            rcases hd2 : dimOf? pd.name d2 with e | p2 <;> simp only [hd2] at h
            · simp at h
            simp only [Except.ok.injEq] at h; subst h
            simp [PType.hren, DeclT.hren, PDecl.hren, dimOf?_hren pfx pd.name _ hd1,
              dimOf?_hren pfx pd.name _ hd2]
          · simp at h
    · simp [hinit] at h
  · simp [h0] at h

theorem declsOf?_append : ∀ {l1 l2 : List PDecl} {s1 s2 : List DeclT},
    declsOf? l1 = .ok s1 → declsOf? l2 = .ok s2 → declsOf? (l1 ++ l2) = .ok (s1 ++ s2)
  | [], l2, s1, s2, h1, h2 => by simp only [declsOf?, Except.ok.injEq] at h1; subst h1; simpa using h2
  | pd :: rest, l2, s1, s2, h1, h2 => by
      obtain ⟨dt, s1', hd, hr, rfl⟩ := declsOf?_cons h1
      simp [declsOf?, hd, declsOf?_append hr h2]

theorem declsOf?_hren (pfx : String) : ∀ {l : List PDecl} {s : List DeclT},
    declsOf? l = .ok s → declsOf? (l.map (PDecl.hren pfx)) = .ok (s.map (DeclT.hren pfx))
  | [], s, h => by simp only [declsOf?, Except.ok.injEq] at h; subst h; rfl
  | pd :: rest, s, h => by
      obtain ⟨dt, s', hd, hr, rfl⟩ := declsOf?_cons h
      simp [declsOf?, declOf?_hren pfx hd, declsOf?_hren pfx hr]

theorem declsOf?_flatMap {α : Type} (f : α → List PDecl) (g : α → List DeclT)
    (h : ∀ x, declsOf? (f x) = .ok (g x)) : ∀ l : List α, declsOf? (l.flatMap f) = .ok (l.flatMap g)
  | [] => rfl
  | x :: xs => by simp [List.flatMap_cons, declsOf?_append (h x) (declsOf?_flatMap f g h xs)]

/-- The declarations of the summary keep the names and port flags of the source declarations. -/
theorem declsOf?_sig : ∀ {l : List PDecl} {s : List DeclT}, declsOf? l = .ok s →
    s.map (fun dt => (dt.name, dt.isInput, dt.isOutput)) = l.map (fun pd => (pd.name, pd.isInput, pd.isOutput))
  | [], s, h => by simp only [declsOf?, Except.ok.injEq] at h; subst h; rfl
  | pd :: rest, s, h => by
      obtain ⟨dt, s', hd, hr, rfl⟩ := declsOf?_cons h
      obtain ⟨hn, hi, ho, -⟩ := declOf?_spec hd
      simp [hn, hi, ho, declsOf?_sig hr]

@[simp] theorem dimsW_hren (σ : String → Int) (pfx : String) : ∀ dims : List (PDim × Aff × Aff),
    dimsW σ (dims.map fun p => (PDim.hren pfx p.1, p.2.1.hren pfx, p.2.2.hren pfx)) =
      dimsW (fun n => σ (pfx ++ n)) dims
  | [] => rfl
  | p :: rest => by simp [dimsW, dimsW_hren σ pfx rest]

@[simp] theorem DeclT.width_hren (σ : String → Int) (pfx : String) (dt : DeclT) :
    (dt.hren pfx).width σ = dt.width (fun n => σ (pfx ++ n)) := by
  simp [DeclT.hren, DeclT.width]

@[simp] theorem DeclT.vals_hren (σ : String → Int) (pfx : String) (dt : DeclT) :
    (dt.hren pfx).vals σ = dt.vals (fun n => σ (pfx ++ n)) := by
  simp [DeclT.hren, DeclT.vals]

@[simp] theorem DeclT.elemW_hren (σ : String → Int) (pfx : String) (dt : DeclT) :
    (dt.hren pfx).elemW σ = dt.elemW (fun n => σ (pfx ++ n)) := by
  simp only [DeclT.elemW_vals, DeclT.vals_hren]

@[simp] theorem DeclT.name_hren (pfx : String) (dt : DeclT) : (dt.hren pfx).name = pfx ++ dt.name := rfl

theorem DeclT.toDecl_hren (σ : String → Int) (pfx : String) (dt : DeclT) :
    (dt.hren pfx).toDecl σ = Decl.hoist pfx (dt.toDecl (fun n => σ (pfx ++ n))) := by
  simp [DeclT.toDecl, Decl.hoist, DeclT.hren, DeclT.width]

/-- A declaration of a list with distinct names is the one its name finds. -/
theorem findDecl_of_mem {l : List DeclT} (hnd : (l.map (·.name)).Nodup) {dt : DeclT} (h : dt ∈ l) :
    findDecl l dt.name = some dt := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rcases List.mem_cons.mp h with rfl | hm
      · simp [findDecl]
      · have hne : x.name ≠ dt.name := fun he => hnd.1 ⟨dt, hm, he.symm⟩
        have := ih hnd.2 hm
        have hb : (x.name == dt.name) = false := by simpa using hne
        simp only [findDecl, List.find?_cons] at this ⊢
        simp [hb, this]

end declren



/-! ## One process: the real one and the twin's are the same expression -/

namespace CombHier
open CombView CombEq

section procs
variable {σ : String → Int} {EP EF : IEnv} {elP elF : List (String × Nat)}
  {DWP DWF : String → Option Nat} {DGP DGF : String → Option (List (Int × Int))}
  {EWP EWF : String → Option Nat} {nsP nsF : List String} {dw : String → Nat}

/-- The access facts of a site of a loop-free summary (`site_ok` without the bit-read obligation). -/
theorem site_acc {s : Summary} {args : List Int} (hok : s.StructOk) (hauto : s.AutoObl σ args)
    (hin : s.InRangeObl σ) {ls : LSite} (hls : ls ∈ s.lsites) (hh : ls.hdrs = []) :
    ∀ a ∈ ls.site.tgt :: ls.site.rds, AccOK σ (s.DW σ) (s.DG σ) (s.EW σ) s.params a := by
  have hok' := hok
  obtain ⟨-, hnames, -, haff, -, hdecl, hacc, -⟩ := hok'
  obtain ⟨hauto1, hauto2, -⟩ := hauto
  have hpar : ∀ n ∈ s.params, σ n = σ n := fun _ _ => rfl
  have hin' : s.InWin σ σ ls.site := by have := hin.1 ls hls; rw [hh] at this; exact this
  have hrd : ∀ r ∈ ls.site.rds, s.InR σ σ r := by have := hauto1 ls hls; rw [hh] at this; exact this
  intro a ha
  have hInR : s.InR σ σ a := by
    rcases List.mem_cons.mp ha with rfl | hm
    · exact hin'.1
    · exact hrd a hm
  refine ⟨?_, accGeom_of hpar hdecl (hacc ls hls a (TSite.mem_accs ha)) hInR (hauto2 ls hls a (TSite.mem_accs ha)),
    ?_⟩
  · have hn : a.name ∈ s.declNames := by
      apply hnames ls hls
      simp only [TSite.names, List.mem_cons, List.mem_map]
      rcases List.mem_cons.mp ha with rfl | hm
      · exact Or.inl rfl
      · exact Or.inr ⟨a, List.mem_append_right _ hm, rfl⟩
    simpa [Summary.DW] using find_isSome_of_mem hn
  · intro x hx n hn
    have := haff ls hls n (by
      simp only [TSite.affNames, List.mem_append, List.mem_flatMap]
      rcases List.mem_cons.mp ha with rfl | hm
      · exact Or.inl (Or.inl ⟨x, hx, hn⟩)
      · exact Or.inl (Or.inr ⟨a, Or.inr hm, x, hx, hn⟩))
    simpa [hh] using this

/-- The constants of a site of a loop-free summary. -/
theorem site_const {s : Summary} (hok : s.StructOk) (hin : s.InRangeObl σ) {ls : LSite} (hls : ls ∈ s.lsites)
    (hh : ls.hdrs = []) : ls.site.ConstOK σ s.params := by
  have := site_co hok hin hls (σ' := σ) (by rw [hh]; rfl)
  simpa [hh] using this

/-- A whole-signal or select-free right-hand side whose skeleton is as wide as its context (`Sk.exactW`) has that
self-determined width. -/
theorem rhs_selfWidth (C : Ctx σ EP elP DWP DGP EWP nsP) (hdw : ∀ n, (DWP n).isSome = true → DWP n = some (dw n))
    {ds : List DeclT} {v : PExpr} {rs : List Acc} (h : rhsRds? ds v = .ok rs) (hf : fragOk v = true)
    (hacc : ∀ a ∈ rs, AccOK σ DWP DGP EWP nsP a) (hcn : ConstOK σ nsP v) {tw : Nat}
    (hw : (skRhs v rs).WidthOkC σ dw tw) (hex : (skRhs v rs).exactW = true) :
    selfWidth2 EP elP v = some tw := by
  have hnf : ∀ b, v ≠ .fill b := by rintro b rfl; simp [skRhs, Sk.exactW] at hex
  have h1 : rdsOfW? ds v = .ok rs := by cases v <;> first | exact h | exact absurd rfl (hnf _)
  have h2 : fragW v = true := by cases v <;> first | exact hf | exact absurd rfl (hnf _)
  have h3 : skRhs v rs = skT v rs := by cases v <;> first | rfl | exact absurd rfl (hnf _)
  rw [h3] at hw hex
  rw [(skT_shapeC C hdw v rs h1 h2 hacc hcn tw hw).1, Sk.width_of_exactW σ dw _ tw hex hw]

/-- `rhs_selfWidth` for a right-hand side whose unsigned twin is the site's (`PExpr.unsign`): the expression as written
has the twin's self-determined width. -/
theorem rhs_selfWidthU (C : Ctx σ EP elP DWP DGP EWP nsP) (hdw : ∀ n, (DWP n).isSome = true → DWP n = some (dw n))
    {ds : List DeclT} {v : PExpr} {rs : List Acc} (h : rhsRds? ds v.unsign = .ok rs) (hf : fragOk v.unsign = true)
    (hacc : ∀ a ∈ rs, AccOK σ DWP DGP EWP nsP a) (hcn : ConstOK σ nsP v.unsign) {tw : Nat}
    (hw : (skRhs v.unsign rs).WidthOkC σ dw tw) (hex : (skRhs v.unsign rs).exactW = true) :
    selfWidth2 EP elP v = some tw := by
  have hnf : ∀ b, v.unsign ≠ .fill b := by intro b hb; rw [hb] at hex; simp [skRhs, Sk.exactW] at hex
  have key : ∀ x : PExpr, (∀ b, x ≠ .fill b) →
      rhsRds? ds x = rdsOfW? ds x ∧ fragOk x = fragW x ∧ skRhs x rs = skT x rs := by
    intro x hx
    cases x <;> first | exact ⟨rfl, rfl, rfl⟩ | exact absurd rfl (hx _)
  obtain ⟨k1, k2, k3⟩ := key _ hnf
  rw [k1] at h
  rw [k2] at hf
  rw [k3] at hw hex
  rw [(skT_shapeCU C hdw v rs h hf hacc hcn tw hw).1, Sk.width_of_exactW σ dw _ tw hex hw]

/-- **A process of the parent**: instantiated in the parent's own environment (the hierarchical instantiation) or
in the twin's, it is the expression its site determines. -/
theorem parent_proc_eq (CP : Ctx σ EP elP DWP DGP EWP nsP) (CF : Ctx σ EF elF DWF DGF EWF nsF)
    (hdwP : ∀ n, (DWP n).isSome = true → DWP n = some (dw n))
    (hdwF : ∀ n, (DWF n).isSome = true → DWF n = some (dw n))
    {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p = .ok st)
    (hsoP : ∀ a ∈ st.tgt :: st.rds, AccOK σ DWP DGP EWP nsP a)
    (hsoF : ∀ a ∈ st.tgt :: st.rds, AccOK σ DWF DGF EWF nsF a)
    (hcnP : st.ConstOK σ nsP) (hcnF : st.ConstOK σ nsF) (hf : fragOk (rhsOf p) = true)
    (hw : (skRhs (rhsOf p) st.rds).WidthOkC σ dw (st.tgt.win σ dw).2.2) :
    instProcess2 EP elP p = instProcess2 EF elF p := by
  rw [proc_shapeC CP hdwP hs hsoP hcnP hf hw, proc_shapeC CF hdwF hs hsoF hcnF hf hw]

/-- **A process of the parent, read through its unsigned twin** (`twinOf`): instantiated in the parent's own environment
as written, or in the twin's as its unsigned twin, it is the expression the twin's site determines (`proc_shapeCU`). -/
theorem parent_proc_eqU (CP : Ctx σ EP elP DWP DGP EWP nsP) (CF : Ctx σ EF elF DWF DGF EWF nsF)
    (hdwP : ∀ n, (DWP n).isSome = true → DWP n = some (dw n))
    (hdwF : ∀ n, (DWF n).isSome = true → DWF n = some (dw n))
    {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p.unsign = .ok st)
    (hsoP : ∀ a ∈ st.tgt :: st.rds, AccOK σ DWP DGP EWP nsP a)
    (hsoF : ∀ a ∈ st.tgt :: st.rds, AccOK σ DWF DGF EWF nsF a)
    (hcnP : st.ConstOK σ nsP) (hcnF : st.ConstOK σ nsF) (hf : fragOk (rhsOf p.unsign) = true)
    (hw : (skRhs (rhsOf p.unsign) st.rds).WidthOkC σ dw (st.tgt.win σ dw).2.2) :
    instProcess2 EP elP p = instProcess2 EF elF p.unsign := by
  rw [proc_shapeCU CP hdwP hs hsoP hcnP hf hw, proc_shapeC CF hdwF hs hsoF hcnF hf hw]

/-- **An input port connection** (`connProcs`): the assignment of the port from its actual `e` is the twin's
`p ++ a = e.unsign` (`connPP`), instantiated: the hierarchical instantiation lowers the actual as written, the twin its
unsigned twin, and under the twin's width obligation (the actual exactly as wide as the port) the two are the expression
the twin's site determines (`rhs_shapeCU`, `proc_shapeC`). -/
theorem conn_in_eq (CP : Ctx σ EP elP DWP DGP EWP nsP) (CF : Ctx σ EF elF DWF DGF EWF nsF)
    (hdwP : ∀ n, (DWP n).isSome = true → DWP n = some (dw n))
    (hdwF : ∀ n, (DWF n).isSome = true → DWF n = some (dw n))
    {pfx : String} {conns : List PConn} {dc : Decl} {p : String} {e : PExpr} {net : Bool}
    (hfind : conns.find? (·.port == dc.name) = some (.input p (some e) net)) (hin : dc.isInput = true)
    {ds : List DeclT} {pos : Nat} {st : TSite}
    (hs : siteOf? ds pos (.assign (pfx ++ dc.name) e.unsign) = .ok st)
    (hsoP : ∀ a ∈ st.rds, AccOK σ DWP DGP EWP nsP a) (hsoF : ∀ a ∈ st.tgt :: st.rds, AccOK σ DWF DGF EWF nsF a)
    (hcnP : st.ConstOK σ nsP) (hcnF : st.ConstOK σ nsF) (hf : fragOk e.unsign = true)
    (hw : (skRhs e.unsign st.rds).WidthOkC σ dw dc.width) (hex : (skRhs e.unsign st.rds).exactW = true)
    (hdn : dw (pfx ++ dc.name) = dc.width) :
    connProcs EP elP pfx conns dc = [instProcess2 EF elF (.assign (pfx ++ dc.name) e.unsign)] := by
  rcases siteOf?_cases hs with ⟨t, v, rds, hp, hrds, rfl⟩ | ⟨l, v, tg, rds, hp, -, -, -⟩
  · simp only [PProcess.assign.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    have hcnP' : ConstOK σ nsP e.unsign := hcnP
    have hsw := rhs_selfWidthU CP hdwP hrds hf hsoP hcnP' hw hex
    have hfit := rhs_shapeCU CP hdwP hrds hf hsoP hcnP' hw
    have hwF : (skRhs (rhsOf (PProcess.assign (pfx ++ dc.name) e.unsign)) rds).WidthOkC σ dw
        ((Acc.whole (pfx ++ dc.name)).win σ dw).2.2 := by
      simpa [rhsOf, Acc.win, hdn] using hw
    rw [proc_shapeC CF hdwF hs hsoF hcnF hf hwF]
    unfold connProcs
    simp only [hfind, hin, Bool.not_true, Bool.false_eq_true, if_false]
    cases net <;>
      simp [netNarrower, portInOk, hsw, hfit, rhsOf, Acc.lhs, Acc.win, hdn]
  · simp at hp

/-- **An output port connection** (`connProcs`): the assignment of the target from the port is the twin's
`target = p ++ y`, instantiated. -/
theorem conn_out_eq (CP : Ctx σ EP elP DWP DGP EWP nsP) (CF : Ctx σ EF elF DWF DGF EWF nsF)
    (hdwP : ∀ n, (DWP n).isSome = true → DWP n = some (dw n))
    (hdwF : ∀ n, (DWF n).isSome = true → DWF n = some (dw n))
    {pfx : String} {conns : List PConn} {dc : Decl} {p : String} {t : PLhs}
    (hfind : conns.find? (·.port == dc.name) = some (.output p (some t))) (hout : dc.isOutput = true)
    {ds : List DeclT} {pos : Nat} {st : TSite}
    (hs : siteOf? ds pos (.assignL t (.ident (pfx ++ dc.name))) = .ok st)
    (hrds : st.rds = [.whole (pfx ++ dc.name)])
    (hsoP : AccOK σ DWP DGP EWP nsP st.tgt) (hsoF : ∀ a ∈ st.tgt :: st.rds, AccOK σ DWF DGF EWF nsF a)
    (hcnF : st.ConstOK σ nsF)
    (hw : (skRhs (.ident (pfx ++ dc.name)) st.rds).WidthOkC σ dw (st.tgt.win σ dw).2.2)
    (hdn : dw (pfx ++ dc.name) = dc.width) :
    connProcs EP elP pfx conns dc = [instProcess2 EF elF (.assignL t (.ident (pfx ++ dc.name)))] := by
  rcases siteOf?_cases hs with ⟨t', v, rds, hp, -, -⟩ | ⟨l, v, tg, rds, hp, htg, -, rfl⟩
  · simp at hp
  · simp only [PProcess.assignL.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp only at hrds
    subst hrds
    have hlhs := instLhs_acc_w CP hdwP htg hsoP
    have hwt : dw (pfx ++ dc.name) = (tg.win σ dw).2.2 := by
      simpa [skRhs, skT, Sk.WidthOkC, Acc.win] using hw
    rw [proc_shapeC CF hdwF hs hsoF hcnF rfl hw]
    unfold connProcs
    simp [hfind, hout, hlhs, portOut, ← hwt, hdn, skRhs, skT, Sk.low, accExpr, rhsOf]

end procs

/-- **A process of a child**: instantiated in the child's environment at its own parameter point and renamed under
the instance prefix (the hierarchical instantiation, `instBodyProc`), or renamed first and instantiated in the
twin's environment, it is the expression its site determines. -/
theorem child_proc_eq {σF : String → Int} {EC EF : IEnv} {elC elF : List (String × Nat)}
    {DWC DWF : String → Option Nat} {DGC DGF : String → Option (List (Int × Int))}
    {EWC EWF : String → Option Nat} {nsC nsF : List String} {pfx : String} {dwF : String → Nat}
    (CC : Ctx (fun n => σF (pfx ++ n)) EC elC DWC DGC EWC nsC) (CF : Ctx σF EF elF DWF DGF EWF nsF)
    (hdwC : ∀ n, (DWC n).isSome = true → DWC n = some (dwF (pfx ++ n)))
    (hdwF : ∀ n, (DWF n).isSome = true → DWF n = some (dwF n))
    {dsC dsF : List DeclT} {posC posF : Nat} {p : PProcess} {stC stF : TSite}
    (hsC : siteOf? dsC posC p = .ok stC) (hsF : siteOf? dsF posF (p.hren pfx) = .ok stF)
    (htg : stF.tgt = stC.tgt.hren pfx)
    (hsk : skRhs (rhsOf (p.hren pfx)) stF.rds = (skRhs (rhsOf p) stC.rds).hren pfx)
    (hsoC : ∀ a ∈ stC.tgt :: stC.rds, AccOK (fun n => σF (pfx ++ n)) DWC DGC EWC nsC a)
    (hsoF : ∀ a ∈ stF.tgt :: stF.rds, AccOK σF DWF DGF EWF nsF a)
    (hcnC : stC.ConstOK (fun n => σF (pfx ++ n)) nsC) (hcnF : stF.ConstOK σF nsF)
    (hfC : fragOk (rhsOf p) = true) (hfF : fragOk (rhsOf (p.hren pfx)) = true)
    (hwF : (skRhs (rhsOf (p.hren pfx)) stF.rds).WidthOkC σF dwF (stF.tgt.win σF dwF).2.2) :
    ∃ e, instProcess2 EC elC p = .assign (stC.tgt.lhs (fun n => σF (pfx ++ n))) e ∧
      instProcess2 EF elF (p.hren pfx) =
        .assign ((stC.tgt.lhs (fun n => σF (pfx ++ n))).rename (pfx ++ ·)) (e.rename (pfx ++ ·)) := by
  have hwC : (skRhs (rhsOf p) stC.rds).WidthOkC (fun n => σF (pfx ++ n)) (fun n => dwF (pfx ++ n))
      (stC.tgt.win (fun n => σF (pfx ++ n)) (fun n => dwF (pfx ++ n))).2.2 := by
    rw [hsk, htg, Acc.win_hren_snd, Sk.widthOkC_hren] at hwF
    exact hwF
  refine ⟨_, proc_shapeC CC hdwC hsC hsoC hcnC hfC hwC, ?_⟩
  rw [proc_shapeC CF hdwF hsF hsoF hcnF hfF hwF, hsk, htg, Acc.lhs_hren, Sk.low_hren, Acc.win_hren_snd]

/-- A child's flattened assignment (`instBodyProc`): the target and the right-hand side renamed under the prefix. -/
theorem instBodyProc_assign (pfx : String) (i : PInst) (ports : List Decl) (bare : List (String × String))
    (t : Lhs2) (e : Expr2) :
    instBodyProc pfx i ports bare (.assign t e) = .assign (t.rename (pfx ++ ·)) (e.rename (pfx ++ ·)) := by
  simp [instBodyProc, Process2.clock?, Process2.rename, Process2.inInstance]

/-- The access facts of a child's site at its own parameter point, from those of its renamed copy in the twin. -/
theorem accGeom_of_hren {σF : String → Int} {DGF DGC : String → Option (List (Int × Int))}
    {EWF EWC : String → Option Nat} {pfx : String} {a : Acc}
    (h : AccGeom σF DGF EWF (a.hren pfx)) (hDG : DGF (pfx ++ a.name) = DGC a.name)
    (hEW : EWF (pfx ++ a.name) = EWC a.name) : AccGeom (fun n => σF (pfx ++ n)) DGC EWC a := by
  cases a <;> simp_all [AccGeom, Acc.hren, Acc.name]

end CombHier

namespace CombHier
open CombView CombEq

/-! ## The flat twin -/

/-- The prefix of a module-level instance (`PInst.prefix` at an empty generate path). -/
def hpfx (i : PInst) : String := i.name ++ "."

/-- The port declarations of a child, in its port order. -/
def childPorts (c : PDesign) : List PDecl := c.decls.filter fun pd => pd.isInput || pd.isOutput

/-- The localparams standing for a child's parameters at an instance: the override (a constant expression of the
parent's scope), else the child's default, renamed. -/
def childParamLps (i : PInst) (c : PDesign) : Except String (List PLocalParam) :=
  c.params.mapM fun p =>
    match i.params.lookup p.name with
    | some e => .ok { name := hpfx i ++ p.name, expr := e, type? := p.type?.map (PType.hren (hpfx i)),
                      signed? := p.signed? }
    | none =>
        match p.default? with
        | some e => .ok { name := hpfx i ++ p.name, expr := e.hren (hpfx i),
                          type? := p.type?.map (PType.hren (hpfx i)), signed? := p.signed? }
        | none => .error s!"instance `{i.name}`: parameter `{p.name}` of module `{c.name}` has no override and no default"

/-- The continuous assignment of one port connection (`connProcs` at the template level): `p ++ a = actual` for an
input, `target = p ++ y` for an output. v1 reads every port connected. The input's actual is its unsigned twin
(`PExpr.unsign`, `CombView.lean`): a select of a signed signal is an unsigned value (IEEE 1800-2023 §11.8.1) and
`instExpr2` lowers it through the base's element width, which the cast marker does not change, and a whole signed signal
is read as the same bits where it is not widened; `conn_in_eq` proves the connection the hierarchical instantiation builds
from the actual as written equal to the twin's, under the twin's width obligation (the actual exactly as wide as its
port). -/
def connPP (i : PInst) (pd : PDecl) : Except String PProcess :=
  match i.conns.find? (·.port == pd.name) with
  | none => .error s!"instance `{i.name}`: port `{pd.name}` has no connection"
  | some (.unsupported _ k t) => .error s!"instance `{i.name}`: port `{pd.name}`: {t} ({k})"
  | some (.input _ (some e) _) =>
      if pd.isInput && !pd.isOutput then .ok (.assign (hpfx i ++ pd.name) e.unsign)
      else .error s!"instance `{i.name}`: port `{pd.name}` is connected as an input but is not one"
  | some (.input _ none _) =>
      .error s!"instance `{i.name}`: input port `{pd.name}` is left open (an open input reads `x` or `z`; v1 of the hierarchy summary reads every port connected)"
  | some (.output _ (some t)) =>
      if pd.isOutput && !pd.isInput then .ok (.assignL t (.ident (hpfx i ++ pd.name)))
      else .error s!"instance `{i.name}`: port `{pd.name}` is connected as an output but is not one"
  | some (.output _ none) =>
      .error s!"instance `{i.name}`: output port `{pd.name}` is left open (v1 of the hierarchy summary reads every port connected)"

/-- Does an item list hold a module instance (at any depth)? -/
def hasInst (l : List GenItem) : Bool := !GenItem.listInstFree l

/-- The refusal of an item of the parent's generate list that is not a module-level instance. -/
def itemRefusal : GenItem → String
  | .genFor label g _ _ _ _ body =>
      if hasInst body then
        s!"an instance sits inside the generate loop `{label.getD "genblk"}` (genvar `{g}`): v1 of the hierarchy summary reads module-level instances only (one instance per loop iteration would make the child's sites a generate family whose names carry the loop index, which the summary does not build yet); the structure of such a design can be proved by hand (`Examples/system-verilog/ripple_fa` is a worked by-hand proof)"
      else
        s!"the module has a generate loop (`{label.getD "genblk"}`) besides its instances: v1 of the hierarchy summary reads a parent whose generate items are all module-level instances"
  | .genIf _ t e =>
      if hasInst t || hasInst e then
        "an instance sits inside a generate `if`: v1 of the hierarchy summary reads module-level instances only"
      else "the module has a generate `if` besides its instances: v1 of the hierarchy summary reads a parent whose generate items are all module-level instances"
  | .process _ => "the module has a generate-level process besides its instances (v1 of the hierarchy summary)"
  | .unsupported k t => s!"{t} ({k})"
  | .inst i => s!"instance `{i.name}` has a generate path (v1 of the hierarchy summary reads module-level instances only)"

/-- The module-level instances of the parent, with their children from the library; anything else refused. -/
def hierInsts (d : PDesign) (lib : List PDesign) : Except String (List (PInst × PDesign)) :=
  d.generates.mapM fun it =>
    match it with
    | .inst i =>
        if !i.path.isEmpty then .error (itemRefusal it)
        else
          match lib.find? (·.name == i.module) with
          | none => .error s!"instance `{i.name}`: module `{i.module}` is not in the envelope's module library"
          | some c => .ok (i, c)
    | it => .error (itemRefusal it)

/-- The checks on one child and its instance, with the refusal that names what v1 does not read. -/
def childCheck (i : PInst) (c : PDesign) : Except String Unit := do
  unless c.generates.isEmpty do
    throw s!"instance `{i.name}`: module `{c.name}` has generate blocks or instances of its own (v1 of the hierarchy summary reads children without them)"
  match c.others with
  | (k, t) :: _ =>
      throw s!"instance `{i.name}`: module `{c.name}` has a member outside the semantic tier (`{k}`: {t})"
  | [] => pure ()
  unless c.enums.isEmpty && c.packageParams.isEmpty do
    throw s!"instance `{i.name}`: module `{c.name}` has enums or package parameters (v1 of the hierarchy summary reads neither)"
  match i.params.find? (fun (n, _) => !c.params.any (·.name == n)) with
  | some (n, _) => throw s!"instance `{i.name}`: `{n}` is not a parameter of module `{c.name}`"
  | none => pure ()
  match i.conns.find? (fun cn => !(childPorts c).any (·.name == cn.port)) with
  | some cn => throw s!"instance `{i.name}`: connection `{cn.port}` names no port of module `{c.name}`"
  | none => pure ()
  match c.summary with
  | .error m => throw s!"instance `{i.name}`: module `{c.name}` is outside the supported fragment — {m}"
  | .ok _ => pure ()

/-- The twin's part of one instance: the localparams (the child's parameters, then its localparams), the hoisted
declarations, and the processes (the port connections in port order, then the child's processes), all under the
instance prefix. -/
def instPart (i : PInst) (c : PDesign) : Except String (List PLocalParam × List PDecl × List PProcess) := do
  childCheck i c
  let plps ← childParamLps i c
  let conns ← (childPorts c).mapM (connPP i)
  pure (plps ++ c.localParams.map (PLocalParam.hren (hpfx i)), c.decls.map (PDecl.hren (hpfx i)),
    conns ++ c.processes.map (PProcess.hren (hpfx i)))

/-- The twin assembled from the parts of its instances. The parent's own processes are their unsigned twins
(`PProcess.unsign`, as `PDesign.unsign` reads a flat design with signed reads; `parent_proc_eqU`). -/
def twinOf (d : PDesign) (parts : List (List PLocalParam × List PDecl × List PProcess)) : PDesign :=
  { d with localParams := d.localParams ++ parts.flatMap (·.1), decls := d.decls ++ parts.flatMap (·.2.1),
           processes := d.processes.map PProcess.unsign ++ parts.flatMap (·.2.2), generates := [] }

/-- **The flat twin** of a design with module-level instances (module docstring), with the instances and their
children. -/
def hierTwin (d : PDesign) (lib : List PDesign) : Except String (PDesign × List (PInst × PDesign)) := do
  match d.others with
  | (k, t) :: _ =>
      throw s!"the module has a member outside the semantic tier (`{k}`: {t}), which the instantiation keeps as a loud process"
  | [] => pure ()
  unless d.enums.isEmpty && d.packageParams.isEmpty do
    throw "the module has enums or package parameters (v1 of the hierarchy summary reads neither)"
  let pl ← hierInsts d lib
  let parts ← pl.mapM fun x => instPart x.1 x.2
  return (twinOf d parts, pl)

/-- Where process `k` of the flat twin comes from in the design as written: one of the parent's own processes, or, per
instance in source order, the connection of one port (in the child's port order) or one of the child's processes. -/
def twinOrigin (d : PDesign) (pl : List (PInst × PDesign)) (k : Nat) : String :=
  if k < d.processes.length then s!"process #{k} of module `{d.name}`" else go pl (k - d.processes.length)
where
  go : List (PInst × PDesign) → Nat → String
    | [], _ => "a process of the twin"
    | (i, c) :: rest, k =>
        match (childPorts c)[k]? with
        | some pd => s!"instance `{i.name}`, the connection of port `{pd.name}`"
        | none =>
            let j := k - (childPorts c).length
            if j < c.processes.length then s!"instance `{i.name}`, process #{j} of module `{c.name}`"
            else go rest (j - c.processes.length)

/-- The origin of the first process of the flat twin that the site recognizer refuses (`""` when there is none, or
when the twin's declarations are refused first): for the refusal, whose site names are the twin's. -/
def twinRefusedOrigin (d : PDesign) (lib : List PDesign) : String :=
  match hierTwin d lib with
  | .error _ => ""
  | .ok (dF, pl) =>
      match declsOf? dF.decls with
      | .error _ => ""
      | .ok ds =>
          match (dF.processes.zipIdx.find? fun (p, k) => (siteOf? ds k p).toOption.isNone) with
          | some (_, k) => twinOrigin d pl k
          | none => ""

/-- (Refusal text only; no theorem reads it.) What the tactics' refusal of a design with module instances adds about the
markers below them (`PDesign.wallNote`): the parent's, or else the first instantiated child module's that has one, the
module named. -/
def hierWallNote (d : PDesign) (lib : List PDesign) : String :=
  let n := d.wallNote
  if !n.isEmpty then n
  else
    let kids := lib.filter fun c => d.generates.any fun it => match it with
      | .inst i => i.module == c.name
      | _ => false
    (kids.findSome? fun c =>
      let m := c.wallNoteIn s!"in module `{c.name}`: "
      if m.isEmpty then none else some m).getD ""

/-- **The hierarchy summary**: the summary of the flat twin (module docstring). -/
def summaryH (d : PDesign) (lib : List PDesign) : Except String Summary := do
  let (dF, _) ← hierTwin d lib
  dF.summary

/-! ## What a successful twin construction says -/

/-- Two lists related elementwise. -/
def Rel2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: r => R a b ∧ Rel2 R l r
  | _, _ => False

theorem mapM_rel2 {α β : Type} {f : α → Except String β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → Rel2 (fun a b => f a = .ok b) l r
  | [], r, h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; trivial
  | a :: l, r, h => by
      simp only [List.mapM_cons] at h
      rcases ha : f a with e | b
      · simp [ha, bind, Except.bind] at h
      · rcases hl : l.mapM f with e | bs
        · simp [ha, hl, bind, Except.bind, Functor.map, Except.map] at h
        · simp only [ha, hl, bind, Except.bind, Functor.map, Except.map, pure, Except.pure,
            Except.ok.injEq] at h
          subst h
          exact ⟨ha, mapM_rel2 hl⟩

theorem Rel2.length {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {r : List β}, Rel2 R l r → l.length = r.length
  | [], [], _ => rfl
  | _ :: l, _ :: r, h => by simp [Rel2.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Rel2.mem {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {r : List β}, Rel2 R l r →
    ∀ b ∈ r, ∃ a ∈ l, R a b
  | [], [], _, b, hb => by simp at hb
  | a :: l, b' :: r, h, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hm
      · exact ⟨a, List.mem_cons_self .., h.1⟩
      · obtain ⟨a', ha', hr⟩ := Rel2.mem h.2 b hm
        exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

theorem hierTwin_ok {d : PDesign} {lib : List PDesign} {dF : PDesign} {pl : List (PInst × PDesign)}
    (h : hierTwin d lib = .ok (dF, pl)) :
    d.others = [] ∧ hierInsts d lib = .ok pl ∧
      ∃ parts, pl.mapM (fun x => instPart x.1 x.2) = .ok parts ∧ dF = twinOf d parts := by
  unfold hierTwin at h
  rcases ho : d.others with _ | ⟨⟨k, t⟩, rest⟩
  · simp only [ho] at h
    by_cases h0 : (d.enums.isEmpty && d.packageParams.isEmpty) = true
    · simp only [h0, Bool.not_true, Bool.false_eq_true, if_false] at h
      rcases hi : hierInsts d lib with e | pl'
      · simp [hi, bind, Except.bind, pure, Except.pure] at h
      · rcases hp : pl'.mapM (fun x => instPart x.1 x.2) with e | parts
        · simp [hi, hp, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
        · simp only [hi, hp, bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, rfl, parts, hp, rfl⟩
    · simp [h0, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  · simp [ho, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem hierInsts_ok {d : PDesign} {lib : List PDesign} {pl : List (PInst × PDesign)}
    (h : hierInsts d lib = .ok pl) :
    d.generates = pl.map (fun x => GenItem.inst x.1) ∧
      ∀ x ∈ pl, x.1.path = [] ∧ lib.find? (·.name == x.1.module) = some x.2 := by
  unfold hierInsts at h
  have h2 := mapM_rel2 h
  clear h
  generalize d.generates = gs at h2 ⊢
  induction gs generalizing pl with
  | nil =>
      cases pl with
      | nil => exact ⟨rfl, by simp⟩
      | cons _ _ => exact h2.elim
  | cons it its ih =>
      cases pl with
      | nil => exact h2.elim
      | cons x xs =>
          obtain ⟨hx, hr⟩ := h2
          obtain ⟨ih1, ih2⟩ := ih hr
          cases it with
          | inst i =>
              by_cases hp : i.path.isEmpty = true
              · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at hx
                rcases hf : lib.find? (·.name == i.module) with _ | c
                · simp [hf] at hx
                · simp only [hf, Except.ok.injEq] at hx
                  subst hx
                  refine ⟨by simp [ih1], ?_⟩
                  intro y hy
                  rcases List.mem_cons.mp hy with rfl | hm
                  · exact ⟨by simpa using hp, hf⟩
                  · exact ih2 y hm
              · simp [hp] at hx
          | _ => simp at hx

theorem instPart_ok {i : PInst} {c : PDesign} {part : List PLocalParam × List PDecl × List PProcess}
    (h : instPart i c = .ok part) :
    childCheck i c = .ok () ∧ ∃ plps conns, childParamLps i c = .ok plps ∧
      (childPorts c).mapM (connPP i) = .ok conns ∧
      part = (plps ++ c.localParams.map (PLocalParam.hren (hpfx i)), c.decls.map (PDecl.hren (hpfx i)),
        conns ++ c.processes.map (PProcess.hren (hpfx i))) := by
  unfold instPart at h
  rcases hc : childCheck i c with e | ⟨⟩
  · simp [hc, bind, Except.bind] at h
  rcases hl : childParamLps i c with e | plps
  · simp [hc, hl, bind, Except.bind] at h
  rcases hm : (childPorts c).mapM (connPP i) with e | conns
  · simp [hc, hl, hm, bind, Except.bind] at h
  simp only [hc, hl, hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  exact ⟨rfl, plps, conns, rfl, rfl, h.symm⟩

theorem childCheck_ok {i : PInst} {c : PDesign} (h : childCheck i c = .ok ()) :
    c.generates = [] ∧ (∀ cn ∈ i.conns, (childPorts c).any (·.name == cn.port) = true) ∧
      ∃ sc, c.summary = .ok sc := by
  unfold childCheck at h
  by_cases h1 : c.generates.isEmpty = true
  · simp only [h1, Bool.not_true, Bool.false_eq_true, if_false] at h
    rcases ho : c.others with _ | ⟨⟨k, t⟩, rest⟩
    · simp only [ho] at h
      by_cases h2 : (c.enums.isEmpty && c.packageParams.isEmpty) = true
      · simp only [h2, Bool.not_true, Bool.false_eq_true, if_false] at h
        rcases h3 : i.params.find? (fun (n, _) => !c.params.any (·.name == n)) with _ | ⟨n, e⟩
        · rcases h4 : i.conns.find? (fun cn => !(childPorts c).any (·.name == cn.port)) with _ | cn
          · rcases h5 : c.summary with e | sc
            · simp [h3, h4, h5, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
            · refine ⟨by simpa using h1, ?_, sc, rfl⟩
              intro cn hcn
              have := List.find?_eq_none.mp h4 cn hcn
              simpa using this
          · simp [h3, h4, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
        · simp [h3, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      · simp [h2, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simp [ho, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simp [h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

theorem connPP_ok {i : PInst} {pd : PDecl} {p : PProcess} (h : connPP i pd = .ok p) :
    (pd.isInput = true ∧ pd.isOutput = false ∧ ∃ q e net,
        i.conns.find? (·.port == pd.name) = some (.input q (some e) net) ∧
          p = .assign (hpfx i ++ pd.name) e.unsign) ∨
    (pd.isOutput = true ∧ pd.isInput = false ∧ ∃ q t,
        i.conns.find? (·.port == pd.name) = some (.output q (some t)) ∧
        p = .assignL t (.ident (hpfx i ++ pd.name))) := by
  unfold connPP at h
  split at h
  · simp at h
  · simp at h
  · rename_i q e net hf
    by_cases hi : (pd.isInput && !pd.isOutput) = true
    · simp only [hi, if_true, Except.ok.injEq] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
      exact Or.inl ⟨hi.1, hi.2, q, e, net, hf, h.symm⟩
    · simp [hi] at h
  · simp at h
  · rename_i q t hf
    by_cases ho : (pd.isOutput && !pd.isInput) = true
    · simp only [ho, if_true, Except.ok.injEq] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at ho
      exact Or.inr ⟨ho.1, ho.2, q, t, hf, h.symm⟩
    · simp [ho] at h
  · simp at h

/-! ## The checks the tactics decide on the twin's summary -/

/-- The parent's constants: its parameters, then its localparams. -/
def parentNames (d : PDesign) : List String := d.params.map (·.name) ++ d.localParams.map (·.name)

/-- A child's constants (`Summary.params` of its summary). -/
def childNames (c : PDesign) : List String := c.params.map (·.name) ++ c.localParams.map (·.name)

/-- The parent alone, as a summary of its declarations: the context of its processes and of the port connections
in the hierarchical instantiation, where only the parent's own declarations are in scope. -/
def parentSum (d : PDesign) (dsP : List DeclT) : Summary :=
  { params := parentNames d, decls := dsP, statics := [], fams := [] }

/-- An access of a declaration of `ds`, with indices over the constants `ns`. -/
def AccIn (ds : List DeclT) (ns : List String) (a : Acc) : Prop :=
  a.name ∈ ds.map (·.name) ∧ ∀ x ∈ a.affs, ∀ n ∈ x.names, n ∈ ns

instance (ds : List DeclT) (ns : List String) (a : Acc) : Decidable (AccIn ds ns a) := by
  unfold AccIn; infer_instance

/-- A twin site of one of the parent's processes reads the parent's scope only. -/
def ParentSiteOk (ds : List DeclT) (ns : List String) (st : TSite) : Prop :=
  (∀ a ∈ st.tgt :: st.rds, AccIn ds ns a) ∧ ∀ n ∈ st.cnames, n ∈ ns

instance (ds : List DeclT) (ns : List String) (st : TSite) : Decidable (ParentSiteOk ds ns st) := by
  unfold ParentSiteOk; infer_instance

/-- A twin site of a port connection: an input's actual reads the parent's scope and its skeleton is as wide as its
context (`Sk.exactW`, so the connection takes `connProcs`'s assignment branch); an output's target is in the parent's
scope and it reads the whole port. -/
def ConnSiteOk (ds : List DeclT) (ns : List String) (st : TSite) : Prop :=
  match st.proc with
  | .assign _ e => (∀ a ∈ st.rds, AccIn ds ns a) ∧ (∀ n ∈ st.cnames, n ∈ ns) ∧ (skRhs e st.rds).exactW = true
  | .assignL _ (.ident n) => AccIn ds ns st.tgt ∧ st.rds = [.whole n]
  | _ => False

instance (ds : List DeclT) (ns : List String) (st : TSite) : Decidable (ConnSiteOk ds ns st) := by
  unfold ConnSiteOk; split <;> infer_instance

/-- A twin site of a child's process is the child's own site renamed under the prefix (target, reads, replication
counts and skeleton), and the child's site reads the child's scope. -/
def ChildSiteOk (pfx : String) (sc : Summary) (stF stC : TSite) : Prop :=
  stF.tgt = stC.tgt.hren pfx ∧ stF.rds = stC.rds.map (Acc.hren pfx) ∧ stF.rcounts = stC.rcounts.map (Aff.hren pfx) ∧
  skRhs (rhsOf stF.proc) stF.rds = (skRhs (rhsOf stC.proc) stC.rds).hren pfx ∧
  (∀ a ∈ stC.tgt :: stC.rds, AccIn sc.decls sc.params a) ∧ (∀ n ∈ stC.cnames, n ∈ sc.params) ∧
  fragOk (rhsOf stC.proc) = true

deriving instance DecidableEq for Part
deriving instance DecidableEq for Gate
deriving instance DecidableEq for Sk

instance (pfx : String) (sc : Summary) (stF stC : TSite) : Decidable (ChildSiteOk pfx sc stF stC) := by
  unfold ChildSiteOk; infer_instance

instance Rel2.decidable {α β : Type} (R : α → β → Prop) [∀ a b, Decidable (R a b)] :
    ∀ (l : List α) (r : List β), Decidable (Rel2 R l r)
  | [], [] => isTrue trivial
  | a :: l, b :: r => by unfold Rel2; have := Rel2.decidable R l r; infer_instance
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)

/-- The twin's sites of one instance: its port connections (`stsC`) and its child's processes (`stsB`). -/
def InstOk (dsP : List DeclT) (pn : List String) (i : PInst) (c : PDesign) (stsC stsB : List TSite) : Prop :=
  match c.summary with
  | .error _ => False
  | .ok sc => (∀ st ∈ stsC, ConnSiteOk dsP pn st) ∧ Rel2 (ChildSiteOk (hpfx i) sc) stsB sc.statics ∧
      ∀ dt ∈ sc.decls, ∀ n ∈ dt.affNames, n ∈ sc.params

instance (dsP : List DeclT) (pn : List String) (i : PInst) (c : PDesign) (stsC stsB : List TSite) :
    Decidable (InstOk dsP pn i c stsC stsB) := by
  unfold InstOk; split <;> infer_instance

/-- The twin's sites of the instances, segment by segment (one site per port, then one per child process). -/
def SegsOk (dsP : List DeclT) (pn : List String) : List (PInst × PDesign) → List TSite → Prop
  | [], sts => sts = []
  | x :: pl, sts =>
      InstOk dsP pn x.1 x.2 (sts.take (childPorts x.2).length)
        ((sts.drop (childPorts x.2).length).take x.2.processes.length) ∧
      SegsOk dsP pn pl (sts.drop ((childPorts x.2).length + x.2.processes.length))

instance SegsOk.decidable (dsP : List DeclT) (pn : List String) :
    ∀ (pl : List (PInst × PDesign)) (sts : List TSite), Decidable (SegsOk dsP pn pl sts)
  | [], sts => by unfold SegsOk; infer_instance
  | x :: pl, sts => by unfold SegsOk; have := SegsOk.decidable dsP pn pl; infer_instance

/-- **The decidable side condition of `instantiateHD2_twin`** on the twin's summary: the parent's declarations over
its constants, its processes' sites in its scope, and the sites of every instance (`SegsOk`). -/
def HierOk (d : PDesign) (dsP : List DeclT) (pl : List (PInst × PDesign)) (sF : Summary) : Prop :=
  (∀ dt ∈ dsP, ∀ n ∈ dt.affNames, n ∈ parentNames d) ∧
  (∀ st ∈ sF.statics.take d.processes.length, ParentSiteOk dsP (parentNames d) st) ∧
  SegsOk dsP (parentNames d) pl (sF.statics.drop d.processes.length)

instance (d : PDesign) (dsP : List DeclT) (pl : List (PInst × PDesign)) (sF : Summary) :
    Decidable (HierOk d dsP pl sF) := by
  unfold HierOk; infer_instance

/-- A child's parameter point at an instance, and its instantiation environment: the overrides evaluated in the
parent's scope (`PInst.given`), the child at that point (`PDesign.atPoint`), its parameter stage. -/
def childEnv (env : IEnv) (i : PInst) (c : PDesign) : Res (PDesign × List Int × IEnv) :=
  match i.given env c with
  | .error m => .unsupported m
  | .ok given =>
      match c.atPoint given with
      | .error m => .unsupported m
      | .ok (c', cargs) =>
          match c'.paramEnv2 cargs with
          | .ok envC => .ok (c', cargs, envC)
          | .timeout => .timeout
          | .unsupported m => .unsupported m

/-- The child's environment at an instance binds each of its constants at the twin's value of the constant's
renamed copy (a goal the tactics close as they close `hag`). -/
def ChildEnvOk (σ : String → Int) (env : IEnv) (x : PInst × PDesign) : Prop :=
  ∃ r : PDesign × List Int × IEnv, childEnv env x.1 x.2 = .ok r ∧ r.2.1.length = r.1.params.length ∧
    (childNames x.2).map (fun n => r.2.2.intVal? n) = (childNames x.2).map (fun n => some (σ (hpfx x.1 ++ n)))

/-- `ChildEnvOk` at every instance (one conjunct per instance, which the tactics split). -/
def AllChildEnvOk (σ : String → Int) (env : IEnv) : List (PInst × PDesign) → Prop
  | [] => True
  | x :: xs => ChildEnvOk σ env x ∧ AllChildEnvOk σ env xs

theorem AllChildEnvOk.mem {σ : String → Int} {env : IEnv} :
    ∀ {pl : List (PInst × PDesign)}, AllChildEnvOk σ env pl → ∀ x ∈ pl, ChildEnvOk σ env x
  | [], _, x, hx => by simp at hx
  | y :: ys, h, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hm
      · exact h.1
      · exact AllChildEnvOk.mem h.2 x hm

theorem childEnv_ok {env : IEnv} {i : PInst} {c : PDesign} {r : PDesign × List Int × IEnv}
    (h : childEnv env i c = .ok r) :
    ∃ given, i.given env c = .ok given ∧ c.atPoint given = .ok (r.1, r.2.1) ∧ r.1.paramEnv2 r.2.1 = .ok r.2.2 := by
  unfold childEnv at h
  split at h
  · simp at h
  · rename_i given hg
    split at h
    · simp at h
    · rename_i c' cargs hat
      split at h
      · rename_i envC he
        simp only [Res.ok.injEq] at h
        subst h
        exact ⟨given, hg, hat, he⟩
      · simp at h
      · simp at h

theorem atPoint_shape {c c' : PDesign} {given : List (Option Int)} {cargs : List Int}
    (h : c.atPoint given = .ok (c', cargs)) : ∃ ps, c' = { c with params := ps } := by
  unfold PDesign.atPoint at h
  simp only [bind, Except.bind] at h
  split at h <;> try (simp at h; done)
  split at h <;> try (simp at h; done)
  split at h <;> try (simp at h; done)
  rename_i v _
  obtain ⟨ps, args⟩ := v
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨ps, h.1.symm⟩

/-! ## The child's one-driver rule, from the twin's -/

theorem drvWins_acc_rename (σ : String → Int) (f : String → String) (a : Acc) :
    ((a.lhs σ).rename f).drvWins = (a.lhs σ).drvWins.map (fun w => (f w.1, w.2)) := by
  cases a <;> simp [Acc.lhs, Lhs2.rename, Lhs2.drvWins]

theorem flatMap_sublist {α β : Type} {f g : α → List β} (h : ∀ x, (f x).Sublist (g x)) :
    ∀ l : List α, (l.flatMap f).Sublist (l.flatMap g)
  | [] => List.Sublist.slnil
  | x :: xs => by simp only [List.flatMap_cons]; exact (h x).append (flatMap_sublist h xs)

theorem DrvWin.overlaps_ren (f : String → String) {a b : DrvWin} (h : a.overlaps b = true) :
    DrvWin.overlaps (f a.1, a.2) (f b.1, b.2) = true := by
  obtain ⟨n, x⟩ := a
  obtain ⟨m, y⟩ := b
  simp only [DrvWin.overlaps, Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨by rw [h.1], h.2⟩

/-- **A child's one-driver rule** (`childInstOf`'s `PDesign.driverGuard`): its processes are continuous assignments
to access targets whose renamed copies, after the instance's port connections `cs`, have pairwise disjoint driver
windows (a stretch of the twin's flattened design, which has them: `driversOk_of_combDesign`), and every input port
of the child is driven whole by one of `cs`. -/
theorem child_driversOk {names inputs : List String} {pfx : String} {σ : String → Int}
    {ps cs : List Process2} (hps : ∀ p ∈ ps, ∃ (a : Acc) (e : Expr2), p = .assign (a.lhs σ) e)
    (hcin : ∀ n ∈ inputs, (pfx ++ n, (none : Option (Nat × Nat))) ∈ cs.flatMap Process2.drvWins)
    (hD : ((cs ++ ps.map (Process2.rename (pfx ++ ·) id)).flatMap Process2.drvWins).Pairwise
      (fun a b => a.overlaps b = false)) :
    driversOk names inputs ps = true := by
  have hren : (ps.map (Process2.rename (pfx ++ ·) id)).flatMap Process2.drvWins =
      (ps.flatMap Process2.drvWins).map (fun w => (pfx ++ w.1, w.2)) := by
    rw [List.flatMap_map, List.map_flatMap]
    apply CombView.flatMap_congr'
    intro p hp
    obtain ⟨a, e, rfl⟩ := hps p hp
    simp [Process2.rename, Process2.drvWins, drvWins_acc_rename]
  rw [List.flatMap_append, hren, List.pairwise_append] at hD
  obtain ⟨-, hR, hX⟩ := hD
  rw [List.pairwise_map] at hR
  have hsub : (driverWins names ps).Sublist (ps.flatMap Process2.drvWins) := by
    unfold driverWins
    exact flatMap_sublist (fun p => List.filter_sublist) ps
  have hpw : ps.flatMap Process2.procWrites = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro p hp
    obtain ⟨a, e, rfl⟩ := hps p hp
    rfl
  apply driversOk_of_continuous hpw
  · refine (hR.imp ?_).sublist hsub
    intro a b h
    rw [Bool.eq_false_iff]
    intro hab
    have := DrvWin.overlaps_ren (pfx ++ ·) hab
    rw [h] at this
    exact Bool.false_ne_true this
  · intro w hw
    rw [Bool.eq_false_iff]
    intro hin
    have hc := hcin w.1 (by simpa using hin)
    have hw' : (pfx ++ w.1, w.2) ∈ (ps.flatMap Process2.drvWins).map (fun w => (pfx ++ w.1, w.2)) :=
      List.mem_map.mpr ⟨w, hsub.subset hw, rfl⟩
    have := hX _ hc _ hw'
    simp [DrvWin.overlaps] at this

/-- The clock-source rule changes nothing on a design of continuous assignments. -/
theorem clockGuard_of_noClock {clocks : List String} {i : PInst} {m : Design2}
    (h : ∀ p ∈ m.processes.toList, p.clock? = none) : m.clockGuard clocks i = m := by
  unfold Design2.clockGuard
  have : m.processes.map (clockGuardProc clocks i m) = m.processes := by
    apply Array.ext'
    rw [Array.toList_map]
    conv => rhs; rw [← List.map_id m.processes.toList]
    apply List.map_congr_left
    intro p hp
    simp [clockGuardProc, h p hp]
  rw [this]

/-- The facts the twin's obligations give at each of its sites (all module-level: the twin has no generate loop). -/
structure TwinFacts (sF : Summary) (σF : String → Int) : Prop where
  acc : ∀ st ∈ sF.statics, ∀ a ∈ st.tgt :: st.rds, AccOK σF (sF.DW σF) (sF.DG σF) (sF.EW σF) sF.params a
  cn : ∀ st ∈ sF.statics, st.ConstOK σF sF.params
  frag : ∀ st ∈ sF.statics, fragOk (rhsOf st.proc) = true
  wid : ∀ st ∈ sF.statics,
    (skRhs (rhsOf st.proc) st.rds).WidthOkC σF (sF.dw σF) (st.tgt.win σF (sF.dw σF)).2.2
  site : ∀ st ∈ sF.statics, ∃ pos, siteOf? sF.decls pos st.proc = .ok st

theorem accGeom_congr {σ : String → Int} {DG DG' : String → Option (List (Int × Int))}
    {EW EW' : String → Option Nat} {a : Acc} (h : AccGeom σ DG EW a) (hDG : DG a.name = DG' a.name)
    (hEW : EW a.name = EW' a.name) : AccGeom σ DG' EW' a := by
  cases a <;> simp_all [AccGeom, Acc.name]

/-- The access facts of a site in the parent's scope, from the twin's (the parent's declarations come first in the
twin's, so a parent name finds the same declaration in both). -/
theorem accOK_parent {d : PDesign} {dsP : List DeclT} {sF : Summary} {σF : String → Int}
    (hPF : ∀ n ∈ dsP.map (·.name), findDecl dsP n = findDecl sF.decls n) {a : Acc}
    (h : AccOK σF (sF.DW σF) (sF.DG σF) (sF.EW σF) sF.params a) (hin : AccIn dsP (parentNames d) a) :
    AccOK σF ((parentSum d dsP).DW σF) ((parentSum d dsP).DG σF) ((parentSum d dsP).EW σF) (parentNames d) a := by
  have hf : (parentSum d dsP).find a.name = sF.find a.name := hPF a.name hin.1
  refine ⟨?_, accGeom_congr h.2.1 ?_ ?_, hin.2⟩
  · simp only [Summary.DW, hf]; exact h.1
  · simp [Summary.DG, hf]
  · simp [Summary.EW, hf]

theorem rel2_and_map {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {r : List β}, Rel2 R l r → l.map f = r.map g → Rel2 (fun a b => R a b ∧ f a = g b) l r
  | [], [], _, _ => trivial
  | _ :: l, _ :: r, h, he => by
      simp only [List.map_cons, List.cons.injEq] at he
      exact ⟨⟨h.1, he.1⟩, rel2_and_map h.2 he.2⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem rel2_of_map {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {r : List β}, r.map g = l.map f → Rel2 (fun a b => g b = f a) l r
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      exact ⟨h.1, rel2_of_map h.2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem rel2_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {r : List β}, Rel2 R l r → (∀ a ∈ l, ∀ b ∈ r, R a b → f a = g b) → l.map f = r.map g
  | [], [], _, _ => rfl
  | a :: l, b :: r, h, he => by
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨he a (List.mem_cons_self ..) b (List.mem_cons_self ..) h.1,
        rel2_map_eq h.2 fun a' ha' b' hb' => he a' (List.mem_cons_of_mem _ ha') b' (List.mem_cons_of_mem _ hb')⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem rel2_mem {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {r : List β}, Rel2 R l r →
    ∀ a ∈ l, ∃ b ∈ r, R a b
  | [], [], _, a, ha => by simp at ha
  | a' :: l, b :: r, h, a, ha => by
      rcases List.mem_cons.mp ha with rfl | hm
      · exact ⟨b, List.mem_cons_self .., h.1⟩
      · obtain ⟨b', hb', hr⟩ := rel2_mem h.2 a hm
        exact ⟨b', List.mem_cons_of_mem _ hb', hr⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

theorem declsOf?_rel2 : ∀ {l : List PDecl} {s : List DeclT}, declsOf? l = .ok s →
    Rel2 (fun pd dt => declOf? pd = .ok dt) l s
  | [], s, h => by simp only [declsOf?, Except.ok.injEq] at h; subst h; trivial
  | pd :: rest, s, h => by
      obtain ⟨dt, s', hd, hr, rfl⟩ := declsOf?_cons h
      exact ⟨hd, declsOf?_rel2 hr⟩

theorem rel2_filter {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l : List α} {r : List β}, Rel2 R l r → Rel2 R (l.filter p) (r.filter q)
  | [], [], _ => trivial
  | a :: l, b :: r, h => by
      simp only [List.filter_cons, hpq a b h.1]
      split
      · exact ⟨h.1, rel2_filter hpq h.2⟩
      · exact rel2_filter hpq h.2
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem rel2_map_right {α β γ : Type} {R : α → β → Prop} {f : γ → β} :
    ∀ {l : List α} {r : List γ}, Rel2 R l (r.map f) → Rel2 (fun a c => R a (f c)) l r
  | [], [], _ => trivial
  | _ :: l, _ :: r, h => ⟨h.1, rel2_map_right h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem rel2_flatMap_eq {α β γ δ : Type} {R : α → β → Prop} {Q : α → γ → Prop} {f : β → List δ} {g : γ → δ} :
    ∀ {l : List α} {r : List β} {s : List γ}, Rel2 R l r → Rel2 Q l s →
      (∀ a ∈ l, ∀ b ∈ r, ∀ c ∈ s, R a b → Q a c → f b = [g c]) → r.flatMap f = s.map g
  | [], [], [], _, _, _ => rfl
  | a :: l, b :: r, c :: s, h1, h2, he => by
      simp only [List.flatMap_cons, List.map_cons]
      rw [he a (List.mem_cons_self ..) b (List.mem_cons_self ..) c (List.mem_cons_self ..) h1.1 h2.1,
        rel2_flatMap_eq h1.2 h2.2 fun a' ha' b' hb' c' hc' => he a' (List.mem_cons_of_mem _ ha') b'
          (List.mem_cons_of_mem _ hb') c' (List.mem_cons_of_mem _ hc')]
      rfl
  | [], [], _ :: _, _, h, _ => h.elim
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, h, _ => h.elim

/-- A child's declaration, renamed, is the twin's declaration of the renamed name (the twin's names are distinct). -/
theorem find_hren {sc sF : Summary} {pfx : String} (hnodup : (sF.decls.map (·.name)).Nodup)
    (hmemD : ∀ dt ∈ sc.decls, dt.hren pfx ∈ sF.decls) {n : String} {dt : DeclT} (h : sc.find n = some dt) :
    sF.find (pfx ++ n) = some (dt.hren pfx) := by
  have hdmem : dt ∈ sc.decls := List.mem_of_find?_eq_some h
  have hdn : dt.name = n := by have := List.find?_some h; simpa using this
  have := findDecl_of_mem hnodup (hmemD dt hdmem)
  rw [DeclT.name_hren, hdn] at this
  exact this

/-- **One module-level instance**: the hierarchical instantiation of the instance (`instExpandH`: the child at its
parameter point under its one-driver and clock-source rules, flattened under the prefix) is the twin's part of it —
the child's declarations renamed, and the twin's processes of the instance (its port connections, then the child's
processes renamed), instantiated. -/
theorem inst_step {d : PDesign} {lib : List PDesign} {sF : Summary} {dsP : List DeclT}
    {envP EF : IEnv} {elF : List (String × Nat)} {F : Nat} {σF : String → Int}
    (CP : Ctx σF (envP.withDecls (dsP.map (DeclT.toDecl σF))) (dsP.map fun dt => (dt.name, dt.elemW σF))
      ((parentSum d dsP).DW σF) ((parentSum d dsP).DG σF) ((parentSum d dsP).EW σF) (parentNames d))
    (CF : Ctx σF EF elF (sF.DW σF) (sF.DG σF) (sF.EW σF) sF.params)
    (hPF : ∀ n ∈ dsP.map (·.name), findDecl dsP n = findDecl sF.decls n)
    (hnodup : (sF.decls.map (·.name)).Nodup) (TF : TwinFacts sF σF)
    {i : PInst} {c : PDesign} {sc : Summary} (hsc : c.summary = .ok sc)
    (hmemD : ∀ dt ∈ sc.decls, dt.hren (hpfx i) ∈ sF.decls)
    (hpath : i.path = []) (hfind : lib.find? (·.name == i.module) = some c)
    {part : List PLocalParam × List PDecl × List PProcess} (hpart : instPart i c = .ok part)
    (hce : ChildEnvOk σF (envP.withDecls (dsP.map (DeclT.toDecl σF))) (i, c))
    {S : List TSite} (hS : S.map TSite.proc = part.2.2) (hSF : ∀ st ∈ S, st ∈ sF.statics)
    (hok : InstOk dsP (parentNames d) i c (S.take (childPorts c).length)
      ((S.drop (childPorts c).length).take c.processes.length))
    (hD : ((S.map fun st => instProcess2 EF elF st.proc).flatMap Process2.drvWins).Pairwise
      (fun a b => a.overlaps b = false)) :
    instExpandH (PDesign.childRec lib.length lib { int32 := true } F (Decl.inputNames (dsP.map (DeclT.toDecl σF))))
      (envP.withDecls (dsP.map (DeclT.toDecl σF))) (dsP.map fun dt => (dt.name, dt.elemW σF)) i =
      .ok ((sc.decls.map (DeclT.hren (hpfx i))).map (DeclT.toDecl σF),
        S.map fun st => instProcess2 EF elF st.proc) := by
  -- the instance's part of the twin, and the child's summary
  obtain ⟨hcc, plps, conns, -, hconns, rfl⟩ := instPart_ok hpart
  obtain ⟨hcgen, hstray, -⟩ := childCheck_ok hcc
  obtain ⟨hloc, -, hothC, hparC, hsdC, hstsC, -, -⟩ := summary_spec hsc
  obtain ⟨hprocC, hsitesC⟩ := sitesOf?_spec hstsC
  simp only [InstOk, hsc] at hok
  obtain ⟨hcon, hrel, hdeclC⟩ := hok
  have hrc := mapM_rel2 hconns
  obtain ⟨SC, SB, rfl, hSC, hSB⟩ := List.map_eq_append_iff.mp hS
  have hlSC : SC.length = (childPorts c).length := by rw [hrc.length, ← hSC, List.length_map]
  have hlSB : SB.length = c.processes.length := by
    have := congrArg List.length hSB
    simpa using this
  rw [List.take_left' hlSC] at hcon
  rw [List.drop_left' hlSC, List.take_of_length_le (by omega)] at hrel
  have hSCF : ∀ st ∈ SC, st ∈ sF.statics := fun st h => hSF st (List.mem_append_left _ h)
  have hSBF : ∀ st ∈ SB, st ∈ sF.statics := fun st h => hSF st (List.mem_append_right _ h)
  -- the child at its parameter point
  obtain ⟨⟨c', cargs, envC⟩, hce1, hce2, hce3⟩ := hce
  obtain ⟨given, hg, hat, h1C⟩ := childEnv_ok hce1
  simp only at hat h1C hce2 hce3
  obtain ⟨ps, rfl⟩ := atPoint_shape hat
  have hscp : sc.params = childNames c := by rw [hparC, hloc]; rfl
  have hagC : Agrees (fun n => σF (hpfx i ++ n)) envC sc.params := by rw [hscp]; exact Agrees_of_map hce3
  have hagdC : ∀ dt ∈ sc.decls, ∀ n ∈ dt.affNames, envC.intVal? n = some (σF (hpfx i ++ n)) :=
    fun dt hdt n hn => hagC n (hdeclC dt hdt n hn)
  have h2C : buildDecls envC ({ c with params := ps } : PDesign).decls =
      .ok (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n))) :=
    buildDecls_summary c.decls sc.decls hsdC envC hagdC
  have h3C : buildElems envC ({ c with params := ps } : PDesign).decls =
      .ok (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) :=
    buildElems_summary c.decls sc.decls hsdC envC hagdC
  have CC := ctx_of_env (s := sc) (d := { c with params := ps }) hsdC (paramEnv2_dims h1C) hagC hdeclC
  have hMC := PDesign.instantiate2_of_ok (F := F) hce2 h1C h2C h3C (gens := [])
    (by show expandList2 _ _ F c.generates = _; rw [hcgen]; exact expandList2_nil)
  -- the declarations of the child, against the twin's
  have hdwC : ∀ n, (sc.DW (fun n => σF (hpfx i ++ n)) n).isSome = true →
      sc.DW (fun n => σF (hpfx i ++ n)) n = some (sF.dw σF (hpfx i ++ n)) := by
    intro n hn
    obtain ⟨dt, hdt⟩ := Option.isSome_iff_exists.mp
      (show (sc.find n).isSome = true by simpa [Summary.DW] using hn)
    have hF := find_hren hnodup hmemD hdt
    simp [Summary.DW, Summary.dw, hdt, hF]
  have hdwP : ∀ n, ((parentSum d dsP).DW σF n).isSome = true →
      (parentSum d dsP).DW σF n = some (sF.dw σF n) := by
    intro n hn
    obtain ⟨dt, hdt⟩ := Option.isSome_iff_exists.mp
      (show ((parentSum d dsP).find n).isSome = true by simpa [Summary.DW] using hn)
    have hmem : n ∈ dsP.map (·.name) := by
      have h1 : dt ∈ dsP := List.mem_of_find?_eq_some hdt
      have h2 : dt.name = n := by have := List.find?_some hdt; simpa using this
      exact List.mem_map.mpr ⟨dt, h1, h2⟩
    have hF : sF.find n = some dt := by
      show findDecl sF.decls n = some dt
      rw [← hPF n hmem]; exact hdt
    simp [Summary.DW, Summary.dw, hdt, hF]
  have hdwF : ∀ n, (sF.DW σF n).isSome = true → sF.DW σF n = some (sF.dw σF n) := fun n h => dw_some n h
  have hdwn : ∀ dt ∈ sc.decls, sF.dw σF (hpfx i ++ dt.name) = dt.width (fun n => σF (hpfx i ++ n)) := by
    intro dt hdt
    have hF : sF.find (hpfx i ++ dt.name) = some (dt.hren (hpfx i)) := by
      have := findDecl_of_mem hnodup (hmemD dt hdt)
      rwa [DeclT.name_hren] at this
    simp [Summary.dw, hF]
  -- the child's processes, pair by pair with the twin's
  have hrel' := rel2_and_map (f := TSite.proc) (g := fun st => st.proc.hren (hpfx i)) hrel
    (by rw [hSB, ← hprocC, List.map_map]; rfl)
  have hchild : ∀ stF ∈ SB, ∀ stC ∈ sc.statics,
      (ChildSiteOk (hpfx i) sc stF stC ∧ stF.proc = stC.proc.hren (hpfx i)) →
      ∃ e, instProcess2 (envC.withDecls (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n))))
          (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) stC.proc =
          .assign (stC.tgt.lhs (fun n => σF (hpfx i ++ n))) e ∧
        instProcess2 EF elF stF.proc =
          .assign ((stC.tgt.lhs (fun n => σF (hpfx i ++ n))).rename (hpfx i ++ ·)) (e.rename (hpfx i ++ ·)) := by
    rintro stF hF stC hC ⟨⟨htg, hrds, hrcs, hsk, hacc, hcn, hfr⟩, hpr⟩
    have hFS := hSBF stF hF
    obtain ⟨posF, hsF⟩ := TF.site stF hFS
    rw [hpr] at hsF
    obtain ⟨posC, pC, hsC⟩ := hsitesC stC hC
    have hpC : stC.proc = pC := siteOf?_proc hsC
    rw [← hpC] at hsC
    have hsk' : skRhs (rhsOf (stC.proc.hren (hpfx i))) stF.rds =
        (skRhs (rhsOf stC.proc) stC.rds).hren (hpfx i) := by rw [← hpr]; exact hsk
    have hsoC : ∀ a ∈ stC.tgt :: stC.rds, AccOK (fun n => σF (hpfx i ++ n))
        (sc.DW fun n => σF (hpfx i ++ n)) (sc.DG fun n => σF (hpfx i ++ n))
        (sc.EW fun n => σF (hpfx i ++ n)) sc.params a := by
      intro a ha
      obtain ⟨hain, hans⟩ := hacc a ha
      obtain ⟨dt, hdt⟩ := Option.isSome_iff_exists.mp (find_isSome_of_mem (s := sc) hain)
      have hF' := find_hren hnodup hmemD hdt
      have haF : a.hren (hpfx i) ∈ stF.tgt :: stF.rds := by
        rcases List.mem_cons.mp ha with rfl | hm
        · rw [htg]; exact List.mem_cons_self ..
        · rw [hrds]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hm)
      have hFacc := TF.acc stF hFS _ haF
      refine ⟨by simp [Summary.DW, hdt], accGeom_of_hren hFacc.2.1 ?_ ?_, hans⟩
      · simp [Summary.DG, hF', hdt]
      · simp [Summary.EW, hF', hdt]
    have hcnC : stC.ConstOK (fun n => σF (hpfx i ++ n)) sc.params := by
      refine ⟨hcn, fun c hc => ?_⟩
      have := (TF.cn stF hFS).2 (c.hren (hpfx i)) (by rw [hrcs]; exact List.mem_map_of_mem hc)
      simpa using this
    have hfF : fragOk (rhsOf (stC.proc.hren (hpfx i))) = true := by
      have := TF.frag stF hFS; rwa [hpr] at this
    have hwF := TF.wid stF hFS
    rw [hpr] at hwF
    obtain ⟨e, he1, he2⟩ := child_proc_eq CC CF hdwC hdwF hsC hsF htg hsk' hsoC (TF.acc stF hFS) hcnC
      (TF.cn stF hFS) hfr hfF hwF
    exact ⟨e, he1, by rw [hpr]; exact he2⟩
  -- the port connections, port by port with the twin's
  have hdr := rel2_filter (p := fun pd : PDecl => pd.isInput || pd.isOutput)
    (q := fun dt : DeclT => dt.isInput || dt.isOutput)
    (fun pd dt h => by obtain ⟨-, hi, ho, -⟩ := declOf?_spec h; simp [hi, ho]) (declsOf?_rel2 hsdC)
  rw [← hSC] at hrc
  have hrcS := rel2_map_right hrc
  have hport : ∀ pd ∈ childPorts c, ∀ dt ∈ sc.decls.filter (fun dt => dt.isInput || dt.isOutput), ∀ st ∈ SC,
      declOf? pd = .ok dt → connPP i pd = .ok st.proc →
      connProcs (envP.withDecls (dsP.map (DeclT.toDecl σF))) (dsP.map fun dt => (dt.name, dt.elemW σF))
        (hpfx i) i.conns (dt.toDecl fun n => σF (hpfx i ++ n)) = [instProcess2 EF elF st.proc] := by
    intro pd _ dt hdt st hst hdo hcp
    obtain ⟨hn, hi, ho, -⟩ := declOf?_spec hdo
    have hdtm : dt ∈ sc.decls := (List.mem_filter.mp hdt).1
    have hSt := hSCF st hst
    obtain ⟨pos, hsF⟩ := TF.site st hSt
    have hcs := hcon st hst
    unfold ConnSiteOk at hcs
    have hdn : sF.dw σF (hpfx i ++ (dt.toDecl fun n => σF (hpfx i ++ n)).name) =
        (dt.toDecl fun n => σF (hpfx i ++ n)).width := hdwn dt hdtm
    rcases connPP_ok hcp with ⟨hin, -, q, e, net, hfd, hpe⟩ | ⟨hout, -, q, t, hfd, hpe⟩
    · rw [hpe] at hsF hcs
      obtain ⟨hrdin, hcnin, hex⟩ := hcs
      have hs' : siteOf? sF.decls pos (.assign (hpfx i ++ (dt.toDecl fun n => σF (hpfx i ++ n)).name) e.unsign) =
          .ok st := by simpa [DeclT.toDecl, hn] using hsF
      have htgt : st.tgt = .whole (hpfx i ++ (dt.toDecl fun n => σF (hpfx i ++ n)).name) := by
        rcases siteOf?_cases hs' with ⟨t', v, rds, hp, -, hst'⟩ | ⟨l, v, tg, rds, hp, -, -, -⟩
        · simp only [PProcess.assign.injEq] at hp
          rw [hst', ← hp.1]
        · simp at hp
      have hw : (skRhs e.unsign st.rds).WidthOkC σF (sF.dw σF) (dt.toDecl fun n => σF (hpfx i ++ n)).width := by
        have := TF.wid st hSt
        rw [hpe, htgt] at this
        simpa [rhsOf, Acc.win, hdwn dt hdtm, DeclT.toDecl] using this
      have hfd' : i.conns.find? (·.port == (dt.toDecl fun n => σF (hpfx i ++ n)).name) =
          some (.input q (some e) net) := by simpa [DeclT.toDecl, hn] using hfd
      have hfr : fragOk e.unsign = true := by have := TF.frag st hSt; rwa [hpe] at this
      rw [conn_in_eq CP CF hdwP hdwF hfd' (by simpa [DeclT.toDecl, hi] using hin) hs'
        (fun a ha => accOK_parent hPF (TF.acc st hSt a (List.mem_cons_of_mem _ ha)) (hrdin a ha))
        (TF.acc st hSt) ⟨hcnin, (TF.cn st hSt).2⟩ (TF.cn st hSt) hfr hw hex hdn, hpe]
      simp [DeclT.toDecl, hn]
    · rw [hpe] at hsF hcs
      obtain ⟨htin, hrds⟩ := hcs
      have hs' : siteOf? sF.decls pos (.assignL t (.ident (hpfx i ++ (dt.toDecl fun n => σF (hpfx i ++ n)).name))) =
          .ok st := by simpa [DeclT.toDecl, hn] using hsF
      have hfd' : i.conns.find? (·.port == (dt.toDecl fun n => σF (hpfx i ++ n)).name) =
          some (.output q (some t)) := by simpa [DeclT.toDecl, hn] using hfd
      have hw := TF.wid st hSt
      rw [hpe] at hw
      rw [conn_out_eq CP CF hdwP hdwF hfd' (by simpa [DeclT.toDecl, ho] using hout) hs'
        (by simpa [DeclT.toDecl, hn] using hrds) (accOK_parent hPF (TF.acc st hSt _ (List.mem_cons_self ..)) htin)
        (TF.acc st hSt) (TF.cn st hSt) (by simpa [rhsOf, DeclT.toDecl, hn] using hw) hdn, hpe]
      simp [DeclT.toDecl, hn]
  -- the child's instantiation, under its one-driver and clock-source rules
  have hMCp : (({ c with params := ps } : PDesign).assemble2 envC
      (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
      (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) []).processes.toList =
      sc.statics.map (fun st => instProcess2 (envC.withDecls (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n))))
        (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) st.proc) := by
    rw [PDesign.assemble2_processes]
    simp [hothC, ← hprocC]
  have hbodyEq : ∀ (h : Process2 → Process2), (∀ t e, h (.assign t e) = .assign (t.rename (hpfx i ++ ·))
      (e.rename (hpfx i ++ ·))) →
      (({ c with params := ps } : PDesign).assemble2 envC
        (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
        (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) []).processes.toList.map h =
      SB.map fun st => instProcess2 EF elF st.proc := by
    intro h hh
    rw [hMCp, List.map_map]
    symm
    apply rel2_map_eq hrel'
    intro stF hF stC hC hp
    obtain ⟨e, h1, h2⟩ := hchild stF hF stC hC hp
    simp only [Function.comp_apply, h1, hh, h2]
  have hps : ∀ p ∈ (({ c with params := ps } : PDesign).assemble2 envC
      (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
      (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) []).processes.toList,
      ∃ (a : Acc) (e : Expr2), p = .assign (a.lhs fun n => σF (hpfx i ++ n)) e := by
    rw [hMCp]
    intro p hp
    obtain ⟨stC, hC, rfl⟩ := List.mem_map.mp hp
    obtain ⟨stF, hF, hpr⟩ := Rel2.mem hrel' stC hC
    obtain ⟨e, h1, -⟩ := hchild stF hF stC hC hpr
    exact ⟨stC.tgt, e, h1⟩
  have hdrv : driversOk ({ c with params := ps } : PDesign).declNames ({ c with params := ps } : PDesign).inputNames
      (({ c with params := ps } : PDesign).assemble2 envC
        (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
        (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) []).processes.toList = true := by
    apply child_driversOk (pfx := hpfx i) (cs := SC.map fun st => instProcess2 EF elF st.proc) hps
    · intro n hn
      simp only [PDesign.inputNames, List.mem_map, List.mem_filter] at hn
      obtain ⟨pd, ⟨hpdm, hpdi⟩, rfl⟩ := hn
      have hpdp : pd ∈ childPorts c := List.mem_filter.mpr ⟨hpdm, by simp [hpdi]⟩
      obtain ⟨st, hst, hcp⟩ := rel2_mem hrcS pd hpdp
      obtain ⟨dt, hdt, hdo⟩ := rel2_mem hdr pd hpdp
      obtain ⟨hn', -, -, -⟩ := declOf?_spec hdo
      have hdtm : dt ∈ sc.decls := (List.mem_filter.mp hdt).1
      rcases connPP_ok hcp with ⟨-, -, q, e, net, -, hpe⟩ | ⟨-, hin', -⟩
      · have hF : sF.find (hpfx i ++ pd.name) = some (dt.hren (hpfx i)) := by
          have := findDecl_of_mem hnodup (hmemD dt hdtm)
          rwa [DeclT.name_hren, hn'] at this
        have hW : EF.widths.lookup (hpfx i ++ pd.name) = some (sF.dw σF (hpfx i ++ pd.name)) := by
          rw [CF.widths]; exact dw_some _ (by simp [Summary.DW, hF])
        refine List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hst, ?_⟩
        simp [hpe, instProcess2, hW, Process2.drvWins, Lhs2.drvWins]
      · rw [hpdi] at hin'; cases hin'
    · rw [hbodyEq (Process2.rename (hpfx i ++ ·) id) (fun t e => rfl), ← List.map_append]
      exact hD
  have hguard : (PDesign.driverGuard ({ c with params := ps } : PDesign) (({ c with params := ps } : PDesign).assemble2
      envC (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
      (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) [])).clockGuard
        (Decl.inputNames (dsP.map (DeclT.toDecl σF))) i =
      ({ c with params := ps } : PDesign).assemble2 envC (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
        (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) [] := by
    rw [PDesign.driverGuard, Design2.driverGuard_of_ok hdrv]
    apply clockGuard_of_noClock
    intro p hp
    obtain ⟨a, e, rfl⟩ := hps p hp
    rfl
  -- the child instantiator, and the prefix
  have hcb : PDesign.childRec lib.length lib { int32 := true } F (Decl.inputNames (dsP.map (DeclT.toDecl σF)))
      (envP.withDecls (dsP.map (DeclT.toDecl σF))) i =
      .ok (({ c with params := ps } : PDesign).assemble2 envC (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
        (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) []) := by
    obtain ⟨k, hk⟩ : ∃ k, lib.length = k + 1 :=
      ⟨lib.length - 1, by have := List.length_pos_of_mem (List.mem_of_find?_eq_some hfind); omega⟩
    have hflat := PDesign.instantiateRec_flat k lib { int32 := true } ({ c with params := ps } : PDesign) cargs F
      (by show GenItem.listInstFree c.generates = true; rw [hcgen]; rfl)
    simp only [PDesign.childRec, childInstOf, hfind, hg, hat, hk, hflat]
    show (({ c with params := ps } : PDesign).instantiate2 cargs F >>= fun cd => Res.ok _) = _
    rw [hMC]
    simp only [Res.ok_bind]
    rw [hguard]
  have hpre : i.prefix (envP.withDecls (dsP.map (DeclT.toDecl σF))) = .ok (hpfx i) := by
    simp [PInst.prefix, hpath, PInst.pathPrefix, hpfx, bind, Except.bind, pure, Except.pure]
  rw [instExpandH_of hpre hcb]
  -- the flattened instance is the twin's part
  have hnm : (childPorts c).map (·.name) = (sc.decls.filter fun dt => dt.isInput || dt.isOutput).map (·.name) :=
    rel2_map_eq hdr (fun pd _ dt _ h => (declOf?_spec h).1.symm)
  simp only [flattenInst, Res.ok.injEq, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp [PDesign.assemble2, List.map_map, Function.comp_def, DeclT.toDecl_hren]
  · have hports : ((({ c with params := ps } : PDesign).assemble2 envC
        (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
        (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) []).decls.toList.filter
          fun dc => dc.isInput || dc.isOutput) =
        (sc.decls.filter fun dt => dt.isInput || dt.isOutput).map (DeclT.toDecl fun n => σF (hpfx i ++ n)) := by
      simp [PDesign.assemble2, List.filter_map, Function.comp_def, DeclT.toDecl]
    rw [hports, hbodyEq _ (instBodyProc_assign (hpfx i) i _ _), List.flatMap_map,
      rel2_flatMap_eq hdr hrcS hport, List.map_append]
    have hstr : i.conns.filterMap (strayConn (({ c with params := ps } : PDesign).assemble2 envC
        (sc.decls.map (DeclT.toDecl fun n => σF (hpfx i ++ n)))
        (sc.decls.map fun dt => (dt.name, dt.elemW fun n => σF (hpfx i ++ n))) [])
        ((sc.decls.filter fun dt => dt.isInput || dt.isOutput).map (DeclT.toDecl fun n => σF (hpfx i ++ n)))) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro cn hcn
      have h1 := hstray cn hcn
      have h2 : ((sc.decls.filter fun dt => dt.isInput || dt.isOutput).map
          (DeclT.toDecl fun n => σF (hpfx i ++ n))).any (·.name == cn.port) = true := by
        rw [List.any_map]
        have : (childPorts c).any (fun pd => pd.name == cn.port) =
            (sc.decls.filter fun dt => dt.isInput || dt.isOutput).any (fun dt => dt.name == cn.port) := by
          have := congrArg (fun l => l.any (· == cn.port)) hnm
          simpa [List.any_map, Function.comp_def] using this
        rw [this] at h1
        simpa [Function.comp_def, DeclT.toDecl] using h1
      simp [strayConn, h2]
    rw [hstr, List.nil_append]

/-! ## The soundness theorem -/

/-- The twin's declarations of an instance: the child's, renamed (`[]` when its summary fails, which `hierTwin`
refuses). -/
def childDecls (x : PInst × PDesign) : List DeclT :=
  match x.2.summary with
  | .ok sc => sc.decls.map (DeclT.hren (hpfx x.1))
  | .error _ => []

theorem declsOf?_parts : ∀ {pl : List (PInst × PDesign)} {parts : List (List PLocalParam × List PDecl × List PProcess)},
    Rel2 (fun x part => instPart x.1 x.2 = .ok part) pl parts →
      declsOf? (parts.flatMap (·.2.1)) = .ok (pl.flatMap childDecls)
  | [], [], _ => rfl
  | x :: pl, part :: parts, h => by
      obtain ⟨hcc, plps, conns, -, -, rfl⟩ := instPart_ok h.1
      obtain ⟨-, -, sc, hsc⟩ := childCheck_ok hcc
      obtain ⟨-, -, -, -, hsd, -⟩ := summary_spec hsc
      simp only [List.flatMap_cons]
      have : childDecls x = sc.decls.map (DeclT.hren (hpfx x.1)) := by simp [childDecls, hsc]
      rw [this]
      exact declsOf?_append (declsOf?_hren _ hsd) (declsOf?_parts h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem paramEnvH_int32 (d : PDesign) (args : List Int) : d.paramEnvH { int32 := true } args = d.paramEnv2 args := rfl

/-- **The hierarchy summary is sound**: at every parameter point where the twin's obligations hold (the view's, plus
the fragment and width obligations of `sv_equations`), the decidable side condition on the twin's summary
(`HierOk`) holds, the parent's environment agrees with the twin's valuation, and every child's environment binds its
constants at the twin's values of their renamed copies (`ChildEnvOk`), the hierarchical family IS the twin's flat
family: `X.sem N` may be read through the twin. -/
theorem instantiateHD2_twin {d : PDesign} {lib : List PDesign} {args : List Int} {dF : PDesign}
    {pl : List (PInst × PDesign)} (htw : hierTwin d lib = .ok (dF, pl))
    {sF : Summary} {envF : IEnv} (hs : dF.summary = .ok sF) (harity : args.length = dF.params.length)
    (h1 : dF.paramEnv2 args = .ok envF)
    (hag : sF.params.map (fun n => envF.intVal? n) = sF.params.map (fun n => some (sF.val args n)))
    (hok : sF.StructOk) (hauto : sF.AutoObl (sF.val args) args) (hin : sF.InRangeObl (sF.val args))
    (hdisj : sF.DisjObl (sF.val args)) (hfrag : sF.EqFrag) (hwid : sF.WidthObl (sF.val args))
    {dsP : List DeclT} (hdsP : declsOf? d.decls = .ok dsP) (hck : HierOk d dsP pl sF)
    {envP : IEnv} (h1P : d.paramEnv2 args = .ok envP)
    (hagP : (parentNames d).map (fun n => envP.intVal? n) =
      (parentNames d).map (fun n => some (sF.val args n)))
    (hch : AllChildEnvOk (sF.val args) (envP.withDecls (dsP.map (DeclT.toDecl (sF.val args)))) pl) :
    d.instantiateHD2 lib args = dF.instantiateGD2 args := by
  obtain ⟨hothD, hpl, parts, hparts, rfl⟩ := hierTwin_ok htw
  obtain ⟨hgenD, hplx⟩ := hierInsts_ok hpl
  obtain ⟨hck1, hck2, hck3⟩ := hck
  obtain ⟨-, -, -, -, hsd, hsts, hgen, -⟩ := summary_spec hs
  have hfams : sF.fams = [] := by
    have : ([] : List GenItem) = sF.fams.map TFam.toGen := hgen
    exact List.map_eq_nil_iff.mp this.symm
  obtain ⟨hprocF, hsitesF⟩ := sitesOf?_spec hsts
  have hlsF : ∀ st ∈ sF.statics, (⟨[], "plain", st⟩ : LSite) ∈ sF.lsites := by
    intro st hst
    simp only [Summary.lsites, hfams, List.flatMap_nil, List.append_nil]
    exact List.mem_map.mpr ⟨st, hst, rfl⟩
  have hagF : Agrees (sF.val args) envF sF.params := Agrees_of_map hag
  have hok' := hok
  obtain ⟨hnodupF, -, -, -, -, hdeclF, -, -⟩ := hok'
  -- the twin's instantiation, its comb profile and its one-driver rule
  have hagdF : ∀ dt ∈ sF.decls, ∀ n ∈ dt.affNames, envF.intVal? n = some (sF.val args n) :=
    fun dt hdt n hn => hagF n (hdeclF dt hdt n hn)
  have h2F := buildDecls_summary (σ := sF.val args) _ _ hsd envF hagdF
  have h3F := buildElems_summary (σ := sF.val args) _ _ hsd envF hagdF
  have CF := ctx_of_env hsd (paramEnv2_dims h1) hagF hdeclF
  have hMF := PDesign.instantiate2_of_ok (F := PDesign.surfaceFuel args) harity h1 h2F h3F (gens := [])
    (by show expandList2 _ _ _ [] = _; exact expandList2_nil)
  obtain ⟨M', hM', hR⟩ := Summary.sound hs harity h1 hagF hok hauto hin
  rw [hMF] at hM'
  obtain rfl := Res.ok.inj hM'
  obtain ⟨hcMF, hposMF⟩ := realized_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_combDesign hMF hcMF hposMF]
  -- the twin's facts at each site
  have TF : TwinFacts sF (sF.val args) := by
    refine ⟨fun st hst => site_acc hok hauto hin (hlsF st hst) rfl,
      fun st hst => site_const hok hin (hlsF st hst) rfl, fun st hst => (hfrag _ (hlsF st hst)).1,
      fun st hst => hwid _ (hlsF st hst), fun st hst => ?_⟩
    obtain ⟨pos, p, h⟩ := hsitesF st hst
    exact ⟨pos, by rw [siteOf?_proc h]; exact h⟩
  -- the parent's environment
  have hagP' : Agrees (sF.val args) envP (parentNames d) := Agrees_of_map hagP
  have hagdP : ∀ dt ∈ dsP, ∀ n ∈ dt.affNames, envP.intVal? n = some (sF.val args n) :=
    fun dt hdt n hn => hagP' n (hck1 dt hdt n hn)
  have h2P := buildDecls_summary (σ := sF.val args) _ _ hdsP envP hagdP
  have h3P := buildElems_summary (σ := sF.val args) _ _ hdsP envP hagdP
  have CP := ctx_of_env (s := parentSum d dsP) hdsP (paramEnv2_dims h1P) hagP' hck1
  -- the twin's declarations: the parent's, then each child's renamed
  have hdeclsF : sF.decls = dsP ++ pl.flatMap childDecls := by
    have h := declsOf?_append hdsP (declsOf?_parts (mapM_rel2 hparts))
    have hsd' : declsOf? (d.decls ++ parts.flatMap (·.2.1)) = .ok sF.decls := hsd
    exact Except.ok.inj (hsd'.symm.trans h)
  have hPF : ∀ n ∈ dsP.map (·.name), findDecl dsP n = findDecl sF.decls n := by
    intro n hn
    obtain ⟨dt, hdt, rfl⟩ := List.mem_map.mp hn
    have hs' : (findDecl dsP dt.name).isSome = true := by
      unfold findDecl; rw [List.find?_isSome]; exact ⟨dt, hdt, by simp⟩
    obtain ⟨dt', hdt'⟩ := Option.isSome_iff_exists.mp hs'
    rw [hdeclsF, hdt']
    simp only [findDecl, List.find?_append] at hdt' ⊢
    rw [hdt']
    rfl
  have hdwP : ∀ n, ((parentSum d dsP).DW (sF.val args) n).isSome = true →
      (parentSum d dsP).DW (sF.val args) n = some (sF.dw (sF.val args) n) := by
    intro n hn
    obtain ⟨dt, hdt⟩ := Option.isSome_iff_exists.mp
      (show ((parentSum d dsP).find n).isSome = true by simpa [Summary.DW] using hn)
    have hmem : n ∈ dsP.map (·.name) := by
      have h1 : dt ∈ dsP := List.mem_of_find?_eq_some hdt
      have h2 : dt.name = n := by have := List.find?_some hdt; simpa using this
      exact List.mem_map.mpr ⟨dt, h1, h2⟩
    have hF : sF.find n = some dt := by
      show findDecl sF.decls n = some dt
      rw [← hPF n hmem]; exact hdt
    simp [Summary.DW, Summary.dw, hdt, hF]
  have hdwF : ∀ n, (sF.DW (sF.val args) n).isSome = true →
      sF.DW (sF.val args) n = some (sF.dw (sF.val args) n) := fun n h => dw_some n h
  -- the twin's sites: the parent's, then the instances'
  rw [show (twinOf d parts).processes = d.processes.map PProcess.unsign ++ parts.flatMap (·.2.2) from rfl] at hprocF
  obtain ⟨SP, SR, hSPR, hSP, hSR⟩ := List.map_eq_append_iff.mp hprocF
  have hlSP : SP.length = d.processes.length := by
    have := congrArg List.length hSP
    simpa using this
  rw [hSPR, List.take_left' hlSP] at hck2
  rw [hSPR, List.drop_left' hlSP] at hck3
  -- the twin's processes
  have hMFp : (((twinOf d parts).assemble2 envF (sF.decls.map (DeclT.toDecl (sF.val args)))
      (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) []).processes.toList) =
      (SP ++ SR).map fun st => instProcess2 (envF.withDecls (sF.decls.map (DeclT.toDecl (sF.val args))))
        (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) st.proc := by
    rw [PDesign.assemble2_processes, ← hSPR]
    simp [← hprocF, hothD, twinOf, List.map_map, Function.comp_def]
  -- disjoint driver windows of the whole twin
  have hDW : (((twinOf d parts).assemble2 envF (sF.decls.map (DeclT.toDecl (sF.val args)))
      (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) []).processes.toList.flatMap
        Process2.drvWins).Pairwise (fun a b => a.overlaps b = false) := by
    have h := driversOk_of_combDesign (inputs := [])
      (names := (((twinOf d parts).assemble2 envF (sF.decls.map (DeclT.toDecl (sF.val args)))
        (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) []).processes.toList.flatMap
          Process2.drvWins).map (·.1)) hcMF hposMF (by simp)
    rw [driversOk_iff] at h
    have hfil : ∀ (L : List Process2), (∀ p ∈ L, ∀ w ∈ p.drvWins,
        w.1 ∈ (((twinOf d parts).assemble2 envF (sF.decls.map (DeclT.toDecl (sF.val args)))
          (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) []).processes.toList.flatMap
            Process2.drvWins).map (·.1)) →
        driverWins ((((twinOf d parts).assemble2 envF (sF.decls.map (DeclT.toDecl (sF.val args)))
          (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) []).processes.toList.flatMap
            Process2.drvWins).map (·.1)) L = L.flatMap Process2.drvWins := by
      intro L hL
      unfold driverWins
      apply CombView.flatMap_congr'
      intro p hp
      apply List.filter_eq_self.mpr
      intro w hw
      simpa using hL p hp w hw
    rw [hfil _ (fun p hp w hw => List.mem_map.mpr ⟨w, List.mem_flatMap.mpr ⟨p, hp, hw⟩, rfl⟩)] at h
    exact h.1
  rw [hMFp, List.map_append, List.flatMap_append, List.pairwise_append] at hDW
  obtain ⟨-, hDR, -⟩ := hDW
  -- the instances, one by one
  have key : ∀ (pl' : List (PInst × PDesign)) (parts' : List (List PLocalParam × List PDecl × List PProcess))
      (S : List TSite), (∀ x ∈ pl', x ∈ pl) → Rel2 (fun x part => instPart x.1 x.2 = .ok part) pl' parts' →
      S.map TSite.proc = parts'.flatMap (·.2.2) → (∀ st ∈ S, st ∈ sF.statics) →
      SegsOk dsP (parentNames d) pl' S →
      ((S.map fun st => instProcess2 (envF.withDecls (sF.decls.map (DeclT.toDecl (sF.val args))))
        (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) st.proc).flatMap Process2.drvWins).Pairwise
          (fun a b => a.overlaps b = false) →
      expandListH (PDesign.childRec lib.length lib { int32 := true } (PDesign.surfaceFuel args)
          (Decl.inputNames (dsP.map (DeclT.toDecl (sF.val args)))))
        (envP.withDecls (dsP.map (DeclT.toDecl (sF.val args)))) (dsP.map fun dt => (dt.name, dt.elemW (sF.val args)))
        (PDesign.surfaceFuel args) (pl'.map fun x => GenItem.inst x.1) =
        .ok ((pl'.flatMap childDecls).map (DeclT.toDecl (sF.val args)),
          S.map fun st => instProcess2 (envF.withDecls (sF.decls.map (DeclT.toDecl (sF.val args))))
            (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) st.proc) := by
    intro pl'
    induction pl' with
    | nil =>
        intro parts' S _ hr hS _ _ _
        cases parts' with
        | nil =>
            simp only [List.flatMap_nil, List.map_eq_nil_iff] at hS
            subst hS
            simp
        | cons _ _ => exact hr.elim
    | cons x xs ih =>
        intro parts' S hsub hr hS hSF hseg hD
        cases parts' with
        | nil => exact hr.elim
        | cons part parts'' =>
            obtain ⟨hx, hr'⟩ := hr
            obtain ⟨hcc, plps, conns, -, hconns, hpe⟩ := instPart_ok hx
            obtain ⟨-, -, sc, hsc⟩ := childCheck_ok hcc
            have hxm := hsub x (List.mem_cons_self ..)
            obtain ⟨hpath, hfind⟩ := hplx x hxm
            simp only [List.flatMap_cons] at hS
            obtain ⟨S1, S2, rfl, hS1, hS2⟩ := List.map_eq_append_iff.mp hS
            have hl1 : S1.length = (childPorts x.2).length + x.2.processes.length := by
              rw [← List.length_map (f := TSite.proc), hS1, hpe]
              simp [(mapM_rel2 hconns).length]
            obtain ⟨hseg1, hseg2⟩ := hseg
            have e1 : (S1 ++ S2).take (childPorts x.2).length = S1.take (childPorts x.2).length :=
              List.take_append_of_le_length (by omega)
            have e2 : ((S1 ++ S2).drop (childPorts x.2).length).take x.2.processes.length =
                (S1.drop (childPorts x.2).length).take x.2.processes.length := by
              rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
            have e3 : (S1 ++ S2).drop ((childPorts x.2).length + x.2.processes.length) = S2 :=
              List.drop_left' hl1
            rw [e1, e2] at hseg1
            rw [e3] at hseg2
            rw [List.map_append, List.flatMap_append, List.pairwise_append] at hD
            have hmemD : ∀ dt ∈ sc.decls, dt.hren (hpfx x.1) ∈ sF.decls := by
              intro dt hdt
              rw [hdeclsF]
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hxm, ?_⟩)
              simp only [childDecls, hsc]
              exact List.mem_map_of_mem hdt
            have hstep := inst_step (F := PDesign.surfaceFuel args) CP CF hPF hnodupF TF hsc hmemD hpath hfind hx
              (hch.mem x hxm) hS1 (fun st h => hSF st (List.mem_append_left _ h)) hseg1 hD.1
            have hcd : childDecls x = sc.decls.map (DeclT.hren (hpfx x.1)) := by simp [childDecls, hsc]
            have hrest := ih parts'' S2 (fun y hy => hsub y (List.mem_cons_of_mem _ hy)) hr' hS2
              (fun st h => hSF st (List.mem_append_right _ h)) hseg2 hD.2.1
            rw [List.map_cons, expandListH_cons_ok (by simp [GenItem.listInstFree, GenItem.instFree])
              (by rw [GenItem.expandH_inst]; exact hstep) hrest]
            simp [hcd, List.map_append]
  have hgens := key pl parts SR (fun x h => h) (mapM_rel2 hparts) hSR
    (fun st h => by rw [hSPR]; exact List.mem_append_right _ h) hck3 hDR
  rw [← hgenD] at hgens
  -- the hierarchical instantiation
  have hrec := PDesign.instantiateRec_of_ok (d := d) (depth := lib.length) (lib := lib)
    (F := PDesign.surfaceFuel args) (harity := harity) (by rw [paramEnvH_int32]; exact h1P) h2P h3P hgens
  have hm : d.assembleH envP (dsP.map (DeclT.toDecl (sF.val args)))
      ((pl.flatMap childDecls).map (DeclT.toDecl (sF.val args))) (dsP.map fun dt => (dt.name, dt.elemW (sF.val args)))
      (SR.map fun st => instProcess2 (envF.withDecls (sF.decls.map (DeclT.toDecl (sF.val args))))
        (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) st.proc) =
      (twinOf d parts).assemble2 envF (sF.decls.map (DeclT.toDecl (sF.val args)))
        (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) [] := by
    have hpar : d.processes.map (instProcess2 (envP.withDecls (dsP.map (DeclT.toDecl (sF.val args))))
        (dsP.map fun dt => (dt.name, dt.elemW (sF.val args)))) =
        SP.map fun st => instProcess2 (envF.withDecls (sF.decls.map (DeclT.toDecl (sF.val args))))
          (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) st.proc := by
      apply rel2_map_eq (rel2_of_map hSP)
      intro p _ st hst hpst
      have hstF : st ∈ sF.statics := by rw [hSPR]; exact List.mem_append_left _ hst
      obtain ⟨pos, hsF⟩ := TF.site st hstF
      obtain ⟨hpa, hpc⟩ := hck2 st hst
      have hfr := TF.frag st hstF
      have hwr := TF.wid st hstF
      rw [hpst] at hsF hfr hwr ⊢
      exact parent_proc_eqU CP CF hdwP hdwF hsF
        (fun a ha => accOK_parent hPF (TF.acc st hstF a ha) (hpa a ha)) (TF.acc st hstF)
        ⟨hpc, (TF.cn st hstF).2⟩ (TF.cn st hstF) hfr hwr
    have hproc' : (twinOf d parts).processes.map (instProcess2 (envF.withDecls (sF.decls.map (DeclT.toDecl (sF.val args))))
        (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args)))) =
        (SP ++ SR).map fun st => instProcess2 (envF.withDecls (sF.decls.map (DeclT.toDecl (sF.val args))))
          (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) st.proc := by
      rw [show (twinOf d parts).processes = d.processes.map PProcess.unsign ++ parts.flatMap (·.2.2) from rfl,
        ← hprocF, hSPR,
        List.map_map]
      rfl
    simp only [PDesign.assembleH, PDesign.assemble2]
    congr 1
    · rw [hdeclsF]; simp
    · rw [hproc', hpar, hothD]
      simp [twinOf, hothD]
  rw [hm] at hrec
  have hdrv : driversOk d.declNames d.inputNames
      ((twinOf d parts).assemble2 envF (sF.decls.map (DeclT.toDecl (sF.val args)))
        (sF.decls.map fun dt => (dt.name, dt.elemW (sF.val args))) []).processes.toList = true := by
    apply driversOk_of_combDesign hcMF hposMF
    intro n hn
    apply PDesign.instantiate2_inputNames hMF
    simp only [PDesign.inputNames, twinOf, List.filter_append, List.map_append] at hn ⊢
    exact List.mem_append_left _ hn
  exact PDesign.instantiateHD2_of_ok (PDesign.instantiateH_of_rec hrec hdrv)

/-- **`X.sem N` of a hierarchical design is the twin's unguarded family** (the alias guard is inert: every process
of the twin's instantiation is a continuous assignment, `CombDesign`). The form the tactics rewrite the goal along. -/
theorem instantiateHDAlias2_twin {d : PDesign} {lib : List PDesign} {args : List Int} {dF : PDesign}
    {pl : List (PInst × PDesign)} (htw : hierTwin d lib = .ok (dF, pl))
    {sF : Summary} {envF : IEnv} (hs : dF.summary = .ok sF) (harity : args.length = dF.params.length)
    (h1 : dF.paramEnv2 args = .ok envF)
    (hag : sF.params.map (fun n => envF.intVal? n) = sF.params.map (fun n => some (sF.val args n)))
    (hok : sF.StructOk) (hauto : sF.AutoObl (sF.val args) args) (hin : sF.InRangeObl (sF.val args))
    (hdisj : sF.DisjObl (sF.val args)) (hfrag : sF.EqFrag) (hwid : sF.WidthObl (sF.val args))
    {dsP : List DeclT} (hdsP : declsOf? d.decls = .ok dsP) (hck : HierOk d dsP pl sF)
    {envP : IEnv} (h1P : d.paramEnv2 args = .ok envP)
    (hagP : (parentNames d).map (fun n => envP.intVal? n) =
      (parentNames d).map (fun n => some (sF.val args n)))
    (hch : AllChildEnvOk (sF.val args) (envP.withDecls (dsP.map (DeclT.toDecl (sF.val args)))) pl) :
    d.instantiateHDAlias2 lib args = dF.instantiateGD2 args := by
  unfold PDesign.instantiateHDAlias2
  rw [instantiateHD2_twin htw hs harity h1 hag hok hauto hin hdisj hfrag hwid hdsP hck h1P hagP hch]
  apply Design2.aliasGuard_of_noComb
  have hc := comb_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj
  intro p hp b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨t, e, ws, hpe, -⟩ := hc.assign i p (by rw [← Array.getElem?_toList]; exact hi)
  rw [hpe] at hb
  cases hb

/-! ## Axiom pins -/

/-- info: 'LeanModels.Sv.CombHier.instantiateHD2_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instantiateHD2_twin

/-- info: 'LeanModels.Sv.CombHier.instantiateHDAlias2_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms instantiateHDAlias2_twin

/-- info: 'LeanModels.Sv.CombHier.inst_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inst_step

-- The affine reader with its quotient atoms (`CombView.Aff.qs`), and their renaming under an instance prefix.
/-- info: 'LeanModels.Sv.CombView.affOf?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.affOf?_sound

/-- info: 'LeanModels.Sv.CombView.evalInt_div_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.evalInt_div_of

/-- info: 'LeanModels.Sv.CombView.affDiv_cases' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CombView.affDiv_cases

/-- info: 'LeanModels.Sv.affDiv_hren' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms affDiv_hren

/-- info: 'LeanModels.Sv.Aff.eval_hren' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Aff.eval_hren

end CombHier
end LeanModels.Sv
