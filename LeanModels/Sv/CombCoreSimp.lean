import Lean

/-!
# `sv_simp`: the tactics' own `simp` does not depend on the ambient simp set (WP-B review, gate M)

The `sv_comb` tactics (`sv_structure`, `sv_equations`, `sv_interface`, `sv_norm`, ...) normalize their obligations
with `simp only [...]` followed by a plain `try simp`, the WHOLE ambient simp set. A submission that imports Mathlib
adds some 37,000 `@[simp]` entries to it, and those change what the tactics leave: `Nat.cast_natAbs` turns the
declared-range obligations into `|↑N + -1|`, which `omega` cannot read; `Order.add_one_le_iff` turns `x + 1 ≤ y` into
`x < y`, a form `sv_rowmajor` does not expect; `sv_cover` meets `(1 + 1).toNat`; `mul_struct` runs out of heartbeats.
Erasing lemmas one at a time is whack-a-mole, and the player-side workaround (`sv_core_simp`, `SvGolf/CoreSimp.lean`)
asks every Mathlib user to know about it.

`sv_simp` is `simp` run with the simp set the tactics were written against: the ambient set MINUS every `@[simp]` tag
added by a module of Mathlib or of one of the packages it imports (`coreSimpPackageRoots`, the roots of
`PACKAGE_ROOTS` in `svgolf/check.py`), for the duration of that one call. It replaces every plain `simp` inside the
tactics. With no package imported it erases nothing and is `simp` itself (nothing else changes: the goals the tactics
print are the same), so a design proved without Mathlib behaves exactly as before; with Mathlib imported the tactics see
Lean core's simp set, as under `sv_core_simp`, WITHOUT the player writing it. The player's own `simp` is untouched.

No axiom and no declaration is added: the erased simp set is built from the environment and handed to `mkSimpContext`
(the environment is not modified: theorem bodies elaborate asynchronously, where a simp-extension update panics); it is
cached (keyed by the number of modules and the size of the ambient lemma set) so that a tactic that runs `sv_simp`
hundreds of times pays the 37,000 erasures once.
-/

namespace LeanModels.Sv

open Lean Meta Elab Tactic

/-- The module roots of Mathlib's package closure (the same eight as `PACKAGE_ROOTS` in `svgolf/check.py` and
`corePackageRoots` in `SvGolf/CoreSimp.lean`). -/
def coreSimpPackageRoots : List Name :=
  [`Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible, `ImportGraph, `LeanSearchClient]

/-- The simp origins that modules of the package roots added: their lemmas, the lemmas of other modules they
re-tagged `@[simp]`, and the definitions they marked to be unfolded. -/
def coreSimpPackageOrigins (env : Environment) : Array Origin := Id.run do
  let names := env.header.moduleNames
  let mut origins : Array Origin := #[]
  for i in [0:names.size] do
    if coreSimpPackageRoots.contains names[i]!.getRoot then
      for e in simpExtension.ext.getModuleEntries env i do
        let se : SimpEntry := match e with | .global a => a | .scoped _ a => a
        match se with
        | .thm t => origins := origins.push t.origin
        | .toUnfold n => origins := origins.push (.decl n)
        | .toUnfoldThms n _ => origins := origins.push (.decl n)
  return origins

/-- The ambient simp set without the package entries, cached by (number of modules, size of the ambient set). -/
initialize coreSimpCache : IO.Ref (Option ((Nat × Nat) × SimpTheorems)) ← IO.mkRef none

/-- The simp theorems `sv_simp` runs with: the ambient ones minus the package entries (the ambient ones themselves
when no package is imported). It READS the environment only: an environment extension cannot be modified inside
the asynchronous elaboration of a theorem body (Lean marks `simpExtension` `mainOnly`), so the erased set is handed
to `mkSimpContext` as a value instead of being swapped into the extension. -/
def erasedSimpTheorems : CoreM SimpTheorems := do
  let env ← getEnv
  let cur ← getSimpTheorems
  let names := env.header.moduleNames
  if !(names.any fun n => coreSimpPackageRoots.contains n.getRoot) then
    return cur
  let key := (names.size, cur.lemmaNames.fold (fun n _ => n + 1) 0)
  let cached ← coreSimpCache.get
  match cached with
  | some (k, e) =>
      if k == key then return e
  | none => pure ()
  let origins := coreSimpPackageOrigins env
  let e := origins.foldl (fun s o => s.eraseCore o) cur
  coreSimpCache.set (some (key, e))
  return e

/-- `simp` (given as syntax) with `erasedSimpTheorems`. -/
def runSvSimp (stx : Syntax) : TacticM Unit := withMainContext do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext stx (eraseLocal := false) (simpTheorems := erasedSimpTheorems)
  discard <| dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])

/-- `sv_simp` / `sv_simp [lemmas]`: `simp` with the simp set of Lean core (see the module docstring). -/
syntax (name := svSimp) "sv_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| sv_simp) => do runSvSimp (← `(tactic| simp))
  | `(tactic| sv_simp [$ids,*]) => do runSvSimp (← `(tactic| simp [$ids,*]))

end LeanModels.Sv
