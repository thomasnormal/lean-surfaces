/-
The Lean tier's AXIOM-DEPENDENCY instrument (M1 inch 5).

For a given environment, reports **which declarations depend on a native
computation, and which one** — the receipt `docs/family-architecture.md` §0.1
II(a) asks every rung-3 `native_decide` use to carry, computed rather than
promised.

Why this is not just `#print axioms`: that prints one constant's axioms to a
human. This walks a whole module set, classifies every declaration's axiom
closure against the TRUST EXTENSIONS measured in `docs/lean-kernel-census.json`
(`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` — all three
deprecated upstream since 2026-02-01), and emits machine-readable rows a
scoreboard can gate on.

Run by `harness/lean_axiom_census.py`, which drives it niced and turns the
output into JSON. Dependency-free apart from `import Lean`, so it needs no
`lake` and no build lock (BUILD_LOCK_PROTOCOL rule 3).

  lean --run harness/lean_axiom_deps.lean <Module> [<Module> ...]
-/
import Lean

open Lean

/-- The three axioms that move the compiler, its runtime and every
`@[implemented_by]` into the trusted base. Measured, not recalled: see
`docs/lean-kernel-census.json`. -/
def trustExtensions : Array Name :=
  #[``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- `sorryAx` is not a trust extension — it is the unsoundness MARKER. Tracked
separately because conflating "this proof is incomplete" with "this proof trusts
the compiler" would misreport both. -/
def unsoundnessMarker : Name := ``sorryAx

structure Row where
  decl    : Name
  axioms  : Array Name
  native  : Array Name
  sorried : Bool

/-- JSON string escaping, hand-rolled to keep this file dependency-free. -/
def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | c    => if c.toNat < 0x20 then "" else c.toString)

def arr (ns : Array Name) : String :=
  "[" ++ String.intercalate "," (ns.toList.map fun n => "\"" ++ esc n.toString ++ "\"") ++ "]"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "REFUSE: no modules given (usage: lean_axiom_deps.lean <Module> ...)"
    return 2
  let mods := args.map (·.toName)
  for m in mods do
    if m.isAnonymous then
      IO.eprintln s!"REFUSE: not a module name: {m}"
      return 2
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => {module := m}) {} (trustLevel := 0)
  -- The scan runs in CoreM, which is what supplies `collectAxioms` its MonadEnv.
  let scan : CoreM (Array Row × Nat × Nat) := do
    -- Only the named modules' OWN declarations: an import closure would report
    -- the same core theorems for every input and make the number meaningless.
    let mut rows : Array Row := #[]
    let mut scanned := 0
    let mut internal := 0
    for (name, ci) in (← getEnv).constants.toList do
      let some idx := (← getEnv).getModuleIdxFor? name | continue
      let some modName := (← getEnv).header.moduleNames[idx.toNat]? | continue
      if !mods.contains modName then continue
      if name.isInternal then
        internal := internal + 1
        continue
      -- Constructors, recursors and inductive types have no closure of their own.
      match ci with
      | .ctorInfo _ | .recInfo _ | .inductInfo _ => continue
      | _ => pure ()
      scanned := scanned + 1
      let axs ← Lean.collectAxioms name
      let native := axs.filter (trustExtensions.contains ·)
      let sorried := axs.contains unsoundnessMarker
      if !native.isEmpty || sorried then
        rows := rows.push { decl := name, axioms := axs, native := native, sorried := sorried }
    return (rows, scanned, internal)
  let ((rows, scanned, internal), _) ←
    scan.toIO { fileName := "<lean_axiom_deps>", fileMap := default } { env := env }
  let nativeRows := rows.filter (!·.native.isEmpty)
  let sorryRows := rows.filter (·.sorried)
  IO.println "{"
  IO.println s!"  \"modules\": {arr mods.toArray},"
  IO.println s!"  \"scanned\": {scanned},"
  IO.println s!"  \"internal_skipped\": {internal},"
  IO.println s!"  \"native_dependent\": {nativeRows.size},"
  IO.println s!"  \"sorry_dependent\": {sorryRows.size},"
  IO.println "  \"rows\": ["
  let mut first := true
  for r in rows do
    let sep := if first then "    " else "   ,"
    first := false
    let q := "\""
    IO.println (sep ++ "{" ++ q ++ "decl" ++ q ++ ": " ++ q ++ esc r.decl.toString ++ q
      ++ ", " ++ q ++ "native" ++ q ++ ": " ++ arr r.native
      ++ ", " ++ q ++ "sorry" ++ q ++ ": " ++ (if r.sorried then "true" else "false")
      ++ ", " ++ q ++ "axioms" ++ q ++ ": " ++ arr r.axioms ++ "}")
  IO.println "  ]"
  IO.println "}"
  return 0
