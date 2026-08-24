import LeanModels.C.Load
import LeanModels.C.C23

/-!
# `c-torture-run` — inch 6's batch driver, and the tier's first NUMBER

`docs/c23-goal.md` §4.2 specced a scoreboard and did not build one. This
is it: a `lean_exe` that reads a MANIFEST of ingested `gcc.c-torture`
tests, runs each one's `main`, and prints one verdict per test followed by
the summary the tier's §9.0 number is read off.

## THE CORPUS IS NEVER IN THIS REPOSITORY

`gcc.c-torture` is **GPL-3.0-or-later** (`docs/c23-goal.md` §2, measured:
0 of the sampled files carry a per-file header, so they inherit GCC's).
`tools/c_corpus_fetch.py` fetches it AT A PIN into a cache OUTSIDE the
tree and refuses to write inside it; what the repository holds is a
manifest of **hashes and verdicts**, which is not the corpus. This driver
never sees a `.c` file — only the `c-0.1` envelopes the extractor
produced from one.

## THE ZEROES ARE NOT THE SAME ZERO

The summary distinguishes them, because a scoreboard that prints one `0`
for all of these is unreadable and, worse, unfalsifiable — it cannot tell
*"the model declined"* from *"nobody ran it."*

| state | what happened | whose fact |
| --- | --- | --- |
| `not-fetched` | the file was never obtained at the pin | the fetch |
| `not-parsed` | clang rejected it under the pinned profile | the FRONTEND |
| `not-ingested` | clang accepted it and the c-0.1 INGESTER refused the extractor's output | the EXTRACTOR/schema pair — neither the frontend nor the model |
| `runner-error` | the envelope could not be read at all | the plumbing (§4.2: an unexecutable test emits a row, never no row) |
| `refused` | the model saw it and declined — cause kept apart | the tier's frontier |
| `timeout` | fuel ran out | the fuel bound |
| `failed` | the program reached `abort()` | **scored** |
| `passed` | `main` returned | **scored** |

**`scored = passed + failed`, and that is the oracle's own reading.**
`docs/c23-goal.md` §1.2: torture's verdict style is *exit status —
`abort()` on failure, fall off `main` on success*. Reaching `abort` is
therefore a RESULT, not a refusal to produce one: the program ran and its
own check failed. Pooling it with `refused` would hide the only failures
this scoreboard can currently see.
-/

namespace LeanModels.C.C23.Torture

open LeanModels.C

/-- What one test did. Constructors, not strings, so the summary buckets
on the TYPE and never by parsing prose (`Core`'s `RefusalCause` rule, one
level up). -/
inductive Verdict where
  | passed
  | passedViaExit                -- reached `exit(0)`: the ORACLE, not a libc model
  | failed                       -- reached `abort()`: the test's own check failed
  | refusedUB (what : String)
  | refusedLibc (name : String)
  | unsupported (what : String)
  | timeout
  | notParsed (why : String)      -- clang rejected it: the FRONTEND's fact
  | notIngested (why : String)    -- the extractor's output; the INGESTER's fact
  | runnerError (why : String)    -- neither: the plumbing failed
  | notFetched
deriving Repr, Inhabited, BEq

/-- Is this a SCORE — a verdict the oracle can read — as opposed to an
absence of one? -/
def Verdict.isScored : Verdict → Bool
  | .passed | .passedViaExit | .failed => true
  | _ => false

def Verdict.token : Verdict → String
  | .passed => "passed"
  | .passedViaExit => "passed"
  | .failed => "failed"
  | .refusedUB _ => "refused-ub"
  | .refusedLibc _ => "refused-libc"
  | .unsupported _ => "refused-unsupported"
  | .timeout => "timeout"
  | .notParsed _ => "not-parsed"
  | .notIngested _ => "not-ingested"
  | .runnerError _ => "runner-error"
  | .notFetched => "not-fetched"

def Verdict.detail : Verdict → String
  | .passed | .failed | .timeout | .notFetched => ""
  | .passedViaExit => "exit(0) — the oracle's success channel, not a libc model"
  | .refusedUB w => w
  | .refusedLibc n => n
  | .unsupported w => w
  | .notParsed w => w
  | .notIngested w => w
  | .runnerError w => w

/-! ## The layout, from the PROFILE and not from a host

`docs/c-profile.md` pins `char_bit_8`, `int_32`, `long_64`. A spelling
outside the table gets `none`, which is a loud refusal at the use site
rather than a guessed size — the same discipline `Layout.unknown` exists
for. -/
/-- The SCALAR spellings, from `docs/c-profile.md`'s `char_bit_8`,
`int_32`, `long_64`. `double` is deliberately absent — floats are a named
decision, not an oversight. -/
def torScalarSize : CType → Option Nat
  | "char" | "signed char" | "unsigned char" | "_Bool" => some 1
  | "short" | "short int" | "unsigned short" => some 2
  | "int" | "unsigned int" | "unsigned" => some 4
  | "long" | "unsigned long" | "long long" | "unsigned long long"
  | "long int" | "unsigned long int" => some 8
  | t => if t.endsWith "*" then some 8 else none

/-- Drop the qualifiers. Exact: `const`/`volatile` do not change a size. -/
def stripQuals : Nat → CType → CType
  | 0, t => t
  | n + 1, t =>
      if t.startsWith "const " then stripQuals n ((t.drop 6).toString)
      else if t.startsWith "volatile " then stripQuals n ((t.drop 9).toString)
      else t

/-- `T[N]` → `(T, N)`. **Single dimension only**: `int[2][3]` splits into
three parts and gets `none`, which is a named zero rather than a guess. -/
def arrayOf (t : CType) : Option (CType × Nat) :=
  if !t.endsWith "]" then none
  else match ((t.dropEnd 1).toString).splitOn "[" with
       | [e, ext] => ext.toNat?.map fun n => (e, n)
       | _ => none

/-- The unit's own typedefs, as a spelling map. A lookup, not a
computation — so resolving through it invents nothing. -/
def typedefsOf (envl : Envelope) : List (CType × CType) :=
  envl.unit.items.filterMap fun i => match i with
    | .decl (.typedef nm ty _ _) => some (nm, ty)
    | _ => none

def resolve (tds : List (CType × CType)) : Nat → CType → CType
  | 0, t => t
  | n + 1, t0 =>
      let t := stripQuals 8 t0
      match tds.find? (·.1 == t) with
      | some p => resolve tds n p.2
      | none => t

/-- A size the instrument can compute EXACTLY, or `none`.

Scalars come from the profile; an array is `n × elem` and §6.2.5p20 says
so with no padding to guess; typedefs and qualifiers are lookups.

**A `struct` gets `none`, and that is the item rather than a shortfall in
it.** Laying one out needs an ALIGNMENT RULE: C leaves the padding
implementation-defined (§6.7.2.1p18), the natural-alignment convention
everyone reaches for is an ABI this project has not pinned, and a layout
computed from an undeclared rule is a FABRICATED layout — the same defect
as a fabricated column, one abstraction up. Structs stay a named zero
until `docs/c-profile.md` pins the rule. -/
def sizeIn (tds : List (CType × CType)) : Nat → CType → Option Nat
  | 0, _ => none
  | n + 1, t0 =>
      let t := resolve tds 8 t0
      match torScalarSize t with
      | some s => some s
      | none => (arrayOf t).bind fun p => (sizeIn tds n p.1).map (· * p.2)

/-- The layout for ONE test, built from its own envelope. -/
def layoutFor (envl : Envelope) : Layout :=
  let tds := typedefsOf envl
  { Layout.unknown with
      size := fun t => sizeIn tds 16 t
      elem := fun t => arrayOf (resolve tds 8 t) }

/-- Peel the conversions a value arrives wrapped in. -/
def peelVal : Expr → Expr
  | .implicitCast _ s _ _ => peelVal s
  | .cast _ s _ _ => peelVal s
  | .paren s _ _ => peelVal s
  | e => e

/-- **THE ORACLE GUARD.** `exit(n)` is the verdict channel, not a library
call this tier models — but the refusal carries only the NAME, and
`exit(0)` and `exit(1)` are opposite verdicts. So an `exit` refusal is
read as success only when every `exit` in the translation unit takes
exactly one argument that peels to the literal `0`.

A program with any other `exit` is NOT scored: we could not tell which one
was reached, and guessing is the pooling §3.1 forbids.

Measured when it was written: all 36 tests that refused on `exit` contain
`exit(0)` and nothing else, so this guard is free today. It is here
because it is what makes the reading honest rather than lucky. -/
def exitIsAlwaysZero (envl : Envelope) : Bool :=
  envl.unit.exprs.all fun e => match e with
    | .call callee args _ _ =>
        if calleeNameOf callee == "exit" then
          match args with
          | [a] => match peelVal a with
                   | .intLit "0" _ _ => true
                   | _ => false
          | _ => false
        else true
    | _ => true

/-- Run one ingested test: call its `main` with no arguments, from an
empty memory, and read the outcome.

`abort` and `exit` are caught BY NAME, before the libc slice can turn
them into environment refusals, because both are the exit-status oracle
speaking — `docs/c23-goal.md` §1.2. Neither is modelled and neither ever
will be by widening the slice. -/
def scoreEnvelope (fuel : Nat) (envl : Envelope) : Verdict :=
  let prog : Program := { fns := envl.unit.functionDefns, layout := layoutFor envl }
  match ExecM.verdict Mem.empty (callByName fuel prog "main" []) with
  | .ok _ => .passed
  | .refused (.libc "abort") => .failed
  | .refused (.libc "exit") =>
      if exitIsAlwaysZero envl then .passedViaExit
      else .refusedLibc "exit (an argument is not a literal 0 — which exit was reached is unknown)"
  | .refused (.libc n) => .refusedLibc n
  | .refused (.valueUB u) => .refusedUB (toString (repr u))
  | .refused (.memUB f) => .refusedUB (toString (repr f))
  | .unsupported w => .unsupported w
  | .timeout => .timeout

/-! ## The manifest

`{ "pin": {...}, "tests": [ { "name":…, "status":"parsed"|"rejected"|"absent",
"envelope":…, "why":… } ] }` — produced by `tools/c_corpus_fetch.py`, in
NAME ORDER, and the order is load-bearing: the summary quotes the FIRST
failure, and "first" has to mean something stable. -/

structure Entry where
  name : String
  status : String
  envelope : Option String
  why : String
deriving Inhabited

private def str? (j : Lean.Json) (k : String) : String :=
  (j.getObjValAs? String k).toOption.getD ""

def parseEntry (j : Lean.Json) : Entry :=
  let env := str? j "envelope"
  { name := str? j "name", status := str? j "status"
    envelope := if env.isEmpty then none else some env
    why := str? j "why" }

def runEntry (fuel : Nat) (e : Entry) : IO Verdict := do
  match e.status, e.envelope with
  | "absent", _ => pure .notFetched
  | "rejected", _ => pure (.notParsed e.why)
  | _, none => pure (.runnerError "manifest says parsed but names no envelope")
  | _, some p =>
      match ← (IO.FS.readFile ⟨p⟩).toBaseIO with
      | .error err => pure (.runnerError s!"cannot read envelope: {toString err}")
      | .ok contents =>
          match parseEnvelopeString contents with
          | .error err => pure (.notIngested err)
          | .ok envl => pure (scoreEnvelope fuel envl)

/-! ## The summary

**The first failure is printed VERBATIM, in log order.** Not the
lexicographically smallest, not one of a deduplicated set: the first one
the run met. A summary that sorts or uniques its failures answers a
different question from the one a reader asks after a red run, and the
reader cannot tell that it did. -/

def summarise (rows : List (String × Verdict)) : List String := Id.run do
  let mut passed := 0; let mut failed := 0; let mut refUB := 0
  let mut refLibc := 0; let mut unsup := 0; let mut tmo := 0
  let mut notParsed := 0; let mut notIngested := 0
  let mut runnerErr := 0; let mut notFetched := 0
  let mut firstFail : Option (String × Verdict) := none
  for (n, v) in rows do
    match v with
    | .passed | .passedViaExit => passed := passed + 1
    | .failed =>
        failed := failed + 1
        if firstFail.isNone then firstFail := some (n, v)
    | .refusedUB _ => refUB := refUB + 1
    | .refusedLibc _ => refLibc := refLibc + 1
    | .unsupported _ => unsup := unsup + 1
    | .timeout => tmo := tmo + 1
    | .notParsed _ => notParsed := notParsed + 1
    | .notIngested _ => notIngested := notIngested + 1
    | .runnerError _ => runnerErr := runnerErr + 1
    | .notFetched => notFetched := notFetched + 1
  let total := rows.length
  let scored := passed + failed
  let mut out : List String := []
  out := out ++ [s!"gcc.c-torture {scored}/{total} scored  (passed {passed}, failed {failed})"]
  out := out ++ [s!"  the zeroes, kept apart: refused-unsupported {unsup}, refused-libc {refLibc}, refused-ub {refUB}, timeout {tmo}, not-ingested {notIngested}, not-parsed {notParsed}, runner-error {runnerErr}, not-fetched {notFetched}"]
  match firstFail with
  | none => out := out ++ ["  first failure: none"]
  | some (n, v) =>
      out := out ++ [s!"  FIRST FAILURE (log order, verbatim): {n}  {v.token}  {v.detail}"]
  pure out

def main (args : List String) : IO UInt32 := do
  let (manifestPath, fuel) :=
    match args with
    | [p] => (p, 64)
    | [p, f] => (p, f.toNat?.getD 64)
    | _ => ("", 64)
  if manifestPath.isEmpty then
    IO.eprintln "usage: c-torture-run <manifest.json> [fuel]"
    return 2
  let contents ← IO.FS.readFile ⟨manifestPath⟩
  let j ← IO.ofExcept (Lean.Json.parse contents)
  let tests := (j.getObjValAs? (Array Lean.Json) "tests").toOption.getD #[]
  let mut rows : List (String × Verdict) := []
  for tj in tests do
    let e := parseEntry tj
    let v ← runEntry fuel e
    IO.println s!"{e.name}\t{v.token}\t{v.detail}"
    rows := rows ++ [(e.name, v)]
  IO.println "----"
  for l in summarise rows do IO.println l
  return 0

end LeanModels.C.C23.Torture

/-- The `lean_exe` root. -/
def main (args : List String) : IO UInt32 := LeanModels.C.C23.Torture.main args
