import LeanModels.Es

/-!
# `es-score` — the ES tier's test262 scoreboard

The first instrument in this lane that produces a VERDICT rather than a
prediction. Every number the lane has reported until now — `+1,249`,
`+1,036`, `33/66`, `5,464 in vocabulary` — is a claim about what COULD run,
computed from the evaluator's own arms. This runs the tests.

**THE ZEROES ARE NOT THE SAME ZERO.** `refused-construct`,
`refused-intrinsic`, `refused-host`, `timeout`, `not-parsed`,
`not-ingested`, `prelude-failed` and `runner-error` are all "not scored",
and they are eight different facts about different subsystems — the
evaluator's frontier, the realm's absence, the host's, the fuel bound, the
frontend, the ingester, the harness, and this file. Pooling them makes the
scoreboard unfalsifiable: it can no longer say whether a rung would move
the number. `docs/es-charter.md` §3.6 already forbids pooling the three ES
refusal causes, and this is that rule at the scoreboard.

**`prelude-failed` is its own state, and that is not bookkeeping.** Every
test262 test runs `sta.js` and `assert.js` first (INTERPRETING.md). If the
prelude does not evaluate, the test never ran — reporting that as the
TEST's refusal would blame the test for the harness, and 1,816 identical
refusals would look like a frontier rather than one broken file.

**The summary here is re-derived by `harness/es_score.py`** from the
per-test lines, by a different program. Agreement is evidence; disagreement
is a defect in one of the two.
-/

namespace LeanModels.Es.Score

open LeanModels.Es

/-- One test's outcome. -/
inductive Verdict where
  | passed
  | failed (detail : String)
  | refusedConstruct (detail : String)
  | refusedIntrinsic (detail : String)
  | refusedHost (detail : String)
  | timeout
  | threwOther (detail : String)
  | preludeFailed (detail : String)
  | notParsed (detail : String)
  | notIngested (detail : String)
  | runnerError (detail : String)
  deriving Repr, Inhabited

def Verdict.token : Verdict → String
  | .passed => "passed"
  | .failed _ => "failed"
  | .refusedConstruct _ => "refused-construct"
  | .refusedIntrinsic _ => "refused-intrinsic"
  | .refusedHost _ => "refused-host"
  | .timeout => "timeout"
  | .threwOther _ => "threw-other"
  | .preludeFailed _ => "prelude-failed"
  | .notParsed _ => "not-parsed"
  | .notIngested _ => "not-ingested"
  | .runnerError _ => "runner-error"

def Verdict.detail : Verdict → String
  | .passed | .timeout => ""
  | .failed d | .refusedConstruct d | .refusedIntrinsic d | .refusedHost d
  | .threwOther d | .preludeFailed d | .notParsed d | .notIngested d
  | .runnerError d => d

/-- A one-line rendering of a thrown value, for the detail column. It is
telemetry: nothing branches on it. -/
def describe (fuel : Nat) (v : Val) : EsW String := do
  match v with
  | .str s => return s
  | .num _ | .bool _ | .undef | .null => return (toString (repr v))
  | .obj r => do
    match ← getV fuel r (.str "message") (.obj r) with
    | .str m => return m
    | _ => return "«object»"
  | _ => return "«value»"

/--
Run the prelude and then the test in ONE realm, as INTERPRETING.md requires.

A `throw` is classified by whether it is a `Test262Error` — that is the
suite's own protocol for "this assertion failed", and anything else is the
program throwing for its own reasons, which is a different fact.
-/
def runInRealm (fuel : Nat) (prelude : List Node) (test : Node) : EsW Verdict := do
  let env ← newScriptEnvironment
  for p in prelude do
    let bad ← SemM.catchRaise
                (do let _ ← evalProgram fuel env p; pure (none : Option String))
                (fun a => match a with
                  | .throw v => do return some (← describe fuel v)
                  | _ => return some "a non-throw completion escaped the prelude")
    match bad with
    | some d => return .preludeFailed d
    | none => pure ()
  SemM.catchRaise
    (do let _ ← evalProgram fuel env test; return Verdict.passed)
    (fun a =>
      match a with
      | .throw v => do
        let ctor ← lookupName fuel env "Test262Error"
        if ← ordinaryHasInstance fuel ctor v then
          return .failed (← describe fuel v)
        else
          return .threwOther (← describe fuel v)
      | _ => return .runnerError "a non-throw abrupt completion escaped the Script")

/-- Classify what the base monad returned. A refusal and a timeout live
BELOW `ExceptT ρ`, so they arrive here and never through `catchRaise` —
which is what stops a `try` in a test from swallowing the tier's own
frontier and scoring it as a pass. -/
def classify (r : LeanModels.HaltWith EsDetail Unit (Except Abrupt Verdict × EsWorld)) : Verdict :=
  match r with
  | .ok (.ok v, _) => v
  | .ok (.error _, _) => .runnerError "an abrupt completion escaped the runner"
  | .error .timeout => .timeout
  | .error (.unsupported c m _) =>
    match c.detail.kind with
    | .construct => .refusedConstruct m
    | .unmodeledIntrinsic => .refusedIntrinsic m
    | .hostFacility => .refusedHost m

/-- The whole of one test, from envelope text to verdict. -/
def scoreOne (fuel : Nat) (prelude : List Node) (envelopeText : String) : Verdict :=
  match parseEnvelopeString envelopeText with
  | .error e => .notIngested e
  | .ok envl =>
    match envl.parse with
    | .error kind msg line col => .notParsed s!"{kind} at {line}:{col}: {msg}"
    | .ok program => classify (SemM.run (ρ := Abrupt) (runInRealm fuel prelude program) default)

/-! ## The summary, and the rules it obeys -/

structure Tally where
  passed := 0
  failed := 0
  refusedConstruct := 0
  refusedIntrinsic := 0
  refusedHost := 0
  timeout := 0
  threwOther := 0
  preludeFailed := 0
  notParsed := 0
  notIngested := 0
  runnerError := 0
  deriving Inhabited

def Tally.add (t : Tally) : Verdict → Tally
  | .passed => { t with passed := t.passed + 1 }
  | .failed _ => { t with failed := t.failed + 1 }
  | .refusedConstruct _ => { t with refusedConstruct := t.refusedConstruct + 1 }
  | .refusedIntrinsic _ => { t with refusedIntrinsic := t.refusedIntrinsic + 1 }
  | .refusedHost _ => { t with refusedHost := t.refusedHost + 1 }
  | .timeout => { t with timeout := t.timeout + 1 }
  | .threwOther _ => { t with threwOther := t.threwOther + 1 }
  | .preludeFailed _ => { t with preludeFailed := t.preludeFailed + 1 }
  | .notParsed _ => { t with notParsed := t.notParsed + 1 }
  | .notIngested _ => { t with notIngested := t.notIngested + 1 }
  | .runnerError _ => { t with runnerError := t.runnerError + 1 }

/-- Every state, so the reader can check the sum rather than trust it. -/
def Tally.total (t : Tally) : Nat :=
  t.passed + t.failed + t.refusedConstruct + t.refusedIntrinsic + t.refusedHost
    + t.timeout + t.threwOther + t.preludeFailed + t.notParsed + t.notIngested
    + t.runnerError

def summarise (t : Tally) (firstFailure : Option (String × Verdict)) : List String :=
  let scored := t.passed + t.failed
  [ s!"test262 {scored}/{t.total} scored  (passed {t.passed}, failed {t.failed})",
    s!"  the zeroes, kept apart: refused-construct {t.refusedConstruct}, " ++
      s!"refused-intrinsic {t.refusedIntrinsic}, refused-host {t.refusedHost}, " ++
      s!"timeout {t.timeout}, threw-other {t.threwOther}, " ++
      s!"prelude-failed {t.preludeFailed}, not-parsed {t.notParsed}, " ++
      s!"not-ingested {t.notIngested}, runner-error {t.runnerError}",
    s!"  states sum to {t.total}" ]
  ++ (match firstFailure with
      | none => []
      -- IN LOG ORDER, VERBATIM. Not sorted, not deduplicated: `sort -u`
      -- answers "which distinct failures exist", and a reader after a red
      -- run is asking "what went wrong FIRST".
      | some (n, v) => [s!"  FIRST NON-PASS (log order, verbatim): {n}  {v.token}  {v.detail}"])

/-- `es-score <fuel> <prelude.json>,… <list-of-envelope-paths>` -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [fuelS, preludeS, listPath] => do
    let fuel := (fuelS.toNat?).getD 2000
    let mut prelude : List Node := []
    for p in preludeS.splitOn "," do
      let txt ← IO.FS.readFile ⟨p⟩
      match parseEnvelopeString txt with
      | .error e => IO.eprintln s!"es-score: prelude '{p}' is not an envelope: {e}"; return 2
      | .ok envl =>
        match envl.parse with
        | .error _ m _ _ => IO.eprintln s!"es-score: prelude '{p}' did not parse: {m}"; return 2
        | .ok prog => prelude := prelude ++ [prog]
    let listing ← IO.FS.readFile ⟨listPath⟩
    let mut tally : Tally := {}
    let mut first : Option (String × Verdict) := none
    for line in listing.splitOn "\n" do
      let path := line.trim
      if path.isEmpty then continue
      let v ←
        match ← (IO.FS.readFile ⟨path⟩).toBaseIO with
        | .error e => pure (Verdict.runnerError s!"cannot read envelope: {toString e}")
        | .ok txt => pure (scoreOne fuel prelude txt)
      let name := path.splitOn "/" |>.getLast!
      IO.println s!"{name}\t{v.token}\t{v.detail}"
      tally := tally.add v
      if first.isNone then
        match v with
        | .passed => pure ()
        | _ => first := some (name, v)
    IO.println "----"
    for l in summarise tally first do IO.println l
    return 0
  | _ =>
    IO.eprintln "usage: es-score <fuel> <prelude1.json[,prelude2.json]> <envelope-list>"
    return 2

end LeanModels.Es.Score

def main (args : List String) : IO UInt32 := LeanModels.Es.Score.main args
