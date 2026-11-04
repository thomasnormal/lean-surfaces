/-
# SV multi-point cross-check runner (round 3 CX)

  lake env lean --run harness/sv/xcheck2.lean <envelope.sv.json> [<probes.json>]

Loads a symbolic sv-0.2 envelope and its probe sidecar (default: the
envelope's own `<file>.sv.probes.json`, `probeSidecarPath`; written by
`extract.py --top T --probe-points "N=1;N=4"`), and prints one line per
probe entry (`Envelope2.probeReport`, `LeanModels/Sv/Probe2.lean`):

  XCHECK ok          <point> <entry> (<ms> ms)
  XCHECK UNCONFIRMED <point> <entry>: <verdict> (<ms> ms)
  XCHECK FAIL        <point> <entry>: <verdict> (<ms> ms)

(`ProbeVerdict.status`) then `XCHECK-SUMMARY <agree> agree, <fail> fail`
(`fail` counts every entry that is not `ok`). Exit 0 iff every entry
agrees, 3 if some entry does not, 1 on a load/parse error (a missing
sidecar is an error here: nothing compared is not agreement).

  lake env lean --run harness/sv/xcheck2.lean --batch <list.txt>

checks many pairs in ONE process (the measurement sweep): each line of
`list.txt` is `<envelope>\t<probes.json>`; every output line is prefixed
`<envelope> `, a pair that fails to load prints `XCHECK ERROR <envelope>`.
-/

import Lean
import LeanModels.Sv.Ingest2

open LeanModels.Sv

/-- Check one envelope/sidecar pair; `(agree, fail)` or a load error. -/
def checkPair (out : IO.FS.Stream) (pfx envPath sidePath : String) :
    IO (Except String (Nat × Nat)) := do
  unless ← System.FilePath.pathExists ⟨sidePath⟩ do
    return .error s!"no probe sidecar '{sidePath}' (nothing compared is not agreement)"
  let envText ← IO.FS.readFile ⟨envPath⟩
  let prText ← IO.FS.readFile ⟨sidePath⟩
  let envl ← match parseEnvelope2String envText with
    | .ok e => pure e
    | .error e => return .error s!"envelope: {e}"
  let pr ← match parseProbes2String prText with
    | .ok p => pure p
    | .error e => return .error s!"sidecar: {e}"
  let mut agree := 0
  let mut fail := 0
  -- Point by point (timed), so the per-point cost is measurable.
  for p in pr.points do
    let t0 ← IO.monoMsNow
    let one : Probes2 := { pr with points := [p] }
    let lines ← IO.lazyPure fun _ =>
      (envl.probeReport one).map fun (l, v) => (l, v.ok, v.status, v.render)
    let n := lines.foldl (fun acc (_, _, _, r) => acc + r.length) 0
    let t1 ← IO.monoMsNow
    for (l, ok, st, r) in lines do
      if ok then
        agree := agree + 1
        out.putStrLn s!"{pfx}XCHECK ok   {l} ({t1 - t0} ms)"
      else
        fail := fail + 1
        out.putStrLn s!"{pfx}XCHECK {st} {l}: {r} ({t1 - t0} ms)"
    if n == 0 then out.putStrLn ""
  return .ok (agree, fail)

def main (argv : List String) : IO UInt32 := do
  let err (msg : String) : IO UInt32 := do
    (← IO.getStderr).putStrLn s!"ERROR: {msg}"
    return 1
  let out ← IO.getStdout
  match argv with
  | ["--batch", listPath] =>
      let mut agree := 0
      let mut fail := 0
      let mut errors := 0
      for ln in (← IO.FS.readFile ⟨listPath⟩).splitOn "\n" do
        match ln.splitOn "\t" with
        | [e, p] =>
            match ← checkPair out s!"{e} " e p with
            | .ok (a, f) => agree := agree + a; fail := fail + f
            | .error m =>
                errors := errors + 1
                out.putStrLn s!"{e} XCHECK ERROR {m}"
        | _ => pure ()
      out.putStrLn s!"XCHECK-SUMMARY {agree} agree, {fail} fail, {errors} error(s)"
      return (if errors != 0 then 1 else if fail == 0 then 0 else 3)
  | _ =>
    let (envPath, sidePath) ← match argv with
      | [e] => pure (e, probeSidecarPath e)
      | [e, p] => pure (e, p)
      | _ => return (← err "usage: xcheck2.lean <envelope.sv.json> [<probes.json>] | --batch <list.txt>")
    match ← checkPair out "" envPath sidePath with
    | .error m => err m
    | .ok (agree, fail) =>
        out.putStrLn s!"XCHECK-SUMMARY {agree} agree, {fail} fail"
        return (if fail == 0 then 0 else 3)
