import LeanModels.Sv.Kernel.Core1Edge

/-!
# Source-shaped edge elaboration

IEEE 1800-2023 §§9.2.2.1, 9.2.2.4, 9.4.2: transport the retained positive-edge
`always` and `always_ff` nodes into E's edge processes. The event and body are
unchanged; the source style stays in `FF.style`. No clocked body is lowered.

This narrow entry point admits scalar input clocks, the existing active-low
reset event, and `ffOkB` bodies. Other events, mixed comb/edge designs and
active-high resets remain loud. Step 9's general elaborator can reuse the
node transport; this file does not define `Elab1.ofDesign2`.
-/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

/-- Source-node transport; unsupported process kinds fail rather than being
discarded or replaced by an empty body. Body admission is checked separately. -/
def FF.ofProcess2 : Process2 → Except String FF
  | .alwaysFF clk body => .ok { clk := clk, rstn := none, body := body }
  | .alwaysPlain clk body =>
      .ok { clk := clk, rstn := none, body := body, style := .alwaysPlain }
  | .alwaysFFR clk rstn body false =>
      .ok { clk := clk, rstn := some rstn, body := body }
  | .alwaysFFR _ _ _ true => .error "9.4.2: active-high reset is outside this E edge elaborator"
  | .alwaysComb _ | .assign _ _ => .error "9.2: mixed comb/edge design is outside this E edge elaborator"
  | .unsupported k msg => .error s!"{k}: {msg}"

/-- Read the retained source node back. Some manually constructed E events
have no corresponding frozen Process2 node, so the reverse is optional. -/
def FF.toProcess2? (f : FF) : Option Process2 :=
  match f.edge, f.style, f.rstn with
  | .posedge, .alwaysFF, none => some (.alwaysFF f.clk f.body)
  | .posedge, .alwaysPlain, none => some (.alwaysPlain f.clk f.body)
  | .posedge, .alwaysFF, some r => some (.alwaysFFR f.clk r f.body false)
  | _, _, _ => none

/-- Transport every process in source order, without filtering. -/
def FF.ofProcesses2 : List Process2 → Except String (List FF)
  | [] => .ok []
  | p :: ps =>
      match FF.ofProcess2 p with
      | .error msg => .error msg
      | .ok f =>
          match FF.ofProcesses2 ps with
          | .error msg => .error msg
          | .ok fs => .ok (f :: fs)

/-- This elaborator's event profile: a declared scalar input. The first
declaration is consulted, as in E's existing flat name lookup. -/
def edgeInputB (d : Design2) (n : String) : Bool :=
  match d.decls.toList.find? (fun dc => dc.name == n) with
  | some dc => dc.isInput && dc.width == 1
  | none => false

def FF.eventInputsB (d : Design2) (f : FF) : Bool :=
  edgeInputB d f.clk && match f.rstn with
    | none => true
    | some r => edgeInputB d r

/-- A source-kind-preserving entry into the edge-only fragment. Admission
is loud; one-writer/no-clock-write profile proofs are still explicit. -/
def Elab1.ofEdgeDesign2 (d : Design2) : Except String Elab1 :=
  match FF.ofProcesses2 d.processes.toList with
  | .error msg => .error msg
  | .ok fs =>
      let E : Elab1 := { decls := d.decls, procs := fs.toArray, name := d.name }
      if !fs.all (FF.eventInputsB d) then
        .error "9.4.2: this E edge elaborator requires declared scalar input clocks and resets"
      else if !E.okB then
        .error "9.2.2.1/9.2.2.4: procedural body is outside E's admitted edge fragment"
      else .ok E

/-- A successful transport retains the source kind, event and entire body. -/
theorem FF.ofProcess2_preserves {p : Process2} {f : FF}
    (h : FF.ofProcess2 p = .ok f) : f.toProcess2? = some p := by
  cases p with
  | alwaysFF clk body => cases h; rfl
  | alwaysPlain clk body => cases h; rfl
  | alwaysFFR clk r body high =>
      cases high with
      | false => cases h; rfl
      | true => cases h
  | alwaysComb body => cases h
  | assign t e => cases h
  | unsupported k msg => cases h

theorem FF.ofProcesses2_preserves {ps : List Process2} {fs : List FF}
    (h : FF.ofProcesses2 ps = .ok fs) :
    fs.map FF.toProcess2? = ps.map some := by
  induction ps generalizing fs with
  | nil => cases h; rfl
  | cons p ps ih =>
      simp only [FF.ofProcesses2] at h
      cases hp : FF.ofProcess2 p with
      | error msg => simp [hp] at h
      | ok f =>
          cases hs : FF.ofProcesses2 ps with
          | error msg => simp [hp, hs] at h
          | ok rest =>
              simp only [hp, hs, Except.ok.injEq] at h
              cases h
              simp only [List.map, FF.ofProcess2_preserves hp, ih hs]

/-- Every source process survives in order, together with the original
declarations/name; a successful design has admitted events and bodies. -/
theorem Elab1.ofEdgeDesign2_spec {d : Design2} {E : Elab1}
    (h : Elab1.ofEdgeDesign2 d = .ok E) :
    E.decls = d.decls ∧ E.name = d.name ∧
      E.procs.toList.map FF.toProcess2? = d.processes.toList.map some ∧
      E.procs.toList.all (FF.eventInputsB d) = true ∧ E.okB = true := by
  unfold Elab1.ofEdgeDesign2 at h
  cases hs : FF.ofProcesses2 d.processes.toList with
  | error msg => simp [hs] at h
  | ok fs =>
      simp only [hs] at h
      split at h
      · cases h
      · rename_i he
        split at h
        · cases h
        · rename_i hb
          cases h
          exact ⟨rfl, rfl, by simpa using FF.ofProcesses2_preserves hs,
            by simpa using he, by simpa using hb⟩

#print axioms FF.ofProcess2_preserves
#print axioms FF.ofProcesses2_preserves
#print axioms Elab1.ofEdgeDesign2_spec

end LeanModels.Sv.Kernel
