/-
Step 11 source evidence for plain always @*. Retained extraction preserves
its ImplicitEventControl rather than replacing it by always_comb. PProcess
keeps that event and its parsed body. The frozen execution boundary stays
loud; these are no execution witnesses.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

namespace Examples.«system-verilog».sem2.always_star_step11.agree

open LeanModels.Sv

load_design_sv2 alwaysStarStep11
  from "Examples/system-verilog/sem2/always_star_step11/always_star_step11.sv.json"

#guard alwaysStarStep11.pdesign.others == []
#guard match alwaysStarStep11.pdesign.processes with
  | [.alwaysImplicit (.block [.caseStmt _ _ _ .normal .none]), .alwaysComb _] => true
  | _ => false
#guard match (alwaysStarStep11.sem 4).processes.toList with
  | [.unsupported "ProceduralBlockSymbol:Always" _, .alwaysComb _] => true
  | _ => false
#guard (alwaysStarStep11.sem 4).hasUnsupported

load_design_sv2 alwaysStarFunctionSensitivityStep11
  from "Examples/system-verilog/sem2/always_star_step11/always_star_function_sensitivity_step11.sv.json"

-- User function calls and implicit events stay source-shaped in the envelope
-- and loud at the frozen process/expression boundary; no inlining witness.
#guard (alwaysStarFunctionSensitivityStep11.sem 4).hasUnsupported
#guard alwaysStarFunctionSensitivityStep11.pdesign.processes.any fun p =>
  match p with | .alwaysImplicit _ => true | _ => false

load_design_sv2 alwaysStarStartupStep11
  from "Examples/system-verilog/sem2/always_star_step11/always_star_startup_step11.sv.json"

#guard alwaysStarStartupStep11.pdesign.others == []
#guard (alwaysStarStartupStep11.sem 4).hasUnsupported
#guard (alwaysStarStartupStep11.pdesign.processes.filter fun p =>
  match p with | .alwaysImplicit _ => true | _ => false).length == 2

-- Neither frozen view evaluates or rewrites the retained body.
example (env : IEnv) (body : PStmt) :
    instProcess env (.alwaysImplicit body) = instProcess env
      (.unsupported "ProceduralBlockSymbol:Always"
        "source-level event-controlled always is retained; the frozen process AST has no event-list constructor") := rfl

example (env : IEnv) (elems : List (String × Nat)) (body : PStmt) :
    instProcess2 env elems (.alwaysImplicit body) = instProcess2 env elems
      (.unsupported "ProceduralBlockSymbol:Always"
        "source-level event-controlled always is retained; the frozen process AST has no event-list constructor") := rfl

private def eventJson (kind : String) (extra : List (String × Lean.Json) := []) : Lean.Json :=
  .mkObj ([
    ("kind", .str "AlwaysEvent"), ("event_kind", .str kind),
    ("body", .mkObj [("kind", .str "Empty")])] ++ extra)

-- Empty bodies still have an implicit wait; they must not become comb.
#guard (parsePProcess (eventJson "ImplicitEventControl")).toOption ==
  some (.alwaysImplicit (.block []))
#guard (parsePProcess (eventJson "ImplicitEventControl" [("style", .str "always")])).toOption ==
  some (.alwaysImplicit (.block []))

-- Event lists, edges, guards, clocks, resets and foreign source styles cannot
-- be discarded while claiming this is the parser's implicit control.
#guard ["events", "edge", "iff", "clock", "areset", "areset_n", "reset_iff"].all fun field =>
  (parsePProcess (eventJson "ImplicitEventControl" [(field, .bool true)])).toOption.isNone
#guard [Lean.Json.str "always_ff", .str "always_comb", .bool true].all fun style =>
  (parsePProcess (eventJson "ImplicitEventControl" [("style", style)])).toOption.isNone
#guard match (parsePProcess (eventJson "SignalEventControl")).toOption with
  | some (.unsupported "ProceduralBlockSymbol:Always" _) => true
  | _ => false
#guard (parsePProcess (.mkObj [("kind", .str "AlwaysEvent"),
  ("event_kind", .str "ImplicitEventControl")])).toOption.isNone

-- The retiring memory adapter must refuse the new source node, including
-- generated instances, instead of silently skipping it.
#guard match alwaysStarStep11.pdesign.instantiateMem2 [4] with
  | .unsupported "ProceduralBlockSymbol:Always: source-level event-controlled always is retained; the frozen process AST has no event-list constructor" => true
  | _ => false

private def generatedImplicit : PDesign :=
  { name := "generated_implicit", params := [], localParams := [], enums := [],
    decls := [], processes := [],
    generates := [.genIf (.int 1) [.process (.alwaysImplicit (.block []))] []] }

#guard match generatedImplicit.instantiateMem2 [] with
  | .unsupported "ProceduralBlockSymbol:Always: source-level event-controlled always is retained; the frozen process AST has no event-list constructor" => true
  | _ => false

end Examples.«system-verilog».sem2.always_star_step11.agree
