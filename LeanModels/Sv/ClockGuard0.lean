import LeanModels.Sv.Ast

/-!
# The M0 implicit-clock guard

The M0 cycle semantics treats each stimulus entry as one rising edge of one
implicit clock.  That contract cannot give a meaning to two independent
clocks, a derived/data clock, or a clock that is absent from the input ports.
This small guard keeps those shapes loud at the JSON boundary and in the M0
runner.  The canonical M0 source clock is `clk`; richer clock names and event
lists belong to the sv-0.2/kernel route.
-/

namespace LeanModels.Sv

def Process.clock? : Process → Option String
  | .alwaysFF c _ | .alwaysPlain c _ => some c
  | .alwaysComb _ | .assign _ _ | .unsupported _ _ => none

def Design.clockNames (d : Design) : List String :=
  (d.processes.toList.filterMap Process.clock?).eraseDups

def Design.clockPort (d : Design) (c : String) : Option Decl :=
  d.decls.toList.find? fun dc => dc.name == c

def Design.clockViolation (d : Design) : Option (String × String) :=
  match d.clockNames with
  | [] => none
  | c :: rest =>
      if !rest.isEmpty then
        some ("Clock:multiple",
          s!"module '{d.name}' has multiple M0 clocks ({String.intercalate ", " (c :: rest)}); one stimulus entry cannot represent independent edge arrivals")
      else
        match d.clockPort c with
        | none =>
            some ("Clock:source",
              s!"clock '{c}' of module '{d.name}' is not an input port; the M0 cycle has no event source")
        | some dc =>
            if !dc.isInput then
              some ("Clock:source",
                s!"clock '{c}' of module '{d.name}' is not an input port; the M0 cycle has no event source")
            else if c != "clk" then
              some ("Clock:implicit",
                s!"clock '{c}' of module '{d.name}' is not the canonical M0 `clk`: the M0 cycle fires every edge process on every stimulus entry, so a data or derived clock would capture when no real edge occurred")
            else none

def Design.clockReport (d : Design) : Option (String × String) := d.clockViolation

def Design.clockGuard (d : Design) : Design :=
  match d.clockReport with
  | none => d
  | some (kind, msg) =>
      { d with processes := d.processes.push (.unsupported kind msg) }

private def m0Ok : Design :=
  { name := "m0_ok"
    decls := #[{ name := "clk", width := 1, isInput := true }]
    processes := #[.alwaysFF "clk" (.blockingAssign "q" (.lit (.ofNat 1 0)))] }

private def m0Two : Design :=
  { name := "m0_two"
    decls := #[{ name := "clk", width := 1, isInput := true },
      { name := "clk2", width := 1, isInput := true }]
    processes := #[.alwaysFF "clk" (.blockingAssign "q" (.lit (.ofNat 1 0))),
      .alwaysFF "clk2" (.blockingAssign "r" (.lit (.ofNat 1 0)))] }

private def m0Data : Design :=
  { name := "m0_data"
    decls := #[{ name := "en", width := 1, isInput := true }]
    processes := #[.alwaysFF "en" (.blockingAssign "q" (.lit (.ofNat 1 0)))] }

#guard m0Ok.clockReport == none
#guard m0Two.clockReport |>.isSome
#guard m0Data.clockReport |>.isSome

end LeanModels.Sv
