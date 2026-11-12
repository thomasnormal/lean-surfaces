import LeanModels.Sv.Kernel.Core0E
import LeanModels.Sv.Param2
import LeanModels.Sv.Kernel.MemE

/-!
# Parser entries for E-core-0

The authority module (`Core0E`) contains only the exact scalar E definitions.
This file is the source-shaped adapter layer: it depends on the symbolic
parameter frontend and on the optional memory profile, and therefore must not
be imported by E-core-0's authority or observation modules.

`Process2` is frozen and has no constructor for an implicit event control.
`EProcess2` keeps that retained parser node beside the ordinary image; the
adapter below turns it into `Proc0` only at the E entry boundary.  Memory is
similarly kept in an explicit wrapper rather than in `Elab`, so the scalar
authority has no dependency on `MemE`.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Source-preserving E entry point -/

def Proc0.ofEProcess2 : EProcess2 → Proc0
  | .alwaysImplicit body => .implicit body
  | .ordinary p =>
      match p with
      | .assign t e => .assign t e
      | .alwaysComb b => .comb b
      | .unsupported k x => .comb (.unsupported k x)
      | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ =>
          .comb (.unsupported "always_ff" "clocked processes are outside E-core-0")

def Elab.ofEDesign2 (d : EDesign2) : Elab :=
  { decls := d.decls
    procs := (d.processes.toList.map Proc0.ofEProcess2).toArray
    name := d.name }

/-! ## Canonical source-shaped memory entry -/

structure MemoryElab where
  scalar : Elab
  memory : MemEDesign

def MemoryElab.memoryInitial (E : MemoryElab) : Except String MemEState :=
  E.memory.timeZero

def MemoryElab.memoryStep (E : MemoryElab) (s : MemEState) (inputs : SvState) :
    Except String MemEState :=
  E.memory.step s inputs

def PDesign.instantiateMemoryE (d : PDesign) (args : List Int) : Res MemoryElab := do
  let md ← MemEDesign.ofPDesign d args
  -- The scalar E elaborator deliberately refuses unpacked declarations; the
  -- memory entry keeps the source declaration in `md` and supplies the scalar
  -- declaration view needed by observations without expanding its cells.
  .ok { scalar := { name := d.name, decls := md.decls.toArray, procs := #[] }
        memory := md }

end LeanModels.Sv.Kernel

