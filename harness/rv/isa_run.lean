import LeanModels.Rv.Step
import Lean.Data.Json

/-!
# ISA-step batch runner for the RV differential harness

Driven by `harness/rv/diff_test.py`: reads a JSON file of program cases
(the same flat binaries the harness hands to the sail-riscv reference
emulator as ELFs), executes each with `LeanModels.Rv.isaStep` from reset,
and prints one JSON record per case with the observable trace the harness
compares against the sail `--trace-instr --trace-gpr --trace-mem` log:

* `pcs`  — the pc of every *retired* instruction, in order. Exception
  steps retire a record at the faulting pc (sail prints a trace header for
  them); interrupt-dispatch steps retire nothing (sail prints no header).
* `gprs` — the value-changing register writes `[reg, value]`, in order
  (sail logs every architectural write; the harness filters both sides to
  value-changing writes so that e.g. `add x5, x5, x0` compares equal).
* `mems` — data-memory writes `[addr, nbytes, value]` as issued (any
  alignment; `value` masked to the access width).
* `regs` — the final 32-entry register file; `csrs` — the final CSR file.

Platform layer (owned here, not by the model, mirroring the sail platform):

* instruction fetch reads the current memory at `pc` (bits `[1:0] = 11` ⇒
  32-bit parcel, else compressed halfword);
* a store to the simple-interrupt-generator register (`irqgen`) sets or
  clears MSI/MEI on the `irq` lines: bit 31 selects set/clear, bits 3/11
  are the lines (`doc/SimpleInterruptGenerator.md` in sail-riscv);
* a store to `tohost + 4` (the high word of the 64-bit HTIF mailbox —
  the write on which the sail emulator dispatches the HTIF command)
  terminates the run.
-/

open Lean LeanModels.Rv

/-- Byte image loaded from the case's segments; addresses not in the image
read 0 (the sail platform zero-initializes RAM). -/
abbrev Image := Std.HashMap Nat UInt8

def Image.toMem (img : Image) : Mem :=
  fun a => BitVec.ofNat 8 (img.getD a.toNat 0).toNat

/-- Fetch a parcel from memory at `pc` (bits `[1:0] = 11` ⇒ 32-bit word). -/
def fetchAt (m : Mem) (pc : BitVec 32) : Fetched :=
  let h : BitVec 16 := m (pc + 1) ++ m pc
  if h &&& 3 == 3 then
    .word (m (pc + 3) ++ m (pc + 2) ++ m (pc + 1) ++ m pc)
  else
    .half h

/-- One case's observable trace. -/
structure CaseOut where
  name  : String
  term  : Bool := false
  steps : Nat := 0
  pcs   : Array Nat := #[]
  gprs  : Array (Nat × Nat) := #[]
  mems  : Array (Nat × Nat × Nat) := #[]
  regs  : Array Nat := #[]
  csrs  : List (String × Nat) := []

/-- `Nat` to JSON number. -/
def jnat (n : Nat) : Json := Json.num n

def CaseOut.toJson (o : CaseOut) : Json :=
  Json.mkObj
    [ ("name", Json.str o.name)
    , ("term", Json.bool o.term)
    , ("steps", jnat o.steps)
    , ("pcs", Json.arr (o.pcs.map jnat))
    , ("gprs", Json.arr (o.gprs.map fun (r, v) => Json.arr #[jnat r, jnat v]))
    , ("mems", Json.arr (o.mems.map fun (a, n, v) =>
        Json.arr #[jnat a, jnat n, jnat v]))
    , ("regs", Json.arr (o.regs.map jnat))
    , ("csrs", Json.mkObj (o.csrs.map fun (k, v) => (k, jnat v))) ]

/-- The simple-interrupt-generator update: `v[31]` selects set/clear of the
MSI (3) / MEI (11) lines. -/
def irqgenUpdate (irq v : BitVec 32) : BitVec 32 :=
  let lines := v &&& 0x00000808
  if v[31] then irq ||| lines else irq &&& ~~~lines

/-- Run one case to termination (or out of fuel). -/
def runCase (name : String) (entry tohost irqgen : Nat) (maxSteps : Nat)
    (img : Image) : CaseOut :=
  let rec go (fuel : Nat) (s : ArchState) (m : Mem) (irq : BitVec 32)
      (out : CaseOut) : CaseOut :=
    match fuel with
    | 0 => out
    | fuel + 1 =>
      let parcel := fetchAt m s.pc
      let (s', eff) := isaStep s m parcel irq
      -- retired-instruction record: everything except interrupt dispatch
      let retired := match eff.trap with
        | some (.interrupt _) => false
        | _ => true
      let out := { out with steps := out.steps + 1 }
      let out := if retired then { out with pcs := out.pcs.push s.pc.toNat } else out
      -- value-changing register writes, in index order (at most one per step)
      let out := (List.range 32).foldl (init := out) fun out r =>
        let r : Reg := ⟨r % 32, Nat.mod_lt _ (by omega)⟩
        if s'.regs r ≠ s.regs r then
          { out with gprs := out.gprs.push (r.val, (s'.regs r).toNat) }
        else out
      -- data-memory write effect (as issued; value masked to the width)
      let (out, irq', termNow) := match eff.mem with
        | some (.write addr width data) =>
          let n := width.bytes
          let v := data.toNat % (2 ^ (8 * n))
          let out := { out with mems := out.mems.push (addr.toNat, n, v) }
          let irq' := if addr.toNat == irqgen then irqgenUpdate irq data else irq
          (out, irq', addr.toNat == tohost + 4)
        | _ => (out, irq, false)
      let m' := applyMemEffect m eff.mem
      if termNow then
        { out with term := true
                   regs := (Array.range 32).map fun r => (s'.regs ⟨r % 32, by omega⟩).toNat
                   csrs := [ ("mstatus", s'.csrs.mstatus.toNat)
                           , ("mtvec", s'.csrs.mtvec.toNat)
                           , ("mepc", s'.csrs.mepc.toNat)
                           , ("mcause", s'.csrs.mcause.toNat)
                           , ("mie", s'.csrs.mie.toNat)
                           , ("mscratch", s'.csrs.mscratch.toNat) ] }
      else
        go fuel s' m' irq' out
  go maxSteps (ArchState.init (BitVec.ofNat 32 entry)) img.toMem 0 { name := name }

/-! ## JSON input -/

def getNatField (j : Json) (k : String) : Except String Nat := do
  (← j.getObjVal? k).getNat?

def hexByte (c₁ c₀ : Char) : Except String Nat := do
  let d (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
    else .error s!"bad hex digit {c}"
  return 16 * (← d c₁) + (← d c₀)

def loadSegments (j : Json) : Except String Image := do
  let segs ← (← j.getObjVal? "segments").getArr?
  let mut img : Image := {}
  for seg in segs do
    let base ← getNatField seg "base"
    let hex ← (← seg.getObjVal? "hex").getStr?
    let cs := hex.toList.toArray
    if cs.size % 2 != 0 then throw "odd hex string"
    for i in [0 : cs.size / 2] do
      img := img.insert (base + i) (UInt8.ofNat (← hexByte cs[2*i]! cs[2*i+1]!))
  return img

def runCaseJson (j : Json) : Except String Json := do
  let name ← (← j.getObjVal? "name").getStr?
  let entry ← getNatField j "entry"
  let tohost ← getNatField j "tohost"
  let irqgen ← getNatField j "irqgen"
  let maxSteps ← getNatField j "maxSteps"
  let img ← loadSegments j
  return (runCase name entry tohost irqgen maxSteps img).toJson

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | do
    IO.eprintln "usage: lake env lean --run harness/rv/isa_run.lean <cases.json>"
    return 1
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => IO.eprintln s!"bad JSON: {e}"; return 1
  | .ok j =>
    match j.getArr? with
    | .error e => IO.eprintln s!"expected array: {e}"; return 1
    | .ok cases =>
      for c in cases do
        match runCaseJson c with
        | .ok out => IO.println out.compress
        | .error e => IO.eprintln s!"case error: {e}"; return 1
      return 0
