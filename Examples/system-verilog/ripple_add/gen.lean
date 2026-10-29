import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# `ripple_add` — the generate-loop acceptance of the Design2 proof layer

The real envelope `ripple_add.sv.json` (an `N`-bit ripple-carry adder
written with ONE `generate for` over the bit index) instantiates, for EVERY
`N` — symbolically, nothing unrolled at a fixed width — to exactly

```
c[0] = cin;   cout = c[N];   for i < N:  s[i] = a[i]^b[i]^c[i];
                                         c[i+1] = (a[i]&b[i]) | (c[i]&(a[i]^b[i]))
```

as `Process2.assign` nodes over 1-bit `slice` targets (and the whole-signal
1-bit target `.ident "cout"`) and 1-bit `slice` reads (plus the whole-signal
1-bit read `.ident "cin"`), with no `resize` nodes anywhere (every operand
is 1 bit wide in a 1-bit context — `fitExpr2_bitSel_ident`). This is what
the combinational settle theorem (`Comb2*.lean`) consumes for the ∀N
correctness proof in this directory's `spec.lean`/`proof.lean`.

Route (all through `LeanModels/Sv/Gen2.lean`, no hand unfolding of the
well-founded expansion): `PDesign.instantiate2_of_ok` splits
`instantiate2` into its stages; the parameter environment is `rfl`
(`ripple_paramEnv`), declarations and element widths are `simp`
computations with symbolic `N` (`ripple_decls`, `ripple_elems`); the
generate-for is `GenItem.expand2_genFor_ascending_processes` (the shared
`genvarSeq_ascending`) and `intRange_zero` turns its `Int` genvar
sequence into `List.range N`; each body template instantiates at a
`Nat`-cast genvar by the `sv2_inst_simp` recipe (`ripple_sum_inst`,
`ripple_carry_inst`).

This file lives in `Examples/` (not `LeanModels/`) because
`load_design_sv2` reads the envelope at elaboration time and envelopes live
beside their example sources. The envelope is NOT a tracked build input:
`lakefile.toml`'s `Examples` library lists no input directory for
`Examples/system-verilog`, so re-extracting `ripple_add.sv.json` does not by
itself rebuild this module; force a rebuild of it (and of `proof.lean` /
`spec.lean`) after an envelope change.
`proof.lean` imports this module and reuses ITS `ripple_add` constant (a
second `load_design_sv2` would produce a definitionally-equal but distinct
constant that these theorems do not syntactically mention).
-/

namespace Examples.«system-verilog».ripple_add.gen

open LeanModels.Sv

load_design_sv2 ripple_add from "Examples/system-verilog/ripple_add/ripple_add.sv.json"

/-! ## The envelope's shape (pinned by `rfl`) -/

/-- The sum-bit template `assign s[i] = a[i] ^ b[i] ^ c[i];`. -/
def sumT : PProcess :=
  .assignL (.bitSel "s" (.genvarRef "i"))
    (.binary (.m0 .xor)
      (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i"))
        (.bitSel (.ident "b") (.genvarRef "i")))
      (.bitSel (.ident "c") (.genvarRef "i")))

/-- The carry template `assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));`. -/
def carryT : PProcess :=
  .assignL (.bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 1)))
    (.binary (.m0 .or)
      (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "i"))
        (.bitSel (.ident "b") (.genvarRef "i")))
      (.binary (.m0 .and) (.bitSel (.ident "c") (.genvarRef "i"))
        (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i"))
          (.bitSel (.ident "b") (.genvarRef "i")))))

/-- The one generate item: `for (i = 0; i s< N; i++)` over the two
templates (`resolved_count` 4 is the defaults metadata). -/
theorem ripple_generates :
    ripple_add.pdesign.generates =
      [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
        (.unary .inc (.genvarRef "i")) (some 4) ([sumT, carryT].map GenItem.process)] := rfl

/-- The two static continuous assigns, in source order. Their labels are
static (`0`, `N`) over the parameter-dependent `[N:0]`, so both selects are
`ArraySel` paths, normalized against the declared range at every point
(2026-10-28; the legacy `BitSel` read a label as an offset from bit 0). -/
theorem ripple_static_source :
    ripple_add.pdesign.processes =
      [.assignL (.arrayElem "c" [.int 0]) (.ident "cin"),
       .assign "cout" (.arrayElem "c" [.paramRef "N" none])] := rfl

/-! ## The instantiated vocabulary -/

/-- `c[0] = cin`. -/
def cinProc : Process2 := .assign (.slice "c" 0 1) (.ident "cin")

/-- `cout = c[N]`. -/
def coutProc (N : Nat) : Process2 := .assign (.ident "cout") (.slice (.ident "c") N 1)

/-- `s[i] = a[i] ^ b[i] ^ c[i]` at bit `i`. -/
def sumProc (i : Nat) : Process2 :=
  .assign (.slice "s" i 1)
    (.binary .xor (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
      (.slice (.ident "c") i 1))

/-- `c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]))` at bit `i`. -/
def carryProc (i : Nat) : Process2 :=
  .assign (.slice "c" (i + 1) 1)
    (.binary .or (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))
      (.binary .and (.slice (.ident "c") i 1)
        (.binary .xor (.slice (.ident "a") i 1) (.slice (.ident "b") i 1))))

/-- The whole instantiated process list, in `instantiate2`'s order: static
processes, then the generate family bit by bit (sum before carry). -/
def rippleProcs (N : Nat) : List Process2 :=
  cinProc :: coutProc N :: (List.range N).flatMap fun i => [sumProc i, carryProc i]

/-- The instantiated declarations (ports first, then `c`), for `N ≥ 1`. -/
def rippleDecls (N : Nat) : List Decl :=
  [{ name := "a", width := N, isInput := true },
   { name := "b", width := N, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := N, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := N + 1 }]

/-! ## The stages of `instantiate2` at symbolic `N` -/

/-- The declaration scope: `N` bound, its declared type `int` 32 bits. -/
def rippleScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment: the declaration scope plus the packed-array
geometry table evaluated in it (`dimTable` — every `instantiate2`
environment carries it). -/
def rippleEnv (N : Int) : IEnv :=
  { rippleScope N with dims := dimTable (rippleScope N) ripple_add.pdesign.decls }

/-- Declarations at raw widths: `wv` = `|N-1| + 1` (the `[N-1:0]` ports),
`wc` = `|N| + 1` (`c[N:0]`) — the width rule is total in `N`, which is why
the process-list theorems below need no `1 ≤ N`. -/
def rippleDeclsRaw (wv wc : Nat) : List Decl :=
  [{ name := "a", width := wv, isInput := true },
   { name := "b", width := wv, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := wv, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := wc }]

/-- Every declaration is 1-D: element width 1. -/
def rippleElems : List (String × Nat) :=
  [("a", 1), ("b", 1), ("cin", 1), ("s", 1), ("cout", 1), ("c", 1)]

/-- The parameter stage binds `N` (by `rfl`). -/
theorem ripple_paramEnv (N : Int) : ripple_add.pdesign.paramEnv2 [N] = .ok (rippleEnv N) := rfl

/-- The declaration stage at symbolic `N`: the raw widths `|N-1| + 1` and
`|N| + 1`. -/
theorem ripple_decls (N : Int) :
    buildDecls (rippleEnv N) ripple_add.pdesign.decls =
      .ok (rippleDeclsRaw ((N - 1).natAbs + 1) (N.natAbs + 1)) := by
  simp [ripple_add.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    rippleEnv, rippleScope, List.lookup, rippleDeclsRaw, Gen2.except_ok_bind]

/-- The element-width stage: every declaration has element width 1. -/
theorem ripple_elems (N : Int) :
    buildElems (rippleEnv N) ripple_add.pdesign.decls = .ok rippleElems := by
  simp [ripple_add.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, rippleEnv,
    rippleScope, List.lookup, rippleElems, Gen2.except_ok_bind]

/-- The sum template at a `Nat`-cast genvar (any surrounding environment:
the template reads only element widths and the genvar). -/
theorem ripple_sum_inst (env : IEnv) (i : Nat) :
    instProcess2 (env.bindVal "i" i) rippleElems sumT = sumProc i := by
  sv2_inst_simp [rippleElems, sumT, sumProc]

/-- The carry template at a `Nat`-cast genvar (`c[i+1]`: offset `i + 1`). -/
theorem ripple_carry_inst (env : IEnv) (i : Nat) :
    instProcess2 (env.bindVal "i" i) rippleElems carryT = carryProc i := by
  sv2_inst_simp [rippleElems, carryT, carryProc]

/-- The static processes (`cout = c[N]` reads the PARAMETER-indexed bit). -/
theorem ripple_static (N : Nat) (wv wc : Nat) :
    ripple_add.pdesign.processes.map
        (instProcess2 ((rippleEnv N).withDecls (rippleDeclsRaw wv wc)) rippleElems) =
      [cinProc, coutProc N] := by
  sv2_inst_simp [ripple_add.pdesign, rippleEnv, rippleScope, rippleDeclsRaw, rippleElems, cinProc,
    coutProc, dimTable, dimTableStep, PType.width_packed_cons, PDim.width, Int.lt_add_one_iff]

/-- The generate expansion at the surface fuel: the bit-indexed family. -/
theorem ripple_gens (N : Nat) (wv wc : Nat) :
    expandList2 ((rippleEnv N).withDecls (rippleDeclsRaw wv wc)) rippleElems
      (PDesign.surfaceFuel [(N : Int)]) ripple_add.pdesign.generates =
      .ok ((List.range N).flatMap fun i => [sumProc i, carryProc i]) := by
  rw [ripple_generates]
  apply expandList2_singleton_ok
  rw [GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
    (fun i => by simp [rippleEnv, rippleScope, List.lookup])
    (fun i => by simp [evalInt, rippleEnv, rippleScope, List.lookup])
    (by
      have := Nat.le_mul_self (N + 2)
      simp [PDesign.surfaceFuel]
      omega)]
  simp only [Int.sub_zero, Int.toNat_natCast, intRange_zero, List.flatMap_map, List.map_cons,
    List.map_nil, ripple_sum_inst, ripple_carry_inst]

/-- **`instantiate2` at symbolic `N`**: succeeds, and is the assembled
design of the stages above. -/
theorem ripple_instantiate2 (N : Nat) :
    ripple_add.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (ripple_add.pdesign.assemble2 (rippleEnv N)
        (rippleDeclsRaw (((N : Int) - 1).natAbs + 1) ((N : Int).natAbs + 1)) rippleElems
        ((List.range N).flatMap fun i => [sumProc i, carryProc i])) :=
  PDesign.instantiate2_of_ok rfl (ripple_paramEnv N) (ripple_decls N) (ripple_elems N)
    (ripple_gens N _ _)

/-! ## The acceptance theorems -/

/-- **The instantiated process list, for every `N`** (no unrolling): `c[0] =
cin`, `cout = c[N]`, then `s[i]`, `c[i+1]` for each `i < N`. -/
theorem ripple_processes (N : Nat) :
    (ripple_add.pdesign.instantiateD2 [(N : Int)]).processes.toList = rippleProcs N := by
  rw [PDesign.instantiateD2_of_ok (ripple_instantiate2 N), PDesign.assemble2_processes,
    ripple_static]
  simp [rippleProcs, ripple_add.pdesign]

/-- **Membership characterization, both directions**:
a process of the instantiated adder is the carry-in, the carry-out, or the
sum/carry cell of some bit `i < N`. -/
theorem mem_ripple_processes (N : Nat) (p : Process2) :
    p ∈ (ripple_add.pdesign.instantiateD2 [(N : Int)]).processes.toList ↔
      p = cinProc ∨ p = coutProc N ∨ ∃ i < N, p = sumProc i ∨ p = carryProc i := by
  rw [ripple_processes]
  simp [rippleProcs]

/-- The process count: `2N + 2`. -/
theorem ripple_processes_length (N : Nat) :
    (ripple_add.pdesign.instantiateD2 [(N : Int)]).processes.toList.length = 2 * N + 2 := by
  rw [ripple_processes]
  simp only [rippleProcs, List.length_cons, List.length_flatMap, List.length_nil,
    List.map_const', List.sum_replicate_nat, List.length_range]
  omega

/-- **The instantiated declarations** for `N ≥ 1`: `a`, `b`, `s` are `N`
bits, `cin`/`cout` 1 bit, the carry chain `c` is `N + 1` bits. -/
theorem ripple_decls_instantiated (N : Nat) (hN : 1 ≤ N) :
    (ripple_add.pdesign.instantiateD2 [(N : Int)]).decls.toList = rippleDecls N := by
  rw [PDesign.instantiateD2_of_ok (ripple_instantiate2 N), PDesign.assemble2_decls]
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hc : (N : Int).natAbs = N := Int.natAbs_natCast N
  rw [hv, hc]
  rfl

/-! ## The one-driver rule, for every `N`

`ripple_add.sem N` is `instantiateGD2`: the instantiated design under the
one-driver rule (`Hier2.lean`, "Drivers" — a flat top is checked at every
parameter point since 2026-10-28). The rule holds for every `N`, by the
process-list recipe of `Hier2Gen.lean`: compute the driver windows of
`rippleProcs N` (`ripple_driverWins`), split the generate family with
`pairwise_flatMap_range`, close each pair with `omega`. -/

/-- The envelope's declared names and input ports (parameter-free). -/
theorem ripple_declNames : ripple_add.pdesign.declNames = ["a", "b", "cin", "s", "cout", "c"] :=
  rfl

theorem ripple_inputNames_pd : ripple_add.pdesign.inputNames = ["a", "b", "cin"] := rfl

/-- The windows bit `i` drives: `s[i]` and `c[i+1]`. -/
def rippleWins (i : Nat) : List DrvWin := [("s", some (i, 1)), ("c", some (i + 1, 1))]

/-- The continuous-driver windows of the instantiated adder, for every `N`. -/
theorem ripple_driverWins (N : Nat) :
    driverWins ["a", "b", "cin", "s", "cout", "c"] (rippleProcs N) =
      [("c", some (0, 1)), ("cout", none)] ++ (List.range N).flatMap rippleWins := by
  have hs : ["a", "b", "cin", "s", "cout", "c"].contains "s" = true := by decide
  have hc : ["a", "b", "cin", "s", "cout", "c"].contains "c" = true := by decide
  have ho : ["a", "b", "cin", "s", "cout", "c"].contains "cout" = true := by decide
  simp only [rippleProcs, driverWins_cons, driverWins_nil, driverWins_flatMap, cinProc, coutProc,
    sumProc, carryProc, Process2.drvWins, Lhs2.drvWins, List.filter_cons, List.filter_nil, hs, hc,
    ho, ↓reduceIte, List.cons_append, List.nil_append, List.append_nil]
  rfl

/-- **The one-driver rule holds for every `N`**: no procedural process;
`c[0]`, the whole `cout`, and per bit `s[i]`, `c[i+1]` are pairwise
disjoint; none is an input port. -/
theorem ripple_driversOk (N : Nat) :
    driversOk ripple_add.pdesign.declNames ripple_add.pdesign.inputNames (rippleProcs N) = true := by
  rw [ripple_declNames, ripple_inputNames_pd]
  apply driversOk_of_continuous
  · rw [List.flatMap_eq_nil_iff]
    intro p hp
    simp only [rippleProcs, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | ⟨k, _, rfl | rfl⟩ <;> rfl
  · rw [ripple_driverWins, List.pairwise_append]
    refine ⟨by decide, pairwise_flatMap_range (fun k _ => ?_) (fun j k hjk _ a ha b hb => ?_), ?_⟩
    · simp [rippleWins]
    · simp only [rippleWins, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [DrvWin.overlaps] <;> omega
    · intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [List.mem_flatMap, List.mem_range, rippleWins, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      obtain ⟨k, _, hb⟩ := hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [DrvWin.overlaps]
  · intro w hw
    rw [ripple_driverWins] at hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
      List.mem_range, rippleWins] at hw
    rcases hw with (rfl | rfl) | ⟨k, _, (rfl | rfl)⟩ <;> rfl

/-- **`ripple_add.sem N` is the instantiated design**, for every `N` (the
guard of `instantiateGD2` passes: `ripple_driversOk`). -/
theorem ripple_sem_eq (N : Nat) :
    ripple_add.sem N = ripple_add.pdesign.instantiateD2 [(N : Int)] := by
  show ripple_add.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [ripple_processes]
  exact ripple_driversOk N

/-- The `load_design_sv2` family member `ripple_add.sem N` is the same
design (`Int.ofNat N` is the binder encoding of `(N : Int)`; the one-driver
guard passes, `ripple_sem_eq`). -/
theorem ripple_sem_processes (N : Nat) :
    (ripple_add.sem N).processes.toList = rippleProcs N := by
  rw [ripple_sem_eq]
  exact ripple_processes N

/-- `mem_ripple_processes` for the family member `ripple_add.sem N`. -/
theorem mem_ripple_sem_processes (N : Nat) (p : Process2) :
    p ∈ (ripple_add.sem N).processes.toList ↔
      p = cinProc ∨ p = coutProc N ∨ ∃ i < N, p = sumProc i ∨ p = carryProc i := by
  rw [ripple_sem_eq]
  exact mem_ripple_processes N p

/-- `ripple_decls_instantiated` for the family member `ripple_add.sem N`. -/
theorem ripple_sem_decls (N : Nat) (hN : 1 ≤ N) :
    (ripple_add.sem N).decls.toList = rippleDecls N := by
  rw [ripple_sem_eq]
  exact ripple_decls_instantiated N hN

#print axioms ripple_driversOk
#print axioms ripple_sem_eq

/-! ## Concrete agreement (non-vacuity at the default `N = 4`) -/

#guard (ripple_add.sem 4).processes.size == 10
#guard (ripple_add.sem 4).decls.toList.map (·.width) == [4, 4, 1, 4, 1, 5]

end Examples.«system-verilog».ripple_add.gen
