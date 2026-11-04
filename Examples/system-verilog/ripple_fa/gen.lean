import LeanModels.Sv.Ingest2
import LeanModels.Sv.Hier2Gen

/-!
# `ripple_fa` — the module-hierarchy acceptance of the Design2 layer (F3)

The real envelope `ripple_fa.sv.json` (the `ripple_add` adder written
STRUCTURALLY: one `full_adder` instance per bit, instantiated by a
`generate for`) is a hierarchical envelope — the top module `ripple_fa`
plus the definition of `full_adder`, elaborated alone at its defaults. It
flattens (`PDesign.instantiateH`, `Hier2.lean`), for EVERY `N` —
symbolically, nothing unrolled — to

```
c[0] = cin;   cout = c[N];
for i < N:  g_bit[i].fa.a   = a[i];    g_bit[i].fa.b = b[i];   g_bit[i].fa.cin = c[i];
            s[i]   = g_bit[i].fa.s;     c[i+1] = g_bit[i].fa.cout;
            g_bit[i].fa.s    = g_bit[i].fa.a ^ g_bit[i].fa.b ^ g_bit[i].fa.cin;
            g_bit[i].fa.cout = (g_bit[i].fa.a & g_bit[i].fa.b)
                             | (g_bit[i].fa.cin & (g_bit[i].fa.a ^ g_bit[i].fa.b))
```

— the port connections as continuous assignments (inputs first, in the
child's port order), then the child's own processes under the hierarchical
names — and declares the five port signals of each instance after the
top's six declarations (`ripple_fa_decls`).

Route (`LeanModels/Sv/Hier2Gen.lean`, no hand unfolding of the
well-founded walk): `PDesign.instantiateRec_of_ok` splits the
instantiation; the parameter environment is `rfl`; declarations and element
widths are the `ripple_add` computations; the generate-for is
`GenItem.expandH_genFor_ascending_flatMap`; each iteration is ONE instance
(`expandListH_singleton_ok`, `GenItem.expandH_inst`, `instExpandH_of`)
whose prefix computes symbolically (`fa_prefix`), whose child is the
closed `full_adder` design (`fa_child`), and whose flattening is
`fa_flatten` (the `sv2_inst_simp` recipe on the connection actuals).

Like `ripple_add/gen.lean`, this file lives in `Examples/` because
`load_design_sv2` reads the envelope at elaboration time.
-/

namespace Examples.«system-verilog».ripple_fa.gen

open LeanModels.Sv

load_design_sv2 ripple_fa from "Examples/system-verilog/ripple_fa/ripple_fa.sv.json"

/-! ## The envelope's shape (pinned by `rfl`) -/

/-- The one instance of the generate body: `full_adder fa (.a(a[i]),
.b(b[i]), .cin(c[i]), .s(s[i]), .cout(c[i+1]))` under block `g_bit[i]`. -/
def faInst : PInst :=
  { name := "fa", module := "full_adder", path := [⟨"g_bit", some "i"⟩], params := []
    conns :=
      [.input "a" (some (.bitSel (.ident "a") (.genvarRef "i"))) false,
       .input "b" (some (.bitSel (.ident "b") (.genvarRef "i"))) false,
       .input "cin" (some (.bitSel (.ident "c") (.genvarRef "i"))) false,
       .output "s" (some (.bitSel "s" (.genvarRef "i"))),
       .output "cout" (some (.bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 1))))] }

/-- The one generate item: `for (i = 0; i s< N; i++)` over the instance. -/
theorem ripple_fa_generates :
    ripple_fa.pdesign.generates =
      [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
        (.unary .inc (.genvarRef "i")) (some 4) [.inst faInst]] := rfl

/-- The two static continuous assigns, in source order. Their labels are
static (`0`, `N`) over the parameter-dependent `[N:0]`, so both selects are
`ArraySel` paths, normalized against the declared range at every point
(2026-10-28; the legacy `BitSel` read a label as an offset from bit 0). -/
theorem ripple_fa_static_source :
    ripple_fa.pdesign.processes =
      [.assignL (.arrayElem "c" [.int 0]) (.ident "cin"),
       .assign "cout" (.arrayElem "c" [.paramRef "N" none])] := rfl

/-- The module library is the one `full_adder` definition. -/
theorem ripple_fa_lib_names : ripple_fa.plib.map (·.name) = ["full_adder"] := rfl

/-! ## The flattened vocabulary -/

/-- The hierarchical prefix of bit `k`'s instance: `g_bit[k].fa.`. -/
def faPfx (k : Nat) : String := "g_bit[" ++ toString (k : Int) ++ "].fa."

/-- `full_adder` instantiated alone: its five ports and its two assigns. -/
def faDesign : Design2 :=
  { name := "full_adder"
    decls := #[{ name := "a", width := 1, isInput := true },
               { name := "b", width := 1, isInput := true },
               { name := "cin", width := 1, isInput := true },
               { name := "s", width := 1, isOutput := true },
               { name := "cout", width := 1, isOutput := true }]
    processes :=
      #[.assign (.ident "s") (.binary .xor (.binary .xor (.ident "a") (.ident "b")) (.ident "cin")),
        .assign (.ident "cout")
          (.binary .or (.binary .and (.ident "a") (.ident "b"))
            (.binary .and (.ident "cin") (.binary .xor (.ident "a") (.ident "b"))))] }

/-- The flattened processes of bit `k`: the five port connections (inputs
first, child port order), then the adder's two assigns, renamed. -/
def faProcs (k : Nat) : List Process2 :=
  let n := fun s => faPfx k ++ s
  [.assign (.ident (n "a")) (.slice (.ident "a") k 1),
   .assign (.ident (n "b")) (.slice (.ident "b") k 1),
   .assign (.ident (n "cin")) (.slice (.ident "c") k 1),
   .assign (.slice "s" k 1) (.ident (n "s")),
   .assign (.slice "c" (k + 1) 1) (.ident (n "cout")),
   .assign (.ident (n "s"))
     (.binary .xor (.binary .xor (.ident (n "a")) (.ident (n "b"))) (.ident (n "cin"))),
   .assign (.ident (n "cout"))
     (.binary .or (.binary .and (.ident (n "a")) (.ident (n "b")))
       (.binary .and (.ident (n "cin")) (.binary .xor (.ident (n "a")) (.ident (n "b")))))]

/-- The hoisted declarations of bit `k`: the adder's ports, 1 bit each, no
longer ports. -/
def faDecls (k : Nat) : List Decl :=
  ["a", "b", "cin", "s", "cout"].map fun s => { name := faPfx k ++ s, width := 1 }

/-- `c[0] = cin`. -/
def cinProc : Process2 := .assign (.slice "c" 0 1) (.ident "cin")

/-- `cout = c[N]`. -/
def coutProc (N : Nat) : Process2 := .assign (.ident "cout") (.slice (.ident "c") N 1)

/-- The whole flattened process list, in `instantiateH`'s order: static
processes, then the instance family bit by bit. -/
def rippleFaProcs (N : Nat) : List Process2 :=
  cinProc :: coutProc N :: (List.range N).flatMap faProcs

/-- The top's own declarations (ports first, then `c`), for `N ≥ 1`. -/
def rippleDecls (N : Nat) : List Decl :=
  [{ name := "a", width := N, isInput := true },
   { name := "b", width := N, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := N, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := N + 1 }]

/-! ## The stages at symbolic `N` -/

/-- The declaration scope: `N` bound, its declared type `int` 32 bits. -/
def rippleScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment (with the evaluated packed-array geometry). -/
def rippleEnv (N : Int) : IEnv :=
  { rippleScope N with dims := dimTable (rippleScope N) ripple_fa.pdesign.decls }

/-- Declarations at raw widths (`|N-1| + 1`, `|N| + 1`). -/
def rippleDeclsRaw (wv wc : Nat) : List Decl :=
  [{ name := "a", width := wv, isInput := true },
   { name := "b", width := wv, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := wv, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := wc }]

/-- Every declaration of the top is 1-D: element width 1. -/
def rippleElems : List (String × Nat) :=
  [("a", 1), ("b", 1), ("cin", 1), ("s", 1), ("cout", 1), ("c", 1)]

theorem ripple_paramEnvH (N : Int) :
    ripple_fa.pdesign.paramEnvH {} [N] = .ok (rippleEnv N) := rfl

theorem ripple_decls (N : Int) :
    buildDecls (rippleEnv N) ripple_fa.pdesign.decls =
      .ok (rippleDeclsRaw ((N - 1).natAbs + 1) (N.natAbs + 1)) := by
  simp [ripple_fa.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    rippleEnv, rippleScope, List.lookup, rippleDeclsRaw, Gen2.except_ok_bind]

theorem ripple_elems (N : Int) :
    buildElems (rippleEnv N) ripple_fa.pdesign.decls = .ok rippleElems := by
  simp [ripple_fa.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, rippleEnv,
    rippleScope, List.lookup, rippleElems, Gen2.except_ok_bind]

/-- The static processes (as in `ripple_add`). -/
theorem ripple_static (N : Nat) (wv wc : Nat) :
    ripple_fa.pdesign.processes.map
        (instProcess2 ((rippleEnv N).withDecls (rippleDeclsRaw wv wc)) rippleElems) =
      [cinProc, coutProc N] := by
  sv2_inst_simp [ripple_fa.pdesign, rippleEnv, rippleScope, rippleDeclsRaw, rippleElems, cinProc,
    coutProc, dimTable, dimTableStep, PType.width_packed_cons, PDim.width, Int.lt_add_one_iff]

/-! ## One instance -/

/-- The instance prefix at a `Nat`-cast genvar: `g_bit[k].fa.`. -/
theorem fa_prefix (env : IEnv) (k : Nat) :
    faInst.prefix (env.bindVal "i" k) = .ok (faPfx k) := by
  simp [PInst.prefix, PInst.pathPrefix, faInst, IEnv.bindVal, List.lookup, faPfx,
    String.append_assoc, Functor.map, Except.map]

/-- The `full_adder` definition of the library (pinned by `rfl`). -/
def faDef : PDesign :=
  { name := "full_adder", params := [], localParams := [], enums := []
    decls := [{ name := "a", type := .packed [] (some 1), isInput := true },
              { name := "b", type := .packed [] (some 1), isInput := true },
              { name := "cin", type := .packed [] (some 1), isInput := true },
              { name := "s", type := .packed [] (some 1), isOutput := true },
              { name := "cout", type := .packed [] (some 1), isOutput := true }]
    processes :=
      [.assign "s" (.binary (.m0 .xor) (.binary (.m0 .xor) (.ident "a") (.ident "b")) (.ident "cin")),
       .assign "cout"
         (.binary (.m0 .or) (.binary (.m0 .and) (.ident "a") (.ident "b"))
           (.binary (.m0 .and) (.ident "cin") (.binary (.m0 .xor) (.ident "a") (.ident "b"))))]
    generates := [] }

theorem ripple_fa_plib : ripple_fa.plib = [faDef] := rfl

/-- The adder's parameter environment (no parameters; the scalar ports'
geometry). -/
def faEnv : IEnv := { dims := dimTable {} faDef.decls }

theorem fa_paramEnvH : faDef.paramEnvH {} [] = .ok faEnv := rfl

theorem fa_decls : buildDecls faEnv faDef.decls = .ok faDesign.decls.toList := by
  simp [faDef, faDesign, buildDecls, instDecl, PType.width_packed_nil]

def faElems : List (String × Nat) := [("a", 1), ("b", 1), ("cin", 1), ("s", 1), ("cout", 1)]

theorem fa_elems : buildElems faEnv faDef.decls = .ok faElems := by
  simp [faDef, faElems, buildElems]

/-- The child: `full_adder` from the library, at its (empty) parameter
point, instantiated alone — the closed `faDesign`, in any instantiating
scope, at any fuel and for any instantiating input ports (the adder has no
flop, so the clock-source rule leaves it unchanged, and drives `s` and
`cout` once each, so the one-driver rule does too). -/
theorem fa_child (env : IEnv) (F : Nat) (clocks : List String) :
    PDesign.childRec 1 ripple_fa.plib {} F clocks env faInst = .ok faDesign := by
  rw [ripple_fa_plib]
  simp only [PDesign.childRec, childInstOf]
  have hg : PInst.given env faDef faInst = .ok [] := by
    simp [PInst.given, faDef, faInst]
    rfl
  have hp : faDef.atPoint [] = .ok (faDef, []) := rfl
  have hfind : [faDef].find? (fun x => x.name == faInst.module) = some faDef := rfl
  rw [hfind]
  simp only [hg, hp]
  have hasm : faDef.assembleH faEnv faDesign.decls.toList [] faElems [] = faDesign := by
    simp only [PDesign.assembleH, faDesign, faDef, List.append_nil, List.map_nil]
    sv2_inst_simp [faElems, faEnv]
  -- The one-driver rule at the child (closed data): `s`, `cout` driven once.
  have hok : driversOk faDef.declNames faDef.inputNames faDesign.processes.toList = true := by
    decide
  rw [PDesign.instantiateRec_of_ok (depth := 0) (idecls := []) (gens := []) rfl fa_paramEnvH
    fa_decls fa_elems (by simp [faDef]), hasm]
  simp only [Res.ok_bind, PDesign.driverGuard, Design2.driverGuard_of_ok hok]
  simp [Design2.clockGuard, clockGuardProc, Process2.clock?, faDesign]

/-- **The instance at bit `k`, flattened** (any surrounding environment):
the adder's ports hoisted under `g_bit[k].fa.`, the five connections as
1-bit continuous assignments (no `resize` anywhere: every port is 1 bit and
so is every actual), then the adder's two assigns under the new names. -/
theorem fa_flatten (env : IEnv) (k : Nat) :
    flattenInst (env.bindVal "i" k) rippleElems (faPfx k) faInst faDesign =
      (faDecls k, faProcs k) := by
  have hports : (faDesign.decls.toList.filter fun dc => dc.isInput || dc.isOutput) =
      faDesign.decls.toList := rfl
  have hbare : bareInputs (env.bindVal "i" k) faDesign.decls.toList faInst.conns = [] := rfl
  have hstray : faInst.conns.filterMap (strayConn faDesign faDesign.decls.toList) = [] := rfl
  have hwire : faDesign.decls.toList.flatMap
      (connProcs (env.bindVal "i" k) rippleElems (faPfx k) faInst.conns) =
      (faProcs k).take 5 := by
    simp only [faDesign, faInst, connProcs, List.toList_toArray, List.flatMap_cons,
      List.flatMap_nil, List.find?, PConn.port, faProcs]
    sv2_inst_simp [portInOk, PExpr.portSafe, portOut, rippleElems]
  simp only [flattenInst, hports, hbare, hstray, List.nil_append]
  rw [hwire]
  simp [faDesign, instBodyProc, Process2.clock?, Process2.rename, Lhs2.rename, Expr2.rename,
    faProcs, Decl.hoist, faDecls]

/-- One iteration of the generate loop: the singleton body `[fa]` at the
`Nat`-cast genvar `k`. -/
theorem fa_iter (env : IEnv) (F : Nat) (clocks : List String) (k : Nat) :
    expandListH (PDesign.childRec 1 ripple_fa.plib {} F clocks) (env.bindVal "i" k) rippleElems F
        [.inst faInst] = .ok (faDecls k, faProcs k) := by
  apply expandListH_singleton_ok rfl
  rw [GenItem.expandH_inst, instExpandH_of (fa_prefix env k) (fa_child _ F clocks), fa_flatten]

/-- The generate expansion at the surface fuel: the instance family, bit by
bit. -/
theorem ripple_gens (N : Nat) (wv wc : Nat) (clocks : List String) :
    expandListH (PDesign.childRec 1 ripple_fa.plib {} (PDesign.surfaceFuel [(N : Int)]) clocks)
        ((rippleEnv N).withDecls (rippleDeclsRaw wv wc)) rippleElems
        (PDesign.surfaceFuel [(N : Int)]) ripple_fa.pdesign.generates =
      .ok ((List.range N).flatMap faDecls, (List.range N).flatMap faProcs) := by
  rw [ripple_fa_generates]
  apply expandListH_singleton_ok rfl
  rw [GenItem.expandH_genFor_ascending_flatMap (N := (N : Int))
    (f := fun v => (faDecls v.toNat, faProcs v.toNat)) (evalInt_int 0)
    (fun i => by simp [rippleEnv, rippleScope, List.lookup])
    (fun i => by simp [evalInt, rippleEnv, rippleScope, List.lookup])
    (by
      have := Nat.le_mul_self (N + 2)
      simp [PDesign.surfaceFuel]
      omega)
    (fun v hv _ => by
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hv
      simpa using fa_iter _ _ clocks k)]
  simp [intRange_zero, List.flatMap_map]

/-! ## The one-driver rule at symbolic `N`

After flattening, the top's own signals are driven once per bit
(`Hier2.lean`, "Drivers"): `c[0]` by the carry-in, `cout` by `c[N]`'s
assign, and for each `i < N` the instance outputs `s[i]` and `c[i+1]` —
pairwise disjoint windows, no input port among them, no procedural process.
The hoisted `g_bit[i].fa.*` signals are not the top's (they are checked one
level down, `fa_child`): their names are too long to be one of the top's. -/

/-- The top's declaration names. -/
def rippleNames : List String := ["a", "b", "cin", "s", "cout", "c"]

/-- The top's input ports. -/
def rippleInputs : List String := ["a", "b", "cin"]

theorem ripple_declNames : ripple_fa.pdesign.declNames = rippleNames := rfl

theorem ripple_inputNames : ripple_fa.pdesign.inputNames = rippleInputs := rfl

/-- Every hierarchical name of bit `k` is at least 11 characters long. -/
theorem faPfx_length (k : Nat) (x : String) : 11 ≤ (faPfx k ++ x).length := by
  have h1 : "g_bit[".length = 6 := by decide
  have h2 : "].fa.".length = 5 := by decide
  simp [faPfx, String.length_append, h1, h2]
  omega

/-- ... so it is none of the top's names. -/
theorem rippleNames_faPfx (k : Nat) (x : String) : rippleNames.contains (faPfx k ++ x) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [List.contains_iff_mem] at h
  have hshort : ∀ y ∈ rippleNames, y.length < 11 := by decide
  have := hshort _ h
  have := faPfx_length k x
  omega

/-- The windows bit `k` drives on the top's signals: `s[k]`, `c[k+1]`. -/
def faWins (k : Nat) : List DrvWin := [("s", some (k, 1)), ("c", some (k + 1, 1))]

theorem fa_driverWins (k : Nat) : driverWins rippleNames (faProcs k) = faWins k := by
  have hs : rippleNames.contains "s" = true := by decide
  have hc : rippleNames.contains "c" = true := by decide
  simp only [faProcs, driverWins_cons, driverWins_nil, Process2.drvWins, Lhs2.drvWins,
    List.filter_cons, List.filter_nil, rippleNames_faPfx, hs, hc, Bool.false_eq_true,
    ↓reduceIte, List.nil_append, List.cons_append, List.append_nil, faWins]

/-- The top's continuous-driver windows, for every `N`. -/
theorem ripple_driverWins (N : Nat) :
    driverWins rippleNames (rippleFaProcs N) =
      [("c", some (0, 1)), ("cout", none)] ++ (List.range N).flatMap faWins := by
  have hc : rippleNames.contains "c" = true := by decide
  have ho : rippleNames.contains "cout" = true := by decide
  simp only [rippleFaProcs, driverWins_cons, driverWins_flatMap, fa_driverWins, cinProc,
    coutProc, Process2.drvWins, Lhs2.drvWins, List.filter_cons, List.filter_nil, hc, ho,
    ↓reduceIte, List.cons_append, List.nil_append]

/-- Pairwise disjoint: `s[j]`/`s[k]` and `c[j+1]`/`c[k+1]` for `j < k`, and
`c[0]` below every `c[k+1]`. -/
theorem ripple_wins_disjoint (N : Nat) :
    ([("c", some (0, 1)), ("cout", none)] ++ (List.range N).flatMap faWins).Pairwise
      (fun (a b : DrvWin) => a.overlaps b = false) := by
  rw [List.pairwise_append, List.pairwise_flatMap]
  refine ⟨by decide, ⟨fun k _ => ?_, ?_⟩, ?_⟩
  · simp [faWins, DrvWin.overlaps]
  · refine List.pairwise_lt_range.imp ?_
    intro j k hjk x hx y hy
    simp only [faWins, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [DrvWin.overlaps] <;> omega
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [List.mem_flatMap, List.mem_range, faWins, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    obtain ⟨k, _, hb⟩ := hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [DrvWin.overlaps]

/-- No procedural process: every flattened process is a continuous assign. -/
theorem ripple_procWrites (N : Nat) : (rippleFaProcs N).flatMap Process2.procWrites = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  simp only [rippleFaProcs, List.mem_cons, List.mem_flatMap, List.mem_range] at hp
  rcases hp with rfl | rfl | ⟨k, _, hp⟩
  · rfl
  · rfl
  · simp only [faProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The one-driver rule holds for every `N`.** -/
theorem ripple_fa_driversOk (N : Nat) :
    driversOk rippleNames rippleInputs (rippleFaProcs N) = true := by
  apply driversOk_of_continuous (ripple_procWrites N)
  · rw [ripple_driverWins]
    exact ripple_wins_disjoint N
  · rw [ripple_driverWins]
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
      List.mem_range, faWins] at hw
    rcases hw with (rfl | rfl) | ⟨k, _, (rfl | rfl)⟩ <;> rfl

/-- **`instantiateH` at symbolic `N`**: succeeds, and is the assembled
flattened design (the top's one-driver rule passing, `ripple_fa_driversOk`). -/
theorem ripple_fa_instantiateH (N : Nat) :
    ripple_fa.pdesign.instantiateH ripple_fa.plib [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (ripple_fa.pdesign.assembleH (rippleEnv N)
        (rippleDeclsRaw (((N : Int) - 1).natAbs + 1) ((N : Int).natAbs + 1))
        ((List.range N).flatMap faDecls) rippleElems ((List.range N).flatMap faProcs)) := by
  apply PDesign.instantiateH_of_rec (PDesign.instantiateRec_of_ok (depth := 1) rfl
    (ripple_paramEnvH N) (ripple_decls N) (ripple_elems N) (ripple_gens N _ _ _))
  have hps : (ripple_fa.pdesign.assembleH (rippleEnv N)
        (rippleDeclsRaw (((N : Int) - 1).natAbs + 1) ((N : Int).natAbs + 1))
        ((List.range N).flatMap faDecls) rippleElems
        ((List.range N).flatMap faProcs)).processes.toList = rippleFaProcs N := by
    rw [PDesign.assembleH_processes, ripple_static]
    simp [rippleFaProcs, ripple_fa.pdesign]
  rw [hps, ripple_declNames, ripple_inputNames]
  exact ripple_fa_driversOk N

/-! ## The acceptance theorems -/

/-- **The flattened process list, for every `N`** (no unrolling): `c[0] =
cin`, `cout = c[N]`, then for each `i < N` the instance `g_bit[i].fa`'s
five connections and two assigns. -/
theorem ripple_fa_processes (N : Nat) :
    (ripple_fa.sem N).processes.toList = rippleFaProcs N := by
  show (ripple_fa.pdesign.instantiateHD2 ripple_fa.plib [(N : Int)]).processes.toList = _
  rw [PDesign.instantiateHD2_of_ok (ripple_fa_instantiateH N), PDesign.assembleH_processes,
    ripple_static]
  simp [rippleFaProcs, ripple_fa.pdesign]

/-- **Membership characterization, both directions**: a process of the
flattened adder is the carry-in, the carry-out, or one of bit `i`'s seven
instance processes for some `i < N`. -/
theorem mem_ripple_fa_processes (N : Nat) (p : Process2) :
    p ∈ (ripple_fa.sem N).processes.toList ↔
      p = cinProc ∨ p = coutProc N ∨ ∃ i < N, p ∈ faProcs i := by
  rw [ripple_fa_processes]
  simp [rippleFaProcs]

/-- The process count: `7N + 2`. -/
theorem ripple_fa_processes_length (N : Nat) :
    (ripple_fa.sem N).processes.toList.length = 7 * N + 2 := by
  rw [ripple_fa_processes]
  simp only [rippleFaProcs, faProcs, List.length_cons, List.length_flatMap, List.length_nil,
    List.map_const', List.sum_replicate_nat, List.length_range]
  omega

/-- **The flattened declarations** for `N ≥ 1`: the top's six (`a`, `b`,
`s` of `N` bits, `cin`/`cout` 1 bit, the carry chain `c` of `N + 1` bits),
then each instance's five 1-bit port signals under `g_bit[i].fa.`. Ports of
the flattened design are exactly the top's: hoisted signals carry no port
flag. -/
theorem ripple_fa_decls (N : Nat) (hN : 1 ≤ N) :
    (ripple_fa.sem N).decls.toList = rippleDecls N ++ (List.range N).flatMap faDecls := by
  show (ripple_fa.pdesign.instantiateHD2 ripple_fa.plib [(N : Int)]).decls.toList = _
  rw [PDesign.instantiateHD2_of_ok (ripple_fa_instantiateH N), PDesign.assembleH_decls]
  have hv : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hc : (N : Int).natAbs = N := Int.natAbs_natCast N
  rw [hv, hc]
  rfl

/-! ## Concrete agreement (non-vacuity at the default `N = 4`) -/

#guard (ripple_fa.sem 4).processes.size == 30
#guard (ripple_fa.sem 4).decls.toList.map (·.width) == [4, 4, 1, 4, 1, 5] ++ List.replicate 20 1
#guard (ripple_fa.sem 4).namesNodup
#guard (((ripple_fa.sem 4).decls.toList.drop 6).take 5).map (·.name) ==
  ["g_bit[0].fa.a", "g_bit[0].fa.b", "g_bit[0].fa.cin", "g_bit[0].fa.s", "g_bit[0].fa.cout"]
-- 9 + 5 + 1 = 15 and 15 + 15 + 0 = 30 ≡ 14 (carry out 1) at N = 4.
#guard (match run2 (ripple_fa.sem 4) σ_src 1000
          [[("a", .ofNat 4 9), ("b", .ofNat 4 5), ("cin", .ofNat 1 1)],
           [("a", .ofNat 4 15), ("b", .ofNat 4 15), ("cin", .ofNat 1 0)]] with
        | .ok [s1, s2] =>
            (SvState.lookup s1 "s").map LVec.toBinString == some "1111" &&
            (SvState.lookup s1 "cout").map LVec.toBinString == some "0" &&
            (SvState.lookup s2 "s").map LVec.toBinString == some "1110" &&
            (SvState.lookup s2 "cout").map LVec.toBinString == some "1"
        | _ => false)

end Examples.«system-verilog».ripple_fa.gen
