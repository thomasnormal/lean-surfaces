import Examples.«system-verilog».comb_case.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombProcTactic

/-!
# `sv_equations?` on a `case` (WP-G S3a)

What the player sees. A plain `case` is stated as ONE fold, not as a chain of `if`s:

    st.boolAt "y" k = XF.caseSel w (subject bits) [([pattern bits], arm bits), …] (default bits) k

`XF.caseSel` returns the arm of the FIRST item one of whose patterns equals the subject (compared at the
subject's width `w`), else the default; `XF.caseSel_cons` unfolds one item. This is the one place where the
printed shape of a procedural statement is a fold and not the `if` the statement stands for (an `if` and a
`?:` print as `if`): a table of 256 items must stay one list, which `XF.caseSel_table` turns into a lookup
in a table of numbers (`comb_proof.lean`). The literals are the items' own bits, bit 0 first; a comma list is
ONE item with several patterns (`case_multi`: `2'd0, 2'd3`); a repeated pattern is kept (the second `2'd1`
is never reached). The subject is read once: its bits are a function of the signals (`case_gen`: `s ^ a[i]`).
Pinned verbatim.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_case.gen

namespace Examples.«system-verilog».comb_case.comb_hint

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < Int.natAbs 3 + 1 →
    st.boolAt "y" k =
      XF.caseSel (Int.natAbs 1 + 1) (fun x => st.boolAt "s" x)
        [([{ bits := #[Logic.l0, Logic.l0] }.boolAt], fun x => st.boolAt "a" x),
          ([{ bits := #[Logic.l1, Logic.l0] }.boolAt], fun x => st.boolAt "b" x),
          ([{ bits := #[Logic.l0, Logic.l1] }.boolAt], fun x => st.boolAt "c" x)]
        (fun x => st.boolAt "d" x) k
  known_y_plain_0 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown_1] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 2
  [inputsKnown_2] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_3] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_4] ⊢ ∃ v, st.lookup "c" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_5] ⊢ ∃ v, st.lookup "d" = some v ∧ v.allKnown = true ∧ v.width = 4
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example {d' : Design2} (hl : case_mux.sem.lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < Int.natAbs 3 + 1 →
    st.boolAt "y" k =
      XF.caseSel (Int.natAbs 1 + 1) (fun x => st.boolAt "x" x)
        [([{ bits := #[Logic.l0, Logic.l0] }.boolAt], fun x =>
            { bits := #[Logic.l1, Logic.l0, Logic.l0, Logic.l1] }.boolAt x),
          ([{ bits := #[Logic.l1, Logic.l0] }.boolAt], fun x =>
            { bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l0] }.boolAt x),
          ([{ bits := #[Logic.l0, Logic.l1] }.boolAt], fun x =>
            { bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l1] }.boolAt x)]
        (fun x => { bits := #[Logic.l1, Logic.l0, Logic.l0, Logic.l0] }.boolAt x) k
  known_y_plain_0 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = 2
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example {d' : Design2} (hl : case_lut.sem.lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < Int.natAbs 3 + 1 →
    st.boolAt "y" k =
      XF.caseSel (Int.natAbs 1 + 1) (fun x => st.boolAt "s" x)
        [([{ bits := #[Logic.l0, Logic.l0] }.boolAt, { bits := #[Logic.l1, Logic.l1] }.boolAt], fun x =>
            st.boolAt "a" x),
          ([{ bits := #[Logic.l1, Logic.l0] }.boolAt], fun x => st.boolAt "b" x),
          ([{ bits := #[Logic.l1, Logic.l0] }.boolAt], fun x => !st.boolAt "a" x)]
        (fun x => st.boolAt "a" x ^^ st.boolAt "b" x) k
  known_y_plain_0 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown_1] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 2
  [inputsKnown_2] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_3] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = 4
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example {d' : Design2} (hl : case_multi.sem.lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_g_bit_0 : ∀ (i : Nat),
  i < N →
    st.boolAt "y" i =
      XF.caseSel 1 (fun x => st.boolAt "s" x ^^ st.boolAt "a" (i + x))
        [([{ bits := #[Logic.l0] }.boolAt], fun x => st.boolAt "b" (i + x))] (fun x => !st.boolAt "b" (i + x)) 0
  known_y_g_bit_0 : ∀ (i : Nat), i < N → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" i
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_g_bit_0    known_y_1 := known_y_g_bit_0
  [inRange] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [bitRead] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs
  [cover] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i < ↑(↑N + -1).natAbs + 1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) {d'} (hl : (case_gen.sem N).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

end Examples.«system-verilog».comb_case.comb_hint
