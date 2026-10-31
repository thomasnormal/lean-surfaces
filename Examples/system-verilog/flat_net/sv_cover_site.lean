import Examples.«system-verilog».flat_net.p_gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic

/-!
# `sv_cover` with a SITE as the witness (`flat_net_p`, WP-P3b)

`flat_net_p.sv` is flat (26 plain sites, no generate loop) but has a parameter `K`, so the flat-netlist
fast path does not apply: the instantiated design mentions the free variable `K`, `sv_equations` normalizes
its obligations, and every read of a net leaves a coverage goal whose witness is a SITE,

    ∃ b, (b = site₀ ∨ b = site₁ ∨ … ∨ b = site₂₅) ∧ b.site.tgt.name = "c" ∧ <the write window holds the bit>

(the input-bit reads `4 < 12 ∨ ∃ b, …`). Before WP-P3b `sv_cover` searched the disjunction one `Or.inr` at a
time under a budget of 250 attempts and failed at this size (33 goals of a 26-site netlist were left); the
player wrote the position of the writer in the disjunction by hand (`Or.inr (Or.inr (… (Or.inl rfl)))`). It now
picks the writer by NAME (the site whose target is the signal the goal states), builds the membership proof, and
closes the rest. The proof below has no hand-written witness.

The heartbeat limit is raised (`2000000`): this design takes the normalization route of `sv_equations` (the very
cost the flat-netlist fast path removes for a parameter-free design: `svgolf/PROVING.md`, sections 11 and 12).

Build: `lake build Examples.«system-verilog».flat_net.sv_cover_site`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».flat_net.p_gen

namespace Examples.«system-verilog».flat_net.sv_cover_site

set_option maxHeartbeats 2000000 in
/-- Every obligation of `sv_equations` that is left (the coverage of every read, 26 sites) is closed by
`sv_cover`, the three input premises by `inKnown_ofBitVec`. -/
theorem flat_p (K : Nat) (hc : CombDesign (flat_net_p.sem K)) (ha : Acyclic (flat_net_p.sem K)) :
    flat_net_p.sem K ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec 12) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) → True := by
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · trivial
  all_goals first
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- info: 'Examples.«system-verilog».flat_net.sv_cover_site.flat_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_p

end Examples.«system-verilog».flat_net.sv_cover_site
