import LeanModels.SoftFloat.Binary.Fields

/-!
# The rounding certificate, and the rounding stage of a datapath

`certNF f N D s c` checks, with `+ - *` and comparisons only (no division, no `log2`), that the bit pattern `c` is
the roundTiesToEven result of the exact magnitude `N / D` units with sign `s`, overflow included:
`certNF_iff : unitsResultF f s N D = c ↔ certNF f N D s c = true` for ANY exact positive fraction (a quotient, a
product, a sum, a square root's bracket...).

`fin_cert_abs`, `ovf_cert_abs` (with `cert_fin_grid`, `cert_inf_grid`, `fields_gridF`) are the rounding STAGE of a
datapath, stated over its abstract quantities: a quotient `qm` of `M0` by `nb` with sticky bit `st0`, a shift `sh`, a
grid exponent `j`, the rounded grid mantissa `z`, the packed magnitude `mag` (round by incrementing the packed
`{exponent, fraction}`, subnormal shift with sticky, overflow to infinity); any exact `N / D` related to the quotient
by `N·(nb·2^(sh+1)) = D·(2^j·M0)` is certified. A multiplier, adder, fused multiply-add or square root that rounds the
same way uses them unchanged.

Ported from svGolf's fdivp reference proof (sections `CertF`, `DpM`), the maintainers' text.
-/

namespace LeanModels.SoftFloat.Binary

open NatFacts

/-- **The interval characterizes the roundTiesToEven magnitude, for every pattern magnitude**
`uF f E T` (`T < 2^t`; no threshold, no sign), in every format. -/
theorem claimF (f : Format) (s : Bool) (N D E T : Nat) (hD : 0 < D) (hT : T < 2 ^ f.t) :
    (uF f E T = roundUnits f .nearestTiesToEven s N D) ↔
      ((uF f E T = 0 ∨ leB (decide (T % 2 = 0)) (D * (2 * uF f E T - dnF E T)) (2 * N)) ∧
        leB (decide (T % 2 = 0)) (2 * N) (D * (2 * uF f E T + 2 ^ (E - 1)))) := by
  have hp1 : 2 ^ (f.p - 1) = 2 ^ f.t := rfl
  have hp2 := two_pow_t f
  have hB := Nat.two_pow_pos f.t
  by_cases hE0 : E = 0
  · subst hE0
    by_cases hT0 : T = 0
    · subst hT0
      have hu : uF f 0 0 = 0 := rfl
      have hd : dnF 0 0 = 1 := rfl
      have h1 : (2 : Nat) ^ (0 - 1) = 1 := rfl
      have h2 : decide ((0 : Nat) % 2 = 0) = true := rfl
      rw [hu, hd, h1, h2]
      exact rne_eq_iff f s N D 0 1 1 true hD Nat.one_pos Nat.one_pos (zero_rep _)
        ⟨1, 0, by omega, rfl⟩ (fun h => absurd rfl h) (fun w _ => by omega)
        (fun h => absurd rfl h)
        ⟨fun _ => rfl, fun _ => by simp [EvenSig]⟩
    · have hu : uF f 0 T = T * 2 ^ 0 := by simp [uF]
      have hd : dnF 0 T = if T = 2 ^ (f.p - 1) ∧ 0 < 0 then 2 ^ (0 - 1) else 2 ^ 0 := by
        simp [dnF]
      exact rne_eq_iff_canon f s N D T 0 (uF f 0 T) (2 ^ (0 - 1)) (dnF 0 T)
        (decide (T % 2 = 0)) hD (by omega) (by omega) (fun h => absurd h (Nat.lt_irrefl 0)) hu
        rfl hd (by simp)
  · have hu : uF f E T = (2 ^ f.t + T) * 2 ^ (E - 1) := by simp [uF, hE0]
    have hd : dnF E T = if 2 ^ f.t + T = 2 ^ (f.p - 1) ∧ 0 < E - 1 then 2 ^ (E - 1 - 1)
        else 2 ^ (E - 1) := by
      rw [hp1]
      unfold dnF
      by_cases hb : 2 ≤ E ∧ T = 0
      · rw [if_pos hb, if_pos (by omega)]
      · rw [if_neg hb, if_neg (by omega)]
    exact rne_eq_iff_canon f s N D (2 ^ f.t + T) (E - 1) (uF f E T) (2 ^ (E - 1)) (dnF E T)
      (decide (T % 2 = 0)) hD (by omega) (by omega) (fun _ => by omega) hu rfl hd
      (by have := two_pow_t_even f; simp only [decide_eq_true_eq]; omega)

/-- `cert16 a b c` with the exact quotient `N / D` (in units) and the XOR sign `s` abstracted.
`(2^(p+1) - 1) · 2^(2·emax - 2)` is the overflow threshold in units (binary16: `4095 · 2^28`). -/
def certNF (f : Format) (N D : Nat) (s : Bool) (c : BitVec f.k) : Bool :=
  (signF f c == s) &&
    (if expF f c = 2 ^ f.w - 1 then
      fracF f c == 0 && decide (D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N)
     else decide (N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) &&
      (uF f (expF f c) (fracF f c) == 0 ||
        (if fracF f c % 2 == 0
          then decide (D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) ≤ 2 * N)
          else decide (D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) < 2 * N))) &&
      (if fracF f c % 2 == 0
        then decide (2 * N ≤ D * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)))
        else decide (2 * N < D * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)))))

/-- The certificate for `E = 2^w - 1`: the infinity pattern, at or above the threshold. -/
theorem certNF_inf (f : Format) (N D : Nat) (s : Bool) (c : BitVec f.k)
    (hE : expF f c = 2 ^ f.w - 1) :
    certNF f N D s c = true ↔
      (signF f c = s ∧ fracF f c = 0 ∧
        D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N) := by
  unfold certNF
  rw [if_pos hE]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

/-- The certificate for `E ≠ 2^w - 1`: below the threshold and inside the pattern's interval. -/
theorem certNF_fin (f : Format) (N D : Nat) (s : Bool) (c : BitVec f.k)
    (hE : expF f c ≠ 2 ^ f.w - 1) :
    certNF f N D s c = true ↔
      (signF f c = s ∧ N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ∧
        (uF f (expF f c) (fracF f c) = 0 ∨
          leB (decide (fracF f c % 2 = 0))
            (D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c))) (2 * N)) ∧
        leB (decide (fracF f c % 2 = 0)) (2 * N)
          (D * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)))) := by
  unfold certNF
  rw [if_neg hE]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, ite_decide_leB, decide_eq_true_eq,
    and_assoc]

/-- The roundTiesToEven result of an exact positive quotient `N / D`, measured in units of
`2^-scale`, with sign `s`: the encoder applied to `roundUnits`, or the infinity on overflow.
This is `round f .nearestTiesToEven s` after the unit scaling. -/
def unitsResultF (f : Format) (s : Bool) (N D : Nat) : BitVec f.k :=
  if roundUnits f .nearestTiesToEven s N D ≤ f.maxUnits
  then finite f s (roundUnits f .nearestTiesToEven s N D) else infinity f s

/-- The overflow threshold of the spec in units, in the certificate's form. -/
theorem thr_iff (f : Format) (N D : Nat) :
    D * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) ≤ 2 * N ↔
      D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N := by
  have he := emax_pos f
  have hP := Nat.two_pow_pos f.p
  obtain ⟨J, hJ⟩ : ∃ J, 2 * f.emax - 2 = J := ⟨_, rfl⟩
  have e1 : 2 * f.emax - 1 = J + 1 := by omega
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ f.p = Q + 1 := ⟨2 ^ f.p - 1, by omega⟩
  have e2 : 2 ^ (f.p + 1) - 1 = 2 * Q + 1 := by rw [Nat.pow_succ]; omega
  have e3 : 2 ^ f.p - 1 = Q := by omega
  rw [maxUnits_eq, e1, hJ, e2, e3, Nat.pow_succ]
  have h : D * (2 * (Q * (2 ^ J * 2)) + 2 ^ J * 2) = 2 * (D * (2 * Q + 1) * 2 ^ J) := by grind
  rw [h]; omega

/-- **The certificate characterizes the rounded quotient**, for any exact quotient `N / D`,
in every format. -/
theorem certNF_iff (f : Format) (N D : Nat) (hD : 0 < D) (s : Bool) (c : BitVec f.k) :
    unitsResultF f s N D = c ↔ certNF f N D s c = true := by
  have hEl : expF f c < 2 ^ f.w := expF_lt f c
  have hTl : fracF f c < 2 ^ f.t := fracF_lt f c
  have hw4 := four_le_two_pow_w f
  have hc := eq_fieldsF f c
  have key : ∀ (s' : Bool) (E' T' : Nat), E' < 2 ^ f.w → T' < 2 ^ f.t →
      (fields f s' E' T' = c ↔
        s' = signF f c ∧ E' = expF f c ∧ T' = fracF f c) := by
    intro s' E' T' hE' hT'
    constructor
    · intro h
      exact fields_injF f s' (signF f c) E' (expF f c) T' (fracF f c) hE' hEl hT' hTl (h.trans hc)
    · rintro ⟨h1, h2, h3⟩
      rw [h1, h2, h3]
      exact hc.symm
  have hovf := rne_overflow_iff f s N D hD
  have hthr : f.maxUnits < roundUnits f .nearestTiesToEven s N D ↔
      D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N := by
    rw [hovf]; exact thr_iff f N D
  have hrep := rne_rep f s N D
  unfold unitsResultF
  by_cases hth : D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N
  · -- overflow: the result is the infinity
    have hgt := hthr.mpr hth
    rw [if_neg (Nat.not_le.mpr hgt)]
    have hinf : infinity f s = fields f s (2 ^ f.w - 1) 0 := rfl
    rw [hinf, key s (2 ^ f.w - 1) 0 (by omega) (Nat.two_pow_pos _)]
    by_cases hE31 : expF f c = 2 ^ f.w - 1
    · rw [certNF_inf f N D s c hE31]
      constructor
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1.symm, h3.symm, hth⟩
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1.symm, hE31.symm, h2.symm⟩
    · constructor
      · rintro ⟨-, h2, -⟩
        exact absurd h2.symm hE31
      · intro h
        have := ((certNF_fin f N D s c hE31).mp h).2.1
        omega
  · -- below the threshold: the result is the encoding of `roundUnits`
    have hle : roundUnits f .nearestTiesToEven s N D ≤ f.maxUnits :=
      Nat.not_lt.mp fun h => hth (hthr.mp h)
    rw [if_pos hle]
    obtain ⟨E0, T0, hE0, hT0, hu0⟩ := uF_of_rep f _ hle hrep
    have hf : finite f s (roundUnits f .nearestTiesToEven s N D) = fields f s E0 T0 := by
      rw [hu0]; exact finite_uF f s E0 T0 hE0 hT0
    rw [hf, key s E0 T0 (by omega) hT0]
    by_cases hE31 : expF f c = 2 ^ f.w - 1
    · constructor
      · rintro ⟨-, h2, -⟩
        omega
      · intro h
        exact absurd ((certNF_inf f N D s c hE31).mp h).2.2 hth
    · rw [certNF_fin f N D s c hE31]
      have hD' := claimF f s N D (expF f c) (fracF f c) hD hTl
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hu : uF f (expF f c) (fracF f c) =
            roundUnits f .nearestTiesToEven s N D := by
          rw [← h2, ← h3, ← hu0]
        exact ⟨h1.symm, by omega, hD'.mp hu⟩
      · rintro ⟨h1, -, h3⟩
        have hu := hD'.mpr h3
        have hfe : fields f s (expF f c) (fracF f c) = fields f s E0 T0 := by
          rw [← finite_uF f s (expF f c) (fracF f c) (by omega) hTl, hu, hf]
        obtain ⟨-, h2, h3'⟩ := fields_injF f s s _ _ _ _ hEl (by omega) hTl hT0 hfe
        exact ⟨h1.symm, h2.symm, h3'.symm⟩

/-- `N·S = D·T` for the datapath, `S = nb·2^(sh+1)`, `T = 2^j·M0`, `M0 = 2^(p+adj)·(ma·2^lza)`, `nb = mb·2^lzb`,
`e = xa - xb + scale` and `E = xa - lza - xb + lzb + emax - adj` the true result exponent; `j + 1 = E + sh`. -/
theorem scale_id' (ma mb lza lzb xa xb adj j sh emax T : Nat) (e E : Int)
    (he : e = (xa : Int) - xb + (emax + T - 1))
    (hE : E = (xa : Int) - lza - xb + lzb + emax - adj)
    (hjs : (j : Int) + 1 = E + sh) :
    (ma * 2 ^ e.toNat) * (mb * 2 ^ lzb * 2 ^ (sh + 1)) =
      (mb * 2 ^ (-e).toNat) * (2 ^ j * (2 ^ (T + 1 + adj) * (ma * 2 ^ lza))) := by
  have hp : e.toNat + lzb + (sh + 1) = (-e).toNat + j + (T + 1 + adj) + lza := by omega
  have l : (ma * 2 ^ e.toNat) * (mb * 2 ^ lzb * 2 ^ (sh + 1)) =
      ma * mb * 2 ^ (e.toNat + lzb + (sh + 1)) := by
    simp only [Nat.pow_add]
    generalize 2 ^ e.toNat = A; generalize 2 ^ lzb = B; generalize 2 ^ sh = C; generalize 2 ^ 1 = D
    ac_rfl
  have r : (mb * 2 ^ (-e).toNat) * (2 ^ j * (2 ^ (T + 1 + adj) * (ma * 2 ^ lza))) =
      ma * mb * 2 ^ ((-e).toNat + j + (T + 1 + adj) + lza) := by
    simp only [Nat.pow_add]
    generalize 2 ^ (-e).toNat = A; generalize 2 ^ j = B; generalize 2 ^ T = C; generalize 2 ^ 1 = D
    generalize 2 ^ adj = E'; generalize 2 ^ lza = F
    ac_rfl
  rw [l, r, hp]

theorem fields_gridF (f : Format) (j z Ec Tc : Nat)
    (h : (Ec = 0 ∧ j = 0 ∧ z = Tc ∧ Tc < 2 ^ f.t) ∨
         (1 ≤ Ec ∧ j + 1 = Ec ∧ z = 2 ^ f.t + Tc ∧ Tc < 2 ^ f.t) ∨
         (1 ≤ Ec ∧ j + 2 = Ec ∧ z = 2 * 2 ^ f.t ∧ Tc = 0)) :
    uF f Ec Tc = z * 2 ^ j ∧
    (dnF Ec Tc = 2 ^ j ∨ (dnF Ec Tc * 2 = 2 ^ j ∧ z = 2 ^ f.t ∧ 1 ≤ j)) ∧
    (2 ^ (Ec - 1) = 2 ^ j ∨ (2 ^ (Ec - 1) = 2 * 2 ^ j ∧ z = 2 * 2 ^ f.t)) ∧
    (Tc % 2 = 0 ↔ z % 2 = 0) := by
  have hev := two_pow_t_even f
  rcases h with ⟨hE, hj, hz, hT⟩ | ⟨hE1, hj, hz, hT⟩ | ⟨hE1, hj, hz, hT⟩
  · subst hE hj hz
    refine ⟨?_, Or.inl ?_, Or.inl ?_, Iff.rfl⟩
    · simp [uF]
    · simp [dnF]
    · simp
  · have hj' : j = Ec - 1 := by omega
    subst hj'
    have hu : uF f Ec Tc = z * 2 ^ (Ec - 1) := by
      unfold uF
      rw [if_neg (show ¬ (Ec = 0) by omega), hz]
    refine ⟨hu, ?_, Or.inl rfl, by omega⟩
    by_cases hd : 2 ≤ Ec ∧ Tc = 0
    · right
      unfold dnF
      rw [if_pos hd]
      obtain ⟨k, hk⟩ : ∃ k, Ec - 1 = k + 1 := ⟨Ec - 2, by omega⟩
      have : Ec - 1 - 1 = k := by omega
      rw [this, hk, Nat.pow_succ]
      exact ⟨rfl, by omega, by omega⟩
    · left
      unfold dnF
      rw [if_neg hd]
  · have hj' : Ec = j + 2 := by omega
    subst hj' hT hz
    have h1 : j + 2 - 1 = j + 1 := by omega
    refine ⟨?_, Or.inl ?_, Or.inr ⟨?_, rfl⟩, by omega⟩
    · unfold uF
      rw [if_neg (show ¬ (j + 2 = 0) by omega), h1, Nat.pow_succ]
      rw [Nat.add_zero, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm (2 ^ f.t) 2]
    · unfold dnF
      rw [if_pos (show 2 ≤ j + 2 ∧ (0 : Nat) = 0 by omega)]
      have : j + 2 - 1 - 1 = j := by omega
      rw [this]
    · rw [h1, Nat.pow_succ, Nat.mul_comm]

/-- **The certificate for a finite pattern on the grid.** `c` has fields `(Ec, Tc)` in one of three shapes (subnormal,
normal, normal after the carry), `u = z·2^j`; `N·(nb·M) = D·(2^j·M0)`; `qm` is the quotient of `M0` by `nb`, `st0` its
inexactness; the rounding core relates `z`, `qm`, `M`. -/
theorem cert_fin_grid (f : Format) (N D nb M qm M0 z j : Nat) (st0 : Prop) (c : BitVec f.k) (s : Bool)
    (hD : 0 < D) (hnb : 0 < nb) (hM : 0 < M)
    (hrel : N * (nb * M) = D * (2 ^ j * M0))
    (hq1 : nb * qm ≤ M0) (hq2 : M0 < nb * qm + nb)
    (hst1 : st0 → nb * qm < M0) (hst2 : ¬ st0 → M0 = nb * qm)
    (hcT : st0 → ((z = 0 ∨ (2 * z - 1) * M ≤ 2 * qm) ∧ 2 * qm + 2 ≤ (2 * z + 1) * M))
    (hcF : ¬ st0 → ((z = 0 ∨ ((2 * z - 1) * M ≤ 2 * qm ∧ (z % 2 = 1 → (2 * z - 1) * M < 2 * qm))) ∧
                    2 * qm ≤ (2 * z + 1) * M ∧ (z % 2 = 1 → 2 * qm < (2 * z + 1) * M)))
    (hfloor : z = 2 ^ f.t → 1 ≤ j → z * M ≤ qm)
    (hsign : signF f c = s) (hE : expF f c ≠ 2 ^ f.w - 1)
    (hshape : (expF f c = 0 ∧ j = 0 ∧ z = fracF f c ∧ fracF f c < 2 ^ f.t) ∨
         (1 ≤ expF f c ∧ j + 1 = expF f c ∧ z = 2 ^ f.t + fracF f c ∧ fracF f c < 2 ^ f.t) ∨
         (1 ≤ expF f c ∧ j + 2 = expF f c ∧ z = 2 * 2 ^ f.t ∧ fracF f c = 0))
    (hC0 : N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) :
    certNF f N D s c = true := by
  have hPpos : 0 < 2 ^ j := Nat.two_pow_pos _
  have hSpos : 0 < nb * M := Nat.mul_pos hnb hM
  obtain ⟨hu, hdn, hup, hpar⟩ := fields_gridF f j z (expF f c) (fracF f c) hshape
  have hrel2 : (2 * N) * (nb * M) = D * (2 * (2 ^ j * M0)) := by
    calc (2 * N) * (nb * M) = 2 * (N * (nb * M)) := by ac_rfl
      _ = 2 * (D * (2 ^ j * M0)) := by rw [hrel]
      _ = D * (2 * (2 ^ j * M0)) := by ac_rfl
  rw [certNF_fin f N D s c hE]
  refine ⟨hsign, hC0, ?_, ?_⟩
  · -- the lower bound
    by_cases hz0 : z = 0
    · left; rw [hu, hz0]; simp
    · right
      have hy : (2 * z - 1) + 1 = 2 * z := by omega
      have hle : D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) ≤ 2 * N := by
        rw [scale_le D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2, hu]
        rcases hdn with hdn | ⟨hdn, hz1024, hj1⟩
        · rw [hdn]
          by_cases hs : st0
          · exact low_std nb M (2 ^ j) (2 * z - 1) z qm M0 hy ((hcT hs).1.resolve_left hz0) hq1
          · exact low_std nb M (2 ^ j) (2 * z - 1) z qm M0 hy (((hcF hs).1.resolve_left hz0).1) hq1
        · exact low_floor nb M (2 ^ j) z qm M0 _ (hfloor hz1024 hj1) hq1
      have hlt : z % 2 = 1 →
          D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) < 2 * N := by
        intro hodd
        rw [scale_lt D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2, hu]
        have hdn' : dnF (expF f c) (fracF f c) = 2 ^ j := by
          rcases hdn with hdn | ⟨-, hz1024, -⟩
          · exact hdn
          · have := two_pow_t_even f
            omega
        rw [hdn']
        by_cases hs : st0
        · exact low_std_lt_b nb M (2 ^ j) (2 * z - 1) z qm M0 hPpos hy ((hcT hs).1.resolve_left hz0) (hst1 hs)
        · exact low_std_lt_a nb M (2 ^ j) (2 * z - 1) z qm M0 hnb hPpos hy
            (((hcF hs).1.resolve_left hz0).2 hodd) hq1
      by_cases hev : fracF f c % 2 = 0
      · rw [leB_of_eq (decide_eq_true hev)]; exact hle
      · rw [leB_of_ne (fun h => hev (of_decide_eq_true h))]
        exact hlt (by omega)
  · -- the upper bound
    have mono : ∀ upv : Nat, (upv = 2 ^ j ∨ upv = 2 * 2 ^ j) →
        (nb * M) * (2 * (z * 2 ^ j) + 2 ^ j) ≤ (nb * M) * (2 * (z * 2 ^ j) + upv) := by
      intro upv h
      apply Nat.mul_le_mul_left
      rcases h with h | h <;> omega
    have hupv : 2 ^ (expF f c - 1) = 2 ^ j ∨ 2 ^ (expF f c - 1) = 2 * 2 ^ j := by
      rcases hup with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hle : 2 * (2 ^ j * M0) ≤
        (nb * M) * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)) := by
      rw [hu]
      have hbase : 2 * (2 ^ j * M0) ≤ (nb * M) * (2 * (z * 2 ^ j) + 2 ^ j) := by
        by_cases hs : st0
        · exact Nat.le_of_lt (up_lt_b nb M (2 ^ j) (2 * z + 1) z qm M0 hnb hPpos rfl (hcT hs).2 hq2)
        · exact up_le nb M (2 ^ j) (2 * z + 1) z qm M0 rfl (hcF hs).2.1 (Nat.le_of_eq (hst2 hs))
      exact Nat.le_trans hbase (mono _ hupv)
    have hlt : z % 2 = 1 → 2 * (2 ^ j * M0) <
        (nb * M) * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)) := by
      intro hodd
      rw [hu]
      have hup1 : 2 ^ (expF f c - 1) = 2 ^ j := by
        rcases hup with h | ⟨-, hz2048⟩
        · exact h
        · have := two_pow_t_even f
          omega
      rw [hup1]
      by_cases hs : st0
      · exact up_lt_b nb M (2 ^ j) (2 * z + 1) z qm M0 hnb hPpos rfl (hcT hs).2 hq2
      · exact up_lt_a nb M (2 ^ j) (2 * z + 1) z qm M0 hnb hPpos rfl ((hcF hs).2.2 hodd)
          (Nat.le_of_eq (hst2 hs))
    by_cases hev : fracF f c % 2 = 0
    · rw [leB_of_eq (decide_eq_true hev),
        scale_ge D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2]
      exact hle
    · rw [leB_of_ne (fun h => hev (of_decide_eq_true h)),
        scale_gt D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2]
      exact hlt (by omega)

/-- **The certificate for the infinity pattern**, at or above the threshold. -/
theorem cert_inf_grid (f : Format) (N D nb M M0 j : Nat) (c : BitVec f.k) (s : Bool)
    (hD : 0 < D) (hnb : 0 < nb) (hM : 0 < M)
    (hrel : N * (nb * M) = D * (2 ^ j * M0))
    (hE : expF f c = 2 ^ f.w - 1) (hT : fracF f c = 0) (hsign : signF f c = s)
    (hge : nb * M * ((2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) ≤ 2 ^ j * M0) :
    certNF f N D s c = true := by
  rw [certNF_inf f N D s c hE]
  refine ⟨hsign, hT, ?_⟩
  have h := (scale_le D (nb * M) N (2 ^ j * M0) ((2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) hD
    (Nat.mul_pos hnb hM) hrel).2 hge
  calc D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)
      = D * ((2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) := Nat.mul_assoc _ _ _
    _ ≤ N := h

/-- **The finite, not overflowing case.** Abstract datapath: `qm ∈ [2^p, 2^(p+1))` is the quotient of `M0` by `nb` with
sticky `st0`; the shift is `sh`, `qs = qm / 2^sh`, `inc` the round-to-nearest-even increment, `z = qs / 2 + inc`; the
packed magnitude is `mag = j · 2^t + z`, with `j` the grid exponent: in the normal regime (`sh = 0`) `z ∈ [2^t, 2^(t+1)]`,
`j + 3 ≤ 2^w`, and a carry (`z = 2^(t+1)`) happens exactly for `qm = 2^(p+1) - 1`; in the subnormal regime `j = 0`,
`sh ≥ 1`, `z ≤ 2^t`. -/
theorem fin_cert_abs (f : Format) (N D nb M0 qm sh j z mag : Nat) (st0 inc : Prop) [Decidable inc] (s : Bool)
    (hD : 0 < D) (hnb : 0 < nb)
    (hrel : N * (nb * 2 ^ (sh + 1)) = D * (2 ^ j * M0))
    (hq1 : nb * qm ≤ M0) (hq2 : M0 < nb * qm + nb)
    (hst1 : st0 → nb * qm < M0) (hst2 : ¬ st0 → M0 = nb * qm)
    (hqm1 : 2 * 2 ^ f.t ≤ qm) (hqm2 : qm < 4 * 2 ^ f.t)
    (hinc : inc ↔ (qm / 2 ^ sh % 2 = 1 ∧ (st0 ∨ qm % 2 ^ sh ≠ 0 ∨ qm / 2 ^ sh / 2 % 2 = 1)))
    (hz : z = qm / 2 ^ sh / 2 + (if inc then 1 else 0))
    (hmag : mag = j * 2 ^ f.t + z)
    (hreg : (sh = 0 ∧ 2 ^ f.t ≤ z ∧ z ≤ 2 * 2 ^ f.t ∧ j + 3 ≤ 2 ^ f.w ∧
              (z = 2 * 2 ^ f.t ↔ qm = 4 * 2 ^ f.t - 1)) ∨
            (j = 0 ∧ 1 ≤ sh ∧ z ≤ 2 ^ f.t)) :
    certNF f N D s (fields f s (mag / 2 ^ f.t) (mag % 2 ^ f.t)) = true := by
  have hMt : 0 < 2 ^ f.t := Nat.two_pow_pos _
  have hev := two_pow_t_even f
  have hw2 := two_pow_w_emax f
  have hw4 := four_le_two_pow_w f
  have hp1 := two_pow_p1 f
  have hemax := emax_pos f
  have hMpos : 0 < 2 ^ (sh + 1) := Nat.two_pow_pos _
  have hMt2 : 2 ≤ 2 ^ f.t := by omega
  -- the field bounds
  have hmag_lt : mag < 2 ^ f.w * 2 ^ f.t := by
    rcases hreg with ⟨-, h1, h2, h3, -⟩ | ⟨h0, -, h2⟩
    · have : (j + 3) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ h3
      rw [Nat.add_mul] at this
      omega
    · subst h0
      have : 2 * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ (by omega)
      omega
  -- the fields (Ec, Tc) of mag
  obtain ⟨Ec, Tc, hmagE, hTc, hshape'⟩ : ∃ Ec Tc : Nat, mag = Ec * 2 ^ f.t + Tc ∧ Tc < 2 ^ f.t ∧
      ((Ec = 0 ∧ j = 0 ∧ z = Tc ∧ Tc < 2 ^ f.t) ∨
       (1 ≤ Ec ∧ j + 1 = Ec ∧ z = 2 ^ f.t + Tc ∧ Tc < 2 ^ f.t) ∨
       (1 ≤ Ec ∧ j + 2 = Ec ∧ z = 2 * 2 ^ f.t ∧ Tc = 0)) := by
    rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩
    · by_cases hz2 : z = 2 * 2 ^ f.t
      · refine ⟨j + 2, 0, ?_, hMt, Or.inr (Or.inr ⟨by omega, rfl, hz2, rfl⟩)⟩
        rw [hmag, hz2, Nat.add_mul]; omega
      · refine ⟨j + 1, z - 2 ^ f.t, ?_, by omega, Or.inr (Or.inl ⟨by omega, rfl, by omega, by omega⟩)⟩
        rw [hmag, Nat.add_mul, Nat.one_mul]; omega
    · by_cases hzM : z = 2 ^ f.t
      · refine ⟨1, 0, ?_, hMt, Or.inr (Or.inl ⟨Nat.le_refl _, by omega, by omega, hMt⟩)⟩
        rw [hmag, h0, hzM]; omega
      · refine ⟨0, z, ?_, by omega, Or.inl ⟨rfl, h0, rfl, by omega⟩⟩
        rw [hmag, h0]
  have hEc : Ec < 2 ^ f.w := by
    have h1 : Ec * 2 ^ f.t < 2 ^ f.w * 2 ^ f.t := by omega
    exact Nat.lt_of_mul_lt_mul_right h1
  obtain ⟨hd1, hd2⟩ := (Nat.div_mod_unique (a := mag) (d := Ec) hMt).mpr
    ⟨by rw [hmagE, Nat.mul_comm Ec, Nat.add_comm Tc], hTc⟩
  rw [hd1, hd2]
  obtain ⟨hsg, hex, hfr⟩ := fields_fields f s Ec Tc hEc hTc
  -- the rounding core
  have hcT : st0 → ((z = 0 ∨ (2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm) ∧ 2 * qm + 2 ≤ (2 * z + 1) * 2 ^ (sh + 1)) := by
    intro hs
    apply core_t qm sh z
    rw [hz]
    by_cases hi : inc
    · have h1 := (hinc.1 hi).1
      rw [if_pos hi]; omega
    · rw [if_neg hi]
      have : ¬ (qm / 2 ^ sh % 2 = 1) := fun h1 => hi (hinc.2 ⟨h1, Or.inl hs⟩)
      omega
  have hcF : ¬ st0 → ((z = 0 ∨ ((2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm ∧
        (z % 2 = 1 → (2 * z - 1) * 2 ^ (sh + 1) < 2 * qm))) ∧
      2 * qm ≤ (2 * z + 1) * 2 ^ (sh + 1) ∧ (z % 2 = 1 → 2 * qm < (2 * z + 1) * 2 ^ (sh + 1))) := by
    intro hs
    apply core_f qm sh z
    by_cases hi : inc
    · left
      refine ⟨?_, by rw [hz, if_pos hi]⟩
      have := hinc.1 hi
      refine ⟨this.1, ?_⟩
      rcases this.2 with h | h
      · exact absurd h hs
      · exact h
    · right
      refine ⟨fun h => hi (hinc.2 ?_), by rw [hz, if_neg hi, Nat.add_zero]⟩
      rcases h with ⟨h1, h2⟩
      exact ⟨h1, Or.inr h2⟩
  have hQ : 0 < 2 ^ (2 * f.emax - 2) := Nat.two_pow_pos _
  by_cases hcarry : j + 3 = 2 ^ f.w ∧ z = 2 * 2 ^ f.t ∧ sh = 0
  · -- the carry out of the largest finite number: infinity
    obtain ⟨hj, hz2, hsh0⟩ := hcarry
    have hqm : qm = 4 * 2 ^ f.t - 1 := by
      rcases hreg with ⟨-, -, -, -, h5⟩ | ⟨-, h1, -⟩
      · exact h5.1 hz2
      · omega
    have hE31 : Ec = 2 ^ f.w - 1 ∧ Tc = 0 := by
      rcases hshape' with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
    refine cert_inf_grid f N D nb (2 ^ (sh + 1)) M0 j _ s hD hnb hMpos hrel
      (by rw [hex]; exact hE31.1) (by rw [hfr]; exact hE31.2) hsg ?_
    have hjE : j = (2 * f.emax - 2) + 1 := by omega
    have h2j : 2 ^ j = 2 * 2 ^ (2 * f.emax - 2) := by rw [hjE, Nat.pow_succ]; ac_rfl
    rw [hsh0, h2j, hp1]
    simp only [Nat.zero_add, Nat.pow_one]
    rw [hqm] at hq1
    have := Nat.mul_le_mul_left (2 * 2 ^ (2 * f.emax - 2)) hq1
    calc nb * 2 * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2))
        = 2 * 2 ^ (2 * f.emax - 2) * (nb * (4 * 2 ^ f.t - 1)) := by ac_rfl
      _ ≤ 2 * 2 ^ (2 * f.emax - 2) * M0 := this
  · -- a finite pattern on the grid
    have hE : Ec ≠ 2 ^ f.w - 1 := by
      rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩ <;>
      rcases hshape' with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ <;> omega
    have hC0 : N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) := by
      have hb : 2 ^ j * (qm + 1) ≤ 2 ^ (sh + 1) * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) := by
        apply thr_bound (4 * 2 ^ f.t) (2 ^ (2 * f.emax - 2)) (2 ^ j) qm (2 ^ (sh + 1)) hQ (by omega)
        rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩
        · subst hsh
          by_cases hjl : j ≤ 2 * f.emax - 2
          · left
            exact ⟨by simp, Nat.pow_le_pow_right (by omega) hjl, by omega⟩
          · right; left
            have hjE : j = (2 * f.emax - 2) + 1 := by omega
            have hz2 : z ≠ 2 * 2 ^ f.t := fun hz2 => hcarry ⟨by omega, hz2, rfl⟩
            have hq3 : qm ≠ 4 * 2 ^ f.t - 1 := fun hq => hz2 (h5.2 hq)
            refine ⟨by simp, ?_, by omega⟩
            rw [hjE, Nat.pow_succ]; ac_rfl
        · right; right
          subst h0
          refine ⟨?_, by simp, by omega⟩
          have : 2 ^ 2 ≤ 2 ^ (sh + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
      have hc0 := c0_of nb (2 ^ (sh + 1)) (2 ^ j) qm M0 ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) hnb
        (Nat.two_pow_pos _) hq2 hb
      have := (scale_gt D (nb * 2 ^ (sh + 1)) N (2 ^ j * M0)
        ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) hD (Nat.mul_pos hnb hMpos) hrel).2 hc0
      rw [hp1]
      calc N < D * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) := this
        _ = D * (4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2) := (Nat.mul_assoc _ _ _).symm
    have hfloor : z = 2 ^ f.t → 1 ≤ j → z * 2 ^ (sh + 1) ≤ qm := by
      intro hzM hj1
      rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩
      · subst hsh
        rw [hzM]
        simp only [Nat.zero_add, Nat.pow_one]
        omega
      · omega
    exact cert_fin_grid f N D nb (2 ^ (sh + 1)) qm M0 z j st0 _ s hD hnb hMpos hrel hq1 hq2 hst1 hst2 hcT hcF
      hfloor hsg (by rw [hex]; exact hE) (by rw [hex, hfr]; exact hshape') hC0

/-- **Overflow**: `E >= 2^w - 1` (so `sh = 0`, `j = E - 1 >= 2^w - 2`): the infinity pattern is at or above the threshold. -/
theorem ovf_cert_abs (f : Format) (N D nb M0 qm j : Nat) (s : Bool) (hD : 0 < D) (hnb : 0 < nb)
    (hrel : N * (nb * 2 ^ (0 + 1)) = D * (2 ^ j * M0)) (hq1 : nb * qm ≤ M0)
    (hqm1 : 2 * 2 ^ f.t ≤ qm) (hj : 2 ^ f.w ≤ j + 2) :
    certNF f N D s (infinity f s) = true := by
  have hw2 := two_pow_w_emax f
  have hw4 := four_le_two_pow_w f
  have hp1 := two_pow_p1 f
  have hemax := emax_pos f
  have hMt := Nat.two_pow_pos f.t
  obtain ⟨hsg, hex, hfr⟩ := fields_fields f s (2 ^ f.w - 1) 0 (by omega) hMt
  refine cert_inf_grid f N D nb (2 ^ (0 + 1)) M0 j (infinity f s) s hD hnb (Nat.two_pow_pos _) hrel hex hfr hsg ?_
  have h4 : 2 ^ (2 * f.emax) = 4 * 2 ^ (2 * f.emax - 2) := by
    have e : 2 * f.emax = (2 * f.emax - 2) + 2 := by omega
    have h4' : 2 ^ ((2 * f.emax - 2) + 2) = 4 * 2 ^ (2 * f.emax - 2) := by
      rw [Nat.pow_add]; omega
    rw [← e] at h4'
    exact h4'
  have h2j : 4 * 2 ^ (2 * f.emax - 2) ≤ 2 ^ j := by
    rw [← h4]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hM0 : nb * (2 * 2 ^ f.t) ≤ M0 := Nat.le_trans (Nat.mul_le_mul_left nb hqm1) hq1
  have h5 := Nat.mul_le_mul h2j hM0
  rw [hp1]
  simp only [Nat.zero_add, Nat.pow_one]
  calc nb * 2 * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2))
      ≤ nb * 2 * ((4 * 2 ^ f.t) * 2 ^ (2 * f.emax - 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    _ = 4 * 2 ^ (2 * f.emax - 2) * (nb * (2 * 2 ^ f.t)) := by ac_rfl
    _ ≤ 2 ^ j * M0 := h5

end LeanModels.SoftFloat.Binary
