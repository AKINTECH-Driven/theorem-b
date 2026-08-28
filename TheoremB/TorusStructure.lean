/-
# Torus flow structure (Tier 5, waves W-synth-S4 / W-2pi / W-struct)

L2-continuity of the synthesized flow on the half line, the 2pi-calibrated
integral equation with the honest torus constants, and the structure
transfer: a.e. reality, spectral divergence-freeness, and mean-zero.
-/
import TheoremB.TorusSynthesis

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance ts_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance ts_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance ts_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### CHARLIE-1: L²-continuity of the synthesized flow -/

/-- Synthesis is subtractive on the square-summable class. -/
private lemma c1_synthT_sub {a b : (Fin 3 → ℤ) → Vel}
    (ha : Summable fun k => ‖a k‖ ^ 2) (hb : Summable fun k => ‖b k‖ ^ 2) (j : Fin 3) :
    synthT j a - synthT j b = synthT j (fun k => a k - b k) := by
  have hab : Summable fun k => ‖a k - b k‖ ^ 2 := summable_sq_sub ha hb
  rw [synthT_eq j ha, synthT_eq j hb, synthT_eq j hab]
  unfold synth
  rw [← LinearIsometryEquiv.map_sub]
  congr 1

/-- **The synthesis-difference energy bound**: the L² distance between two
synthesized components is controlled by the coefficient defect energy. -/
theorem continuousOn_synthT_sub_bound {a b : (Fin 3 → ℤ) → Vel}
    (ha : Summable fun k => ‖a k‖ ^ 2) (hb : Summable fun k => ‖b k‖ ^ 2) (j : Fin 3) :
    ‖synthT j a - synthT j b‖ ^ (2:ℝ) ≤ en (fun k => a k - b k) := by
  have hab : Summable fun k => ‖a k - b k‖ ^ 2 := summable_sq_sub ha hb
  rw [c1_synthT_sub ha hb j]
  have hterm : ∀ k, ‖(a k - b k) j‖ ^ (2:ℝ) ≤ ‖a k - b k‖ ^ 2 := by
    intro k
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (a k - b k) j) 2
  have hsummand : Summable fun k => ‖(a k - b k) j‖ ^ (2:ℝ) := by
    refine (summable_component j hab).congr fun k => ?_
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  calc ‖synthT j (fun k => a k - b k)‖ ^ (2:ℝ)
      = ∑' k, ‖(a k - b k) j‖ ^ (2:ℝ) := norm_synthT_sq j hab
    _ ≤ ∑' k, ‖a k - b k‖ ^ 2 := hsummand.tsum_le_tsum hterm hab
    _ = en (fun k => a k - b k) := rfl

set_option linter.unusedVariables false in
/-- **CHARLIE-1**: the synthesized component flow of an ℓ²-continuous,
enstrophy-bounded coefficient flow is L²-continuous on the half-line. -/
theorem continuousOn_synthT {c : ℝ → (Fin 3 → ℤ) → Vel} {Z : ℝ} (hZ0 : 0 ≤ Z)
    (hsum : ∀ t ∈ Set.Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2))
    (hwsum : ∀ t ∈ Set.Ici (0:ℝ), Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2))
    (hens : ∀ t ∈ Set.Ici (0:ℝ), ens (c t) ≤ Z)
    (hcont : ∀ k, ContinuousOn (fun s => c s k) (Set.Ici (0:ℝ)))
    (j : Fin 3) :
    ContinuousOn (fun t => synthT j (c t)) (Set.Ici (0:ℝ)) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : (0:ℝ) < ε ^ 2 := pow_pos hε 2
  -- defect certificates against the base time t
  have hdsum : ∀ s ∈ Set.Ici (0:ℝ), Summable fun l => ‖c s l - c t l‖ ^ 2 :=
    fun s hs => summable_sq_sub (hsum s hs) (hsum t ht)
  have hdwsum : ∀ s ∈ Set.Ici (0:ℝ),
      Summable fun l => ‖freq l‖ ^ 2 * ‖c s l - c t l‖ ^ 2 :=
    fun s hs => summable_wsq_sub (hwsum s hs) (hwsum t ht)
  have hdens : ∀ s ∈ Set.Ici (0:ℝ), ens (fun l => c s l - c t l) ≤ 4 * Z := by
    intro s hs
    have h := ens_sub_le (hwsum s hs) (hwsum t ht)
    have h1 := hens s hs
    have h2 := hens t ht
    linarith
  -- the box radius: the tail contributes less than ε²/2
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * Z / ε ^ 2)
  have hR : 0 < n + 1 := Nat.succ_pos n
  have hRpos : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hR
  have hRgt : 8 * Z / ε ^ 2 < ((n + 1 : ℕ) : ℝ) := by
    have h1 : ((n : ℝ)) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
    linarith
  have hR1 : (1:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hR
  have hRsq : 8 * Z / ε ^ 2 < ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have h2 : ((n + 1 : ℕ) : ℝ) * 1 ≤ ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hR1 hRpos.le
    nlinarith
  have htailb : 4 * Z / ((n + 1 : ℕ) : ℝ) ^ 2 < ε ^ 2 / 2 := by
    rw [div_lt_iff₀ hε2] at hRsq
    rw [div_lt_iff₀ (pow_pos hRpos 2)]
    nlinarith
  -- the per-mode threshold
  have hcard1 : (0:ℝ) < 2 * (((insert (0 : Fin 3 → ℤ) (boxS (n + 1))).card : ℝ) + 1) := by
    positivity
  set η : ℝ :=
    Real.sqrt (ε ^ 2 / (2 * (((insert (0 : Fin 3 → ℤ) (boxS (n + 1))).card : ℝ) + 1)))
    with hηdef
  have hη : 0 < η := by
    rw [hηdef, Real.sqrt_pos]
    positivity
  have hηsq : η ^ 2
      = ε ^ 2 / (2 * (((insert (0 : Fin 3 → ℤ) (boxS (n + 1))).card : ℝ) + 1)) := by
    rw [hηdef]
    exact Real.sq_sqrt (by positivity)
  -- per-mode deltas from mode continuity
  have hδk : ∀ k : Fin 3 → ℤ, ∃ δ, 0 < δ ∧ ∀ s ∈ Set.Ici (0:ℝ),
      dist s t < δ → dist (c s k) (c t k) < η := by
    intro k
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousWithinAt_iff.mp (hcont k t ht) η hη
    exact ⟨δ, hδ0, fun s hs hst => hδ hs hst⟩
  choose δf hδf0 hδf using hδk
  have hFne : (insert (0 : Fin 3 → ℤ) (boxS (n + 1))).Nonempty :=
    ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨(insert (0 : Fin 3 → ℤ) (boxS (n + 1))).inf' hFne δf, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff hFne).mpr fun k _ => hδf0 k
  intro s hs hst
  -- each boxed mode is η-close
  have hmode : ∀ k ∈ insert (0 : Fin 3 → ℤ) (boxS (n + 1)),
      ‖c s k - c t k‖ ^ 2 ≤ η ^ 2 := by
    intro k hk
    have h1 : dist s t < δf k := lt_of_lt_of_le hst (Finset.inf'_le δf hk)
    have h2 := hδf k s hs h1
    rw [dist_eq_norm] at h2
    exact pow_le_pow_left₀ (norm_nonneg _) h2.le 2
  -- the finite part is below ε²/2
  have hfin : (∑ k ∈ insert (0 : Fin 3 → ℤ) (boxS (n + 1)), ‖c s k - c t k‖ ^ 2)
      < ε ^ 2 / 2 := by
    have h1 := Finset.sum_le_card_nsmul (insert (0 : Fin 3 → ℤ) (boxS (n + 1)))
      (fun k => ‖c s k - c t k‖ ^ 2) (η ^ 2) hmode
    rw [nsmul_eq_mul] at h1
    have h2 : ((insert (0 : Fin 3 → ℤ) (boxS (n + 1))).card : ℝ) * η ^ 2
        < ε ^ 2 / 2 := by
      rw [hηsq, ← mul_div_assoc, div_lt_iff₀ hcard1]
      have h3 : ε ^ 2 / 2 * (2 * (((insert (0 : Fin 3 → ℤ) (boxS (n + 1))).card : ℝ) + 1))
          = ((insert (0 : Fin 3 → ℤ) (boxS (n + 1))).card : ℝ) * ε ^ 2 + ε ^ 2 := by
        ring
      rw [h3]
      have hM0 : (0:ℝ) ≤ ((insert (0 : Fin 3 → ℤ) (boxS (n + 1))).card : ℝ) :=
        Nat.cast_nonneg _
      linarith
    linarith
  -- the tail is at most ε²/2 short of strict, so the defect energy is below ε²
  have htail := tail_en_lt (Z := 4 * Z) (n + 1) hR (hdsum s hs) (hdwsum s hs)
    (hdens s hs)
  have henlt : en (fun l => c s l - c t l) < ε ^ 2 := by
    linarith [hfin, htailb, htail]
  -- conclude in L²
  have hbound := continuousOn_synthT_sub_bound (hsum s hs) (hsum t ht) j
  have hrw : ‖synthT j (c s) - synthT j (c t)‖ ^ (2:ℝ)
      = ‖synthT j (c s) - synthT j (c t)‖ ^ (2:ℕ) := by
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hsq : ‖synthT j (c s) - synthT j (c t)‖ ^ (2:ℕ) < ε ^ 2 := by
    rw [← hrw]
    exact lt_of_le_of_lt hbound henlt
  show dist (synthT j (c s)) (synthT j (c t)) < ε
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- `2π > 0`. -/
private theorem c2_two_pi_pos : (0:ℝ) < 2 * Real.pi := by positivity

/-- Scalar bookkeeping: `2π · (−ν‖k‖²) = −(ν/(2π)) · ((2π)²‖k‖²)`. -/
private theorem c2_scalar_calc (ν : ℝ) (k : Fin 3 → ℤ) :
    2 * Real.pi * -(ν * ‖freq k‖ ^ 2)
      = -(ν / (2 * Real.pi) * ((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Pointwise integrand identity: scaling the Galerkin right-hand side by `2π`
produces the calibrated right-hand side. -/
private theorem c2_integrand_eq (ν : ℝ) (k : Fin 3 → ℤ) (v w : Vel) :
    (2 * Real.pi) • ((-(ν * ‖freq k‖ ^ 2)) • v + w)
      = (-(ν / (2 * Real.pi) * ((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2))) • v
        + (2 * Real.pi) • w := by
  rw [smul_add, smul_smul, c2_scalar_calc]

/-- **The 2π calibration.** A solution of the Galerkin integral equation with
viscosity `ν`, run at speed `2π`, solves the calibrated integral equation with
viscosity `ν/(2π)` against the `(2π)²`-scaled dissipation symbol and the
`2π`-scaled nonlinearity. -/
theorem calibrated_integral_equation {ν : ℝ} {c₀ : (Fin 3 → ℤ) → Vel}
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (heq : ∀ t ∈ Set.Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) :
    ∀ t ∈ Set.Ici (0:ℝ), ∀ k, c (2 * Real.pi * t) k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν / (2 * Real.pi) * ((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2))) • c (2 * Real.pi * s) k
        + (2 * Real.pi) • lerayProj k (convFull (c (2 * Real.pi * s)) k)) := by
  intro t ht k
  have ht' : (2 * Real.pi * t) ∈ Set.Ici (0:ℝ) :=
    Set.mem_Ici.mpr (mul_nonneg (le_of_lt c2_two_pi_pos) (Set.mem_Ici.mp ht))
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := t)
    (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))
    (2 * Real.pi)
  rw [mul_zero] at hsub
  have hint : (∫ s in (0:ℝ)..(2 * Real.pi * t),
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)))
      = ∫ s in (0:ℝ)..t,
        ((-(ν / (2 * Real.pi) * ((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2))) • c (2 * Real.pi * s) k
          + (2 * Real.pi) • lerayProj k (convFull (c (2 * Real.pi * s)) k)) := by
    calc (∫ s in (0:ℝ)..(2 * Real.pi * t),
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)))
        = (2 * Real.pi) • ∫ s in (0:ℝ)..t,
            ((-(ν * ‖freq k‖ ^ 2)) • c (2 * Real.pi * s) k
              + lerayProj k (convFull (c (2 * Real.pi * s)) k)) := hsub.symm
      _ = ∫ s in (0:ℝ)..t, (2 * Real.pi) •
            ((-(ν * ‖freq k‖ ^ 2)) • c (2 * Real.pi * s) k
              + lerayProj k (convFull (c (2 * Real.pi * s)) k)) :=
          (intervalIntegral.integral_smul _ _).symm
      _ = ∫ s in (0:ℝ)..t,
            ((-(ν / (2 * Real.pi) * ((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2))) • c (2 * Real.pi * s) k
              + (2 * Real.pi) • lerayProj k (convFull (c (2 * Real.pi * s)) k)) := by
          simp only [c2_integrand_eq]
  rw [heq (2 * Real.pi * t) ht' k, hint]

/-- **Trap calibration.** Any property holding on all of `[0, ∞)` holds along the
`2π`-sped-up clock. -/
theorem calibrated_trap {P : ℝ → Prop}
    (h : ∀ t ∈ Set.Ici (0:ℝ), P t) :
    ∀ t ∈ Set.Ici (0:ℝ), P (2 * Real.pi * t) := by
  intro t ht
  exact h _ (Set.mem_Ici.mpr (mul_nonneg (le_of_lt c2_two_pi_pos) (Set.mem_Ici.mp ht)))

/-- Componentwise formula for `conjVel`: the `j`-th component of the
conjugated velocity value is the conjugate of the `j`-th component. -/
lemma c3_conjVel_apply (v : Vel) (j : Fin 3) :
    conjVel v j = (starRingEnd ℂ) (v j) := rfl

/-- `mFourierCoeff` only sees the a.e. class of its argument. -/
lemma c3_mFourierCoeff_congr_ae {f g : T3 → ℂ}
    (h : f =ᵐ[(volume : Measure T3)] g) (k : Fin 3 → ℤ) :
    mFourierCoeff f k = mFourierCoeff g k := by
  unfold mFourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [ht]

/-- **Structure transfer, star**: the Fourier coefficients of the `Lp`-level
star are the conjugated, frequency-reflected coefficients. -/
theorem mFourierCoeff_star (f : L2T3) (k : Fin 3 → ℤ) :
    mFourierCoeff ((star f : L2T3) : T3 → ℂ) k =
      (starRingEnd ℂ) (mFourierCoeff (f : T3 → ℂ) (-k)) := by
  have hae : ((star f : L2T3) : T3 → ℂ) =ᵐ[(volume : Measure T3)]
      fun t => (starRingEnd ℂ) ((f : T3 → ℂ) t) := by
    filter_upwards [MeasureTheory.Lp.coeFn_star f] with t ht
    rw [ht, Pi.star_apply, starRingEnd_apply]
  rw [c3_mFourierCoeff_congr_ae hae]
  unfold mFourierCoeff
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [neg_neg, smul_eq_mul, map_mul, ← mFourier_neg]

/-- **Structure transfer, reality**: a `RealField` coefficient family
synthesizes to a real (star-fixed) component field. -/
theorem synthT_real {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) (hreal : RealField c) (j : Fin 3) :
    star (synthT j c) = synthT j c := by
  apply (mFourierBasis (d := Fin 3)).repr.injective
  ext k
  rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_star,
    mFourierCoeff_synthT j hc, mFourierCoeff_synthT j hc, hreal k,
    c3_conjVel_apply]
  exact Complex.conj_conj _

/-- **Structure transfer, incompressibility**: a `DivFree` coefficient family
synthesizes to a field whose coefficients satisfy the spectral divergence-free
identity at every frequency. -/
theorem synthT_divFree_spectral {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) (hdiv : DivFree c) (k : Fin 3 → ℤ) :
    (∑ j : Fin 3, ((k j : ℝ) : ℂ) * mFourierCoeff (synthT j c : T3 → ℂ) k) = 0 := by
  calc ∑ j : Fin 3, ((k j : ℝ) : ℂ) * mFourierCoeff (synthT j c : T3 → ℂ) k
      = ∑ j : Fin 3, ((k j : ℝ) : ℂ) * c k j :=
        Finset.sum_congr rfl fun j _ => by rw [mFourierCoeff_synthT j hc]
    _ = dotR (c k) (freq k) := by
        unfold dotR freq
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = 0 := hdiv k

/-- **Structure transfer, mean-zero**: a mean-free coefficient family
synthesizes to a mean-free component field. -/
theorem synthT_meanZero {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) (h0 : c 0 = 0) (j : Fin 3) :
    mFourierCoeff (synthT j c : T3 → ℂ) 0 = 0 := by
  rw [mFourierCoeff_synthT j hc, h0]
  rfl

end

end TheoremB
