/-
# THEOREM B ON THE TORUS (Tier 5 summit)

The synthesized eternal flow as a genuine velocity field on the unit
3-torus: global-in-time, L²-continuous, a.e. real, divergence-free,
satisfying the calibrated Navier-Stokes equation in the band-limited weak
form with the HONEST physical constants (−ν(2π)²‖k‖² dissipation and
2π-weighted convection), trapped forever — and unique in its class.
-/
import TheoremB.SpectralWeak
import TheoremB.CoeffExtract

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance tbt_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance tbt_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance tbt_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private lemma tb_two_pi_pos : (0:ℝ) < 2 * Real.pi := by
  have := Real.pi_pos
  linarith

/-- The ℂ-valued time-stretch identity for interval integrals. -/
private lemma tb_integral_stretch (g : ℝ → ℂ) (t : ℝ) :
    (∫ s in (0:ℝ)..(2 * Real.pi * t), g s) =
      ∫ s in (0:ℝ)..t, (2 * Real.pi : ℂ) * g (2 * Real.pi * s) := by
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := t) g (2 * Real.pi)
  rw [mul_zero] at hsub
  calc (∫ s in (0:ℝ)..(2 * Real.pi * t), g s)
      = (2 * Real.pi) • ∫ s in (0:ℝ)..t, g (2 * Real.pi * s) := hsub.symm
    _ = ∫ s in (0:ℝ)..t, (2 * Real.pi) • g (2 * Real.pi * s) :=
        (intervalIntegral.integral_smul _ _).symm
    _ = ∫ s in (0:ℝ)..t, (2 * Real.pi : ℂ) * g (2 * Real.pi * s) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [Complex.real_smul]
        push_cast
        ring

/-- Extraction of the frequency component: `freq k` acts componentwise as the
integer cast. -/
private lemma tb_freq_apply (k : Fin 3 → ℤ) (j : Fin 3) :
    freq k j = (k j : ℝ) := rfl

/-- **THEOREM B ON THE TORUS.** There is a universal constant `κ_t > 0` such
that for every viscosity `ν > 0` and every initial field `u₀` on the unit
3-torus — components a.e. real, mean-zero, spectrally divergence-free, with
finite spectral enstrophy — satisfying the smallness condition
`κ_t · ‖u₀‖² · ((2π)²·Z₀) < ν⁴` (the middle factor is the L² energy, the
last the honest gradient energy): there exists a velocity field
`u : ℝ → Fin 3 → L2T3`, global in time, which starts at `u₀`, has
L²-continuous components on the half line, stays a.e. real and spectrally
divergence-free, keeps its energy and spectral enstrophy below their
initial values forever, and satisfies the calibrated Navier-Stokes equation
in band-limited weak form with the honest physical constants: for every
finitely supported divergence-free test coefficient field, the pairing
evolves by `−ν(2π)²‖k‖²`-dissipation plus `2π`-weighted convection. -/
theorem theorem_B_torus :
    ∃ κ_t : ℝ, 0 < κ_t ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {u₀ : Fin 3 → L2T3},
      (∀ j, star (u₀ j) = u₀ j) →
      (∀ j, mFourierCoeff ((u₀ j : L2T3) : T3 → ℂ) 0 = 0) →
      (∀ k : Fin 3 → ℤ, (∑ j : Fin 3, ((k j : ℝ) : ℂ) *
        mFourierCoeff ((u₀ j : L2T3) : T3 → ℂ) k) = 0) →
      Summable (fun k => ‖freq k‖ ^ 2 * ‖extractCoeff u₀ k‖ ^ 2) →
      κ_t * (∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) *
        ((2 * Real.pi) ^ 2 * ens (extractCoeff u₀)) < ν ^ 4 →
      ∃ u : ℝ → Fin 3 → L2T3,
        u 0 = u₀ ∧
        (∀ j, ContinuousOn (fun t => u t j) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ j, star (u t j) = u t j) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k : Fin 3 → ℤ, (∑ j : Fin 3, ((k j : ℝ) : ℂ) *
          mFourierCoeff ((u t j : L2T3) : T3 → ℂ) k) = 0) ∧
        (∀ t ∈ Ici (0:ℝ),
          (∑ j : Fin 3, ‖u t j‖ ^ (2:ℝ)) ≤ ∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) ∧
        (∀ t ∈ Ici (0:ℝ),
          ens (extractCoeff (u t)) ≤ ens (extractCoeff u₀)) ∧
        (∀ t ∈ Ici (0:ℝ),
          Summable (fun k => ‖freq k‖ ^ 2 * ‖extractCoeff (u t) k‖ ^ 2)) ∧
        (∀ t ∈ Ici (0:ℝ), extractCoeff (u t) 0 = 0) ∧
        (∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
          (∀ k, k ∉ F → w k = 0) → DivFree w → ∀ t ∈ Ici (0:ℝ),
          (∑ k ∈ F, inner ℂ (w k) (extractCoeff (u t) k)) =
            (∑ k ∈ F, inner ℂ (w k) (extractCoeff u₀ k)) + ∫ s in (0:ℝ)..t,
              (∑ k ∈ F, ((-(ν * (2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) *
                  inner ℂ (w k) (extractCoeff (u s) k)
                + (2 * Real.pi) * inner ℂ (w k) (convFull (extractCoeff (u s)) k)))) := by
  obtain ⟨κ, hκ, hflow⟩ := ns_full_global_flow
  refine ⟨κ / (2 * Real.pi) ^ 6, by positivity, ?_⟩
  intro ν hν u₀ hreal₀ hmean₀ hdiv₀ hZ₀ hsmall
  -- the coefficient datum
  set c₀ : (Fin 3 → ℤ) → Vel := extractCoeff u₀ with hc₀def
  have hE₀ : Summable fun k => ‖c₀ k‖ ^ 2 := summable_extractCoeff u₀
  have hen₀ : en c₀ = ∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ) := en_extractCoeff u₀
  -- mean-zero
  have hmean : c₀ 0 = 0 := by
    have h : ∀ j, c₀ 0 j = 0 := fun j => by
      rw [hc₀def, extractCoeff_apply]
      exact hmean₀ j
    ext j
    exact h j
  -- reality
  have hrealF : RealField c₀ := by
    intro k
    ext j
    rw [conjVel_apply']
    show extractCoeff u₀ (-k) j = (starRingEnd ℂ) (extractCoeff u₀ k j)
    rw [extractCoeff_apply, extractCoeff_apply]
    -- from star (u₀ j) = u₀ j and the star-coefficient identity
    have h1 : mFourierCoeff ((u₀ j : L2T3) : T3 → ℂ) k =
        (starRingEnd ℂ) (mFourierCoeff ((u₀ j : L2T3) : T3 → ℂ) (-k)) := by
      conv_lhs => rw [← hreal₀ j]
      exact mFourierCoeff_star (u₀ j) k
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [Complex.conj_conj] at h2
    exact h2.symm
  -- divergence-freeness
  have hdivF : DivFree c₀ := by
    intro k
    have h := hdiv₀ k
    rw [dotR]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc₀def]
    have h1 : (extractCoeff u₀ k).ofLp j = extractCoeff u₀ k j := rfl
    rw [h1, extractCoeff_apply]
    have h2 : ((freq k).ofLp j : ℂ) = ((k j : ℝ) : ℂ) := by
      norm_cast
    rw [h2]
    ring
  -- smallness at the lattice viscosity
  have hsmall' : κ * en c₀ * ens c₀ < (2 * Real.pi * ν) ^ 4 := by
    have hp4 : (0:ℝ) < (2 * Real.pi) ^ 4 := by positivity
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have key : κ / (2 * Real.pi) ^ 6 * (∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) *
        ((2 * Real.pi) ^ 2 * ens c₀) =
        κ * (∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) * ens c₀ / (2 * Real.pi) ^ 4 := by
      field_simp
      try ring
    rw [key] at hsmall
    rw [hen₀]
    have h1 : κ * (∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) * ens c₀ =
        κ * (∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) * ens c₀ / (2 * Real.pi) ^ 4 *
          (2 * Real.pi) ^ 4 := by
      field_simp
    calc κ * (∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) * ens c₀
        = κ * (∑ j : Fin 3, ‖u₀ j‖ ^ (2:ℝ)) * ens c₀ / (2 * Real.pi) ^ 4 *
          (2 * Real.pi) ^ 4 := h1
      _ < ν ^ 4 * (2 * Real.pi) ^ 4 := mul_lt_mul_of_pos_right hsmall hp4
      _ = (2 * Real.pi * ν) ^ 4 := by ring
  -- the eternal coefficient flow at the lattice viscosity
  obtain ⟨c, hc0, hstr, hsummab, hccont, hinteg, _, htrap⟩ :=
    hflow (ν := 2 * Real.pi * ν) (by positivity) hE₀ hZ₀ hmean hrealF hdivF hsmall'
  -- the physical flow: synthesis at the sped-up clock
  set u : ℝ → Fin 3 → L2T3 := fun t j => synthT j (c (2 * Real.pi * t)) with hudef
  have hclock : ∀ t ∈ Ici (0:ℝ), (2 * Real.pi * t) ∈ Ici (0:ℝ) := fun t ht =>
    mem_Ici.mpr (mul_nonneg tb_two_pi_pos.le (mem_Ici.mp ht))
  -- coefficient extraction round trip along the flow
  have hext : ∀ t ∈ Ici (0:ℝ), extractCoeff (u t) = c (2 * Real.pi * t) := by
    intro t ht
    have hsm := (hsummab _ (hclock t ht)).1
    funext k
    ext j
    rw [hudef]
    show extractCoeff (fun j' => synthT j' (c (2 * Real.pi * t))) k j = _
    rw [extractCoeff_apply, mFourierCoeff_synthT j hsm k]
  -- the zero mode of the eternal flow vanishes for all nonnegative times
  have hfreq0 : freq (0 : Fin 3 → ℤ) = 0 := by
    have h := freq_sub 0 0
    simpa using h
  have hP0 : lerayProj 0 (0 : Vel) = 0 := by
    have h := lerayProj_sub 0 (0 : Vel) 0
    rw [sub_self, sub_self] at h
    exact h
  have hczero : ∀ τ ∈ Ici (0:ℝ), c τ 0 = 0 := by
    intro τ hτ
    have h1 := hinteg τ hτ 0
    have h2 : ∀ s ∈ uIcc (0:ℝ) τ,
        ((-(2 * Real.pi * ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0 +
          lerayProj 0 (convFull (c s) 0)) = 0 := by
      intro s hs
      have hsIci : s ∈ Ici (0:ℝ) := by
        rw [uIcc_of_le (mem_Ici.mp hτ)] at hs
        exact mem_Ici.mpr hs.1
      rw [hfreq0]
      simp only [norm_zero]
      rw [convFull_zero_of_divFree (hstr s hsIci).2, hP0, add_zero]
      norm_num
    rw [intervalIntegral.integral_congr h2] at h1
    rw [hmean] at h1
    simpa using h1
  refine ⟨u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- initial value
    funext j
    rw [hudef]
    show synthT j (c (2 * Real.pi * 0)) = u₀ j
    rw [mul_zero, hc0]
    exact synthT_extractCoeff u₀ hE₀ j
  · -- continuity
    intro j
    have h1 : ContinuousOn (fun τ => synthT j (c τ)) (Ici (0:ℝ)) :=
      continuousOn_synthT (Z := ens c₀)
        (tsum_nonneg fun l => by positivity)
        (fun τ hτ => (hsummab τ hτ).1) (fun τ hτ => (hsummab τ hτ).2)
        (fun τ hτ => (htrap τ hτ).2.1) hccont j
    have h2 : ContinuousOn (fun t : ℝ => 2 * Real.pi * t) (Ici (0:ℝ)) :=
      (continuous_const.mul continuous_id).continuousOn
    exact h1.comp h2 hclock
  · -- reality
    intro t ht j
    exact synthT_real (hsummab _ (hclock t ht)).1 (hstr _ (hclock t ht)).1 j
  · -- spectral divergence-freeness
    intro t ht k
    have h := synthT_divFree_spectral (hsummab _ (hclock t ht)).1
      (hstr _ (hclock t ht)).2 k
    exact h
  · -- the energy trap
    intro t ht
    have h1 : (∑ j : Fin 3, ‖u t j‖ ^ (2:ℝ)) = en (c (2 * Real.pi * t)) :=
      sum_norm_synthT_sq (hsummab _ (hclock t ht)).1
    rw [h1, ← hen₀]
    exact (htrap _ (hclock t ht)).1
  · -- the enstrophy trap
    intro t ht
    rw [hext t ht]
    exact (htrap _ (hclock t ht)).2.1
  · -- enstrophy summability along the flow
    intro t ht
    rw [hext t ht]
    exact (hsummab _ (hclock t ht)).2
  · -- mean-zero along the flow
    intro t ht
    rw [hext t ht]
    exact hczero _ (hclock t ht)
  · -- the calibrated weak equation
    intro F w hw hwdiv t ht
    -- budgets for the spectral-weak identity
    have hb : ∀ τ ∈ Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
        ∑ l ∈ G, ‖c τ l‖ ^ 2 ≤ en c₀ := fun τ hτ G =>
      ((hsummab τ hτ).1.sum_le_tsum G (fun l _ => sq_nonneg _)).trans
        (htrap τ hτ).1
    have hwb : ∀ τ ∈ Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
        ∑ l ∈ G, ‖freq l‖ ^ 2 * ‖c τ l‖ ^ 2 ≤ ens c₀ := fun τ hτ G =>
      ((hsummab τ hτ).2.sum_le_tsum G (fun l _ => by positivity)).trans
        (htrap τ hτ).2.1
    have hweak := spectral_weak_equation
      (tsum_nonneg fun l => sq_nonneg _) (tsum_nonneg fun l => by positivity)
      (fun τ hτ => (hsummab τ hτ).1) hb hwb hw hwdiv hccont hinteg
      (2 * Real.pi * t) (hclock t ht)
    -- rewrite through the extraction round trip
    have hrw : ∀ s ∈ Ici (0:ℝ), ∀ k ∈ F,
        inner ℂ (w k) (extractCoeff (u s) k) = inner ℂ (w k) (c (2 * Real.pi * s) k) :=
      fun s hs k _ => by rw [hext s hs]
    -- the time-stretch on the scalar identity (rw unifies the integrand)
    rw [tb_integral_stretch] at hweak
    -- assemble
    calc (∑ k ∈ F, inner ℂ (w k) (extractCoeff (u t) k))
        = ∑ k ∈ F, inner ℂ (w k) (c (2 * Real.pi * t) k) := by
          rw [hext t ht]
      _ = (∑ k ∈ F, inner ℂ (w k) (c₀ k)) + _ := hweak
      _ = (∑ k ∈ F, inner ℂ (w k) (extractCoeff u₀ k)) + _ := by rw [hc₀def]
      _ = _ := by
          congr 1
          refine intervalIntegral.integral_congr fun s hs => ?_
          have hs' : s ∈ Ici (0:ℝ) := by
            rw [uIcc_of_le (mem_Ici.mp ht)] at hs
            exact mem_Ici.mpr hs.1
          rw [hext s hs', Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          push_cast
          ring

/-- Mode extraction of an L²-continuous curve is continuous (per mode). -/
private lemma tb_extract_mode_cont {u : ℝ → Fin 3 → L2T3}
    (hu : ∀ j, ContinuousOn (fun t => u t j) (Ici (0:ℝ))) (k : Fin 3 → ℤ) :
    ContinuousOn (fun t => extractCoeff (u t) k) (Ici (0:ℝ)) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- component thresholds from the three L²-continuities
  have hδj : ∀ j : Fin 3, ∃ δ, 0 < δ ∧ ∀ s ∈ Ici (0:ℝ),
      dist s t < δ → dist (u s j) (u t j) < ε / 2 := by
    intro j
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousWithinAt_iff.mp (hu j t ht) (ε / 2)
      (by positivity)
    exact ⟨δ, hδ0, fun s hs hst => hδ hs hst⟩
  choose δf hδf0 hδf using hδj
  refine ⟨min (δf 0) (min (δf 1) (δf 2)),
    lt_min (hδf0 0) (lt_min (hδf0 1) (hδf0 2)), ?_⟩
  intro s hs hst
  have hcomp : ∀ j : Fin 3, ‖u s j - u t j‖ ^ (2:ℝ) < (ε / 2) ^ 2 := by
    intro j
    have h1 : dist s t < δf j := by
      fin_cases j <;> [exact lt_of_lt_of_le hst (le_min_iff.mp le_rfl).1;
        exact lt_of_lt_of_le hst ((le_min_iff.mp (min_le_right _ _)).1);
        exact lt_of_lt_of_le hst ((le_min_iff.mp (min_le_right _ _)).2)]
    have h2 := hδf j s hs h1
    rw [dist_eq_norm] at h2
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    exact pow_lt_pow_left₀ h2 (norm_nonneg _) (by norm_num)
  have hlip := extractCoeff_lipschitz (u s) (u t) k
  have hsum : (∑ j : Fin 3, ‖u s j - u t j‖ ^ (2:ℝ)) < 3 * (ε / 2) ^ 2 := by
    have h := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 3)))
      ⟨0, Finset.mem_univ 0⟩ (fun j _ => hcomp j)
    simpa using h
  rw [dist_eq_norm]
  have h3 : ‖extractCoeff (u s) k - extractCoeff (u t) k‖ ^ 2 < 3 * (ε / 2) ^ 2 :=
    lt_of_le_of_lt hlip hsum
  have h4 : 3 * (ε / 2) ^ 2 < ε ^ 2 := by nlinarith
  have h5 : ‖extractCoeff (u s) k - extractCoeff (u t) k‖ ^ 2 < ε ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h5

/-- **UNIQUENESS ON THE TORUS.** Two members of the torus solution class —
L²-continuous, spectrally divergence-free, mean-zero, enstrophy-budgeted
fields satisfying the calibrated weak Navier-Stokes equation from the same
initial field — agree at every time. Pulled back through coefficient
extraction to `theorem_B_unique`. -/
theorem theorem_B_torus_unique {ν E Z : ℝ} (hν : 0 < ν) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {u v : ℝ → Fin 3 → L2T3}
    (huv0 : u 0 = v 0)
    (hucont : ∀ j, ContinuousOn (fun t => u t j) (Ici (0:ℝ)))
    (hvcont : ∀ j, ContinuousOn (fun t => v t j) (Ici (0:ℝ)))
    (hudiv : ∀ t ∈ Ici (0:ℝ), DivFree (extractCoeff (u t)))
    (hvdiv : ∀ t ∈ Ici (0:ℝ), DivFree (extractCoeff (v t)))
    (humean : ∀ t ∈ Ici (0:ℝ), extractCoeff (u t) 0 = 0)
    (hvmean : ∀ t ∈ Ici (0:ℝ), extractCoeff (v t) 0 = 0)
    (hub : ∀ t ∈ Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
      (∑ l ∈ G, ‖extractCoeff (u t) l‖ ^ 2 ≤ E) ∧
      (∑ l ∈ G, ‖freq l‖ ^ 2 * ‖extractCoeff (u t) l‖ ^ 2 ≤ Z))
    (hvb : ∀ t ∈ Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
      (∑ l ∈ G, ‖extractCoeff (v t) l‖ ^ 2 ≤ E) ∧
      (∑ l ∈ G, ‖freq l‖ ^ 2 * ‖extractCoeff (v t) l‖ ^ 2 ≤ Z))
    (huweak : ∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
      (∀ k, k ∉ F → w k = 0) → DivFree w → ∀ t ∈ Ici (0:ℝ),
      (∑ k ∈ F, inner ℂ (w k) (extractCoeff (u t) k)) =
        (∑ k ∈ F, inner ℂ (w k) (extractCoeff (u 0) k)) + ∫ s in (0:ℝ)..t,
          (∑ k ∈ F, ((-(ν * (2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) *
              inner ℂ (w k) (extractCoeff (u s) k)
            + (2 * Real.pi) * inner ℂ (w k) (convFull (extractCoeff (u s)) k))))
    (hvweak : ∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
      (∀ k, k ∉ F → w k = 0) → DivFree w → ∀ t ∈ Ici (0:ℝ),
      (∑ k ∈ F, inner ℂ (w k) (extractCoeff (v t) k)) =
        (∑ k ∈ F, inner ℂ (w k) (extractCoeff (v 0) k)) + ∫ s in (0:ℝ)..t,
          (∑ k ∈ F, ((-(ν * (2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) *
              inner ℂ (w k) (extractCoeff (v s) k)
            + (2 * Real.pi) * inner ℂ (w k) (convFull (extractCoeff (v s)) k)))) :
    ∀ t ∈ Ici (0:ℝ), ∀ j, u t j = v t j := by
  have h2π : (2 * Real.pi) ≠ 0 := ne_of_gt tb_two_pi_pos
  have hdivpos : ∀ τ ∈ Ici (0:ℝ), τ / (2 * Real.pi) ∈ Ici (0:ℝ) := fun τ hτ =>
    mem_Ici.mpr (div_nonneg (mem_Ici.mp hτ) tb_two_pi_pos.le)
  set νl : ℝ := 2 * Real.pi * ν with hνl
  -- the uncalibrated (lattice-clock) weak identity, in extract-form
  have hlat : ∀ (uu : ℝ → Fin 3 → L2T3),
      (∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
        (∀ k, k ∉ F → w k = 0) → DivFree w → ∀ t ∈ Ici (0:ℝ),
        (∑ k ∈ F, inner ℂ (w k) (extractCoeff (uu t) k)) =
          (∑ k ∈ F, inner ℂ (w k) (extractCoeff (uu 0) k)) + ∫ s in (0:ℝ)..t,
            (∑ k ∈ F, ((-(ν * (2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) *
                inner ℂ (w k) (extractCoeff (uu s) k)
              + (2 * Real.pi) * inner ℂ (w k) (convFull (extractCoeff (uu s)) k)))) →
      ∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
        (∀ k, k ∉ F → w k = 0) → DivFree w → ∀ τ ∈ Ici (0:ℝ),
        (∑ k ∈ F, inner ℂ (w k) (extractCoeff (uu (τ / (2 * Real.pi))) k)) =
          (∑ k ∈ F, inner ℂ (w k) (extractCoeff (uu ((0:ℝ) / (2 * Real.pi))) k)) +
            ∫ σ in (0:ℝ)..τ,
            (∑ k ∈ F, ((-(νl * ‖freq k‖ ^ 2)) *
                inner ℂ (w k) (extractCoeff (uu (σ / (2 * Real.pi))) k)
              + inner ℂ (w k) (convFull (extractCoeff (uu (σ / (2 * Real.pi)))) k))) := by
    intro uu hweak F w hw hwdiv τ hτ
    have hphys := hweak F w hw hwdiv (τ / (2 * Real.pi)) (hdivpos τ hτ)
    have hτeq : 2 * Real.pi * (τ / (2 * Real.pi)) = τ := by field_simp
    have hstr := tb_integral_stretch
      (fun σ => ∑ k ∈ F, ((-(νl * ‖freq k‖ ^ 2)) *
          inner ℂ (w k) (extractCoeff (uu (σ / (2 * Real.pi))) k)
        + inner ℂ (w k) (convFull (extractCoeff (uu (σ / (2 * Real.pi)))) k)))
      (τ / (2 * Real.pi))
    rw [hτeq] at hstr
    rw [hstr, zero_div]
    -- match against the physical identity
    rw [hphys]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hcan : 2 * Real.pi * s / (2 * Real.pi) = s := by
      rw [mul_comm (2 * Real.pi) s, mul_div_assoc, div_self h2π, mul_one]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hcan, hνl]
    push_cast
    ring
  -- the mode integral equations for both lattice-clock flows
  have hνlat : (0:ℝ) < νl := by rw [hνl]; positivity
  have hdivmap : ContinuousOn (fun σ : ℝ => σ / (2 * Real.pi)) (Ici (0:ℝ)) :=
    (continuous_id.div_const _).continuousOn
  have hmode : ∀ (uu : ℝ → Fin 3 → L2T3),
      (∀ j, ContinuousOn (fun t => uu t j) (Ici (0:ℝ))) →
      (∀ t ∈ Ici (0:ℝ), DivFree (extractCoeff (uu t))) →
      (∀ t ∈ Ici (0:ℝ), extractCoeff (uu t) 0 = 0) →
      (∀ t ∈ Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
        (∑ l ∈ G, ‖extractCoeff (uu t) l‖ ^ 2 ≤ E) ∧
        (∑ l ∈ G, ‖freq l‖ ^ 2 * ‖extractCoeff (uu t) l‖ ^ 2 ≤ Z)) →
      (∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
        (∀ k, k ∉ F → w k = 0) → DivFree w → ∀ t ∈ Ici (0:ℝ),
        (∑ k ∈ F, inner ℂ (w k) (extractCoeff (uu t) k)) =
          (∑ k ∈ F, inner ℂ (w k) (extractCoeff (uu 0) k)) + ∫ s in (0:ℝ)..t,
            (∑ k ∈ F, ((-(ν * (2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) *
                inner ℂ (w k) (extractCoeff (uu s) k)
              + (2 * Real.pi) * inner ℂ (w k) (convFull (extractCoeff (uu s)) k)))) →
      ∀ τ ∈ Ici (0:ℝ), ∀ k,
        extractCoeff (uu (τ / (2 * Real.pi))) k =
          extractCoeff (uu ((0:ℝ) / (2 * Real.pi))) k + ∫ σ in (0:ℝ)..τ,
            ((-(νl * ‖freq k‖ ^ 2)) •
              extractCoeff (uu (σ / (2 * Real.pi))) k +
              lerayProj k (convFull (extractCoeff (uu (σ / (2 * Real.pi)))) k)) := by
    intro uu hcont hdiv hmean hbud hweak
    exact mode_equation_of_weak (ν := νl) hνlat hE0 hZ0
      (c := fun τ => extractCoeff (uu (τ / (2 * Real.pi))))
      (fun k => (tb_extract_mode_cont hcont k).comp hdivmap hdivpos)
      (fun τ _ => summable_extractCoeff _)
      (fun τ hτ G => (hbud _ (hdivpos τ hτ) G).1)
      (fun τ hτ G => (hbud _ (hdivpos τ hτ) G).2)
      (fun τ hτ => hdiv _ (hdivpos τ hτ))
      (fun τ hτ => hmean _ (hdivpos τ hτ))
      (hlat uu hweak)
  have hcu := hmode u hucont hudiv humean hub huweak
  have hcv := hmode v hvcont hvdiv hvmean hvb hvweak
  -- initial agreement of the lattice flows
  have hinit : ∀ k, extractCoeff (u ((0:ℝ) / (2 * Real.pi))) k =
      extractCoeff (v ((0:ℝ) / (2 * Real.pi))) k := by
    intro k
    rw [zero_div, huv0]
  -- uniqueness on every lattice horizon
  have hagree : ∀ τ ∈ Ici (0:ℝ), ∀ k,
      extractCoeff (u (τ / (2 * Real.pi))) k =
        extractCoeff (v (τ / (2 * Real.pi))) k := by
    intro τ hτ k
    have hIccIci : ∀ {σ : ℝ}, σ ∈ Icc (0:ℝ) τ → σ ∈ Ici (0:ℝ) :=
      fun hσ => mem_Ici.mpr hσ.1
    have huniq := theorem_B_unique (ν := νl) (E := E) (Z := Z)
      (T := τ) hνlat (mem_Ici.mp hτ)
      (c₀ := fun k' => extractCoeff (u ((0:ℝ) / (2 * Real.pi))) k')
      (c₁ := fun σ => extractCoeff (u (σ / (2 * Real.pi))))
      (c₂ := fun σ => extractCoeff (v (σ / (2 * Real.pi))))
      rfl (funext fun k' => (hinit k').symm)
      (fun k' => ((tb_extract_mode_cont hucont k').comp hdivmap hdivpos).mono
        Icc_subset_Ici_self)
      (fun k' => ((tb_extract_mode_cont hvcont k').comp hdivmap hdivpos).mono
        Icc_subset_Ici_self)
      (fun σ hσ => ⟨summable_extractCoeff _,
        summable_of_sum_le (fun l => by positivity)
          (fun G => (hub _ (hdivpos σ (hIccIci hσ)) G).2)⟩)
      (fun σ hσ => ⟨summable_extractCoeff _,
        summable_of_sum_le (fun l => by positivity)
          (fun G => (hvb _ (hdivpos σ (hIccIci hσ)) G).2)⟩)
      (fun σ hσ => ⟨Real.tsum_le_of_sum_le (fun l => sq_nonneg _)
          (fun G => (hub _ (hdivpos σ (hIccIci hσ)) G).1),
        Real.tsum_le_of_sum_le (fun l => by positivity)
          (fun G => (hub _ (hdivpos σ (hIccIci hσ)) G).2)⟩)
      (fun σ hσ => ⟨Real.tsum_le_of_sum_le (fun l => sq_nonneg _)
          (fun G => (hvb _ (hdivpos σ (hIccIci hσ)) G).1),
        Real.tsum_le_of_sum_le (fun l => by positivity)
          (fun G => (hvb _ (hdivpos σ (hIccIci hσ)) G).2)⟩)
      (fun σ hσ => hudiv _ (hdivpos σ (hIccIci hσ)))
      (fun σ hσ => hvdiv _ (hdivpos σ (hIccIci hσ)))
      (fun σ hσ k' => hcu σ (hIccIci hσ) k')
      (fun σ hσ k' => by
        have h := hcv σ (hIccIci hσ) k'
        rwa [← hinit k'] at h)
    exact huniq τ ⟨mem_Ici.mp hτ, le_refl τ⟩ k
  -- recover field equality
  intro t ht j
  have hcan : 2 * Real.pi * t / (2 * Real.pi) = t := by
    rw [mul_comm (2 * Real.pi) t, mul_div_assoc, div_self h2π, mul_one]
  have h1 := hagree (2 * Real.pi * t)
    (mem_Ici.mpr (mul_nonneg tb_two_pi_pos.le (mem_Ici.mp ht)))
  have h2 : extractCoeff (u t) = extractCoeff (v t) := by
    funext k
    have := h1 k
    rwa [hcan] at this
  calc u t j = synthT j (extractCoeff (u t)) :=
        (synthT_extractCoeff (u t) (summable_extractCoeff _) j).symm
    _ = synthT j (extractCoeff (v t)) := by rw [h2]
    _ = v t j := synthT_extractCoeff (v t) (summable_extractCoeff _) j

end

end TheoremB
