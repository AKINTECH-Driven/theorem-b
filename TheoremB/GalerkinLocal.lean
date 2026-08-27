/-
  TheoremB/GalerkinLocal.lean
  M5 wave 1 of the Theorem B campaign (27 Aug 2026).

  The INTERVAL-LOCALIZED Galerkin chain, plus uniqueness: the honest forms
  for CONSTRUCTED flows.  The prior capstones hypothesize the coefficient
  ODE at every t : ℝ, but dissipative quadratic systems generically blow up
  backward in time, so a constructed forward flow cannot satisfy them; here
  every dynamical hypothesis lives on Icc 0 T only.

  Contents: defect_vanishes_on' (window-ODE Gronwall), divFree_propagates_on
  and realField_propagates_on (forward propagation on the window),
  galerkin_conditional_trap_on (localized abstract trap, via finite-sum
  surrogates and EventuallyEq transfer at interior points),
  two_flow_forcing_bound and ns_galerkin_unique_on (uniqueness via the
  no-conjugation defect telescope), and the capstone
  ns_galerkin_trap_zero_data_on.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.RealityProp

namespace TheoremB

open Set

/-! ### Private transplants (localized re-proofs of RealityProp's private layer) -/

/-- Coefficient-wise product rule for the plain (weight-1) energy sum along a
flow: transplant of RealityProp's private `hasDerivAt_sum_sq`. -/
private lemma ppSum_sq {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] {S : Finset (Fin 3 → ℤ)}
    {c : ℝ → (Fin 3 → ℤ) → W} {c' : (Fin 3 → ℤ) → W} {t : ℝ}
    (hderiv : ∀ k, HasDerivAt (fun s : ℝ => c s k) (c' k) t) :
    HasDerivAt (fun s : ℝ => ∑ k ∈ S, ‖c s k‖ ^ 2)
      (∑ k ∈ S, 2 * inner ℝ (c' k) (c t k)) t := by
  have hterm : ∀ k ∈ S, HasDerivAt (fun s : ℝ => ‖c s k‖ ^ 2)
      (2 * inner ℝ (c' k) (c t k)) t := by
    intro k _
    have h1 : HasDerivAt (fun s : ℝ => inner ℝ (c s k) (c s k))
        (inner ℝ (c t k) (c' k) + inner ℝ (c' k) (c t k)) t :=
      (hderiv k).inner ℝ (hderiv k)
    have h2 : (fun s : ℝ => ‖c s k‖ ^ 2) = fun s : ℝ => inner ℝ (c s k) (c s k) := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    have h4 : inner ℝ (c t k) (c' k) + inner ℝ (c' k) (c t k) =
        2 * inner ℝ (c' k) (c t k) := by
      rw [real_inner_comm (c t k) (c' k)]; ring
    rw [h2, ← h4]; exact h1
  have h := HasDerivAt.sum hterm
  have heq : (∑ i ∈ S, fun s : ℝ => ‖c s i‖ ^ 2) =
      fun s : ℝ => ∑ k ∈ S, ‖c s k‖ ^ 2 := by
    funext s
    simp [Finset.sum_apply]
  rwa [heq] at h

/-- Mirror of the public `le_of_deriv_nonpos`, backward monotone direction
(transplant of RealityProp's private `ge_of_deriv_nonneg'`). -/
private lemma ppGe_of_deriv_nonneg {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hc : ContinuousOn f (Icc x y))
    (hd : DifferentiableOn ℝ f (Ioo x y))
    (h' : ∀ t ∈ Ioo x y, 0 ≤ deriv f t) :
    f x ≤ f y := by
  have h := monotoneOn_of_deriv_nonneg (convex_Icc x y) hc
    (by rwa [interior_Icc]) (by rwa [interior_Icc])
  exact h (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

/-- Root-free two-sided Gronwall on an interval containing `0`, with the
`HasDerivAt` hypothesis required ONLY on the window (interval-localized
variant of RealityProp's private `vanish_of_deriv_bounds_on`). -/
private lemma ppVanish_of_deriv_bounds_on {φ D : ℝ → ℝ} {A B a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (hd : ∀ s ∈ Icc a b, HasDerivAt φ (D s) s)
    (hub : ∀ s ∈ Icc a b, D s ≤ A * φ s)
    (hlb : ∀ s ∈ Icc a b, (-B) * φ s ≤ D s)
    (hnn : ∀ s : ℝ, 0 ≤ φ s) (h0 : φ 0 = 0) :
    ∀ t ∈ Icc a b, φ t = 0 := by
  intro t htm
  rcases le_total 0 t with ht | ht
  · -- forward branch on Icc 0 t ⊆ Icc a b
    have hsub : ∀ s ∈ Icc (0:ℝ) t, s ∈ Icc a b := fun s hs =>
      ⟨le_trans ha hs.1, le_trans hs.2 htm.2⟩
    have hψd : ∀ s ∈ Icc (0:ℝ) t, HasDerivAt (fun u : ℝ => Real.exp (-A * u) * φ u)
        (Real.exp (-A * s) * (-A) * φ s + Real.exp (-A * s) * D s) s := by
      intro s hs
      have hlin : HasDerivAt (fun u : ℝ => -A * u) (-A) s := by
        simpa using (hasDerivAt_id s).const_mul (-A)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-A * u))
          (Real.exp (-A * s) * (-A)) s := hlin.exp
      exact hexp.mul (hd s (hsub s hs))
    have hnonpos : ∀ s ∈ Ioo (0 : ℝ) t,
        deriv (fun u : ℝ => Real.exp (-A * u) * φ u) s ≤ 0 := by
      intro s hs
      have hsI : s ∈ Icc (0:ℝ) t := ⟨hs.1.le, hs.2.le⟩
      have hsm : s ∈ Icc a b := hsub s hsI
      rw [(hψd s hsI).deriv]
      nlinarith [mul_le_mul_of_nonneg_left (hub s hsm) (Real.exp_pos (-A * s)).le]
    have hcont : ContinuousOn (fun u : ℝ => Real.exp (-A * u) * φ u) (Icc 0 t) :=
      fun s hs => (hψd s hs).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun u : ℝ => Real.exp (-A * u) * φ u) (Ioo 0 t) :=
      fun s hs => (hψd s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt
    have hle : Real.exp (-A * t) * φ t ≤ Real.exp (-A * 0) * φ 0 :=
      le_of_deriv_nonpos ht hcont hdiff hnonpos
    have h00 : Real.exp (-A * 0) * φ 0 = 0 := by rw [h0]; ring
    have hψ0 : Real.exp (-A * t) * φ t = 0 :=
      le_antisymm (h00 ▸ hle) (mul_nonneg (Real.exp_pos (-A * t)).le (hnn t))
    rcases mul_eq_zero.mp hψ0 with h | h
    · exact absurd h (Real.exp_ne_zero _)
    · exact h
  · -- backward branch on Icc t 0 ⊆ Icc a b
    have hsub : ∀ s ∈ Icc t (0:ℝ), s ∈ Icc a b := fun s hs =>
      ⟨le_trans htm.1 hs.1, le_trans hs.2 hb⟩
    have hχd : ∀ s ∈ Icc t (0:ℝ), HasDerivAt (fun u : ℝ => Real.exp (B * u) * φ u)
        (Real.exp (B * s) * B * φ s + Real.exp (B * s) * D s) s := by
      intro s hs
      have hlin : HasDerivAt (fun u : ℝ => B * u) B s := by
        simpa using (hasDerivAt_id s).const_mul B
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (B * u))
          (Real.exp (B * s) * B) s := hlin.exp
      exact hexp.mul (hd s (hsub s hs))
    have hnonneg : ∀ s ∈ Ioo t (0 : ℝ),
        0 ≤ deriv (fun u : ℝ => Real.exp (B * u) * φ u) s := by
      intro s hs
      have hsI : s ∈ Icc t (0:ℝ) := ⟨hs.1.le, hs.2.le⟩
      have hsm : s ∈ Icc a b := hsub s hsI
      rw [(hχd s hsI).deriv]
      nlinarith [mul_le_mul_of_nonneg_left (hlb s hsm) (Real.exp_pos (B * s)).le]
    have hcont : ContinuousOn (fun u : ℝ => Real.exp (B * u) * φ u) (Icc t 0) :=
      fun s hs => (hχd s hs).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun u : ℝ => Real.exp (B * u) * φ u) (Ioo t 0) :=
      fun s hs => (hχd s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt
    have hle : Real.exp (B * t) * φ t ≤ Real.exp (B * 0) * φ 0 :=
      ppGe_of_deriv_nonneg ht hcont hdiff hnonneg
    have h00 : Real.exp (B * 0) * φ 0 = 0 := by rw [h0]; ring
    have hχ0 : Real.exp (B * t) * φ t = 0 :=
      le_antisymm (h00 ▸ hle) (mul_nonneg (Real.exp_pos (B * t)).le (hnn t))
    rcases mul_eq_zero.mp hχ0 with h | h
    · exact absurd h (Real.exp_ne_zero _)
    · exact h

/-! ## Target 1: interval-localized defect vanishing -/

/-- **Two-sided defect vanishing on an interval containing `0`, with the
defect ODE required only on the window.** -/
theorem defect_vanishes_on' {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : Finset (Fin 3 → ℤ)} {d : ℝ → (Fin 3 → ℤ) → V} {lam : (Fin 3 → ℤ) → ℝ}
    {R : ℝ → (Fin 3 → ℤ) → V} {L a b : ℝ}
    (hL : 0 ≤ L) (ha : a ≤ 0) (hb : 0 ≤ b) (hlam : ∀ k, 0 ≤ lam k)
    (hderiv : ∀ s ∈ Icc a b, ∀ k, HasDerivAt (fun u => d u k) ((-(lam k)) • d s k + R s k) s)
    (hsupp : ∀ (s : ℝ) k, k ∉ S → d s k = 0)
    (hR : ∀ s ∈ Icc a b, ∀ k ∈ S, ‖R s k‖ ^ 2 ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2))
    (h0 : ∀ k, d 0 k = 0) : ∀ t ∈ Icc a b, ∀ k, d t k = 0 := by
  classical
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, ∀ k ∈ S, lam k ≤ Λ :=
    ⟨∑ k ∈ S, lam k, fun k hk => Finset.single_le_sum (fun j _ => hlam j) hk⟩
  have hΦd : ∀ s ∈ Icc a b, HasDerivAt (fun u : ℝ => ∑ j ∈ S, ‖d u j‖ ^ 2)
      (∑ k ∈ S, 2 * inner ℝ ((-(lam k)) • d s k + R s k) (d s k)) s :=
    fun s hs => ppSum_sq (fun k => hderiv s hs k)
  have hpair : ∀ (s : ℝ) (k : Fin 3 → ℤ),
      (2 : ℝ) * inner ℝ ((-(lam k)) • d s k + R s k) (d s k)
        = -(2 * lam k * ‖d s k‖ ^ 2) + 2 * inner ℝ (R s k) (d s k) := by
    intro s k
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hub : ∀ s ∈ Icc a b, ∀ k ∈ S,
      (2 : ℝ) * inner ℝ ((-(lam k)) • d s k + R s k) (d s k)
        ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2 := by
    intro s hs k hk
    rw [hpair s k]
    have h1 : |inner ℝ (R s k) (d s k)| ≤ ‖R s k‖ * ‖d s k‖ :=
      abs_real_inner_le_norm _ _
    have h2 : 2 * (‖R s k‖ * ‖d s k‖) ≤ ‖R s k‖ ^ 2 + ‖d s k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖R s k‖ - ‖d s k‖)]
    have h3 : ‖R s k‖ ^ 2 ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2) := hR s hs k hk
    have h4 : (0 : ℝ) ≤ 2 * lam k * ‖d s k‖ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (hlam k)) (sq_nonneg _)
    have h5 : inner ℝ (R s k) (d s k) ≤ |inner ℝ (R s k) (d s k)| := le_abs_self _
    linarith
  have hlb : ∀ s ∈ Icc a b, ∀ k ∈ S,
      (-(2 * Λ)) * ‖d s k‖ ^ 2 - (L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2)
        ≤ (2 : ℝ) * inner ℝ ((-(lam k)) • d s k + R s k) (d s k) := by
    intro s hs k hk
    rw [hpair s k]
    have h1 : |inner ℝ (R s k) (d s k)| ≤ ‖R s k‖ * ‖d s k‖ :=
      abs_real_inner_le_norm _ _
    have h2 : 2 * (‖R s k‖ * ‖d s k‖) ≤ ‖R s k‖ ^ 2 + ‖d s k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖R s k‖ - ‖d s k‖)]
    have h3 : ‖R s k‖ ^ 2 ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2) := hR s hs k hk
    have h5 : -|inner ℝ (R s k) (d s k)| ≤ inner ℝ (R s k) (d s k) := neg_abs_le _
    have h6 : 2 * lam k * ‖d s k‖ ^ 2 ≤ 2 * Λ * ‖d s k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hΛ k hk]) (sq_nonneg _)
    linarith
  have hDub : ∀ s ∈ Icc a b,
      (∑ k ∈ S, 2 * inner ℝ ((-(lam k)) • d s k + R s k) (d s k))
        ≤ ((S.card : ℝ) * L + 1) * (∑ j ∈ S, ‖d s j‖ ^ 2) := by
    intro s hs
    have h := Finset.sum_le_sum (hub s hs)
    have hsum : ∑ k ∈ S, (L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2)
        = (S.card : ℝ) * (L * (∑ j ∈ S, ‖d s j‖ ^ 2)) + (∑ j ∈ S, ‖d s j‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at h
    linarith
  have hDlb : ∀ s ∈ Icc a b,
      (-(2 * Λ + (S.card : ℝ) * L + 1)) * (∑ j ∈ S, ‖d s j‖ ^ 2)
        ≤ ∑ k ∈ S, 2 * inner ℝ ((-(lam k)) • d s k + R s k) (d s k) := by
    intro s hs
    have h := Finset.sum_le_sum (hlb s hs)
    have hsum : ∑ k ∈ S,
        ((-(2 * Λ)) * ‖d s k‖ ^ 2 - (L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2))
        = (-(2 * Λ)) * (∑ j ∈ S, ‖d s j‖ ^ 2)
          - ((S.card : ℝ) * (L * (∑ j ∈ S, ‖d s j‖ ^ 2)) + (∑ j ∈ S, ‖d s j‖ ^ 2)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at h
    linarith
  have hΦnn : ∀ s : ℝ, (0 : ℝ) ≤ ∑ j ∈ S, ‖d s j‖ ^ 2 :=
    fun s => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hΦ0 : (∑ j ∈ S, ‖d 0 j‖ ^ 2) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [h0 j]; simp
  have hΦ : ∀ t ∈ Icc a b, (∑ j ∈ S, ‖d t j‖ ^ 2) = 0 :=
    ppVanish_of_deriv_bounds_on ha hb hΦd hDub hDlb hΦnn hΦ0
  intro t htm k
  by_cases hk : k ∈ S
  · have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ‖d t j‖)).mp (hΦ t htm) k hk
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  · exact hsupp t k hk

/-! ## Target 2: forward-interval divergence-freeness propagation -/

/-- **Divergence-freeness propagates on `Icc 0 T` under the Leray-projected
ODE required only there**: the divergence component's squared norm has
nonpositive derivative (root-free, no complex exponentials). -/
theorem divFree_propagates_on {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t)
    (h0 : DivFree (c 0)) : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) := by
  intro t htm k
  set lam : ℝ := ν * ‖freq k‖ ^ 2 with hlamdf
  have hlamnn : (0:ℝ) ≤ lam := by
    rw [hlamdf]
    exact mul_nonneg hν (sq_nonneg _)
  set y : ℝ → ℂ := fun s => dotR (c s k) (freq k) with hy
  -- dotR (·, freq k) is linear; transport the derivative componentwise
  have hdotlin : ∀ (a : Vel) (b : Vel),
      dotR (a + b) (freq k) = dotR a (freq k) + dotR b (freq k) := by
    intro a b
    simp [dotR, Finset.sum_add_distrib, add_mul]
  have hdotsmul : ∀ (z : ℝ) (a : Vel),
      dotR (z • a) (freq k) = (z : ℂ) * dotR a (freq k) := by
    intro z a
    simp [dotR, Finset.mul_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hyderiv : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt y (-(lam : ℂ) * y s) s := by
    intro s hs
    have h := hODE s hs k
    have hco : ∀ j : Fin 3, HasDerivAt (fun u => (c u k).ofLp j)
        (((-(lam)) • c s k + lerayProj k (convGal S (c s) k)).ofLp j) s := by
      intro j
      exact ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h
    have hterm : ∀ j : Fin 3, HasDerivAt
        (fun u => (c u k).ofLp j * (((freq k).ofLp j : ℝ) : ℂ))
        ((((-(lam)) • c s k + lerayProj k (convGal S (c s) k)).ofLp j) *
          (((freq k).ofLp j : ℝ) : ℂ)) s := fun j => (hco j).mul_const _
    have hsum := HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    have heq1 : (∑ j ∈ Finset.univ, fun u => (c u k).ofLp j *
        (((freq k).ofLp j : ℝ) : ℂ)) = y := by
      funext u
      simp [hy, dotR, Finset.sum_apply]
    rw [heq1] at hsum
    have heq2 : (∑ j, (((-(lam)) • c s k +
        lerayProj k (convGal S (c s) k)).ofLp j) * (((freq k).ofLp j : ℝ) : ℂ)) =
        -(lam : ℂ) * y s := by
      have hdd : (∑ j, (((-(lam)) • c s k +
          lerayProj k (convGal S (c s) k)).ofLp j) * (((freq k).ofLp j : ℝ) : ℂ)) =
          dotR ((-(lam)) • c s k + lerayProj k (convGal S (c s) k)) (freq k) := rfl
      rw [hdd, hdotlin, hdotsmul, dotR_lerayProj_freq, add_zero, hy]
      push_cast
      ring
    rw [heq2] at hsum
    exact hsum
  -- convert the derivative value to real-smul form
  have hyderiv' : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt y ((-lam) • y s) s := by
    intro s hs
    have h := hyderiv s hs
    have hv : -(lam : ℂ) * y s = (-lam) • y s := by
      rw [Complex.real_smul]
      push_cast
      ring
    rwa [hv] at h
  -- the squared norm of the divergence component decays
  have hφd : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt (fun u : ℝ => ‖y u‖ ^ 2)
      (2 * inner ℝ ((-lam) • y s) (y s)) s := by
    intro s hs
    have hyd := hyderiv' s hs
    have h1 : HasDerivAt (fun u : ℝ => inner ℝ (y u) (y u))
        (inner ℝ (y s) ((-lam) • y s) + inner ℝ ((-lam) • y s) (y s)) s :=
      hyd.inner ℝ hyd
    have h2 : (fun u : ℝ => ‖y u‖ ^ 2) = fun u : ℝ => inner ℝ (y u) (y u) := by
      funext u
      rw [real_inner_self_eq_norm_sq]
    have h4 : inner ℝ (y s) ((-lam) • y s) + inner ℝ ((-lam) • y s) (y s) =
        2 * inner ℝ ((-lam) • y s) (y s) := by
      rw [real_inner_comm (y s) ((-lam) • y s)]; ring
    rw [h2, ← h4]
    exact h1
  have ht0 : (0:ℝ) ≤ t := htm.1
  have hsubI : ∀ s ∈ Icc (0:ℝ) t, s ∈ Icc (0:ℝ) T := fun s hs =>
    ⟨hs.1, le_trans hs.2 htm.2⟩
  have hnonpos : ∀ s ∈ Ioo (0:ℝ) t, deriv (fun u : ℝ => ‖y u‖ ^ 2) s ≤ 0 := by
    intro s hs
    have hsm : s ∈ Icc (0:ℝ) T := hsubI s ⟨hs.1.le, hs.2.le⟩
    rw [(hφd s hsm).deriv]
    have hv : (2:ℝ) * inner ℝ ((-lam) • y s) (y s) = -(2 * lam) * ‖y s‖ ^ 2 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      ring
    rw [hv]
    have h1 : (0:ℝ) ≤ 2 * lam * ‖y s‖ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hlamnn) (sq_nonneg _)
    linarith
  have hcont : ContinuousOn (fun u : ℝ => ‖y u‖ ^ 2) (Icc 0 t) :=
    fun s hs => (hφd s (hsubI s hs)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun u : ℝ => ‖y u‖ ^ 2) (Ioo 0 t) :=
    fun s hs => (hφd s (hsubI s ⟨hs.1.le, hs.2.le⟩)).differentiableAt.differentiableWithinAt
  have hle : ‖y t‖ ^ 2 ≤ ‖y 0‖ ^ 2 := le_of_deriv_nonpos ht0 hcont hdiff hnonpos
  have hy0 : y 0 = 0 := h0 k
  have hz : ‖y t‖ ^ 2 = 0 := by
    have h00 : ‖y 0‖ ^ 2 = 0 := by rw [hy0, norm_zero]; norm_num
    have hnn : (0:ℝ) ≤ ‖y t‖ ^ 2 := sq_nonneg _
    linarith
  have hyt : y t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact hyt

/-! ## Target 3: interval-localized reality propagation -/

private lemma ppConjVel_zero : conjVel 0 = 0 := by
  ext j
  simp [conjVel]

private lemma ppConjVel_real_smul (r : ℝ) (v : Vel) :
    conjVel (r • v) = r • conjVel v :=
  conjVelL.map_smul r v

private lemma ppConjVel_add (a b : Vel) : conjVel (a + b) = conjVel a + conjVel b :=
  conjVelL.map_add a b

/-- **Reality propagates on `Icc 0 T` under the Leray-projected Galerkin ODE
required only there**: the (mode-clamped) conjugation defect obeys a damped
linear system on the window, and the interval Gronwall kills it. -/
theorem realField_propagates_on {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    (hSsym : ∀ k ∈ S, -k ∈ S) {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0)
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t)
    (h0real : RealField (c 0)) : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) := by
  classical
  by_cases hT : (0:ℝ) ≤ T
  · -- main case: the window is nonempty
    -- the mode-clamped conjugation defect (clamping restores GLOBAL support)
    set d : ℝ → (Fin 3 → ℤ) → Vel :=
      fun t k => if k ∈ S then c t (-k) - conjVel (c t k) else 0 with hdDef
    set R : ℝ → (Fin 3 → ℤ) → Vel :=
      fun t k => if k ∈ S then lerayProj (-k) (convGal S (c t) (-k)) -
        conjVel (lerayProj k (convGal S (c t) k)) else 0 with hRDef
    set lam : (Fin 3 → ℤ) → ℝ := fun k => ν * ‖freq k‖ ^ 2 with hlamDef
    have hlamnn : ∀ k, 0 ≤ lam k := by
      intro k
      simp only [hlamDef]
      exact mul_nonneg hν (sq_nonneg _)
    have hSnot : ∀ k, k ∉ S → -k ∉ S := by
      intro k hk hnk
      exact hk (by simpa using hSsym (-k) hnk)
    -- the clamped defect ODE at points of the window
    have hdderiv : ∀ s ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun u => d u k)
        ((-(lam k)) • d s k + R s k) s := by
      intro s hs k
      by_cases hk : k ∈ S
      · have h1 : HasDerivAt (fun u => c u (-k))
            ((-(ν * ‖freq (-k)‖ ^ 2)) • c s (-k) +
              lerayProj (-k) (convGal S (c s) (-k))) s := hODE s hs (-k)
        have hfneg : ‖freq (-k)‖ = ‖freq k‖ := by rw [freq_neg, norm_neg]
        rw [hfneg] at h1
        have h2 : HasDerivAt (fun u => conjVel (c u k))
            (conjVel ((-(ν * ‖freq k‖ ^ 2)) • c s k +
              lerayProj k (convGal S (c s) k))) s := by
          have := (conjVelL.hasFDerivAt (x := c s k)).comp_hasDerivAt s (hODE s hs k)
          exact this
        have h2' : HasDerivAt (fun u => conjVel (c u k))
            ((-(ν * ‖freq k‖ ^ 2)) • conjVel (c s k) +
              conjVel (lerayProj k (convGal S (c s) k))) s := by
          rwa [ppConjVel_add, ppConjVel_real_smul] at h2
        have h3 := h1.sub h2'
        have hfun : ((fun u => c u (-k)) - fun u => conjVel (c u k)) = fun u => d u k := by
          funext u
          simp only [Pi.sub_apply, hdDef, if_pos hk]
        have hval : ((-(ν * ‖freq k‖ ^ 2)) • c s (-k) +
              lerayProj (-k) (convGal S (c s) (-k))) -
            ((-(ν * ‖freq k‖ ^ 2)) • conjVel (c s k) +
              conjVel (lerayProj k (convGal S (c s) k))) =
            (-(lam k)) • d s k + R s k := by
          simp only [hlamDef, hdDef, hRDef, if_pos hk, smul_sub]
          abel
        rw [hfun, hval] at h3
        exact h3
      · have hzero : (fun u => d u k) = fun _ : ℝ => (0 : Vel) := by
          funext u
          simp only [hdDef, if_neg hk]
        have hval : (-(lam k)) • d s k + R s k = 0 := by
          simp only [hdDef, hRDef, if_neg hk, smul_zero, add_zero]
        rw [hzero, hval]
        exact hasDerivAt_const s 0
    have hdsupp : ∀ (s : ℝ) k, k ∉ S → d s k = 0 := by
      intro s k hk
      simp only [hdDef, if_neg hk]
    have hd0 : ∀ k, d 0 k = 0 := by
      intro k
      by_cases hk : k ∈ S
      · simp only [hdDef, if_pos hk]
        rw [h0real k, sub_self]
      · simp only [hdDef, if_neg hk]
    -- bound the field on the compact window
    have hne : (Icc (0:ℝ) T).Nonempty := ⟨0, le_refl 0, hT⟩
    obtain ⟨M, hM0, hMb⟩ : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (0:ℝ) T, ∀ j, ‖c s j‖ ≤ M := by
      have hmode : ∀ j, ContinuousOn (fun s : ℝ => c s j) (Icc (0:ℝ) T) :=
        fun j s hs => ((hODE s hs j).continuousAt).continuousWithinAt
      have hcont : ContinuousOn (fun s : ℝ => ∑ j ∈ S, ‖c s j‖) (Icc (0:ℝ) T) :=
        continuousOn_finsetSum S fun j _ => (hmode j).norm
      obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
      refine ⟨∑ j ∈ S, ‖c s₀ j‖,
        Finset.sum_nonneg fun j _ => norm_nonneg _, ?_⟩
      intro s hs j
      by_cases hj : j ∈ S
      · calc ‖c s j‖ ≤ ∑ i ∈ S, ‖c s i‖ :=
              Finset.single_le_sum (f := fun i => ‖c s i‖)
                (fun i _ => norm_nonneg _) hj
          _ ≤ ∑ i ∈ S, ‖c s₀ i‖ := hmax hs
      · rw [hsupp s hs j hj]
        simp only [norm_zero]
        exact Finset.sum_nonneg fun i _ => norm_nonneg _
    -- the Lipschitz constant from the forcing bound
    obtain ⟨C, hC0, hCb⟩ := defect_forcing_bound hSsym
    have hRb : ∀ s ∈ Icc (0:ℝ) T, ∀ j ∈ S,
        ‖R s j‖ ^ 2 ≤ (C * M ^ 2) * (∑ i ∈ S, ‖d s i‖ ^ 2) := by
      intro s hs j hj
      have hb := hCb (c := c s) (hsupp s hs) hM0 (fun i => hMb s hs i) j
      have hRj : R s j = lerayProj (-j) (convGal S (c s) (-j)) -
          conjVel (lerayProj j (convGal S (c s) j)) := by
        simp only [hRDef, if_pos hj]
      have hsum : (∑ i ∈ S, ‖d s i‖ ^ 2) = ∑ i ∈ S, ‖c s (-i) - conjVel (c s i)‖ ^ 2 :=
        Finset.sum_congr rfl fun i hi => by simp only [hdDef, if_pos hi]
      rw [hRj, hsum]
      exact hb
    -- the interval Gronwall
    have hvan : ∀ t ∈ Icc (0:ℝ) T, ∀ k, d t k = 0 :=
      defect_vanishes_on' (mul_nonneg hC0 (sq_nonneg M)) (le_refl (0:ℝ)) hT hlamnn
        hdderiv hdsupp hRb hd0
    -- unfold the defect vanishing into the reality statement
    intro t ht k
    by_cases hk : k ∈ S
    · have hz := hvan t ht k
      simp only [hdDef, if_pos hk] at hz
      exact sub_eq_zero.mp hz
    · rw [hsupp t ht (-k) (hSnot k hk), hsupp t ht k hk, ppConjVel_zero]
  · -- ¬ 0 ≤ T: the window is empty, the statement is vacuous
    intro t ht
    exact absurd (ht.1.trans ht.2) hT

/-! ## The two-flow forcing bound -/

/-! ### Transplanted private helpers (tf-prefixed) -/

private lemma tfDotR_zero_left (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

private lemma tfDotR_sub_left (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (v - w) r = dotR v r - dotR w r := by
  simp only [dotR, WithLp.ofLp_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma tfCastCV_zero : castCV 0 = 0 := by
  ext j
  simp [castCV]

private lemma tfFreq_zero : freq (0 : Fin 3 → ℤ) = 0 := by
  ext j
  simp [freq]

private lemma tfLerayProj_sub (k : Fin 3 → ℤ) (v w : Vel) :
    lerayProj k (v - w) = lerayProj k v - lerayProj k w := by
  simp only [lerayProj, tfDotR_sub_left, sub_div, sub_smul]
  abel

private lemma tfLerayProj_zero (k : Fin 3 → ℤ) : lerayProj k 0 = 0 := by
  simp [lerayProj, tfDotR_zero_left]

private lemma tfNorm_lerayProj_le (k : Fin 3 → ℤ) (w : Vel) :
    ‖lerayProj k w‖ ≤ 2 * ‖w‖ := by
  by_cases hk : k = 0
  · subst hk
    simp only [lerayProj, tfFreq_zero, tfCastCV_zero, smul_zero, sub_zero]
    linarith [norm_nonneg w]
  · have h1 : (1 : ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
    have hpos : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos h1
    have hstep : ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ ≤ ‖w‖ := by
      rw [norm_smul, norm_div, norm_castCV]
      have hcast : ‖((‖freq k‖ ^ 2 : ℝ) : ℂ)‖ = ‖freq k‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg _)
      rw [hcast, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖freq k‖ ^ 2)]
      calc ‖dotR w (freq k)‖ * ‖freq k‖
          ≤ (‖freq k‖ * ‖w‖) * ‖freq k‖ :=
            mul_le_mul_of_nonneg_right (norm_dotR_le w (freq k)) (norm_nonneg _)
        _ = ‖w‖ * ‖freq k‖ ^ 2 := by ring
    have htri : ‖lerayProj k w‖
        ≤ ‖w‖ + ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ := by
      simp only [lerayProj]
      exact norm_sub_le _ _
    linarith

private lemma tfFreqBound (S : Finset (Fin 3 → ℤ)) :
    ∀ x ∈ S, ∀ y ∈ S, ‖freq (x - y)‖ ≤ 2 * ∑ j ∈ S, ‖freq j‖ := by
  intro x hx y hy
  have h1 : ‖freq x‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hx
  have h2 : ‖freq y‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hy
  rw [freq_sub]
  calc ‖freq x - freq y‖ ≤ ‖freq x‖ + ‖freq y‖ := norm_sub_le _ _
    _ ≤ 2 * ∑ j ∈ S, ‖freq j‖ := by linarith

private lemma tfSq_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simpa using h

/-! ### The two-flow forcing bound -/

theorem two_flow_forcing_bound {S : Finset (Fin 3 → ℤ)} :
    ∃ C, 0 ≤ C ∧ ∀ {c₁ c₂ : (Fin 3 → ℤ) → Vel},
      (∀ k, k ∉ S → c₁ k = 0) → (∀ k, k ∉ S → c₂ k = 0) →
      ∀ {M : ℝ}, 0 ≤ M → (∀ k, ‖c₁ k‖ ≤ M) → (∀ k, ‖c₂ k‖ ≤ M) →
      ∀ k, ‖lerayProj k (convGal S c₁ k) - lerayProj k (convGal S c₂ k)‖ ^ 2 ≤
        C * M ^ 2 * (∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2) := by
  classical
  obtain ⟨FB, hFB0, hFBb⟩ : ∃ FB : ℝ, 0 ≤ FB ∧ ∀ x ∈ S, ∀ y ∈ S, ‖freq (x - y)‖ ≤ FB :=
    ⟨2 * ∑ j ∈ S, ‖freq j‖,
      by
        have := Finset.sum_nonneg (fun j (_ : j ∈ S) => norm_nonneg (freq j))
        linarith,
      tfFreqBound S⟩
  refine ⟨16 * FB ^ 2 * S.card, by positivity, ?_⟩
  intro c₁ c₂ hc₁ hc₂ M hM0 hM1 hM2 k
  by_cases hkS : k ∈ S
  · -- main case: k ∈ S
    have hd0 : ∀ j, j ∉ S → c₁ j - c₂ j = 0 := by
      intro j hj
      rw [hc₁ j hj, hc₂ j hj, sub_zero]
    -- expand the two convections
    have hA : convGal S c₁ k
        = -∑ l ∈ S, (Complex.I * dotR (c₁ l) (freq (k - l))) • c₁ (k - l) := by
      simp [convGal, hkS]
    have hB : convGal S c₂ k
        = -∑ l ∈ S, (Complex.I * dotR (c₂ l) (freq (k - l))) • c₂ (k - l) := by
      simp [convGal, hkS]
    -- the telescope
    have hdiff : convGal S c₁ k - convGal S c₂ k
        = -∑ l ∈ S, ((Complex.I * dotR (c₁ l - c₂ l) (freq (k - l))) • c₁ (k - l)
            + (Complex.I * dotR (c₂ l) (freq (k - l))) • (c₁ (k - l) - c₂ (k - l))) := by
      rw [hA, hB, neg_sub_neg, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [tfDotR_sub_left]
      simp only [mul_sub, sub_smul, smul_sub, neg_add, neg_sub]
      abel
    -- termwise bound
    have hterm : ∀ l ∈ S,
        ‖(Complex.I * dotR (c₁ l - c₂ l) (freq (k - l))) • c₁ (k - l)
          + (Complex.I * dotR (c₂ l) (freq (k - l))) • (c₁ (k - l) - c₂ (k - l))‖
        ≤ FB * M * (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) := by
      intro l hl
      have hfb : ‖freq (k - l)‖ ≤ FB := hFBb k hkS l hl
      have h1 : ‖(Complex.I * dotR (c₁ l - c₂ l) (freq (k - l))) • c₁ (k - l)‖
          ≤ FB * M * ‖c₁ l - c₂ l‖ := by
        rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
        calc ‖dotR (c₁ l - c₂ l) (freq (k - l))‖ * ‖c₁ (k - l)‖
            ≤ (‖freq (k - l)‖ * ‖c₁ l - c₂ l‖) * M := by
              refine mul_le_mul (norm_dotR_le _ _) (hM1 _) (norm_nonneg _) ?_
              positivity
          _ ≤ (FB * ‖c₁ l - c₂ l‖) * M := by
              have hmm := mul_le_mul_of_nonneg_right hfb (norm_nonneg (c₁ l - c₂ l))
              exact mul_le_mul_of_nonneg_right hmm hM0
          _ = FB * M * ‖c₁ l - c₂ l‖ := by ring
      have h2 : ‖(Complex.I * dotR (c₂ l) (freq (k - l)))
            • (c₁ (k - l) - c₂ (k - l))‖
          ≤ FB * M * ‖c₁ (k - l) - c₂ (k - l)‖ := by
        rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
        calc ‖dotR (c₂ l) (freq (k - l))‖ * ‖c₁ (k - l) - c₂ (k - l)‖
            ≤ (‖freq (k - l)‖ * ‖c₂ l‖) * ‖c₁ (k - l) - c₂ (k - l)‖ :=
              mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
          _ ≤ (FB * M) * ‖c₁ (k - l) - c₂ (k - l)‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul hfb (hM2 l) (norm_nonneg _) hFB0
          _ = FB * M * ‖c₁ (k - l) - c₂ (k - l)‖ := by ring
      calc ‖(Complex.I * dotR (c₁ l - c₂ l) (freq (k - l))) • c₁ (k - l)
            + (Complex.I * dotR (c₂ l) (freq (k - l))) • (c₁ (k - l) - c₂ (k - l))‖
          ≤ ‖(Complex.I * dotR (c₁ l - c₂ l) (freq (k - l))) • c₁ (k - l)‖
            + ‖(Complex.I * dotR (c₂ l) (freq (k - l)))
                • (c₁ (k - l) - c₂ (k - l))‖ := norm_add_le _ _
        _ ≤ FB * M * ‖c₁ l - c₂ l‖ + FB * M * ‖c₁ (k - l) - c₂ (k - l)‖ :=
            add_le_add h1 h2
        _ = FB * M * (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) := by ring
    -- sum bound
    have hsum : ‖convGal S c₁ k - convGal S c₂ k‖
        ≤ FB * M * ∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) := by
      rw [hdiff, norm_neg]
      calc ‖∑ l ∈ S, ((Complex.I * dotR (c₁ l - c₂ l) (freq (k - l))) • c₁ (k - l)
              + (Complex.I * dotR (c₂ l) (freq (k - l))) • (c₁ (k - l) - c₂ (k - l)))‖
          ≤ ∑ l ∈ S, ‖(Complex.I * dotR (c₁ l - c₂ l) (freq (k - l))) • c₁ (k - l)
              + (Complex.I * dotR (c₂ l) (freq (k - l)))
                • (c₁ (k - l) - c₂ (k - l))‖ := norm_sum_le _ _
        _ ≤ ∑ l ∈ S, FB * M * (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) :=
            Finset.sum_le_sum hterm
        _ = FB * M * ∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) :=
            (Finset.mul_sum _ _ _).symm
    -- the shifted-index sum bound
    have hshift : ∑ l ∈ S, ‖c₁ (k - l) - c₂ (k - l)‖ ^ 2
        ≤ ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2 := by
      have hinj : Set.InjOn (fun l => k - l) ↑S := by
        intro a _ b _ hab
        have hab' : k - a = k - b := hab
        exact sub_right_inj.mp hab'
      have himg : ∑ l ∈ S, ‖c₁ (k - l) - c₂ (k - l)‖ ^ 2
          = ∑ j ∈ Finset.image (fun l => k - l) S, ‖c₁ j - c₂ j‖ ^ 2 :=
        (Finset.sum_image (f := fun j => ‖c₁ j - c₂ j‖ ^ 2) hinj).symm
      have hfil : ∑ j ∈ (Finset.image (fun l => k - l) S).filter (fun j => j ∈ S),
            ‖c₁ j - c₂ j‖ ^ 2
          = ∑ j ∈ Finset.image (fun l => k - l) S, ‖c₁ j - c₂ j‖ ^ 2 := by
        apply Finset.sum_filter_of_ne
        intro x _ hne
        by_contra hxS
        exact hne (by rw [hd0 x hxS, norm_zero]; norm_num)
      have hsub : (Finset.image (fun l => k - l) S).filter (fun j => j ∈ S) ⊆ S := by
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      calc ∑ l ∈ S, ‖c₁ (k - l) - c₂ (k - l)‖ ^ 2
          = ∑ j ∈ Finset.image (fun l => k - l) S, ‖c₁ j - c₂ j‖ ^ 2 := himg
        _ = ∑ j ∈ (Finset.image (fun l => k - l) S).filter (fun j => j ∈ S),
              ‖c₁ j - c₂ j‖ ^ 2 := hfil.symm
        _ ≤ ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
    -- split of the squared sum
    have hsplit : ∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) ^ 2
        ≤ 4 * ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2 := by
      have h1 : ∀ l ∈ S,
          (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) ^ 2
          ≤ 2 * ‖c₁ l - c₂ l‖ ^ 2 + 2 * ‖c₁ (k - l) - c₂ (k - l)‖ ^ 2 := fun l _ => by
        nlinarith [sq_nonneg (‖c₁ l - c₂ l‖ - ‖c₁ (k - l) - c₂ (k - l)‖)]
      calc ∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) ^ 2
          ≤ ∑ l ∈ S, (2 * ‖c₁ l - c₂ l‖ ^ 2
              + 2 * ‖c₁ (k - l) - c₂ (k - l)‖ ^ 2) := Finset.sum_le_sum h1
        _ = 2 * (∑ l ∈ S, ‖c₁ l - c₂ l‖ ^ 2)
            + 2 * (∑ l ∈ S, ‖c₁ (k - l) - c₂ (k - l)‖ ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ 2 * (∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2)
            + 2 * (∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2) := by
            linarith [hshift]
        _ = 4 * ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2 := by ring
    -- Cauchy–Schwarz
    have hT2 : (∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖)) ^ 2
        ≤ (S.card : ℝ) * (4 * ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2) := by
      calc (∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖)) ^ 2
          ≤ (S.card : ℝ) * ∑ l ∈ S,
              (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖) ^ 2 :=
            tfSq_sum_le S _
        _ ≤ (S.card : ℝ) * (4 * ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg _)
    -- assemble
    rw [← tfLerayProj_sub]
    have hX : ‖lerayProj k (convGal S c₁ k - convGal S c₂ k)‖
        ≤ 2 * (FB * M * ∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖)) := by
      calc ‖lerayProj k (convGal S c₁ k - convGal S c₂ k)‖
          ≤ 2 * ‖convGal S c₁ k - convGal S c₂ k‖ := tfNorm_lerayProj_le k _
        _ ≤ 2 * (FB * M * ∑ l ∈ S, (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖)) := by
            linarith [hsum]
    have hXsq : ‖lerayProj k (convGal S c₁ k - convGal S c₂ k)‖ ^ 2
        ≤ (2 * (FB * M * ∑ l ∈ S,
            (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖))) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) hX
    calc ‖lerayProj k (convGal S c₁ k - convGal S c₂ k)‖ ^ 2
        ≤ (2 * (FB * M * ∑ l ∈ S,
            (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖))) ^ 2 := hXsq
      _ = 4 * FB ^ 2 * M ^ 2 * (∑ l ∈ S,
            (‖c₁ l - c₂ l‖ + ‖c₁ (k - l) - c₂ (k - l)‖)) ^ 2 := by ring
      _ ≤ 4 * FB ^ 2 * M ^ 2
            * ((S.card : ℝ) * (4 * ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left hT2 ?_
          positivity
      _ = 16 * FB ^ 2 * (S.card : ℝ) * M ^ 2 * ∑ j ∈ S, ‖c₁ j - c₂ j‖ ^ 2 := by ring
  · -- k ∉ S : both convGal terms vanish
    have h1 : convGal S c₁ k = 0 := by simp [convGal, hkS]
    have h2 : convGal S c₂ k = 0 := by simp [convGal, hkS]
    rw [h1, h2, tfLerayProj_zero, sub_zero, norm_zero]
    have h0 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    rw [h0]
    positivity

/-! ## The localized abstract trap -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private lemma l_weighted_tsum_eq_sum (w : (Fin 3 → ℤ) → ℝ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → V} (hsupp : ∀ k, k ∉ S → c k = 0) :
    ∑' k, w k * ‖c k‖ ^ 2 = ∑ k ∈ S, w k * ‖c k‖ ^ 2 :=
  tsum_eq_sum fun k hk => by rw [hsupp k hk]; simp

private lemma l_summable_weighted (w : (Fin 3 → ℤ) → ℝ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → V} (hsupp : ∀ k, k ∉ S → c k = 0) :
    Summable fun k => w k * ‖c k‖ ^ 2 :=
  summable_of_ne_finset_zero (s := S) fun k hk => by rw [hsupp k hk]; simp

private lemma l_hasDerivAt_weighted_sum (w : (Fin 3 → ℤ) → ℝ) (S : Finset (Fin 3 → ℤ))
    {c c' : ℝ → (Fin 3 → ℤ) → V} {t : ℝ}
    (hderiv : ∀ k, HasDerivAt (fun s => c s k) (c' t k) t) :
    HasDerivAt (fun s => ∑ k ∈ S, w k * ‖c s k‖ ^ 2)
      (∑ k ∈ S, w k * (2 * inner ℝ (c' t k) (c t k))) t := by
  have hterm : ∀ k ∈ S, HasDerivAt (fun s => w k * ‖c s k‖ ^ 2)
      (w k * (2 * inner ℝ (c' t k) (c t k))) t := by
    intro k _
    have h1 : HasDerivAt (fun s => inner ℝ (c s k) (c s k))
        (inner ℝ (c t k) (c' t k) + inner ℝ (c' t k) (c t k)) t :=
      (hderiv k).inner ℝ (hderiv k)
    have h2 : (fun s => ‖c s k‖ ^ 2) = fun s => inner ℝ (c s k) (c s k) := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    have h4 : inner ℝ (c t k) (c' t k) + inner ℝ (c' t k) (c t k) =
        2 * inner ℝ (c' t k) (c t k) := by
      rw [real_inner_comm (c t k) (c' t k)]; ring
    have h3 : HasDerivAt (fun s => ‖c s k‖ ^ 2)
        (2 * inner ℝ (c' t k) (c t k)) t := by
      rw [h2, ← h4]; exact h1
    exact h3.const_mul (w k)
  have h := HasDerivAt.sum hterm
  have heq : (∑ i ∈ S, fun s => w i * ‖c s i‖ ^ 2) =
      fun s => ∑ k ∈ S, w k * ‖c s k‖ ^ 2 := by
    funext s
    simp [Finset.sum_apply]
  rwa [heq] at h

/-- **Interval-localized abstract Galerkin trap**: the wave-2 theorem with the
coefficient ODE and support hypothesized on `Icc 0 T` only — the honest form
for CONSTRUCTED (rather than globally hypothesized) flows. -/
theorem galerkin_conditional_trap_on :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c F : ℝ → (Fin 3 → ℤ) → V},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + F t k) t) →
      (∀ t ∈ Ioo (0:ℝ) T, (∑ k ∈ S, 2 * inner ℝ (F t k) (c t k)) ≤ 0) →
      (∀ t ∈ Ioo (0:ℝ) T,
        (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k))) ≤
        2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖)) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Ico (0:ℝ) T,
        κ * en (c t) * ens (c t) < ν ^ 4 ∧
          ens (c t) ≤ ens (c 0) ∧ en (c t) ≤ en (c 0) := by
  obtain ⟨κ, hκ, htrap⟩ := conditional_trap (V := V)
  refine ⟨κ, hκ, ?_⟩
  intro T ν hν S hS0 c F hsupp hODE hEpair hZpair h0
  set cd : ℝ → (Fin 3 → ℤ) → V :=
    fun t k => (-(ν * ‖freq k‖ ^ 2)) • c t k + F t k with hcd
  have hIcoIcc : Ico (0:ℝ) T ⊆ Icc 0 T := Ico_subset_Icc_self
  have hIooIcc : Ioo (0:ℝ) T ⊆ Icc 0 T := Ioo_subset_Icc_self
  have hmean : ∀ t ∈ Ico (0:ℝ) T, c t 0 = 0 := fun t ht =>
    hsupp t (hIcoIcc ht) 0 hS0
  have hDsum : ∀ t ∈ Ico (0:ℝ) T,
      Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t ht =>
    l_summable_weighted _ (hsupp t (hIcoIcc ht))
  have hens_eq : ∀ t ∈ Icc (0:ℝ) T,
      ens (c t) = ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c t k‖ ^ 2 := fun t ht =>
    l_weighted_tsum_eq_sum _ (hsupp t ht)
  have hdis_eq : ∀ t ∈ Icc (0:ℝ) T,
      dis (c t) = ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t ht =>
    l_weighted_tsum_eq_sum _ (hsupp t ht)
  have hen_eq : ∀ t ∈ Icc (0:ℝ) T, en (c t) = ∑ k ∈ S, ‖c t k‖ ^ 2 := by
    intro t ht
    have h := l_weighted_tsum_eq_sum (V := V) (fun _ => (1:ℝ)) (hsupp t ht)
    simpa [en] using h
  -- finite-sum surrogates with genuine derivatives on the interval
  set Ef : ℝ → ℝ := fun s => ∑ k ∈ S, ‖c s k‖ ^ 2 with hEf
  set Zf : ℝ → ℝ := fun s => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 with hZf
  have hEfd : ∀ t ∈ Icc (0:ℝ) T,
      HasDerivAt Ef (∑ k ∈ S, 2 * inner ℝ (cd t k) (c t k)) t := by
    intro t ht
    have h := l_hasDerivAt_weighted_sum (fun _ => (1:ℝ)) S (c' := cd)
      (fun k => hODE t ht k)
    have he : (fun s => ∑ k ∈ S, (1:ℝ) * ‖c s k‖ ^ 2) = Ef := by
      funext s
      simp [hEf]
    have hv : (∑ k ∈ S, (1:ℝ) * (2 * inner ℝ (cd t k) (c t k))) =
        ∑ k ∈ S, 2 * inner ℝ (cd t k) (c t k) := by
      simp
    rw [he, hv] at h
    exact h
  have hZfd : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt Zf
      (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) t := fun t ht =>
    l_hasDerivAt_weighted_sum (fun k => ‖freq k‖ ^ 2) S (c' := cd)
      (fun k => hODE t ht k)
  -- agreement with the tsum quantities on the interval
  have hEagree : EqOn (fun s => en (c s)) Ef (Icc 0 T) := fun t ht => hen_eq t ht
  have hZagree : EqOn (fun s => ens (c s)) Zf (Icc 0 T) := fun t ht => hens_eq t ht
  have hEev : ∀ t ∈ Ioo (0:ℝ) T, (fun s => en (c s)) =ᶠ[nhds t] Ef := fun t ht =>
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
      (fun s hs => hEagree (hIooIcc hs))
  have hZev : ∀ t ∈ Ioo (0:ℝ) T, (fun s => ens (c s)) =ᶠ[nhds t] Zf := fun t ht =>
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
      (fun s hs => hZagree (hIooIcc hs))
  -- per-mode pairing split
  have hterm : ∀ t k, 2 * inner ℝ (cd t k) (c t k) =
      -(2 * (ν * ‖freq k‖ ^ 2) * ‖c t k‖ ^ 2) + 2 * inner ℝ (F t k) (c t k) := by
    intro t k
    rw [hcd]
    simp only [inner_add_left, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    ring
  -- the conditional_trap interface
  have hEcf : ContinuousOn Ef (Ico 0 T) := fun t ht =>
    (hEfd t (hIcoIcc ht)).continuousAt.continuousWithinAt
  have hZcf : ContinuousOn Zf (Ico 0 T) := fun t ht =>
    (hZfd t (hIcoIcc ht)).continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun s => en (c s)) (Ico 0 T) :=
    hEcf.congr (fun t ht => hEagree (hIcoIcc ht))
  have hZc : ContinuousOn (fun s => ens (c s)) (Ico 0 T) :=
    hZcf.congr (fun t ht => hZagree (hIcoIcc ht))
  have hEd : DifferentiableOn ℝ (fun s => en (c s)) (Ioo 0 T) := by
    intro t ht
    exact (((hEev t ht).differentiableAt_iff).mpr
      (hEfd t (hIooIcc ht)).differentiableAt).differentiableWithinAt
  have hZd : DifferentiableOn ℝ (fun s => ens (c s)) (Ioo 0 T) := by
    intro t ht
    exact (((hZev t ht).differentiableAt_iff).mpr
      (hZfd t (hIooIcc ht)).differentiableAt).differentiableWithinAt
  have hE' : ∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => en (c s)) t ≤ 0 := by
    intro t ht
    rw [(hEev t ht).deriv_eq, (hEfd t (hIooIcc ht)).deriv]
    have hsplit : (∑ k ∈ S, 2 * inner ℝ (cd t k) (c t k)) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c t k‖ ^ 2) +
          ∑ k ∈ S, 2 * inner ℝ (F t k) (c t k) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm t k]
      ring
    rw [hsplit]
    have h1 : 0 ≤ ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c t k‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (sq_nonneg _)
    have h2 := hEpair t ht
    nlinarith
  have hbal : ∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => ens (c s)) t ≤
      -(2 * ν) * dis (c t) +
        2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) := by
    intro t ht
    rw [(hZev t ht).deriv_eq, (hZfd t (hIooIcc ht)).deriv]
    have hsplit : (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) +
          ∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm t k]
      ring
    rw [hsplit, hdis_eq t (hIooIcc ht)]
    have h2 := hZpair t ht
    linarith
  exact htrap hν hmean hDsum hEc hZc hEd hZd hE' hbal h0

/-! ## Uniqueness -/

/-- **Uniqueness of Galerkin Navier-Stokes flows on an interval**: two
supported flows of the Leray-projected system with the same initial value
coincide on the window — the difference runs through the same defect
machinery, no conjugation needed. -/
theorem ns_galerkin_unique_on {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel}
    (hs₁ : ∀ (t : ℝ) k, k ∉ S → c₁ t k = 0)
    (hs₂ : ∀ (t : ℝ) k, k ∉ S → c₂ t k = 0)
    (hODE₁ : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₁ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ t k + lerayProj k (convGal S (c₁ t) k)) t)
    (hODE₂ : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ t k + lerayProj k (convGal S (c₂ t) k)) t)
    (h0 : ∀ k, c₁ 0 k = c₂ 0 k) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₂ t k := by
  by_cases hT : (0:ℝ) ≤ T
  · -- the defect
    set d : ℝ → (Fin 3 → ℤ) → Vel := fun t k => c₁ t k - c₂ t k with hd
    set R : ℝ → (Fin 3 → ℤ) → Vel := fun t k =>
      lerayProj k (convGal S (c₁ t) k) - lerayProj k (convGal S (c₂ t) k) with hR
    set lam : (Fin 3 → ℤ) → ℝ := fun k => ν * ‖freq k‖ ^ 2 with hlam
    have hlamnn : ∀ k, 0 ≤ lam k := fun k => by positivity
    have hdderiv : ∀ s ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun u => d u k)
        ((-(lam k)) • d s k + R s k) s := by
      intro s hs k
      have h3 := (hODE₁ s hs k).sub (hODE₂ s hs k)
      have hval : ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convGal S (c₁ s) k)) -
          ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convGal S (c₂ s) k)) =
          (-(lam k)) • d s k + R s k := by
        rw [hlam, hd, hR]
        simp only [smul_sub]
        abel
      rw [hval] at h3
      exact h3
    have hdsupp : ∀ (s : ℝ) k, k ∉ S → d s k = 0 := by
      intro s k hk
      rw [hd]
      simp only
      rw [hs₁ s k hk, hs₂ s k hk, sub_self]
    have hd0 : ∀ k, d 0 k = 0 := by
      intro k
      rw [hd]
      simp only
      rw [h0 k, sub_self]
    -- bound both fields on the window
    obtain ⟨M, hM0, hMb⟩ : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (0:ℝ) T,
        (∀ j, ‖c₁ s j‖ ≤ M) ∧ (∀ j, ‖c₂ s j‖ ≤ M) := by
      have hmode : ∀ j, ContinuousOn (fun s : ℝ => c₁ s j) (Icc 0 T) := fun j t ht =>
        (hODE₁ t ht j).continuousAt.continuousWithinAt
      have hmode₂ : ∀ j, ContinuousOn (fun s : ℝ => c₂ s j) (Icc 0 T) := fun j t ht =>
        (hODE₂ t ht j).continuousAt.continuousWithinAt
      have hcont : ContinuousOn
          (fun s : ℝ => (∑ j ∈ S, ‖c₁ s j‖) + ∑ j ∈ S, ‖c₂ s j‖) (Icc 0 T) := by
        apply ContinuousOn.add
        · exact continuousOn_finsetSum S fun j _ => (hmode j).norm
        · exact continuousOn_finsetSum S fun j _ => (hmode₂ j).norm
      have hne : (Icc (0:ℝ) T).Nonempty := ⟨0, le_refl 0, hT⟩
      obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
      refine ⟨(∑ j ∈ S, ‖c₁ s₀ j‖) + ∑ j ∈ S, ‖c₂ s₀ j‖, by positivity, ?_⟩
      intro s hs
      have hsum1 : 0 ≤ ∑ j ∈ S, ‖c₁ s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
      have hsum2 : 0 ≤ ∑ j ∈ S, ‖c₂ s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
      constructor
      · intro j
        by_cases hj : j ∈ S
        · calc ‖c₁ s j‖ ≤ ∑ i ∈ S, ‖c₁ s i‖ :=
                Finset.single_le_sum (f := fun i => ‖c₁ s i‖)
                  (fun i _ => norm_nonneg _) hj
            _ ≤ (∑ i ∈ S, ‖c₁ s i‖) + ∑ i ∈ S, ‖c₂ s i‖ := by linarith
            _ ≤ _ := hmax hs
        · rw [hs₁ s j hj]
          simp only [norm_zero]
          have := hmax hs
          positivity
      · intro j
        by_cases hj : j ∈ S
        · calc ‖c₂ s j‖ ≤ ∑ i ∈ S, ‖c₂ s i‖ :=
                Finset.single_le_sum (f := fun i => ‖c₂ s i‖)
                  (fun i _ => norm_nonneg _) hj
            _ ≤ (∑ i ∈ S, ‖c₁ s i‖) + ∑ i ∈ S, ‖c₂ s i‖ := by linarith
            _ ≤ _ := hmax hs
        · rw [hs₂ s j hj]
          simp only [norm_zero]
          have := hmax hs
          positivity
    obtain ⟨C, hC0, hCb⟩ := two_flow_forcing_bound (S := S)
    have hRb : ∀ s ∈ Icc (0:ℝ) T, ∀ j ∈ S,
        ‖R s j‖ ^ 2 ≤ (C * M ^ 2) * (∑ i ∈ S, ‖d s i‖ ^ 2) := by
      intro s hs j _
      have := hCb (hs₁ s) (hs₂ s) hM0 (hMb s hs).1 (hMb s hs).2 j
      simpa [hR, hd] using this
    intro t ht k
    have hz := defect_vanishes_on' (mul_nonneg hC0 (by positivity)) (le_refl 0) hT
      hlamnn hdderiv hdsupp hRb hd0 t ht k
    have : c₁ t k - c₂ t k = 0 := hz
    exact sub_eq_zero.mp this
  · intro t ht
    exact absurd (ht.1.trans ht.2) hT

/-! ## The localized zero-data capstone -/

/-- **M5 wave-1 capstone: the interval-localized zero-data trap** — the
honest form for CONSTRUCTED flows: ODE and support on `Icc 0 T` only,
reality and divergence-freeness at `t = 0` only, trap on `Ico 0 T`. -/
theorem ns_galerkin_trap_zero_data_on :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      RealField (c 0) → DivFree (c 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Ico (0:ℝ) T,
        κ * en (c t) * ens (c t) < ν ^ 4 ∧
          ens (c t) ≤ ens (c 0) ∧ en (c t) ≤ en (c 0) := by
  obtain ⟨κ, hκ, htrap⟩ := galerkin_conditional_trap_on (V := Vel)
  refine ⟨κ, hκ, ?_⟩
  intro T ν hν S hS0 hSsym c hsupp h0real h0div hODE h0
  have hIooIcc : Ioo (0:ℝ) T ⊆ Icc 0 T := Ioo_subset_Icc_self
  have hreal : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) :=
    realField_propagates_on hν.le hSsym hsupp hODE h0real
  have hdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) :=
    divFree_propagates_on hν.le hODE h0div
  have hpair : ∀ t ∈ Icc (0:ℝ) T, ∀ k,
      inner ℝ (lerayProj k (convGal S (c t) k)) (c t k) =
        inner ℝ (convGal S (c t) k) (c t k) := fun t ht k =>
    inner_lerayProj_of_divFree (hdiv t ht) k _
  refine htrap hν hS0 hsupp hODE ?_ ?_ h0
  · intro t ht
    have hE := convGal_energy_pairing (hsupp t (hIooIcc ht)) (hreal t (hIooIcc ht))
      (hdiv t (hIooIcc ht))
    calc (∑ k ∈ S, 2 * inner ℝ (lerayProj k (convGal S (c t) k)) (c t k))
        = ∑ k ∈ S, 2 * inner ℝ (convGal S (c t) k) (c t k) :=
          Finset.sum_congr rfl fun k _ => by rw [hpair t (hIooIcc ht) k]
      _ ≤ 0 := le_of_eq hE
  · intro t ht
    have hZ := convGal_enstrophy_pairing (hsupp t (hIooIcc ht)) (hreal t (hIooIcc ht))
    calc (∑ k ∈ S, ‖freq k‖ ^ 2 *
          (2 * inner ℝ (lerayProj k (convGal S (c t) k)) (c t k)))
        = ∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (convGal S (c t) k) (c t k)) :=
          Finset.sum_congr rfl fun k _ => by rw [hpair t (hIooIcc ht) k]
      _ ≤ 2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
            (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) := hZ

end TheoremB
