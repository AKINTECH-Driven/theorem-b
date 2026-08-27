/-
  TheoremB/GalerkinTrap.lean
  M4 wave 2 of the Theorem B campaign (27 Aug 2026).

  The conditional trap DISCHARGED for abstract Galerkin flows: for finitely
  supported spectral trajectories obeying the NS-shaped coefficient ODE
  c' = -nu*|k|^2 * c + F, the enstrophy-balance hypothesis of
  conditional_trap is PROVED (coefficient-wise product rule over the finite
  box; no differentiation under an infinite sum, following the leray-hopf
  pattern), assuming only the two forcing-pairing bounds:
    (energy)     sum_k 2<F k, c k>  <= 0
    (enstrophy)  sum_k |k|^2 * 2<F k, c k>  <= 2 * triMaj(...)
  Wave 3's sole obligation is that the concrete spectral convection term
  satisfies these two bounds (antisymmetry gives the first with equality;
  the vortex-stretching estimate gives the second).  Note the ODE hypothesis
  ranges over ALL k, which together with the support hypothesis forces
  F t k = 0 off S — exactly the Galerkin reality, where F is the projection
  of the convection back onto the box.  At finite level every
  sum is a Finset.sum, so the triMaj nested-tsum summability trap is moot
  on the c-side.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.ConditionalTheoremB

namespace TheoremB

open Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Weighted spectral sums collapse to finite sums on finitely supported fields. -/
private lemma weighted_tsum_eq_sum (w : (Fin 3 → ℤ) → ℝ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → V} (hsupp : ∀ k, k ∉ S → c k = 0) :
    ∑' k, w k * ‖c k‖ ^ 2 = ∑ k ∈ S, w k * ‖c k‖ ^ 2 :=
  tsum_eq_sum fun k hk => by rw [hsupp k hk]; simp

private lemma summable_weighted_of_support (w : (Fin 3 → ℤ) → ℝ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → V} (hsupp : ∀ k, k ∉ S → c k = 0) :
    Summable fun k => w k * ‖c k‖ ^ 2 :=
  summable_of_ne_finset_zero (s := S) fun k hk => by rw [hsupp k hk]; simp

/-- Coefficient-wise product rule for a weighted enstrophy-type sum along a flow. -/
private lemma hasDerivAt_weighted_sum (w : (Fin 3 → ℤ) → ℝ) (S : Finset (Fin 3 → ℤ))
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

/-- **Wave-2 capstone: the conditional trap for abstract Galerkin flows.**
For a finitely supported spectral flow obeying the NS-shaped coefficient ODE
`c' = -ν‖k‖²·c + F`, with the energy forcing pairing nonpositive and the
enstrophy forcing pairing dominated by the trilinear majorant, the balance
hypothesis of `conditional_trap` HOLDS, and small data traps the orbit.
Wave 3's sole obligation: the concrete convection term satisfies the two
pairing hypotheses. -/
theorem galerkin_conditional_trap :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c F : ℝ → (Fin 3 → ℤ) → V},
      (∀ t k, k ∉ S → c t k = 0) →
      (∀ t k, HasDerivAt (fun s => c s k)
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
  have hmean : ∀ t ∈ Ico (0:ℝ) T, c t 0 = 0 := fun t _ => hsupp t 0 hS0
  have hDsum : ∀ t ∈ Ico (0:ℝ) T,
      Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t _ =>
    summable_weighted_of_support _ (hsupp t)
  -- collapse identities
  have hen_eq : ∀ t, en (c t) = ∑ k ∈ S, ‖c t k‖ ^ 2 := by
    intro t
    have h := weighted_tsum_eq_sum (V := V) (fun _ => (1:ℝ)) (hsupp t)
    simpa [en] using h
  have hens_eq : ∀ t, ens (c t) = ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c t k‖ ^ 2 := fun t =>
    weighted_tsum_eq_sum _ (hsupp t)
  have hdis_eq : ∀ t, dis (c t) = ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t =>
    weighted_tsum_eq_sum _ (hsupp t)
  -- derivatives of the scalar histories
  have hen_deriv : ∀ t, HasDerivAt (fun s => en (c s))
      (∑ k ∈ S, 2 * inner ℝ (cd t k) (c t k)) t := by
    intro t
    have h := hasDerivAt_weighted_sum (fun _ => (1:ℝ)) S (c' := cd)
      (fun k => hODE t k)
    have heq : (fun s => ∑ k ∈ S, (1:ℝ) * ‖c s k‖ ^ 2) = fun s => en (c s) := by
      funext s
      rw [hen_eq s]
      simp
    rw [heq] at h
    simpa using h
  have hens_deriv : ∀ t, HasDerivAt (fun s => ens (c s))
      (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) t := by
    intro t
    have h := hasDerivAt_weighted_sum (fun k => ‖freq k‖ ^ 2) S (c' := cd)
      (fun k => hODE t k)
    have heq : (fun s => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2) =
        fun s => ens (c s) := by
      funext s
      rw [hens_eq s]
    rw [heq] at h
    exact h
  -- per-mode pairing split: dissipation + forcing
  have hterm : ∀ t k, 2 * inner ℝ (cd t k) (c t k) =
      -(2 * (ν * ‖freq k‖ ^ 2) * ‖c t k‖ ^ 2) + 2 * inner ℝ (F t k) (c t k) := by
    intro t k
    rw [hcd]
    simp only [inner_add_left, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    ring
  -- interface of conditional_trap
  have hEc : ContinuousOn (fun t => en (c t)) (Ico 0 T) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hen_deriv t).continuousAt).continuousOn
  have hZc : ContinuousOn (fun t => ens (c t)) (Ico 0 T) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hens_deriv t).continuousAt).continuousOn
  have hEd : DifferentiableOn ℝ (fun t => en (c t)) (Ioo 0 T) := fun t _ =>
    (hen_deriv t).differentiableAt.differentiableWithinAt
  have hZd : DifferentiableOn ℝ (fun t => ens (c t)) (Ioo 0 T) := fun t _ =>
    (hens_deriv t).differentiableAt.differentiableWithinAt
  have hE' : ∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => en (c s)) t ≤ 0 := by
    intro t ht
    rw [(hen_deriv t).deriv]
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
    rw [(hens_deriv t).deriv]
    have hsplit : (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) +
          ∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm t k]
      ring
    rw [hsplit, hdis_eq t]
    have h2 := hZpair t ht
    linarith
  exact htrap hν hmean hDsum hEc hZc hEd hZd hE' hbal h0

/-- **Wave-2 twin: the quantitative safety window for abstract Galerkin
flows**, under positive enstrophy: the exact Riccati-orbit bound inside the
window, with the same uniform constant. -/
theorem galerkin_safety_window :
    ∃ K, 0 < K ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c F : ℝ → (Fin 3 → ℤ) → V},
      (∀ t k, k ∉ S → c t k = 0) →
      (∀ t k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + F t k) t) →
      (∀ t ∈ Ico (0:ℝ) T, 0 < ens (c t)) →
      (∀ t ∈ Ioo (0:ℝ) T,
        (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k))) ≤
        2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖)) →
      ∀ t ∈ Ico (0:ℝ) T, 2 * (K / ν ^ 3) * ens (c 0) ^ 2 * t < 1 →
        ens (c t) ^ 2 ≤ ens (c 0) ^ 2 / (1 - 2 * (K / ν ^ 3) * ens (c 0) ^ 2 * t) := by
  obtain ⟨K, hK, hwin⟩ := conditional_safety_window (V := V)
  refine ⟨K, hK, ?_⟩
  intro T ν hν S hS0 c F hsupp hODE hpos hZpair t ht hw
  set cd : ℝ → (Fin 3 → ℤ) → V :=
    fun t k => (-(ν * ‖freq k‖ ^ 2)) • c t k + F t k with hcd
  have hmean : ∀ t ∈ Ico (0:ℝ) T, c t 0 = 0 := fun t _ => hsupp t 0 hS0
  have hDsum : ∀ t ∈ Ico (0:ℝ) T,
      Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t _ =>
    summable_weighted_of_support _ (hsupp t)
  have hens_eq : ∀ t, ens (c t) = ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c t k‖ ^ 2 := fun t =>
    weighted_tsum_eq_sum _ (hsupp t)
  have hdis_eq : ∀ t, dis (c t) = ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t =>
    weighted_tsum_eq_sum _ (hsupp t)
  have hens_deriv : ∀ t, HasDerivAt (fun s => ens (c s))
      (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) t := by
    intro t
    have h := hasDerivAt_weighted_sum (fun k => ‖freq k‖ ^ 2) S (c' := cd)
      (fun k => hODE t k)
    have heq : (fun s => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2) =
        fun s => ens (c s) := by
      funext s
      rw [hens_eq s]
    rw [heq] at h
    exact h
  have hterm : ∀ t k, 2 * inner ℝ (cd t k) (c t k) =
      -(2 * (ν * ‖freq k‖ ^ 2) * ‖c t k‖ ^ 2) + 2 * inner ℝ (F t k) (c t k) := by
    intro t k
    rw [hcd]
    simp only [inner_add_left, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    ring
  have hZc : ContinuousOn (fun t => ens (c t)) (Ico 0 T) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hens_deriv t).continuousAt).continuousOn
  have hZd : DifferentiableOn ℝ (fun t => ens (c t)) (Ioo 0 T) := fun t _ =>
    (hens_deriv t).differentiableAt.differentiableWithinAt
  have hbal : ∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => ens (c s)) t ≤
      -(2 * ν) * dis (c t) +
        2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) := by
    intro t ht'
    rw [(hens_deriv t).deriv]
    have hsplit : (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) +
          ∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm t k]
      ring
    rw [hsplit, hdis_eq t]
    have h2 := hZpair t ht'
    linarith
  exact hwin hν hmean hDsum hZc hZd hpos hbal t ht hw

end TheoremB

