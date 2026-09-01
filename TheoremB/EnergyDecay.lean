/-
# Ambient energy decay (Tier 7, wave W-R0)

The trap's energy clause (`en (c t) ≤ en (c 0)`) is not sharp. On a
mean-zero field the spectral Poincare inequality `en ≤ ens` holds for
free - every nonzero lattice frequency has `1 ≤ ‖freq k‖` - and the
exact energy identity `en' = -2ν·ens + (energy pairing)` therefore
upgrades to `en' ≤ -2ν·en` whenever the pairing is nonpositive. Every
trapped Galerkin flow decays exponentially at least at rate `2ν`, with no
smallness used beyond what the trap already supplies.

This is the fact that makes the ASYMPTOTIC form of a determining-modes
statement vacuous in this campaign's regime (rung9 blueprint,
Correction 1): every solution reaches zero unaided, so "agreement on N
modes forces agreement of the whole flow" is true and empty. Tier 7's
capstones are consequently stated as RATES with an explicit threshold,
never as limits.

Scope, and not to be overstated: this file proves the decay for the
GALERKIN flows. Transferring it to the eternal flow of
`ns_full_global_flow` is wave W-R0b and is NOT claimed here; the two
candidate routes are recorded in the rung9 blueprint.
-/
import TheoremB.GalerkinTrap
import TheoremB.SobolevNorms

namespace TheoremB

open Set

/-- **Spectral Poincare.** On a mean-zero field, energy never exceeds
enstrophy. Immediate from the Sobolev ladder at levels `0 ≤ 1`, since
`sob 0 = en` and `sob 1 = ens`. -/
lemma en_le_ens {c : (Fin 3 → ℤ) → Vel} (hc0 : c 0 = 0)
    (hZ : Summable fun k => ‖freq k‖ ^ 2 * ‖c k‖ ^ 2) :
    en c ≤ ens c := by
  have hZ' : Summable fun k => ‖freq k‖ ^ (2 * 1) * ‖c k‖ ^ 2 := by
    simpa using hZ
  have h := sob_le_sob (j := 0) (m := 1) (by omega) hc0 hZ'
  rwa [sob_zero_eq_en, sob_one_eq_ens] at h

/-- **W-R0: exponential energy decay of a trapped Galerkin flow.**

A finitely supported flow off the zero mode, solving the mode ODE with a
forcing whose energy pairing is nonpositive on the window, has energy
decaying at least at rate `2ν`. The hypotheses are exactly
`galerkin_conditional_trap`'s energy-side hypotheses WEAKENED to the
window (`hODE` on `Icc 0 T`, not on all of `ℝ`), which is the form every
producer in this campaign actually exports - `galerkin_family` gives the
ODE on `Icc 0 T` and `ns_galerkin_global_flow` on `Ici 0`, neither on
`ℝ`. The conclusion strengthens the trap's `en (c t) ≤ en (c 0)` clause
to an explicit rate.

The zero mode is excluded by `hS0`, which is what makes the field
mean-zero and hence what makes `en_le_ens` available. -/
theorem galerkin_energy_decay {ν T : ℝ} (hν : 0 < ν) {S : Finset (Fin 3 → ℤ)}
    (hS0 : (0 : Fin 3 → ℤ) ∉ S) {c F : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ t k, k ∉ S → c t k = 0)
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + F t k) t)
    (hEpair : ∀ t ∈ Ioo (0:ℝ) T, (∑ k ∈ S, 2 * inner ℝ (F t k) (c t k)) ≤ 0) :
    ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en (c 0) * Real.exp (-(2 * ν * t)) := by
  intro t ht
  -- the finite-support collapse identities
  have hen_eq : ∀ s, en (c s) = ∑ k ∈ S, ‖c s k‖ ^ 2 := by
    intro s
    have h := weighted_tsum_eq_sum (fun _ => (1:ℝ)) (hsupp s)
    simpa [en] using h
  have hens_eq : ∀ s, ens (c s) = ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 := fun s =>
    weighted_tsum_eq_sum _ (hsupp s)
  set cd : ℝ → (Fin 3 → ℤ) → Vel :=
    fun s k => (-(ν * ‖freq k‖ ^ 2)) • c s k + F s k with hcd
  -- the energy derivative, through the finite collapse first
  have hen_deriv : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt (fun r => en (c r))
      (∑ k ∈ S, 2 * inner ℝ (cd s k) (c s k)) s := by
    intro s hs
    have h := hasDerivAt_weighted_finset_sum_sq (fun _ => (1:ℝ)) S (c' := cd)
      (fun k => hODE s hs k)
    have heq : (fun r => ∑ k ∈ S, (1:ℝ) * ‖c r k‖ ^ 2) = fun r => en (c r) := by
      funext r
      rw [hen_eq r]
      simp
    rw [heq] at h
    simpa using h
  -- mean-zero and summability, from the support hypothesis
  have hmean : ∀ s, c s 0 = 0 := fun s => hsupp s 0 hS0
  have hZsum : ∀ s, Summable fun k => ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 := fun s =>
    summable_weighted_of_support _ (hsupp s)
  -- the Poincare-upgraded derivative bound
  have hderiv_le : ∀ s ∈ Ioo (0:ℝ) T,
      (∑ k ∈ S, 2 * inner ℝ (cd s k) (c s k)) ≤ -(2 * ν) * en (c s) := by
    intro s hs
    have hsplit : (∑ k ∈ S, 2 * inner ℝ (cd s k) (c s k)) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2) +
          ∑ k ∈ S, 2 * inner ℝ (F s k) (c s k) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcd]
      simp only [inner_add_left, real_inner_smul_left]
      rw [real_inner_self_eq_norm_sq]
      ring
    rw [hsplit]
    have hp : en (c s) ≤ ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 := by
      have h := en_le_ens (hmean s) (hZsum s)
      rwa [hens_eq s] at h
    have hscale : 2 * ν * en (c s) ≤
        2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    have h2 := hEpair s hs
    linarith
  -- the exponential factor g s = en (c s) * exp (2ν s)
  set g : ℝ → ℝ := fun s => en (c s) * Real.exp (2 * ν * s) with hg
  have hgd : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt g
      (((∑ k ∈ S, 2 * inner ℝ (cd s k) (c s k)) + 2 * ν * en (c s)) *
        Real.exp (2 * ν * s)) s := by
    intro s hs
    have h1 := hen_deriv s hs
    have h2 : HasDerivAt (fun r : ℝ => Real.exp (2 * ν * r))
        (Real.exp (2 * ν * s) * (2 * ν)) s := by
      have h3 : HasDerivAt (fun r : ℝ => 2 * ν * r) (2 * ν) s := by
        simpa using (hasDerivAt_id s).const_mul (2 * ν)
      exact (Real.hasDerivAt_exp _).comp s h3
    have h4 := h1.mul h2
    have heq : ((∑ k ∈ S, 2 * inner ℝ (cd s k) (c s k)) + 2 * ν * en (c s)) *
        Real.exp (2 * ν * s) =
        (∑ k ∈ S, 2 * inner ℝ (cd s k) (c s k)) * Real.exp (2 * ν * s) +
          en (c s) * (Real.exp (2 * ν * s) * (2 * ν)) := by ring
    rw [hg, heq]
    exact h4
  have hsubT : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := Icc_subset_Icc le_rfl ht.2
  have hgc : ContinuousOn g (Icc 0 t) := fun s hs =>
    (hgd s (hsubT hs)).continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (Ioo 0 t) := fun s hs =>
    (hgd s (hsubT (Ioo_subset_Icc_self hs))).differentiableAt.differentiableWithinAt
  have hgderiv : ∀ s ∈ Ioo (0:ℝ) t, deriv g s ≤ 0 := by
    intro s hs
    have hsT : s ∈ Ioo (0:ℝ) T := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
    rw [(hgd s (hsubT (Ioo_subset_Icc_self hs))).deriv]
    have hexp : 0 < Real.exp (2 * ν * s) := Real.exp_pos _
    have h := hderiv_le s hsT
    have hsum : (∑ k ∈ S, 2 * inner ℝ (cd s k) (c s k)) + 2 * ν * en (c s) ≤ 0 := by
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg hsum hexp.le
  have hmono := le_of_deriv_nonpos ht.1 hgc hgdiff hgderiv
  -- unfold g and divide the exponential across
  have hg0 : g 0 = en (c 0) := by
    rw [hg]
    simp
  rw [hg0] at hmono
  have hgt : en (c t) * Real.exp (2 * ν * t) ≤ en (c 0) := hmono
  have hme : Real.exp (2 * ν * t) * Real.exp (-(2 * ν * t)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h7 := mul_le_mul_of_nonneg_right hgt (Real.exp_pos (-(2 * ν * t))).le
  calc en (c t)
      = en (c t) * (Real.exp (2 * ν * t) * Real.exp (-(2 * ν * t))) := by
        rw [hme]; ring
    _ = en (c t) * Real.exp (2 * ν * t) * Real.exp (-(2 * ν * t)) := by ring
    _ ≤ en (c 0) * Real.exp (-(2 * ν * t)) := h7

end TheoremB
