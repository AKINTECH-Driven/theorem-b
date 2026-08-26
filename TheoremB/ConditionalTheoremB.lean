/-
  TheoremB/ConditionalTheoremB.lean
  Tier 2 of the Theorem B campaign (M3, 27 Aug 2026, full-auto session).

  The composition of Tier 0 (RiccatiTrap: trap_forward_invariance,
  riccati_window) with Tier 1 (SpectralNorms: master_inequality, W2):
  the CONDITIONAL Theorem B and Theorem A for a time-parametrized spectral
  trajectory.  The standing conditional hypothesis is the enstrophy-balance
  inequality  Z' <= -2nu*D + 2*triMaj(...)  — the single obligation Tier 3
  discharges from the PDE.  Discharging it requires BOTH the pointwise
  domination of the concrete convection pairing by the majorant AND the
  summability of that pairing (triMaj's nested tsums return 0 on
  non-summable inner sums, so domination claims need their own summability
  hypotheses on the Tier-3 side).

  The trap constant kappa and the window constant K are BOTH the
  master-inequality constant: uniform in c, nu, and T.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.RiccatiTrap
import TheoremB.SpectralNorms

namespace TheoremB

open Set

/-- **Tier 2: conditional trap (Theorem B, conditional form).**
For a time-parametrized spectral trajectory whose energy can only descend and
whose enstrophy obeys the balance inequality
`Z' ≤ -2ν·D + 2·(trilinear majorant)` — the standing conditional hypothesis
that Tier 3 will discharge from the PDE — there is a UNIFORM constant `κ`
(the master-inequality constant, independent of `c`, `ν`, `T`) such that
small data `κ·E₀·Z₀ < ν⁴` traps the orbit: the smallness persists and both
quantities stay below their initial values for the whole lifespan. -/
theorem conditional_trap {V : Type*} [NormedAddCommGroup V] :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {c : ℝ → (Fin 3 → ℤ) → V},
      (∀ t ∈ Ico (0:ℝ) T, c t 0 = 0) →
      (∀ t ∈ Ico (0:ℝ) T, Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) →
      ContinuousOn (fun t => en (c t)) (Ico 0 T) →
      ContinuousOn (fun t => ens (c t)) (Ico 0 T) →
      DifferentiableOn ℝ (fun t => en (c t)) (Ioo 0 T) →
      DifferentiableOn ℝ (fun t => ens (c t)) (Ioo 0 T) →
      (∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => en (c s)) t ≤ 0) →
      (∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => ens (c s)) t ≤
        -(2 * ν) * dis (c t) +
          2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
            (fun m => ‖freq m‖ ^ 2 * ‖c t m‖)) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Ico (0:ℝ) T,
        κ * en (c t) * ens (c t) < ν ^ 4 ∧
          ens (c t) ≤ ens (c 0) ∧ en (c t) ≤ en (c 0) := by
  obtain ⟨K, hK, hmaster⟩ := master_inequality (V := V)
  refine ⟨K, hK, ?_⟩
  intro T ν hν c hmean hDsum hEc hZc hEd hZd hE' hbal h0
  have hν4 : (0:ℝ) < ν ^ 4 := by positivity
  have hEnn : ∀ t ∈ Ico (0:ℝ) T, 0 ≤ en (c t) := fun t _ =>
    tsum_nonneg fun k => sq_nonneg _
  have hZnn : ∀ t ∈ Ico (0:ℝ) T, 0 ≤ ens (c t) := fun t _ =>
    tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hZ'cond : ∀ t ∈ Ioo (0:ℝ) T,
      K * en (c t) * ens (c t) < ν ^ 4 → deriv (fun s => ens (c s)) t ≤ 0 := by
    intro t ht hreg
    have htI : t ∈ Ico (0:ℝ) T := ⟨ht.1.le, ht.2⟩
    have hm := hmean t htI
    have hs := hDsum t htI
    have hW2 := ens_sq_le_en_mul_dis hm hs
    have hM := hmaster (c t) hm hs ν hν
    have hDnn : 0 ≤ dis (c t) :=
      tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
    have hEnn' : 0 ≤ en (c t) := tsum_nonneg fun k => sq_nonneg _
    have hZnn' : 0 ≤ ens (c t) :=
      tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
    have hstep : deriv (fun s => ens (c s)) t ≤
        -(ν * dis (c t)) + K / ν ^ 3 * ens (c t) ^ 3 := by
      have hb := hbal t ht
      linarith [hM]
    have hfin : K / ν ^ 3 * ens (c t) ^ 3 ≤ ν * dis (c t) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < ν ^ 3)]
      nlinarith [mul_le_mul_of_nonneg_left hW2 (mul_nonneg hK.le hZnn'),
        mul_le_mul_of_nonneg_right hreg.le hDnn,
        mul_nonneg hK.le (mul_nonneg hEnn' hDnn)]
    linarith
  exact trap_forward_invariance hK hν4 hEc hZc hEd hZd hEnn hZnn hE' hZ'cond h0

/-- **Tier 2: conditional safety window (Theorem A, conditional form).**
Under the same balance hypothesis, a positive-enstrophy trajectory obeys the
exact Riccati-orbit bound with `a = K/ν³` inside its window — the
quantitative safety time `T_safe ~ ν³/(2K·Z₀²)`, machine-checked. -/
theorem conditional_safety_window {V : Type*} [NormedAddCommGroup V] :
    ∃ K, 0 < K ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {c : ℝ → (Fin 3 → ℤ) → V},
      (∀ t ∈ Ico (0:ℝ) T, c t 0 = 0) →
      (∀ t ∈ Ico (0:ℝ) T, Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) →
      ContinuousOn (fun t => ens (c t)) (Ico 0 T) →
      DifferentiableOn ℝ (fun t => ens (c t)) (Ioo 0 T) →
      (∀ t ∈ Ico (0:ℝ) T, 0 < ens (c t)) →
      (∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => ens (c s)) t ≤
        -(2 * ν) * dis (c t) +
          2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
            (fun m => ‖freq m‖ ^ 2 * ‖c t m‖)) →
      ∀ t ∈ Ico (0:ℝ) T, 2 * (K / ν ^ 3) * ens (c 0) ^ 2 * t < 1 →
        ens (c t) ^ 2 ≤ ens (c 0) ^ 2 / (1 - 2 * (K / ν ^ 3) * ens (c 0) ^ 2 * t) := by
  obtain ⟨K, hK, hmaster⟩ := master_inequality (V := V)
  refine ⟨K, hK, ?_⟩
  intro T ν hν c hmean hDsum hZc hZd hpos hbal t ht hwin
  have ha : (0:ℝ) < K / ν ^ 3 := by positivity
  have hZ' : ∀ s ∈ Ioo (0:ℝ) T,
      deriv (fun u => ens (c u)) s ≤ K / ν ^ 3 * ens (c s) ^ 3 := by
    intro s hs
    have hsI : s ∈ Ico (0:ℝ) T := ⟨hs.1.le, hs.2⟩
    have hm := hmean s hsI
    have hsum := hDsum s hsI
    have hM := hmaster (c s) hm hsum ν hν
    have hb := hbal s hs
    have hDnn : 0 ≤ dis (c s) :=
      tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
    nlinarith [mul_nonneg hν.le hDnn]
  exact riccati_window ha hZc hZd hpos hZ' ht hwin
