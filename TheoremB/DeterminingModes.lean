/-
# Determining modes (Tier 7, wave W-R4)

`theorem_B_modes`: the summit of Tier 7. Two flows in the trap class
whose defect carries at most `δ` in the modes below `N` synchronize
exponentially at rate `ν·N² − K`, down to a floor proportional to `δ`.

The composition is exactly two waves: W-R3 supplies the window integral
inequality with the rate kept instead of discarded, and W-R2b turns a
window inequality into decay with no differentiability.

Read the threshold, not just the rate. It is stated `2ν + K < ν·N²`,
NOT `K < ν·N²`, because W-R0a proved that energy decays at rate `2ν`
unaided: a determining-modes statement that only beat `0` would be
describing the ambient decay and claiming it as synchronization. The
frozen threshold makes the claim honest at the type level - no outward
description of this theorem can overstate it without changing the
statement.

As `N → ∞` the floor `ν·N²/(ν·N² − K)·δ` tends to `δ`: the flow is
recovered to the accuracy with which its low modes are known. `δ = 0`
gives exact synchronization.
-/
import TheoremB.ModesWindow
import TheoremB.WindowDecay

namespace TheoremB

open Set

/-- **W-R4, the Tier-7 summit: determining modes with an explicit
count.** `K` is `pairing_absorbed`'s constant at the class budgets, so
it depends only on `(ν, E, Z)`; any `N` past the threshold
`2ν + K < ν·N²` is a determining-mode count.

Initial data are NOT assumed equal - that is the content. -/
theorem theorem_B_modes :
    ∀ {ν E Z T δ : ℝ}, 0 < ν → 0 ≤ T → 0 ≤ δ →
    ∀ {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel},
    (∀ k, ContinuousOn (fun s => c₁ s k) (Icc (0:ℝ) T)) →
    (∀ k, ContinuousOn (fun s => c₂ s k) (Icc (0:ℝ) T)) →
    (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₁ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ t l‖ ^ 2)) →
    (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₂ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₂ t l‖ ^ 2)) →
    (∀ t ∈ Icc (0:ℝ) T, en (c₁ t) ≤ E ∧ ens (c₁ t) ≤ Z) →
    (∀ t ∈ Icc (0:ℝ) T, en (c₂ t) ≤ E ∧ ens (c₂ t) ≤ Z) →
    (∀ t ∈ Icc (0:ℝ) T, DivFree (c₁ t)) →
    (∀ t ∈ Icc (0:ℝ) T, DivFree (c₂ t)) →
    (∀ t ∈ Icc (0:ℝ) T, c₁ t 0 = 0) →
    (∀ t ∈ Icc (0:ℝ) T, c₂ t 0 = 0) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₁ 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k))) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₂ 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k))) →
    ∃ K, 0 < K ∧ ∀ N : ℕ, 2 * ν + K < ν * (N:ℝ) ^ 2 →
      (∀ s ∈ Icc (0:ℝ) T,
        (∑ k ∈ insert 0 (boxS N), ‖c₁ s k - c₂ s k‖ ^ 2) ≤ δ) →
      ∀ t ∈ Icc (0:ℝ) T,
        en (fun l => c₁ t l - c₂ t l)
          ≤ en (fun l => c₁ 0 l - c₂ 0 l) *
              Real.exp (-((ν * (N:ℝ) ^ 2 - K) * t))
            + ν * (N:ℝ) ^ 2 / (ν * (N:ℝ) ^ 2 - K) * δ := by
  intro ν E Z T δ hν hT hδ c₁ c₂ h1cont h2cont h1sum h2sum h1b h2b
    h1div h2div h1zero h2zero h1eq h2eq
  obtain ⟨K, hK, hwindow⟩ := modes_window_ineq hν hT hδ h1cont h2cont
    h1sum h2sum h1b h2b h1div h2div h1zero h2zero h1eq h2eq
  refine ⟨K, hK, ?_⟩
  intro N hthr hlow
  -- the threshold forces a positive rate, strictly better than ambient decay
  have hrate : 0 < ν * (N:ℝ) ^ 2 - K := by nlinarith
  have hNpos : 0 < N := by
    by_contra hcon
    push_neg at hcon
    interval_cases N
    · simp at hthr
      nlinarith
  -- budgets, for the integrability of the energy history
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_refl 0, hT⟩
  have hE0 : 0 ≤ E := le_trans (tsum_nonneg fun l => sq_nonneg _) (h1b 0 h0mem).1
  have hdcont : ∀ k, ContinuousOn (fun s => c₁ s k - c₂ s k) (Icc (0:ℝ) T) :=
    fun k => (h1cont k).sub (h2cont k)
  have hdsum : ∀ s ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₁ s l - c₂ s l‖ ^ 2) :=
    fun s hs => summable_sq_sub (h1sum s hs).1 (h2sum s hs).1
  have hdenE : ∀ s ∈ Icc (0:ℝ) T, en (fun l => c₁ s l - c₂ s l) ≤ 4 * E := by
    intro s hs
    have h := en_sub_le (h1sum s hs).1 (h2sum s hs).1
    linarith [(h1b s hs).1, (h2b s hs).1]
  have hEint0T : IntervalIntegrable (fun s => en (fun l => c₁ s l - c₂ s l))
      MeasureTheory.volume 0 T :=
    intervalIntegrable_en (by positivity) hT hdcont hdsum hdenE
  -- feed the window inequality to the derivative-free engine
  have hdecay := decay_of_window_integral_ineq
    (e := fun s => en (fun l => c₁ s l - c₂ s l))
    (c := ν * (N:ℝ) ^ 2 - K) (A := ν * (N:ℝ) ^ 2 * δ) (T := T)
    hrate (by positivity) hT
    (fun s _ => tsum_nonneg fun l => sq_nonneg _)
    (fun t₀ ht₀ t ht => hEint0T.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc ht₀.1 ht.2))
    (fun t₀ ht₀ t ht => hwindow N hNpos hlow t₀ ht₀ t ht)
  intro t ht
  have h := hdecay t ht
  have hfloor : ν * (N:ℝ) ^ 2 * δ / (ν * (N:ℝ) ^ 2 - K)
      = ν * (N:ℝ) ^ 2 / (ν * (N:ℝ) ^ 2 - K) * δ := by ring
  rw [hfloor] at h
  exact h

end TheoremB
