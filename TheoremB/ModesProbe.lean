/-
# Audit probes for the Tier-7 summit (waves W-R4, W-R5)

The register requires that a capstone be shown NON-VACUOUS before it is
tagged: a theorem whose hypotheses cannot be jointly satisfied is true
and empty. Every probe in this file is a compiled declaration; nothing
below is asserted in prose only.

**Probe 1 (`modes_hypotheses_consistent`).** The zero flow inhabits
every hypothesis of `theorem_B_modes`, for every `ν > 0` and `T ≥ 0`,
at budgets `E = Z = 0` and tolerance `δ = 0`. So the hypothesis set is
consistent. The probe follows the theorem's quantifier order: the
class-uniform `K` is obtained first, from `(ν, E, Z)` alone, and only
then is the inner statement fed a horizon, a tolerance, and the pair of
(zero) flows.

**Probe 2 (`probe2_low_mode_at_4E`, and it is the sharper point).**
Consistency at the zero flow would leave open whether anything
NON-trivial satisfies the low-mode hypothesis. It does, and cheaply: the
hypothesis `∑_{k ∈ box N} ‖d s k‖² ≤ δ` is implied by `en (d s) ≤ δ`,
and every defect in the class obeys `en (d s) ≤ 4E`. So at `δ := 4E`
the hypothesis holds for EVERY pair of flows in the class, for every
`N`, with no assumption relating them.

**Probe 3 (`probe_modes_composes_with_flow`).** Probe 2 composed with
`ns_full_global_flow_modes`: two eternal flows of `ns_full_global_flow`
with DIFFERENT data satisfy the determining-modes estimate on every
window, for every `N` past the threshold, UNCONDITIONALLY at
`δ := 4·max (en c₀) (en c₀')`. So `theorem_B_modes` is inhabited by
genuinely distinct trapped flows, not only by `c₁ = c₂`. What that
instance buys is weak (the floor exceeds the trivial bound `4E`), which
is the honest content of Correction 2 in the rung9 blueprint: the
theorem's force lives at SMALL `δ`, and the statement degrades
gracefully rather than becoming vacuous as `δ` grows.
-/
import TheoremB.DeterminingModes
import TheoremB.ModesFlow

namespace TheoremB

open Set

/-- The zero coefficient field has zero energy. -/
private lemma probe_en_zero : en (fun _ : Fin 3 → ℤ => (0:Vel)) = 0 := by
  simp [en]

/-- The zero coefficient field has zero enstrophy. -/
private lemma probe_ens_zero : ens (fun _ : Fin 3 → ℤ => (0:Vel)) = 0 := by
  simp [ens]

/-- The full convection annihilates the zero field. -/
private lemma probe_convFull_zero (k : Fin 3 → ℤ) :
    convFull (fun _ : Fin 3 → ℤ => (0:Vel)) k = 0 := by
  simp [convFull]

/-- The Leray projection annihilates zero. -/
private lemma probe_lerayProj_zero (k : Fin 3 → ℤ) :
    lerayProj k (0:Vel) = 0 := by
  have h := lerayProj_sub k (0:Vel) 0
  rw [sub_self, sub_self] at h
  exact h

/-- **Probe 1: `theorem_B_modes` is non-vacuous.** The class-uniform
constant is obtained first, at budgets `E = Z = 0`; then every flow
hypothesis of the inner statement is discharged at the zero flow, so the
hypothesis set is consistent for every `ν > 0` and every horizon.
Elaborating this `obtain` together with the `have` that follows it IS
the probe. -/
theorem modes_hypotheses_consistent {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 < K := by
  obtain ⟨K, hK, hmodes⟩ := theorem_B_modes (E := 0) (Z := 0) hν le_rfl le_rfl
  have _probe := hmodes (T := T) (δ := 0)
    (c₁ := fun _ _ => (0:Vel)) (c₂ := fun _ _ => (0:Vel))
    hT le_rfl
    (fun _ => continuousOn_const) (fun _ => continuousOn_const)
    (fun _ _ => ⟨by simp, by simp⟩)
    (fun _ _ => ⟨by simp, by simp⟩)
    (fun _ _ => ⟨le_of_eq probe_en_zero, le_of_eq probe_ens_zero⟩)
    (fun _ _ => ⟨le_of_eq probe_en_zero, le_of_eq probe_ens_zero⟩)
    (fun _ _ k => by simp [dotR])
    (fun _ _ k => by simp [dotR])
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ k => by
      simp only [probe_convFull_zero, probe_lerayProj_zero, smul_zero, add_zero,
        intervalIntegral.integral_zero])
    (fun _ _ k => by
      simp only [probe_convFull_zero, probe_lerayProj_zero, smul_zero, add_zero,
        intervalIntegral.integral_zero])
  exact ⟨K, hK⟩

/-- **Probe 2: at `δ := 4E` the low-mode hypothesis holds for EVERY pair
in the class**, for every `N`, with nothing assumed relating the two
flows: the box sum is dominated by the defect energy
(`Summable.sum_le_tsum`), and the defect energy by `2E + 2E`
(`en_sub_le`). -/
theorem probe2_low_mode_at_4E {E T : ℝ} {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel}
    (h1sum : ∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₁ t l‖ ^ 2))
    (h2sum : ∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₂ t l‖ ^ 2))
    (h1b : ∀ t ∈ Icc (0:ℝ) T, en (c₁ t) ≤ E)
    (h2b : ∀ t ∈ Icc (0:ℝ) T, en (c₂ t) ≤ E) (N : ℕ) :
    ∀ s ∈ Icc (0:ℝ) T,
      (∑ k ∈ insert 0 (boxS N), ‖c₁ s k - c₂ s k‖ ^ 2) ≤ 4 * E := by
  intro s hs
  have hd := summable_sq_sub (h1sum s hs) (h2sum s hs)
  have h1 : (∑ k ∈ insert 0 (boxS N), ‖c₁ s k - c₂ s k‖ ^ 2)
      ≤ en (fun l => c₁ s l - c₂ s l) :=
    hd.sum_le_tsum (insert 0 (boxS N)) (fun l _ => sq_nonneg _)
  have h2 := en_sub_le (h1sum s hs) (h2sum s hs)
  linarith [h1b s hs, h2b s hs]

/-- **Probe 3: the composition is inhabited by DISTINCT trapped flows.**
Two eternal flows of `ns_full_global_flow` with different data, through
`ns_full_global_flow_modes`, with Probe 2 discharging the low-mode
clause at `δ := 4·max (en c₀) (en c₀')`: the determining-modes estimate
holds between them on every window and for every `N` past the
threshold, with NO hypothesis relating the two flows. The instance is
weak (its floor exceeds the trivial bound), which is exactly Correction
2's point; its job is to show the hypothesis set of `theorem_B_modes`
is met by a pair that is not `c₁ = c₂`. -/
theorem probe_modes_composes_with_flow :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ c₀' : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      Summable (fun l => ‖c₀' l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀' l‖ ^ 2) →
      c₀' 0 = 0 → RealField c₀' → DivFree c₀' → κ * en c₀' * ens c₀' < ν ^ 4 →
      ∃ K, 0 < K ∧ ∃ c c' : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧ c' 0 = c₀' ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c' t k = c₀' k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c' s k + lerayProj k (convFull (c' s) k))) ∧
        ∀ T : ℝ, 0 ≤ T → ∀ N : ℕ, 2 * ν + K < ν * (N:ℝ) ^ 2 →
          ∀ t ∈ Icc (0:ℝ) T,
            en (fun l => c t l - c' t l)
              ≤ en (fun l => c₀ l - c₀' l) *
                  Real.exp (-((ν * (N:ℝ) ^ 2 - K) * t))
                + ν * (N:ℝ) ^ 2 / (ν * (N:ℝ) ^ 2 - K) *
                    (4 * max (en c₀) (en c₀')) := by
  obtain ⟨κ, hκ, hflow⟩ := ns_full_global_flow_modes
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ c₀' hE hZ hm hr hd hs hE' hZ' hm' hr' hd' hs'
  obtain ⟨K, hK, c, c', hc0, -, hsum, -, hinteq, -, htrap, -,
    hc0', -, hsum', -, hinteq', -, htrap', -, hest⟩ :=
    hflow hν hE hZ hm hr hd hs hE' hZ' hm' hr' hd' hs'
  refine ⟨K, hK, c, c', hc0, hc0', hinteq, hinteq', ?_⟩
  intro T hT N hN
  have hE0 : 0 ≤ max (en c₀) (en c₀') :=
    le_max_of_le_left (tsum_nonneg fun l => sq_nonneg _)
  have hsub : Icc (0:ℝ) T ⊆ Ici (0:ℝ) := Icc_subset_Ici_self
  exact hest T hT (4 * max (en c₀) (en c₀')) (mul_nonneg (by norm_num) hE0) N hN
    (probe2_low_mode_at_4E (E := max (en c₀) (en c₀'))
      (fun t ht => (hsum t (hsub ht)).1) (fun t ht => (hsum' t (hsub ht)).1)
      (fun t ht => le_trans (htrap t (hsub ht)).1 (le_max_left _ _))
      (fun t ht => le_trans (htrap' t (hsub ht)).1 (le_max_right _ _)) N)

end TheoremB
