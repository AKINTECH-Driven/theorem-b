/-
# Audit probes for the Tier-7 summit (wave W-R4)

The register requires that a capstone be shown NON-VACUOUS before it is
tagged: a theorem whose hypotheses cannot be jointly satisfied is true
and empty. These probes are compiled, not asserted.

**Probe 1 (this file).** The zero flow inhabits every hypothesis of
`theorem_B_modes`, for every `ν > 0` and `T ≥ 0`, at budgets
`E = Z = 0` and tolerance `δ = 0`. So the hypothesis set is consistent.

**Probe 2 (prose, and it is the sharper point).** Consistency at the
zero flow would leave open whether anything NON-trivial satisfies the
low-mode hypothesis. It does, and cheaply: the hypothesis
`∑_{k ∈ box N} ‖d s k‖² ≤ δ` is implied by `en (d s) ≤ δ`, and every
defect in the class obeys `en (d s) ≤ 4E`. So at `δ := 4E` the
hypothesis holds for EVERY pair of flows in the class, with no
assumption relating them - the theorem is inhabited by genuinely
distinct flows, not only by `c₁ = c₂`. What that instance buys is weak
(the floor exceeds the trivial bound `4E`), which is the honest content
of Correction 2 in the rung9 blueprint: the theorem's force lives at
SMALL `δ`, and the statement degrades gracefully rather than becoming
vacuous as `δ` grows.
-/
import TheoremB.DeterminingModes

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

/-- **Probe 1: `theorem_B_modes` is non-vacuous.** Every hypothesis is
discharged at the zero flow, so the hypothesis set is consistent for
every `ν > 0` and every horizon. Elaborating this `obtain` IS the
probe. -/
theorem modes_hypotheses_consistent {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 < K := by
  obtain ⟨K, hK, _⟩ := theorem_B_modes (E := 0) (Z := 0) (T := T) (δ := 0)
    (c₁ := fun _ _ => (0:Vel)) (c₂ := fun _ _ => (0:Vel))
    hν hT le_rfl
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

end TheoremB
