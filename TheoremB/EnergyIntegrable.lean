/-
# Integrability of the energy history (Tier 7, wave W-R2a)

`decay_of_window_integral_ineq` consumes `IntervalIntegrable` on
subwindows, and nothing stronger. That is fortunate, because CONTINUITY
of `s ↦ en (d s)` is not available cheaply: the Weierstrass route
(`continuousOn_tsum`) needs a summable uniform majorant, and the only
candidate here is `‖d s k‖² ≤ Z/‖freq k‖²`, whose sum `Σ‖k‖^(−2)`
DIVERGES over ℤ³ - the campaign's recurring obstruction, recorded in the
announcement draft's long-form note on the ε/3 tail method.

Measurability, on the other hand, is free: `en (d ·)` is the pointwise
limit of its continuous box sections, and it is bounded by the energy
budget, so it is integrable on the window. This file is the `en` twin of
the private `b4_*` machinery that `TailBounds.tail_integrable` already
runs for `ens`, with `b4_box_tendsto` re-derived public from the public
`exists_boxS`.
-/
import TheoremB.TailBounds

namespace TheoremB

open Set

/-- The boxes `insert 0 (boxS R)` exhaust the lattice. Public re-derivation
of TailBounds' private `b4_box_tendsto`. -/
lemma box_tendsto_atTop :
    Filter.Tendsto (fun R : ℕ => insert 0 (boxS R)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) fun k => ?_
  · refine Finset.insert_subset_insert _ fun k hk => ?_
    rw [mem_boxS] at hk ⊢
    refine ⟨hk.1, fun i => ?_⟩
    have := hk.2 i
    omega
  · rcases eq_or_ne k 0 with rfl | hk
    · exact ⟨0, Finset.mem_insert_self _ _⟩
    · obtain ⟨R, hR⟩ := exists_boxS k hk
      exact ⟨R, Finset.mem_insert_of_mem (hR R le_rfl)⟩

/-- Box sections of the energy sum converge to the energy. -/
lemma en_sec_tendsto {c : (Fin 3 → ℤ) → Vel} (hs : Summable fun l => ‖c l‖ ^ 2) :
    Filter.Tendsto (fun R : ℕ => ∑ k ∈ insert 0 (boxS R), ‖c k‖ ^ 2)
      Filter.atTop (nhds (en c)) := by
  have h1 : Filter.Tendsto (fun F : Finset (Fin 3 → ℤ) => ∑ k ∈ F, ‖c k‖ ^ 2)
      Filter.atTop (nhds (en c)) := hs.hasSum
  exact h1.comp box_tendsto_atTop

/-- Finite sections of the energy sum are continuous in time. -/
lemma en_sec_contOn {T : ℝ} {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T))
    (F : Finset (Fin 3 → ℤ)) :
    ContinuousOn (fun s => ∑ k ∈ F, ‖d s k‖ ^ 2) (Icc (0:ℝ) T) := by
  refine continuousOn_finsetSum F fun k _ => ?_
  exact ((hcont k).norm).pow 2

/-- `s ↦ en (d s)` is a.e. strongly measurable on the window, as the
pointwise limit of its continuous box sections. -/
lemma aestronglyMeasurable_en {T : ℝ} {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T))
    (hsum : ∀ t ∈ Icc (0:ℝ) T, Summable fun l => ‖d t l‖ ^ 2) :
    MeasureTheory.AEStronglyMeasurable (fun s => en (d s))
      (MeasureTheory.volume.restrict (Icc (0:ℝ) T)) := by
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (f := fun (n : ℕ) (s : ℝ) => ∑ k ∈ insert 0 (boxS n), ‖d s k‖ ^ 2)
    (fun n => ?_) ?_
  · exact (en_sec_contOn hcont _).aestronglyMeasurable measurableSet_Icc
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun s hs => en_sec_tendsto (hsum s hs)

/-- **W-R2a.** The energy history is interval integrable on the window:
measurable as a limit of sections, and squeezed between `0` and the
energy budget. -/
theorem intervalIntegrable_en {E T : ℝ} (hE0 : 0 ≤ E) (hT : 0 ≤ T)
    {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T))
    (hsum : ∀ t ∈ Icc (0:ℝ) T, Summable fun l => ‖d t l‖ ^ 2)
    (hbound : ∀ t ∈ Icc (0:ℝ) T, en (d t) ≤ E) :
    IntervalIntegrable (fun s => en (d s)) MeasureTheory.volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  refine MeasureTheory.Integrable.mono' (g := fun _ => E)
    (MeasureTheory.integrableOn_const measure_Icc_lt_top.ne)
    (aestronglyMeasurable_en hcont hsum) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun s hs => ?_
  have h1 : (0:ℝ) ≤ en (d s) := tsum_nonneg fun l => sq_nonneg _
  have h3 := hbound s hs
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

end TheoremB
