/-
# Mode-wise Arzela-Ascoli extraction (Tier 3, wave 3, abstract half)

The compactness engine of the Galerkin limit: uniformly bounded, uniformly
Lipschitz mode curves on a window form a compact set of continuous maps
(Arzela-Ascoli in the compact-open topology), and the countable product over
all modes is compact and first-countable, so ONE subsequence converges for
every mode simultaneously — uniformly on the window, with the limit again
Lipschitz and bounded.

Pin facts this construction leans on: product METRIZABILITY is finite-index
only at this Mathlib pin, but sequential extraction needs only first
countability, whose countable-index pi instance synthesizes automatically.
-/
import TheoremB.NSGalerkin

namespace TheoremB

open Metric Set

/-- The per-mode candidate compact set: `L`-Lipschitz curves on `[0,T]` with
values in the closed `B`-ball, as a subset of `C(Icc 0 T, Vel)`. -/
def modeSet (T B : ℝ) (L : NNReal) : Set C(Set.Icc (0:ℝ) T, Vel) :=
  {f | LipschitzWith L ⇑f ∧ ∀ t, f t ∈ closedBall 0 B}

theorem isCompact_modeSet (T B : ℝ) (L : NNReal) : IsCompact (modeSet T B L) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · have hset : ContinuousMap.toFun '' (modeSet T B L) =
        {g : Set.Icc (0:ℝ) T → Vel | LipschitzWith L g ∧ ∀ t, g t ∈ closedBall 0 B} := by
      ext g
      constructor
      · rintro ⟨f, hf, rfl⟩; exact hf
      · rintro ⟨h1, h2⟩; exact ⟨⟨g, h1.continuous⟩, ⟨h1, h2⟩, rfl⟩
    rw [hset]
    refine IsCompact.of_isClosed_subset
      (isCompact_pi_infinite fun _ => isCompact_closedBall 0 B) ?_ ?_
    · rw [Set.setOf_and, Set.setOf_forall]
      exact (isClosed_setOf_lipschitzWith L).inter
        (isClosed_iInter fun t => isClosed_closedBall.preimage (continuous_apply t))
    · exact fun g hg t => hg.2 t
  · apply Metric.equicontinuous_of_continuity_modulus (fun d => L * d)
    · have h : Filter.Tendsto (fun d : ℝ => (L : ℝ) * d) (nhds 0) (nhds ((L : ℝ) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using h
    · rintro x y ⟨f, hf⟩
      exact hf.1.dist_le_mul x y

/-- **The extraction**: from any sequence of mode-indexed curve families living
in the per-mode compact sets, ONE subsequence converges (in `C(Icc 0 T, Vel)`,
i.e. uniformly on the window, per mode) for every mode simultaneously; the
limit is again mode-wise Lipschitz and bounded. -/
theorem mode_extraction (T B : ℝ) (L : (Fin 3 → ℤ) → NNReal)
    (u : ℕ → ∀ _ : Fin 3 → ℤ, C(Set.Icc (0:ℝ) T, Vel))
    (hu : ∀ n k, u n k ∈ modeSet T B (L k)) :
    ∃ f : ∀ _ : Fin 3 → ℤ, C(Set.Icc (0:ℝ) T, Vel),
      (∀ k, f k ∈ modeSet T B (L k)) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, Filter.Tendsto (fun n => u (φ n) k) Filter.atTop (nhds (f k)) := by
  obtain ⟨f, hf, φ, hφ, hconv⟩ :=
    (isCompact_univ_pi fun k => isCompact_modeSet T B (L k)).tendsto_subseq
      (x := u) (fun n => Set.mem_univ_pi.2 fun k => hu n k)
  exact ⟨f, fun k => hf k (Set.mem_univ k), φ, hφ, fun k => tendsto_pi_nhds.1 hconv k⟩

/-- Convergence in `C(Icc 0 T, Vel)` is uniform convergence on the window. -/
lemma modeTendstoUniformly {T : ℝ} {g : ℕ → C(Set.Icc (0:ℝ) T, Vel)}
    {f : C(Set.Icc (0:ℝ) T, Vel)}
    (h : Filter.Tendsto g Filter.atTop (nhds f)) :
    TendstoUniformly (fun n t => g n t) (⇑f) Filter.atTop :=
  ContinuousMap.tendsto_iff_tendstoUniformly.1 h

end TheoremB
