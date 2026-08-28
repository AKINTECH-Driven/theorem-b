/-
# Test separation and density (Tier 5 polish)

Band-limited divergence-free tests separate divergence-free coefficient
fields (the defect-as-test trick, one more time), and Mathlib's own density
of the Fourier span — the formal citation behind the capstone's band-limited
scope note.
-/
import TheoremB.TheoremBTorus

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance f2_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance f2_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance f2_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- `dotR` kills the zero vector (local copy; the siblings are `private`). -/
private lemma f2_dotR_zero (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

/-- **Band tests separate**: two square-summable div-free coefficient families that
agree at the zero mode and produce identical pairings against every finitely
supported div-free test family are equal mode-by-mode.  The engine is the
defect-as-test trick: at each `k ≠ 0` the defect `a k − b k` is itself div-free
at `k`, so the single-mode test supported on `{k}` with value the defect is
admissible, and instantiating the hypothesis there collapses to
`⟪d, d⟫ = 0`, hence `d = 0`. -/
theorem band_tests_separate {a b : (Fin 3 → ℤ) → Vel}
    (hadiv : DivFree a) (hbdiv : DivFree b)
    (h : ∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
      (∀ k, k ∉ F → w k = 0) → DivFree w →
      (∑ k ∈ F, inner ℂ (w k) (a k)) = ∑ k ∈ F, inner ℂ (w k) (b k)) :
    ∀ k, a k = b k := by
  intro k
  -- the defect is div-free at mode `k` (every `k`, the zero mode included:
  -- `freq 0 = 0` makes the condition automatic there)
  have hddiv : dotR (a k - b k) (freq k) = 0 := by
    rw [dotR_sub_left', hadiv k, hbdiv k, sub_self]
  -- the single-mode test carrying the defect is admissible
  have hsupp : ∀ m, m ∉ ({k} : Finset (Fin 3 → ℤ)) →
      (fun m => if m = k then a k - b k else 0) m = 0 := by
    intro m hm
    exact if_neg (fun hmk => hm (Finset.mem_singleton.mpr hmk))
  have hwdiv : DivFree (fun m => if m = k then a k - b k else 0) := by
    intro m
    rcases eq_or_ne m k with rfl | hmk
    · simpa using hddiv
    · simp [hmk, f2_dotR_zero]
  -- instantiate the pairing hypothesis at `F = {k}`
  have hw := h {k} (fun m => if m = k then a k - b k else 0) hsupp hwdiv
  simp only [Finset.sum_singleton, if_true] at hw
  -- assemble: ⟪d, d⟫ = 0, hence d = 0
  have h2 : inner ℂ (a k - b k) (a k - b k) = (0 : ℂ) := by
    rw [inner_sub_right, hw, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h2)

/-- **Density of the Fourier span**: the ℂ-linear span of the multivariate Fourier
monomials `mFourierLp 2 n`, `n : (Fin 3) → ℤ`, is dense in `L²(T³)`.  This is
Mathlib's `UnitAddTorus.span_mFourierLp_closure_eq_top` specialised to `p = 2`,
`d = Fin 3`; it is the formal citation for the density remark in the capstone's
scope note. -/
theorem mFourier_span_dense :
    (Submodule.span ℂ (Set.range (mFourierLp 2 (d := Fin 3)))).topologicalClosure = ⊤ :=
  span_mFourierLp_closure_eq_top (by simp)

end

end TheoremB
