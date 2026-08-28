/-
# Fourier synthesis of coefficient flows (Tier 5, base layer)

From an ℓ² coefficient family on ℤ³ to a genuine L² function on the unit
3-torus, component by component: the synthesis operator, coefficient
recovery, and the Parseval identities. The campaign's coefficient flows
(Vel-valued, `Vel := EuclideanSpace ℂ (Fin 3)`) synthesize as component
triples `Fin 3 → L2T3` — Mathlib's `mFourierBasis` is scalar, and this
matches the leray-hopf component convention.

The three local MeasureSpace instances replicate Mathlib's AddCircleMulti
preamble VERBATIM (as TheoremB/FourierDeriv.lean does): without them,
`volume` resolves to a different measure and the Lp types are not the ones
`mFourierBasis` lives on.
-/
import TheoremB.FullUnique

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance tsyn_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance tsyn_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance tsyn_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit 3-torus. -/
abbrev T3 := UnitAddTorus (Fin 3)

/-- Scalar L² on the unit 3-torus (with the probability Haar measure). -/
abbrev L2T3 : Type := MeasureTheory.Lp ℂ 2 (volume : Measure T3)

/-- Component square-summability from `Vel`-level square-summability. -/
lemma summable_component {c : (Fin 3 → ℤ) → Vel} (j : Fin 3)
    (hc : Summable fun k => ‖c k‖ ^ 2) :
    Summable fun k => ‖c k j‖ ^ 2 :=
  hc.of_nonneg_of_le (fun k => by positivity)
    (fun k => by
      have h := PiLp.norm_apply_le (c k) j
      exact pow_le_pow_left₀ (norm_nonneg _) h 2)

/-- The `j`-th component family of a coefficient field, as an ℓ² element. -/
def velSeq (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖ ^ 2) : ℓ²((Fin 3 → ℤ), ℂ) :=
  ⟨fun k => c k j, by
    apply memℓp_gen
    have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
    simpa [h2, Real.rpow_natCast] using summable_component j hc⟩

@[simp] lemma velSeq_apply (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖ ^ 2) (k : Fin 3 → ℤ) :
    (velSeq j c hc : (Fin 3 → ℤ) → ℂ) k = c k j := rfl

/-- **The synthesis operator**: the `j`-th component of the velocity field
whose Fourier coefficients are the `j`-components of `c`. -/
def synth (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖ ^ 2) : L2T3 :=
  (mFourierBasis (d := Fin 3)).repr.symm (velSeq j c hc)

/-- **Coefficient recovery**: the synthesized field's Fourier coefficients
are the input coefficients. -/
lemma mFourierCoeff_synth (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖ ^ 2) (k : Fin 3 → ℤ) :
    mFourierCoeff (synth j c hc : T3 → ℂ) k = c k j := by
  have h : mFourierCoeff (synth j c hc : T3 → ℂ) k =
      ((mFourierBasis (d := Fin 3)).repr (synth j c hc) : (Fin 3 → ℤ) → ℂ) k :=
    (mFourierBasis_repr _ _).symm
  rw [h]
  unfold synth
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The synthesis is the L²-convergent Fourier series of its coefficients. -/
lemma hasSum_synth (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖ ^ 2) :
    HasSum (fun k => c k j • (mFourierBasis (d := Fin 3)) k) (synth j c hc) := by
  have h := HilbertBasis.hasSum_repr_symm (mFourierBasis (d := Fin 3)) (velSeq j c hc)
  exact h

/-- **Parseval, per component**: the synthesized component's squared L²-norm
is the component coefficient energy. -/
lemma norm_synth_sq (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖ ^ 2) :
    ‖synth j c hc‖ ^ (2:ℝ) = ∑' k, ‖c k j‖ ^ (2:ℝ) := by
  unfold synth
  rw [LinearIsometryEquiv.norm_map]
  have h := lp.norm_rpow_eq_tsum (p := 2)
    (E := fun _ : (Fin 3 → ℤ) => ℂ) (by norm_num) (velSeq j c hc)
  simpa using h

/-- **Parseval, total**: the summed squared norms of the three synthesized
components equal the coefficient energy `en c`. -/
lemma sum_norm_synth_sq (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖ ^ 2) :
    (∑ j : Fin 3, ‖synth j c hc‖ ^ (2:ℝ)) = en c := by
  have h1 : ∀ j : Fin 3, ‖synth j c hc‖ ^ (2:ℝ) = ∑' k, ‖c k j‖ ^ 2 := by
    intro j
    rw [norm_synth_sq]
    exact tsum_congr fun k => by
      rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have h2 : (∑ j : Fin 3, ‖synth j c hc‖ ^ (2:ℝ)) =
      ∑ j : Fin 3, ∑' k, ‖c k j‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => h1 j
  rw [h2]
  -- swap the finite sum with the tsum, then collapse the Euclidean norm
  rw [← Summable.tsum_finsetSum (fun j _ => summable_component j hc)]
  have hen : en c = ∑' k, ‖c k‖ ^ 2 := rfl
  rw [hen]
  refine tsum_congr fun k => ?_
  have h3 : ‖c k‖ ^ 2 = ∑ j : Fin 3, ‖c k j‖ ^ 2 := by
    have h4 := EuclideanSpace.norm_eq (c k)
    rw [h4, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  rw [h3]

open Classical in
/-- The TOTAL synthesis operator: junk-zero off the square-summable class
(the campaign's junk-convention style — every lemma below carries its
`Summable` certificate). -/
def synthT (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) : L2T3 :=
  if hc : Summable (fun k => ‖c k‖ ^ 2) then synth j c hc else 0

lemma synthT_eq (j : Fin 3) {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) : synthT j c = synth j c hc := by
  unfold synthT
  exact dif_pos hc

lemma mFourierCoeff_synthT (j : Fin 3) {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) (k : Fin 3 → ℤ) :
    mFourierCoeff (synthT j c : T3 → ℂ) k = c k j := by
  rw [synthT_eq j hc]
  exact mFourierCoeff_synth j c hc k

lemma norm_synthT_sq (j : Fin 3) {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) :
    ‖synthT j c‖ ^ (2:ℝ) = ∑' k, ‖c k j‖ ^ (2:ℝ) := by
  rw [synthT_eq j hc]
  exact norm_synth_sq j c hc

lemma sum_norm_synthT_sq {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) :
    (∑ j : Fin 3, ‖synthT j c‖ ^ (2:ℝ)) = en c := by
  refine (Finset.sum_congr rfl fun j _ => by rw [synthT_eq j hc]).trans
    (sum_norm_synth_sq c hc)

end

end TheoremB
