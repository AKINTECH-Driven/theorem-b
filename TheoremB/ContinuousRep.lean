/-
# The continuous representative (Tier 6, wave W5a)

From an ℓ¹ coefficient family on ℤ³ to a genuine CONTINUOUS function on the
unit 3-torus, component by component: the sup-norm synthesis `uCont` in
C(T3, ℂ), its uniform and pointwise Fourier expansions, the identification
of its L² class with the campaign's `synthT` (so every structural clause of
TorusSynthesis/TorusStructure transfers), coefficient recovery, the ℓ¹
sup-norm bound, and pointwise reality under `RealField`.

The three local MeasureSpace instances replicate Mathlib's AddCircleMulti
preamble VERBATIM (as TheoremB/TorusSynthesis.lean does): without them,
`volume` resolves to a different measure and the Lp types are not the ones
`mFourierBasis` lives on.
-/
import TheoremB.TorusStructure

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance cr_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance cr_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance cr_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Component ℓ¹-summability from `Vel`-level ℓ¹-summability. -/
lemma summable_component_norm {c : (Fin 3 → ℤ) → Vel} (j : Fin 3)
    (hc : Summable fun k => ‖c k‖) :
    Summable fun k => ‖c k j‖ :=
  hc.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => PiLp.norm_apply_le (c k) j)

/-- The character series of an ℓ¹ coefficient family is summable in
`C(T3, ℂ)` with the sup norm — i.e. converges uniformly. -/
lemma summable_uContSeries (j : Fin 3) {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖) :
    Summable fun k => c k j • (mFourier (d := Fin 3) k) := by
  apply Summable.of_norm
  refine (summable_component_norm j hc).congr fun k => ?_
  rw [norm_smul, mFourier_norm, mul_one]

set_option linter.unusedVariables false in
/-- **The continuous representative**: the sup-norm sum of the Fourier
series of an ℓ¹ coefficient family, as an element of `C(T3, ℂ)`. The
`Summable` certificate is carried in the signature (junk-tsum discipline);
`hasSum_uCont` exports the convergence. -/
def uCont (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) : C(T3, ℂ) :=
  ∑' k, c k j • mFourier k

/-- The continuous representative is the sup-norm (uniform) limit of its
Fourier series. -/
lemma hasSum_uCont (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) :
    HasSum (fun k => c k j • (mFourier (d := Fin 3) k)) (uCont j c hc) :=
  (summable_uContSeries j hc).hasSum

/-- **Pointwise evaluation**: the Fourier series of the continuous
representative converges at EVERY point (not just a.e.). -/
lemma uCont_apply (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) (x : T3) :
    HasSum (fun k => c k j • mFourier k x) (uCont j c hc x) := by
  have h := (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_uCont j c hc)
  refine h.congr_fun fun k => ?_
  simp [ContinuousMap.evalCLM]

/-- **The identification**: the `L²` class of the continuous representative
is the campaign's synthesized field `synthT`. -/
theorem toLp_uCont (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) (hc2 : Summable fun k => ‖c k‖ ^ 2) :
    ContinuousMap.toLp (E := ℂ) 2 (volume : Measure T3) ℂ (uCont j c hc)
      = synthT j c := by
  rw [synthT_eq j hc2]
  have h1 := (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure T3) ℂ).hasSum
    (hasSum_uCont j c hc)
  have h2 : ∀ k : Fin 3 → ℤ,
      ContinuousMap.toLp (E := ℂ) 2 (volume : Measure T3) ℂ (c k j • mFourier k)
        = c k j • (mFourierBasis (d := Fin 3)) k := by
    intro k
    rw [map_smul, coe_mFourierBasis]
  have h1' : HasSum (fun k => c k j • (mFourierBasis (d := Fin 3)) k)
      (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure T3) ℂ (uCont j c hc)) :=
    h1.congr_fun fun k => (h2 k).symm
  exact h1'.unique (hasSum_synth j c hc2)

/-- **Coefficient recovery**: the continuous representative's Fourier
coefficients are the input coefficients. -/
theorem mFourierCoeff_uCont (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) (hc2 : Summable fun k => ‖c k‖ ^ 2)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (⇑(uCont j c hc)) k = c k j := by
  have hae : (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure T3) ℂ
      (uCont j c hc) : T3 → ℂ) =ᵐ[(volume : Measure T3)] ⇑(uCont j c hc) :=
    ContinuousMap.coeFn_toLp (volume : Measure T3) (uCont j c hc)
  rw [← c3_mFourierCoeff_congr_ae hae k, toLp_uCont j c hc hc2]
  exact mFourierCoeff_synthT j hc2 k

/-- **The sup-norm ℓ¹ bound** for the continuous representative
(`norm_tsum_le_tsum_norm` shape, for the capstone's joint-continuity
bookkeeping). -/
theorem norm_uCont_le (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) :
    ‖uCont j c hc‖ ≤ ∑' k, ‖c k‖ := by
  have hnorm : Summable fun k => ‖c k j • (mFourier (d := Fin 3) k)‖ := by
    refine (summable_component_norm j hc).congr fun k => ?_
    rw [norm_smul, mFourier_norm, mul_one]
  have hu : uCont j c hc = ∑' k, c k j • (mFourier (d := Fin 3) k) := rfl
  have h1 : ‖uCont j c hc‖ ≤ ∑' k, ‖c k j • (mFourier (d := Fin 3) k)‖ := by
    rw [hu]
    exact norm_tsum_le_tsum_norm hnorm
  have h2 : (∑' k, ‖c k j • (mFourier (d := Fin 3) k)‖) ≤ ∑' k, ‖c k‖ := by
    refine hnorm.tsum_le_tsum (fun k => ?_) hc
    rw [norm_smul, mFourier_norm, mul_one]
    exact PiLp.norm_apply_le (c k) j
  exact h1.trans h2

/-- **Pointwise reality**: under `RealField`, the continuous representative
takes real (conjugation-fixed) values at every point. -/
theorem uCont_real_apply {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖) (hreal : RealField c) (j : Fin 3) (x : T3) :
    (starRingEnd ℂ) (uCont j c hc x) = uCont j c hc x := by
  have h1 := uCont_apply j c hc x
  have h2 : HasSum (fun k => (starRingEnd ℂ) (c k j • mFourier k x))
      ((starRingEnd ℂ) (uCont j c hc x)) := h1.star
  have h3 : ∀ k : Fin 3 → ℤ, (starRingEnd ℂ) (c k j • mFourier k x)
      = c (-k) j • mFourier (-k) x := by
    intro k
    have hcj : c (-k) j = (starRingEnd ℂ) (c k j) := by
      rw [hreal k, c3_conjVel_apply]
    rw [smul_eq_mul, map_mul, smul_eq_mul, hcj, ← mFourier_neg]
  have h4 : HasSum (fun k => c (-k) j • mFourier (-k) x)
      ((starRingEnd ℂ) (uCont j c hc x)) :=
    h2.congr_fun fun k => (h3 k).symm
  have h5 : HasSum (fun k => c k j • mFourier k x)
      ((starRingEnd ℂ) (uCont j c hc x)) := by
    refine ((Equiv.neg (Fin 3 → ℤ)).hasSum_iff).mp ?_
    refine h4.congr_fun fun k => ?_
    simp
  exact h5.unique h1

end

end TheoremB
