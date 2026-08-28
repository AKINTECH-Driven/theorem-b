/-
# The leray-hopf vocabulary, restated (Tier 5 alignment record)

A faithful restatement of the leray-hopf project's L²σ vocabulary layer —
Torus3, haarTorus3, L2VF/L2C, torus3_mFourierBasis, mFourierCoeff3 with
Parseval, the component CLMs, DivFreeL2/divSymbol, the closed complete
L2Sigma, memH1Torus/h1EnergySq, viscousFormSq, stokesTestPairing,
DissipativeEvolution, and WeakFormNS — compiled against THIS repository's
Mathlib pin. Statements copied byte-similar from the read-only clone at
~/Documents/leray-hopf-ref (commit e704400f2fb2, v0.2.1, 2026-08-08), with
this header as the per-file provenance record; both projects pin the same
toolchain (v4.31.0-rc2) and the same Mathlib revision, so the restatement
carries no pin risk.

PURPOSE AND HONEST SCOPE. This file is the kernel-checked half of the
alignment the Tier-5 blueprint promised: it proves the leray-hopf solution
vocabulary ELABORATES IDENTICALLY over our pin, so the correspondences
noted in the campaign documents are checkable in one place:
- our spectral divergence-freeness (Σⱼ (kⱼ:ℂ)·û_j(k) = 0) is verbatim
  their `DivFreeL2` / `divSymbol = 0`;
- our band-limited test class mirrors their `isTest`/IsGalerkinTest slot;
- our spectral enstrophy differs from their `viscousFormSq`/`h1EnergySq`
  by the documented (2π)² and (1 + ·) weights.
The TYPE-LEVEL bridge — carrying our component-triple fields
(Fin 3 → Lp ℂ 2 volume) into their real vector-valued L2VF over
haarTorus3 (equal to volume only propositionally, via
`volume_torus3_eq_haarTorus3` below) and instantiating their WeakFormNS
with our flow — is deliberately NOT attempted here; it is the recorded
v2 interop, gated on the user's decision about a writable copy of the
clone. Nothing in this file is consumed by the campaign capstones.
-/
import Mathlib


open MeasureTheory

namespace LHRestate

abbrev Time := ℝ
abbrev Torus3 := UnitAddTorus (Fin 3)

noncomputable instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  IsProbabilityMeasure.mk UnitAddCircle.measure_univ

noncomputable example : MeasureSpace Torus3 := inferInstance
noncomputable example : IsProbabilityMeasure (volume : Measure Torus3) := inferInstance

abbrev VelocityValue := EuclideanSpace ℝ (Fin 3)

noncomputable def haarTorus3 : Measure Torus3 :=
  Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)

theorem volume_torus3_eq_haarTorus3 : (volume : Measure Torus3) = haarTorus3 := by
  have hfiber : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  rw [MeasureTheory.volume_pi]
  exact congrArg Measure.pi (funext fun _ => hfiber)

noncomputable abbrev L2VF := Lp VelocityValue 2 haarTorus3
noncomputable abbrev L2C := Lp ℂ 2 haarTorus3

noncomputable example : InnerProductSpace ℝ L2VF := inferInstance
noncomputable example : InnerProductSpace ℂ L2C := inferInstance

noncomputable def torus3_mFourierBasis : HilbertBasis (Fin 3 → ℤ) ℂ L2C :=
  UnitAddTorus.mFourierBasis

noncomputable def mFourierCoeff3 (f : L2C) (k : Fin 3 → ℤ) : ℂ :=
  torus3_mFourierBasis.repr f k

theorem L2C_norm_sq_eq_tsum_coeff_sq (f : L2C) :
    ‖f‖ ^ 2 = ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 f k‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (torus3_mFourierBasis.repr f)
  simp only [ENNReal.toReal_ofNat] at h
  have h2 : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ (2 : ℕ) := fun x => by
    rw [← Real.rpow_natCast x 2]; norm_num
  simp only [h2] at h
  rw [← torus3_mFourierBasis.repr.norm_map f]
  exact h

noncomputable def L2VF_projComponent (j : Fin 3) : L2VF →L[ℝ] Lp ℝ 2 haarTorus3 :=
  (EuclideanSpace.proj j (𝕜 := ℝ)).compLpL 2 haarTorus3

noncomputable def L2VF_projComponentC (j : Fin 3) : L2VF →L[ℝ] L2C :=
  (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 ∘L L2VF_projComponent j

noncomputable def L2VF_injectComponent (j : Fin 3) : Lp ℝ 2 haarTorus3 →L[ℝ] L2VF :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ))).compLpL 2 haarTorus3

def DivFreeL2 (u : L2VF) : Prop :=
  ∀ k : Fin 3 → ℤ,
    ∑ j : Fin 3, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k = 0

noncomputable def fourierCoeffCLM (k : Fin 3 → ℤ) : L2C →L[ℂ] ℂ :=
  innerSL ℂ (torus3_mFourierBasis k)

noncomputable def divSymbol (k : Fin 3 → ℤ) : L2VF →L[ℝ] ℂ :=
  ∑ j : Fin 3,
    (k j : ℂ) • ((fourierCoeffCLM k).restrictScalars ℝ ∘L L2VF_projComponentC j)

theorem fourierCoeffCLM_apply (k : Fin 3 → ℤ) (f : L2C) :
    fourierCoeffCLM k f = mFourierCoeff3 f k := by
  simp only [fourierCoeffCLM, innerSL_apply_apply, mFourierCoeff3,
    HilbertBasis.repr_apply_apply]

theorem divSymbol_apply (k : Fin 3 → ℤ) (u : L2VF) :
    divSymbol k u =
      ∑ j : Fin 3, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k := by
  simp only [divSymbol, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    fourierCoeffCLM_apply, smul_eq_mul]

noncomputable def L2Sigma : Submodule ℝ L2VF :=
  ⨅ k : Fin 3 → ℤ, (divSymbol k).ker

theorem mem_L2Sigma_iff (u : L2VF) : u ∈ L2Sigma ↔ DivFreeL2 u := by
  simp only [L2Sigma, Submodule.mem_iInf, LinearMap.mem_ker, DivFreeL2,
    ← divSymbol_apply, ContinuousLinearMap.coe_coe]

theorem isClosed_L2Sigma : IsClosed (L2Sigma : Set L2VF) := by
  simp only [L2Sigma, Submodule.coe_iInf]
  exact isClosed_iInter fun k => ContinuousLinearMap.isClosed_ker (divSymbol k)

noncomputable instance : CompleteSpace L2Sigma :=
  isClosed_L2Sigma.completeSpace_coe

/- Sobolev + energy functionals -/

noncomputable def memH1Torus (f : L2C) : Prop :=
  Summable (fun k : Fin 3 → ℤ =>
    (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2)

noncomputable def h1EnergySq (u : L2VF) : ℝ :=
  ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
    (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2

def memH1VF (u : L2VF) : Prop :=
  ∀ j : Fin 3, memH1Torus (L2VF_projComponentC j u)

noncomputable def viscousFormSq (ν : ℝ) (u : L2VF) : ℝ :=
  ν * ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
    (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2

noncomputable def stokesTestPairing (u w : L2VF) : ℝ :=
  ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
    ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) : ℝ) *
      (mFourierCoeff3 (L2VF_projComponentC j u) k *
        (starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j w) k))).re

/- The abstract weak form (EvolutionTriple.lean restated) -/

structure DissipativeEvolution where
  H : Type*
  instNACG : NormedAddCommGroup H
  instIPS : InnerProductSpace ℝ H
  instCS : CompleteSpace H
  reg : H → ℝ
  reg_nonneg : ∀ u, 0 ≤ reg u
  viscousForm : H → H → ℝ
  convForm : H → H → H → ℝ
  convForm_antisymm : ∀ u v w, convForm u v w = - convForm u w v
  isTest : H → Prop

def WeakFormNS (ν T : ℝ) (E : DissipativeEvolution) (u : Time → E.H) : Prop :=
  letI := E.instNACG
  letI := E.instIPS
  ∀ (ψ : Time → ℝ), HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T →
    ContDiff ℝ 1 ψ →
  ∀ (w : E.H), E.isTest w →
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) (u t) w) * deriv ψ t +
        ψ t * (ν * E.viscousForm (u t) w + E.convForm (u t) (u t) w)) = 0

end LHRestate
