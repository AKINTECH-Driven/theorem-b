/-
  TheoremB/CommunityClass.lean
  Tier 8b, waves W3 and W4 (Theorem B campaign, 9 Sep 2026): OUR COPY of the
  community solution class, the datum-side bridge into it (W3, part 1), and the
  inhabitation of the class by the eternal flow (W4, part 2, appended at the end
  of this file after the W3 probe section).

  WHAT IS DELIVERED HERE (W3, part 1).
  * `TheoremB.Community`: OUR COPY of the community definitions (two `def`s,
    `divergence` and `IsOnePeriodic`, and the six structures
    `InitialVelocityCondition`, `InitialVelocityConditionPeriodic`,
    `ForceCondition`, `ForceConditionPeriodic`,
    `NavierStokesExistenceAndSmoothness`,
    `NavierStokesExistenceAndSmoothnessPeriodic`) in the wording of
    google-deepmind/formal-conjectures as adapted in OpenAI's Comparator file
    (`ComparatorChallenges/NavierStokes.lean`).  DIFF RECORD (binding, house
    rule of `context/rung10-tier8-blueprint.md` section 2a): declaration by
    declaration, comments stripped, our block is IDENTICAL to the upstream
    file EXCEPT in exactly two places, the namespace (`NavierStokes` upstream,
    `TheoremB.Community` here) and the divergence notation (a global
    `@[inherit_doc] notation "∇⬝"` upstream, a `local notation "∇⬝"` here).
    A claim that the namespace is the sole difference would be false and is
    not made.  The upstream half of this record (the namespace name and the
    global notation) is inherited from the blueprint, since no copy of the
    upstream file is kept on this machine; the local half is measured against
    the persisted `ProbeOpenAIStatement.lean`.  The external file is not
    imported into the gated tree; this block is a copy of it.
    [Superseded 13 Sep 2026: the upstream file was fetched and compared, comments
    stripped (D27 in `context/rung12-tier9c-blueprint.md`); the two differences
    recorded above are the only ones in the copied definitions and structures.]
  * The bridge objects `vReal`, `pReal`, `u₀Real` (position before time, as
    the class has it; the factor `2π` on the pressure is the clock change of
    section 2b, `τ = t/(2π)`).
  * The operator bridges `fderiv_uLift_single`, `laplacian_uLift`,
    `fderiv_pLift_single`: the first Fréchet derivative of a lifted character
    series along a coordinate vector is the `2πi·kᵢ`-twisted series, and the
    Laplacian is the `-(2π)²‖k‖²`-weighted series.  Route: the line derivative
    `s ↦ f (x + s·eᵢ)` at `s = 0` is `fderiv f x eᵢ`, and the line series is
    differentiated term by term (`hasDerivAt_tsum`, majorant
    `2π‖freq k‖‖a k‖`).
  * The reality lemmas `convFull_neg_of_realField`,
    `pressureCoeff_neg_of_realField`, `im_uLift_eq_zero`, `im_pLift_eq_zero`
    (a real coefficient field has a real lift and a real pressure: the series
    is its own conjugate after pairing `k` with `-k`), the periodicity lemmas
    `isOnePeriodic_uLift`, `isOnePeriodic_pLift`, the divergence lemma
    `divergence_uReal_eq_zero` (the trace divergence is the coordinate sum of
    directional derivatives, and `DivFree` kills every mode), and the two
    datum-side conditions `initialVelocityConditionPeriodic_u₀Real`,
    `forceConditionPeriodic_zero` (force spelled `(f := 0)` as upstream;
    `force_zero_spelling_rfl` records that `fun _ _ => 0` is the same term).
  * A registered probe section `W3Probe` (non-frozen, section 6b of the
    blueprint): the nonzero shear datum `testDatum ε` meets every capstone
    hypothesis (`exists_nonzero_admissible_datum`), its lift is nonzero
    (`uLift_testDatum_zero`, `u₀Real_testDatum_ne_zero`), the rest pair is not
    a witness of the class for it (`rest_pair_fails_class`), and the
    time-constant coefficient flow fails the mode equation
    (`const_flow_fails_ode`).

  WHAT IS DELIVERED HERE (W4, part 2; section 8 of this file).
  * `hasDerivWithinAt_charSum_zero` (frozen): the right derivative at `t = 0`,
    within `Ici 0`, of the torus character sum `s ↦ Σ_k c_s(k)_j e_k(x)`, with
    the spectral right-hand side as its value.  Route: the W2 within-convex
    engine `hasDerivWithinAt_tsum_of_convex` at `E = ℝ` on `Ico 0 b`, the
    per-mode derivatives being the chain's endpoint derivative at `0` and the
    mode equation on `t > 0`, the majorant being the window majorant of the
    first chain element; then `mono_of_mem_nhdsWithin`.
  * `derivWithin_vReal_Ici` (frozen): the within-derivative on `Ici 0` of the
    real velocity in the community clock is `2π` times the real part of the
    lift of the spectral right-hand side at `2πτ`.  Route: the clock
    `HasDerivWithinAt.scomp_of_eq`, the real part through `Complex.reCLM`, the
    packing through `hasDerivWithinAt_pi` and `PiLp.continuousLinearEquiv`, and
    `HasDerivWithinAt.derivWithin` with the unique differentials of `Ici 0`.
  * `theorem_B_community_periodic_flow` (frozen, the pinned capstone): the
    twenty classical clauses of `theorem_B_smooth_classical_eq`, verbatim, plus
    clause 21: OUR COPY of the class
    `NavierStokesExistenceAndSmoothnessPeriodic (ν/(2π)) (u₀Real c₀) 0 (vReal c) (pReal c)`
    is inhabited by the eternal flow, at `f = 0`.  Route: the component
    identity `navier_stokes_component_spectral` (non-frozen; the spectral
    right-hand side decomposed by clause 18 into viscous, convective and
    pressure series, the viscous series identified with the Laplacian bridge,
    the convective series with clause 19 through the reality of the factors,
    the pressure series with the pressure bridge, and the `2π` arithmetic
    `2π·ν/(2π)² = ν/(2π)`, `2π·(1/(2π)) = 1`), the operator reductions
    `gradient_apply_eq_fderiv_single`, `fderiv_apply_expand`,
    `laplacian_apply_component`, `laplacian_re` (Mathlib-side), the seam
    `velocity_smooth_of_clause24` / `pressure_smooth_of_clause25` (clauses 24
    and 25 composed with `Complex.reCLM` and the clock CLM `(x, τ) ↦ (x, 2πτ)`),
    `divergence_uReal_eq_zero`, `chain_one_eq` (the first chain element is the
    spectral right-hand side), and the two frozen lemmas above.
  * `theorem_B_community_periodic` (frozen, the bare capstone, the community's
    own shape): the composition of the pinned capstone with the two datum-side
    conditions at `ν := 2π·ν'` (`mul_div_cancel_left₀`).
  * A registered probe section `W4Probe` (non-frozen, section 6b): for every
    `ν' > 0` the bare capstone fires on a NONZERO admissible datum
    (`capstones_fire_on_nonzero_datum`, and with the datum explicit,
    `capstone_fires_on_testDatum`); the rest velocity is not a witness whenever
    the real datum is nonzero (`rest_state_not_witness_of_ne_zero`,
    `rest_state_not_witness_for_nonzero`); and under `velocity_smooth` the
    class's `derivWithin` and `fderiv` are genuine derivatives, not junk values
    (`differentiableWithinAt_time_slice_of_velocity_smooth`,
    `differentiableAt_space_slice_of_velocity_smooth`).  The time-constant
    witness `v x t := u₀Real c₀ x` for the bare class on the shear datum is
    EXCLUDED by the registered probe `TimeConstantWitness.const_witness_fails`
    (section 10 of this file, the blueprint's former NOT-PROBED item): for every
    `ν' ≠ 0` and every pressure it fails the class's `navier_stokes` clause,
    through `laplacian_uLift`, `fderiv_uLift_single` and one-periodicity of
    the pressure; `ν' ≠ 0` is necessary (at `ν' = 0` the stationary shear with
    `p = 0` is an Euler solution).

  HONEST SCOPE (binding wording, section 7 of the blueprint).
  * The upstream file carries the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown
    statement `navier_stokes_breakdown_periodic`.  The bare capstone
    `theorem_B_community_periodic` is exactly the positive statement's
    CONCLUSION restricted to the data class `u₀ = u₀Real c₀` with
    `κ·en c₀·ens c₀ < (2πν')⁴` at `f = 0`; it says nothing about the positive
    statement for general data and nothing about the breakdown statement.  Both
    upstream `sorry`s are untouched.  The class is inhabited for trap-class
    data at `f = 0` only and says nothing beyond that.
  * OUR COPY of the community class is inhabited; the external file is not
    imported.
  * Existence only: the class has no uniqueness clause.  Uniqueness of the
    coefficient flow behind `vReal c` is `theorem_B_unique`, whose hypothesis
    set is exactly clauses 1-7 of the pinned form.
  * The rest state is not a witness for nonzero data
    (`W3Probe.rest_pair_fails_class`); at `c₀ = 0` it is, as it must be.
  * `κ` is of explicit form, exported as a compiled existential; the window
    constants of the time-derivative chain and the majorants (`WindowL1`, the
    `u`-majorants of `hasDerivWithinAt_charSum_zero`) are UNTRACKED
    existentials.  No numeric value of any constant is claimed.
  * The real-part bridge and the clock change are textbook; nothing here is
    new mathematics.  Smoothness means `C^∞` with `∞ = (⊤ : ℕ∞)`; analyticity
    is not claimed.  Priority is not claimed for anything.  The machine-checked
    Navier-Stokes work this file sits beside is named in the announcement and
    the README (uda-lab/leray-hopf, HeliCorgi's ns-mns2-flowmap-bridge, Miller,
    OpenAI's forced-breakdown certificate, Alpöge and Buckmaster); none of it
    is composed with, reproduced by, or superseded by anything here.
  * Private declarations of frozen files (PeriodicLift's term lemmas,
    NSGalerkin/RealityProp's `conjVel`/`dotR` algebra, TimeSmooth's
    `norm_convTerm_le`, ForcedProbe's pair-mode datum) are CLONED here with a
    `cc` prefix, never un-privated; the W4 probe section uses the W3 probe
    section's private datum lemmas within this same file.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.JointSmooth

open Set Filter Topology MeasureTheory InnerProductSpace UnitAddTorus
open scoped ContDiff Laplacian
local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace TheoremB

/-
The definitions and structures of this section are copied from the Navier-Stokes file of
google-deepmind/formal-conjectures (file content as of commit
b9fc95eb75b048b195f3d01af4315ad3437ab157, 11 Sep 2026), whose header reads:

Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Only the two definitions and six structures used here are copied; the rest of the upstream
file (its other lemmas, structures and statements) is not. Modified here (2026): namespace
`TheoremB.Community` in place of `NavierStokes`, the divergence notation made `local` (its
`@[inherit_doc]` attribute dropped), comments and docstrings removed. Everything outside this
section is original to this repository.
-/
namespace Community
variable {n : ℕ}
noncomputable
def divergence (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ := (fderiv ℝ v x).trace ℝ (ℝ^n)

local notation "∇⬝" => divergence


def IsOnePeriodic {α : Sort*} (f : ℝ^n → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

structure InitialVelocityCondition (u₀ : ℝ^n → ℝ^n) : Prop where
  div_free : ∀ x, ∇⬝ u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

structure InitialVelocityConditionPeriodic (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  isOnePeriodic : IsOnePeriodic u₀

structure ForceCondition (f : ℝ^n → ℝ → ℝ^n) : Prop where
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

structure ForceConditionPeriodic (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  isOnePeriodic : ∀ t ≥ 0, IsOnePeriodic (f · t)
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K

structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop where
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)

end Community

open Community

noncomputable section

/-! ## 1. The force-zero spelling and the zero force -/

/-- The upstream force `(f := 0)` is the Pi zero; `fun _ _ => 0` is the same term. -/
theorem force_zero_spelling_rfl :
    (fun (_ : ℝ³) (_ : ℝ) => (0 : ℝ³)) = (0 : ℝ³ → ℝ → ℝ³) := rfl

/-- The zero force meets `ForceConditionPeriodic`: constant, periodic, and every
iterated derivative vanishes (constant `C := 0` for every order and every decay
exponent). -/
theorem forceConditionPeriodic_zero :
    ForceConditionPeriodic (n := 3) (f := 0) := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · exact contDiffOn_const
  · intro t _ x i; rfl
  · intro m K
    refine ⟨0, fun x t ht => ?_⟩
    have h0 : (↿(0 : ℝ³ → ℝ → ℝ³)) = fun _ => (0 : ℝ³) := rfl
    rw [h0, iteratedFDerivWithin_fun_zero]
    simp

/-! ## 2. The bridge objects (position before time, as the class has it) -/

/-- The real velocity field of a coefficient flow in the community clock
`τ = t/(2π)`: the real part of the lift of `c (2πτ)`, packed into `ℝ³`. -/
noncomputable def vReal (c : ℝ → (Fin 3 → ℤ) → Vel) (x : ℝ³) (τ : ℝ) : ℝ³ :=
  WithLp.toLp 2 fun j : Fin 3 => (uLift j (c (2 * Real.pi * τ)) x).re

/-- The real pressure in the community clock; the factor `2π` is the clock change. -/
noncomputable def pReal (c : ℝ → (Fin 3 → ℤ) → Vel) (x : ℝ³) (τ : ℝ) : ℝ :=
  (2 * Real.pi) * (pLift (c (2 * Real.pi * τ)) x).re

/-- The real initial datum: the real part of the lift of `c₀`, packed into `ℝ³`. -/
noncomputable def u₀Real (c₀ : (Fin 3 → ℤ) → Vel) : ℝ³ → ℝ³ :=
  fun x => WithLp.toLp 2 fun j : Fin 3 => (uLift j c₀ x).re

/-! ## 3. Periodicity -/

/-- The Euclidean image of the lattice unit vector is the Euclidean unit vector. -/
lemma freq_single (i : Fin 3) : freq (Pi.single i 1) = EuclideanSpace.single i 1 := by
  ext l
  simp [freq, Pi.single_apply, PiLp.single_apply]

/-- The lift is `1`-periodic in every coordinate (`uLift_periodic` at `g := Pi.single i 1`). -/
theorem isOnePeriodic_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) :
    IsOnePeriodic (uLift j c) := by
  intro x i
  rw [← freq_single i]
  exact uLift_periodic j c _ x

/-- Integer coordinates die on the unit circle (clone of PeriodicLift's private lemma). -/
private lemma cc_coe_int_addCircle (g : ℤ) : ((g : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨g, by simp [zsmul_eq_mul]⟩

/-- ℤ³-periodicity of the pressure lift (the route of `uLift_periodic`: the two
series agree term by term, no summability needed). -/
theorem pLift_periodic (c : (Fin 3 → ℤ) → Vel) (g : Fin 3 → ℤ) (x : ℝ³) :
    pLift c (x + freq g) = pLift c x := by
  have hcoord : ∀ i : Fin 3,
      (((x + freq g) i : ℝ) : AddCircle (1 : ℝ)) = ((x i : ℝ) : AddCircle (1 : ℝ)) := by
    intro i
    have h1 : ((x + freq g) i : ℝ) = x i + (g i : ℝ) := rfl
    rw [h1, AddCircle.coe_add, cc_coe_int_addCircle (g i), add_zero]
  show (∑' k : Fin 3 → ℤ, pressureCoeff c k *
      ∏ i : Fin 3, fourier (k i) (((x + freq g) i : ℝ) : AddCircle (1 : ℝ)))
      = ∑' k : Fin 3 → ℤ, pressureCoeff c k *
          ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))
  exact tsum_congr fun k =>
    congrArg (pressureCoeff c k * ·)
      (Finset.prod_congr rfl fun i _ => congrArg (fourier (k i)) (hcoord i))

/-- The pressure lift is `1`-periodic in every coordinate. -/
theorem isOnePeriodic_pLift (c : (Fin 3 → ℤ) → Vel) :
    IsOnePeriodic (pLift c) := by
  intro x i
  rw [← freq_single i]
  exact pLift_periodic c _ x

/-! ## 4. Reality: a real coefficient field has a real lift and a real pressure

The `conjVel`/`dotR` algebra is cloned from the private sections of
NSGalerkin.lean / RealityProp.lean, and `norm_convTerm_le` from TimeSmooth.lean. -/

private lemma cc_conjVel_smul (z : ℂ) (v : Vel) :
    conjVel (z • v) = (starRingEnd ℂ) z • conjVel v := by
  ext j
  simp [conjVel]

private lemma cc_conjVel_neg (v : Vel) : conjVel (-v) = -conjVel v := by
  ext j
  simp [conjVel]

private lemma cc_conj_dotR (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (dotR v r) = dotR (conjVel v) r := by
  simp only [dotR]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1

private lemma cc_dotR_neg_right (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR v (-r) = -dotR v r := by
  simp [dotR, mul_neg, Finset.sum_neg_distrib]

private lemma cc_norm_convTerm_le (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    ‖(Complex.I * dotR v r) • w‖ ≤ ‖v‖ * (‖r‖ * ‖w‖) := by
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotR v r‖ * ‖w‖ ≤ (‖r‖ * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
    _ = ‖v‖ * (‖r‖ * ‖w‖) := by ring

/-- **Reality of the full convection**: for a real coefficient field the convection
at `-k` is the conjugate of the convection at `k` (reindex the defining series by
`l ↦ -l`, `freq_neg`, and `conjVel` through the ℝ-linear map `conjVelL`; the
summability certificate is discrete Young `conv_l1_summable_le'`). -/
theorem convFull_neg_of_realField {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (k : Fin 3 → ℤ) :
    convFull c (-k) = conjVel (convFull c k) := by
  have hterm : ∀ l : Fin 3 → ℤ,
      (Complex.I * dotR (c (-l)) (freq (-k - -l))) • c (-k - -l)
        = conjVel ((Complex.I * dotR (c l) (freq (k - l))) • c (k - l)) := by
    intro l
    have e1 : -k - -l = -(k - l) := by abel
    rw [e1, freq_neg, hreal l, hreal (k - l), cc_conjVel_smul, cc_dotR_neg_right,
      ← cc_conj_dotR]
    congr 1
    rw [map_mul, Complex.conj_I]
    ring
  have hsum : Summable fun l => (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) := by
    obtain ⟨hmaj, -⟩ := conv_l1_summable_le' h0 h1 (fun _ => norm_nonneg _)
      (fun _ => by positivity) k
    exact Summable.of_norm_bounded hmaj (fun l => cc_norm_convTerm_le _ _ _)
  have hmap : conjVel (∑' l, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l))
      = ∑' l, conjVel ((Complex.I * dotR (c l) (freq (k - l))) • c (k - l)) := by
    have := conjVelL.map_tsum hsum
    simpa only [conjVelL_apply] using this
  unfold convFull
  rw [cc_conjVel_neg, hmap,
    ← (Equiv.neg (Fin 3 → ℤ)).tsum_eq
      (fun l => (Complex.I * dotR (c l) (freq (-k - l))) • c (-k - l))]
  simp only [Equiv.neg_apply]
  rw [tsum_congr hterm]

/-- **Reality of the spectral pressure**: `p̂_{-k} = conj p̂_k` for a real field. -/
theorem pressureCoeff_neg_of_realField {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (k : Fin 3 → ℤ) :
    pressureCoeff c (-k) = (starRingEnd ℂ) (pressureCoeff c k) := by
  unfold pressureCoeff
  rw [convFull_neg_of_realField hreal h0 h1 k, freq_neg, norm_neg, cc_dotR_neg_right,
    ← cc_conj_dotR]
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

set_option linter.unusedVariables false in
/-- **The lift of a real field is real**: the series is its own conjugate after the
reindexing `k ↦ -k` (`fourier_neg`, `RealField`); no summability is used (the frozen
`h0` is not needed), the conjugation is the ℝ-linear equivalence `Complex.conjCLE`. -/
theorem im_uLift_eq_zero {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖) (j : Fin 3) (x : ℝ³) :
    (uLift j c x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  show (starRingEnd ℂ) (∑' k : Fin 3 → ℤ,
      c k j • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
      = ∑' k : Fin 3 → ℤ, c k j • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))
  have hmap : (starRingEnd ℂ) (∑' k : Fin 3 → ℤ,
        c k j • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
      = ∑' k : Fin 3 → ℤ, (starRingEnd ℂ)
          (c k j • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) := by
    have := Complex.conjCLE.map_tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
      (f := fun k : Fin 3 → ℤ =>
        c k j • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
    simpa only [Complex.conjCLE_apply] using this
  rw [hmap]
  have hterm : ∀ k : Fin 3 → ℤ,
      (starRingEnd ℂ) (c k j • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
        = c (-k) j • ∏ l : Fin 3, fourier ((-k) l) ((x l : ℝ) : AddCircle (1 : ℝ)) := by
    intro k
    rw [hreal k, smul_eq_mul, smul_eq_mul, map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun l _ => by rw [Pi.neg_apply, fourier_neg]
  rw [tsum_congr hterm]
  exact (Equiv.neg (Fin 3 → ℤ)).tsum_eq
    (fun k : Fin 3 → ℤ => c k j • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))

/-- **The pressure lift of a real field is real** (the same pairing, with
`pressureCoeff_neg_of_realField`). -/
theorem im_pLift_eq_zero {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (x : ℝ³) :
    (pLift c x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  show (starRingEnd ℂ) (∑' k : Fin 3 → ℤ,
      pressureCoeff c k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
      = ∑' k : Fin 3 → ℤ,
          pressureCoeff c k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))
  have hmap : (starRingEnd ℂ) (∑' k : Fin 3 → ℤ,
        pressureCoeff c k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
      = ∑' k : Fin 3 → ℤ, (starRingEnd ℂ)
          (pressureCoeff c k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) := by
    have := Complex.conjCLE.map_tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
      (f := fun k : Fin 3 → ℤ =>
        pressureCoeff c k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
    simpa only [Complex.conjCLE_apply] using this
  rw [hmap]
  have hterm : ∀ k : Fin 3 → ℤ,
      (starRingEnd ℂ)
          (pressureCoeff c k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
        = pressureCoeff c (-k) *
            ∏ l : Fin 3, fourier ((-k) l) ((x l : ℝ) : AddCircle (1 : ℝ)) := by
    intro k
    rw [pressureCoeff_neg_of_realField hreal h0 h1 k, map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun l _ => by rw [Pi.neg_apply, fourier_neg]
  rw [tsum_congr hterm]
  exact (Equiv.neg (Fin 3 → ℤ)).tsum_eq
    (fun k : Fin 3 → ℤ =>
      pressureCoeff c k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))

/-! ## 5. The operator bridges

The character `x ↦ ∏ᵢ fourier kᵢ xᵢ` is `cexp(2πi⟨freq k, x⟩)` (clone of the private
`char_eq_comp` of JointSmooth.lean), so along the coordinate line `x + s·eᵢ` every
term is `a_k · char_k(x) · cexp(2πi kᵢ s)`.  The series is differentiated term by
term (`hasDerivAt_tsum`, majorant `2π‖freq k‖‖a k‖`) and identified with the Fréchet
derivative along `eᵢ` through the line-derivative identity. -/

private lemma cc_char_eq_comp (k : Fin 3 → ℤ) :
    (fun x : EuclideanSpace ℝ (Fin 3) =>
        ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)))
      = (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
          (innerSL ℝ (freq k)) := by
  funext x
  show (∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)))
      = Complex.exp ((2 * Real.pi * Complex.I) * ((inner ℝ (freq k) x : ℝ) : ℂ))
  have hinner : inner ℝ (freq k) x = ∑ i, (k i : ℝ) * x i := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
  rw [hinner]
  have h1 : ∀ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * (k i) * (x i) / 1) := fun i =>
    fourier_coe_apply
  rw [Finset.prod_congr rfl fun i _ => h1 i, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The character along the coordinate line `x + s·eᵢ`. -/
lemma char_line (k : Fin 3 → ℤ) (x : ℝ³) (i : Fin 3) (s : ℝ) :
    (∏ l : Fin 3, fourier (k l)
        (((x + s • EuclideanSpace.single i 1 : ℝ³) l : ℝ) : AddCircle (1 : ℝ)))
      = (∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
        * Complex.exp ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * s) := by
  have h1 := congrFun (cc_char_eq_comp k) (x + s • EuclideanSpace.single i 1)
  have h2 := congrFun (cc_char_eq_comp k) x
  simp only [Function.comp, innerSL_apply_apply] at h1 h2
  rw [h1, h2, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right,
    ← Complex.exp_add]
  congr 1
  simp only [starRingEnd_apply, star_trivial]
  have hk : ((freq k).ofLp i : ℝ) = (k i : ℝ) := rfl
  rw [hk]
  push_cast
  ring

/-- 1-D: derivative of `t ↦ cexp (a·t)` along ℝ (clone of PeriodicLift's private lemma). -/
private lemma cc_hasDerivAt_cexp_mul_real (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (a * s)) (a * Complex.exp (a * t)) t := by
  have hin : HasDerivAt (fun w : ℂ => a * w) a (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul a
  have h := (Complex.hasDerivAt_exp (a * (t : ℂ))).comp (t : ℂ) hin
  simpa [mul_comm] using h.comp_ofReal

/-- Per-term derivative along the coordinate line. -/
lemma hasDerivAt_char_line_term (a : ℂ) (k : Fin 3 → ℤ) (x : ℝ³) (i : Fin 3) (s : ℝ) :
    HasDerivAt
      (fun s : ℝ => a * ∏ l : Fin 3, fourier (k l)
        (((x + s • EuclideanSpace.single i 1 : ℝ³) l : ℝ) : AddCircle (1 : ℝ)))
      ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * a
        * (∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
        * Complex.exp ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * s)) s := by
  have hfun : (fun s : ℝ => a * ∏ l : Fin 3, fourier (k l)
        (((x + s • EuclideanSpace.single i 1 : ℝ³) l : ℝ) : AddCircle (1 : ℝ)))
      = fun s : ℝ => (a * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
          * Complex.exp ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * s) := by
    funext s
    rw [char_line]
    ring
  rw [hfun]
  have h := (cc_hasDerivAt_cexp_mul_real (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) s).const_mul
    (a * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
  refine h.congr_deriv ?_
  ring

/-- The character has unit modulus (the value of `mFourier` at a point is
definitionally the product of `fourier` values). -/
lemma norm_char_eq_one (k : Fin 3 → ℤ) (x : ℝ³) :
    ‖∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))‖ = 1 :=
  norm_mFourier_apply k (fun l => ((x l : ℝ) : AddCircle (1 : ℝ)))

lemma norm_twist_coeff (i : Fin 3) (k : Fin 3 → ℤ) :
    ‖(2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ))‖ = 2 * Real.pi * |(k i : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
  have e1 : ‖(2 : ℂ)‖ = 2 := by simp
  have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
  have e4 : ‖((k i : ℤ) : ℂ)‖ = |(k i : ℝ)| := by simp
  rw [e1, e2, e4]
  ring

lemma norm_cexp_twist (i : Fin 3) (k : Fin 3 → ℤ) (s : ℝ) :
    ‖Complex.exp ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * s)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The twisted term is bounded by `2π‖freq k‖‖a‖` (coordinate bound `|kᵢ| ≤ ‖freq k‖`). -/
lemma norm_twist_term_le (i : Fin 3) (a : ℂ) (k : Fin 3 → ℤ) (x : ℝ³) :
    ‖(2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * a
        * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))‖
      ≤ 2 * Real.pi * (‖freq k‖ * ‖a‖) := by
  rw [norm_mul, norm_mul, norm_char_eq_one, mul_one, norm_twist_coeff]
  have hπ : (0:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  calc 2 * Real.pi * |(k i : ℝ)| * ‖a‖
      ≤ 2 * Real.pi * ‖freq k‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_coord_le_norm_freq k i) hπ) (norm_nonneg _)
    _ = 2 * Real.pi * (‖freq k‖ * ‖a‖) := by ring

/-- The same bound with the line factor `cexp(2πi kᵢ s)` (unit modulus). -/
lemma norm_twist_term_line_le (i : Fin 3) (a : ℂ) (k : Fin 3 → ℤ) (x : ℝ³) (s : ℝ) :
    ‖(2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * a
        * (∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
        * Complex.exp ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * s)‖
      ≤ 2 * Real.pi * (‖freq k‖ * ‖a‖) := by
  rw [norm_mul, norm_cexp_twist, mul_one]
  exact norm_twist_term_le i a k x

/-- The twisted series is summable given one weighted ℓ¹ order. -/
lemma summable_twist_term (i : Fin 3) (a : (Fin 3 → ℤ) → ℂ)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖a k‖) (x : ℝ³) :
    Summable fun k : Fin 3 → ℤ => (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * a k
      * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) :=
  Summable.of_norm_bounded (h1.mul_left (2 * Real.pi)) fun k => norm_twist_term_le i (a k) k x

/-- **Term-wise differentiation of a character series along a coordinate line.** -/
theorem hasDerivAt_charSeries_line (i : Fin 3) (a : (Fin 3 → ℤ) → ℂ)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖a k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖a k‖) (x : ℝ³) :
    HasDerivAt
      (fun s : ℝ => ∑' k : Fin 3 → ℤ, a k * ∏ l : Fin 3, fourier (k l)
        (((x + s • EuclideanSpace.single i 1 : ℝ³) l : ℝ) : AddCircle (1 : ℝ)))
      (∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * a k
        * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) 0 := by
  have hg0 : Summable fun k : Fin 3 → ℤ => a k * ∏ l : Fin 3, fourier (k l)
      (((x + (0:ℝ) • EuclideanSpace.single i 1 : ℝ³) l : ℝ) : AddCircle (1 : ℝ)) := by
    refine Summable.of_norm_bounded h0 fun k => ?_
    rw [norm_mul, norm_char_eq_one, mul_one]
  have h := hasDerivAt_tsum (u := fun k : Fin 3 → ℤ => 2 * Real.pi * (‖freq k‖ * ‖a k‖))
    (g := fun (k : Fin 3 → ℤ) (s : ℝ) => a k * ∏ l : Fin 3, fourier (k l)
      (((x + s • EuclideanSpace.single i 1 : ℝ³) l : ℝ) : AddCircle (1 : ℝ)))
    (g' := fun (k : Fin 3 → ℤ) (s : ℝ) => (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * a k
        * (∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
        * Complex.exp ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * s))
    (y₀ := 0) (h1.mul_left (2 * Real.pi))
    (fun k s => hasDerivAt_char_line_term (a k) k x i s)
    (fun k s => norm_twist_term_line_le i (a k) k x s) hg0 0
  refine h.congr_deriv (tsum_congr fun k => ?_)
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- The line-derivative identity: `fderiv f x v` is the derivative at `0` of
`s ↦ f (x + s·v)` (recon C5). -/
theorem hasDerivAt_line_of_differentiableAt {f : ℝ³ → ℂ} {x v : ℝ³}
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f x v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    simpa using this
  have hfx : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact hfx.comp_hasDerivAt (0:ℝ) hl

/-- **The first-order bridge for a scalar character series**: the Fréchet derivative
along `eᵢ` is the `2πi kᵢ`-twisted series (differentiability is a hypothesis, to be
supplied by `contDiff_uLift` / `contDiff_charSeries`). -/
theorem fderiv_charSeries_single (i : Fin 3) (a : (Fin 3 → ℤ) → ℂ)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖a k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖a k‖) (x : ℝ³)
    (hd : DifferentiableAt ℝ
      (fun y : ℝ³ => ∑' k : Fin 3 → ℤ, a k * ∏ l : Fin 3,
        fourier (k l) ((y l : ℝ) : AddCircle (1 : ℝ))) x) :
    fderiv ℝ (fun y : ℝ³ => ∑' k : Fin 3 → ℤ, a k * ∏ l : Fin 3,
        fourier (k l) ((y l : ℝ) : AddCircle (1 : ℝ))) x (EuclideanSpace.single i 1)
      = ∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * a k
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) :=
  (hasDerivAt_line_of_differentiableAt (v := EuclideanSpace.single i 1) hd).unique
    (hasDerivAt_charSeries_line i a h0 h1 x)

/-- `C^p` of a scalar character series from weighted ℓ¹ certificates at every order
`q ≤ p` (`contDiff_tsum` against `(2π‖freq k‖)^q‖a k‖`, via JointSmooth's
`contDiff_char` / `norm_iteratedFDeriv_char_le`). -/
theorem contDiff_charSeries (a : (Fin 3 → ℤ) → ℂ) (p : ℕ)
    (ha : ∀ q : ℕ, q ≤ p → Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ q * ‖a k‖) :
    ContDiff ℝ (p : ℕ∞) fun x : ℝ³ =>
      ∑' k : Fin 3 → ℤ, a k * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) := by
  refine contDiff_tsum
    (v := fun (q : ℕ) (k : Fin 3 → ℤ) => (2 * Real.pi) ^ q * (‖freq k‖ ^ q * ‖a k‖))
    (fun k => ?_) (fun q hq => ?_) (fun q k x _ => ?_)
  · exact ((contDiff_char k).const_smul (a k)).of_le (by exact_mod_cast le_top)
  · have hq' : q ≤ p := by exact_mod_cast hq
    exact (ha q hq').mul_left ((2 * Real.pi) ^ q)
  · have hpull : iteratedFDeriv ℝ q
        (fun x : ℝ³ => a k • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) x
        = a k • iteratedFDeriv ℝ q
            (fun x : ℝ³ => ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) x :=
      iteratedFDeriv_const_smul_apply'
        (((contDiff_char k).of_le (by exact_mod_cast le_top)).contDiffAt)
    show ‖iteratedFDeriv ℝ q
        (fun x : ℝ³ => a k • ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) x‖ ≤ _
    rw [hpull, norm_smul]
    calc ‖a k‖ * ‖iteratedFDeriv ℝ q
          (fun x : ℝ³ => ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) x‖
        ≤ ‖a k‖ * (2 * Real.pi * ‖freq k‖) ^ q :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_char_le k q x) (norm_nonneg _)
      _ = (2 * Real.pi) ^ q * (‖freq k‖ ^ q * ‖a k‖) := by rw [mul_pow]; ring

/-- The lift is the scalar character series of its `j`-th coefficients (by `rfl`;
`•` on `ℂ` is `*`). -/
lemma uLift_eq_charSeries (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) :
    uLift j c = fun x : ℝ³ =>
      ∑' k : Fin 3 → ℤ, c k j * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) :=
  rfl

/-- The pressure lift is the scalar character series of `pressureCoeff c` (by `rfl`). -/
lemma pLift_eq_charSeries (c : (Fin 3 → ℤ) → Vel) :
    pLift c = fun x : ℝ³ =>
      ∑' k : Fin 3 → ℤ, pressureCoeff c k *
        ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) :=
  rfl

/-- ℓ¹ of the `j`-th component from ℓ¹ of the family. -/
lemma summable_norm_component (j : Fin 3) {c : (Fin 3 → ℤ) → Vel}
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖) :
    Summable fun k : Fin 3 → ℤ => ‖c k j‖ :=
  h0.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => PiLp.norm_apply_le (c k) j)

/-- Weighted ℓ¹ of the `j`-th component from weighted ℓ¹ of the family. -/
lemma summable_freq_norm_component (j : Fin 3) {c : (Fin 3 → ℤ) → Vel}
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) :
    Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k j‖ :=
  h1.of_nonneg_of_le (fun _ => by positivity)
    (fun k => mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (c k) j) (norm_nonneg _))

/-- `C¹` of the lift from ℓ¹ and one weighted ℓ¹ order. -/
lemma contDiff_one_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) :
    ContDiff ℝ 1 (uLift j c) := by
  have h := contDiff_uLift j c 1 fun q hq => by
    interval_cases q
    · simpa using h0
    · simpa using h1
  exact_mod_cast h

/-- `C²` of the lift from ℓ¹ and two weighted ℓ¹ orders. -/
lemma contDiff_two_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖)
    (h2 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ 2 * ‖c k‖) :
    ContDiff ℝ 2 (uLift j c) := by
  have h := contDiff_uLift j c 2 fun q hq => by
    interval_cases q
    · simpa using h0
    · simpa using h1
    · exact h2
  exact_mod_cast h

/-- `C¹` of the pressure lift from ℓ¹ and one weighted ℓ¹ order of `pressureCoeff`. -/
lemma contDiff_one_pLift (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖pressureCoeff c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖pressureCoeff c k‖) :
    ContDiff ℝ 1 (pLift c) := by
  rw [pLift_eq_charSeries]
  have h := contDiff_charSeries (pressureCoeff c) 1 fun q hq => by
    interval_cases q
    · simpa using h0
    · simpa using h1
  exact_mod_cast h

/-- **The first-order bridge for the velocity lift**: `∂ᵢ u_j` is the
`2πi kᵢ`-twisted character series. -/
theorem fderiv_uLift_single (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (x : ℝ³) :
    fderiv ℝ (uLift j c) x (EuclideanSpace.single i 1)
      = ∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * c k j
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) := by
  have hd : DifferentiableAt ℝ (uLift j c) x :=
    ((contDiff_one_uLift j c h0 h1).differentiable one_ne_zero) x
  rw [uLift_eq_charSeries] at hd ⊢
  exact fderiv_charSeries_single i (fun k => c k j) (summable_norm_component j h0)
    (summable_freq_norm_component j h1) x hd

/-- **The first-order bridge for the pressure lift**: `∂ᵢ p` is the
`2πi kᵢ`-twisted pressure series. -/
theorem fderiv_pLift_single (i : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖pressureCoeff c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖pressureCoeff c k‖) (x : ℝ³) :
    fderiv ℝ (pLift c) x (EuclideanSpace.single i 1)
      = ∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * pressureCoeff c k
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) := by
  have hd : DifferentiableAt ℝ (pLift c) x :=
    ((contDiff_one_pLift c h0 h1).differentiable one_ne_zero) x
  rw [pLift_eq_charSeries] at hd ⊢
  exact fderiv_charSeries_single i (pressureCoeff c) h0 h1 x hd

/-- The Laplacian of a `C²` function on `ℝ³` is the sum of the three second
directional derivatives along the standard basis (recon C4:
`laplacian_eq_iteratedFDeriv_orthonormalBasis` + `iteratedFDeriv_two_apply` +
`fderiv_clm_apply`). -/
theorem laplacian_eq_sum_second {f : ℝ³ → ℂ} (hf : ContDiff ℝ 2 f) (x : ℝ³) :
    Δ f x = ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.basisFun_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The first derivative of the lift along `eᵢ` is the lift of the twisted family
`twistFreq i c`, as a function. -/
lemma fderiv_uLift_single_eq_twist (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) :
    (fun y : ℝ³ => fderiv ℝ (uLift j c) y (EuclideanSpace.single i 1))
      = uLift j (twistFreq i c) := by
  funext y
  rw [fderiv_uLift_single i j c h0 h1 y, uLift_eq_charSeries]
  exact tsum_congr fun k => by rw [twistFreq_apply]

/-- **The Laplacian bridge for the velocity lift**: `Δ u_j` is the
`-(2π)²‖k‖²`-weighted character series (the twisted bridge applied twice, then
`laplacian_charSum` collects the three directional symbols). -/
theorem laplacian_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖)
    (h2 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ 2 * ‖c k‖) (x : ℝ³) :
    Δ (uLift j c) x
      = ∑' k : Fin 3 → ℤ, (((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) : ℝ) : ℂ) * c k j
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) := by
  rw [laplacian_eq_sum_second (contDiff_two_uLift j c h0 h1 h2) x]
  have ht0 : ∀ i : Fin 3, Summable fun k : Fin 3 → ℤ => ‖twistFreq i c k‖ := fun i => by
    have := summable_twistFreq (q := 0) i (by simpa using h1)
    simpa using this
  have ht1 : ∀ i : Fin 3, Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖twistFreq i c k‖ :=
    fun i => by
    have := summable_twistFreq (q := 1) i (by simpa using h2)
    simpa using this
  have hsecond : ∀ i : Fin 3,
      fderiv ℝ (fun y : ℝ³ => fderiv ℝ (uLift j c) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)
        = ∑' k : Fin 3 → ℤ, ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) ^ 2 * c k j)
            * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)) := by
    intro i
    rw [fderiv_uLift_single_eq_twist i j c h0 h1,
      fderiv_uLift_single i j (twistFreq i c) (ht0 i) (ht1 i) x]
    exact tsum_congr fun k => by rw [twistFreq_apply]; ring
  rw [Finset.sum_congr rfl fun i _ => hsecond i]
  exact laplacian_charSum j c h2 (fun l => ((x l : ℝ) : AddCircle (1 : ℝ)))

/-! ## 6. Divergence and the datum-side condition -/

/-- The trace divergence is the coordinate sum of directional derivatives (recon C3:
`LinearMap.trace_eq_sum_inner` on the standard orthonormal basis). -/
theorem divergence_eq_sum (v : ℝ³ → ℝ³) (x : ℝ³) :
    Community.divergence v x = ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i 1)) i := by
  unfold Community.divergence
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp

/-- Component `j` of the derivative of a `toLp`-packed map is the derivative of the
`j`-th component (recon C8). -/
theorem fderiv_toLp_apply {F : Fin 3 → ℝ³ → ℝ} {x : ℝ³}
    (hF : ∀ j, DifferentiableAt ℝ (F j) x) (v : ℝ³) (j : Fin 3) :
    (fderiv ℝ (fun y => (WithLp.toLp 2 (fun j => F j y) : ℝ³)) x v) j = fderiv ℝ (F j) x v := by
  have hpi : HasFDerivAt (fun y (j : Fin 3) => F j y)
      (ContinuousLinearMap.pi fun j => fderiv ℝ (F j) x) x :=
    hasFDerivAt_pi.mpr fun j => (hF j).hasFDerivAt
  have hL := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm : (Fin 3 → ℝ) →L[ℝ] ℝ³)
    |>.hasFDerivAt.comp x hpi
  have hL' : HasFDerivAt (fun y => (WithLp.toLp 2 (fun j => F j y) : ℝ³))
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm : (Fin 3 → ℝ) →L[ℝ] ℝ³) ∘L
        ContinuousLinearMap.pi fun j => fderiv ℝ (F j) x) x := hL
  rw [hL'.fderiv]
  rfl

/-- The derivative of the real part is the real part of the derivative
(`Complex.reCLM` composed; the `HasFDerivAt` is restated with the exact lambda). -/
theorem fderiv_re_apply {f : ℝ³ → ℂ} {x : ℝ³} (hf : DifferentiableAt ℝ f x) (v : ℝ³) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  have h : HasFDerivAt (fun y => (f y).re) (Complex.reCLM.comp (fderiv ℝ f x)) x :=
    Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

set_option linter.unusedVariables false in
/-- **The real velocity of a divergence-free field is divergence-free**: the trace
divergence is `∑ᵢ Re ∂ᵢ u_i`, each `∂ᵢ u_i` is the twisted series, and after the
finite/infinite sum swap every mode carries `2πi·dotR (c k) (freq k) = 0` (the frozen
`hreal` is not needed: reality is not used, only `DivFree`). -/
theorem divergence_uReal_eq_zero {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (hdiv : DivFree c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (x : ℝ³) :
    Community.divergence (fun y : ℝ³ => (WithLp.toLp 2 fun j : Fin 3 => (uLift j c y).re : ℝ³)) x
      = 0 := by
  rw [divergence_eq_sum]
  have hU : ∀ j : Fin 3, DifferentiableAt ℝ (uLift j c) x := fun j =>
    ((contDiff_one_uLift j c h0 h1).differentiable one_ne_zero) x
  have hF : ∀ j : Fin 3, DifferentiableAt ℝ (fun y : ℝ³ => (uLift j c y).re) x := fun j =>
    Complex.reCLM.differentiableAt.comp x (hU j)
  have hcomp : ∀ i : Fin 3,
      (fderiv ℝ (fun y : ℝ³ => (WithLp.toLp 2 fun j : Fin 3 => (uLift j c y).re : ℝ³)) x
          (EuclideanSpace.single i 1)) i
        = (∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * c k i
            * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))).re := by
    intro i
    rw [fderiv_toLp_apply (F := fun j y => (uLift j c y).re) hF (EuclideanSpace.single i 1) i,
      fderiv_re_apply (hU i), fderiv_uLift_single i i c h0 h1 x]
  rw [Finset.sum_congr rfl fun i _ => hcomp i, ← Complex.re_sum,
    ← Summable.tsum_finsetSum (fun i _ => summable_twist_term i (fun k => c k i)
      (summable_freq_norm_component i h1) x)]
  have hzero : ∀ k : Fin 3 → ℤ,
      (∑ i : Fin 3, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * c k i
        * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    intro k
    have hd : dotR (c k) (freq k) = ∑ i : Fin 3, c k i * (((k i : ℤ) : ℝ) : ℂ) := rfl
    have hsum : (∑ i : Fin 3, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * c k i
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
        = (2 * Real.pi * Complex.I *
            ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ)))
          * ∑ i : Fin 3, c k i * (((k i : ℤ) : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [hsum, ← hd, hdiv k, mul_zero]
  rw [tsum_congr hzero, tsum_zero, Complex.zero_re]

/-- `C^∞` of the packed real datum from all-orders weighted ℓ¹ (recon C9:
`contDiff_infty`, `contDiff_euclidean`, `contDiff_uLift`, `Complex.reCLM`). -/
theorem contDiff_u₀Real (c₀ : (Fin 3 → ℤ) → Vel)
    (hc : ∀ q : ℕ, Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ q * ‖c₀ k‖) :
    ContDiff ℝ ∞ (u₀Real c₀) := by
  rw [contDiff_infty]
  intro p
  rw [contDiff_euclidean]
  intro j
  have hu : ContDiff ℝ (p : ℕ∞) (uLift j c₀) := contDiff_uLift j c₀ p fun q _ => hc q
  exact Complex.reCLM.contDiff.comp hu

/-- **The real datum meets the community initial condition**: divergence-free
(`divergence_uReal_eq_zero`), `C^∞` (`contDiff_u₀Real`), and `1`-periodic
(`isOnePeriodic_uLift` in every component); the weighted ℓ¹ certificates come from
the Sobolev levels through `summable_weighted_norm` (mean-zero datum). -/
theorem initialVelocityConditionPeriodic_u₀Real {c₀ : (Fin 3 → ℤ) → Vel}
    (hsob : ∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2)
    (h0 : c₀ 0 = 0) (hreal : RealField c₀) (hdiv : DivFree c₀) :
    InitialVelocityConditionPeriodic (n := 3) (u₀Real c₀) := by
  have hc : ∀ q : ℕ, Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ q * ‖c₀ k‖ := fun q =>
    summable_weighted_norm h0 (hsob (q + 2))
  have hc0 : Summable fun k : Fin 3 → ℤ => ‖c₀ k‖ := by simpa using hc 0
  have hc1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c₀ k‖ := by simpa using hc 1
  refine ⟨⟨fun x => ?_, contDiff_u₀Real c₀ hc⟩, fun x i => ?_⟩
  · exact divergence_uReal_eq_zero hreal hdiv hc0 hc1 x
  · show (WithLp.toLp 2 fun j : Fin 3 => (uLift j c₀ (x + EuclideanSpace.single i 1)).re : ℝ³)
        = WithLp.toLp 2 fun j : Fin 3 => (uLift j c₀ x).re
    congr 1
    funext j
    rw [isOnePeriodic_uLift j c₀ x i]

end

/-! ## 7. Probe section (non-frozen, registered): the nonzero shear datum

The pair-mode shear datum `ε·e₂` on the modes `±e₁` is CLONED from the private
section of ForcedProbe.lean (never un-privated there).  It is the section 6b witness:
every capstone hypothesis of Tier 8b holds for it with `c₀ ≠ 0`, its real lift is
nonzero, the rest pair is not a witness of the class for it, and the time-constant
coefficient flow fails the mode equation. -/

namespace W3Probe

noncomputable section

private def pe1 : Fin 3 → ℤ := ![1, 0, 0]

private lemma pe1_ne_zero : pe1 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [pe1] at this

private lemma neg_pe1_ne_zero : -pe1 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [pe1] at this

private lemma pe1_ne_neg : pe1 ≠ -pe1 := by
  intro h
  have := congrFun h 0
  simp [pe1] at this

private lemma norm_freq_pe1 : ‖freq pe1‖ = 1 := by
  rw [norm_freq]
  simp [pe1, Fin.sum_univ_three]

private lemma norm_freq_neg_pe1 : ‖freq (-pe1)‖ = 1 := by
  rw [norm_freq]
  simp [pe1, Fin.sum_univ_three]

private def pBox : Finset (Fin 3 → ℤ) := {pe1, -pe1}

private lemma zero_not_mem_pBox : (0 : Fin 3 → ℤ) ∉ pBox := by
  simp [pBox, pe1_ne_zero.symm, neg_pe1_ne_zero.symm]

private lemma pBox_symm : ∀ k ∈ pBox, -k ∈ pBox := by
  intro k hk
  simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hk ⊢
  rcases hk with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

private def probeVec (r : ℝ) : Vel := EuclideanSpace.single 1 (r : ℂ)

private lemma norm_probeVec (r : ℝ) : ‖probeVec r‖ = |r| := by
  rw [probeVec, PiLp.norm_single, Complex.norm_real, Real.norm_eq_abs]

private lemma conjVel_probeVec (r : ℝ) : conjVel (probeVec r) = probeVec r := by
  ext j
  simp only [conjVel, probeVec, WithLp.ofLp_toLp, PiLp.single_apply]
  split_ifs <;> simp

private lemma dotR_probeVec_pe1 (r : ℝ) : dotR (probeVec r) (freq pe1) = 0 := by
  simp [dotR, probeVec, freq, pe1]

private lemma dotR_probeVec_neg_pe1 (r : ℝ) : dotR (probeVec r) (freq (-pe1)) = 0 := by
  simp [dotR, probeVec, freq, pe1]

private lemma probeVec_ne_zero {r : ℝ} (hr : r ≠ 0) : probeVec r ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [norm_probeVec, norm_zero] at this
  exact hr (abs_eq_zero.mp this)

private def pairDatum (v : Vel) : (Fin 3 → ℤ) → Vel :=
  fun k => if k = pe1 ∨ k = -pe1 then v else 0

private lemma pairDatum_eq_zero {v : Vel} {k : Fin 3 → ℤ} (hk : k ∉ pBox) :
    pairDatum v k = 0 := by
  simp only [pBox, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [pairDatum, hk.1, hk.2]

private lemma pairDatum_pe1 (v : Vel) : pairDatum v pe1 = v := by
  simp [pairDatum]

private lemma pairDatum_neg_pe1 (v : Vel) : pairDatum v (-pe1) = v := by
  simp [pairDatum]

private lemma pairDatum_zero_mode (v : Vel) : pairDatum v 0 = 0 :=
  pairDatum_eq_zero zero_not_mem_pBox

private lemma pair_tsum (w : (Fin 3 → ℤ) → ℝ) (v : Vel) :
    ∑' k, w k * ‖pairDatum v k‖ ^ 2 = (w pe1 + w (-pe1)) * ‖v‖ ^ 2 := by
  have hsupp : ∀ k ∉ pBox, w k * ‖pairDatum v k‖ ^ 2 = 0 := by
    intro k hk
    simp [pairDatum_eq_zero hk]
  rw [tsum_eq_sum hsupp]
  simp only [pBox]
  rw [Finset.sum_pair pe1_ne_neg]
  simp [pairDatum, pe1_ne_neg, pe1_ne_neg.symm]
  ring

private lemma en_pairDatum (v : Vel) : en (pairDatum v) = 2 * ‖v‖ ^ 2 := by
  have h := pair_tsum (fun _ => 1) v
  simp only [one_mul] at h
  show ∑' k, ‖pairDatum v k‖ ^ 2 = _
  rw [h]
  ring

private lemma ens_pairDatum (v : Vel) : ens (pairDatum v) = 2 * ‖v‖ ^ 2 := by
  have h := pair_tsum (fun k => ‖freq k‖ ^ 2) v
  show ∑' k, ‖freq k‖ ^ 2 * ‖pairDatum v k‖ ^ 2 = _
  rw [h, norm_freq_pe1, norm_freq_neg_pe1]
  norm_num

private lemma summable_wsq_pairDatum_all (v : Vel) (m : ℕ) :
    Summable fun l => ‖freq l‖ ^ (2 * m) * ‖pairDatum v l‖ ^ 2 :=
  summable_of_ne_finset_zero (s := pBox) fun k hk => by rw [pairDatum_eq_zero hk]; simp

private lemma realField_pairDatum_probeVec (r : ℝ) : RealField (pairDatum (probeVec r)) := by
  intro k
  by_cases hk : k ∈ pBox
  · have hnk : -k ∈ pBox := pBox_symm k hk
    simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hk hnk
    simp only [pairDatum]
    rw [if_pos hnk, if_pos hk, conjVel_probeVec]
  · have hnk : -k ∉ pBox := by
      intro h
      exact hk (by simpa using pBox_symm (-k) h)
    rw [pairDatum_eq_zero hk, pairDatum_eq_zero hnk]
    ext j
    simp [conjVel]

private lemma divFree_pairDatum_probeVec (r : ℝ) : DivFree (pairDatum (probeVec r)) := by
  intro k
  by_cases hk : k ∈ pBox
  · simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [pairDatum]
    rw [if_pos hk]
    rcases hk with rfl | rfl
    · exact dotR_probeVec_pe1 r
    · exact dotR_probeVec_neg_pe1 r
  · rw [pairDatum_eq_zero hk]
    simp [dotR]

private lemma pairDatum_probeVec_ne_zero {r : ℝ} (hr : r ≠ 0) :
    pairDatum (probeVec r) ≠ 0 := by
  intro h
  have := congrFun h pe1
  simp only [pairDatum, true_or, if_true, Pi.zero_apply] at this
  exact probeVec_ne_zero hr this

private lemma convFull_pairDatum_probeVec (r : ℝ) (k : Fin 3 → ℤ) :
    convFull (pairDatum (probeVec r)) k = 0 := by
  unfold convFull
  have hterm : ∀ l : Fin 3 → ℤ,
      (Complex.I * dotR (pairDatum (probeVec r) l) (freq (k - l))) •
        pairDatum (probeVec r) (k - l) = 0 := by
    intro l
    by_cases hkl : k - l ∈ pBox
    · have hdot : dotR (pairDatum (probeVec r) l) (freq (k - l)) = 0 := by
        simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hkl
        by_cases hl : l = pe1 ∨ l = -pe1
        · simp only [pairDatum, if_pos hl]
          rcases hkl with h | h
          · rw [h]; exact dotR_probeVec_pe1 r
          · rw [h]; exact dotR_probeVec_neg_pe1 r
        · simp only [pairDatum, if_neg hl]
          simp [dotR]
      rw [hdot, mul_zero, zero_smul]
    · rw [pairDatum_eq_zero hkl, smul_zero]
  rw [tsum_congr hterm]
  simp

private lemma lerayProj_zero_vec (k : Fin 3 → ℤ) : lerayProj k (0 : Vel) = 0 := by
  have h := lerayProj_sub k (0 : Vel) 0
  rw [sub_self, sub_self] at h
  exact h

/-- **The test datum**: the shear `ε·e₂` on the two modes `±e₁`, zero elsewhere. -/
def testDatum (ε : ℝ) : (Fin 3 → ℤ) → Vel := pairDatum (probeVec ε)

/-- MUST INHABIT (section 6b): for every `κ, ν > 0` the shear datum with
`ε = ν/(κ+3)` is NONZERO, summable at every Sobolev level, mean-zero, real,
divergence-free, and strictly inside the smallness threshold: exactly the
hypothesis set of the Tier 8b capstones. -/
theorem exists_nonzero_admissible_datum {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ c₀ : (Fin 3 → ℤ) → Vel, c₀ ≠ 0 ∧
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) ∧
      c₀ 0 = 0 ∧ RealField c₀ ∧ DivFree c₀ ∧ κ * en c₀ * ens c₀ < ν ^ 4 := by
  set r : ℝ := ν / (κ + 3) with hr
  have hrpos : 0 < r := by positivity
  refine ⟨testDatum r, pairDatum_probeVec_ne_zero hrpos.ne',
    summable_wsq_pairDatum_all _, pairDatum_zero_mode _, realField_pairDatum_probeVec r,
    divFree_pairDatum_probeVec r, ?_⟩
  show κ * en (pairDatum (probeVec r)) * ens (pairDatum (probeVec r)) < ν ^ 4
  rw [en_pairDatum, ens_pairDatum, norm_probeVec, sq_abs]
  have h1 : 4 * κ < (κ + 3) ^ 2 := by nlinarith [sq_nonneg (κ - 1)]
  have h2 : (κ + 3) ^ 2 ≤ (κ + 3) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hν4 : 0 < ν ^ 4 := by positivity
  have hkey : κ * (2 * r ^ 2) * (2 * r ^ 2) = 4 * κ * ν ^ 4 / (κ + 3) ^ 4 := by
    rw [hr]; field_simp; ring
  rw [hkey, div_lt_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2) hν4]

/-- The character at the origin is `1`. -/
private lemma char_zero (k : Fin 3 → ℤ) :
    (∏ l : Fin 3, fourier (k l) (((0 : ℝ³) l : ℝ) : AddCircle (1 : ℝ))) = 1 := by
  refine Finset.prod_eq_one fun l _ => ?_
  have h : (((0 : ℝ³) l : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
  rw [h, fourier_eval_zero]

/-- The second component of the lift of the test datum at the origin is `2ε`
(the two modes `±e₁` each contribute `ε`). -/
theorem uLift_testDatum_zero (ε : ℝ) : uLift 1 (testDatum ε) 0 = 2 * (ε : ℂ) := by
  rw [uLift_eq_charSeries]
  simp only [char_zero, mul_one]
  rw [tsum_eq_sum (s := pBox) (fun k hk => by
    show (pairDatum (probeVec ε) k) 1 = 0
    rw [pairDatum_eq_zero hk]; rfl)]
  simp only [pBox]
  rw [Finset.sum_pair pe1_ne_neg]
  show (pairDatum (probeVec ε) pe1) 1 + (pairDatum (probeVec ε) (-pe1)) 1 = _
  rw [pairDatum_pe1, pairDatum_neg_pe1]
  simp [probeVec]
  ring

/-- The real datum of the test datum is NONZERO for `ε ≠ 0`. -/
theorem u₀Real_testDatum_ne_zero {ε : ℝ} (hε : ε ≠ 0) : u₀Real (testDatum ε) ≠ 0 := by
  intro h
  have h1 := congrArg (fun F : ℝ³ → ℝ³ => (F 0) 1) h
  simp only [u₀Real, Pi.zero_apply, PiLp.zero_apply, PiLp.toLp_apply,
    uLift_testDatum_zero] at h1
  simp at h1
  exact hε h1

/-- MUST FAIL (section 6b): the rest velocity `v := 0` is NOT a witness of the class
for the test datum (`ε ≠ 0`), for every `nu`, every force and every pressure: its
`initial_condition` clause fails. -/
theorem rest_pair_fails_class {ε : ℝ} (hε : ε ≠ 0) (nu : ℝ) (f : ℝ³ → ℝ → ℝ³)
    (p : ℝ³ → ℝ → ℝ) :
    ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) nu (u₀Real (testDatum ε)) f
        (fun _ _ => 0) p := by
  intro h
  have h1 := h.initial_condition 0
  have h2 := congrArg (fun v : ℝ³ => v 1) h1
  simp only [u₀Real, PiLp.zero_apply, PiLp.toLp_apply, uLift_testDatum_zero] at h2
  simp at h2
  exact hε h2

/-- MUST FAIL (section 6b): the time-constant coefficient flow `c t := testDatum ε`
violates the mode equation of clause 6 of `theorem_B_time_smooth` (`ε ≠ 0`, `ν > 0`):
at `t = 1`, `k = e₁` the right-hand side is `(-ν) • (ε·e₂) ≠ 0` while a constant has
derivative `0`. -/
theorem const_flow_fails_ode {ν : ℝ} (hν : 0 < ν) {ε : ℝ} (hε : ε ≠ 0) :
    ¬ (∀ t ∈ Ioi (0:ℝ), ∀ k,
        HasDerivAt (fun s => (fun (_ : ℝ) => testDatum ε) s k)
          ((-(ν * ‖freq k‖ ^ 2)) • (fun (_ : ℝ) => testDatum ε) t k
            + lerayProj k (convFull ((fun (_ : ℝ) => testDatum ε) t) k)) t) := by
  intro h
  have h1 := h 1 (by norm_num) pe1
  have hrhs : (-(ν * ‖freq pe1‖ ^ 2)) • testDatum ε pe1
      + lerayProj pe1 (convFull (testDatum ε) pe1) = (-ν) • probeVec ε := by
    show (-(ν * ‖freq pe1‖ ^ 2)) • pairDatum (probeVec ε) pe1
      + lerayProj pe1 (convFull (pairDatum (probeVec ε)) pe1) = (-ν) • probeVec ε
    rw [convFull_pairDatum_probeVec, lerayProj_zero_vec, add_zero, pairDatum_pe1, norm_freq_pe1]
    norm_num
  have h2 : HasDerivAt (fun (_ : ℝ) => testDatum ε pe1) 0 1 := hasDerivAt_const _ _
  have h3 : (-ν) • probeVec ε = 0 := by
    have := h1.unique h2
    rwa [hrhs] at this
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact hν.ne' (neg_eq_zero.mp h4)
  · exact probeVec_ne_zero hε h4

end

end W3Probe


noncomputable section

/-! ## 8. Wave W4: the clock-transported derivatives and the two capstones

The endpoint derivative at `t = 0` of the character sum, the within-derivative of the
real velocity in the community clock, the per-component spectral identity behind the
`navier_stokes` clause, the Mathlib-side operator reductions (recon G1 to G4), the seam
of clauses 24/25 into the two smoothness fields, and the two capstones. -/

/-- **The endpoint derivative of the character sum** (frozen W4): within `Ici 0` at
`t = 0`, `s ↦ Σ_k c_s(k)_j e_k(x)` has the spectral right-hand side as derivative.  The
W2 engine `hasDerivWithinAt_tsum_of_convex` at `E = ℝ` on `Ico 0 b` (per-mode
derivatives from `hzero` at `0` and `hchain` on `t > 0`, majorant `u`, summability at
the base point `0`), then `mono_of_mem_nhdsWithin` with `Ico 0 b ∈ 𝓝[≥] 0`. -/
theorem hasDerivWithinAt_charSum_zero {ν : ℝ} {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hzero : ∀ k, HasDerivWithinAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c 0 k + lerayProj k (convFull (c 0) k)) (Ici (0:ℝ)) 0)
    (hchain : ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t)
    {b : ℝ} (hb : 0 < b) {u : (Fin 3 → ℤ) → ℝ} (hu : Summable u)
    (hmaj : ∀ t ∈ Icc (0:ℝ) b, ∀ k,
      ‖(-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)‖ ≤ u k)
    (hs₀ : Summable fun k => ‖c 0 k‖) (j : Fin 3) (x : UnitAddTorus (Fin 3)) :
    HasDerivWithinAt (fun s => ∑' k, c s k j * mFourier k x)
      (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c 0 k
        + lerayProj k (convFull (c 0) k)) j * mFourier k x) (Ici (0:ℝ)) 0 := by
  -- the per-mode within-derivatives on `Ico 0 b`
  have hIco : ∀ k, ∀ s ∈ Ico (0:ℝ) b,
      HasDerivWithinAt (fun s => c s k j * mFourier k x)
        (((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)) j * mFourier k x)
        (Ico (0:ℝ) b) s := by
    intro k s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h
      have h1 := ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt
        |>.comp_hasDerivWithinAt (0:ℝ) (hzero k)
      exact (h1.mul_const (mFourier k x)).mono Ico_subset_Ici_self
    · have h1 := ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt
        |>.comp_hasDerivAt s (hchain s h k)
      exact (h1.mul_const (mFourier k x)).hasDerivWithinAt
  -- the majorant
  have hbound : ∀ k, ∀ s ∈ Ico (0:ℝ) b,
      ‖((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)) j * mFourier k x‖
        ≤ u k := by
    intro k s hs
    rw [norm_mul, norm_mFourier_apply, mul_one]
    exact le_trans (PiLp.norm_apply_le _ j) (hmaj s ⟨hs.1, hs.2.le⟩ k)
  -- summability at the base point
  have hs0 : Summable fun k => c 0 k j * mFourier k x := by
    refine Summable.of_norm (hs₀.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_)
    rw [norm_mul, norm_mFourier_apply, mul_one]
    exact PiLp.norm_apply_le _ j
  have h := hasDerivWithinAt_tsum_of_convex (convex_Ico (0:ℝ) b) hu hIco hbound
    (x₀ := 0) ⟨le_rfl, hb⟩ hs0 (x := 0) ⟨le_rfl, hb⟩
  exact h.mono_of_mem_nhdsWithin (Ico_mem_nhdsGE hb)

/-- **The within-derivative of the real velocity in the community clock** (frozen W4):
on `Ici 0` at `τ ≥ 0` it is `2π` times the real part of the lift of `g (2πτ)`, packed
into `ℝ³`.  The clock `HasDerivWithinAt.scomp_of_eq` (its point is the first explicit
argument), the real part through `Complex.reCLM`, the packing through
`hasDerivWithinAt_pi` and `PiLp.continuousLinearEquiv`, and `HasDerivWithinAt.derivWithin`
with the unique differentials of `Ici 0` (`uniqueDiffOn_Ici`), uniformly in `τ`. -/
theorem derivWithin_vReal_Ici {c : ℝ → (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel}
    (hpos : ∀ (j : Fin 3) (x : ℝ³), ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (fun s => uLift j (c s) x) (uLift j (g t) x) t)
    (hzero : ∀ (j : Fin 3) (x : ℝ³),
      HasDerivWithinAt (fun s => uLift j (c s) x) (uLift j (g 0) x) (Ici (0:ℝ)) 0)
    (x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    derivWithin (vReal c x ·) (Ici (0:ℝ)) τ
      = WithLp.toLp 2 fun j : Fin 3 =>
          (2 * Real.pi) * (uLift j (g (2 * Real.pi * τ)) x).re := by
  -- the within-derivative of each real component in the clock
  have hcomp : ∀ j : Fin 3,
      HasDerivWithinAt (fun σ : ℝ => (uLift j (c (2 * Real.pi * σ)) x).re)
        ((2 * Real.pi) * (uLift j (g (2 * Real.pi * τ)) x).re) (Ici (0:ℝ)) τ := by
    intro j
    have hw : HasDerivWithinAt (fun s => uLift j (c s) x) (uLift j (g (2 * Real.pi * τ)) x)
        (Ici (0:ℝ)) (2 * Real.pi * τ) := by
      rcases eq_or_lt_of_le hτ with h | h
      · subst h
        rw [mul_zero]
        exact hzero j x
      · exact (hpos j x _ (mem_Ioi.mpr (by positivity))).hasDerivWithinAt
    have hh : HasDerivWithinAt (fun σ : ℝ => 2 * Real.pi * σ) (2 * Real.pi) (Ici (0:ℝ)) τ := by
      simpa using ((hasDerivWithinAt_id τ (Ici (0:ℝ))).const_mul (2 * Real.pi))
    have hmaps : MapsTo (fun σ : ℝ => 2 * Real.pi * σ) (Ici (0:ℝ)) (Ici (0:ℝ)) := by
      intro σ hσ
      exact mul_nonneg (by positivity) (mem_Ici.mp hσ)
    have hclock : HasDerivWithinAt (fun σ : ℝ => uLift j (c (2 * Real.pi * σ)) x)
        ((2 * Real.pi) • uLift j (g (2 * Real.pi * τ)) x) (Ici (0:ℝ)) τ :=
      HasDerivWithinAt.scomp_of_eq τ hw hh hmaps rfl
    have hre : HasDerivWithinAt (fun σ : ℝ => Complex.reCLM (uLift j (c (2 * Real.pi * σ)) x))
        (Complex.reCLM ((2 * Real.pi) • uLift j (g (2 * Real.pi * τ)) x)) (Ici (0:ℝ)) τ :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt τ hclock
    have hval : Complex.reCLM ((2 * Real.pi) • uLift j (g (2 * Real.pi * τ)) x)
        = (2 * Real.pi) * (uLift j (g (2 * Real.pi * τ)) x).re := by
      rw [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul]
    rw [hval] at hre
    exact hre
  have hpi : HasDerivWithinAt
      (fun σ : ℝ => fun j : Fin 3 => (uLift j (c (2 * Real.pi * σ)) x).re)
      (fun j : Fin 3 => (2 * Real.pi) * (uLift j (g (2 * Real.pi * τ)) x).re) (Ici (0:ℝ)) τ :=
    hasDerivWithinAt_pi.mpr hcomp
  have hpack : HasDerivWithinAt (vReal c x ·)
      (WithLp.toLp 2 fun j : Fin 3 => (2 * Real.pi) * (uLift j (g (2 * Real.pi * τ)) x).re)
      (Ici (0:ℝ)) τ :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm : (Fin 3 → ℝ) →L[ℝ] ℝ³)
      |>.hasFDerivAt.comp_hasDerivWithinAt τ hpi
  exact hpack.derivWithin (uniqueDiffOn_Ici 0 τ hτ)

/-! ### The spectral component identity (non-frozen) -/

/-- The fiber point of `x : ℝ³` on the torus (`uLift j d x` is the character sum at it,
by `rfl`). -/
def fiber (x : ℝ³) : UnitAddTorus (Fin 3) := fun l => ((x l : ℝ) : AddCircle (1 : ℝ))

lemma uLift_eq_charSum_fiber (j : Fin 3) (d : (Fin 3 → ℤ) → Vel) (x : ℝ³) :
    uLift j d x = ∑' k, d k j * mFourier k (fiber x) := rfl

lemma pLift_eq_charSum_fiber (d : (Fin 3 → ℤ) → Vel) (x : ℝ³) :
    pLift d x = ∑' k, pressureCoeff d k * mFourier k (fiber x) := rfl

/-- **The per-component identity behind the class's `navier_stokes` clause**, at a fixed
coefficient field `d` (later `c (2πτ)`): `2π·Re(u_j(RHS)) + Σᵢ Re(uᵢ)·Re(∂ᵢu_j)
= (ν/(2π))·Re(Δu_j) − 2π·Re(∂_j p)`.  The spectral right-hand side is decomposed by
clause 18 (`hleray`) into viscous, convective and pressure series; the viscous series is
`(ν/(2π)²)` times the Laplacian bridge `laplacian_uLift`; the convective series is
clause 19 (`hnl`) once the factors `uᵢ` are real (`im_uLift_eq_zero`); the pressure
series is the bridge `fderiv_pLift_single`; the rest is the `2π` arithmetic. -/
theorem navier_stokes_component_spectral {ν : ℝ} (hν : 0 < ν) {d : (Fin 3 → ℤ) → Vel}
    (hreal : RealField d)
    (hE : Summable fun l => ‖d l‖ ^ 2) (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖d l‖ ^ 2)
    (h0 : Summable fun k => ‖d k‖) (h1 : Summable fun k => ‖freq k‖ * ‖d k‖)
    (h2 : Summable fun k => ‖freq k‖ ^ 2 * ‖d k‖)
    (hp0 : Summable fun k => ‖pressureCoeff d k‖)
    (hp1 : Summable fun k => ‖freq k‖ * ‖pressureCoeff d k‖)
    (hleray : ∀ (k : Fin 3 → ℤ) (j : Fin 3),
      (lerayProj k (convFull d k)) j
        = convFull d k j - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff d k)
    (hnl : ∀ (j : Fin 3) (z : UnitAddTorus (Fin 3)),
      (∑ i : Fin 3, (∑' l, d l i * mFourier l z) *
          (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * d m j * mFourier m z))
        = ((-(2 * Real.pi) : ℝ) : ℂ) * ∑' k, convFull d k j * mFourier k z)
    (x : ℝ³) (j : Fin 3) :
    (2 * Real.pi) *
        (uLift j (fun k => (-(ν * ‖freq k‖ ^ 2)) • d k + lerayProj k (convFull d k)) x).re
      + ∑ i : Fin 3, (uLift i d x).re * (fderiv ℝ (uLift j d) x (EuclideanSpace.single i 1)).re
      = (ν / (2 * Real.pi)) * (Δ (uLift j d) x).re
        - (2 * Real.pi) * (fderiv ℝ (pLift d) x (EuclideanSpace.single j 1)).re := by
  -- the four series at the fiber point
  have hDi : ∀ i : Fin 3, fderiv ℝ (uLift j d) x (EuclideanSpace.single i 1)
      = ∑' k, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * d k j * mFourier k (fiber x) := by
    intro i
    rw [fderiv_uLift_single i j d h0 h1 x]
    rfl
  have hL : Δ (uLift j d) x
      = ∑' k, (((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) : ℝ) : ℂ) * d k j * mFourier k (fiber x) := by
    rw [laplacian_uLift j d h0 h1 h2 x]
    rfl
  have hGr : fderiv ℝ (pLift d) x (EuclideanSpace.single j 1)
      = ∑' k, (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff d k
          * mFourier k (fiber x) := by
    rw [fderiv_pLift_single j d hp0 hp1 x]
    rfl
  have hRHS : uLift j (fun k => (-(ν * ‖freq k‖ ^ 2)) • d k + lerayProj k (convFull d k)) x
      = ∑' k, ((-(ν * ‖freq k‖ ^ 2)) • d k + lerayProj k (convFull d k)) j
          * mFourier k (fiber x) := rfl
  -- summability of the three pieces (the ClassicalEquation recipe)
  have hV : Summable fun k =>
      (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * d k j) * mFourier k (fiber x) := by
    refine Summable.of_norm ((h2.mul_left ν).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_)
    have hr : ‖(((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ))‖ = ν * ‖freq k‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    rw [norm_mul, norm_mFourier_apply, mul_one, norm_mul, hr]
    calc ν * ‖freq k‖ ^ 2 * ‖d k j‖ ≤ ν * ‖freq k‖ ^ 2 * ‖d k‖ := by
          gcongr; exact PiLp.norm_apply_le (d k) j
      _ = ν * (‖freq k‖ ^ 2 * ‖d k‖) := by ring
  have hC : Summable fun k => convFull d k j * mFourier k (fiber x) := by
    refine Summable.of_norm ((summable_norm_convFull hE hZ h0 h1)
      |>.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_)
    rw [norm_mul, norm_mFourier_apply, mul_one]
    exact PiLp.norm_apply_le (convFull d k) j
  have hG : Summable fun k =>
      (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff d k * mFourier k (fiber x) := by
    refine Summable.of_norm ((hp1.mul_left (2 * Real.pi)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_)
    have e : ‖(2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ))‖ = 2 * Real.pi * |(k j : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
      have e1 : ‖(2 : ℂ)‖ = 2 := by simp
      have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
      have e4 : ‖((k j : ℤ) : ℂ)‖ = |(k j : ℝ)| := by simp
      rw [e1, e2, e4]; ring
    rw [norm_mul, norm_mFourier_apply, mul_one, norm_mul, e]
    calc 2 * Real.pi * |(k j : ℝ)| * ‖pressureCoeff d k‖
        ≤ 2 * Real.pi * ‖freq k‖ * ‖pressureCoeff d k‖ := by
          gcongr; exact abs_coord_le_norm_freq k j
      _ = 2 * Real.pi * (‖freq k‖ * ‖pressureCoeff d k‖) := by ring
  -- term-wise decomposition of the spectral right-hand side (clause 18)
  have hterm : ∀ k, ((-(ν * ‖freq k‖ ^ 2)) • d k + lerayProj k (convFull d k)) j
        * mFourier k (fiber x)
      = (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * d k j) * mFourier k (fiber x)
        + convFull d k j * mFourier k (fiber x)
        - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff d k
            * mFourier k (fiber x) := by
    intro k
    rw [PiLp.add_apply, PiLp.smul_apply, hleray k j, Complex.real_smul]
    ring
  have hsplit : (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • d k + lerayProj k (convFull d k)) j
        * mFourier k (fiber x))
      = (∑' k, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * d k j) * mFourier k (fiber x))
        + (∑' k, convFull d k j * mFourier k (fiber x))
        - ∑' k, (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff d k
            * mFourier k (fiber x) := by
    rw [tsum_congr hterm, Summable.tsum_sub (hV.add hC) hG, Summable.tsum_add hV hC]
  -- the viscous series is the scaled Laplacian series
  have hVL : (∑' k, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * d k j) * mFourier k (fiber x))
      = ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          ∑' k, (((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) : ℝ) : ℂ) * d k j
            * mFourier k (fiber x) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  -- the convection: real factors
  have him : ∀ i : Fin 3, (uLift i d x).im = 0 := fun i => im_uLift_eq_zero hreal h0 i x
  have hprod : (∑ i : Fin 3, (uLift i d x).re
        * (fderiv ℝ (uLift j d) x (EuclideanSpace.single i 1)).re)
      = (∑ i : Fin 3, uLift i d x * fderiv ℝ (uLift j d) x (EuclideanSpace.single i 1)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_re, him i, zero_mul, sub_zero]
  have hnl' : (∑ i : Fin 3, uLift i d x * fderiv ℝ (uLift j d) x (EuclideanSpace.single i 1))
      = ((-(2 * Real.pi) : ℝ) : ℂ) * ∑' k, convFull d k j * mFourier k (fiber x) := by
    rw [← hnl j (fiber x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hDi i, uLift_eq_charSum_fiber]
  rw [hprod, hnl', hRHS, hsplit, hVL, hL, hGr, Complex.re_ofReal_mul, Complex.sub_re,
    Complex.add_re, Complex.re_ofReal_mul]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### The Mathlib-side operator reductions (recon G1 to G4) and the bridges on the
packed real fields -/

/-- G1: the gradient's components are the coordinate directional derivatives. -/
theorem gradient_apply_eq_fderiv_single {f : ℝ³ → ℝ} {x : ℝ³} (hf : DifferentiableAt ℝ f x)
    (i : Fin 3) :
    (gradient f x) i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hg : HasGradientAt f (gradient f x) x := hf.hasGradientAt
  have hfd : HasFDerivAt f ((toDual ℝ ℝ³) (gradient f x)) x := hasGradientAt_iff_hasFDerivAt.mp hg
  rw [hfd.fderiv]
  rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_right]
  simp

/-- G2: a directional derivative expands along the coordinate basis, component `j`. -/
theorem fderiv_apply_expand {V : ℝ³ → ℝ³} {x : ℝ³} (w : ℝ³) (j : Fin 3) :
    (fderiv ℝ V x w) j
      = ∑ i : Fin 3, w i * (fderiv ℝ V x (EuclideanSpace.single i 1)) j := by
  have hw : w = ∑ i : Fin 3, w i • EuclideanSpace.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]
  simp [map_smul]

/-- G3: the Laplacian of a packed field, component by component. -/
theorem laplacian_apply_component {V : ℝ³ → ℝ³} {x : ℝ³} (hV : ContDiffAt ℝ 2 V x) (j : Fin 3) :
    (Δ V x) j = Δ (fun y => V y j) x := by
  have h := ContDiffAt.laplacian_CLM_comp_left (l := EuclideanSpace.proj (𝕜 := ℝ) j) hV
  exact h.symm

/-- G4: the Laplacian commutes with the real part. -/
theorem laplacian_re {g : ℝ³ → ℂ} {x : ℝ³} (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y => (g y).re) x = (Δ g x).re := by
  have h := ContDiffAt.laplacian_CLM_comp_left (l := Complex.reCLM) hg
  exact h

/-- The convection term of the packed real field, component `j`: `Σᵢ Re(uᵢ)·Re(∂ᵢu_j)`
(`fderiv_apply_expand`, `fderiv_toLp_apply`, `fderiv_re_apply`). -/
theorem vReal_convection_apply (d : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k => ‖d k‖) (h1 : Summable fun k => ‖freq k‖ * ‖d k‖)
    (x : ℝ³) (j : Fin 3) :
    (fderiv ℝ (fun y : ℝ³ => (WithLp.toLp 2 fun i : Fin 3 => (uLift i d y).re : ℝ³)) x
        (WithLp.toLp 2 fun i : Fin 3 => (uLift i d x).re)) j
      = ∑ i : Fin 3, (uLift i d x).re
          * (fderiv ℝ (uLift j d) x (EuclideanSpace.single i 1)).re := by
  rw [fderiv_apply_expand]
  have hU : ∀ i : Fin 3, DifferentiableAt ℝ (uLift i d) x := fun i =>
    ((contDiff_one_uLift i d h0 h1).differentiable one_ne_zero) x
  have hF : ∀ i : Fin 3, DifferentiableAt ℝ (fun y : ℝ³ => (uLift i d y).re) x := fun i =>
    Complex.reCLM.differentiableAt.comp x (hU i)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_toLp_apply (F := fun j y => (uLift j d y).re) hF (EuclideanSpace.single i 1) j,
    fderiv_re_apply (hU j)]

/-- The Laplacian of the packed real field, component `j`, is `Re(Δu_j)` (G3, G4). -/
theorem vReal_laplacian_apply (d : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k => ‖d k‖) (h1 : Summable fun k => ‖freq k‖ * ‖d k‖)
    (h2 : Summable fun k => ‖freq k‖ ^ 2 * ‖d k‖) (x : ℝ³) (j : Fin 3) :
    (Δ (fun y : ℝ³ => (WithLp.toLp 2 fun i : Fin 3 => (uLift i d y).re : ℝ³)) x) j
      = (Δ (uLift j d) x).re := by
  have hV : ContDiffAt ℝ 2 (fun y : ℝ³ => (WithLp.toLp 2 fun i : Fin 3 => (uLift i d y).re : ℝ³)) x := by
    refine ContDiff.contDiffAt ?_
    rw [contDiff_euclidean]
    intro i
    exact Complex.reCLM.contDiff.comp (contDiff_two_uLift i d h0 h1 h2)
  rw [laplacian_apply_component hV j]
  exact laplacian_re (contDiff_two_uLift j d h0 h1 h2).contDiffAt

/-- The gradient of `2π·Re p`, component `j`, is `2π·Re(∂_j p)` (G1, `fderiv_const_mul`,
`fderiv_re_apply`). -/
theorem pReal_gradient_apply (d : (Fin 3 → ℤ) → Vel)
    (hp0 : Summable fun k => ‖pressureCoeff d k‖)
    (hp1 : Summable fun k => ‖freq k‖ * ‖pressureCoeff d k‖) (x : ℝ³) (j : Fin 3) :
    (gradient (fun y : ℝ³ => (2 * Real.pi) * (pLift d y).re) x) j
      = (2 * Real.pi) * (fderiv ℝ (pLift d) x (EuclideanSpace.single j 1)).re := by
  have hP : DifferentiableAt ℝ (pLift d) x :=
    ((contDiff_one_pLift d hp0 hp1).differentiable one_ne_zero) x
  have hR : DifferentiableAt ℝ (fun y : ℝ³ => (pLift d y).re) x :=
    Complex.reCLM.differentiableAt.comp x hP
  have hf : DifferentiableAt ℝ (fun y : ℝ³ => (2 * Real.pi) * (pLift d y).re) x :=
    hR.const_mul _
  rw [gradient_apply_eq_fderiv_single hf j, fderiv_const_mul hR, ContinuousLinearMap.smul_apply,
    smul_eq_mul, fderiv_re_apply hP]

/-! ## The clock CLM and the two smoothness fields (the W2 seam, reused) -/

/-- The clock CLM `(x, τ) ↦ (x, 2πτ)`. -/
def clockCLM : ℝ³ × ℝ →L[ℝ] ℝ³ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ³ ℝ).prod ((2 * Real.pi) • ContinuousLinearMap.snd ℝ ℝ³ ℝ)

lemma clockCLM_apply (q : ℝ³ × ℝ) : clockCLM q = (q.1, 2 * Real.pi * q.2) := rfl

lemma clockCLM_mapsTo :
    MapsTo clockCLM ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) := by
  intro q hq
  refine ⟨mem_univ _, ?_⟩
  show (0:ℝ) ≤ 2 * Real.pi * q.2
  have := mem_Ici.mp hq.2
  positivity

/-- Clause 24 composed with `Complex.reCLM` and the clock gives `velocity_smooth`. -/
theorem velocity_smooth_of_clause24 {c : ℝ → (Fin 3 → ℤ) → Vel}
    (h24 : ∀ j : Fin 3, ContDiffOn ℝ ∞
      (fun q : ℝ³ × ℝ => uLift j (c q.2) q.1) ((univ : Set ℝ³) ×ˢ Ici (0:ℝ))) :
    ContDiffOn ℝ ∞ (↿(vReal c)) (Set.univ ×ˢ Set.Ici 0) := by
  rw [contDiffOn_euclidean]
  intro j
  have h : ContDiffOn ℝ ∞
      ((Complex.reCLM ∘ (fun q : ℝ³ × ℝ => uLift j (c q.2) q.1)) ∘ clockCLM)
      ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) :=
    (Complex.reCLM.contDiff.comp_contDiffOn (h24 j)).comp clockCLM.contDiff.contDiffOn
      clockCLM_mapsTo
  exact h

/-- Clause 25 composed with `2π • Complex.reCLM` and the clock gives `pressure_smooth`. -/
theorem pressure_smooth_of_clause25 {c : ℝ → (Fin 3 → ℤ) → Vel}
    (h25 : ContDiffOn ℝ ∞
      (fun q : ℝ³ × ℝ => pLift (c q.2) q.1) ((univ : Set ℝ³) ×ˢ Ici (0:ℝ))) :
    ContDiffOn ℝ ∞ (↿(pReal c)) (Set.univ ×ˢ Set.Ici 0) := by
  have h : ContDiffOn ℝ ∞
      (((2 * Real.pi) • Complex.reCLM) ∘ (fun q : ℝ³ × ℝ => pLift (c q.2) q.1) ∘ clockCLM)
      ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) :=
    ((2 * Real.pi) • Complex.reCLM).contDiff.comp_contDiffOn
      (h25.comp clockCLM.contDiff.contDiffOn clockCLM_mapsTo)
  exact h

/-! ## The first chain element is the spectral right-hand side -/

/-- `D 1 = RHS(c)` on `Ici 0`: the recurrence at `n = 0` with `antidiagonal 0 = {(0,0)}`,
`choose 0 0 = 1` and `convBil_self`. -/
theorem chain_one_eq {ν : ℝ} {c : ℝ → (Fin 3 → ℤ) → Vel} {D S : ℕ → ℝ → (Fin 3 → ℤ) → Vel}
    (hD0 : D 0 = c)
    (hSdef : ∀ (n : ℕ) (t : ℝ) (k : Fin 3 → ℤ),
      S n t k = ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • convBil (D ij.1 t) (D ij.2 t) k)
    (hDrec : ∀ n : ℕ, ∀ t ∈ Ici (0:ℝ), ∀ k,
      D (n + 1) t k = (-(ν * ‖freq k‖ ^ 2)) • D n t k + lerayProj k (S n t k))
    {t : ℝ} (ht : t ∈ Ici (0:ℝ)) (k : Fin 3 → ℤ) :
    D 1 t k = (-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) := by
  have hS : S 0 t k = convFull (c t) k := by
    rw [hSdef, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp only [Nat.choose_zero_right, one_smul, hD0]
    rfl
  have h : D 1 t k = (-(ν * ‖freq k‖ ^ 2)) • D 0 t k + lerayProj k (S 0 t k) := hDrec 0 t ht k
  rw [h, hS, hD0]

/-! ## The bridges stated on `vReal` / `pReal` (the class's own shapes) -/

/-- `vReal_convection_apply` in the class's own shape `fderiv ℝ (v · τ) x (v x τ)`. -/
theorem vReal_convection_apply' (c : ℝ → (Fin 3 → ℤ) → Vel) (τ : ℝ)
    (h0 : Summable fun k => ‖c (2 * Real.pi * τ) k‖)
    (h1 : Summable fun k => ‖freq k‖ * ‖c (2 * Real.pi * τ) k‖) (x : ℝ³) (j : Fin 3) :
    (fderiv ℝ (fun y => vReal c y τ) x (vReal c x τ)) j
      = ∑ i : Fin 3, (uLift i (c (2 * Real.pi * τ)) x).re
          * (fderiv ℝ (uLift j (c (2 * Real.pi * τ))) x (EuclideanSpace.single i 1)).re :=
  vReal_convection_apply (c (2 * Real.pi * τ)) h0 h1 x j

/-- `vReal_laplacian_apply` in the class's own shape `Δ (v · τ) x`. -/
theorem vReal_laplacian_apply' (c : ℝ → (Fin 3 → ℤ) → Vel) (τ : ℝ)
    (h0 : Summable fun k => ‖c (2 * Real.pi * τ) k‖)
    (h1 : Summable fun k => ‖freq k‖ * ‖c (2 * Real.pi * τ) k‖)
    (h2 : Summable fun k => ‖freq k‖ ^ 2 * ‖c (2 * Real.pi * τ) k‖) (x : ℝ³) (j : Fin 3) :
    (Δ (fun y => vReal c y τ) x) j = (Δ (uLift j (c (2 * Real.pi * τ))) x).re :=
  vReal_laplacian_apply (c (2 * Real.pi * τ)) h0 h1 h2 x j

/-- `pReal_gradient_apply` in the class's own shape `gradient (p · τ) x`. -/
theorem pReal_gradient_apply' (c : ℝ → (Fin 3 → ℤ) → Vel) (τ : ℝ)
    (hp0 : Summable fun k => ‖pressureCoeff (c (2 * Real.pi * τ)) k‖)
    (hp1 : Summable fun k => ‖freq k‖ * ‖pressureCoeff (c (2 * Real.pi * τ)) k‖)
    (x : ℝ³) (j : Fin 3) :
    (gradient (fun y => pReal c y τ) x) j
      = (2 * Real.pi) * (fderiv ℝ (pLift (c (2 * Real.pi * τ))) x (EuclideanSpace.single j 1)).re :=
  pReal_gradient_apply (c (2 * Real.pi * τ)) hp0 hp1 x j

/-! ### The pinned capstone -/

/-- **THE PINNED CAPSTONE OF TIER 8b**: the twenty classical clauses of
`theorem_B_smooth_classical_eq`, verbatim, and clause 21: OUR COPY of the community class
`NavierStokesExistenceAndSmoothnessPeriodic (ν/(2π)) (u₀Real c₀) 0 (vReal c) (pReal c)`
is inhabited by the eternal flow `c` of the twenty clauses, in the clock `τ = t/(2π)`,
at `f = 0`.

`navier_stokes` is proved component by component: the time derivative is
`derivWithin_vReal_Ici` (clause 13 on `t > 0`; at `t = 0` the endpoint derivative
`hasDerivWithinAt_charSum_zero` fed by the chain of clause 21 through `chain_one_eq` and
the window majorant `WindowL1.majorant`), the convection, Laplacian and gradient are the
three bridges on the packed real fields, and the identity is
`navier_stokes_component_spectral` (clauses 18 and 19 and the `2π` arithmetic).
`div_free` is `divergence_uReal_eq_zero`; `initial_condition` is `2π·0 = 0` and
`c 0 = c₀`; `velocity_smooth`/`pressure_smooth` are clauses 24/25 composed with
`Complex.reCLM` and the clock CLM; periodicity is `isOnePeriodic_uLift`/`_pLift`.

The rest state is not a witness for nonzero data (`W3Probe.exists_nonzero_admissible_datum`
and `W3Probe.rest_pair_fails_class`, compiled); at `c₀ = 0` it is, as it must be.  The
class carries no uniqueness clause: uniqueness of the coefficient flow behind `vReal c` is
`theorem_B_unique`, whose hypothesis set is exactly clauses 1-7 of this pinned form.
`κ` is that of `theorem_B_joint_smooth`, of explicit form and exported as a compiled
existential; the window constants and majorants are untracked existentials.  The class is
inhabited for trap-class data at `f = 0` only and says nothing beyond that; the external
file is not imported; nothing here is new mathematics. -/
theorem theorem_B_community_periodic_flow :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,

        c 0 = c₀ ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) ∧
        -- every Sobolev level survives, for THIS one flow
        (∀ (m : ℕ), ∀ t ∈ Ici (0:ℝ),
          Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
        -- the flow stays mean-zero
        (∀ t ∈ Ici (0:ℝ), c t 0 = 0) ∧
        -- weighted ℓ¹ at every order
        (∀ t ∈ Ici (0:ℝ), ∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖c t l‖) ∧
        -- SPACE: the periodic lift is C^p for every p, and ℤ³-periodic
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (p : ℕ),
          ContDiff ℝ (p : ℕ∞) (uLift j (c t))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (g : Fin 3 → ℤ)
            (x : EuclideanSpace ℝ (Fin 3)),
          uLift j (c t) (x + freq g) = uLift j (c t) x) ∧
        -- TIME: the spectral Navier-Stokes equation, pointwise on the torus
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
          HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
            (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c t k
              + lerayProj k (convFull (c t) k)) j * mFourier k x) t) ∧
        -- C¹ IN TIME: that derivative is itself continuous on `t > 0`
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          ContinuousOn (fun s => ∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c s k
            + lerayProj k (convFull (c s) k)) j * mFourier k x) (Ioi (0:ℝ))) ∧
        -- the SECOND spatial fiber derivatives exist, with symbol (2πi·kᵢ)²
        (∀ t ∈ Ici (0:ℝ), ∀ (i j : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ),
          HasDerivAt
            (fun r : ℝ => ∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) * c t k j) •
              mFourier k (i.insertNth (↑r : UnitAddCircle) y))
            (∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) •
              mFourier k (i.insertNth (↑s : UnitAddCircle) y)) s) ∧
        -- CALIBRATION: the viscous term IS the Laplacian, scaled by ν/(2π)²
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (z : UnitAddTorus (Fin 3)),
          (∑' k, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c t k j) • mFourier k z)
            = ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
              (∑ i : Fin 3, ∑' k,
                ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k z)) ∧
        -- the PRESSURE is ℓ¹ (continuous) AND has one weighted order, so
        -- its gradient ∇p is a genuine object
        (∀ t ∈ Ici (0:ℝ), (Summable fun k => ‖pressureCoeff (c t) k‖) ∧
          Summable fun k => ‖freq k‖ * ‖pressureCoeff (c t) k‖) ∧
        -- the Leray projection is the convection MINUS a pressure gradient
        (∀ t ∈ Ici (0:ℝ), ∀ (k : Fin 3 → ℤ) (j : Fin 3),
          (lerayProj k (convFull (c t) k)) j
            = convFull (c t) k j
              - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k) ∧
        -- and the convection itself IS the classical (u·∇)u
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
              (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
                * mFourier m x))
            = ((-(2 * Real.pi) : ℝ) : ℂ) * ∑' k, convFull (c t) k j * mFourier k x) ∧
        -- THE CLASSICAL EQUATION, pointwise:
        --   ∂ₜu_j = (ν/(2π)²)·(Δu)_j − (1/2π)·((u·∇)u)_j − ∂_j p
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
          HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
            (((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
                (∑ i : Fin 3, ∑' k,
                  ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k x)
              - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
                  (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
                    * mFourier m x))
              - ∑' k, (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k
                  * mFourier k x) t) ∧
        -- 21. THE COMMUNITY CLASS, inhabited by this flow
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) (ν / (2 * Real.pi))
          (u₀Real c₀) (f := 0) (vReal c) (pReal c) := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_joint_smooth
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hall hmean0 hreal hdiv hsmall
  obtain ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl, hclassical,
    hchain21, hCinf, hpl1, h24, h25⟩ := H hν hall hmean0 hreal hdiv hsmall
  obtain ⟨D, S, hD0, hSdef, hDrec, hDder, hDzero, hDcont, hDwin, hSder, hScont, hSwin⟩ :=
    hchain21
  -- re-export clauses 1-20 verbatim; only the class remains
  refine ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl, hclassical, ?_⟩
  -- ℓ¹ certificates at every time (clause 10)
  have h0 : ∀ t ∈ Ici (0:ℝ), Summable fun k => ‖c t k‖ := fun t ht => by
    simpa using hl1 t ht 0
  have h1 : ∀ t ∈ Ici (0:ℝ), Summable fun k => ‖freq k‖ * ‖c t k‖ := fun t ht => by
    simpa using hl1 t ht 1
  have h2 : ∀ t ∈ Ici (0:ℝ), Summable fun k => ‖freq k‖ ^ 2 * ‖c t k‖ := fun t ht =>
    hl1 t ht 2
  have hτt : ∀ τ : ℝ, 0 ≤ τ → 2 * Real.pi * τ ∈ Ici (0:ℝ) := fun τ hτ =>
    mem_Ici.mpr (by positivity)
  -- the time-derivative data of `derivWithin_vReal_Ici`: clause 13 on `t > 0`,
  -- and the endpoint derivative at `0` from the chain and the W2 engine
  have hpos : ∀ (j : Fin 3) (x : ℝ³), ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (fun s => uLift j (c s) x)
        (uLift j (fun k => (-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) x)
        t :=
    fun j x t ht => htime j (fiber x) t ht
  have hzero : ∀ (j : Fin 3) (x : ℝ³),
      HasDerivWithinAt (fun s => uLift j (c s) x)
        (uLift j (fun k => (-(ν * ‖freq k‖ ^ 2)) • c 0 k + lerayProj k (convFull (c 0) k)) x)
        (Ici (0:ℝ)) 0 := by
    intro j x
    have hz : ∀ k, HasDerivWithinAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c 0 k + lerayProj k (convFull (c 0) k)) (Ici (0:ℝ)) 0 := by
      intro k
      have h := hDzero 0 k
      rw [chain_one_eq hD0 hSdef hDrec self_mem_Ici k, hD0] at h
      exact h
    obtain ⟨A, hA, -, hAle⟩ := WindowL1.majorant (hDwin 1 1)
    have hmaj : ∀ t ∈ Icc (0:ℝ) 1, ∀ k,
        ‖(-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)‖ ≤ A k := by
      intro t ht k
      rw [← chain_one_eq hD0 hSdef hDrec (mem_Ici.mpr ht.1) k]
      exact hAle t ht k
    exact hasDerivWithinAt_charSum_zero hz hode one_pos hA hmaj (h0 0 self_mem_Ici) j (fiber x)
  refine ⟨⟨?_, ?_, ?_, velocity_smooth_of_clause24 h24, pressure_smooth_of_clause25 h25⟩,
    ?_, ?_⟩
  · -- navier_stokes, component by component
    intro x τ hτ
    have ht := hτt τ hτ
    ext j
    rw [derivWithin_vReal_Ici hpos hzero x hτ]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Pi.zero_apply, add_zero,
      smul_eq_mul]
    rw [vReal_convection_apply' c τ (h0 _ ht) (h1 _ ht) x j,
      vReal_laplacian_apply' c τ (h0 _ ht) (h1 _ ht) (h2 _ ht) x j,
      pReal_gradient_apply' c τ (hpress _ ht).1 (hpress _ ht).2 x j]
    exact navier_stokes_component_spectral hν (hstruct _ ht).1 (hsum _ ht).1 (hsum _ ht).2
      (h0 _ ht) (h1 _ ht) (h2 _ ht) (hpress _ ht).1 (hpress _ ht).2 (hleray _ ht) (hnl _ ht) x j
  · -- div_free
    intro x t ht
    have ht' := hτt t ht
    exact divergence_uReal_eq_zero (hstruct _ ht').1 (hstruct _ ht').2 (h0 _ ht') (h1 _ ht') x
  · -- initial_condition: `2π·0 = 0` and `c 0 = c₀`
    intro x
    show (WithLp.toLp 2 fun j : Fin 3 => (uLift j (c (2 * Real.pi * 0)) x).re : ℝ³)
      = WithLp.toLp 2 fun j : Fin 3 => (uLift j c₀ x).re
    rw [mul_zero, hc0]
  · -- isOnePeriodic_velocity
    intro t _ x i
    show (WithLp.toLp 2 fun j : Fin 3 =>
        (uLift j (c (2 * Real.pi * t)) (x + EuclideanSpace.single i 1)).re : ℝ³)
      = WithLp.toLp 2 fun j : Fin 3 => (uLift j (c (2 * Real.pi * t)) x).re
    congr 1
    funext j
    rw [isOnePeriodic_uLift j _ x i]
  · -- isOnePeriodic_pressure
    intro t _ x i
    show (2 * Real.pi) * (pLift (c (2 * Real.pi * t)) (x + EuclideanSpace.single i 1)).re
      = (2 * Real.pi) * (pLift (c (2 * Real.pi * t)) x).re
    rw [isOnePeriodic_pLift _ x i]

/-! ### The bare capstone (the community's own shape) -/

/-- **THE BARE CAPSTONE OF TIER 8b**, in the community's own shape.  The proposed
announcement wording (blueprint section 7, rule 6; the user's call, not made here): "for
data in the campaign's small class, OUR copy of the community's periodic solution class
`NavierStokesExistenceAndSmoothnessPeriodic (ν/(2π)) u₀ 0 v p` is inhabited by the
eternal flow (compiled); this is the conclusion of the upstream positive statement
restricted to that data class with `f = 0`; both upstream statements are untouched."

Precisely: the upstream file carries the positive statement
`navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
`navier_stokes_breakdown_periodic`; this theorem is exactly the positive statement's
CONCLUSION restricted to the data class `u₀ = u₀Real c₀` with `κ·en c₀·ens c₀ < (2πν')⁴`
at `f = 0` (`ν' > 0` arbitrary); it says nothing about the positive statement for general
data and nothing about the breakdown statement; both upstream `sorry`s are untouched.
Existence only: the class has no uniqueness clause; uniqueness of the coefficient flow
behind `vReal c` is `theorem_B_unique` through clauses 1-7 of the pinned form.  The rest
state is not a witness for nonzero data (`W3Probe.rest_pair_fails_class`); at `c₀ = 0` it
is.  Proof: the pinned capstone at `ν := 2π·ν'` (the class at `(2πν')/(2π)` is the class
at `ν'`, `mul_div_cancel_left₀`), with `initialVelocityConditionPeriodic_u₀Real` and
`forceConditionPeriodic_zero`. -/
theorem theorem_B_community_periodic :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      κ * en c₀ * ens c₀ < (2 * Real.pi * ν') ^ 4 →
      InitialVelocityConditionPeriodic (n := 3) (u₀Real c₀) ∧
      ForceConditionPeriodic (n := 3) (f := 0) ∧
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real c₀)
          (f := 0) v p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_flow
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' c₀ hall hmean0 hreal hdiv hsmall
  have hν : 0 < 2 * Real.pi * ν' := by positivity
  obtain ⟨c, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hclass⟩ :=
    H hν hall hmean0 hreal hdiv hsmall
  refine ⟨initialVelocityConditionPeriodic_u₀Real hall hmean0 hreal hdiv,
    forceConditionPeriodic_zero, vReal c, pReal c, ?_⟩
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rwa [mul_div_cancel_left₀ _ h2π] at hclass

end

/-! ## 9. Probe section (non-frozen, registered): the capstones at work

Section 6b of the blueprint at capstone level: the bare capstone fires on a NONZERO
admissible datum for every `ν' > 0`; the rest velocity is not a witness whenever the real
datum is nonzero; and under `velocity_smooth` the class's `derivWithin`/`fderiv` are
genuine derivatives (SLICE GENUINENESS).  The time-constant witness for the bare class is
NOT probed (see the header). -/

namespace W4Probe

noncomputable section


/-- MUST INHABIT at capstone level: for every `ν' > 0` there is a NONZERO datum meeting
the community initial condition on which the bare capstone produces a member of the
class (`W3Probe.exists_nonzero_admissible_datum` at `κ` and `ν := 2πν'`). -/
theorem capstones_fire_on_nonzero_datum {ν' : ℝ} (hν' : 0 < ν') :
    ∃ c₀ : (Fin 3 → ℤ) → Vel, c₀ ≠ 0 ∧
      InitialVelocityConditionPeriodic (n := 3) (u₀Real c₀) ∧
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real c₀) (f := 0) v p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic
  have hν : 0 < 2 * Real.pi * ν' := by positivity
  obtain ⟨c₀, hne, hall, hmean0, hreal, hdiv, hsmall⟩ :=
    W3Probe.exists_nonzero_admissible_datum hκ hν
  obtain ⟨hinit, -, v, p, hclass⟩ := H hν' hall hmean0 hreal hdiv hsmall
  exact ⟨c₀, hne, hinit, v, p, hclass⟩

/-- MUST INHABIT with the datum EXPLICIT: for every `ν' > 0` the bare capstone fires on
the shear datum `testDatum ε` with `ε = 2πν'/(κ+3) ≠ 0`, whose real datum is nonzero, and
the rest velocity is not a witness for it (the W3 probe's arithmetic at `ν := 2πν'`). -/
theorem capstone_fires_on_testDatum {ν' : ℝ} (hν' : 0 < ν') :
    ∃ ε : ℝ, ε ≠ 0 ∧ u₀Real (W3Probe.testDatum ε) ≠ 0 ∧
      (∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
          (f := 0) v p) ∧
      ∀ p : ℝ³ → ℝ → ℝ,
        ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
          (f := 0) (fun _ _ => 0) p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic
  set r : ℝ := (2 * Real.pi * ν') / (κ + 3) with hr
  have hrpos : 0 < r := by positivity
  have hsmall : κ * en (W3Probe.testDatum r) * ens (W3Probe.testDatum r)
      < (2 * Real.pi * ν') ^ 4 := by
    show κ * en (W3Probe.pairDatum (W3Probe.probeVec r))
      * ens (W3Probe.pairDatum (W3Probe.probeVec r)) < (2 * Real.pi * ν') ^ 4
    rw [W3Probe.en_pairDatum, W3Probe.ens_pairDatum, W3Probe.norm_probeVec, sq_abs]
    have h1 : 4 * κ < (κ + 3) ^ 2 := by nlinarith [sq_nonneg (κ - 1)]
    have h2 : (κ + 3) ^ 2 ≤ (κ + 3) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hν4 : 0 < (2 * Real.pi * ν') ^ 4 := by positivity
    have hkey : κ * (2 * r ^ 2) * (2 * r ^ 2)
        = 4 * κ * (2 * Real.pi * ν') ^ 4 / (κ + 3) ^ 4 := by
      rw [hr]; field_simp; ring
    rw [hkey, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2) hν4]
  obtain ⟨-, -, v, p, hclass⟩ := H hν' (W3Probe.summable_wsq_pairDatum_all _)
    (W3Probe.pairDatum_zero_mode _) (W3Probe.realField_pairDatum_probeVec r)
    (W3Probe.divFree_pairDatum_probeVec r) hsmall
  exact ⟨r, hrpos.ne', W3Probe.u₀Real_testDatum_ne_zero hrpos.ne', ⟨v, p, hclass⟩,
    fun p => W3Probe.rest_pair_fails_class hrpos.ne' ν' 0 p⟩

/-- MUST FAIL: whenever the real datum is nonzero, the rest velocity fails the class's
`initial_condition` for every viscosity, force and pressure. -/
theorem rest_state_not_witness_of_ne_zero {c₀ : (Fin 3 → ℤ) → Vel} (h : u₀Real c₀ ≠ 0)
    (nu : ℝ) (f : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) :
    ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) nu (u₀Real c₀) f
        (fun _ _ => 0) p := by
  intro hc
  apply h
  funext x
  exact (hc.initial_condition x).symm

/-- MUST FAIL, against the capstone's own datum and force spelling: for the shear datum
`testDatum ε`, `ε ≠ 0`, the rest velocity is not a witness at `f := 0` for any `ν'`, `p`
(`W3Probe.rest_pair_fails_class` restated). -/
theorem rest_state_not_witness_for_nonzero {ε : ℝ} (hε : ε ≠ 0) (ν' : ℝ) (p : ℝ³ → ℝ → ℝ) :
    ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
        (f := 0) (fun _ _ => 0) p :=
  W3Probe.rest_pair_fails_class hε ν' 0 p

/-- SLICE GENUINENESS (time): under `velocity_smooth`, `t ↦ v x t` is differentiable
within `Ici 0` at every `t ≥ 0`, so the class's `derivWithin` is a genuine derivative. -/
theorem differentiableWithinAt_time_slice_of_velocity_smooth {v : ℝ³ → ℝ → ℝ³}
    (hv : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableWithinAt ℝ (v x ·) (Ici (0:ℝ)) t := by
  have hD : DifferentiableOn ℝ (↿v) ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) :=
    hv.differentiableOn (by simp)
  have hslice : DifferentiableWithinAt ℝ (fun s : ℝ => ((x, s) : ℝ³ × ℝ)) (Ici (0:ℝ)) t :=
    (DifferentiableAt.prodMk (differentiableAt_const _) differentiableAt_id).differentiableWithinAt
  have hmaps : MapsTo (fun s : ℝ => ((x, s) : ℝ³ × ℝ)) (Ici (0:ℝ))
      ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) := fun s hs => ⟨mem_univ _, hs⟩
  exact (hD (x, t) ⟨mem_univ _, ht⟩).comp t hslice hmaps

/-- SLICE GENUINENESS (space): under `velocity_smooth`, `x ↦ v x t` is differentiable at
every `x` for `t ≥ 0`, so the class's `fderiv` is a genuine derivative. -/
theorem differentiableAt_space_slice_of_velocity_smooth {v : ℝ³ → ℝ → ℝ³}
    (hv : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)) {t : ℝ} (ht : 0 ≤ t) (x : ℝ³) :
    DifferentiableAt ℝ (v · t) x := by
  have hD : DifferentiableOn ℝ (↿v) ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) :=
    hv.differentiableOn (by simp)
  have hslice : DifferentiableWithinAt ℝ (fun y : ℝ³ => ((y, t) : ℝ³ × ℝ)) univ x :=
    (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const _)).differentiableWithinAt
  have hmaps : MapsTo (fun y : ℝ³ => ((y, t) : ℝ³ × ℝ)) univ
      ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) := fun y _ => ⟨mem_univ _, ht⟩
  have h := (hD (x, t) ⟨mem_univ _, ht⟩).comp x hslice hmaps
  rw [differentiableWithinAt_univ] at h
  exact h

end

end W4Probe


/-! ## 10. Audit probe: the time-constant witness is excluded (blueprint 6b, the NOT-PROBED item)

For the BARE class on the nonzero shear datum `W3Probe.testDatum ε` the time-constant
velocity `v x t := u₀Real (testDatum ε) x` is NOT a witness, for every viscosity `ν' ≠ 0`
and every pressure `p`: its time derivative vanishes while `ν'·Δv` does not, and the
pressure gradient cannot compensate because `p` is one-periodic along `e₂` with a
constant line derivative there.  The hypothesis `ν' ≠ 0` is necessary (at `ν' = 0` the
stationary shear with `p = 0` is an Euler solution).  Proof by the W4 statement-shape
reader (probe `ShapeB.lean`, persisted in the session audit directory), landed verbatim;
it uses `laplacian_uLift`, `fderiv_uLift_single` and one-periodicity of the pressure, not
any symmetry of second derivatives.  Nothing here is new mathematics. -/

noncomputable section
namespace TimeConstantWitness

/-- the character, as in `uLift_eq_charSeries` -/
def cchar (k : Fin 3 → ℤ) (x : ℝ³) : ℂ :=
  ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))

lemma uLift_eq (j : Fin 3) (d : (Fin 3 → ℤ) → Vel) (x : ℝ³) :
    uLift j d x = ∑' k, d k j * cchar k x := rfl

def ccpe1 : Fin 3 → ℤ := ![1, 0, 0]

lemma ccpe1_ne_neg : ccpe1 ≠ -ccpe1 := by
  intro h
  have := congrFun h 0
  simp [ccpe1] at this

lemma ccpe1_one : ccpe1 1 = 0 := by simp [ccpe1]
lemma neg_ccpe1_one : (-ccpe1) 1 = 0 := by simp [ccpe1]

lemma norm_freq_ccpe1 : ‖freq ccpe1‖ = 1 := by
  rw [norm_freq]
  simp [ccpe1, Fin.sum_univ_three]

lemma norm_freq_neg_ccpe1 : ‖freq (-ccpe1)‖ = 1 := by
  rw [norm_freq]
  simp [ccpe1, Fin.sum_univ_three]

def ccBox : Finset (Fin 3 → ℤ) := {ccpe1, -ccpe1}

def ccVec (r : ℝ) : Vel := EuclideanSpace.single 1 (r : ℂ)

def ccPair (v : Vel) : (Fin 3 → ℤ) → Vel :=
  fun k => if k = ccpe1 ∨ k = -ccpe1 then v else 0

lemma ccPair_eq_zero {v : Vel} {k : Fin 3 → ℤ} (hk : k ∉ ccBox) : ccPair v k = 0 := by
  simp only [ccBox, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [ccPair, hk.1, hk.2]

/-- the W3 test datum IS the clone (definitional) -/
lemma testDatum_eq (ε : ℝ) : W3Probe.testDatum ε = ccPair (ccVec ε) := rfl

lemma summ0 (v : Vel) : Summable fun k => ‖ccPair v k‖ :=
  summable_of_ne_finset_zero (s := ccBox) fun k hk => by rw [ccPair_eq_zero hk, norm_zero]

lemma summ1 (v : Vel) : Summable fun k => ‖freq k‖ * ‖ccPair v k‖ :=
  summable_of_ne_finset_zero (s := ccBox) fun k hk => by
    rw [ccPair_eq_zero hk, norm_zero, mul_zero]

lemma summ2 (v : Vel) : Summable fun k => ‖freq k‖ ^ 2 * ‖ccPair v k‖ :=
  summable_of_ne_finset_zero (s := ccBox) fun k hk => by
    rw [ccPair_eq_zero hk, norm_zero, mul_zero]

lemma pair_tsum (w : (Fin 3 → ℤ) → ℂ) (v : Vel) (j : Fin 3) (x : ℝ³) :
    ∑' k, w k * ccPair v k j * cchar k x
      = (w ccpe1 * cchar ccpe1 x + w (-ccpe1) * cchar (-ccpe1) x) * v j := by
  have hsupp : ∀ k ∉ ccBox, w k * ccPair v k j * cchar k x = 0 := by
    intro k hk
    rw [ccPair_eq_zero hk]
    simp
  rw [tsum_eq_sum hsupp]
  simp only [ccBox]
  rw [Finset.sum_pair ccpe1_ne_neg]
  simp [ccPair, ccpe1_ne_neg, ccpe1_ne_neg.symm]
  ring

lemma uLift_pair (v : Vel) (j : Fin 3) (x : ℝ³) :
    uLift j (ccPair v) x = (cchar ccpe1 x + cchar (-ccpe1) x) * v j := by
  rw [uLift_eq]
  have := pair_tsum (fun _ => 1) v j x
  simp only [one_mul] at this
  rw [this]

lemma ccVec_apply (r : ℝ) (j : Fin 3) : (ccVec r) j = if j = 1 then (r : ℂ) else 0 := by
  simp [ccVec, EuclideanSpace.single_apply]

lemma uLift_pair_ne_one (r : ℝ) (j : Fin 3) (hj : j ≠ 1) (x : ℝ³) :
    uLift j (ccPair (ccVec r)) x = 0 := by
  rw [uLift_pair, ccVec_apply, if_neg hj, mul_zero]

lemma fderiv_pair_single_one (v : Vel) (j : Fin 3) (x : ℝ³) :
    fderiv ℝ (uLift j (ccPair v)) x (EuclideanSpace.single 1 1) = 0 := by
  rw [fderiv_uLift_single 1 j (ccPair v) (summ0 v) (summ1 v) x]
  have := pair_tsum (fun k => 2 * Real.pi * Complex.I * ((k 1 : ℤ) : ℂ)) v j x
  simp only [cchar] at this
  rw [this]
  simp [ccpe1_one]

lemma laplacian_pair (v : Vel) (j : Fin 3) (x : ℝ³) :
    Δ (uLift j (ccPair v)) x = ((-((2 * Real.pi) ^ 2) : ℝ) : ℂ) * uLift j (ccPair v) x := by
  rw [laplacian_uLift j (ccPair v) (summ0 v) (summ1 v) (summ2 v) x, uLift_pair]
  have := pair_tsum (fun k => (((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) : ℝ) : ℂ)) v j x
  simp only [cchar] at this ⊢
  rw [this, norm_freq_ccpe1, norm_freq_neg_ccpe1]
  push_cast
  ring

lemma cchar_shift (k : Fin 3 → ℤ) (hk : k 1 = 0) (x : ℝ³) (s : ℝ) :
    cchar k (x + s • EuclideanSpace.single 1 1) = cchar k x := by
  unfold cchar
  rw [char_line]
  simp [hk]

lemma uLift_pair_line (v : Vel) (j : Fin 3) (s : ℝ) :
    uLift j (ccPair v) (s • EuclideanSpace.single 1 1) = uLift j (ccPair v) 0 := by
  have h := congrArg (uLift j (ccPair v)) (zero_add (s • EuclideanSpace.single 1 (1:ℝ) : ℝ³))
  rw [← h, uLift_pair, uLift_pair, cchar_shift _ ccpe1_one, cchar_shift _ neg_ccpe1_one]

/-- the two W4 bridges, restated on `u₀Real` (definitional) -/
lemma conv_U (v : Vel) (y : ℝ³) (j : Fin 3) :
    (fderiv ℝ (fun x => u₀Real (ccPair v) x) y (u₀Real (ccPair v) y)) j
      = ∑ i : Fin 3, (uLift i (ccPair v) y).re
          * (fderiv ℝ (uLift j (ccPair v)) y (EuclideanSpace.single i 1)).re :=
  vReal_convection_apply (ccPair v) (summ0 v) (summ1 v) y j

lemma lap_U (v : Vel) (y : ℝ³) (j : Fin 3) :
    (Δ (fun x => u₀Real (ccPair v) x) y) j = (Δ (uLift j (ccPair v)) y).re :=
  vReal_laplacian_apply (ccPair v) (summ0 v) (summ1 v) (summ2 v) y j

lemma conv_zero (r : ℝ) (y : ℝ³) (j : Fin 3) :
    (fderiv ℝ (fun x => u₀Real (ccPair (ccVec r)) x) y (u₀Real (ccPair (ccVec r)) y)) j = 0 := by
  rw [conv_U, Fin.sum_univ_three, uLift_pair_ne_one r 0 (by decide) y,
    uLift_pair_ne_one r 2 (by decide) y, fderiv_pair_single_one]
  simp

lemma pressure_slice {p : ℝ³ → ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)) {t : ℝ} (ht : 0 ≤ t) (x : ℝ³) :
    DifferentiableAt ℝ (fun y => p y t) x := by
  have h2 : DifferentiableWithinAt ℝ (↿p) ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) (x, t) :=
    (hp (x, t) ⟨mem_univ _, ht⟩).differentiableWithinAt (by simp)
  have hs : DifferentiableWithinAt ℝ (fun y : ℝ³ => ((y, t) : ℝ³ × ℝ)) univ x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).differentiableWithinAt
  have hm : MapsTo (fun y : ℝ³ => ((y, t) : ℝ³ × ℝ)) univ
      ((univ : Set ℝ³) ×ˢ Ici (0:ℝ)) := fun y _ => ⟨mem_univ _, ht⟩
  have h3 : DifferentiableWithinAt ℝ ((↿p) ∘ fun y : ℝ³ => ((y, t) : ℝ³ × ℝ)) univ x :=
    h2.comp x hs hm
  rw [differentiableWithinAt_univ] at h3
  exact h3

/-- MUST FAIL: the time-constant witness on the shear datum, for every `ν' ≠ 0` and every `p`. -/
theorem const_witness_fails {ε : ℝ} (hε : ε ≠ 0) {ν' : ℝ} (hν' : ν' ≠ 0) (p : ℝ³ → ℝ → ℝ) :
    ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
        (f := 0) (fun x _ => u₀Real (W3Probe.testDatum ε) x) p := by
  rw [testDatum_eq]
  intro hc
  have hpdiff : ∀ y : ℝ³, DifferentiableAt ℝ (fun x => p x 0) y :=
    fun y => pressure_slice hc.pressure_smooth le_rfl y
  have h2ε : uLift 1 (ccPair (ccVec ε)) 0 = 2 * (ε : ℂ) := W3Probe.uLift_testDatum_zero ε
  -- the e₂-component of the pressure gradient along the line `s·e₂` is the constant `A`
  have hA : ∀ s : ℝ,
      fderiv ℝ (fun x => p x 0) (s • EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)
        = -ν' * (2 * Real.pi) ^ 2 * (uLift 1 (ccPair (ccVec ε)) 0).re := by
    intro s
    have heq := hc.navier_stokes (s • EuclideanSpace.single 1 1) 0 le_rfl
    simp only [derivWithin_fun_const, Pi.zero_apply, zero_add, add_zero] at heq
    have h1 := congrArg (fun w : ℝ³ => w 1) heq
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1
    rw [conv_zero, lap_U, laplacian_pair, Complex.re_ofReal_mul, uLift_pair_line,
      gradient_apply_eq_fderiv_single (hpdiff _) 1] at h1
    linarith
  -- the line function has constant derivative `A`, and is one-periodic: `A = 0`
  set A : ℝ := -ν' * (2 * Real.pi) ^ 2 * (uLift 1 (ccPair (ccVec ε)) 0).re with hAdef
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => p (s • EuclideanSpace.single 1 1) 0) A s := by
    intro s
    have hline : HasDerivAt (fun s : ℝ => (s • EuclideanSpace.single 1 (1:ℝ) : ℝ³))
        (EuclideanSpace.single 1 1) s := by
      simpa using (hasDerivAt_id' s).smul_const (EuclideanSpace.single 1 (1:ℝ) : ℝ³)
    have hp := (hpdiff (s • EuclideanSpace.single 1 1)).hasFDerivAt
    have := hp.comp_hasDerivAt s hline
    rw [hA s] at this
    exact this
  have hdiff : Differentiable ℝ (fun s : ℝ => p (s • EuclideanSpace.single 1 1) 0 - A * s) :=
    fun s => ((hg s).sub ((hasDerivAt_id' s).const_mul A)).differentiableAt
  have hzero : ∀ s : ℝ, deriv (fun s : ℝ => p (s • EuclideanSpace.single 1 1) 0 - A * s) s = 0 := by
    intro s
    have h : HasDerivAt (fun s : ℝ => p (s • EuclideanSpace.single 1 1) 0 - A * s) (A - A * 1) s :=
      (hg s).sub ((hasDerivAt_id' s).const_mul A)
    rw [h.deriv]
    ring
  have h10 := is_const_of_deriv_eq_zero hdiff hzero 1 0
  simp only [one_smul, zero_smul, mul_one, mul_zero, sub_zero] at h10
  have hper := hc.isOnePeriodic_pressure 0 le_rfl 0 1
  simp only [zero_add] at hper
  have hA0 : A = 0 := by linarith
  rw [hAdef, h2ε] at hA0
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hA0
  have hne : -ν' * (2 * Real.pi) ^ 2 * (2 * ε) ≠ 0 := by
    have hπ : (2 * Real.pi) ^ 2 ≠ 0 := pow_ne_zero _ (by positivity)
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hν') hπ) (mul_ne_zero two_ne_zero hε)
  apply hne
  simpa using hA0

end TimeConstantWitness

end

end TheoremB
