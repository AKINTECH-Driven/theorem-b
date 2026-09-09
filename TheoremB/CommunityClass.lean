/-
  TheoremB/CommunityClass.lean
  Tier 8b, wave W3 (Theorem B campaign, 9 Sep 2026): OUR COPY of the community
  solution class, and the datum-side bridge into it.  Part 1 of the file; wave
  W4 appends the clock-transported derivative lemmas
  (`hasDerivWithinAt_charSum_zero`, `derivWithin_vReal_Ici`) and the two
  capstones (`theorem_B_community_periodic_flow`, `theorem_B_community_periodic`)
  to this same file.

  WHAT IS DELIVERED HERE.
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
  * A registered probe section (non-frozen, section 6b of the blueprint): the
    nonzero shear datum `testDatum ε` meets every capstone hypothesis
    (`exists_nonzero_admissible_datum`), its lift is nonzero
    (`uLift_testDatum_zero`, `u₀Real_testDatum_ne_zero`), the rest pair is not
    a witness of the class for it (`rest_pair_fails_class`), and the
    time-constant coefficient flow fails the mode equation
    (`const_flow_fails_ode`).

  HONEST SCOPE.  Nothing is inhabited in this wave: no theorem here produces a
  member of `NavierStokesExistenceAndSmoothnessPeriodic`; that is W4's work.
  The upstream file carries the positive statement
  `navier_stokes_existence_and_smoothness_periodic` and the breakdown
  statement `navier_stokes_breakdown_periodic`; this file touches neither and
  says nothing about either.  The real-part bridge and the clock change are
  textbook; nothing here is new mathematics.  Smoothness means `C^∞` with
  `∞ = (⊤ : ℕ∞)`; analyticity is not claimed.  Private declarations of frozen
  files (PeriodicLift's term lemmas, NSGalerkin/RealityProp's `conjVel`/`dotR`
  algebra, TimeSmooth's `norm_convTerm_le`, ForcedProbe's pair-mode datum) are
  CLONED here with a `cc` prefix, never un-privated.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.JointSmooth

open Set Filter Topology MeasureTheory InnerProductSpace UnitAddTorus
open scoped ContDiff Laplacian
local notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace TheoremB

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

end TheoremB
