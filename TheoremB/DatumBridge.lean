/-
  TheoremB/DatumBridge.lean
  Tier 9, wave W1 (Theorem B campaign, 13 Sep 2026): the coefficient field
  of a real-space velocity datum, its decay and summability certificates at
  every order, reality, divergence-freeness, the round trip, the inversion,
  and the W1 capstone `datum_bridge`.  Transcribed from section B of the
  design probe `audit-tier9/design/final/Tier9Final.lean` (session directory,
  never a tracked file; compiled there at the pin, exit 0; section B has no
  declaration with a placeholder proof, the probe's only two being the W3
  candidates of its section F, not transcribed); the frozen statements are those of
  `context/rung11-tier9-blueprint.md` section 4a (the DatumBridge block),
  byte-identical, and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * The coefficient field `coeff u : (Fin 3 → ℤ) → Vel`: the componentwise
    Fourier coefficients of the descent (Descent.lean) of each complexified
    component of `u`, packed by `WithLp.toLp 2`; `coeff_apply` is `rfl`;
    `contDiff_ofReal_component` and `isOnePeriodic_ofReal_component` carry
    smoothness and one-periodicity to the complexified components.
  * The sup bound and the decay (B1): `exists_bound_mFourierCoeff_descend`
    (bounded coefficients for a continuous one-periodic scalar field),
    `exists_bound_coeff_mul_norm_freq_pow` (decay at every order `q`,
    `‖ĉ n‖ ‖freq n‖^q ≤ C_q`, from the iterated bridge of Descent.lean and
    a coordinate bound `‖freq n‖ ≤ √3 |nᵢ|` for some `i`, the helper
    `exists_coord_norm_freq_le` read off SpectralNorms' `natMax` bound), and the
    two summability certificates `summable_norm_freq_pow_mul_coeff` (weighted
    ℓ¹ at every order) and `summable_norm_freq_pow_mul_coeff_sq` (every
    Sobolev level), by comparison with `C · ‖freq n‖^(-4)` off the zero mode.
  * The `Vel`-packed certificates (B2):
    `exists_bound_coeff_vel_mul_norm_freq_pow`, `summable_weight_coeff` and
    `summable_sob_coeff`: the same three facts for `coeff u`, through the
    packing bound `‖toLp 2 f‖ ≤ √3 · M` when every `‖f j‖ ≤ M`.
  * Reality and divergence (B3): `realField_coeff`, UNCONDITIONAL (every
    real field `u` has a conjugate-symmetric coefficient field, because its
    complexified components are real-valued pointwise; for a non-integrable
    descent the coefficient is the junk value `0` and `0 = conj 0`), and
    `divFree_coeff` (the class's pointwise `divergence u = 0` gives
    `DivFree (coeff u)`: the bridge at order one, summed over the components,
    then `2πi ≠ 0`).
  * The round trip, periodicity and the inversion (B4): `coeff_u₀Real`
    (`coeff (u₀Real c) = c` for a real ℓ¹ family), `isOnePeriodic_u₀Real`
    (the real datum of any coefficient family is one-periodic), and
    `u₀Real_coeff`: a `C^∞` one-periodic real field IS the real datum of its
    coefficient field.  Route: Mathlib's pointwise inversion for a continuous
    torus function with summable coefficients
    (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`), the
    summability being the decay at order `p = 0`, and `descend_fiber` reading
    the torus value back at `fiber x`.
  * THE W1 CAPSTONE `datum_bridge`: for every `u` in the community's own
    `InitialVelocityConditionPeriodic (n := 3)` (CommunityClass.lean, our
    copy), the coefficient field `coeff u` has weighted ℓ¹ at every order and
    every Sobolev level, is real, is divergence-free, and
    `u₀Real (coeff u) = u`.  It is the conjunction of the five lemmas above at
    `hu.smooth`, `hu.isOnePeriodic`, `hu.div_free`.

  HONEST SCOPE.
  * Nothing here is new mathematics: the rapid decay of the Fourier
    coefficients of a smooth periodic function and the pointwise Fourier
    inversion are textbook; Mathlib supplies the inversion for continuous
    functions with summable coefficients at the pin; the deliverable is the
    machine-checked bridge from the community's datum vocabulary to the
    campaign's coefficient vocabulary.
  * Constants: the decay constants `C_q` and the sup bounds `M` are UNTRACKED
    existentials produced by `choose`; the `√3` and `(√3/2π)^q` factors are
    literal expressions.  No numeric value of any constant is claimed.
  * `coeff` is total; for a `u` outside `ContDiff ℝ ∞ u ∧ IsOnePeriodic u` (or
    the class) it is a well-typed junk object, and the inversion
    `u₀Real (coeff u) = u` is NOT unconditional (the blueprint's section 6
    register, landing in W2, carries its failure on the identity field
    `fun x => x`, compiled in the design probe).  Every lemma asserting a
    property of `coeff u` for a general `u` carries those two hypotheses or
    the class, except the definitional unfolding `coeff_apply` and the
    unconditional `realField_coeff`.
  * The datum bridge says nothing about any solution of the equations: it is
    the datum-side input of the Tier 9 capstone (W2, CommunityData.lean, not
    built here), which is the conclusion of the upstream positive statement
    `navier_stokes_existence_and_smoothness_periodic` under a smallness
    hypothesis on the mean-free part of the datum's coefficient field, at
    `f = 0`.  Nothing here touches that statement, the breakdown statement
    `navier_stokes_breakdown_periodic`, or either upstream placeholder
    proof; existence only, uniqueness of the coefficient flow being
    `theorem_B_unique`.
    Priority is not claimed for anything.
  * This file edits no earlier file of the tree and clones no private lemma:
    the probe it is transcribed from compiled against the imported tree, so
    every declaration consumed here is public in its file (Descent,
    SpectralNorms, NSGalerkin, PeriodicLift, TorusStructure, CommunityClass,
    Mathlib).  The eight helper lemmas (`norm_twoPiI_mul`,
    `exists_coord_norm_freq_le`, `exists_bound_coeff_mul_absCoord_pow`,
    `norm_freq_zero_rpow_neg_four`, `norm_toLp_le_sqrt3_mul`,
    `summable_vel_of_components`, `dirDeriv_ofReal_component`,
    `sum_dirDeriv_component_eq_divergence`) are shipped public and carry no
    ledger line.

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances anonymously;
  here they are NAMED `db_ms`, `db_haar`, `db_prob` (Descent.lean uses
  `ds_*`; the tree's torus files use `cr_*`, `tsyn_*`, `ts_*`, `ce_*`),
  because auto-named local instances from two modules collide in a third
  module that imports both.  The bodies are the three-line block of
  FourierDeriv.lean lines 31-37.  Instances are not statements; every frozen
  statement is byte-identical to the blueprint.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.Descent

open Set Filter Topology MeasureTheory InnerProductSpace UnitAddTorus
open scoped ContDiff Laplacian ComplexConjugate

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace TheoremB

open Community

noncomputable section

-- The three local instances: the three-line block of TheoremB/FourierDeriv.lean lines 31-37
-- with a file-unique name inserted (torus integrals; local instances are not exported, every
-- torus file of the tree declares its own, NAMED, so that two modules' instances never collide
-- in a third module that imports both).
local instance db_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance db_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance db_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **The coefficient field of a real-space velocity field**: componentwise Fourier
coefficients of the descent of each complexified component, packed into `Vel`.
(R3's `coeffOf`, R6's `coeff`; ONE canonical name.) -/
def coeff (u : ℝ³ → ℝ³) (n : Fin 3 → ℤ) : Vel :=
  WithLp.toLp 2 fun j => mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n

/-- Unfolding `coeff` componentwise (`rfl`): the `j`-th component is the coefficient of the
descent of the complexified `j`-th component of `u`. -/
theorem coeff_apply (u : ℝ³ → ℝ³) (n : Fin 3 → ℤ) (j : Fin 3) :
    coeff u n j = mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n := rfl

/-- The complexified `j`-th component of a `C^∞` real field is `C^∞` (`Complex.ofRealCLM`
after `EuclideanSpace.proj j`). -/
theorem contDiff_ofReal_component {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => ((u x j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu)

/-- The complexified `j`-th component of a one-periodic real field is one-periodic. -/
theorem isOnePeriodic_ofReal_component {u : ℝ³ → ℝ³} (hp : IsOnePeriodic u) (j : Fin 3) :
    IsOnePeriodic (fun x => ((u x j : ℝ) : ℂ)) := by
  intro x i
  simp only [hp x i]

/-! ## B1. The sup bound and the decay (R3 sections 3-5) -/

/-- The coefficients of the descent of a continuous one-periodic scalar field are bounded;
the bound is the sup norm of the bundled descent, an UNTRACKED existential (rule 1 of
the blueprint's section 7).  The hypotheses are those of its consumers: the bound itself
holds for every `g`, the sup norm being replaced by the L¹ norm of the descent, `0` when
not integrable (reader probe `ShapeW1.exists_bound_mFourierCoeff_descend_unconditional`,
session directory `build-w1/reader-shape/`). -/
theorem exists_bound_mFourierCoeff_descend {g : ℝ³ → ℂ} (hg : Continuous g)
    (hp : IsOnePeriodic g) :
    ∃ M : ℝ, ∀ n : Fin 3 → ℤ, ‖mFourierCoeff (descend g) n‖ ≤ M := by
  let G : C(UnitAddTorus (Fin 3), ℂ) := ⟨descend g, continuous_descend hg hp⟩
  exact ⟨‖G‖, fun n => norm_mFourierCoeff_le G n⟩

lemma norm_twoPiI_mul (m : ℤ) :
    ‖(2 * Real.pi * Complex.I * (m : ℂ))‖ = 2 * Real.pi * |(m : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_two,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]

lemma exists_coord_norm_freq_le (n : Fin 3 → ℤ) :
    ∃ i : Fin 3, ‖freq n‖ ≤ Real.sqrt 3 * |(n i : ℝ)| := by
  obtain ⟨i, -, hsup⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3)) Finset.univ_nonempty
      (fun j => (n j).natAbs)
  refine ⟨i, ?_⟩
  have h := norm_freq_le_sqrt3_mul_natMax n
  have hsup' : natMax n = (n i).natAbs := hsup
  rw [hsup'] at h
  have hcast : ((n i).natAbs : ℝ) = |(n i : ℝ)| := by
    calc ((n i).natAbs : ℝ) = (((n i).natAbs : ℤ) : ℝ) := by simp only [Int.cast_natCast]
      _ = |(n i : ℝ)| := by simp only [Int.natCast_natAbs, Int.cast_abs]
  rw [hcast] at h
  exact h

theorem exists_bound_coeff_mul_absCoord_pow {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : Fin 3 → ℤ) (i : Fin 3),
      ‖mFourierCoeff (descend f) n‖ * (2 * Real.pi * |(n i : ℝ)|) ^ q ≤ M := by
  have hbd : ∀ i : Fin 3, ∃ M : ℝ, ∀ n, ‖mFourierCoeff (descend (dirIter i q f)) n‖ ≤ M :=
    fun i => exists_bound_mFourierCoeff_descend (contDiff_dirIter i hf q).continuous
      (dirIter_isOnePeriodic i hp q)
  choose M hM using hbd
  have hM0 : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i 0)
  refine ⟨∑ i, M i, Finset.sum_nonneg fun i _ => hM0 i, fun n i => ?_⟩
  have key : ‖mFourierCoeff (descend (dirIter i q f)) n‖ =
      ‖mFourierCoeff (descend f) n‖ * (2 * Real.pi * |(n i : ℝ)|) ^ q := by
    rw [mFourierCoeff_descend_dirIter i hf hp q n, norm_mul, norm_pow, norm_twoPiI_mul, mul_comm]
  calc ‖mFourierCoeff (descend f) n‖ * (2 * Real.pi * |(n i : ℝ)|) ^ q
      = ‖mFourierCoeff (descend (dirIter i q f)) n‖ := key.symm
    _ ≤ M i := hM i n
    _ ≤ ∑ j, M j := Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_univ i)

/-- **Rapid decay, npow form, all `n`**: `‖ĉ n‖ ‖freq n‖^q ≤ C_q` for smooth periodic `f`. -/
theorem exists_bound_coeff_mul_norm_freq_pow {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ, ‖mFourierCoeff (descend f) n‖ * ‖freq n‖ ^ q ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_coeff_mul_absCoord_pow hf hp q
  refine ⟨(Real.sqrt 3 / (2 * Real.pi)) ^ q * M, by positivity, fun n => ?_⟩
  obtain ⟨i, hi⟩ := exists_coord_norm_freq_le n
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfreq : ‖freq n‖ ^ q ≤
      (Real.sqrt 3 / (2 * Real.pi)) ^ q * (2 * Real.pi * |(n i : ℝ)|) ^ q := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc ‖freq n‖ ≤ Real.sqrt 3 * |(n i : ℝ)| := hi
      _ = Real.sqrt 3 / (2 * Real.pi) * (2 * Real.pi * |(n i : ℝ)|) := by
        field_simp
  calc ‖mFourierCoeff (descend f) n‖ * ‖freq n‖ ^ q
      ≤ ‖mFourierCoeff (descend f) n‖ *
          ((Real.sqrt 3 / (2 * Real.pi)) ^ q * (2 * Real.pi * |(n i : ℝ)|) ^ q) :=
        mul_le_mul_of_nonneg_left hfreq (norm_nonneg _)
    _ = (Real.sqrt 3 / (2 * Real.pi)) ^ q *
          (‖mFourierCoeff (descend f) n‖ * (2 * Real.pi * |(n i : ℝ)|) ^ q) := by ring
    _ ≤ (Real.sqrt 3 / (2 * Real.pi)) ^ q * M :=
        mul_le_mul_of_nonneg_left (hM n i) (by positivity)

lemma norm_freq_zero_rpow_neg_four : ‖freq (0 : Fin 3 → ℤ)‖ ^ (-4 : ℝ) = 0 := by
  have h0 : freq (0 : Fin 3 → ℤ) = 0 := by
    ext i; simp [freq]
  rw [h0, norm_zero, Real.zero_rpow (by norm_num)]

/-- Every polynomial weight against the (scalar) coefficient norms is summable. -/
theorem summable_norm_freq_pow_mul_coeff {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (p : ℕ) :
    Summable fun n : Fin 3 → ℤ => ‖freq n‖ ^ p * ‖mFourierCoeff (descend f) n‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_coeff_mul_norm_freq_pow hf hp (p + 4)
  have hs : Summable fun n : Fin 3 → ℤ => C * ‖freq n‖ ^ (-4 : ℝ) :=
    (summable_norm_freq_rpow (r := -4) (by norm_num)).mul_left C
  refine Summable.of_norm_bounded_eventually hs ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : Fin 3 → ℤ)).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hn0
  apply hn
  have h1 : 1 ≤ ‖freq n‖ := one_le_norm_freq hn0
  have hpos : 0 < ‖freq n‖ := lt_of_lt_of_le one_pos h1
  rw [Real.norm_of_nonneg (by positivity), show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc ‖freq n‖ ^ p * ‖mFourierCoeff (descend f) n‖ * ‖freq n‖ ^ 4
      = ‖mFourierCoeff (descend f) n‖ * ‖freq n‖ ^ (p + 4) := by ring
    _ ≤ C := hC n

/-- Every polynomial weight against the SQUARED scalar coefficient norms is summable: one
factor is absorbed by the sup bound, the other is the weighted ℓ¹ certificate at order
`2 * m`. -/
theorem summable_norm_freq_pow_mul_coeff_sq {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (m : ℕ) :
    Summable fun n : Fin 3 → ℤ => ‖freq n‖ ^ (2 * m) * ‖mFourierCoeff (descend f) n‖ ^ 2 := by
  obtain ⟨M, hM⟩ := exists_bound_mFourierCoeff_descend hf.continuous hp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hs := (summable_norm_freq_pow_mul_coeff hf hp (2 * m)).mul_left M
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  calc ‖freq n‖ ^ (2 * m) * ‖mFourierCoeff (descend f) n‖ ^ 2
      = ‖freq n‖ ^ (2 * m) * ‖mFourierCoeff (descend f) n‖ * ‖mFourierCoeff (descend f) n‖ := by
        ring
    _ ≤ ‖freq n‖ ^ (2 * m) * ‖mFourierCoeff (descend f) n‖ * M :=
        mul_le_mul_of_nonneg_left (hM n) (by positivity)
    _ = M * (‖freq n‖ ^ (2 * m) * ‖mFourierCoeff (descend f) n‖) := by ring

/-! ## B2. The `Vel`-packed certificates (glue; R1's `norm_coeffVel_le` pattern) -/

lemma norm_toLp_le_sqrt3_mul {f : Fin 3 → ℂ} {M : ℝ} (hM : ∀ j, ‖f j‖ ≤ M) :
    ‖(WithLp.toLp 2 f : Vel)‖ ≤ Real.sqrt 3 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ j, ‖(WithLp.toLp 2 f : Vel) j‖ ^ 2 ≤ ∑ _j : Fin 3, M ^ 2 :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hM j) 2
  have h2 : ∑ _j : Fin 3, M ^ 2 = 3 * M ^ 2 := by simp
  calc Real.sqrt (∑ j, ‖(WithLp.toLp 2 f : Vel) j‖ ^ 2)
      ≤ Real.sqrt (3 * M ^ 2) := Real.sqrt_le_sqrt (h1.trans h2.le)
    _ = Real.sqrt 3 * M := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hM0]

/-- Rapid decay of the packed coefficient field, all `n`. -/
theorem exists_bound_coeff_vel_mul_norm_freq_pow {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u)
    (hp : IsOnePeriodic u) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ, ‖coeff u n‖ * ‖freq n‖ ^ q ≤ C := by
  have hbd : ∀ j : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n‖ * ‖freq n‖ ^ q ≤ C :=
    fun j => exists_bound_coeff_mul_norm_freq_pow (contDiff_ofReal_component hu j)
      (isOnePeriodic_ofReal_component hp j) q
  choose C hC0 hC using hbd
  refine ⟨Real.sqrt 3 * ∑ j, C j,
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => hC0 j), fun n => ?_⟩
  have hfq : 0 ≤ ‖freq n‖ ^ q := by positivity
  have hsm : (‖freq n‖ ^ q) • coeff u n = (WithLp.toLp 2 fun j =>
      ((‖freq n‖ ^ q : ℝ) : ℂ) * mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n : Vel) := by
    ext j
    simp only [coeff, PiLp.smul_apply, Complex.real_smul]
  calc ‖coeff u n‖ * ‖freq n‖ ^ q = ‖(‖freq n‖ ^ q) • coeff u n‖ := by
        rw [norm_smul, Real.norm_of_nonneg hfq, mul_comm]
    _ ≤ Real.sqrt 3 * ∑ j, C j := by
        rw [hsm]
        refine norm_toLp_le_sqrt3_mul fun j => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hfq, mul_comm]
        exact (hC j n).trans (Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ j))

/-- **Weighted ℓ¹ at every order** for the coefficient field of a smooth periodic datum. -/
theorem summable_weight_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (p : ℕ) : Summable fun l => ‖freq l‖ ^ p * ‖coeff u l‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_coeff_vel_mul_norm_freq_pow hu hp (p + 4)
  have hs : Summable fun n : Fin 3 → ℤ => C * ‖freq n‖ ^ (-4 : ℝ) :=
    (summable_norm_freq_rpow (r := -4) (by norm_num)).mul_left C
  refine Summable.of_norm_bounded_eventually hs ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : Fin 3 → ℤ)).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hn0
  apply hn
  have h1 : 1 ≤ ‖freq n‖ := one_le_norm_freq hn0
  have hpos : 0 < ‖freq n‖ := lt_of_lt_of_le one_pos h1
  rw [Real.norm_of_nonneg (by positivity), show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc ‖freq n‖ ^ p * ‖coeff u n‖ * ‖freq n‖ ^ 4
      = ‖coeff u n‖ * ‖freq n‖ ^ (p + 4) := by ring
    _ ≤ C := hC n

theorem summable_vel_of_components {c : (Fin 3 → ℤ) → Vel} (m : ℕ)
    (h : ∀ j : Fin 3, Summable fun n => ‖freq n‖ ^ (2 * m) * ‖c n j‖ ^ 2) :
    Summable fun n => ‖freq n‖ ^ (2 * m) * ‖c n‖ ^ 2 := by
  have hfun : (fun n : Fin 3 → ℤ => ‖freq n‖ ^ (2 * m) * ‖c n‖ ^ 2) =
      fun n => ∑ j, ‖freq n‖ ^ (2 * m) * ‖c n j‖ ^ 2 := by
    funext n
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  rw [hfun]
  exact summable_sum fun j _ => h j

/-- **Every Sobolev level** of `theorem_B_community_periodic`'s hypothesis, from the class's own
smoothness and periodicity. -/
theorem summable_sob_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (m : ℕ) : Summable fun l => ‖freq l‖ ^ (2 * m) * ‖coeff u l‖ ^ 2 := by
  refine summable_vel_of_components m fun j => ?_
  have h := summable_norm_freq_pow_mul_coeff_sq (contDiff_ofReal_component hu j)
    (isOnePeriodic_ofReal_component hp j) m
  refine h.congr fun n => ?_
  simp only [coeff, PiLp.toLp_apply]

/-! ## B3. Reality and divergence (R1 pattern; R3 section 8) -/

/-- `RealField (coeff u)` for EVERY real field `u` (no hypothesis: the complexified components
are real-valued pointwise). -/
theorem realField_coeff (u : ℝ³ → ℝ³) : RealField (coeff u) := by
  intro k
  refine PiLp.ext fun j => ?_
  rw [c3_conjVel_apply, coeff_apply, coeff_apply]
  exact mFourierCoeff_neg_of_real (fun z => by simp [descend, Complex.conj_ofReal]) k

lemma dirDeriv_ofReal_component {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (j : Fin 3) (x : ℝ³) :
    dirDeriv j (fun y => ((u y j : ℝ) : ℂ)) x =
      ((fderiv ℝ u x (EuclideanSpace.single j 1)) j : ℂ) := by
  unfold dirDeriv
  have h : HasFDerivAt (fun y => ((u y j : ℝ) : ℂ))
      ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)).comp (fderiv ℝ u x)) x :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)).hasFDerivAt.comp x
      ((hu.differentiable (by simp)) x).hasFDerivAt
  rw [h.fderiv]
  rfl

lemma sum_dirDeriv_component_eq_divergence {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (x : ℝ³) :
    ∑ j, dirDeriv j (fun y => ((u y j : ℝ) : ℂ)) x = ((Community.divergence u x : ℝ) : ℂ) := by
  rw [divergence_eq_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => dirDeriv_ofReal_component hu j x

/-- **`DivFree (coeff u)` from the class's pointwise divergence-free condition** (the bridge at
`q = 1` summed over the components). -/
theorem divFree_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (hdiv : ∀ x, Community.divergence u x = 0) : DivFree (coeff u) := by
  intro k
  have hcomp : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => ((u y j : ℝ) : ℂ)) :=
    contDiff_ofReal_component hu
  have hper : ∀ j : Fin 3, IsOnePeriodic (fun y => ((u y j : ℝ) : ℂ)) :=
    fun j => isOnePeriodic_ofReal_component hp j
  have h1 : ∀ j : Fin 3, mFourierCoeff (descend (dirDeriv j (fun y => ((u y j : ℝ) : ℂ)))) k =
      (2 * Real.pi * Complex.I * (k j)) *
        mFourierCoeff (descend (fun y => ((u y j : ℝ) : ℂ))) k := by
    intro j
    have h := mFourierCoeff_descend_dirIter j (hcomp j) (hper j) 1 k
    rw [pow_one] at h
    exact h
  have hsum : ∑ j, mFourierCoeff (descend (dirDeriv j (fun y => ((u y j : ℝ) : ℂ)))) k = 0 := by
    have hlin := mFourierCoeff_finset_sum (Finset.univ : Finset (Fin 3))
      (fun j => descend (dirDeriv j (fun y => ((u y j : ℝ) : ℂ))))
      (fun j _ => continuous_descend (continuous_dirDeriv j (hcomp j))
        (dirDeriv_isOnePeriodic j (hper j))) k
    beta_reduce at hlin
    have hz : (fun z => ∑ j, descend (dirDeriv j (fun y => ((u y j : ℝ) : ℂ))) z) =
        fun _ => (0 : ℂ) := by
      funext z
      show ∑ j, dirDeriv j (fun y => ((u y j : ℝ) : ℂ)) (rep z) = 0
      rw [sum_dirDeriv_component_eq_divergence hu, hdiv]
      simp
    rw [hz] at hlin
    rw [← hlin]
    unfold mFourierCoeff
    simp
  have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hdot : (2 * Real.pi * Complex.I) * dotR (coeff u k) (freq k) = 0 := by
    unfold dotR
    rw [Finset.mul_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 j]
    simp only [coeff, PiLp.toLp_apply, freq]
    push_cast
    ring
  exact (mul_eq_zero.mp hdot).resolve_left h2πI

/-! ## B4. The round trip and THE INVERSION (R3 section 7, R6 section 1, R1 item 1) -/

/-- **Round trip on coefficient data**: `coeff (u₀Real c) = c` for a real ℓ¹ family. -/
theorem coeff_u₀Real {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (hc : Summable fun k => ‖c k‖) : coeff (u₀Real c) = c := by
  funext n
  ext j
  simp only [coeff, PiLp.toLp_apply]
  have hfun : (fun x : ℝ³ => ((u₀Real c x j : ℝ) : ℂ)) = uLift j c := by
    funext x
    simp only [u₀Real, PiLp.toLp_apply]
    exact Complex.ext (by simp) (by simp [im_uLift_eq_zero hreal hc j x])
  rw [hfun, mFourierCoeff_descend_uLift j c hc]

/-- The real datum of ANY coefficient family is one-periodic (`isOnePeriodic_uLift`). -/
theorem isOnePeriodic_u₀Real (c : (Fin 3 → ℤ) → Vel) : IsOnePeriodic (u₀Real c) := by
  intro x i
  show (WithLp.toLp 2 fun j : Fin 3 => (uLift j c (x + EuclideanSpace.single i 1)).re : ℝ³)
      = WithLp.toLp 2 fun j : Fin 3 => (uLift j c x).re
  congr 1
  funext j
  rw [isOnePeriodic_uLift j c x i]

/-- **THE INVERSION**: a smooth one-periodic real field is the real datum of its coefficient
field.  Mathlib supplies the pointwise inversion for continuous torus functions with summable
coefficients (`hasSum_mFourier_series_apply_of_summable`); the summability is the decay at
order `p = 0`; `descend_fiber` reads the torus value back at `fiber x`.  Textbook, not new. -/
theorem u₀Real_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) :
    u₀Real (coeff u) = u := by
  refine u₀Real_eq_of_lift (coeff u) u fun x j => ?_
  have hfc : ContDiff ℝ ∞ (fun y : ℝ³ => ((u y j : ℝ) : ℂ)) := contDiff_ofReal_component hu j
  have hfp : IsOnePeriodic (fun y : ℝ³ => ((u y j : ℝ) : ℂ)) := isOnePeriodic_ofReal_component hp j
  let g : C(UnitAddTorus (Fin 3), ℂ) :=
    ⟨descend (fun y : ℝ³ => ((u y j : ℝ) : ℂ)), continuous_descend hfc.continuous hfp⟩
  have hs' : Summable fun n => ‖mFourierCoeff (descend (fun y : ℝ³ => ((u y j : ℝ) : ℂ))) n‖ := by
    have h := summable_norm_freq_pow_mul_coeff hfc hfp 0
    simpa using h
  have hs : Summable (mFourierCoeff (⇑g)) := Summable.of_norm hs'
  have hinv : g (fiber x) = ∑' n, mFourierCoeff (⇑g) n • mFourier n (fiber x) :=
    (hasSum_mFourier_series_apply_of_summable hs (fiber x)).tsum_eq.symm
  have hgx : g (fiber x) = ((u x j : ℝ) : ℂ) := descend_fiber hfp x
  rw [uLift_eq_charSum_fiber, ← hgx, hinv]
  exact tsum_congr fun k => by rw [smul_eq_mul]; rfl

/-- **THE W1 CAPSTONE (the datum bridge)**: every datum in the community's own
`InitialVelocityConditionPeriodic` has a coefficient field with weighted ℓ¹ at every order,
every Sobolev level, reality, divergence-freeness, and IS the real datum of that field. -/
theorem datum_bridge {u : ℝ³ → ℝ³} (hu : InitialVelocityConditionPeriodic (n := 3) u) :
    (∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖coeff u l‖) ∧
    (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖coeff u l‖ ^ 2) ∧
    RealField (coeff u) ∧ DivFree (coeff u) ∧ u₀Real (coeff u) = u :=
  ⟨summable_weight_coeff hu.smooth hu.isOnePeriodic,
    summable_sob_coeff hu.smooth hu.isOnePeriodic,
    realField_coeff u,
    divFree_coeff hu.smooth hu.isOnePeriodic hu.div_free,
    u₀Real_coeff hu.smooth hu.isOnePeriodic⟩

end

end TheoremB
