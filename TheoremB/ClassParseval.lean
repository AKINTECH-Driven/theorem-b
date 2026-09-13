/-
  TheoremB/ClassParseval.lean
  Tier 9c, wave W3a (Theorem B campaign, 13 Sep 2026): Parseval for the energy and the
  enstrophy of the coefficient field of a continuous (resp. `C^1`) one-periodic real
  field, as EQUALITIES with the torus integrals; the bounded-integrand bound on the
  probability torus; the two `≤` feeders; the window budgets I11 (`classFlow_budget`)
  that supply `theorem_B_unique`'s hypothesis group H4 for the coefficient flow of a
  member of OUR COPY of the community class; and H3 in the flow spelling
  (`summable_flow`).  Transcribed from section C of the design probe
  `audit-tier9c/design/final/Tier9cFinal.lean` (session directory, never a tracked file;
  compiled there at the pin, exit 0, no declaration with a placeholder proof; section C is
  the recon probe `recon/P6/ReconP6.lean` with its two `-- INTERFACE (P1)` stubs replaced
  by SliceExtract.lean's I5 and I6); the frozen statements are those of
  `context/rung12-tier9c-blueprint.md` section 4a (the ClassParseval block),
  byte-identical, and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * The bricks: `contDiff_one_ofReal_component` (the complexified component at `C^1`),
    `descendC` (the descent of a continuous one-periodic scalar field bundled as
    `C(T³, ℂ)`), `hasSum_sq_mFourierCoeff_descend` (scalar Parseval on the descent:
    Mathlib's `hasSum_sq_mFourierCoeff` on `ContinuousMap.toLp`, transported by
    `mFourierCoeff_toLp` and `ContinuousMap.coeFn_toLp`), `integrable_norm_sq_descend`.
  * Parseval for the energy: `en_coeff_eq`: for a continuous one-periodic `u`,
    `∑ ‖coeff u n‖²` is summable and `en (coeff u) = ∫ ‖u (rep z)‖²` (an equality;
    `hasSum_sum` over the three components, `integral_finsetSum`).
  * Parseval for the enstrophy: `fderiv_ofReal_component`, `norm_sq_twist`,
    `sum_sq_coord_eq_norm_freq_sq`, `norm_freq_sq_mul_norm_coeff_sq_eq`, and
    `ens_coeff_eq`: for a `C^1` one-periodic `u`, `∑ ‖freq n‖² ‖coeff u n‖²` is summable
    and `ens (coeff u) = (2π)^(-2) ∑ᵢ ∫ ‖∂ᵢ u (rep z)‖²` (an equality; the
    derivative bridge `mFourierCoeff_descend_fderiv` per `(i, j)`, then `HasSum.mul_left`).
  * The bounded-integrand bound: `integral_le_of_bound` (a continuous integrand bounded
    by `C` on the probability torus integrates to at most `C`: `integral_mono`,
    `integral_const`, `probReal_univ` through the local instances).
  * The two `≤` feeders: `continuous_fderiv_apply_single_vec`, `en_coeff_le_of_bound`
    (`en (coeff u) ≤ C²` when `‖u‖ ≤ C`) and `ens_coeff_le_of_bound`
    (`ens (coeff u) ≤ (2π)^(-2) · 3 · D²` when `‖fderiv ℝ u x‖ ≤ D`, through
    `le_opNorm` and `PiLp.norm_single`).
  * The window budgets (I11): `classFlow_budget`: for a field `v` that is `C^∞` on the
    closed slab with one-periodic slices on `t ≥ 0`, and every window `Icc 0 T`, there
    are `E Z` with `en (coeff (v · (t / (2π)))) ≤ E` and
    `ens (coeff (v · (t / (2π)))) ≤ Z` for every `t` in the window (the campaign clock
    `t = 2πτ`); `E := C ^ 2` and
    `Z := (2π)^(-2) · (3 · D ^ 2)` from SliceExtract.lean's I5 and I6 on
    `Icc 0 (T / (2π))`.  This supplies the H4 group of `theorem_B_unique`
    (FullUnique.lean) for the coefficient flow of a class member, one flow per call; the
    capstone (W3c) takes the maxima over the two flows.
  * H3 in the flow spelling: `summable_flow` (at every `τ ≥ 0`, the energy and enstrophy
    series of `coeff (v · τ)` are summable, DatumBridge.lean's `summable_sob_coeff` at
    orders `0` and `1`) and `summable_flow_clock` (the same on a window in the campaign
    clock).

  HONEST SCOPE.
  * Nothing here is new mathematics: Parseval on the torus, the frequency multiplier of a
    partial derivative and the bound of an integral by a bound on its integrand are
    textbook; Mathlib supplies Parseval for `L²` of the torus at the pin; the deliverable
    is the machine-checked identity between the campaign's `en`/`ens` of a coefficient
    field (SpectralNorms.lean) and the torus integrals of a class member's slice.
  * Constants: the budgets `E := C ^ 2`, `Z := (2 * Real.pi) ^ (-2 : ℤ) * (3 * D ^ 2)` of
    I11 are UNTRACKED existentials produced by the compactness bounds I5, I6
    (`IsCompact.exists_bound_of_continuousOn`); the `(2π)^(-2)` and the `3` are literal
    expressions.  No numeric value of any constant is claimed.
  * This file delivers NO uniqueness statement.  It is a descent-side brick of W3: the two
    capstones (uniqueness inside OUR COPY of the community class at `f = 0`, for the same
    datum and `0 < ν'`: the velocity on `t ≥ 0`, the pressure up to a function of time) are
    W3c's
    (`TheoremB/CommunityUnique.lean`, not built here); `theorem_B_unique` (Tier 4) is
    consumed there, not here.
  * The unused binder `hT : 0 ≤ T` of `classFlow_budget` and `summable_flow_clock` is
    kept as agreed (blueprint D6: `Icc 0 T` is empty for `T < 0`, so the binder is
    content-free; dropping it would change the frozen shape); two linter warnings are
    expected.
  * `coeff u` is total (DatumBridge.lean): outside `IsOnePeriodic u` with the stated
    regularity it is a well-typed junk object; every statement here carries the
    hypotheses it needs (continuity and periodicity for `en_coeff_eq`, `C^1` and
    periodicity for `ens_coeff_eq`, the class's joint smoothness for the budgets).
  * Nothing here touches either upstream statement (the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
    `navier_stokes_breakdown_periodic`; both upstream placeholder proofs are untouched).
    Priority is not claimed for anything.
  * This file edits no earlier file of the tree and clones no private lemma: every
    declaration consumed here is public in its file.  Consumed tree files, measured by
    identifier grep of the code (docstrings stripped): SliceExtract
    (`exists_bound_velocity`, `exists_bound_space_deriv`, `continuous_ofReal_component`;
    the import), CommunityClass (`IsOnePeriodic`), Descent (`descend`, `rep`,
    `continuous_descend`, `continuous_fderiv_apply_single`,
    `mFourierCoeff_descend_fderiv`, `Community.IsOnePeriodic.fderiv_apply`), DatumBridge
    (`coeff`, `isOnePeriodic_ofReal_component`, `summable_sob_coeff`), Galilean (`slab`,
    `contDiff_space_slice`), SpectralNorms (`en`, `ens`, `freq`, `norm_freq`), and
    Mathlib; ConvectionCoeff is not needed (measured by the feasibility critic's module
    chain).
    The 9 helpers (`contDiff_one_ofReal_component`, `descendC` (def),
    `integrable_norm_sq_descend`, `fderiv_ofReal_component`, `norm_sq_twist`,
    `sum_sq_coord_eq_norm_freq_sq`, `norm_freq_sq_mul_norm_coeff_sq_eq`,
    `continuous_fderiv_apply_single_vec`, `summable_flow_clock`) are shipped public and
    carry no ledger line.

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances as `df_*`; here they are
  NAMED `cp_ms`, `cp_haar`, `cp_prob` (SliceExtract.lean uses `se_*`, ConvectionCoeff.lean
  `cc_*`), because auto-named local instances from two modules collide in a third module
  that imports both.  The bodies are the three-line block of FourierDeriv.lean lines
  31-37.  Instances are not statements; every frozen statement is byte-identical to the
  blueprint.  The probe's `-- SECTION C` marker is dropped; its section headings are kept.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.SliceExtract

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
local instance cp_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance cp_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance cp_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! # C. W3a : TheoremB/ClassParseval.lean (P6) -/

/-! ## 0. Bricks shared by (1) and (2) -/


/-- The complexified `j`-th component of a `C^1` real field is `C^1` (the tree's
`contDiff_ofReal_component` is stated at `∞`; this is the same one-liner at `1`). -/
lemma contDiff_one_ofReal_component {u : ℝ³ → ℝ³} (hu : ContDiff ℝ 1 u) (j : Fin 3) :
    ContDiff ℝ 1 (fun x => ((u x j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu)

/-- The descent of a continuous one-periodic scalar field, bundled as a continuous torus map
(the tree's `continuous_descend`: continuity FIRST, periodicity second). -/
def descendC {g : ℝ³ → ℂ} (hg : Continuous g) (hp : IsOnePeriodic g) :
    C(UnitAddTorus (Fin 3), ℂ) :=
  ⟨descend g, continuous_descend hg hp⟩

/-- **Scalar Parseval on the descent**: for a continuous one-periodic scalar field the squared
coefficients of its descent sum to the torus integral of the squared norm of the descent
(`hasSum_sq_mFourierCoeff` on `ContinuousMap.toLp`, transported by `mFourierCoeff_toLp` and
`ContinuousMap.coeFn_toLp`). -/
theorem hasSum_sq_mFourierCoeff_descend {g : ℝ³ → ℂ} (hg : Continuous g)
    (hp : IsOnePeriodic g) :
    HasSum (fun n => ‖mFourierCoeff (descend g) n‖ ^ 2)
      (∫ z : UnitAddTorus (Fin 3), ‖g (rep z)‖ ^ 2) := by
  have h := hasSum_sq_mFourierCoeff
    (ContinuousMap.toLp (E := ℂ) 2 volume ℂ (descendC hg hp))
  have hcoe : (fun n => ‖mFourierCoeff
      (ContinuousMap.toLp (E := ℂ) 2 volume ℂ (descendC hg hp)) n‖ ^ 2)
      = fun n => ‖mFourierCoeff (descend g) n‖ ^ 2 := by
    funext n
    rw [mFourierCoeff_toLp]
    rfl
  have hint : (∫ z, ‖(ContinuousMap.toLp (E := ℂ) 2 volume ℂ (descendC hg hp)) z‖ ^ 2)
      = ∫ z : UnitAddTorus (Fin 3), ‖g (rep z)‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := volume) (𝕜 := ℂ)
      (descendC hg hp)] with z hz
    rw [hz]
    rfl
  rw [hcoe, hint] at h
  exact h

/-- The squared norm of the descent of a continuous one-periodic scalar field is integrable on
the (compact) torus. -/
lemma integrable_norm_sq_descend {g : ℝ³ → ℂ} (hg : Continuous g) (hp : IsOnePeriodic g) :
    Integrable (fun z : UnitAddTorus (Fin 3) => ‖g (rep z)‖ ^ 2) := by
  have hc : Continuous (fun z : UnitAddTorus (Fin 3) => ‖g (rep z)‖ ^ 2) :=
    (continuous_descend hg hp).norm.pow 2
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ## (1) Parseval for the energy (R6 3.iii-a, retargeted to the tree's `coeff`/`rep`) -/

/-- (3.iii-a) Parseval: the energy of the coefficient field is the torus integral of the squared norm
(an equality, which is what `hasSum_sq_mFourierCoeff` gives; `≤` follows). -/
theorem en_coeff_eq {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hcont : Continuous u) :
    Summable (fun n => ‖coeff u n‖ ^ 2) ∧
    en (coeff u) = ∫ z : UnitAddTorus (Fin 3), ‖u (rep z)‖ ^ 2 := by
  -- Parseval per component
  have hP : ∀ j : Fin 3, HasSum (fun n => ‖mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n‖ ^ 2)
      (∫ z : UnitAddTorus (Fin 3), ‖((u (rep z) j : ℝ) : ℂ)‖ ^ 2) := fun j =>
    hasSum_sq_mFourierCoeff_descend (continuous_ofReal_component hcont j)
      (isOnePeriodic_ofReal_component hper j)
  -- the vector norm is the sum of the component norms
  have hnorm : ∀ n, ‖coeff u n‖ ^ 2
      = ∑ j, ‖mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n‖ ^ 2 := by
    intro n
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hnorm' : ∀ z : UnitAddTorus (Fin 3),
      ‖u (rep z)‖ ^ 2 = ∑ j, ‖((u (rep z) j : ℝ) : ℂ)‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_real]
  have hsum : HasSum (fun n => ‖coeff u n‖ ^ 2)
      (∑ j, ∫ z : UnitAddTorus (Fin 3), ‖((u (rep z) j : ℝ) : ℂ)‖ ^ 2) := by
    have h := hasSum_sum
      (f := fun (j : Fin 3) n => ‖mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n‖ ^ 2)
      (a := fun j => ∫ z : UnitAddTorus (Fin 3), ‖((u (rep z) j : ℝ) : ℂ)‖ ^ 2)
      (s := Finset.univ) (fun j _ => hP j)
    exact h.congr_fun fun n => hnorm n
  -- integrability of each component square (continuous on a compact space)
  have hint : ∀ j : Fin 3,
      Integrable (fun z : UnitAddTorus (Fin 3) => ‖((u (rep z) j : ℝ) : ℂ)‖ ^ 2) := fun j =>
    integrable_norm_sq_descend (continuous_ofReal_component hcont j)
      (isOnePeriodic_ofReal_component hper j)
  have hI : (∑ j, ∫ z : UnitAddTorus (Fin 3), ‖((u (rep z) j : ℝ) : ℂ)‖ ^ 2)
      = ∫ z : UnitAddTorus (Fin 3), ‖u (rep z)‖ ^ 2 := by
    rw [← integral_finsetSum _ (fun j _ => hint j)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hnorm' z).symm)
  exact ⟨hsum.summable, by rw [en, hsum.tsum_eq, hI]⟩

/-! ## (2) Parseval for the enstrophy through the derivative bridge -/

/-- The `i`-th partial of the complexified `j`-th component is the complexified `j`-th component
of the `i`-th partial (`DatumBridge.dirDeriv_ofReal_component` generalised to `i ≠ j` and to
`C^1`): `Complex.ofRealCLM ∘ EuclideanSpace.proj j` after `fderiv ℝ u x`, then `rfl`. -/
lemma fderiv_ofReal_component {u : ℝ³ → ℝ³} (hu : ContDiff ℝ 1 u) (i j : Fin 3) (x : ℝ³) :
    fderiv ℝ (fun y => ((u y j : ℝ) : ℂ)) x (EuclideanSpace.single i 1) =
      (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun y => ((u y j : ℝ) : ℂ))
      ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)).comp (fderiv ℝ u x)) x :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)).hasFDerivAt.comp x
      ((hu.differentiable (by norm_num)) x).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The norm arithmetic of the derivative bridge: `‖(2πi nᵢ) c‖² = (2π)² nᵢ² ‖c‖²`. -/
lemma norm_sq_twist (n : Fin 3 → ℤ) (i : Fin 3) (c : ℂ) :
    ‖(2 * Real.pi * Complex.I * (n i)) * c‖ ^ 2
      = (2 * Real.pi) ^ 2 * (((n i : ℝ) ^ 2) * ‖c‖ ^ 2) := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast,
    Complex.norm_real, Complex.norm_two, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, sq_abs]
  ring

/-- `∑ i, nᵢ² = ‖freq n‖²` (`norm_freq`, `Real.sq_sqrt`). -/
lemma sum_sq_coord_eq_norm_freq_sq (n : Fin 3 → ℤ) :
    ∑ i : Fin 3, ((n i : ℝ) ^ 2) = ‖freq n‖ ^ 2 := by
  rw [norm_freq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- The coefficient-side identity behind the enstrophy Parseval: for a `C^1` one-periodic
field, `‖freq n‖² ‖coeff u n‖² = (2π)^(-2) ∑ i ∑ j ‖mFourierCoeff (descend ∂ᵢ f_j) n‖²`,
with `f_j` the complexified `j`-th component. -/
lemma norm_freq_sq_mul_norm_coeff_sq_eq {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u)
    (hu : ContDiff ℝ 1 u) (n : Fin 3 → ℤ) :
    ‖freq n‖ ^ 2 * ‖coeff u n‖ ^ 2 = (2 * Real.pi) ^ (-2 : ℤ) *
      ∑ i : Fin 3, ∑ j : Fin 3, ‖mFourierCoeff (descend fun x =>
        fderiv ℝ (fun y => ((u y j : ℝ) : ℂ)) x (EuclideanSpace.single i 1)) n‖ ^ 2 := by
  have hbridge : ∀ i j : Fin 3, mFourierCoeff (descend fun x =>
        fderiv ℝ (fun y => ((u y j : ℝ) : ℂ)) x (EuclideanSpace.single i 1)) n
      = (2 * Real.pi * Complex.I * (n i)) *
          mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n := fun i j =>
    mFourierCoeff_descend_fderiv (contDiff_one_ofReal_component hu j)
      (isOnePeriodic_ofReal_component hper j) i n
  have hcoeff : ‖coeff u n‖ ^ 2
      = ∑ j, ‖mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  simp_rw [hbridge, norm_sq_twist]
  rw [hcoeff, ← sum_sq_coord_eq_norm_freq_sq n]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_mul_sum]
  rw [zpow_neg, zpow_ofNat, ← mul_assoc,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi) ^ 2 ≠ 0), one_mul]

/-- (3.iii-b) Parseval for the enstrophy through the derivative bridge.  The `(2π)^(-2)` is
the clock-free calibration: each `∂ᵢ` costs `2πi nᵢ` on the coefficient side. -/
theorem ens_coeff_eq {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hu : ContDiff ℝ 1 u) :
    Summable (fun n => ‖freq n‖ ^ 2 * ‖coeff u n‖ ^ 2) ∧
    ens (coeff u) = (2 * Real.pi) ^ (-2 : ℤ) *
      ∑ i : Fin 3, ∫ z : UnitAddTorus (Fin 3),
        ‖fderiv ℝ u (rep z) (EuclideanSpace.single i 1)‖ ^ 2 := by
  -- the partials of the complexified components, as scalar fields
  set g : Fin 3 → Fin 3 → ℝ³ → ℂ := fun i j x =>
    fderiv ℝ (fun y => ((u y j : ℝ) : ℂ)) x (EuclideanSpace.single i 1) with hg
  have hgc : ∀ i j, Continuous (g i j) := fun i j =>
    continuous_fderiv_apply_single (contDiff_one_ofReal_component hu j) i
  have hgp : ∀ i j, IsOnePeriodic (g i j) := fun i j =>
    (isOnePeriodic_ofReal_component hper j).fderiv_apply _
  -- Parseval per (i, j)
  have hP : ∀ i j : Fin 3, HasSum (fun n => ‖mFourierCoeff (descend (g i j)) n‖ ^ 2)
      (∫ z : UnitAddTorus (Fin 3), ‖g i j (rep z)‖ ^ 2) := fun i j =>
    hasSum_sq_mFourierCoeff_descend (hgc i j) (hgp i j)
  -- sum over j, then over i, then scale by (2π)^(-2)
  have hPi : ∀ i : Fin 3, HasSum (fun n => ∑ j, ‖mFourierCoeff (descend (g i j)) n‖ ^ 2)
      (∑ j, ∫ z : UnitAddTorus (Fin 3), ‖g i j (rep z)‖ ^ 2) := fun i =>
    hasSum_sum (s := Finset.univ) (fun j _ => hP i j)
  have hPsum : HasSum (fun n => ∑ i, ∑ j, ‖mFourierCoeff (descend (g i j)) n‖ ^ 2)
      (∑ i, ∑ j, ∫ z : UnitAddTorus (Fin 3), ‖g i j (rep z)‖ ^ 2) :=
    hasSum_sum (s := Finset.univ) (fun i _ => hPi i)
  have hsum : HasSum (fun n => ‖freq n‖ ^ 2 * ‖coeff u n‖ ^ 2)
      ((2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i, ∑ j, ∫ z : UnitAddTorus (Fin 3), ‖g i j (rep z)‖ ^ 2) := by
    refine (hPsum.mul_left ((2 * Real.pi) ^ (-2 : ℤ))).congr_fun fun n => ?_
    exact norm_freq_sq_mul_norm_coeff_sq_eq hper hu n
  -- the integral side: ∑ j ∫ ‖g i j‖² = ∫ ‖∂ᵢ u‖²
  have hI : ∀ i : Fin 3, (∑ j, ∫ z : UnitAddTorus (Fin 3), ‖g i j (rep z)‖ ^ 2)
      = ∫ z : UnitAddTorus (Fin 3), ‖fderiv ℝ u (rep z) (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    rw [← integral_finsetSum _ (fun j _ => integrable_norm_sq_descend (hgc i j) (hgp i j))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ∑ j, ‖g i j (rep z)‖ ^ 2 = ‖fderiv ℝ u (rep z) (EuclideanSpace.single i 1)‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ‖fderiv ℝ (fun y => ((u y j : ℝ) : ℂ)) (rep z) (EuclideanSpace.single i 1)‖ ^ 2
      = ‖(fderiv ℝ u (rep z) (EuclideanSpace.single i 1)) j‖ ^ 2
    rw [fderiv_ofReal_component hu i j, Complex.norm_real]
  refine ⟨hsum.summable, ?_⟩
  rw [ens, hsum.tsum_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hI i

/-! ## (3) The bounded-integrand bound on the probability torus -/

/-- A continuous integrand bounded by `C` on the probability torus integrates to at most `C`
(`integral_mono` against the constant, `integral_const`, `probReal_univ`). -/
lemma integral_le_of_bound {F : UnitAddTorus (Fin 3) → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ z, F z ≤ C) : ∫ z, F z ≤ C := by
  have hFi : Integrable F (volume : Measure (UnitAddTorus (Fin 3))) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ z, F z ≤ ∫ _z : UnitAddTorus (Fin 3), C := integral_mono hFi (integrable_const C) hC
    _ = C := by rw [integral_const, probReal_univ, one_smul]

/-! ## (4) The window budgets (H4), through SliceExtract.lean's I5 and I6 -/

/-- The partial `∂ᵢ` of a `C^1` vector field is continuous (the vector-valued sibling of the
tree's `continuous_fderiv_apply_single`, which is stated for `ℂ`-valued fields). -/
lemma continuous_fderiv_apply_single_vec {w : ℝ³ → ℝ³} (hw : ContDiff ℝ 1 w) (i : Fin 3) :
    Continuous fun x : ℝ³ => fderiv ℝ w x (EuclideanSpace.single i 1) := by
  have h := hw.continuous_fderiv_apply (by norm_num)
  exact h.comp (continuous_id.prodMk continuous_const)

/-- The energy of a continuous one-periodic field bounded by `C` is at most `C²`
(by `en_coeff_eq` and `integral_le_of_bound`). -/
lemma en_coeff_le_of_bound {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hcont : Continuous u)
    {C : ℝ} (hC : ∀ x, ‖u x‖ ≤ C) : en (coeff u) ≤ C ^ 2 := by
  rw [(en_coeff_eq hper hcont).2]
  refine integral_le_of_bound ((continuous_descend hcont hper).norm.pow 2) fun z => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (hC (rep z)) 2

/-- The enstrophy of a `C^1` one-periodic field with `‖fderiv ℝ u x‖ ≤ D` everywhere is at most
`(2π)^(-2) · 3 · D²` (by `ens_coeff_eq`, `ContinuousLinearMap.le_opNorm` with
`‖single i 1‖ = 1`, and `integral_le_of_bound` per direction). -/
lemma ens_coeff_le_of_bound {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hu : ContDiff ℝ 1 u)
    {D : ℝ} (hD : ∀ x, ‖fderiv ℝ u x‖ ≤ D) :
    ens (coeff u) ≤ (2 * Real.pi) ^ (-2 : ℤ) * (3 * D ^ 2) := by
  rw [(ens_coeff_eq hper hu).2]
  refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (by positivity) _)
  have hi : ∀ i : Fin 3,
      (∫ z : UnitAddTorus (Fin 3), ‖fderiv ℝ u (rep z) (EuclideanSpace.single i 1)‖ ^ 2)
        ≤ D ^ 2 := by
    intro i
    refine integral_le_of_bound
      ((continuous_descend (continuous_fderiv_apply_single_vec hu i)
        (hper.fderiv_apply _)).norm.pow 2) fun z => ?_
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖fderiv ℝ u (rep z) (EuclideanSpace.single i 1)‖
        ≤ ‖fderiv ℝ u (rep z)‖ * ‖(EuclideanSpace.single i (1:ℝ) : ℝ³)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ u (rep z)‖ := by rw [PiLp.norm_single, norm_one, mul_one]
      _ ≤ D := hD (rep z)
  calc (∑ i : Fin 3, ∫ z : UnitAddTorus (Fin 3),
          ‖fderiv ℝ u (rep z) (EuclideanSpace.single i 1)‖ ^ 2)
      ≤ ∑ _i : Fin 3, D ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = 3 * D ^ 2 := by simp

/-- I11: **the window budgets of a class member's coefficient flow**.  `E := C²` with `C` the
sup of `‖v‖` on `[0, T/(2π)]` (I5) and `Z := (2π)^(-2) · 3 · D²` with `D` the sup of
`‖fderiv ℝ (v · τ)‖` there (I6).  PROVED through `SliceExtract.lean`'s I5 and I6
(`exists_bound_velocity`, `exists_bound_space_deriv`). -/
theorem classFlow_budget {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T,
      en (coeff (v · (t / (2 * Real.pi)))) ≤ E ∧ ens (coeff (v · (t / (2 * Real.pi)))) ≤ Z := by
  obtain ⟨C, hC⟩ := exists_bound_velocity hv hper (a := 0) (b := T / (2 * Real.pi)) le_rfl
  obtain ⟨D, hD⟩ := exists_bound_space_deriv hv hper (a := 0) (b := T / (2 * Real.pi)) le_rfl
  refine ⟨C ^ 2, (2 * Real.pi) ^ (-2 : ℤ) * (3 * D ^ 2), fun t ht => ?_⟩
  have hτ : t / (2 * Real.pi) ∈ Icc (0:ℝ) (T / (2 * Real.pi)) :=
    ⟨div_nonneg ht.1 (by positivity), by gcongr; exact ht.2⟩
  have hτ0 : 0 ≤ t / (2 * Real.pi) := hτ.1
  have hs : ContDiff ℝ ∞ (v · (t / (2 * Real.pi))) := contDiff_space_slice hv hτ0
  have hp : IsOnePeriodic (v · (t / (2 * Real.pi))) := hper _ hτ0
  exact ⟨en_coeff_le_of_bound hp hs.continuous (fun x => hC x _ hτ),
    ens_coeff_le_of_bound hp (hs.of_le (WithTop.coe_le_coe.2 le_top)) (fun x => hD x _ hτ)⟩

/-! ## (5) H3 in the flow spelling (no interface) -/

/-- H3 for a class member's space slice at every `τ ≥ 0`: the energy and enstrophy series
are summable (`summable_sob_coeff` at `m = 0` and `m = 1`). -/
theorem summable_flow {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable (fun l => ‖coeff (v · τ) l‖ ^ 2) ∧
    Summable (fun l => ‖freq l‖ ^ 2 * ‖coeff (v · τ) l‖ ^ 2) := by
  have hs : ContDiff ℝ ∞ (v · τ) := contDiff_space_slice hv hτ
  have hp : IsOnePeriodic (v · τ) := hper τ hτ
  constructor
  · simpa using summable_sob_coeff hs hp 0
  · simpa using summable_sob_coeff hs hp 1

/-- H3 in the campaign clock (the spelling `theorem_B_unique` consumes on a window). -/
theorem summable_flow_clock {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0:ℝ) T,
      Summable (fun l => ‖coeff (v · (t / (2 * Real.pi))) l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖coeff (v · (t / (2 * Real.pi))) l‖ ^ 2) :=
  fun t ht => summable_flow hv hper (div_nonneg ht.1 (by positivity))

end

end TheoremB
