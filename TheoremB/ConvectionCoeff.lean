/-
  TheoremB/ConvectionCoeff.lean
  Tier 9c, wave W3a (Theorem B campaign, 13 Sep 2026): the coefficient of an absolutely
  convergent character series, the product coefficient of two continuous one-periodic
  scalar fields with ℓ¹ coefficients (a nonzero mean mode allowed), and the coefficient of
  the class's convection term `x ↦ fderiv ℝ u x (u x)` at a fixed time, matched to `-2π`
  times the campaign's `convFull (coeff u)`.  Transcribed from section B of the design
  probe `audit-tier9c/design/final/Tier9cFinal.lean` (session directory, never a tracked
  file; compiled there at the pin, exit 0, no declaration with a placeholder proof;
  section B is the recon probe `recon/P3/ReconP3.lean` verbatim); the frozen statements
  are those of `context/rung12-tier9c-blueprint.md` section 4a (the ConvectionCoeff
  block), byte-identical, and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * The character-series coefficient: `mFourierCoeff_charSeries`: for an ℓ¹ family `a` on
    `ℤ³`, the `n`-th coefficient of `z ↦ ∑' k, a k * mFourier k z` is `a n`.  Route: the
    scalar family is packed into the `0`-th slot of a `Vel` family, the series is then the
    tree's continuous representative `uCont 0 c hc` (ContinuousRep.lean), and
    `mFourierCoeff_uCont` reads the coefficient off; nothing asks for a zero mean mode.
  * Discrete Young on `ℤ³`: `summable_conv_shear` (the sheared majorant
    `(k, l) ↦ ‖a l‖ ‖b (k - l)‖` is summable on `ℤ³ × ℤ³`, through
    `Summable.mul_of_nonneg` and the tree's `shearEquiv`), `summable_conv_term` (each
    convolution fiber is summable) and `summable_norm_conv` (ℓ¹ ∗ ℓ¹ ⊆ ℓ¹, the marginal
    by `Summable.prod`).
  * The product coefficient: `coeffC_mul`: for continuous one-periodic `f`, `g` whose
    descents have ℓ¹ coefficients, the coefficient of `f * g` at `n` is the convolution
    `∑' l, f̂ l ĝ (n - l)`.  Route: the two descents bundled into `C(T³, ℂ)`, Mathlib's
    pointwise inversion `hasSum_mFourier_series_apply_of_summable` writes each as its
    character series, the tree's `tsum_char_mul` (Nonlinearity.lean) multiplies them, and
    `mFourierCoeff_charSeries` reads the coefficient off.
  * The derivative factor: `dirDeriv_ofReal_component'` (the off-diagonal form of
    DatumBridge.lean's `dirDeriv_ofReal_component`), `factor_eq_dirDeriv`,
    `continuous_factor`, `isOnePeriodic_factor`, `mFourierCoeff_factor` (the coefficient
    of the complexified `∂ᵢ u_j` at `m` is `(2πi mᵢ) · coeff u m j`, the bridge
    `mFourierCoeff_descend_dirIter` at `q = 1`), and the two ℓ¹ certificates
    `summable_norm_coeff_factor`, `summable_norm_coeff_component` (DatumBridge.lean's
    `summable_norm_freq_pow_mul_coeff` at order `0`).
  * The convection coefficient (I10): `vel_tsum_apply` (component extraction from a `Vel`
    tsum, shipped unconsumed), `convection_term_coeff`, `summable_convection_term`, and
    `convection_coeff_eq_convFull`: the sum over `i` of the coefficients of `u_i ∂ᵢ u_j`
    at `n` equals `-2π · (convFull (coeff u) n) j`; the finite sum is pushed inside the
    tsum (`Summable.tsum_finsetSum`), the three directions rebuild `dotR` (the `hdot`
    step of Nonlinearity.lean's `convection_classical`), and `convFull_apply` supplies
    the component of the `Vel` tsum.
  * The real convection field: `isOnePeriodic_mul` and `coeff_convection`:
    `coeff (fun x => fderiv ℝ u x (u x)) n j = -2π · (convFull (coeff u) n) j`, through
    `fderiv_apply_expand` (CommunityClass.lean) and `mFourierCoeff_finset_sum`; this is
    the shape W3b's mode ODE consumes.

  HONEST SCOPE.
  * Nothing here is new mathematics: the coefficient of a character series, the Cauchy
    product of two Fourier series and discrete Young for ℓ¹ sequences on `ℤ³` are
    textbook; the deliverable is the machine-checked match between the class's real-space
    convection term and the campaign's `convFull`.
  * Constants: the `-2π` of I10 and the `2πi mᵢ` of the derivative factor are literal
    expressions computed by the kernel (`push_cast; ring` against `convFull_apply`), not
    assumed; W3b consumes the `-2π` against the campaign clock `t = 2πτ` (the calibration
    in reverse, not built here).  No numeric value of any constant is claimed.
  * This file delivers NO uniqueness statement.  It is a descent-side brick of W3: the two
    capstones (uniqueness inside OUR COPY of the community class at `f = 0`, for the same
    datum and `0 < ν'`: the velocity on `t ≥ 0`, the pressure up to a function of time) are
    W3c's
    (`TheoremB/CommunityUnique.lean`, not built here).
  * `coeff u` is total (DatumBridge.lean): for a `u` outside `ContDiff ℝ ∞ u ∧
    IsOnePeriodic u` it is a well-typed junk object; every statement here about `coeff u`
    carries those two hypotheses.
  * Nothing here touches either upstream statement (the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
    `navier_stokes_breakdown_periodic`; both upstream placeholder proofs are untouched).
    Priority is not claimed for anything.
  * This file edits no earlier file of the tree and clones no private lemma: every
    declaration consumed here is public in its file.  Consumed tree files, measured by
    identifier grep of the code (docstrings stripped): CommunityClass (`IsOnePeriodic`,
    `fderiv_apply_expand`), Descent (`descend`, `rep`, `continuous_descend`, `dirDeriv`
    and its rules, `mFourierCoeff_descend_dirIter`, `mFourierCoeff_finset_sum`,
    `summable_sq_of_summable_norm`), DatumBridge (`coeff`, `coeff_apply`,
    `contDiff_ofReal_component`, `isOnePeriodic_ofReal_component`,
    `summable_norm_freq_pow_mul_coeff`, `summable_sob_coeff`), ContinuousRep (`uCont`,
    `uCont_apply`, `mFourierCoeff_uCont`), NSGalerkin (`Vel`, `dotR`), NSFull
    (`convFull`), Nonlinearity (`convFull_apply`, `tsum_char_mul`), TimeLayer
    (`shearEquiv`), SpectralNorms (`freq`), and Mathlib; Galilean is not needed (measured
    by the design's import probe).
    The 12 helpers (`summable_conv_shear`, `summable_conv_term`,
    `dirDeriv_ofReal_component'`, `factor_eq_dirDeriv`, `continuous_factor`,
    `isOnePeriodic_factor`, `summable_norm_coeff_factor`, `summable_norm_coeff_component`,
    `vel_tsum_apply`, `convection_term_coeff`, `summable_convection_term`,
    `isOnePeriodic_mul`) are shipped public and carry no ledger line.

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances as `df_*`; here they are
  NAMED `cc_ms`, `cc_haar`, `cc_prob` (SliceExtract.lean uses `se_*`, ClassParseval.lean
  `cp_*`), because auto-named local instances from two modules collide in a third module
  that imports both.  The bodies are the three-line block of FourierDeriv.lean lines
  31-37.  Instances are not statements; every frozen statement is byte-identical to the
  blueprint.  The probe's `-- SECTION B` marker is dropped; its section headings are kept.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.DatumBridge

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
local instance cc_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance cc_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance cc_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! # B. W3a : TheoremB/ConvectionCoeff.lean (P3) -/

/-! ## (1) The coefficient of an absolutely convergent scalar character series -/

/-- **(1) Route A, the Vel-packing trick.**  A scalar l1 family `a` is packed into the
`0`-th slot of a `Vel` family `c k := EuclideanSpace.single 0 (a k)`; the scalar
character series is then the tree's continuous representative `uCont 0 c hc` as a
function, whose coefficients `mFourierCoeff_uCont` recovers.  The mean mode `a 0` is
allowed to be nonzero (nothing in `uCont` asks for a zero mode). -/
theorem mFourierCoeff_charSeries {a : (Fin 3 → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖)
    (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => ∑' k, a k * mFourier k z) n = a n := by
  let c : (Fin 3 → ℤ) → Vel := fun k => EuclideanSpace.single (0 : Fin 3) (a k)
  have hc : Summable fun k => ‖c k‖ := ha.congr fun k => by
    show ‖a k‖ = ‖EuclideanSpace.single (0 : Fin 3) (a k)‖
    exact (PiLp.norm_single 2 (fun _ : Fin 3 => ℂ) (0 : Fin 3) (a k)).symm
  have hfun : (fun z => ∑' k, a k * mFourier k z) = ⇑(uCont 0 c hc) := by
    funext z
    rw [← (uCont_apply 0 c hc z).tsum_eq]
    refine tsum_congr fun k => ?_
    show a k * mFourier k z = (EuclideanSpace.single (0 : Fin 3) (a k)) 0 • mFourier k z
    rw [PiLp.single_apply, if_pos rfl, smul_eq_mul]
  rw [hfun, mFourierCoeff_uCont 0 c hc (summable_sq_of_summable_norm hc) n]
  show (EuclideanSpace.single (0 : Fin 3) (a n)) 0 = a n
  rw [PiLp.single_apply, if_pos rfl]

/-! ## (2) Discrete Young on ℤ³ and the product coefficient -/

/-- The sheared convolution majorant `(k, l) ↦ ‖a l‖ ‖b (k - l)‖` is summable on
`ℤ³ × ℤ³` (the TimeLayer.lean:132 pattern: the product family is summable by
`Summable.mul_of_nonneg`, the public `shearEquiv` refibers it). -/
theorem summable_conv_shear {a b : (Fin 3 → ℤ) → ℂ}
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Summable (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) => ‖a q.2‖ * ‖b (q.1 - q.2)‖) := by
  have hF : Summable (fun p : (Fin 3 → ℤ) × (Fin 3 → ℤ) => ‖a p.1‖ * ‖b p.2‖) :=
    ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hcomp : ∀ p : (Fin 3 → ℤ) × (Fin 3 → ℤ),
      (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) => ‖a q.2‖ * ‖b (q.1 - q.2)‖) (shearEquiv p)
        = ‖a p.1‖ * ‖b p.2‖ := by
    rintro ⟨l, m⟩
    have hsub : l + m - l = m := by abel
    show ‖a l‖ * ‖b (l + m - l)‖ = ‖a l‖ * ‖b m‖
    rw [hsub]
  exact (shearEquiv.summable_iff).mp (hF.congr fun p => (hcomp p).symm)

/-- Each convolution fiber is (absolutely) summable. -/
theorem summable_conv_term {a b : (Fin 3 → ℤ) → ℂ}
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) (k : Fin 3 → ℤ) :
    Summable fun l => a l * b (k - l) := by
  refine Summable.of_norm (((summable_conv_shear ha hb).prod_factor k).congr fun l => ?_)
  exact (norm_mul _ _).symm

/-- **Discrete Young, l1 * l1 in l1**: the convolution of two l1 sequences on ℤ³ is
l1 (the k-marginals of the sheared majorant are summable by `Summable.prod`). -/
theorem summable_norm_conv {a b : (Fin 3 → ℤ) → ℂ}
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Summable fun k => ‖∑' l, a l * b (k - l)‖ := by
  have hG := summable_conv_shear ha hb
  have hmarg : Summable fun k => ∑' l, ‖a l‖ * ‖b (k - l)‖ := hG.prod
  refine hmarg.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
  have hinner : Summable fun l => ‖a l * b (k - l)‖ :=
    (hG.prod_factor k).congr fun l => (norm_mul _ _).symm
  refine (norm_tsum_le_tsum_norm hinner).trans (le_of_eq ?_)
  exact tsum_congr fun l => norm_mul _ _

/-- **(2) The product coefficient** (R6 (3.iv), statement VERBATIM with coeffC unfolded).
The two descents are bundled into `C(T³, ℂ)`, Mathlib's pointwise inversion writes each
as its character series, `tsum_char_mul` multiplies them into the convolution series,
and (1) reads the coefficient off since the convolution is l1 by discrete Young. -/
theorem coeffC_mul {f g : ℝ³ → ℂ} (hfp : IsOnePeriodic f) (hgp : IsOnePeriodic g)
    (hf : Continuous f) (hg : Continuous g)
    (hfs : Summable fun k => ‖mFourierCoeff (descend f) k‖) (hgs : Summable fun k => ‖mFourierCoeff (descend g) k‖)
    (n : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => f x * g x) n = ∑' l, mFourierCoeff (descend f) l * mFourierCoeff (descend g) (n - l) := by
  let F : C(UnitAddTorus (Fin 3), ℂ) := ⟨descend f, continuous_descend hf hfp⟩
  let G : C(UnitAddTorus (Fin 3), ℂ) := ⟨descend g, continuous_descend hg hgp⟩
  have hFs : Summable (mFourierCoeff (⇑F)) := Summable.of_norm hfs
  have hGs : Summable (mFourierCoeff (⇑G)) := Summable.of_norm hgs
  have hFz : ∀ z, descend f z = ∑' l, mFourierCoeff (descend f) l * mFourier l z := fun z => by
    have h := (hasSum_mFourier_series_apply_of_summable hFs z).tsum_eq.symm
    refine h.trans (tsum_congr fun k => ?_)
    rfl
  have hGz : ∀ z, descend g z = ∑' l, mFourierCoeff (descend g) l * mFourier l z := fun z => by
    have h := (hasSum_mFourier_series_apply_of_summable hGs z).tsum_eq.symm
    refine h.trans (tsum_congr fun k => ?_)
    rfl
  have hprod : descend (fun x => f x * g x)
      = fun z => ∑' k, (∑' l, mFourierCoeff (descend f) l * mFourierCoeff (descend g) (k - l))
          * mFourier k z := by
    funext z
    show descend f z * descend g z = _
    rw [hFz z, hGz z]
    exact tsum_char_mul hfs hgs z
  rw [hprod]
  exact mFourierCoeff_charSeries (summable_norm_conv hfs hgs) n

/-! ## (3) The derivative-factor coefficients -/

/-- **The off-diagonal generalisation of `dirDeriv_ofReal_component`** (DatumBridge.lean:365,
which is the case `j = i`): the `i`-th partial of the complexified `j`-th component is the
complexified `j`-th component of the `i`-th partial. -/
theorem dirDeriv_ofReal_component' {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (i j : Fin 3) (x : ℝ³) :
    dirDeriv i (fun y => ((u y j : ℝ) : ℂ)) x =
      ((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℂ) := by
  unfold dirDeriv
  have h : HasFDerivAt (fun y => ((u y j : ℝ) : ℂ))
      ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)).comp (fderiv ℝ u x)) x :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) j)).hasFDerivAt.comp x
      ((hu.differentiable (by simp)) x).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The complexified derivative factor `D_ij` IS `dirDeriv i` of the complexified `j`-th
component (function-level). -/
theorem factor_eq_dirDeriv {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (i j : Fin 3) :
    (fun x => (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ))
      = dirDeriv i (fun y => ((u y j : ℝ) : ℂ)) :=
  funext fun x => (dirDeriv_ofReal_component' hu i j x).symm

theorem continuous_factor {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (i j : Fin 3) :
    Continuous (fun x => (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) := by
  rw [factor_eq_dirDeriv hu i j]
  exact continuous_dirDeriv i (contDiff_ofReal_component hu j)

theorem isOnePeriodic_factor {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (i j : Fin 3) :
    IsOnePeriodic (fun x => (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) := by
  rw [factor_eq_dirDeriv hu i j]
  exact dirDeriv_isOnePeriodic i (isOnePeriodic_ofReal_component hp j)

/-- The coefficients of the derivative factor: `(2πi mᵢ) · coeff u m j`
(`mFourierCoeff_descend_dirIter` at `q = 1`). -/
theorem mFourierCoeff_factor {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (i j : Fin 3) (m : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) m
      = (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * coeff u m j := by
  rw [factor_eq_dirDeriv hu i j]
  have h := mFourierCoeff_descend_dirIter i (contDiff_ofReal_component hu j)
    (isOnePeriodic_ofReal_component hp j) 1 m
  rw [pow_one] at h
  exact h

/-- The l1 certificate of the derivative factor (`summable_norm_freq_pow_mul_coeff` at
`p = 0` on `dirDeriv i` of the complexified component; a nonzero mean mode is allowed). -/
theorem summable_norm_coeff_factor {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (i j : Fin 3) :
    Summable fun m =>
      ‖mFourierCoeff (descend fun x => (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) m‖ := by
  rw [factor_eq_dirDeriv hu i j]
  simpa using summable_norm_freq_pow_mul_coeff (contDiff_dirDeriv i (contDiff_ofReal_component hu j))
    (dirDeriv_isOnePeriodic i (isOnePeriodic_ofReal_component hp j)) 0

/-- The l1 certificate of the complexified component itself (order `p = 0`). -/
theorem summable_norm_coeff_component {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (i : Fin 3) :
    Summable fun k => ‖mFourierCoeff (descend fun x => ((u x i : ℝ) : ℂ)) k‖ := by
  simpa using summable_norm_freq_pow_mul_coeff (contDiff_ofReal_component hu i)
    (isOnePeriodic_ofReal_component hp i) 0

/-! ## (4) I10: the convection coefficient in convolution form, matched to `convFull` -/

/-- The measured form in which the `j`-th component of a `Vel` tsum is extracted
(Nonlinearity.lean:256 in `convFull_apply`): `EuclideanSpace.proj j` is a CLM and
`ContinuousLinearMap.map_tsum` commutes it with the sum; `proj j v = v j` is `rfl`. -/
theorem vel_tsum_apply {F : (Fin 3 → ℤ) → Vel} (hF : Summable F) (j : Fin 3) :
    (∑' l, F l) j = ∑' l, F l j :=
  ContinuousLinearMap.map_tsum (EuclideanSpace.proj (𝕜 := ℂ) j) hF

/-- The per-direction product coefficient: (2) with `f` the complexified `uᵢ` and `g` the
derivative factor `D_ij`, the factor's coefficients rewritten by `mFourierCoeff_factor`. -/
theorem convection_term_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (i j : Fin 3) (n : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => ((u x i : ℝ) : ℂ)
        * (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) n
      = ∑' l, coeff u l i * ((2 * Real.pi * Complex.I * (((n - l) i : ℤ) : ℂ)) * coeff u (n - l) j) := by
  refine (coeffC_mul (f := fun x => ((u x i : ℝ) : ℂ))
    (g := fun x => (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ))
    (isOnePeriodic_ofReal_component hp i) (isOnePeriodic_factor hu hp i j)
    (contDiff_ofReal_component hu i).continuous (continuous_factor hu i j)
    (summable_norm_coeff_component hu hp i) (summable_norm_coeff_factor hu hp i j) n).trans ?_
  refine tsum_congr fun l => ?_
  rw [mFourierCoeff_factor hu hp i j (n - l)]
  rfl

/-- The per-direction convolution family is summable (each fiber of discrete Young). -/
theorem summable_convection_term {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (i j : Fin 3) (n : Fin 3 → ℤ) :
    Summable fun l => coeff u l i
      * ((2 * Real.pi * Complex.I * (((n - l) i : ℤ) : ℂ)) * coeff u (n - l) j) := by
  have hai : Summable fun l => ‖coeff u l i‖ := summable_norm_coeff_component hu hp i
  have hbi : Summable fun m => ‖(2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * coeff u m j‖ :=
    (summable_norm_coeff_factor hu hp i j).congr fun m => by rw [mFourierCoeff_factor hu hp i j m]
  exact summable_conv_term hai hbi n

/-- **(4) I10, VERBATIM.**  The convection coefficient in convolution form IS `-2π` times the
`j`-th component of the campaign's `convFull (coeff u) n`: the per-direction product
coefficients (`convection_term_coeff`) are summed over `i`, the finite sum is pushed inside
the tsum (`Summable.tsum_finsetSum`), the three directions rebuild `dotR` (the `hdot` step of
`convection_classical`, Nonlinearity.lean:375), and `convFull_apply` (Nonlinearity.lean:241)
supplies the component of the Vel tsum.  The `2π` and the sign are COMPUTED, not assumed. -/
theorem convection_coeff_eq_convFull {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) (j : Fin 3) (n : Fin 3 → ℤ) : ∑ i : Fin 3, mFourierCoeff (descend fun x => ((u x i : ℝ) : ℂ) * (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) n = ((-(2 * Real.pi) : ℝ) : ℂ) * (convFull (coeff u) n) j := by
  have hE : Summable fun l => ‖coeff u l‖ ^ 2 := by
    simpa using summable_sob_coeff hu hp 0
  have hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖coeff u l‖ ^ 2 := by
    simpa using summable_sob_coeff hu hp 1
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => convection_term_coeff hu hp i j n),
    ← Summable.tsum_finsetSum (fun i (_ : i ∈ Finset.univ) => summable_convection_term hu hp i j n)]
  have hdot : ∀ l : Fin 3 → ℤ, (∑ i : Fin 3, coeff u l i *
      ((2 * Real.pi * Complex.I * (((n - l) i : ℤ) : ℂ)) * coeff u (n - l) j))
      = ((2 * Real.pi : ℝ) : ℂ) *
        ((Complex.I * dotR (coeff u l) (freq (n - l))) * coeff u (n - l) j) := by
    intro l
    rw [dotR, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ((freq (n - l)) i : ℝ) = (((n - l) i : ℤ) : ℝ) := rfl
    rw [hc]
    push_cast
    ring
  rw [tsum_congr hdot, tsum_mul_left, convFull_apply (coeff u) hE hZ n j]
  push_cast
  ring

/-! ## Bonus for P4: the coefficient of the real convection field -/

/-- A pointwise product of one-periodic scalar fields is one-periodic. -/
theorem isOnePeriodic_mul {f g : ℝ³ → ℂ} (hf : IsOnePeriodic f) (hg : IsOnePeriodic g) :
    IsOnePeriodic (fun x => f x * g x) := fun x i => by
  show f (x + EuclideanSpace.single i 1) * g (x + EuclideanSpace.single i 1) = f x * g x
  rw [hf x i, hg x i]

/-- **The coefficient of the real convection field** `x ↦ fderiv ℝ u x (u x)` (the class's
`fderiv ℝ (v · t) x (v x t)` at a fixed time), component `j`, is `-2π · (convFull (coeff u) n) j`:
`fderiv_apply_expand` (CommunityClass.lean:1429) expands the directional derivative along the
basis, the cast distributes, `mFourierCoeff_finset_sum` (Descent.lean:330) splits the
coefficient, and I10 finishes.  This is the shape W3b's mode ODE (`ClassFlowODE.lean`,
`class_member_mode_ode`) consumes. -/
theorem coeff_convection {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (n : Fin 3 → ℤ) (j : Fin 3) :
    coeff (fun x => fderiv ℝ u x (u x)) n j
      = ((-(2 * Real.pi) : ℝ) : ℂ) * (convFull (coeff u) n) j := by
  rw [← convection_coeff_eq_convFull hu hp j n, coeff_apply]
  have hcont : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Continuous (descend fun x =>
      ((u x i : ℝ) : ℂ) * (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) :=
    fun i _ => continuous_descend
      ((contDiff_ofReal_component hu i).continuous.mul (continuous_factor hu i j))
      (isOnePeriodic_mul (isOnePeriodic_ofReal_component hp i) (isOnePeriodic_factor hu hp i j))
  have hsplit := mFourierCoeff_finset_sum Finset.univ (fun i => descend fun x =>
    ((u x i : ℝ) : ℂ) * (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) hcont n
  rw [← hsplit]
  congr 1
  funext z
  show (((fderiv ℝ u (rep z) (u (rep z))) j : ℝ) : ℂ)
    = ∑ i, ((u (rep z) i : ℝ) : ℂ) * (((fderiv ℝ u (rep z) (EuclideanSpace.single i 1)) j : ℝ) : ℂ)
  rw [fderiv_apply_expand (u (rep z)) j, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul]

end

end TheoremB
