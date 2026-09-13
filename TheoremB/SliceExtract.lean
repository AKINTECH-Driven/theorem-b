/-
  TheoremB/SliceExtract.lean
  Tier 9c, wave W3a (Theorem B campaign, 13 Sep 2026): the slice-extraction layer of W3.
  From the joint `C^∞` of a member of OUR COPY of the community class on the closed
  half-slab (Galilean.lean's abbrev `slab = univ ×ˢ Ici 0`) to the continuity, the
  one-periodicity and the `C^∞` of the four slices of the class equation at a fixed time
  `τ ≥ 0` (the time derivative, the Laplacian, the pressure gradient, the convection
  term), the compactness bounds on every window `Icc a b` with `0 ≤ a`, and the Laplacian
  coefficient.  Transcribed from section A of the design probe
  `audit-tier9c/design/final/Tier9cFinal.lean` (session directory, never a tracked file;
  compiled there at the pin, exit 0, no declaration with a placeholder proof; section A is
  the recon probe `recon/P1/ReconP1.lean` with the design's duplicate merges and the four
  D18 docstrings); the frozen statements are those of `context/rung12-tier9c-blueprint.md`
  section 4a (the SliceExtract block), byte-identical, and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * Order arithmetic and the slab: `one_le_infty`, `two_le_infty`, `infty_add_one_le`
    (the pin's `WithTop ℕ∞` facts, closed by `WithTop.coe_le_coe.2 le_top` and `le_rfl`,
    never by `le_top`) and `uniqueDiffOn_slab`.
  * Periodicity of the slices (I3 and its companions, no smoothness hypothesis):
    `isOnePeriodic_time_deriv_slice` (`derivWithin_congr` with the `EqOn` on `Ici 0`),
    `isOnePeriodic_laplacian` and `isOnePeriodic_laplacian_slice` (`laplacian_translate`
    at `eᵢ`, Galilean.lean), `isOnePeriodic_gradient` and `isOnePeriodic_gradient_slice`
    (`gradient_translate`), `isOnePeriodic_fderiv` (generic codomain,
    `fderiv_comp_add_right`), and `isOnePeriodic_convection_slice`.
  * The time derivative (I1, I2): `hasDerivAt_time_slice` (for `τ > 0` the
    within-derivative on `Ici 0` is a genuine derivative, through Galilean.lean's
    `derivWithin_time_slice` and `hasDerivWithinAt_time_slice`),
    `continuous_time_deriv_slice` and its `C^∞` form `contDiff_time_deriv_slice` (the
    joint `fderivWithin` on the slab is `ContinuousOn` at `1 ≤ ∞` and `ContDiffOn` at
    `∞ + 1 ≤ ∞`, applied to the direction `(0, 1)` and composed with `y ↦ (y, τ)`).
  * The compactness bounds (I4, I5, I6): `exists_bound_time_deriv_slice`,
    `exists_bound_velocity`, `exists_bound_space_deriv`: the time-derivative slice, the
    velocity and the operator norm of the space derivative are bounded uniformly in `x`
    and in `τ ∈ Icc a b`, `0 ≤ a`.  Route: `IsCompact.exists_bound_of_continuousOn` (the
    additive twin of the primed lemma) on the compact window
    `closedBall 0 2 ×ˢ Icc a b`, then periodicity moves any `x` to its representative
    `rep (fiber x)` in the ball (`norm_rep_le`: the coordinates lie in `[0, 1)`); I6
    through `fderiv_space_slice`, `opNorm_comp_le` and `norm_inl_le_one ℝ ℝ³ ℝ`.
  * The space slices: `contDiff_space_slice'` (the tree's `contDiff_space_slice` for any
    codomain, the pressure's scalar case included), `continuous_gradient_of_contDiff` and
    `continuous_gradient_slice` (the pressure gradient of a class member at fixed time),
    `contDiff_laplacian` (Mathlib has no smoothness rule for `Δ` at the pin, so the
    Laplacian of a `C^∞` vector field is assembled componentwise through the complexified
    component, `laplacian_ofReal_component`, and the second partials `dirIter i 2`),
    `continuous_laplacian_slice` (the viscous term at fixed time) and
    `continuous_convection_slice`.
  * The Laplacian coefficient (I7): `laplacian_coeff`: the coefficient of the complexified
    `j`-th component of `Δ (v · τ)` at the mode `n` is `-((2π)² ‖freq n‖²)` times the
    coefficient of the component (`laplacian_eq_sum_dirIter`, `mFourierCoeff_finset_sum`,
    the iterated bridge `mFourierCoeff_descend_dirIter` at `q = 2`, `sum_sq_twist`).
  * The generic slice facts consumed by W3b: `continuous_ofReal_component`,
    `isOnePeriodic_add`, `isOnePeriodic_sub`, `isOnePeriodic_convTerm`,
    `continuous_convTerm`.

  HONEST SCOPE.
  * Nothing here is new mathematics: the extraction of a smooth slice from a jointly smooth
    function, the periodicity of the derivatives of a periodic function, the boundedness
    of a continuous function on a compact set and the frequency multiplier of the
    Laplacian are textbook; the deliverable is the machine-checked bridge from the class's
    joint `ContDiffOn ℝ ∞ (↿v) slab` vocabulary to the per-slice vocabulary that the
    coefficient bridge (Descent.lean, DatumBridge.lean) consumes.
  * Constants: the bounds `C` of I4, I5, I6 are UNTRACKED existentials produced by
    `IsCompact.exists_bound_of_continuousOn`; the only other constant is the literal
    `-((2 * Real.pi) ^ 2 * ‖freq n‖ ^ 2)` of I7, computed by the kernel, not assumed.  No
    numeric value of any constant is claimed.
  * This file delivers NO uniqueness statement.  It is the descent-side brick layer of W3:
    the two capstones (uniqueness inside OUR COPY of the community class at `f = 0`, for the
    same datum and `0 < ν'`: the velocity on `t ≥ 0`, the pressure up to a function of time)
    are W3c's
    (`TheoremB/CommunityUnique.lean`, not built here), reached through W3b's mode ODE.
  * The class is the community's own `NavierStokesExistenceAndSmoothnessPeriodic`, copied
    in CommunityClass.lean; the upstream file carries the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
    `navier_stokes_breakdown_periodic`; this file states nothing about either, and both
    upstream placeholder proofs are untouched.  Priority is not claimed for anything.
  * `derivWithin`, `Δ`, `gradient` and `fderiv` are total: for a field without the stated
    smoothness they are well-typed junk objects, and the periodicity statements hold for
    them too (they carry no smoothness hypothesis, by design); every continuity, `C^∞` and
    boundedness statement takes `ContDiffOn ℝ ∞ (↿v) slab`.
  * This file edits no earlier file of the tree and clones no private lemma: the probe it
    is transcribed from compiled against the imported tree, so every declaration consumed
    here is public in its file.  Consumed tree files, measured by identifier grep of the
    code (docstrings stripped): CommunityClass (`IsOnePeriodic`, `fiber`,
    `laplacian_apply_component`, `laplacian_eq_sum_second`), Descent (`descend`,
    `descend_fiber`, `continuous_descend`, `rep`, `rep1`, `dirIter` and its rules,
    `mFourierCoeff_descend_dirIter`, `mFourierCoeff_finset_sum`,
    `Community.IsOnePeriodic.sub_single`), DatumBridge (`contDiff_ofReal_component`,
    `isOnePeriodic_ofReal_component`), Galilean (`slab`, `contDiff_space_slice`,
    `derivWithin_time_slice`, `hasDerivWithinAt_time_slice`, `fderiv_space_slice`,
    `laplacian_translate`, `gradient_translate`), SpectralNorms (`freq`), Calibration
    (`norm_freq_sq`), and Mathlib.
    The 34 helpers (`one_le_infty`, `two_le_infty`, `infty_add_one_le`,
    `uniqueDiffOn_slab`, `isOnePeriodic_laplacian`, `isOnePeriodic_gradient`,
    `isOnePeriodic_fderiv`, `time_deriv_slice_eq`, `continuousOn_fderivWithin_slab`,
    `continuousOn_time_deriv_joint`, `contDiffOn_fderivWithin_slab`,
    `contDiffOn_time_deriv_joint`, `rep1_mem`, `norm_rep1_le`, `rep_apply`, `norm_rep_le`,
    `rep_mem_closedBall`, `window` (abbrev), `isCompact_window`, `window_subset_slab`,
    `time_deriv_slice_rep`, `velocity_rep`, `fderiv_slice_rep`,
    `continuous_gradient_of_contDiff`, `laplacian_ofReal_component`, `dirIter_two_apply`,
    `laplacian_apply_eq_sum_dirIter`, `laplacian_eq_sum_dirIter`, `sum_sq_twist`,
    `continuous_ofReal_component`, `isOnePeriodic_add`, `isOnePeriodic_sub`,
    `isOnePeriodic_convTerm`, `continuous_convTerm`) are shipped public and carry no
    ledger line; ClassParseval.lean consumes `exists_bound_velocity`,
    `exists_bound_space_deriv` and `continuous_ofReal_component`.

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances as `df_*`; here they are
  NAMED `se_ms`, `se_haar`, `se_prob` (the Tier 9 files use `ds_*`, `db_*`; the tree's
  torus files `cr_*`, `tsyn_*`, `ts_*`, `ce_*`), because auto-named local instances from
  two modules collide in a third module that imports both.  The bodies are the three-line
  block of FourierDeriv.lean lines 31-37.  Instances are not statements; every frozen
  statement is byte-identical to the blueprint.  The probe's `-- SECTION A` marker is
  dropped; its section headings are kept.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.DatumBridge
import TheoremB.Galilean

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
local instance se_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance se_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance se_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! # A. W3a : TheoremB/SliceExtract.lean (P1) -/

theorem one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := le_rfl

/-- The closed slab is a set of unique differentiability (`univ ×ˢ Ici 0`). -/
theorem uniqueDiffOn_slab : UniqueDiffOn ℝ slab := uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)

/-! ## 1. I3: periodicity of the time-derivative slice (no smoothness), and of the
Laplacian and gradient slices -/

/-- **I3.** The time-derivative slice `x ↦ ∂_τ⁺ v x τ` (within-derivative on `Ici 0`) of a
field with one-periodic slices is one-periodic (no smoothness needed). -/
theorem isOnePeriodic_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) : IsOnePeriodic (fun x => derivWithin (v x ·) (Ici 0) τ) := by
  intro x i
  show derivWithin (v (x + EuclideanSpace.single i 1) ·) (Ici 0) τ = derivWithin (v x ·) (Ici 0) τ
  apply derivWithin_congr
  · intro t ht
    exact hper t ht x i
  · exact hper τ hτ x i

/-- The Laplacian of a one-periodic field is one-periodic (`laplacian_translate` at
`a := eᵢ`, no differentiability hypothesis). -/
theorem isOnePeriodic_laplacian {V : ℝ³ → ℝ³} (hV : IsOnePeriodic V) :
    IsOnePeriodic (fun x => Δ V x) := by
  intro x i
  have hfun : (fun y => V (y - EuclideanSpace.single i 1)) = V :=
    funext fun y => hV.sub_single y i
  have h := laplacian_translate V (EuclideanSpace.single i 1) (x + EuclideanSpace.single i 1)
  rw [hfun, add_sub_cancel_right] at h
  exact h

/-- The Laplacian slice `x ↦ Δ (v · τ) x` of a field whose time slices are one-periodic on
`t ≥ 0` is one-periodic at every `τ ≥ 0` (through `laplacian_translate`; no smoothness
hypothesis: `Δ` of a non-differentiable field is a well-typed junk object and the identity holds
for it too). -/
theorem isOnePeriodic_laplacian_slice {v : ℝ³ → ℝ → ℝ³} (hper : ∀ t ≥ 0, IsOnePeriodic (v · t))
    {τ : ℝ} (hτ : 0 ≤ τ) : IsOnePeriodic (fun x => Δ (v · τ) x) :=
  isOnePeriodic_laplacian (hper τ hτ)

/-- The gradient of a one-periodic scalar field is one-periodic (`gradient_translate`). -/
theorem isOnePeriodic_gradient {q : ℝ³ → ℝ} (hq : IsOnePeriodic q) :
    IsOnePeriodic (fun x => gradient q x) := by
  intro x i
  have hfun : (fun y => q (y - EuclideanSpace.single i 1)) = q :=
    funext fun y => hq.sub_single y i
  have h := gradient_translate q (EuclideanSpace.single i 1) (x + EuclideanSpace.single i 1)
  rw [hfun, add_sub_cancel_right] at h
  exact h

/-- The gradient slice `x ↦ gradient (p · τ) x` of a scalar field whose time slices are
one-periodic on `t ≥ 0` is one-periodic at every `τ ≥ 0` (through `gradient_translate`; no
smoothness hypothesis, as for the Laplacian slice). -/
theorem isOnePeriodic_gradient_slice {p : ℝ³ → ℝ → ℝ} (hper : ∀ t ≥ 0, IsOnePeriodic (p · t))
    {τ : ℝ} (hτ : 0 ≤ τ) : IsOnePeriodic (fun x => gradient (p · τ) x) :=
  isOnePeriodic_gradient (hper τ hτ)

/-- Periodicity passes to the Fréchet derivative (`fderiv_comp_add_right`, unconditional). -/
theorem isOnePeriodic_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : ℝ³ → F} (hp : IsOnePeriodic V) : IsOnePeriodic (fderiv ℝ V) := by
  intro x i
  have hV : (fun y => V (y + EuclideanSpace.single i 1)) = V := funext fun y => hp y i
  rw [← fderiv_comp_add_right (EuclideanSpace.single i 1), hV]

/-! ## 2. I1: the time derivative is a genuine derivative for `τ > 0` -/

/-- **I1.** For `τ > 0` the within-derivative on `Ici 0` of a class-smooth field is a genuine
derivative (`derivWithin_time_slice`, `hasDerivWithinAt_time_slice`, Galilean.lean). -/
theorem hasDerivAt_time_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (x : ℝ³) {τ : ℝ} (hτ : 0 < τ) : HasDerivAt (v x ·) (derivWithin (v x ·) (Ici 0) τ) τ := by
  rw [derivWithin_time_slice hv x hτ.le]
  exact (hasDerivWithinAt_time_slice hv x hτ.le).hasDerivAt (Ici_mem_nhds hτ)

/-! ## 3. I2: continuity of the time-derivative slice, and its C^∞ form -/

theorem time_deriv_slice_eq {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (fun x => derivWithin (v x ·) (Ici 0) τ) =
      fun x => fderivWithin ℝ (↿v) slab (x, τ) ((0 : ℝ³), (1 : ℝ)) :=
  funext fun x => derivWithin_time_slice hv x hτ

theorem continuousOn_fderivWithin_slab {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) :
    ContinuousOn (fderivWithin ℝ (↿v) slab) slab :=
  hv.continuousOn_fderivWithin uniqueDiffOn_slab one_le_infty

theorem continuousOn_time_deriv_joint {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) :
    ContinuousOn (fun q : ℝ³ × ℝ => fderivWithin ℝ (↿v) slab q ((0 : ℝ³), (1 : ℝ))) slab :=
  (continuousOn_fderivWithin_slab hv).clm_apply continuousOn_const

/-- **I2.** The time-derivative slice is continuous in space at every `τ ≥ 0`. -/
theorem continuous_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (fun x => derivWithin (v x ·) (Ici 0) τ) := by
  rw [time_deriv_slice_eq hv hτ]
  exact (continuousOn_time_deriv_joint hv).comp_continuous
    (continuous_id.prodMk continuous_const) (fun x => ⟨mem_univ _, hτ⟩)

theorem contDiffOn_fderivWithin_slab {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) :
    ContDiffOn ℝ ∞ (fderivWithin ℝ (↿v) slab) slab :=
  hv.fderivWithin uniqueDiffOn_slab infty_add_one_le

theorem contDiffOn_time_deriv_joint {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) :
    ContDiffOn ℝ ∞ (fun q : ℝ³ × ℝ => fderivWithin ℝ (↿v) slab q ((0 : ℝ³), (1 : ℝ))) slab :=
  (contDiffOn_fderivWithin_slab hv).clm_apply contDiffOn_const

/-- The time-derivative slice is `C^∞` in space at every `τ ≥ 0`. -/
theorem contDiff_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : ContDiff ℝ ∞ (fun x => derivWithin (v x ·) (Ici 0) τ) := by
  rw [time_deriv_slice_eq hv hτ]
  have hs : ContDiff ℝ ∞ (fun y : ℝ³ => ((y, τ) : ℝ³ × ℝ)) := contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun y : ℝ³ => ((y, τ) : ℝ³ × ℝ)) univ slab := fun y _ => ⟨mem_univ _, hτ⟩
  have h := (contDiffOn_time_deriv_joint hv).comp hs.contDiffOn hm
  rw [contDiffOn_univ] at h
  exact h

/-! ## 4. The compactness bounds I4, I5, I6 -/

theorem rep1_mem (z : UnitAddCircle) : rep1 z ∈ Ico (0 : ℝ) (0 + 1) := by
  unfold rep1
  exact (AddCircle.equivIco (1 : ℝ) 0 z).2

theorem norm_rep1_le (z : UnitAddCircle) : ‖rep1 z‖ ≤ 1 := by
  have h := rep1_mem z
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

theorem rep_apply (z : UnitAddTorus (Fin 3)) (i : Fin 3) : (rep z) i = rep1 (z i) := rfl

/-- The representative lies in the closed ball of radius `2` (its coordinates lie in `[0,1)`,
so its norm is at most `√3`). -/
theorem norm_rep_le (z : UnitAddTorus (Fin 3)) : ‖rep z‖ ≤ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have h : ∀ i : Fin 3, ‖(rep z) i‖ ^ 2 ≤ 1 := fun i => by
    rw [rep_apply]
    exact pow_le_one₀ (norm_nonneg _) (norm_rep1_le (z i))
  calc ∑ i : Fin 3, ‖(rep z) i‖ ^ 2 ≤ ∑ i : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun i _ => h i
    _ = 3 := by simp
    _ ≤ 2 ^ 2 := by norm_num

theorem rep_mem_closedBall (z : UnitAddTorus (Fin 3)) : rep z ∈ Metric.closedBall (0 : ℝ³) 2 :=
  mem_closedBall_zero_iff.2 (norm_rep_le z)

/-- The compact window `closedBall 0 2 ×ˢ Icc a b`. -/
abbrev window (a b : ℝ) : Set (ℝ³ × ℝ) := Metric.closedBall (0 : ℝ³) 2 ×ˢ Icc a b

theorem isCompact_window (a b : ℝ) : IsCompact (window a b) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

theorem window_subset_slab {a b : ℝ} (ha : 0 ≤ a) : window a b ⊆ slab :=
  fun _ hq => ⟨mem_univ _, le_trans ha hq.2.1⟩

/-- Periodicity moves any point to its representative in the ball. -/
theorem time_deriv_slice_rep {v : ℝ³ → ℝ → ℝ³} (hper : ∀ t ≥ 0, IsOnePeriodic (v · t))
    {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ³) :
    derivWithin (v x ·) (Ici 0) τ = derivWithin (v (rep (fiber x)) ·) (Ici 0) τ :=
  (descend_fiber (isOnePeriodic_time_deriv_slice hper hτ) x).symm

theorem velocity_rep {v : ℝ³ → ℝ → ℝ³} (hper : ∀ t ≥ 0, IsOnePeriodic (v · t))
    {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ³) : v x τ = v (rep (fiber x)) τ :=
  (descend_fiber (hper τ hτ) x).symm

theorem fderiv_slice_rep {v : ℝ³ → ℝ → ℝ³} (hper : ∀ t ≥ 0, IsOnePeriodic (v · t))
    {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ³) :
    fderiv ℝ (v · τ) x = fderiv ℝ (v · τ) (rep (fiber x)) :=
  (descend_fiber (isOnePeriodic_fderiv (hper τ hτ)) x).symm

/-- **I4.** The time-derivative slice is bounded uniformly in `x` and in `τ ∈ Icc a b`, `0 ≤ a`
(compactness of `closedBall 0 2 ×ˢ Icc a b` and periodicity); the bound is an UNTRACKED
existential. -/
theorem exists_bound_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {a b : ℝ} (ha : 0 ≤ a) : ∃ C : ℝ, ∀ x, ∀ τ ∈ Icc a b, ‖derivWithin (v x ·) (Ici 0) τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_window a b).exists_bound_of_continuousOn
    ((continuousOn_time_deriv_joint hv).mono (window_subset_slab ha))
  refine ⟨C, fun x τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := le_trans ha hτ.1
  rw [time_deriv_slice_rep hper hτ0 x, derivWithin_time_slice hv _ hτ0]
  exact hC (rep (fiber x), τ) ⟨rep_mem_closedBall _, hτ⟩

/-- **I5.** The velocity is bounded uniformly in `x` and in `τ ∈ Icc a b`, `0 ≤ a` (UNTRACKED
existential). -/
theorem exists_bound_velocity {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {a b : ℝ} (ha : 0 ≤ a) : ∃ C : ℝ, ∀ x, ∀ τ ∈ Icc a b, ‖v x τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_window a b).exists_bound_of_continuousOn
    (hv.continuousOn.mono (window_subset_slab ha))
  refine ⟨C, fun x τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := le_trans ha hτ.1
  rw [velocity_rep hper hτ0 x]
  exact hC (rep (fiber x), τ) ⟨rep_mem_closedBall _, hτ⟩

/-- **I6.** The space derivative (operator norm) is bounded uniformly in `x` and in
`τ ∈ Icc a b`, `0 ≤ a` (UNTRACKED existential). -/
theorem exists_bound_space_deriv {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {a b : ℝ} (ha : 0 ≤ a) : ∃ C : ℝ, ∀ x, ∀ τ ∈ Icc a b, ‖fderiv ℝ (v · τ) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_window a b).exists_bound_of_continuousOn
    ((continuousOn_fderivWithin_slab hv).mono (window_subset_slab ha))
  refine ⟨C, fun x τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := le_trans ha hτ.1
  rw [fderiv_slice_rep hper hτ0 x, fderiv_space_slice hv _ hτ0]
  have hK := hC (rep (fiber x), τ) ⟨rep_mem_closedBall _, hτ⟩
  calc ‖(fderivWithin ℝ (↿v) slab (rep (fiber x), τ)).comp (ContinuousLinearMap.inl ℝ ℝ³ ℝ)‖
      ≤ ‖fderivWithin ℝ (↿v) slab (rep (fiber x), τ)‖ * ‖ContinuousLinearMap.inl ℝ ℝ³ ℝ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderivWithin ℝ (↿v) slab (rep (fiber x), τ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ ℝ³ ℝ) (norm_nonneg _)
    _ = ‖fderivWithin ℝ (↿v) slab (rep (fiber x), τ)‖ := mul_one _
    _ ≤ C := hK


/-! ## 5. The scalar (any-codomain) space slice and the gradient slice -/

/-- Clone of `contDiff_space_slice` for any codomain (the tree's is `ℝ³`-valued only). -/
theorem contDiff_space_slice' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : ℝ³ → ℝ → F} (hw : ContDiffOn ℝ ∞ (↿w) slab) {τ : ℝ} (hτ : 0 ≤ τ) :
    ContDiff ℝ ∞ (w · τ) := by
  have hs : ContDiff ℝ ∞ (fun y : ℝ³ => ((y, τ) : ℝ³ × ℝ)) := contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun y : ℝ³ => ((y, τ) : ℝ³ × ℝ)) univ slab := fun y _ => ⟨mem_univ _, hτ⟩
  have h := hw.comp hs.contDiffOn hm
  rw [contDiffOn_univ] at h
  exact h

/-- The gradient of a `C^∞` scalar field is continuous (`gradient = toDual.symm ∘ fderiv`). -/
theorem continuous_gradient_of_contDiff {q : ℝ³ → ℝ} (hq : ContDiff ℝ ∞ q) :
    Continuous (gradient q) := by
  unfold gradient
  exact (toDual ℝ ℝ³).symm.continuous.comp (hq.continuous_fderiv (by simp))

/-- The gradient slice of a scalar field that is `C^∞` on the closed slab is continuous at
every `τ ≥ 0` (the slice is `C^∞` by `contDiff_space_slice'`, and `gradient = toDual.symm ∘
fderiv`). This is the pressure gradient of a class member at fixed time. -/
theorem continuous_gradient_slice {p : ℝ³ → ℝ → ℝ} (hp : ContDiffOn ℝ ∞ (↿p) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (gradient (p · τ)) :=
  continuous_gradient_of_contDiff (contDiff_space_slice' hp hτ)

/-! ## 6. I7: the Laplacian coefficient -/

/-- The complexified component of the Laplacian is the Laplacian of the complexified
component (`laplacian_apply_component`, then `ContDiffAt.laplacian_CLM_comp_left` with
`Complex.ofRealCLM`, the pattern of the tree's `laplacian_re`). -/
theorem laplacian_ofReal_component {V : ℝ³ → ℝ³} (hV : ContDiff ℝ ∞ V) (j : Fin 3) (x : ℝ³) :
    Δ (fun y => ((V y j : ℝ) : ℂ)) x = (((Δ V x) j : ℝ) : ℂ) := by
  rw [laplacian_apply_component (hV.contDiffAt.of_le two_le_infty) j]
  have h2 : ContDiffAt ℝ 2 (fun y => V y j) x :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hV).contDiffAt.of_le two_le_infty
  have h := ContDiffAt.laplacian_CLM_comp_left (l := Complex.ofRealCLM) h2
  -- MEASURED: `exact h` closes it (`ofRealCLM r` and `(r : ℂ)` are defeq at default transparency).
  exact h

/-- Two partial derivatives in direction `i`, unfolded (`dirIter_succ` twice, then `rfl`). -/
theorem dirIter_two_apply (i : Fin 3) (f : ℝ³ → ℂ) (x : ℝ³) :
    dirIter i 2 f x =
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
  rw [dirIter_succ, dirIter_succ, dirIter_zero]
  rfl

/-- `Δ f x = ∑ᵢ ∂ᵢ² f x` for a `C^∞` scalar field, in the `dirIter` spelling (pointwise). -/
theorem laplacian_apply_eq_sum_dirIter {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f) (x : ℝ³) :
    Δ f x = ∑ i : Fin 3, dirIter i 2 f x := by
  rw [laplacian_eq_sum_second (hf.of_le two_le_infty) x]
  exact Finset.sum_congr rfl fun i _ => (dirIter_two_apply i f x).symm

/-- `Δ f = ∑ᵢ ∂ᵢ² f` for a `C^∞` scalar field, in the `dirIter` spelling (as functions). -/
theorem laplacian_eq_sum_dirIter {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x => Δ f x) = fun x => ∑ i : Fin 3, dirIter i 2 f x :=
  funext fun x => laplacian_apply_eq_sum_dirIter hf x

/-- The Laplacian of a `C^∞` vector field is `C^∞` (componentwise through the complexified
component, `laplacian_ofReal_component`, then `∑ᵢ dirIter i 2`, then `Complex.reCLM`;
`contDiff_euclidean` packs the components). -/
theorem contDiff_laplacian {V : ℝ³ → ℝ³} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => Δ V x) := by
  rw [contDiff_euclidean]
  intro j
  have hf : ContDiff ℝ ∞ (fun x => ((V x j : ℝ) : ℂ)) := contDiff_ofReal_component hV j
  have hsum : ContDiff ℝ ∞ (fun x => ∑ i : Fin 3, dirIter i 2 (fun y => ((V y j : ℝ) : ℂ)) x) :=
    ContDiff.sum fun i _ => contDiff_dirIter i hf 2
  have heq : (fun x => (Δ V x) j) =
      fun x => (∑ i : Fin 3, dirIter i 2 (fun y => ((V y j : ℝ) : ℂ)) x).re := by
    funext x
    rw [← laplacian_apply_eq_sum_dirIter hf x, laplacian_ofReal_component hV j x,
      Complex.ofReal_re]
  rw [heq]
  exact Complex.reCLM.contDiff.comp hsum

/-- The Laplacian slice of a field that is `C^∞` on the closed slab is continuous at every
`τ ≥ 0` (the slice is `C^∞` by `contDiff_space_slice`, its Laplacian by `contDiff_laplacian`,
assembled componentwise because Mathlib has no smoothness rule for `Δ` at the pin). This is the
viscous term of a class member at fixed time. -/
theorem continuous_laplacian_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (fun x => Δ (v · τ) x) :=
  (contDiff_laplacian (contDiff_space_slice hv hτ)).continuous

/-- The convection slice `x ↦ (v·∇)v` at time `τ` is continuous (bonus for the coefficient
extraction; its coefficient is `ConvectionCoeff.lean`'s `coeff_convection`). -/
theorem continuous_convection_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (fun x => fderiv ℝ (v · τ) x (v x τ)) :=
  ((contDiff_space_slice hv hτ).continuous_fderiv (by simp)).clm_apply
    (contDiff_space_slice hv hτ).continuous

/-- The convection slice is one-periodic (no differentiability hypothesis). -/
theorem isOnePeriodic_convection_slice {v : ℝ³ → ℝ → ℝ³}
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsOnePeriodic (fun x => fderiv ℝ (v · τ) x (v x τ)) := by
  intro x i
  show fderiv ℝ (v · τ) (x + EuclideanSpace.single i 1) (v (x + EuclideanSpace.single i 1) τ)
    = fderiv ℝ (v · τ) x (v x τ)
  -- TRAP: the periodicity lemmas deliver `(fun x => …) (x + e) = (fun x => …) x` un-beta-reduced;
  -- `rw` needs the beta-reduced form, so restate through `have`.
  have h1 : fderiv ℝ (v · τ) (x + EuclideanSpace.single i 1) = fderiv ℝ (v · τ) x :=
    isOnePeriodic_fderiv (hper τ hτ) x i
  have h2 : v (x + EuclideanSpace.single i 1) τ = v x τ := hper τ hτ x i
  rw [h1, h2]

/-- `∑ᵢ (2πi nᵢ)² = -(2π)² ‖freq n‖²` in `ℂ` (`norm_freq_sq`, `push_cast`, `I_sq`). -/
theorem sum_sq_twist (n : Fin 3 → ℤ) :
    ∑ i : Fin 3, (2 * (Real.pi : ℂ) * Complex.I * ((n i : ℤ) : ℂ)) ^ 2 =
      (((-((2 * Real.pi) ^ 2 * ‖freq n‖ ^ 2)) : ℝ) : ℂ) := by
  rw [norm_freq_sq]
  push_cast
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  linear_combination ((2 * (Real.pi : ℂ)) ^ 2 * (((n 0 : ℤ) : ℂ) ^ 2 + ((n 1 : ℤ) : ℂ) ^ 2
    + ((n 2 : ℤ) : ℂ) ^ 2)) * Complex.I_sq

/-- **I7, the Laplacian coefficient.** The coefficient of the complexified `j`-th component of
`Δ (v · τ)` is `-(2π)² ‖freq n‖²` times the coefficient of the component (the iterated bridge
`mFourierCoeff_descend_dirIter` at `q = 2`, three directions summed, `sum_sq_twist`). The
`(2π)²` is computed, not assumed. -/
theorem laplacian_coeff {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) (j : Fin 3) (n : Fin 3 → ℤ) : mFourierCoeff (descend fun x => (((Δ (v · τ) x) j : ℝ) : ℂ)) n = (((-((2 * Real.pi) ^ 2 * ‖freq n‖ ^ 2)) : ℝ) : ℂ) * mFourierCoeff (descend fun x => ((v x τ j : ℝ) : ℂ)) n := by
  have hV : ContDiff ℝ ∞ (v · τ) := contDiff_space_slice hv hτ
  have hf : ContDiff ℝ ∞ (fun x => ((v x τ j : ℝ) : ℂ)) := contDiff_ofReal_component hV j
  have hfp : IsOnePeriodic (fun x => ((v x τ j : ℝ) : ℂ)) :=
    isOnePeriodic_ofReal_component (hper τ hτ) j
  -- Step 1: the integrand is the Laplacian of the complexified component.
  have h1 : (fun x => (((Δ (v · τ) x) j : ℝ) : ℂ)) = fun x => Δ (fun y => ((v y τ j : ℝ) : ℂ)) x :=
    funext fun x => (laplacian_ofReal_component hV j x).symm
  -- Step 2: the Laplacian is the sum of the three second partials.
  have h2 := laplacian_eq_sum_dirIter hf
  -- Step 3: the descent of a finite sum is the finite sum of the descents (rfl).
  have h3 : descend (fun x => ∑ i : Fin 3, dirIter i 2 (fun y => ((v y τ j : ℝ) : ℂ)) x) =
      fun z => ∑ i : Fin 3, descend (dirIter i 2 (fun y => ((v y τ j : ℝ) : ℂ))) z := rfl
  rw [h1, h2, h3, mFourierCoeff_finset_sum Finset.univ
    (fun i => descend (dirIter i 2 (fun y => ((v y τ j : ℝ) : ℂ))))
    (fun i _ => continuous_descend (contDiff_dirIter i hf 2).continuous
      (dirIter_isOnePeriodic i hfp 2)) n]
  rw [Finset.sum_congr rfl (fun i _ => mFourierCoeff_descend_dirIter i hf hfp 2 n),
    ← Finset.sum_mul, sum_sq_twist]

/-! ## 7. Slice facts consumed downstream (by W3b's `ClassFlowODE.lean`, generic field) -/

/-- The complexified `j`-th component of a continuous `ℝ³`-valued field is continuous. -/
theorem continuous_ofReal_component {u : ℝ³ → ℝ³} (hu : Continuous u) (j : Fin 3) :
    Continuous (fun x => ((u x j : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hu)

theorem isOnePeriodic_add {F : Type*} [Add F] {f g : ℝ³ → F} (hf : IsOnePeriodic f)
    (hg : IsOnePeriodic g) : IsOnePeriodic fun x => f x + g x := by
  intro x i
  show f (x + _) + g (x + _) = f x + g x
  rw [hf x i, hg x i]

theorem isOnePeriodic_sub {F : Type*} [Sub F] {f g : ℝ³ → F} (hf : IsOnePeriodic f)
    (hg : IsOnePeriodic g) : IsOnePeriodic fun x => f x - g x := by
  intro x i
  show f (x + _) - g (x + _) = f x - g x
  rw [hf x i, hg x i]

theorem isOnePeriodic_convTerm {V : ℝ³ → ℝ³} (hp : IsOnePeriodic V) :
    IsOnePeriodic fun x => fderiv ℝ V x (V x) := by
  intro x i
  show fderiv ℝ V (x + _) (V (x + _)) = fderiv ℝ V x (V x)
  rw [isOnePeriodic_fderiv hp x i, hp x i]

theorem continuous_convTerm {V : ℝ³ → ℝ³} (hV : ContDiff ℝ ∞ V) :
    Continuous fun x => fderiv ℝ V x (V x) :=
  (hV.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk hV.continuous)

end

end TheoremB
