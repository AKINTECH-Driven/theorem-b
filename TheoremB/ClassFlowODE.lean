/-
  TheoremB/ClassFlowODE.lean
  Tier 9c, wave W3b (Theorem B campaign, 13 Sep 2026): the time side of W3.  The coefficient
  flow `classFlow` of a member of OUR COPY of the community class in the campaign clock
  `t = 2πτ`, defined ONCE here (blueprint D2); the dominated continuity and differentiation of
  the torus parametric integral (Mathlib only); the mode continuity on every window (I8, the H2
  group of `theorem_B_unique`) and the derivative of the flow (I9); the forward FTC on a window
  (I14); the linearity of `coeff`; the pressure-gradient coefficient and its Leray kill at every
  mode; the divergence-free bookkeeping; the Laplacian and convection coefficients packed into
  `Vel`; and THE CALIBRATION IN REVERSE: the class equation read through `coeff` in the clock
  `t = 2πτ` IS the campaign mode ODE at `ν = 2πν'` (I12, for every real `ν'`), and its integral
  form on every window (I13, the H6 group).  Transcribed from section D of the design probe
  `audit-tier9c/design/final/Tier9cFinal.lean` (session directory, never a tracked file;
  compiled there at the pin, exit 0, no declaration with a placeholder proof; section D stitches
  the recon probes `recon/P7/ReconP7.lean` section 1 (the flow), `recon/P2/ReconP2.lean` (the
  parametric integral, with the `ha` binder of its two open-window helpers dropped, D6),
  `recon/P5/ReconP5.lean` (the forward FTC) and `recon/P4/ReconP4.lean` (the calibration, with
  the unused `hν'` of I12 and I13 dropped, D14, and `convection_coeff_vel` proved from
  ConvectionCoeff.lean's `coeff_convection`, D10)); the frozen statements are those of
  `context/rung12-tier9c-blueprint.md` section 4b (the ClassFlowODE block), byte-identical, and
  the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * The flow: `classFlow v t := coeff (v · (t / (2 * Real.pi)))` (D0, the only `def` of the
    file), `classFlow_apply` (`rfl`), `classFlow_clock` (`classFlow v (2πτ) = coeff (v · τ)`,
    `mul_div_cancel_left₀`) and `classFlow_zero_eq` (`classFlow v 0 = coeff (v · 0)`, no class
    hypothesis).  `classFlow` is total: for a `v` that is not the velocity of a class member it
    is a well-typed junk object; the frozen interface statements below keep the inline spelling
    `coeff (v · (t / (2 * Real.pi))) k` verbatim (D2).
  * The parametric integral (Mathlib only): `continuous_space_slice_of_continuousOn`,
    `continuousOn_time_slice_of_continuousOn` (slices of a field jointly continuous on the slab),
    `continuousOn_coeff_of_dominated` (`MeasureTheory.continuousOn_of_dominated` with a constant
    bound, integrable on the probability torus) and `hasDerivAt_coeff_of_dominated`
    (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on an open window, `.2`); the `Vel`
    packing `continuousOn_uncurry_ofReal_component`, `hasDerivAt_ofReal_component`,
    `norm_ofReal_component_le`, `continuousOn_coeff_vel` (`continuousOn_pi` and the ℝ-linear
    `(PiLp.continuousLinearEquiv 2 ℝ _).symm`) and `hasDerivAt_coeff_vel` (`hasDerivAt_pi`).
  * The class-member specialisations: `mapsTo_clock`, I8 `classFlow_continuousOn` (H2: every
    mode of the flow is continuous on `Icc 0 T`; SliceExtract.lean's I5 on `Icc 0 (T/(2π))`,
    then the clock), `hasDerivAt_clock` and I9 `hasDerivAt_classFlow` (for `t > 0` the flow has
    derivative `(1/(2π)) • coeff (∂_τ⁺ v · (t/(2π)))`; dominated differentiation on the window
    `Ioo (τ/2) (2τ)` from SliceExtract.lean's I1 to I4, then `HasDerivAt.scomp` with its point
    and inner function given explicitly).
  * The forward FTC: I14 `integral_eq_of_hasDerivAt` (a `Vel`-valued curve continuous on
    `Icc 0 T`, differentiable on `Ioo 0 T` with a continuous derivative, satisfies
    `f t = f 0 + ∫ s in 0..t, g s` on the window;
    `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, no `t = 0` case split).
  * The Leray kill of the packed gradient: `dotR_castCV_freq`, `lerayProj_smul_castCV_freq`,
    `lerayProj_pressure_gradient` (`k ≠ 0`: the packed vector `(2πi kⱼ p̂)ⱼ` is
    `(2πi p̂) • castCV (freq k)`).
  * The linearity of `coeff`: `mFourierCoeff_add`, `mFourierCoeff_sub`, `mFourierCoeff_neg`,
    `mFourierCoeff_const_mul` (`integral_add`, `integral_sub`, `integral_neg`,
    `integral_const_mul`) and the packed rules `coeff_add`, `coeff_sub` (both fields continuous
    and one-periodic), `coeff_smul` and `coeff_neg` (NO hypothesis: `integral_const_mul` and
    `integral_neg` are unconditional).
  * The pressure gradient: `isOnePeriodic_ofReal_scalar`, `pressure_gradient_coeff`
    (`coeff (∇(p · τ)) n = (2πi nⱼ p̂(n))ⱼ` through `gradient_apply_eq_fderiv_single`,
    `Complex.ofRealCLM` and `mFourierCoeff_descend_fderiv` at `C^1`) and
    `lerayProj_pressure_gradient_coeff` (the gradient mode is killed by `lerayProj n` at EVERY
    mode `n`, `n = 0` included: there the packed vector is `0`, `dotR_zero_left`).
  * The divergence-free bookkeeping: `divFree_slice` (H5 per slice, DatumBridge.lean's
    `divFree_coeff`), `lerayProj_of_divFree` (the projection is the identity on a vector
    orthogonal to its frequency) and `divFree_deriv` (the derivative of a divergence-free mode
    is divergence-free: the pairing against the frequency differentiated as the finite component
    sum through `EuclideanSpace.proj … restrictScalars ℝ` and `HasDerivAt.fun_sum`, then
    `HasDerivAt.unique` against the eventually-zero function).
  * The two packed coefficient facts: `class_eq_force_free` (the class equation with the
    `(f := 0)` term removed, `simp only [Pi.zero_apply, add_zero]`), `laplacian_coeff_vel` (I7
    packed: `coeff (Δ (v · τ)) n = (−(2π)²‖freq n‖²) • coeff (v · τ) n`),
    `convection_coeff_vel` (I10 packed: `coeff ((u·∇)u) n = (−2π) • convFull (coeff u) n`, from
    ConvectionCoeff.lean's `coeff_convection`), `real_smul_eq_coe_smul_vel` and
    `lerayProj_real_smul`.
  * THE CALIBRATION IN REVERSE, I12 `class_member_mode_ode`: for a member `(v, p)` of OUR COPY
    of the class at `f = 0` and viscosity `ν'`, every mode `k` of the flow
    `c t k := coeff (v · (t/(2π))) k` satisfies, for every `t > 0`,
    `c' t k = (−2πν'‖freq k‖²) • c t k + lerayProj k (convFull (c t) k)`, the campaign mode
    ODE at `ν = 2πν'`.  The constants, named per constant and computed by the kernel
    (`field_simp; ring` on `PiLp.ext`): the `−(2π)²` of the Laplacian bridge (I7) against the
    `1/(2π)` of the clock gives `−2πν'‖k‖²`; the `−2π` of the convection bridge (I10) against the
    same `1/(2π)` gives `+ convFull`; the gradient mode is killed by `lerayProj k` for every `k`
    (`k = 0` included); the left-hand side survives `lerayProj k` because the derivative of a
    divergence-free mode is divergence-free (`divFree_deriv`).  The mode ODE holds for EVERY
    real `ν'` (D14: no `hν'` binder; positivity of `ν'` is consumed only by `theorem_B_unique`).
  * The integral form on every window, I13 `class_member_integral_eq` (H6):
    `c t k = coeff u₀ k + ∫ s in 0..t, ((−2πν'‖freq k‖²) • c s k + lerayProj k (convFull (c s) k))`
    for every `t ∈ Icc 0 T` and every `k`: the right-hand side is continuous through I8,
    ClassParseval.lean's budgets I11 with the finite-sum bounds `Summable.sum_le_tsum` for
    ConvContinuity.lean's `continuousOn_convFull`, and `lerayProj_continuous`; I12 on `Ioo 0 T`;
    the initial value from the class's `initial_condition`; then I14.  For every real `ν'`
    (D14).

  HONEST SCOPE.
  * Nothing here is new mathematics: differentiation under the integral sign, the forward
    fundamental theorem of calculus and the calibration of a PDE's Fourier modes to a coefficient
    system are textbook; Mathlib supplies the two dominated-convergence engines and the FTC at the
    pin; the deliverable is the machine-checked identity between the class equation of OUR COPY
    of the community class (CommunityClass.lean) read coefficient by coefficient and the
    campaign's mode ODE (the H6 group of `theorem_B_unique`, FullUnique.lean), with every
    constant computed and named.
  * Constants: the bound `C` of the dominated-convergence hypotheses is an UNTRACKED
    existential produced by SliceExtract.lean's compactness bounds I4 and I5
    (`IsCompact.exists_bound_of_continuousOn`); the budgets `E`, `Z` of I13's continuity step are
    ClassParseval.lean's UNTRACKED existentials of I11; the constants of the calibration,
    `−(2π)²` in I7, `−2π` in I10, `1/(2π)` for the clock and `−2πν'` in I12, are literal
    expressions computed by the kernel.  No numeric value of any constant is claimed.
  * This file delivers NO uniqueness statement.  It delivers the coefficient flow of a class
    member, its mode ODE and its integral equation: the H2 and H6 groups of `theorem_B_unique`
    for that flow (H4 is ClassParseval.lean's I11; H1, H3, H5 in the flow spelling are W3c's).
    The two capstones (uniqueness inside OUR COPY of the community class at `f = 0`, for the
    same datum and `0 < ν'`: the velocity on `t ≥ 0`, the pressure up to a function of time) are
    W3c's (`TheoremB/CommunityUnique.lean`, not built here), a corollary of `theorem_B_unique`
    (Tier 4) through the datum bridge (Tier 9 W1), the textbook energy method in the enstrophy
    class; `theorem_B_unique` is consumed there, not here.
  * The class is the community's own `NavierStokesExistenceAndSmoothnessPeriodic`, copied in
    CommunityClass.lean; the upstream file carries the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
    `navier_stokes_breakdown_periodic`; this file states nothing about either, and both upstream
    placeholder proofs are untouched.  Priority is not claimed for anything; where uniqueness is
    described (W3c) the neighbours are HeliCorgi's local mild uniqueness on `ℝ³` and
    uda-lab/leray-hopf, named there.
  * The unused binders `hT : 0 ≤ T` of `classFlow_continuousOn` (I8) and
    `integral_eq_of_hasDerivAt` (I14) are kept as agreed (blueprint D6: `Icc 0 T` is empty for
    `T < 0`, so the binder is content-free; dropping it would change the frozen shape); two
    linter warnings are expected, plus the pin's `τ` note on
    `continuous_space_slice_of_continuousOn` (the binder is used through the slice notation).
  * `coeff u` and `classFlow v` are total (DatumBridge.lean): outside the stated continuity and
    periodicity they are well-typed junk objects; every statement here carries the hypotheses it
    needs (`coeff_smul` and `coeff_neg` need none, by the unconditional integral rules).
  * This file edits no earlier file of the tree and clones no private lemma: every declaration
    consumed here is public in its file.  Consumed tree files, measured by identifier grep of
    the code (docstrings stripped): SliceExtract (`hasDerivAt_time_slice`,
    `continuous_time_deriv_slice`, `isOnePeriodic_time_deriv_slice`,
    `exists_bound_time_deriv_slice`, `exists_bound_velocity`, `laplacian_coeff`,
    `contDiff_space_slice'`, `continuous_gradient_of_contDiff`, `continuous_ofReal_component`,
    `isOnePeriodic_add`, `isOnePeriodic_gradient`, `isOnePeriodic_convTerm`,
    `continuous_convTerm`; reached through the import of ClassParseval), ConvectionCoeff
    (`coeff_convection`; the import), ClassParseval (`classFlow_budget`; the import),
    CommunityData (`dotR_zero_left`, the public clone at its line 226; the import, the one
    identifier that needs it), CommunityClass (`IsOnePeriodic`,
    `NavierStokesExistenceAndSmoothnessPeriodic`, `gradient_apply_eq_fderiv_single`), Descent
    (`descend`, `rep`, `continuous_descend`, `integrable_of_continuous`,
    `mFourierCoeff_descend_fderiv`), DatumBridge (`coeff`, `coeff_apply`,
    `isOnePeriodic_ofReal_component`, `summable_sob_coeff`, `divFree_coeff`), Galilean (`slab`,
    `contDiff_space_slice`), NSGalerkin (`Vel`, `castCV`, `dotR`, `DivFree`, `lerayProj`),
    NSFull (`convFull`), SpectralNorms (`freq`, `norm_freq`, `one_le_norm_freq`), TimeSmooth
    (`lerayProj_add`, `lerayProj_smul`), LimitHelpers (`lerayProj_sub`, `lerayProj_continuous`),
    ConvContinuity (`continuousOn_convFull`), PeriodicLift (`norm_mFourier_apply`), and Mathlib.
    The 18 helpers (`continuous_space_slice_of_continuousOn`,
    `continuousOn_time_slice_of_continuousOn`, `continuousOn_uncurry_ofReal_component`,
    `hasDerivAt_ofReal_component`, `norm_ofReal_component_le`, `mapsTo_clock`,
    `hasDerivAt_clock`, `dotR_castCV_freq`, `lerayProj_smul_castCV_freq`, `mFourierCoeff_add`,
    `mFourierCoeff_sub`, `mFourierCoeff_neg`, `mFourierCoeff_const_mul`,
    `isOnePeriodic_ofReal_scalar`, `lerayProj_of_divFree`, `class_eq_force_free`,
    `real_smul_eq_coe_smul_vel`, `lerayProj_real_smul`) are shipped public and carry no ledger
    line; `def classFlow` is frozen (fenced, byte-identity checked) and carries no ledger line
    either; the 23 frozen theorems carry one each (gate 421 to 444, entries 422 to 444).

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances as `df_*`; here they are NAMED
  `co_ms`, `co_haar`, `co_prob` (SliceExtract.lean uses `se_*`, ConvectionCoeff.lean `cc_*`,
  ClassParseval.lean `cp_*`; `co_*` is the prefix the feasibility critic's module chain
  compiled), because auto-named local instances from two modules collide in a third module that
  imports both.  The bodies are the three-line block of FourierDeriv.lean lines 31-37.
  Instances are not statements; every frozen statement is byte-identical to the blueprint.  The
  probe's `-- SECTION D` marker is dropped; its section headings are kept.  No sibling was added
  and no spec drift is recorded: every frozen statement is proved as written.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.CommunityData
import TheoremB.ClassParseval
import TheoremB.ConvectionCoeff

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
local instance co_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance co_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance co_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! # D. W3b : TheoremB/ClassFlowODE.lean (classFlow; P2; P5's FTC; P4) -/

/-! ## D0. The canonical spelling of the coefficient flow (P7 section 1) -/

/-- The coefficient flow of a class member in the campaign clock `t = 2πτ`:
`classFlow v t = coeff (v · (t / (2π)))`.  The canonical spelling for W3. -/
def classFlow (v : ℝ³ → ℝ → ℝ³) (t : ℝ) : (Fin 3 → ℤ) → Vel :=
  coeff (v · (t / (2 * Real.pi)))

/-- `classFlow` unfolds by `rfl` to R6's spelling. -/
theorem classFlow_apply (v : ℝ³ → ℝ → ℝ³) (t : ℝ) (k : Fin 3 → ℤ) :
    classFlow v t k = coeff (v · (t / (2 * Real.pi))) k := rfl

/-- The clock change: at campaign time `2πτ` the flow is the coefficient field of the
class slice at `τ`. -/
theorem classFlow_clock (v : ℝ³ → ℝ → ℝ³) (τ : ℝ) :
    classFlow v (2 * Real.pi * τ) = coeff (v · τ) := by
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  unfold classFlow
  rw [mul_div_cancel_left₀ _ h2π]

/-- At campaign time `0` the flow is the coefficient field of the slice at `0` (no class
hypothesis; the H1 form `classFlow_zero` with the datum is W3c's, `CommunityUnique.lean`,
not built here). -/
theorem classFlow_zero_eq (v : ℝ³ → ℝ → ℝ³) : classFlow v 0 = coeff (v · 0) := by
  unfold classFlow
  rw [zero_div]

/-! ## D1. Dominated continuity and differentiation of the torus parametric integral (P2) -/

/-! ## Slices of a jointly continuous field on the slab -/

/-- The space slice at a time `τ ≥ 0` of a field jointly continuous on the slab is
continuous (the slice `y ↦ (y, τ)` maps everything into the slab). -/
theorem continuous_space_slice_of_continuousOn {E : Type*} [TopologicalSpace E]
    {G : ℝ³ → ℝ → E} (hG : ContinuousOn (↿G) slab) {τ : ℝ} (hτ : 0 ≤ τ) :
    Continuous (G · τ) :=
  hG.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨mem_univ _, hτ⟩

/-- The time slice at a point `x` of a field jointly continuous on the slab is continuous
on every `Icc a b` with `0 ≤ a`. -/
theorem continuousOn_time_slice_of_continuousOn {E : Type*} [TopologicalSpace E]
    {G : ℝ³ → ℝ → E} (hG : ContinuousOn (↿G) slab) (x : ℝ³) {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (G x ·) (Icc a b) :=
  hG.comp (continuous_const.prodMk continuous_id).continuousOn
    fun τ hτ => ⟨mem_univ _, ha.trans hτ.1⟩

/-! ## (1) Dominated continuity of the coefficient in time -/

/-- **Dominated continuity.**  The `n`-th coefficient of the descent of a time-dependent
one-periodic scalar field, jointly continuous on the slab and bounded on the window, is
continuous in time on the window (`MeasureTheory.continuousOn_of_dominated` with the
constant bound, integrable on the probability torus). -/
theorem continuousOn_coeff_of_dominated {G : ℝ³ → ℝ → ℂ} {a b C : ℝ} (ha : 0 ≤ a)
    (hG : ContinuousOn (↿G) slab) (hper : ∀ τ ≥ 0, IsOnePeriodic (G · τ))
    (hC : ∀ x, ∀ τ ∈ Icc a b, ‖G x τ‖ ≤ C) (n : Fin 3 → ℤ) :
    ContinuousOn (fun τ => mFourierCoeff (descend (G · τ)) n) (Icc a b) := by
  unfold mFourierCoeff
  refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ ?_ ?_
  · intro τ hτ
    have hτ0 : 0 ≤ τ := ha.trans hτ.1
    exact ((mFourier (-n)).continuous.smul
      (continuous_descend (continuous_space_slice_of_continuousOn hG hτ0) (hper τ hτ0)))
      |>.aestronglyMeasurable
  · intro τ hτ
    refine ae_of_all _ fun z => ?_
    rw [norm_smul, norm_mFourier_apply, one_mul]
    exact hC (rep z) τ hτ
  · exact integrable_const C
  · refine ae_of_all _ fun z => ?_
    exact (continuousOn_time_slice_of_continuousOn hG (rep z) ha).const_smul (mFourier (-n) z)

/-! ## (2) Dominated differentiation of the coefficient in time -/

/-- **Dominated differentiation.**  On an open window `Ioo a b` with `0 ≤ a`, if the field
`G` has time derivative `G'` pointwise, both slices are continuous and one-periodic, and
`G'` is bounded on the window, then the `n`-th coefficient of the descent of `G · τ` has
time derivative the `n`-th coefficient of the descent of `G' · τ₀` at every interior
`τ₀` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the constant bound). -/
theorem hasDerivAt_coeff_of_dominated {G G' : ℝ³ → ℝ → ℂ} {a b C : ℝ}
    (hcont : ∀ τ ∈ Ioo a b, Continuous (G · τ)) (hcont' : ∀ τ ∈ Ioo a b, Continuous (G' · τ))
    (hper : ∀ τ ∈ Ioo a b, IsOnePeriodic (G · τ))
    (hper' : ∀ τ ∈ Ioo a b, IsOnePeriodic (G' · τ))
    (hd : ∀ x, ∀ τ ∈ Ioo a b, HasDerivAt (G x ·) (G' x τ) τ)
    (hC : ∀ x, ∀ τ ∈ Ioo a b, ‖G' x τ‖ ≤ C) (n : Fin 3 → ℤ) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo a b) :
    HasDerivAt (fun τ => mFourierCoeff (descend (G · τ)) n)
      (mFourierCoeff (descend (G' · τ₀)) n) τ₀ := by
  unfold mFourierCoeff
  have hs : Ioo a b ∈ 𝓝 τ₀ := Ioo_mem_nhds hτ₀.1 hτ₀.2
  have hmeas : ∀ τ ∈ Ioo a b,
      AEStronglyMeasurable (fun z => mFourier (-n) z • descend (G · τ) z)
        (volume : Measure (UnitAddTorus (Fin 3))) := fun τ hτ =>
    ((mFourier (-n)).continuous.smul (continuous_descend (hcont τ hτ) (hper τ hτ)))
      |>.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun z => mFourier (-n) z • descend (G' · τ₀) z)
      (volume : Measure (UnitAddTorus (Fin 3))) :=
    ((mFourier (-n)).continuous.smul (continuous_descend (hcont' τ₀ hτ₀) (hper' τ₀ hτ₀)))
      |>.aestronglyMeasurable
  have hint : Integrable (fun z => mFourier (-n) z • descend (G · τ₀) z)
      (volume : Measure (UnitAddTorus (Fin 3))) :=
    integrable_of_continuous
      ((mFourier (-n)).continuous.smul (continuous_descend (hcont τ₀ hτ₀) (hper τ₀ hτ₀)))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (UnitAddTorus (Fin 3))))
    (F := fun τ z => mFourier (-n) z • descend (G · τ) z)
    (F' := fun τ z => mFourier (-n) z • descend (G' · τ) z)
    (bound := fun _ => C) hs (eventually_of_mem hs hmeas) hint hmeas'
    (ae_of_all _ fun z τ hτ => by
      rw [norm_smul, norm_mFourier_apply, one_mul]
      exact hC (rep z) τ hτ)
    (integrable_const C)
    (ae_of_all _ fun z τ hτ => (hd (rep z) τ hτ).const_smul (mFourier (-n) z))
  exact h.2

/-! ## (3) The `Vel` packing -/

/-- Componentwise (real-part) continuity of the complexified components. -/
theorem continuousOn_uncurry_ofReal_component {V : ℝ³ → ℝ → ℝ³}
    (hV : ContinuousOn (↿V) slab) (j : Fin 3) :
    ContinuousOn (↿(fun x τ => ((V x τ j : ℝ) : ℂ))) slab :=
  Complex.continuous_ofReal.comp_continuousOn
    ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn hV)

/-- The time derivative of the complexified `j`-th component is the complexified `j`-th
component of the time derivative (`Complex.ofRealCLM` after `EuclideanSpace.proj j`). -/
theorem hasDerivAt_ofReal_component {V : ℝ → ℝ³} {V' : ℝ³} {τ : ℝ}
    (h : HasDerivAt V V' τ) (j : Fin 3) :
    HasDerivAt (fun σ => ((V σ j : ℝ) : ℂ)) ((V' j : ℝ) : ℂ) τ :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ
    ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt τ h)

/-- The complexified component is bounded by the vector norm. -/
theorem norm_ofReal_component_le (w : ℝ³) (j : Fin 3) : ‖((w j : ℝ) : ℂ)‖ ≤ ‖w‖ := by
  rw [Complex.norm_real]
  exact PiLp.norm_apply_le w j

/-- **(3a) Continuity of the coefficient flow in `Vel`.** -/
theorem continuousOn_coeff_vel {V : ℝ³ → ℝ → ℝ³} {a b C : ℝ} (ha : 0 ≤ a)
    (hV : ContinuousOn (↿V) slab) (hper : ∀ τ ≥ 0, IsOnePeriodic (V · τ))
    (hC : ∀ x, ∀ τ ∈ Icc a b, ‖V x τ‖ ≤ C) (k : Fin 3 → ℤ) :
    ContinuousOn (fun τ => coeff (V · τ) k) (Icc a b) := by
  have hcomp : ∀ j : Fin 3,
      ContinuousOn (fun τ => mFourierCoeff (descend fun x => ((V x τ j : ℝ) : ℂ)) k)
        (Icc a b) := by
    intro j
    refine continuousOn_coeff_of_dominated (G := fun x τ => ((V x τ j : ℝ) : ℂ)) (C := C)
      ha (continuousOn_uncurry_ofReal_component hV j) ?_ ?_ k
    · intro τ hτ
      exact isOnePeriodic_ofReal_component (hper τ hτ) j
    · intro x τ hτ
      exact (norm_ofReal_component_le (V x τ) j).trans (hC x τ hτ)
  have hpi : ContinuousOn
      (fun τ => fun j : Fin 3 => mFourierCoeff (descend fun x => ((V x τ j : ℝ) : ℂ)) k)
      (Icc a b) := continuousOn_pi.mpr hcomp
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm : (Fin 3 → ℂ) →L[ℝ] Vel)
    |>.continuous.comp_continuousOn hpi

/-- **(3b) Differentiation of the coefficient flow in `Vel`.** -/
theorem hasDerivAt_coeff_vel {V V' : ℝ³ → ℝ → ℝ³} {a b C : ℝ}
    (hcont : ∀ τ ∈ Ioo a b, Continuous (V · τ)) (hcont' : ∀ τ ∈ Ioo a b, Continuous (V' · τ))
    (hper : ∀ τ ∈ Ioo a b, IsOnePeriodic (V · τ))
    (hper' : ∀ τ ∈ Ioo a b, IsOnePeriodic (V' · τ))
    (hd : ∀ x, ∀ τ ∈ Ioo a b, HasDerivAt (V x ·) (V' x τ) τ)
    (hC : ∀ x, ∀ τ ∈ Ioo a b, ‖V' x τ‖ ≤ C) (k : Fin 3 → ℤ) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo a b) :
    HasDerivAt (fun τ => coeff (V · τ) k) (coeff (V' · τ₀) k) τ₀ := by
  have hcomp : ∀ j : Fin 3,
      HasDerivAt (fun τ => mFourierCoeff (descend fun x => ((V x τ j : ℝ) : ℂ)) k)
        (mFourierCoeff (descend fun x => ((V' x τ₀ j : ℝ) : ℂ)) k) τ₀ := by
    intro j
    refine hasDerivAt_coeff_of_dominated (G := fun x τ => ((V x τ j : ℝ) : ℂ))
      (G' := fun x τ => ((V' x τ j : ℝ) : ℂ)) (C := C) ?_ ?_ ?_ ?_ ?_ ?_ k hτ₀
    · intro τ hτ
      exact continuous_ofReal_component (hcont τ hτ) j
    · intro τ hτ
      exact continuous_ofReal_component (hcont' τ hτ) j
    · intro τ hτ
      exact isOnePeriodic_ofReal_component (hper τ hτ) j
    · intro τ hτ
      exact isOnePeriodic_ofReal_component (hper' τ hτ) j
    · intro x τ hτ
      exact hasDerivAt_ofReal_component (hd x τ hτ) j
    · intro x τ hτ
      exact (norm_ofReal_component_le (V' x τ) j).trans (hC x τ hτ)
  have hpi : HasDerivAt
      (fun τ => fun j : Fin 3 => mFourierCoeff (descend fun x => ((V x τ j : ℝ) : ℂ)) k)
      (fun j : Fin 3 => mFourierCoeff (descend fun x => ((V' x τ₀ j : ℝ) : ℂ)) k) τ₀ :=
    hasDerivAt_pi.mpr hcomp
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm : (Fin 3 → ℂ) →L[ℝ] Vel)
    |>.hasFDerivAt.comp_hasDerivAt τ₀ hpi

/-! ## (4) The class-member specialisations I8 and I9 -/

/-- The clock `s ↦ s / (2π)` maps `Icc 0 T` into `Icc 0 (T / (2π))`. -/
theorem mapsTo_clock (T : ℝ) :
    MapsTo (fun s : ℝ => s / (2 * Real.pi)) (Icc (0:ℝ) T) (Icc (0:ℝ) (T / (2 * Real.pi))) :=
  fun s hs => ⟨div_nonneg hs.1 (by positivity), div_le_div_of_nonneg_right hs.2 (by positivity)⟩

/-- **I8 (H2 for a class member).** Every mode of the coefficient flow is continuous on the
campaign window `Icc 0 T` (dominated continuity with the bound I5 on `Icc 0 (T/(2π))`, then
the clock). The binder `hT` is not used by the proof (`Icc 0 T` is empty for `T < 0`); it is kept
as agreed so that the consumers' call sites are verbatim. -/
theorem classFlow_continuousOn {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) (k : Fin 3 → ℤ) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => coeff (v · (t / (2 * Real.pi))) k) (Icc (0:ℝ) T) := by
  obtain ⟨C, hC⟩ := exists_bound_velocity hv hper (a := 0) (b := T / (2 * Real.pi)) le_rfl
  have h1 : ContinuousOn (fun τ => coeff (v · τ) k) (Icc (0:ℝ) (T / (2 * Real.pi))) :=
    continuousOn_coeff_vel le_rfl hv.continuousOn hper hC k
  exact h1.comp (continuousOn_id.div_const (2 * Real.pi)) (mapsTo_clock T)

/-- The clock has derivative `1 / (2π)`. -/
theorem hasDerivAt_clock (t : ℝ) :
    HasDerivAt (fun s : ℝ => s / (2 * Real.pi)) (1 / (2 * Real.pi)) t := by
  simpa using (hasDerivAt_id t).div_const (2 * Real.pi)

/-- **I9.** For `t > 0` the coefficient flow is differentiable in the campaign clock with
derivative `(1/(2π)) • coeff (∂_τ⁺ v · (t/(2π)))` (dominated differentiation on the window
`Ioo (τ/2) (2τ)`, I1 to I4, then the clock's derivative `1/(2π)`, `HasDerivAt.scomp`). -/
theorem hasDerivAt_classFlow {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) (k : Fin 3 → ℤ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => coeff (v · (s / (2 * Real.pi))) k)
      ((1 / (2 * Real.pi) : ℝ) •
        coeff (fun x => derivWithin (v x ·) (Ici 0) (t / (2 * Real.pi))) k) t := by
  have hτ₀pos : 0 < t / (2 * Real.pi) := by positivity
  have ha : 0 ≤ t / (2 * Real.pi) / 2 := by positivity
  have hmem : t / (2 * Real.pi) ∈ Ioo (t / (2 * Real.pi) / 2) (2 * (t / (2 * Real.pi))) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨C, hC⟩ := exists_bound_time_deriv_slice hv hper
    (a := t / (2 * Real.pi) / 2) (b := 2 * (t / (2 * Real.pi))) ha
  have hτnn : ∀ τ ∈ Ioo (t / (2 * Real.pi) / 2) (2 * (t / (2 * Real.pi))), 0 ≤ τ :=
    fun τ hτ => ha.trans hτ.1.le
  have hmain : HasDerivAt (fun τ => coeff (v · τ) k)
      (coeff (fun x => derivWithin (v x ·) (Ici 0) (t / (2 * Real.pi))) k)
      (t / (2 * Real.pi)) :=
    hasDerivAt_coeff_vel (V := v) (V' := fun x τ => derivWithin (v x ·) (Ici 0) τ)
      (fun τ hτ => (contDiff_space_slice hv (hτnn τ hτ)).continuous)
      (fun τ hτ => continuous_time_deriv_slice hv (hτnn τ hτ))
      (fun τ hτ => hper τ (hτnn τ hτ))
      (fun τ hτ => isOnePeriodic_time_deriv_slice hper (hτnn τ hτ))
      (fun x τ hτ => hasDerivAt_time_slice hv x (ha.trans_lt hτ.1))
      (fun x τ hτ => hC x τ (Ioo_subset_Icc_self hτ)) k hmem
  exact HasDerivAt.scomp (x := t) (h := fun s : ℝ => s / (2 * Real.pi)) hmain (hasDerivAt_clock t)

/-! ## D2. The forward FTC on the window (P5, I14) -/

/-- **I14.** A mode curve continuous on the window, differentiable inside it with a
continuous derivative, satisfies the integral equation on the window (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`).
The binder `hT` is not used by the proof (`t ∈ Icc 0 T` gives `0 ≤ t`); kept as agreed. -/
theorem integral_eq_of_hasDerivAt {f g : ℝ → Vel} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0:ℝ) T)) (hg : ContinuousOn g (Icc (0:ℝ) T))
    (hd : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt f (g t) t) :
    ∀ t ∈ Icc (0:ℝ) T, f t = f 0 + ∫ s in (0:ℝ)..t, g s := by
  intro t ht
  have h0t : (0:ℝ) ≤ t := ht.1
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := Icc_subset_Icc le_rfl ht.2
  have hI : ∫ s in (0:ℝ)..t, g s = f t - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0t (hf.mono hsub)
      (fun s hs => hd s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
      ((hg.mono hsub).intervalIntegrable_of_Icc h0t)
  rw [hI]
  abel

/-! ## D3. The calibration in reverse (P4) -/

/-! ## 0'. Copied PROVED from R6 (retargeted to the tree names) -/

/-- The pairing of the cast frequency with itself is the squared norm. -/
lemma dotR_castCV_freq (k : Fin 3 → ℤ) :
    dotR (castCV (freq k)) (freq k) = ((‖freq k‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ‖freq k‖ ^ 2 = ∑ j, ((freq k).ofLp j) ^ 2 := by
    rw [norm_freq, Real.sq_sqrt (by positivity)]
    rfl
  rw [dotR]
  push_cast [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [castCV]
  ring

/-- The Leray projection kills every multiple of the cast frequency (`k ≠ 0`). -/
theorem lerayProj_smul_castCV_freq {k : Fin 3 → ℤ} (hk : k ≠ 0) (a : ℂ) :
    lerayProj k (a • castCV (freq k)) = 0 := by
  rw [lerayProj_smul]
  have hfk : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
  have hne : ((‖freq k‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos hfk 2).ne'
  have h : lerayProj k (castCV (freq k)) = 0 := by
    unfold lerayProj
    rw [dotR_castCV_freq, div_self hne, one_smul, sub_self]
  rw [h, smul_zero]

/-- The pressure-gradient packing `(2πi kⱼ) p̂` is `(2πi p̂) • castCV (freq k)` componentwise,
so the Leray projection kills it (`k ≠ 0`). -/
theorem lerayProj_pressure_gradient {k : Fin 3 → ℤ} (hk : k ≠ 0) (phat : ℂ) :
    lerayProj k (WithLp.toLp 2 fun j => (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * phat) = 0 := by
  have hpack : (WithLp.toLp 2 fun j => (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * phat : Vel)
      = (2 * Real.pi * Complex.I * phat) • castCV (freq k) := by
    ext j
    simp [castCV, freq]
    ring
  rw [hpack]
  exact lerayProj_smul_castCV_freq hk _

/-! ## 1. Linearity of `coeff` over pointwise operations -/

/-- The coefficient of a sum of continuous torus functions (`integral_add`). -/
theorem mFourierCoeff_add {f g : UnitAddTorus (Fin 3) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => f z + g z) n = mFourierCoeff f n + mFourierCoeff g n := by
  unfold mFourierCoeff
  simp_rw [smul_add]
  exact integral_add (integrable_of_continuous ((mFourier (-n)).continuous.smul hf))
    (integrable_of_continuous ((mFourier (-n)).continuous.smul hg))

/-- The coefficient of a difference of continuous torus functions (`integral_sub`). -/
theorem mFourierCoeff_sub {f g : UnitAddTorus (Fin 3) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => f z - g z) n = mFourierCoeff f n - mFourierCoeff g n := by
  unfold mFourierCoeff
  simp_rw [smul_sub]
  exact integral_sub (integrable_of_continuous ((mFourier (-n)).continuous.smul hf))
    (integrable_of_continuous ((mFourier (-n)).continuous.smul hg))

/-- The coefficient of a negation (`integral_neg`, no hypothesis). -/
theorem mFourierCoeff_neg (f : UnitAddTorus (Fin 3) → ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => -f z) n = -mFourierCoeff f n := by
  unfold mFourierCoeff
  simp_rw [smul_neg]
  exact integral_neg _

/-- The coefficient of a constant multiple (`integral_const_mul`, no hypothesis). -/
theorem mFourierCoeff_const_mul (a : ℂ) (f : UnitAddTorus (Fin 3) → ℂ) (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => a * f z) n = a * mFourierCoeff f n := by
  unfold mFourierCoeff
  rw [← integral_const_mul]
  congr 1
  funext t
  simp only [smul_eq_mul]
  ring

/-- `coeff` is additive on continuous one-periodic fields. -/
theorem coeff_add {w w' : ℝ³ → ℝ³} (hw : Continuous w) (hwp : IsOnePeriodic w)
    (hw' : Continuous w') (hwp' : IsOnePeriodic w') (n : Fin 3 → ℤ) :
    coeff (fun x => w x + w' x) n = coeff w n + coeff w' n := by
  refine PiLp.ext fun j => ?_
  rw [PiLp.add_apply, coeff_apply, coeff_apply, coeff_apply]
  have hfun : (fun x => ((((fun x => w x + w' x) x) j : ℝ) : ℂ)) =
      fun x => ((w x j : ℝ) : ℂ) + ((w' x j : ℝ) : ℂ) := by
    funext x
    simp only [PiLp.add_apply, Complex.ofReal_add]
  rw [hfun]
  exact mFourierCoeff_add
    (continuous_descend (continuous_ofReal_component hw j) (isOnePeriodic_ofReal_component hwp j))
    (continuous_descend (continuous_ofReal_component hw' j) (isOnePeriodic_ofReal_component hwp' j)) n

/-- `coeff` respects differences on continuous one-periodic fields. -/
theorem coeff_sub {w w' : ℝ³ → ℝ³} (hw : Continuous w) (hwp : IsOnePeriodic w)
    (hw' : Continuous w') (hwp' : IsOnePeriodic w') (n : Fin 3 → ℤ) :
    coeff (fun x => w x - w' x) n = coeff w n - coeff w' n := by
  refine PiLp.ext fun j => ?_
  rw [PiLp.sub_apply, coeff_apply, coeff_apply, coeff_apply]
  have hfun : (fun x => ((((fun x => w x - w' x) x) j : ℝ) : ℂ)) =
      fun x => ((w x j : ℝ) : ℂ) - ((w' x j : ℝ) : ℂ) := by
    funext x
    simp only [PiLp.sub_apply, Complex.ofReal_sub]
  rw [hfun]
  exact mFourierCoeff_sub
    (continuous_descend (continuous_ofReal_component hw j) (isOnePeriodic_ofReal_component hwp j))
    (continuous_descend (continuous_ofReal_component hw' j) (isOnePeriodic_ofReal_component hwp' j)) n

/-- `coeff` of a real multiple: the scalar enters as `((a : ℝ) : ℂ) •` (no hypothesis). -/
theorem coeff_smul (a : ℝ) (w : ℝ³ → ℝ³) (n : Fin 3 → ℤ) :
    coeff (fun x => a • w x) n = ((a : ℝ) : ℂ) • coeff w n := by
  refine PiLp.ext fun j => ?_
  rw [PiLp.smul_apply, smul_eq_mul, coeff_apply, coeff_apply]
  have hfun : (fun x => ((((fun x => a • w x) x) j : ℝ) : ℂ)) =
      fun x => ((a : ℝ) : ℂ) * ((w x j : ℝ) : ℂ) := by
    funext x
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [hfun]
  exact mFourierCoeff_const_mul _ _ n

/-- `coeff` of a negation (no hypothesis). -/
theorem coeff_neg (w : ℝ³ → ℝ³) (n : Fin 3 → ℤ) :
    coeff (fun x => -w x) n = -coeff w n := by
  refine PiLp.ext fun j => ?_
  rw [PiLp.neg_apply, coeff_apply, coeff_apply]
  have hfun : (fun x => ((((fun x => -w x) x) j : ℝ) : ℂ)) =
      fun x => -((w x j : ℝ) : ℂ) := by
    funext x
    simp only [PiLp.neg_apply, Complex.ofReal_neg]
  rw [hfun]
  exact mFourierCoeff_neg _ n

/-! ## 2. The pressure-gradient coefficient -/


theorem isOnePeriodic_ofReal_scalar {q : ℝ³ → ℝ} (hq : IsOnePeriodic q) :
    IsOnePeriodic fun x => ((q x : ℝ) : ℂ) := by
  intro x i
  show ((q (x + _) : ℝ) : ℂ) = ((q x : ℝ) : ℂ)
  rw [hq x i]

/-- **The pressure-gradient coefficient**: `coeff (∇(p · τ)) n` is the packed vector
`(2πi nⱼ) · p̂(n)` where `p̂(n)` is the coefficient of the descent of the complexified slice. -/
theorem pressure_gradient_coeff {p : ℝ³ → ℝ → ℝ} (hp : ContDiffOn ℝ ∞ (↿p) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (p · t)) {τ : ℝ} (hτ : 0 ≤ τ) (n : Fin 3 → ℤ) :
    coeff (fun x => gradient (p · τ) x) n =
      WithLp.toLp 2 fun j => (2 * Real.pi * Complex.I * ((n j : ℤ) : ℂ)) *
        mFourierCoeff (descend fun x => ((p x τ : ℝ) : ℂ)) n := by
  have hq : ContDiff ℝ ∞ (p · τ) := contDiff_space_slice' hp hτ
  have hqC : ContDiff ℝ ∞ (fun x => ((p x τ : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hq
  have hqp : IsOnePeriodic (fun x => ((p x τ : ℝ) : ℂ)) := isOnePeriodic_ofReal_scalar (hper τ hτ)
  refine PiLp.ext fun j => ?_
  rw [PiLp.toLp_apply]
  show mFourierCoeff (descend fun x => (((gradient (p · τ) x) j : ℝ) : ℂ)) n = _
  have hfun : (fun x => (((gradient (p · τ) x) j : ℝ) : ℂ)) =
      fun x => fderiv ℝ (fun y => ((p y τ : ℝ) : ℂ)) x (EuclideanSpace.single j 1) := by
    funext x
    have hd : DifferentiableAt ℝ (p · τ) x := (hq.differentiable (by simp)) x
    have h1 : (gradient (p · τ) x) j = fderiv ℝ (p · τ) x (EuclideanSpace.single j 1) :=
      gradient_apply_eq_fderiv_single hd j
    have h2 : HasFDerivAt (fun y => ((p y τ : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ (p · τ) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt
    rw [h1, h2.fderiv]
    rfl
  rw [hfun]
  exact mFourierCoeff_descend_fderiv (hqC.of_le (by decide)) hqp j n

/-- The Leray projection kills the pressure-gradient coefficient at EVERY mode
(`n ≠ 0` by `lerayProj_pressure_gradient`; at `n = 0` the packed vector is `0`). -/
theorem lerayProj_pressure_gradient_coeff {p : ℝ³ → ℝ → ℝ} (hp : ContDiffOn ℝ ∞ (↿p) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (p · t)) {τ : ℝ} (hτ : 0 ≤ τ) (n : Fin 3 → ℤ) :
    lerayProj n (coeff (fun x => gradient (p · τ) x) n) = 0 := by
  rw [pressure_gradient_coeff hp hper hτ n]
  by_cases hn : n = 0
  · have h0 : (WithLp.toLp 2 fun j => (2 * Real.pi * Complex.I * ((n j : ℤ) : ℂ)) *
        mFourierCoeff (descend fun x => ((p x τ : ℝ) : ℂ)) n : Vel) = 0 := by
      refine PiLp.ext fun j => ?_
      simp [hn]
    rw [h0]
    unfold lerayProj
    rw [dotR_zero_left, zero_div, zero_smul, sub_zero]
  · exact lerayProj_pressure_gradient hn _

/-! ## 3. DivFree bookkeeping -/

/-- (H5) The coefficient field of every time slice of a class member is divergence-free. -/
theorem divFree_slice {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {τ : ℝ} (hτ : 0 ≤ τ) : DivFree (coeff (v · τ)) :=
  divFree_coeff (contDiff_space_slice h.velocity_smooth hτ) (h.isOnePeriodic_velocity τ hτ)
    (fun x => h.div_free x τ hτ)

/-- The Leray projection is the identity on a vector orthogonal to its frequency. -/
theorem lerayProj_of_divFree {k : Fin 3 → ℤ} {w : Vel} (hw : dotR w (freq k) = 0) :
    lerayProj k w = w := by
  unfold lerayProj
  rw [hw, zero_div, zero_smul, sub_zero]

/-- The derivative of a divergence-free mode is divergence-free: the pairing against the
frequency is a finite sum of products (differentiated by `HasDerivAt.fun_sum` through
`EuclideanSpace.proj … restrictScalars ℝ`), and it vanishes on a neighbourhood of `t > 0`. -/
theorem divFree_deriv {c : ℝ → (Fin 3 → ℤ) → Vel} {k : Fin 3 → ℤ} {d : Vel} {t : ℝ} (ht : 0 < t)
    (hd : HasDerivAt (fun s => c s k) d t) (h0 : ∀ s ≥ 0, dotR (c s k) (freq k) = 0) :
    dotR d (freq k) = 0 := by
  have hcomp : ∀ j : Fin 3, HasDerivAt (fun s => (c s k) j) (d j) t := fun j =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have hD : HasDerivAt (fun s => dotR (c s k) (freq k)) (dotR d (freq k)) t := by
    unfold dotR
    exact HasDerivAt.fun_sum fun j _ => (hcomp j).mul_const _
  have hev : (fun s => dotR (c s k) (freq k)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem (Ici_mem_nhds ht) fun s hs => h0 s hs
  have h0' : HasDerivAt (fun s => dotR (c s k) (freq k)) 0 t :=
    (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hev
  exact hD.unique h0'

/-! ## 4. The assembly: the class equation to the campaign mode ODE -/

/-- The class equation with the `(f := 0)` term removed: the exact spelling is
`simp only [Pi.zero_apply, add_zero]` (the force term elaborates as `(0 : ℝ³ → ℝ → ℝ³) x τ`). -/
theorem class_eq_force_free {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    (x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    derivWithin (v x ·) (Ici 0) τ + fderiv ℝ (v · τ) x (v x τ) =
      ν' • Δ (v · τ) x - gradient (p · τ) x := by
  have h1 := h.navier_stokes x τ hτ
  simp only [Pi.zero_apply, add_zero] at h1
  exact h1

/-- I7 packed into `Vel`: `coeff (Δ (v · τ)) n = (−(2π)²‖freq n‖²) • coeff (v · τ) n`. -/
theorem laplacian_coeff_vel {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) (n : Fin 3 → ℤ) :
    coeff (fun x => Δ (v · τ) x) n =
      (((-((2 * Real.pi) ^ 2 * ‖freq n‖ ^ 2)) : ℝ) : ℂ) • coeff (v · τ) n := by
  refine PiLp.ext fun j => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, coeff_apply]
  exact laplacian_coeff hv hper hτ j n

/-- I10 packed into `Vel`: `coeff ((u·∇)u) n = (−2π) • convFull (coeff u) n` (from
`coeff_convection`, ConvectionCoeff, componentwise). -/
theorem convection_coeff_vel {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (n : Fin 3 → ℤ) :
    coeff (fun x => fderiv ℝ u x (u x)) n = ((-(2 * Real.pi) : ℝ) : ℂ) • convFull (coeff u) n := by
  refine PiLp.ext fun j => ?_
  rw [PiLp.smul_apply, smul_eq_mul]
  exact coeff_convection hu hp n j

/-- A real scalar on `Vel` is the cast complex scalar (componentwise `Complex.real_smul`). -/
theorem real_smul_eq_coe_smul_vel (r : ℝ) (w : Vel) : r • w = ((r : ℝ) : ℂ) • w := by
  refine PiLp.ext fun j => ?_
  simp only [PiLp.smul_apply, Complex.real_smul, smul_eq_mul]

/-- The Leray projection is ℝ-homogeneous (through `lerayProj_smul`). -/
theorem lerayProj_real_smul (k : Fin 3 → ℤ) (r : ℝ) (w : Vel) :
    lerayProj k (r • w) = r • lerayProj k w := by
  rw [real_smul_eq_coe_smul_vel, lerayProj_smul, ← real_smul_eq_coe_smul_vel]

/-- **I12 (R6 3.vi with the unused `hν'` dropped, D14)**: the calibration in reverse.  The class's equation at `ν'` in
the clock `t = 2πτ` gives the campaign mode ODE with `ν = 2πν'` for
`c t k := coeff (v · (t/(2π))) k`.  The constant ledger, computed in the proof:
`(1/(2π)) · [ν' · (−(2π)²‖k‖²) • c + 2π • convFull c k − (2πi kⱼ p̂)ⱼ]
  = (−2πν'‖k‖²) • c + convFull c k − (1/(2π)) • (2πi kⱼ p̂)ⱼ`,
and `lerayProj k` of both sides (the derivative is divergence-free, `divFree_deriv`) leaves
`(−2πν'‖k‖²) • c + lerayProj k (convFull c k)`.  No positivity of `ν'` is asked: the mode ODE
holds for every real `ν'` (positivity is consumed only by `theorem_B_unique`); the recon's
agreed text carried an unused `hν'`, dropped here so that the statement says what is proved
(blueprint §1b D14, the rung11 D9 precedent: a stronger frozen statement, one hypothesis fewer). -/
theorem class_member_mode_ode {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    ∀ t > 0, ∀ k, HasDerivAt (fun s => coeff (v · (s / (2 * Real.pi))) k)
      ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · (t / (2 * Real.pi))) k
        + lerayProj k (convFull (coeff (v · (t / (2 * Real.pi)))) k)) t := by
  intro t ht k
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hτ : 0 < t / (2 * Real.pi) := div_pos ht hπ
  have hτ0 : 0 ≤ t / (2 * Real.pi) := hτ.le
  have hv : ContDiffOn ℝ ∞ (↿v) slab := h.velocity_smooth
  have hper : ∀ s ≥ 0, IsOnePeriodic (v · s) := h.isOnePeriodic_velocity
  have hp : ContDiffOn ℝ ∞ (↿p) slab := h.pressure_smooth
  have hpper : ∀ s ≥ 0, IsOnePeriodic (p · s) := h.isOnePeriodic_pressure
  -- (H5) every slice is divergence-free, hence so is the derivative of the mode
  have hdivs : ∀ s ≥ (0:ℝ), dotR (coeff (v · (s / (2 * Real.pi))) k) (freq k) = 0 :=
    fun s hs => divFree_slice h (div_nonneg hs hπ.le) k
  -- the derivative from the interface (P2)
  have hd := hasDerivAt_classFlow hv hper k ht
  have hdiv : dotR ((1 / (2 * Real.pi) : ℝ) •
      coeff (fun x => derivWithin (v x ·) (Ici 0) (t / (2 * Real.pi))) k) (freq k) = 0 :=
    divFree_deriv (c := fun s => coeff (v · (s / (2 * Real.pi)))) ht hd hdivs
  refine hd.congr_deriv ?_
  set τ := t / (2 * Real.pi) with hτdef
  have hVs : ContDiff ℝ ∞ (v · τ) := contDiff_space_slice hv hτ0
  have hVp : IsOnePeriodic (v · τ) := hper τ hτ0
  -- the three pieces: D (time-derivative slice), C (convection), G (pressure gradient)
  have hDc : Continuous (fun x => derivWithin (v x ·) (Ici 0) τ) :=
    continuous_time_deriv_slice hv hτ0
  have hDp : IsOnePeriodic (fun x => derivWithin (v x ·) (Ici 0) τ) :=
    isOnePeriodic_time_deriv_slice hper hτ0
  have hCc : Continuous (fun x => fderiv ℝ (v · τ) x (v x τ)) := continuous_convTerm hVs
  have hCp : IsOnePeriodic (fun x => fderiv ℝ (v · τ) x (v x τ)) := isOnePeriodic_convTerm hVp
  have hGc : Continuous (fun x => gradient (p · τ) x) :=
    continuous_gradient_of_contDiff (contDiff_space_slice' hp hτ0)
  have hGp : IsOnePeriodic (fun x => gradient (p · τ) x) := isOnePeriodic_gradient (hpper τ hτ0)
  -- the class equation as a function identity for the Laplacian term
  have hL : (fun x => ν' • Δ (v · τ) x) = fun x =>
      (derivWithin (v x ·) (Ici 0) τ + fderiv ℝ (v · τ) x (v x τ)) + gradient (p · τ) x := by
    funext x
    exact sub_eq_iff_eq_add.mp (class_eq_force_free h x hτ0).symm
  -- the coefficient of the Laplacian term, two ways
  -- (`Continuous.add` yields `Continuous (f + g)` at the pin: the lambda type is stated
  -- explicitly so that `coeff_add` unifies `w` with the lambda, not the Pi sum)
  have hDCc : Continuous (fun x => derivWithin (v x ·) (Ici 0) τ + fderiv ℝ (v · τ) x (v x τ)) :=
    hDc.add hCc
  have hDCp : IsOnePeriodic (fun x => derivWithin (v x ·) (Ici 0) τ + fderiv ℝ (v · τ) x (v x τ)) :=
    isOnePeriodic_add hDp hCp
  have hcL : coeff (fun x => ν' • Δ (v · τ) x) k =
      coeff (fun x => derivWithin (v x ·) (Ici 0) τ) k
        + coeff (fun x => fderiv ℝ (v · τ) x (v x τ)) k
        + coeff (fun x => gradient (p · τ) x) k := by
    rw [hL, coeff_add hDCc hDCp hGc hGp, coeff_add hDc hDp hCc hCp]
  have hcS : coeff (fun x => ν' • Δ (v · τ) x) k =
      ((ν' : ℝ) : ℂ) • ((((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) : ℝ) : ℂ) • coeff (v · τ) k) := by
    rw [coeff_smul ν' (fun x => Δ (v · τ) x) k, laplacian_coeff_vel hv hper hτ0 k]
  have hcC : coeff (fun x => fderiv ℝ (v · τ) x (v x τ)) k =
      ((-(2 * Real.pi) : ℝ) : ℂ) • convFull (coeff (v · τ)) k := convection_coeff_vel hVs hVp k
  -- the coefficient of the time-derivative slice
  have hcD : coeff (fun x => derivWithin (v x ·) (Ici 0) τ) k =
      ((ν' : ℝ) : ℂ) • ((((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) : ℝ) : ℂ) • coeff (v · τ) k)
        - coeff (fun x => gradient (p · τ) x) k
        - ((-(2 * Real.pi) : ℝ) : ℂ) • convFull (coeff (v · τ)) k := by
    rw [← hcS, ← hcC]
    exact eq_sub_of_add_eq (eq_sub_of_add_eq hcL.symm)
  -- the derivative, expanded: the constants meet
  have hdexp : (1 / (2 * Real.pi) : ℝ) • coeff (fun x => derivWithin (v x ·) (Ici 0) τ) k =
      (-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · τ) k
        + convFull (coeff (v · τ)) k
        - (1 / (2 * Real.pi) : ℝ) • coeff (fun x => gradient (p · τ) x) k := by
    rw [hcD]
    refine PiLp.ext fun j => ?_
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    field_simp
    ring
  -- the Leray projection of both sides
  have hleft : lerayProj k ((1 / (2 * Real.pi) : ℝ) •
      coeff (fun x => derivWithin (v x ·) (Ici 0) τ) k) =
      (1 / (2 * Real.pi) : ℝ) • coeff (fun x => derivWithin (v x ·) (Ici 0) τ) k :=
    lerayProj_of_divFree hdiv
  have hcdiv : lerayProj k (coeff (v · τ) k) = coeff (v · τ) k :=
    lerayProj_of_divFree (divFree_slice h hτ0 k)
  have hG0 : lerayProj k (coeff (fun x => gradient (p · τ) x) k) = 0 :=
    lerayProj_pressure_gradient_coeff hp hpper hτ0 k
  have hright : lerayProj k ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · τ) k
        + convFull (coeff (v · τ)) k
        - (1 / (2 * Real.pi) : ℝ) • coeff (fun x => gradient (p · τ) x) k) =
      (-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · τ) k
        + lerayProj k (convFull (coeff (v · τ)) k) := by
    rw [lerayProj_sub, lerayProj_add, lerayProj_real_smul, lerayProj_real_smul, hcdiv, hG0,
      smul_zero, sub_zero]
  calc (1 / (2 * Real.pi) : ℝ) • coeff (fun x => derivWithin (v x ·) (Ici 0) τ) k
      = lerayProj k ((1 / (2 * Real.pi) : ℝ) •
          coeff (fun x => derivWithin (v x ·) (Ici 0) τ) k) := hleft.symm
    _ = lerayProj k ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · τ) k
        + convFull (coeff (v · τ)) k
        - (1 / (2 * Real.pi) : ℝ) • coeff (fun x => gradient (p · τ) x) k) := by rw [hdexp]
    _ = (-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · τ) k
        + lerayProj k (convFull (coeff (v · τ)) k) := hright

/-! ## 5. The integral form on every window -/

/-- **I13 (R6 3.vi' with the unused `hν'` dropped, D14)**: the integral form `theorem_B_unique`
consumes, on every window
`[0, T]`: mode continuity (I8), the budgets (I11) and the slice summability
(`summable_sob_coeff` at `m = 0, 1`) give the continuity of the right-hand side through
`continuousOn_convFull` and `lerayProj_continuous`; the mode ODE (I12) on `Ioo 0 T`; the initial
value `coeff (v · (0/(2π))) = coeff u₀` from `initial_condition`; then the forward FTC (I14).
This is (H6) of `theorem_B_unique` for the coefficient flow of a class member at `ν = 2πν'`.
No positivity of `ν'` is asked (it fed only the mode ODE, whose own binder is dropped, D14). -/
theorem class_member_integral_eq {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, coeff (v · (t / (2 * Real.pi))) k = coeff u₀ k +
      ∫ s in (0:ℝ)..t, ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) •
          coeff (v · (s / (2 * Real.pi))) k
        + lerayProj k (convFull (coeff (v · (s / (2 * Real.pi)))) k)) := by
  intro t ht k
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  have hv : ContDiffOn ℝ ∞ (↿v) slab := h.velocity_smooth
  have hper : ∀ s ≥ 0, IsOnePeriodic (v · s) := h.isOnePeriodic_velocity
  -- (H2) continuity of every mode on the window
  have hf : ContinuousOn (fun s => coeff (v · (s / (2 * Real.pi))) k) (Icc (0:ℝ) T) :=
    classFlow_continuousOn hv hper k hT
  -- (H4) the budgets, and their nonnegativity
  obtain ⟨E, Z, hEZ⟩ := classFlow_budget hv hper hT
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_refl 0, hT⟩
  have hE0 : 0 ≤ E := le_trans (tsum_nonneg fun l => sq_nonneg _) (hEZ 0 h0mem).1
  have hZ0 : 0 ≤ Z := le_trans (tsum_nonneg fun l => by positivity) (hEZ 0 h0mem).2
  -- (H3) summability of the slices at every time of the window
  have hsum : ∀ s ∈ Icc (0:ℝ) T,
      (Summable fun l => ‖coeff (v · (s / (2 * Real.pi))) l‖ ^ 2) ∧
      (Summable fun l => ‖freq l‖ ^ 2 * ‖coeff (v · (s / (2 * Real.pi))) l‖ ^ 2) := by
    intro s hs
    have hτ0 : 0 ≤ s / (2 * Real.pi) := div_nonneg hs.1 hπ.le
    have hVs := contDiff_space_slice hv hτ0
    have hVp := hper _ hτ0
    constructor
    · exact (summable_sob_coeff hVs hVp 0).congr fun l => by rw [mul_zero, pow_zero, one_mul]
    · exact (summable_sob_coeff hVs hVp 1).congr fun l => by rw [mul_one]
  -- finite-sum bound forms for the continuity of the convection (FullUnique.lean:349 pattern)
  have hEF : ∀ s ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖coeff (v · (s / (2 * Real.pi))) l‖ ^ 2 ≤ E := fun s hs F =>
    ((hsum s hs).1.sum_le_tsum F (fun l _ => sq_nonneg _)).trans (hEZ s hs).1
  have hZF : ∀ s ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖coeff (v · (s / (2 * Real.pi))) l‖ ^ 2 ≤ Z := fun s hs F =>
    ((hsum s hs).2.sum_le_tsum F (fun l _ => by positivity)).trans (hEZ s hs).2
  have hconv : ContinuousOn (fun s => convFull (coeff (v · (s / (2 * Real.pi)))) k)
      (Icc (0:ℝ) T) :=
    continuousOn_convFull hE0 hZ0 (g := fun s => coeff (v · (s / (2 * Real.pi)))) hEF hZF
      (fun l => classFlow_continuousOn hv hper l hT) k
  have hg : ContinuousOn (fun s => (-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) •
      coeff (v · (s / (2 * Real.pi))) k
        + lerayProj k (convFull (coeff (v · (s / (2 * Real.pi)))) k)) (Icc (0:ℝ) T) :=
    (hf.const_smul _).add ((lerayProj_continuous k).comp_continuousOn hconv)
  -- (H6) the mode ODE on the open window
  have hd : ∀ s ∈ Ioo (0:ℝ) T, HasDerivAt (fun s => coeff (v · (s / (2 * Real.pi))) k)
      ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · (s / (2 * Real.pi))) k
        + lerayProj k (convFull (coeff (v · (s / (2 * Real.pi)))) k)) s :=
    fun s hs => class_member_mode_ode h s hs.1 k
  -- (H1) the initial value
  have h0 : coeff (v · ((0:ℝ) / (2 * Real.pi))) k = coeff u₀ k := by
    have hfun : (v · ((0:ℝ) / (2 * Real.pi))) = u₀ := funext fun x => by
      rw [zero_div]; exact h.initial_condition x
    rw [hfun]
  have hint := integral_eq_of_hasDerivAt hT hf hg hd t ht
  rw [h0] at hint
  exact hint

end

end TheoremB
