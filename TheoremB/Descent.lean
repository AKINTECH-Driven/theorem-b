/-
  TheoremB/Descent.lean
  Tier 9, wave W1 (Theorem B campaign, 13 Sep 2026): the descent of a
  one-periodic function on ℝ³ to the unit 3-torus, and the bridge from its
  partial derivatives to its Fourier coefficients at every order.  Transcribed
  from section A of the design probe `audit-tier9/design/final/Tier9Final.lean`
  (session directory, never a tracked file; compiled there at the pin, exit 0;
  section A has no declaration with a placeholder proof, the probe's only two
  being the W3 candidates of its section F, not transcribed); the frozen
  statements are those of
  `context/rung11-tier9-blueprint.md` section 4a (the Descent block),
  byte-identical, and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * Periodicity (A1): `Community.IsOnePeriodic.add_freq` (ℤ³-invariance from
    the class's one-step periodicity, for any `Sort`-valued `f`, by
    `Int.induction_on` one coordinate at a time) and
    `Community.IsOnePeriodic.fderiv_apply` (periodicity passes to every
    directional derivative, with no differentiability hypothesis, through the
    unconditional `fderiv_comp_add_right`).  Both are declared with the
    `Community.` prefix inside `namespace TheoremB`, so that dot-notation on
    `hf : IsOnePeriodic f` finds them (a pin trap measured in this tier).
  * The representative and the descent (A2): `rep1` (the `[0,1)`
    representative on the circle, `AddCircle.equivIco`), `rep` (its `PiLp`
    packing on the torus), `descend f z := f (rep z)` (`Sort`-polymorphic,
    total and choice-free), the round trips `rep1_coe`, `coe_rep1`,
    `rep_fiber`, `fiber_rep`, and `descend_fiber`: for a one-periodic `f` the
    descent reads `f` back along `fiber`.
  * The open quotient map and the continuity transfer (A3):
    `isOpenQuotientMap_fiber` (`fiber` is the coordinatewise
    `QuotientAddGroup.mk` composed with the `PiLp` homeomorphism) and
    `continuous_descend` (a continuous one-periodic `f` has a continuous
    descent).
  * The fiber-slice brick (A4): `sliceLine`, `fiber_sliceLine`,
    `hasDerivAt_sliceLine`, and `hasDerivAt_descend_insertNth`: the slice
    derivative of the descent, in the exact `hderiv` format consumed by
    `mFourierCoeff_deriv` (FourierDeriv.lean).
  * The consumed coefficient facts on the torus (A5):
    `integrable_of_continuous`, the sup bound `norm_mFourierCoeff_le`, the
    reality rule `mFourierCoeff_neg_of_real`, linearity over a `Finset`
    `mFourierCoeff_finset_sum` (`integral_finsetSum`, the pinned name),
    `summable_sq_of_summable_norm` (an ℓ¹ family of `Vel` values is ℓ²), and
    the packaging identity `u₀Real_eq_of_lift`.
  * The derivative bridge at every order (A6): `mFourierCoeff_descend_fderiv`
    (`C¹`, one order, `mFourierCoeff_deriv` fed by the brick), the partial
    derivative `dirDeriv` and its iterate `dirIter` with their smoothness and
    periodicity, and `mFourierCoeff_descend_dirIter`: `q` partial derivatives
    in direction `i` multiply the coefficient at `n` by `(2πi nᵢ)^q`
    (induction on `q`).
  * The descent of a lift (A7): `descend_uLift`, `descend_uLift_eq_uCont`
    (the descent of `uLift j c` is the tree's continuous representative
    `uCont`, ContinuousRep.lean), and `mFourierCoeff_descend_uLift`: the
    coefficients of the descent of the lift are the family `c` itself, for an
    ℓ¹ family (the ℓ² input of the tree's `mFourierCoeff_uCont` is derived
    inside by `summable_sq_of_summable_norm`).

  HONEST SCOPE.
  * Nothing here is new mathematics: the descent of a periodic function to
    the torus and the identity between a partial derivative and a frequency
    multiplier are textbook (any text on Fourier series on the torus); the
    deliverable is the machine-checked bridge between the class's
    `IsOnePeriodic` vocabulary on ℝ³ (CommunityClass.lean) and the tree's
    `mFourierCoeff` on `UnitAddTorus (Fin 3)`.
  * No constant is introduced here; the multipliers `2πi nᵢ` are literal
    expressions.  No numeric value of any constant is claimed.
  * `descend` is total; for a non-periodic `f` it is a well-typed junk object
    (rule 10 of the blueprint's section 7); every statement about the
    descent of a general `f` takes `IsOnePeriodic f` as a hypothesis (the
    three A7 statements are about the lift `uLift j c`, one-periodic by the
    tree's `isOnePeriodic_uLift`).
  * This file states nothing about the community solution class or about
    either upstream statement (the upstream file carries the positive
    statement `navier_stokes_existence_and_smoothness_periodic` and the
    breakdown statement `navier_stokes_breakdown_periodic`;
    CommunityClass.lean copies the class, not those statements); both are
    untouched.  Priority is not claimed for anything.
  * This file edits no earlier file of the tree and clones no private lemma:
    the probe it is transcribed from compiled against the imported tree, so
    every declaration consumed here is public in its file (FourierDeriv,
    SpectralNorms, NSGalerkin, PeriodicLift, ContinuousRep, CommunityClass,
    Mathlib).
    The ten helper lemmas (`Community.IsOnePeriodic.sub_single`,
    `Community.IsOnePeriodic.add_zsmul_single`, `freq_eq_three`,
    `descend_comp_fiber`, `fiber_eq_piMap`,
    `continuous_iff_continuous_comp_fiber`, `sliceLine_eq`,
    `continuous_fderiv_apply_single`, `continuous_dirDeriv`, `dirIter_zero`)
    are shipped public and carry no ledger line; DatumBridge.lean consumes
    `continuous_dirDeriv` among them.

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances anonymously;
  here they are NAMED `ds_ms`, `ds_haar`, `ds_prob`, the tree's habit for
  torus files (`cr_*` in ContinuousRep, `tsyn_*` in TorusSynthesis, `ts_*` in
  TorusStructure, `ce_*` in CoeffExtract), because auto-named local instances
  from two modules collide in a third module that imports both.  The bodies
  are the three-line block of FourierDeriv.lean lines 31-37.  Instances are
  not statements; every frozen statement is byte-identical to the blueprint.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.CommunityClass

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
local instance ds_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance ds_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance ds_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## A1. ℤ³-invariance from the class's one-step periodicity (R2 section 1) -/

theorem Community.IsOnePeriodic.sub_single {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f)
    (x : ℝ³) (i : Fin 3) : f (x - EuclideanSpace.single i 1) = f x := by
  have h := hf (x - EuclideanSpace.single i 1) i
  rw [sub_add_cancel] at h
  exact h.symm

theorem Community.IsOnePeriodic.add_zsmul_single {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f)
    (x : ℝ³) (i : Fin 3) (n : ℤ) : f (x + n • EuclideanSpace.single i 1) = f x := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [add_zsmul, one_zsmul, ← add_assoc, hf]
    exact ih
  | pred n ih =>
    have h1 : (-(n : ℤ) - 1) • EuclideanSpace.single i (1 : ℝ)
        = (-(n : ℤ)) • EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single i 1 := by
      rw [sub_zsmul, one_zsmul, sub_eq_add_neg]
    rw [h1, ← add_sub_assoc, hf.sub_single]
    exact ih

theorem freq_eq_three (g : Fin 3 → ℤ) :
    freq g = ((g 0) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
      + (g 1) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      + (g 2) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
  ext l
  fin_cases l <;>
    simp [freq, PiLp.add_apply, PiLp.smul_apply, zsmul_eq_mul]

/-- ℤ³-invariance of a one-periodic function (any `Sort`-valued `f`). -/
theorem Community.IsOnePeriodic.add_freq {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f)
    (g : Fin 3 → ℤ) (x : ℝ³) : f (x + freq g) = f x := by
  rw [freq_eq_three, ← add_assoc, ← add_assoc, hf.add_zsmul_single, hf.add_zsmul_single,
    hf.add_zsmul_single]

/-- Periodicity passes to every directional derivative, with no differentiability
hypothesis (`fderiv_comp_add_right` is unconditional at the pin). -/
theorem Community.IsOnePeriodic.fderiv_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ³ → F} (hf : IsOnePeriodic f) (v : ℝ³) :
    IsOnePeriodic (fun x => fderiv ℝ f x v) := by
  intro x i
  have h : (fun z : ℝ³ => f (z + EuclideanSpace.single i 1)) = f := funext fun z => hf z i
  show fderiv ℝ f (x + EuclideanSpace.single i 1) v = fderiv ℝ f x v
  rw [← fderiv_comp_add_right, h]

/-! ## A2. The representative and the descent (R2 section 2; THE canonical spelling) -/

/-- The `[0,1)`-representative of a point of the unit circle. -/
def rep1 (z : UnitAddCircle) : ℝ :=
  ((AddCircle.equivIco (1 : ℝ) 0 z : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)

/-- The `[0,1)³`-representative of a point of the torus. -/
def rep (z : UnitAddTorus (Fin 3)) : ℝ³ := WithLp.toLp 2 fun i => rep1 (z i)

/-- The descent of a function on `ℝ³` to the torus, through the representative.  Total and
choice-free; for a NON-periodic `f` it is a well-typed junk object (blueprint section 6). -/
def descend {α : Sort*} (f : ℝ³ → α) (z : UnitAddTorus (Fin 3)) : α := f (rep z)

/-- The representative of the class of `s` is its fractional part `s - ⌊s⌋`
(`AddCircle.coe_equivIco_mk_apply`, `Int.self_sub_floor`). -/
theorem rep1_coe (s : ℝ) : rep1 ((s : ℝ) : AddCircle (1 : ℝ)) = s - ⌊s⌋ := by
  unfold rep1
  rw [AddCircle.coe_equivIco_mk_apply]
  simp [Int.self_sub_floor]

/-- The representative projects back to the point it represents
(`AddCircle.coe_equivIco`). -/
theorem coe_rep1 (z : UnitAddCircle) : ((rep1 z : ℝ) : AddCircle (1 : ℝ)) = z :=
  AddCircle.coe_equivIco

/-- The representative of `fiber x` is `x` shifted back by the integer vector of its
coordinate floors (it lies in `[0,1)³`). -/
theorem rep_fiber (x : ℝ³) : rep (fiber x) = x - freq (fun i => ⌊x i⌋) := by
  ext i
  simp [rep, fiber, freq, rep1_coe, PiLp.sub_apply]

/-- `fiber` is a left inverse of `rep`: the representative lies over the point it
represents. -/
theorem fiber_rep (z : UnitAddTorus (Fin 3)) : fiber (rep z) = z := by
  funext l
  exact coe_rep1 (z l)

/-- The descent recovers `f` along `fiber` (the class's `IsOnePeriodic` vocabulary). -/
theorem descend_fiber {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f) (x : ℝ³) :
    descend f (fiber x) = f x := by
  unfold descend
  rw [rep_fiber]
  have h := hf.add_freq (fun i => ⌊x i⌋) (x - freq (fun i => ⌊x i⌋))
  rw [sub_add_cancel] at h
  exact h.symm

theorem descend_comp_fiber {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f) :
    descend f ∘ fiber = f :=
  funext fun x => descend_fiber hf x

/-! ## A3. `fiber` is an open quotient map; continuity transfer (R2 sections 3-4) -/

theorem fiber_eq_piMap :
    (fiber : ℝ³ → UnitAddTorus (Fin 3)) =
      Pi.map (fun _ : Fin 3 => (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)))
        ∘ (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) := rfl

/-- `fiber : ℝ³ → T³` is an open quotient map: the coordinatewise `QuotientAddGroup.mk`
(`IsOpenQuotientMap.piMap`) composed with the `PiLp` homeomorphism. -/
theorem isOpenQuotientMap_fiber : IsOpenQuotientMap (fiber : ℝ³ → UnitAddTorus (Fin 3)) := by
  rw [fiber_eq_piMap]
  exact (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).comp
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isOpenQuotientMap

theorem continuous_iff_continuous_comp_fiber {E : Type*} [TopologicalSpace E]
    (g : UnitAddTorus (Fin 3) → E) : Continuous g ↔ Continuous (g ∘ fiber) :=
  isOpenQuotientMap_fiber.continuous_comp_iff.symm

/-- The descent of a continuous one-periodic function is continuous. -/
theorem continuous_descend {E : Type*} [TopologicalSpace E] {f : ℝ³ → E}
    (hf : Continuous f) (hper : IsOnePeriodic f) : Continuous (descend f) := by
  rw [continuous_iff_continuous_comp_fiber, descend_comp_fiber hper]
  exact hf

/-! ## A4. The fiber-slice brick for `mFourierCoeff_deriv` (R2 section 5) -/

/-- The straight line in `ℝ³` lying over the `insertNth` slice. -/
def sliceLine (i : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ) : ℝ³ :=
  WithLp.toLp 2 (i.insertNth s (fun m => rep1 (y m)))

/-- The line `sliceLine i y` lies over the `insertNth` slice of the torus: its fiber at
`s` is `i.insertNth (↑s) y`. -/
theorem fiber_sliceLine (i : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ) :
    fiber (sliceLine i y s) = i.insertNth (↑s : UnitAddCircle) y := by
  funext l
  rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨m, rfl⟩
  · simp [fiber, sliceLine, Fin.insertNth_apply_same]
  · simp [fiber, sliceLine, Fin.insertNth_apply_succAbove, coe_rep1]

theorem sliceLine_eq (i : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ) :
    sliceLine i y s = sliceLine i y 0 + s • EuclideanSpace.single i 1 := by
  ext l
  rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨m, rfl⟩
  · simp [sliceLine, Fin.insertNth_apply_same]
  · simp [sliceLine, Fin.insertNth_apply_succAbove, Fin.succAbove_ne]

/-- The slice line is affine in `s` with velocity `EuclideanSpace.single i 1`. -/
theorem hasDerivAt_sliceLine (i : Fin 3) (y : UnitAddTorus (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sliceLine i y s) (EuclideanSpace.single i 1) t := by
  have h : (fun s : ℝ => sliceLine i y s)
      = fun s : ℝ => sliceLine i y 0 + s • EuclideanSpace.single i 1 :=
    funext (sliceLine_eq i y)
  rw [h]
  simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i 1)).const_add
    (sliceLine i y 0)

/-- **The fiber-slice brick**: the slice derivative of the descent, in the exact `hderiv`
format of `mFourierCoeff_deriv` (FourierDeriv.lean:129). -/
theorem hasDerivAt_descend_insertNth {f : ℝ³ → ℂ} (hf : Differentiable ℝ f)
    (hper : IsOnePeriodic f) (i : Fin 3) (y : UnitAddTorus (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => descend f (i.insertNth (↑s : UnitAddCircle) y))
      (descend (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
        (i.insertNth (↑t : UnitAddCircle) y)) t := by
  have hfun : (fun s : ℝ => descend f (i.insertNth (↑s : UnitAddCircle) y))
      = fun s : ℝ => f (sliceLine i y s) := by
    funext s
    rw [← fiber_sliceLine, descend_fiber hper]
  have hval : descend (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      (i.insertNth (↑t : UnitAddCircle) y)
      = fderiv ℝ f (sliceLine i y t) (EuclideanSpace.single i 1) := by
    rw [← fiber_sliceLine]
    exact descend_fiber (hper.fderiv_apply _) _
  rw [hfun, hval]
  exact (hf (sliceLine i y t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_sliceLine i y t)

/-! ## A5. Coefficient facts on the torus (R1, the consumed subset) -/

/-- A continuous function on the (compact) torus is integrable for the Haar probability
measure. -/
theorem integrable_of_continuous {f : UnitAddTorus (Fin 3) → ℂ} (hf : Continuous f) :
    Integrable f (volume : Measure (UnitAddTorus (Fin 3))) :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

/-- The sup bound on a coefficient, `‖mFourierCoeff g n‖ ≤ ‖g‖` for a continuous `g`: the
characters have norm one and the torus measure is a probability measure. -/
theorem norm_mFourierCoeff_le (g : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    ‖mFourierCoeff g n‖ ≤ ‖g‖ := by
  unfold mFourierCoeff
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus (Fin 3))))
    (f := fun t => mFourier (-n) t • g t) (C := ‖g‖)
    (Filter.Eventually.of_forall fun t => by
      rw [norm_smul, norm_mFourier_apply, one_mul]
      exact g.norm_coe_le_norm t)
  rwa [probReal_univ, mul_one] at h

/-- Function-level reality: a real-valued torus function has conjugate-symmetric coefficients. -/
theorem mFourierCoeff_neg_of_real {g : UnitAddTorus (Fin 3) → ℂ}
    (hg : ∀ z, conj (g z) = g z) (n : Fin 3 → ℤ) :
    mFourierCoeff g (-n) = conj (mFourierCoeff g n) := by
  unfold mFourierCoeff
  rw [← integral_conj]
  congr 1
  funext t
  rw [neg_neg, smul_eq_mul, smul_eq_mul, map_mul, hg t, mFourier_neg, starRingEnd_self_apply]

/-- The coefficient of a finite sum of continuous torus functions is the sum of the
coefficients (`integral_finsetSum`, the pinned name). -/
theorem mFourierCoeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → UnitAddTorus (Fin 3) → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => ∑ i ∈ s, f i z) n = ∑ i ∈ s, mFourierCoeff (f i) n := by
  unfold mFourierCoeff
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum s fun i hi =>
    ((mFourier (-n)).continuous.smul (hf i hi)).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact

/-- ℓ¹ ⊂ ℓ² on the coefficient side (the `hc2` input of `mFourierCoeff_uCont`). -/
theorem summable_sq_of_summable_norm {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖) : Summable fun k => ‖c k‖ ^ 2 := by
  have hB : ∀ k, ‖c k‖ ≤ ∑' k, ‖c k‖ := fun k =>
    hc.le_tsum k fun _ _ => norm_nonneg _
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hc.mul_left (∑' k, ‖c k‖))
  calc ‖c k‖ ^ 2 = ‖c k‖ * ‖c k‖ := by ring
    _ ≤ (∑' k, ‖c k‖) * ‖c k‖ := mul_le_mul_of_nonneg_right (hB k) (norm_nonneg _)

/-- The `u₀Real` packaging identity: a real field whose complexified components are the lifts
of `c` IS `u₀Real c`. -/
theorem u₀Real_eq_of_lift (c : (Fin 3 → ℤ) → Vel) (u : ℝ³ → ℝ³)
    (hu : ∀ x j, ((u x j : ℝ) : ℂ) = uLift j c x) :
    u₀Real c = u := by
  funext x
  refine PiLp.ext fun j => ?_
  show (uLift j c x).re = u x j
  rw [← hu x j, Complex.ofReal_re]

/-! ## A6. The derivative bridge on the descent (R2 section 6, R3 sections 1-2) -/

theorem continuous_fderiv_apply_single {f : ℝ³ → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous fun x : ℝ³ => fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have h := hf.continuous_fderiv_apply (by norm_num)
  exact h.comp (continuous_id.prodMk continuous_const)

/-- `mFourierCoeff (descend ∂ᵢ f) n = 2πi nᵢ · mFourierCoeff (descend f) n` for `C¹` periodic `f`. -/
theorem mFourierCoeff_descend_fderiv {f : ℝ³ → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsOnePeriodic f) (i : Fin 3) (n : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) n
      = (2 * Real.pi * Complex.I * (n i)) * mFourierCoeff (descend f) n :=
  mFourierCoeff_deriv i
    (continuous_descend hf.continuous hper)
    (continuous_descend (continuous_fderiv_apply_single hf i) (hper.fderiv_apply _))
    (fun y t => hasDerivAt_descend_insertNth (hf.differentiable (by norm_num)) hper i y t)
    n

/-- The `i`-th partial derivative as a scalar field. -/
def dirDeriv (i : Fin 3) (f : ℝ³ → ℂ) : ℝ³ → ℂ :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

/-- A partial derivative of a `C^∞` scalar field is `C^∞` (`contDiff_infty_iff_fderiv` and
`contDiff_clm_apply_iff`, the pinned route). -/
theorem contDiff_dirDeriv (i : Fin 3) {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirDeriv i f) :=
  contDiff_clm_apply_iff.mp (contDiff_infty_iff_fderiv.mp hf).2 _

theorem continuous_dirDeriv (i : Fin 3) {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f) :
    Continuous (dirDeriv i f) :=
  (contDiff_dirDeriv i hf).continuous

/-- A partial derivative of a one-periodic scalar field is one-periodic (no
differentiability hypothesis, through `Community.IsOnePeriodic.fderiv_apply`). -/
theorem dirDeriv_isOnePeriodic (i : Fin 3) {f : ℝ³ → ℂ} (hp : IsOnePeriodic f) :
    IsOnePeriodic (dirDeriv i f) :=
  hp.fderiv_apply _

/-- The brick in the `dirDeriv` spelling (definitional restatement). -/
theorem hasDerivAt_descend_dirDeriv (i : Fin 3) {f : ℝ³ → ℂ} (hf : Differentiable ℝ f)
    (hp : IsOnePeriodic f) (y : UnitAddTorus (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => descend f (i.insertNth (↑s : UnitAddCircle) y))
      (descend (dirDeriv i f) (i.insertNth (↑t : UnitAddCircle) y)) t :=
  hasDerivAt_descend_insertNth hf hp i y t

/-- The `q`-fold `i`-th partial derivative. -/
def dirIter (i : Fin 3) (q : ℕ) (f : ℝ³ → ℂ) : ℝ³ → ℂ := (dirDeriv i)^[q] f

theorem dirIter_zero (i : Fin 3) (f : ℝ³ → ℂ) : dirIter i 0 f = f := rfl

/-- Unfolding the iterate: `q + 1` partial derivatives are one partial derivative of `q` of
them (`Function.iterate_succ_apply'`). -/
theorem dirIter_succ (i : Fin 3) (q : ℕ) (f : ℝ³ → ℂ) :
    dirIter i (q + 1) f = dirDeriv i (dirIter i q f) :=
  Function.iterate_succ_apply' (dirDeriv i) q f

/-- Every iterated partial derivative of a `C^∞` scalar field is `C^∞` (induction on `q`). -/
theorem contDiff_dirIter (i : Fin 3) {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f) (q : ℕ) :
    ContDiff ℝ ∞ (dirIter i q f) := by
  induction q with
  | zero => exact hf
  | succ q ih => rw [dirIter_succ]; exact contDiff_dirDeriv i ih

/-- Every iterated partial derivative of a one-periodic scalar field is one-periodic
(induction on `q`). -/
theorem dirIter_isOnePeriodic (i : Fin 3) {f : ℝ³ → ℂ} (hp : IsOnePeriodic f) (q : ℕ) :
    IsOnePeriodic (dirIter i q f) := by
  induction q with
  | zero => exact hp
  | succ q ih => rw [dirIter_succ]; exact dirDeriv_isOnePeriodic i ih

/-- **The iterated bridge**: `q` applications of `mFourierCoeff_deriv` through the bricks. -/
theorem mFourierCoeff_descend_dirIter (i : Fin 3) {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (q : ℕ) (n : Fin 3 → ℤ) :
    mFourierCoeff (descend (dirIter i q f)) n =
      (2 * Real.pi * Complex.I * (n i)) ^ q * mFourierCoeff (descend f) n := by
  induction q with
  | zero => simp [dirIter_zero]
  | succ q ih =>
    have hq : ContDiff ℝ ∞ (dirIter i q f) := contDiff_dirIter i hf q
    have hpq : IsOnePeriodic (dirIter i q f) := dirIter_isOnePeriodic i hp q
    rw [dirIter_succ, pow_succ,
      mFourierCoeff_deriv i (continuous_descend hq.continuous hpq)
        (continuous_descend (continuous_dirDeriv i hq) (dirDeriv_isOnePeriodic i hpq))
        (fun y t => hasDerivAt_descend_dirDeriv i (hq.differentiable (by simp)) hpq y t) n, ih]
    ring

/-! ## A7. The descent of a lift is the tree's continuous representative (R2 section 8) -/

/-- The descent of the lift `uLift j c` at `z` is the character sum of the `j`-th components
at `z` (`uLift_eq_charSum_fiber` read at `rep z`, then `fiber_rep`). -/
theorem descend_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (z : UnitAddTorus (Fin 3)) :
    descend (uLift j c) z = ∑' k, c k j * mFourier k z := by
  unfold descend
  rw [uLift_eq_charSum_fiber, fiber_rep]

/-- For an ℓ¹ family, the descent of the lift is the tree's continuous representative
`uCont j c hc` as a function (`uCont_apply` is a `HasSum` statement: its `tsum_eq`, then
`smul = mul` by `rfl`). -/
theorem descend_uLift_eq_uCont (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) : descend (uLift j c) = ⇑(uCont j c hc) := by
  funext z
  rw [descend_uLift, ← (uCont_apply j c hc z).tsum_eq]
  rfl

/-- The coefficients of the descent of a lift are the lift's coefficients, for an ℓ¹ family
(the ℓ² input of the tree's `mFourierCoeff_uCont` is derived by `summable_sq_of_summable_norm`,
RC6 of the statement-shape critique: one hypothesis fewer than the tree's lemma). -/
theorem mFourierCoeff_descend_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) (n : Fin 3 → ℤ) :
    mFourierCoeff (descend (uLift j c)) n = c n j := by
  rw [descend_uLift_eq_uCont j c hc,
    mFourierCoeff_uCont j c hc (summable_sq_of_summable_norm hc)]

end

end TheoremB
