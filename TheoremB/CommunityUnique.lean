/-
  TheoremB/CommunityUnique.lean
  Tier 9c, wave W3c (Theorem B campaign, 13 Sep 2026): THE CAPSTONE WAVE.  Uniqueness inside OUR
  COPY of the community class `NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p`
  (CommunityClass.lean) at `f = 0`, for the same datum `u₀` and `0 < ν'`: the velocity at every
  point and every `t ≥ 0` (`community_unique_velocity`) and the pressure up to a function of time
  (`community_unique_pressure`), with its gradient form, its velocity-hypothesis form and its
  explicit form `p₁ x t = p₂ x t + (p₁ 0 t - p₂ 0 t)`; the H1/H3/H5 facts of the coefficient flow
  `classFlow` of a class member; the wrapper `unique_of_windows` (the citable form of the Tier 4
  consumption); the three injectivity lemmas; the two consistency corollaries; and the register
  `T9cProbe` (the vacuity / must-fail / must-hold register of the blueprint's section 6).
  Transcribed from section E of the design probe `audit-tier9c/design/final/Tier9cFinal.lean`
  (session directory, never a tracked file; compiled there at the pin, exit 0, no declaration with
  a placeholder proof; section E stitches `recon/P7/ReconP7.lean` (H1/H3/H5, the velocity
  capstone, the injectivity lemmas, the consistency corollaries), `recon/P5/ReconP5.lean` sections
  2 to 4 (the constancy lemma, the wrapper, the pressure capstone and its two siblings),
  `recon/P8/ReconP8.lean` (the register, with its local `classFlow` dropped and the junk items on
  ClassFlowODE.lean's `classFlow_zero_eq`), the design pass's two MUST-HOLD items (D12), the
  statement critic's sharpness item (D16) and the blueprint pass's explicit pressure form (D15));
  the frozen statements are those of `context/rung12-tier9c-blueprint.md` section 4c (the
  CommunityUnique block) and the register statements those of its section 6, byte-identical (the
  two capstones additionally byte-identical to rung11 section 4c through `tools/check_capstone.py`),
  and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * E1, H1/H3/H5 in the flow spelling for a member `(v, p)` of OUR COPY of the class at viscosity
    `ν'`, datum `u₀`, `f = 0`: `classFlow_zero` (H1: `classFlow v 0 = coeff u₀`, the class's
    `initial_condition` under `funext`), `summable_classFlow` (H3: the energy and enstrophy series
    of the flow are summable at every campaign time `t ≥ 0`; DatumBridge.lean's `summable_sob_coeff`
    at `m = 0, 1` on the slice) and `divFree_classFlow` (H5: DatumBridge.lean's `divFree_coeff` on
    the slice); the two slice helpers `smooth_slice`, `periodic_slice` (Galilean.lean's
    `contDiff_space_slice` and the class's `isOnePeriodic_velocity` at `t / (2π)`).  These three
    hold for every real `ν'`: positivity is consumed only by `theorem_B_unique`.
  * E2, the constancy lemma `eq_add_const_of_gradient_eq` (two differentiable scalar fields with
    the same gradient everywhere differ by the constant fixed at the origin;
    `fderiv_eq_of_gradient_eq` through `(toDual ℝ ℝ³).symm.injective`, `fderiv_sub`, then Mathlib's
    `is_const_of_fderiv_eq_zero`) and the wrapper `unique_of_windows` (the exact hypothesis shape a
    class-member flow supplies to Tier 4: per-window continuity, budgets per window PER FLOW,
    pointwise summability and divergence-freeness, the integral equation on every window;
    uniqueness on `t ≥ 0` from `theorem_B_unique` on the window `[0, t]` with the shared budgets
    `max E₁ E₂`, `max Z₁ Z₂` through `le_max_left` and `le_max_right`), with its funext sibling
    `unique_of_windows'`.
  * E3, THE VELOCITY CAPSTONE `community_unique_velocity`: two members `(v₁, p₁)`, `(v₂, p₂)` of
    OUR COPY of the class at `f = 0` with the same datum `u₀` and `0 < ν'` have `v₁ x t = v₂ x t`
    for every `x` and every `t ≥ 0`.  Route: the campaign window `T := 2πt`
    (`mul_nonneg (by positivity) ht`) and the campaign viscosity `ν := 2πν'`; ClassParseval.lean's
    budgets I11 (`classFlow_budget`) twice, shared by the maxima; ClassFlowODE.lean's mode
    continuity I8 (`classFlow_continuousOn`) in the `fun s => classFlow v s k` shape and its
    integral equation I13 (`class_member_integral_eq`) at `ν := 2πν'`; `theorem_B_unique`
    (FullUnique.lean, Tier 4) with `classFlow_zero`, `summable_classFlow`, `divFree_classFlow`,
    evaluated at the window's right end `⟨hT, le_refl _⟩`; back to the class clock through
    ClassFlowODE.lean's `classFlow_clock` and `funext`; then THE INVERSION, DatumBridge.lean's
    `u₀Real_coeff` (Tier 9 W1) on the two smooth one-periodic slices at `t`, in a three-step
    `calc`.  No torus-side injectivity lemma is consumed (D3).  Periodicity enters at H2, H3, H5,
    H6 and last at the inversion (without it two non-periodic pairs have equal `classFlow` and
    different velocities: the statement critic's S5, not carried).
  * E4, THE PRESSURE CAPSTONE `community_unique_pressure`: under the same hypotheses
    `∃ g : ℝ → ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + g t`, with `g t := p₁ 0 t - p₂ 0 t`: the velocity
    capstone, then the two class equations at `(x, t)` subtracted (`slice_eq_of_velocity_eq`,
    `derivWithin_eq_of_velocity_eq` through `derivWithin_congr` on `Ici 0`,
    `gradient_eq_of_velocity_eq` with the `(f := 0)` term removed by
    `simp only [Pi.zero_apply, add_zero]` and `sub_right_injective`), then
    `eq_add_const_of_gradient_eq` on the two pressure slices (CommunityClass.lean's
    `TimeConstantWitness.pressure_slice`).  Its three forms, each frozen: the gradient form
    `community_unique_pressure_gradient` (equal pressure gradients at every `x` and every `t ≥ 0`,
    the sharp form behind it), the velocity-hypothesis form `community_unique_pressure_of_velocity`
    (the velocity agreement taken as an explicit hypothesis, no `0 < ν'`: `theorem_B_unique` is not
    consumed there) and the explicit form `community_unique_pressure_explicit` (D15:
    `∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + (p₁ 0 t - p₂ 0 t)`, no `∃`, so a consumer needs no choice).
  * E5, the three injectivity lemmas in tree spelling (D3; frozen and registered; consumed by no
    capstone): `eq_of_mFourierCoeff_eq` (L² injectivity of the coefficients on `C(T³, ℂ)`:
    `mFourierBasis_repr`, `mFourierCoeff_toLp`, `repr.injective`, `ContinuousMap.toLp_inj`),
    `eq_of_coeff_eq` (injectivity of `coeff` on smooth one-periodic fields by the inversion
    `u₀Real_coeff`, three lines) and `eq_of_coeff_eq'` (the same statement by the torus-side route:
    bundled descents of the complexified components through Descent.lean's `continuous_descend`
    and `descend_fiber`, DatumBridge.lean's `contDiff_ofReal_component` and
    `isOnePeriodic_ofReal_component`, `Complex.ofReal_injective`, `PiLp.ext`); the two proofs of one
    statement certify each other.
  * E6, the two consistency corollaries: `const_datum_member_is_const` (every member of OUR COPY of
    the class at `f = 0` on the constant datum `fun _ => m` with `0 < ν'` has velocity `m` at
    every `x` and every `t ≥ 0`: the velocity capstone against CommunityData.lean's
    `T9Probe.const_pair_in_class`) and `capstone_fires_on_const_datum_witness` (the witness of
    Tier 9's `T9Probe.capstone_fires_on_const_datum` is the constant pair's velocity on `t ≥ 0`).
  * E7, the register `namespace T9cProbe` (fifteen theorems, one ledger line each; `def preHistory`
    and the two helpers `gradient_add_const_eq`, `uncurry_pressure_add` carry none), per item:
    (1) `pressure_add_time_function_in_class` and its corollaries `pressure_add_const_in_class`,
    `pressure_add_id_in_class`: a member stays a member when a smooth function of time alone is
    added to the pressure (the momentum equation sees only the spatial gradient; the smoothness
    `hg` is load-bearing, a step in time is not a member, the statement critic's S8, not carried);
    (2) the pressure form is SHARP: `pressure_not_unique` refutes `p₁ = p₂` pointwise (the rest
    pair at `ν' = 1` and its pressure shifted by `1`, at `(0, 0)`) and
    `pressure_not_unique_up_to_const` refutes the `∃ C` form (the shift by `t` needs `C = 0` at
    `t = 0` and `C = 1` at `t = 1`), so the `∃ g : ℝ → ℝ` of the pressure capstone cannot be
    tightened; (3) non-vacuity, `two_members_same_datum`: for every `ν' > 0` two DISTINCT members
    with the same NONZERO datum exist (Tier 9's witness on the shear datum,
    `T9Probe.capstone_fires_on_testDatum`, and the same velocity with the pressure shifted by `1`);
    (4) the datum is load-bearing, `different_data_not_forced_equal` (the rest pair and the
    constant pair at `e₀`, both members at `ν' = 1`, differ in velocity at `(0, 0)`); (5)
    membership says nothing about the sign of `ν'`, `class_inhabited_all_visc` (the rest pair is a
    member for EVERY real `ν'`; non-uniqueness at `ν' ≤ 0` is NOT claimed); (6) the constant datum
    has two named members, `const_datum_two_members` (the constant pair and Tier 9's witness),
    identified in velocity by E6; (7) the junk note, `classFlow_junk` and `classFlow_junk'`:
    `classFlow` is total and for the non-member `v x _ := x` its inversion FAILS
    (CommunityData.lean's `T9Probe.inversion_fails_off_class`); (8) MUST HOLD, consistency with
    Tier 9's flow sibling (D12): `classFlow_eq_of_flow` (any flow in `theorem_B_unique`'s class
    starting from `meanFree (coeff u₀)` equals `classFlow v` of EVERY member `v` on the datum at
    every `t ≥ 0`, PROVIDED the datum is mean-free, `coeff u₀ 0 = 0`; the capstone's route stopped
    before the inversion) and `flow_witness_classFlow_eq` (the Tier 9 instance: on a mean-free
    datum meeting the smallness hypothesis, the flow `c` exhibited by CommunityData.lean's
    `theorem_B_community_periodic_data_flow` IS `classFlow` of the member it exhibits,
    `galV (meanVec (coeff u₀)) (vReal c)`, at every `t ≥ 0`; the `∃ κ` is the sibling's own); the
    general-mean identity is NOT compiled and NOT claimed (blueprint section 8 item 7); (9) the
    velocity capstone's `∀ t ≥ 0` is SHARP (D16): `preHistory m` (the rest state for `t ≥ 0`, the
    constant `m` for `t < 0`) with the zero pressure is a member on the zero datum for every real
    `ν'` (`preHistory_in_class`: every field of the class only looks at `t ≥ 0`), so
    `velocity_not_unique_off_halfline` exhibits two members with the same datum `0` at `ν' = 1`
    whose velocities differ at `t = -1`; function equality `v₁ = v₂` is FALSE as a consequence of
    membership, and the velocity capstone's conclusion cannot be strengthened to it.

  HONEST SCOPE (binding wording, section 7 of the blueprint, rules 1 to 14).
  * What the two capstones say: uniqueness inside OUR COPY of the community class at `f = 0`, for
    the same datum `u₀` and `0 < ν'`; never "uniqueness of Navier-Stokes solutions".  The velocity
    is unique at every point and every `t ≥ 0` ONLY (register item 9); the pressure is unique up
    to a function of time ONLY, never "the pressure is unique" (register items 1 and 2; the `n = 0`
    pressure mode is free).  `0 < ν'` is consumed by `theorem_B_unique`, not implied by
    membership: the constant pair is a member for every real `ν'` (register item 5), so nothing is
    said about `ν' ≤ 0`.
  * What they are: a corollary of `theorem_B_unique` (Tier 4, FullUnique.lean) through the datum
    bridge (Tier 9 W1, DatumBridge.lean) and the calibration in reverse (W3b, ClassFlowODE.lean):
    the textbook energy method in the enstrophy class, read back through the Fourier inversion.
    Nothing here is new mathematics; the deliverable is the machine-checking.  No numeric value of
    any constant is claimed: the budgets `E`, `Z` of I11 are UNTRACKED existentials produced by
    SliceExtract.lean's compactness bounds and are consumed here only through the maxima; the
    constants of the calibration are literal expressions computed by the kernel in
    ClassFlowODE.lean and none is restated here.
  * The class is the community's own `NavierStokesExistenceAndSmoothnessPeriodic`, copied in
    CommunityClass.lean; the upstream file carries the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
    `navier_stokes_breakdown_periodic`; the capstones are about OUR COPY of the class at `f = 0`:
    nothing about general data, nothing about `ν' ≤ 0`, nothing about forced data (`f ≠ 0`),
    nothing about competitors outside the class (a non-smooth or non-periodic pair; weak
    solutions), nothing about the breakdown statement; both upstream placeholder proofs are
    untouched.
  * Tier 9's capstones (`theorem_B_community_periodic_data` and its flow sibling,
    CommunityData.lean) stay "existence only" as written, their files being frozen; the "sized
    candidate" sentences of the Tier 9 headers and of rung11 rule 9 ("uniqueness inside the
    community class in real-space vocabulary is a sized candidate (W3), not a delivered result,
    until and unless it ships") are SUPERSEDED by this wave, not struck (blueprint section 8
    item 11): the two capstones above are what makes uniqueness citable inside OUR COPY of the
    class.
  * PROPOSED announcement wording (blueprint section 8 item 3, the written-out form of D9; the
    user's call; quoted here, not asserted, verbatim):
    "Inside OUR COPY of the community's periodic solution class
    `NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` with `0 < ν'` and `f = 0`, two members
    with the same datum `u₀` have the same velocity at every point and every `t ≥ 0` and pressures
    that differ by a function of time alone (compiled, `community_unique_velocity`,
    `community_unique_pressure`, `community_unique_pressure_explicit`); this is a corollary of
    `theorem_B_unique` (Tier 4) through the datum bridge (Tier 9 W1), the textbook energy method in
    the enstrophy class; nothing about `ν' ≤ 0`, forced data, general data, competitors outside the
    class or the breakdown statement `navier_stokes_breakdown_periodic`; the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement are both
    untouched; the neighbours are HeliCorgi's local mild uniqueness on `ℝ³` and uda-lab/leray-hopf;
    nothing here is new mathematics."
  * Priority is not claimed for anything.  The neighbours named by rule 12 are HeliCorgi's local
    mild uniqueness on `ℝ³` (ns-mns2-flowmap-bridge, 18 Aug 2026) and uda-lab/leray-hopf (weak
    existence); OpenAI's forced-breakdown certificate and Alpöge-Buckmaster sit on the breakdown
    side; none of it is composed with, reproduced by, or superseded by anything here.
  * Junk values (rule 10): `coeff`, `u₀Real` and `classFlow` are total; outside the stated
    smoothness and periodicity they are well-typed junk objects (register item 7), and coefficient
    equality transfers to velocity equality only through `u₀Real_coeff`, which needs the slice
    smooth and one-periodic; every statement here carries the hypotheses it needs.
  * This file edits no earlier file of the tree and clones no private lemma: every declaration
    consumed here is public in its file.  Consumed tree files, measured by identifier grep of the
    code (docstrings stripped): ClassFlowODE (`classFlow`, `classFlow_apply`, `classFlow_clock`,
    `classFlow_zero_eq`, `classFlow_continuousOn`, `class_member_integral_eq`; the import),
    ClassParseval (`classFlow_budget`, consumed directly at the velocity capstone and at
    `T9cProbe.classFlow_eq_of_flow`; reached through the import), CommunityData (`meanFree`,
    `meanVec`, `meanFree_of_mean_zero`, `theorem_B_community_periodic_data_flow`, and the Tier 9
    register `T9Probe`'s `const_pair_in_class`, `rest_pair_in_class'`,
    `capstone_fires_on_const_datum`, `capstone_fires_on_testDatum`, `inversion_fails_off_class`;
    reached through the import), CommunityClass (`NavierStokesExistenceAndSmoothnessPeriodic`,
    `InitialVelocityConditionPeriodic`, `IsOnePeriodic`, `fiber`, `u₀Real`, `vReal`, `pReal`,
    `TimeConstantWitness.pressure_slice`), DatumBridge (`coeff`, `contDiff_ofReal_component`,
    `isOnePeriodic_ofReal_component`, `summable_sob_coeff`, `divFree_coeff`, `u₀Real_coeff`),
    Descent (`descend`, `continuous_descend`, `descend_fiber`), FullUnique (`theorem_B_unique`),
    Galilean (`contDiff_space_slice`, `galV`, `galP`), NSGalerkin (`Vel`, `DivFree`, `RealField`,
    `lerayProj`), NSFull (`convFull`), SpectralNorms (`en`, `ens`, `freq`), and Mathlib.  The
    short-name scan also matches TimeSmooth's `HasDerivAt.lerayProj` and CommunityClass's
    `W4Probe.capstone_fires_on_testDatum`; neither is consumed (`lerayProj k` here is NSGalerkin's;
    the register opens `T9Probe`, not `W4Probe`).  The 7 helpers (`smooth_slice`, `periodic_slice`,
    `fderiv_eq_of_gradient_eq`, `unique_of_windows'`, `slice_eq_of_velocity_eq`,
    `derivWithin_eq_of_velocity_eq`, `gradient_eq_of_velocity_eq`) and the two register helpers are
    shipped public and carry no ledger line; `def preHistory` is fenced (byte-identity checked on
    its signature; its body `fun _ t => if t < 0 then m else 0` is read by eye) and carries none;
    the 15 frozen theorems and the 15 register theorems carry one each, entries 445 to 474 of the
    gate's 474 (`TheoremB.<name>` for the frozen ones, `TheoremB.T9cProbe.<name>` for the register,
    in the probe's audit order).
  * Three register docstrings keep the probe's text and call the velocity capstone a "candidate"
    (`two_members_same_datum`, `class_inhabited_all_visc`, `const_datum_two_members`): the word is
    the recon's, written before the capstone was frozen in this file; each of the three now ends
    with a clause saying so; the theorems they point at are E3 and E6 above, proved here.

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances as `df_*`; here they are NAMED
  `cu_ms`, `cu_haar`, `cu_prob` (SliceExtract.lean uses `se_*`, ConvectionCoeff.lean `cc_*`,
  ClassParseval.lean `cp_*`, ClassFlowODE.lean `co_*`; `cu_*` is the prefix the feasibility
  critic's module chain compiled), because auto-named local instances from two modules collide in
  a third module that imports both.  The bodies are the three-line block of FourierDeriv.lean
  lines 31-37.  Instances are not statements; every frozen and registered statement is
  byte-identical to the blueprint.  The probe's `-- SECTION E` marker is dropped; its section
  headings are kept.  The import is `TheoremB.ClassFlowODE` alone (the blueprint's section 1a
  table lists `TheoremB.CommunityData` beside it; that module is reached through ClassFlowODE's own
  import of it, and the build confirmed that no direct line is needed).  No sibling was added and
  no spec drift is recorded: every frozen statement is proved as written.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.ClassFlowODE

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
local instance cu_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance cu_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance cu_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! # E. W3c : TheoremB/CommunityUnique.lean (P7, P5, the register from P8) -/

/-! ## E1. H1, H3, H5 for a class member (P7 sections 1 and 2) -/

/-- (H1) The flow starts at the coefficient field of the datum. -/
theorem classFlow_zero {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    classFlow v 0 = coeff u₀ := by
  unfold classFlow
  rw [zero_div]
  have hv : (v · (0:ℝ)) = u₀ := funext fun x => h.initial_condition x
  rw [hv]

/-! ## (2) The summability (H3) and divergence (H5) groups from the class alone -/

/-- The space slice at campaign time `t ≥ 0` is smooth. -/
theorem smooth_slice {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (v · (t / (2 * Real.pi))) :=
  contDiff_space_slice h.velocity_smooth (div_nonneg ht (by positivity))

/-- The space slice at campaign time `t ≥ 0` is one-periodic. -/
theorem periodic_slice {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {t : ℝ} (ht : 0 ≤ t) : IsOnePeriodic (v · (t / (2 * Real.pi))) :=
  h.isOnePeriodic_velocity _ (div_nonneg ht (by positivity))

/-- (H3) The energy and enstrophy series of the flow are summable at every campaign time
`t ≥ 0` (`summable_sob_coeff` at `m = 0, 1` on the slice). -/
theorem summable_classFlow {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun l => ‖classFlow v t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖classFlow v t l‖ ^ 2) := by
  have h0 := summable_sob_coeff (smooth_slice h ht) (periodic_slice h ht) 0
  have h1 := summable_sob_coeff (smooth_slice h ht) (periodic_slice h ht) 1
  constructor
  · refine h0.congr fun l => ?_
    rw [classFlow_apply, mul_zero, pow_zero, one_mul]
  · refine h1.congr fun l => ?_
    rw [classFlow_apply, mul_one]

/-- (H5) The flow is divergence-free at every campaign time `t ≥ 0`. -/
theorem divFree_classFlow {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {t : ℝ} (ht : 0 ≤ t) : DivFree (classFlow v t) :=
  divFree_coeff (smooth_slice h ht) (periodic_slice h ht)
    (fun x => h.div_free x _ (div_nonneg ht (by positivity)))

/-! ## E2. The constancy lemma and the theorem_B_unique wrapper (P5) -/

/-- Equal gradients give equal Fréchet derivatives (`gradient` is `toDual.symm` of
`fderiv`, and `toDual.symm` is injective). -/
theorem fderiv_eq_of_gradient_eq {q₁ q₂ : ℝ³ → ℝ} {x : ℝ³}
    (h : gradient q₁ x = gradient q₂ x) : fderiv ℝ q₁ x = fderiv ℝ q₂ x :=
  (toDual ℝ ℝ³).symm.injective h

/-- Two differentiable scalar fields with the same gradient everywhere differ by the
constant fixed at the origin. -/
theorem eq_add_const_of_gradient_eq {q₁ q₂ : ℝ³ → ℝ}
    (h₁ : Differentiable ℝ q₁) (h₂ : Differentiable ℝ q₂)
    (h : ∀ x, gradient q₁ x = gradient q₂ x) :
    ∀ x, q₁ x = q₂ x + (q₁ 0 - q₂ 0) := by
  intro x
  have hz : ∀ y, fderiv ℝ (q₁ - q₂) y = 0 := by
    intro y
    rw [fderiv_sub (h₁ y) (h₂ y), fderiv_eq_of_gradient_eq (h y), sub_self]
  have hc := is_const_of_fderiv_eq_zero (h₁.sub h₂) hz x 0
  simp only [Pi.sub_apply] at hc
  linarith

/-! ## 4. The theorem_B_unique consumption wrapper -/

/-- The exact shape a class-member coefficient flow supplies: per-window continuity,
per-window budgets (a pair `E, Z` for every window, per flow), pointwise summability
and divergence-freeness, and the integral equation on every window. Uniqueness on
`[0, ∞)` follows from `theorem_B_unique` on the window `[0, t]` with the shared
budgets `max E₁ E₂`, `max Z₁ Z₂`. -/
theorem unique_of_windows {ν : ℝ} (hν : 0 < ν) {c₀ : (Fin 3 → ℤ) → Vel}
    {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel} (h10 : c₁ 0 = c₀) (h20 : c₂ 0 = c₀)
    (h1cont : ∀ k, ∀ T ≥ 0, ContinuousOn (fun s => c₁ s k) (Icc (0:ℝ) T))
    (h2cont : ∀ k, ∀ T ≥ 0, ContinuousOn (fun s => c₂ s k) (Icc (0:ℝ) T))
    (h1sum : ∀ t ≥ 0, Summable (fun l => ‖c₁ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ t l‖ ^ 2))
    (h2sum : ∀ t ≥ 0, Summable (fun l => ‖c₂ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₂ t l‖ ^ 2))
    (h1b : ∀ T ≥ 0, ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T, en (c₁ t) ≤ E ∧ ens (c₁ t) ≤ Z)
    (h2b : ∀ T ≥ 0, ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T, en (c₂ t) ≤ E ∧ ens (c₂ t) ≤ Z)
    (h1div : ∀ t ≥ 0, DivFree (c₁ t)) (h2div : ∀ t ≥ 0, DivFree (c₂ t))
    (h1eq : ∀ T ≥ 0, ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k)))
    (h2eq : ∀ T ≥ 0, ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k))) :
    ∀ t ≥ 0, ∀ k, c₁ t k = c₂ t k := by
  intro t ht k
  obtain ⟨E₁, Z₁, hb1⟩ := h1b t ht
  obtain ⟨E₂, Z₂, hb2⟩ := h2b t ht
  exact @theorem_B_unique ν (max E₁ E₂) (max Z₁ Z₂) t hν ht c₀ c₁ c₂ h10 h20
    (fun k => h1cont k t ht) (fun k => h2cont k t ht)
    (fun s hs => h1sum s hs.1) (fun s hs => h2sum s hs.1)
    (fun s hs => ⟨(hb1 s hs).1.trans (le_max_left _ _),
      (hb1 s hs).2.trans (le_max_left _ _)⟩)
    (fun s hs => ⟨(hb2 s hs).1.trans (le_max_right _ _),
      (hb2 s hs).2.trans (le_max_right _ _)⟩)
    (fun s hs => h1div s hs.1) (fun s hs => h2div s hs.1)
    (h1eq t ht) (h2eq t ht) t (right_mem_Icc.2 ht) k

/-- The funext form of the wrapper: the two flows agree as coefficient families at
every nonnegative time. -/
theorem unique_of_windows' {ν : ℝ} (hν : 0 < ν) {c₀ : (Fin 3 → ℤ) → Vel}
    {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel} (h10 : c₁ 0 = c₀) (h20 : c₂ 0 = c₀)
    (h1cont : ∀ k, ∀ T ≥ 0, ContinuousOn (fun s => c₁ s k) (Icc (0:ℝ) T))
    (h2cont : ∀ k, ∀ T ≥ 0, ContinuousOn (fun s => c₂ s k) (Icc (0:ℝ) T))
    (h1sum : ∀ t ≥ 0, Summable (fun l => ‖c₁ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ t l‖ ^ 2))
    (h2sum : ∀ t ≥ 0, Summable (fun l => ‖c₂ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₂ t l‖ ^ 2))
    (h1b : ∀ T ≥ 0, ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T, en (c₁ t) ≤ E ∧ ens (c₁ t) ≤ Z)
    (h2b : ∀ T ≥ 0, ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T, en (c₂ t) ≤ E ∧ ens (c₂ t) ≤ Z)
    (h1div : ∀ t ≥ 0, DivFree (c₁ t)) (h2div : ∀ t ≥ 0, DivFree (c₂ t))
    (h1eq : ∀ T ≥ 0, ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k)))
    (h2eq : ∀ T ≥ 0, ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k))) :
    ∀ t ≥ 0, c₁ t = c₂ t :=
  fun t ht => funext fun k =>
    unique_of_windows hν h10 h20 h1cont h2cont h1sum h2sum h1b h2b h1div h2div
      h1eq h2eq t ht k

/-! ## E3. THE VELOCITY CAPSTONE (P7 section 4) -/

/-- **THE VELOCITY CAPSTONE.** Uniqueness of the velocity inside OUR COPY of the community
class at `f = 0`: two members with the same datum `u₀`, `0 < ν'` (consumed by
`theorem_B_unique`, not implied by membership: the constant pair is a member for every real
`ν'`), have the same velocity at every `x` and every `t ≥ 0`. A corollary of `theorem_B_unique`
(Tier 4) at campaign viscosity `2πν'` on the window `[0, 2πt]`, applied to the two coefficient
flows `classFlow v₁`, `classFlow v₂` (H1 `classFlow_zero`, H2 `classFlow_continuousOn`, H3
`summable_classFlow`, H4 `classFlow_budget` with the maxima, H5 `divFree_classFlow`, H6
`class_member_integral_eq`), followed by the inversion `u₀Real_coeff` (Tier 9 W1, through the
datum bridge) on the two smooth one-periodic slices at `t`. Textbook energy method in the enstrophy class; nothing new;
no torus-side injectivity lemma is consumed. Nothing about `ν' ≤ 0`, nothing about `f ≠ 0`,
nothing about competitors outside the class. Both upstream statements
`navier_stokes_existence_and_smoothness_periodic` and `navier_stokes_breakdown_periodic` are
untouched. -/
theorem community_unique_velocity {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∀ x, ∀ t ≥ 0, v₁ x t = v₂ x t := by
  intro x t ht
  -- the campaign window [0, 2πt] and the campaign viscosity 2πν'
  have hT : (0:ℝ) ≤ 2 * Real.pi * t := mul_nonneg (by positivity) ht
  have hν : (0:ℝ) < 2 * Real.pi * ν' := by positivity
  -- (H4) budgets, shared by taking maxima
  obtain ⟨E₁, Z₁, hb₁⟩ := classFlow_budget h₁.velocity_smooth h₁.isOnePeriodic_velocity hT
  obtain ⟨E₂, Z₂, hb₂⟩ := classFlow_budget h₂.velocity_smooth h₂.isOnePeriodic_velocity hT
  -- (H2) mode continuity, in theorem_B_unique's lambda shape
  have hc₁ : ∀ k, ContinuousOn (fun s => classFlow v₁ s k) (Icc (0:ℝ) (2 * Real.pi * t)) :=
    fun k => classFlow_continuousOn h₁.velocity_smooth h₁.isOnePeriodic_velocity k hT
  have hc₂ : ∀ k, ContinuousOn (fun s => classFlow v₂ s k) (Icc (0:ℝ) (2 * Real.pi * t)) :=
    fun k => classFlow_continuousOn h₂.velocity_smooth h₂.isOnePeriodic_velocity k hT
  -- (H6) the integral equations, in theorem_B_unique's shape at ν := 2πν'
  have he₁ : ∀ s ∈ Icc (0:ℝ) (2 * Real.pi * t), ∀ k, classFlow v₁ s k = coeff u₀ k +
      ∫ r in (0:ℝ)..s, ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • classFlow v₁ r k
        + lerayProj k (convFull (classFlow v₁ r) k)) :=
    class_member_integral_eq h₁ hT
  have he₂ : ∀ s ∈ Icc (0:ℝ) (2 * Real.pi * t), ∀ k, classFlow v₂ s k = coeff u₀ k +
      ∫ r in (0:ℝ)..s, ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • classFlow v₂ r k
        + lerayProj k (convFull (classFlow v₂ r) k)) :=
    class_member_integral_eq h₂ hT
  -- Tier 4 uniqueness on the window
  have hcoef : ∀ k, classFlow v₁ (2 * Real.pi * t) k = classFlow v₂ (2 * Real.pi * t) k :=
    theorem_B_unique (E := max E₁ E₂) (Z := max Z₁ Z₂) hν hT
      (classFlow_zero h₁) (classFlow_zero h₂) hc₁ hc₂
      (fun s hs => summable_classFlow h₁ hs.1)
      (fun s hs => summable_classFlow h₂ hs.1)
      (fun s hs => ⟨(hb₁ s hs).1.trans (le_max_left _ _), (hb₁ s hs).2.trans (le_max_left _ _)⟩)
      (fun s hs => ⟨(hb₂ s hs).1.trans (le_max_right _ _),
        (hb₂ s hs).2.trans (le_max_right _ _)⟩)
      (fun s hs => divFree_classFlow h₁ hs.1)
      (fun s hs => divFree_classFlow h₂ hs.1)
      he₁ he₂ (2 * Real.pi * t) ⟨hT, le_refl _⟩
  -- back to the class clock: equal coefficient fields of the two slices at t
  have hc : coeff (v₁ · t) = coeff (v₂ · t) := by
    rw [← classFlow_clock v₁ t, ← classFlow_clock v₂ t]
    exact funext hcoef
  -- THE INVERSION (W1): equal coefficient fields of smooth one-periodic fields give equal fields
  have hs₁ : ContDiff ℝ ∞ (v₁ · t) := contDiff_space_slice h₁.velocity_smooth ht
  have hs₂ : ContDiff ℝ ∞ (v₂ · t) := contDiff_space_slice h₂.velocity_smooth ht
  have hp₁ : IsOnePeriodic (v₁ · t) := h₁.isOnePeriodic_velocity t ht
  have hp₂ : IsOnePeriodic (v₂ · t) := h₂.isOnePeriodic_velocity t ht
  calc v₁ x t = u₀Real (coeff (v₁ · t)) x := by rw [u₀Real_coeff hs₁ hp₁]
    _ = u₀Real (coeff (v₂ · t)) x := by rw [hc]
    _ = v₂ x t := by rw [u₀Real_coeff hs₂ hp₂]

/-! ## E4. THE PRESSURE CAPSTONE (P5 section 3) -/

/-- Equal velocities on `[0, ∞)` give equal time slices at every `t ≥ 0`. -/
theorem slice_eq_of_velocity_eq {v₁ v₂ : ℝ³ → ℝ → ℝ³}
    (hv : ∀ x, ∀ t ≥ 0, v₁ x t = v₂ x t) {t : ℝ} (ht : 0 ≤ t) :
    (fun x => v₁ x t) = (fun x => v₂ x t) :=
  funext fun x => hv x t ht

/-- Equal velocities on `[0, ∞)` give equal within-derivatives on `Ici 0`. -/
theorem derivWithin_eq_of_velocity_eq {v₁ v₂ : ℝ³ → ℝ → ℝ³}
    (hv : ∀ x, ∀ t ≥ 0, v₁ x t = v₂ x t) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (v₁ x ·) (Ici 0) t = derivWithin (v₂ x ·) (Ici 0) t :=
  derivWithin_congr (fun τ hτ => hv x τ hτ) (hv x t ht)

/-- Subtracting the two class equations at `(x, t)` once the velocities agree: the
pressure gradients agree. -/
theorem gradient_eq_of_velocity_eq {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂)
    (hv : ∀ x, ∀ t ≥ 0, v₁ x t = v₂ x t) (x : ℝ³) {t : ℝ} (ht : 0 ≤ t) :
    gradient (p₁ · t) x = gradient (p₂ · t) x := by
  have e₁ := h₁.navier_stokes x t ht
  have e₂ := h₂.navier_stokes x t ht
  rw [derivWithin_eq_of_velocity_eq hv x ht, slice_eq_of_velocity_eq hv ht,
    hv x t ht] at e₁
  have e := e₁.symm.trans e₂
  simp only [Pi.zero_apply, add_zero] at e
  exact sub_right_injective e

/-- **THE PRESSURE CAPSTONE.** Inside OUR COPY of the community class at
`f = 0`, two members with the same datum have pressures that agree up to a function
of time; the function is `p₁ 0 · - p₂ 0 ·`. The `n = 0` pressure mode is free; never
claim `p₁ = p₂` (the register refutes it and the `∃ C` form). Hypotheses named: `0 < ν'`
(consumed by `theorem_B_unique` through the velocity capstone, not implied by membership),
the same datum `u₀`, `f = 0`, OUR COPY of the class. A corollary of `theorem_B_unique` (Tier 4)
through the datum bridge (Tier 9 W1) and the class equation; textbook; nothing new. Both
upstream statements `navier_stokes_existence_and_smoothness_periodic` and
`navier_stokes_breakdown_periodic` are untouched. -/
theorem community_unique_pressure {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∃ g : ℝ → ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + g t := by
  have hv := community_unique_velocity hν' h₁ h₂
  refine ⟨fun t => p₁ 0 t - p₂ 0 t, ?_⟩
  intro x t ht
  exact eq_add_const_of_gradient_eq
    (fun y => TimeConstantWitness.pressure_slice h₁.pressure_smooth ht y)
    (fun y => TimeConstantWitness.pressure_slice h₂.pressure_smooth ht y)
    (fun y => gradient_eq_of_velocity_eq h₁ h₂ hv y ht) x

/-- The gradient form of the pressure result inside OUR COPY of the community class at
`f = 0`: two members with the same datum `u₀` and `0 < ν'` (consumed by `theorem_B_unique`
through the velocity capstone, not implied by membership) have equal pressure gradients at
every `x` and every `t ≥ 0`. This is the sharp form behind `community_unique_pressure` (the
pressure itself is unique only up to a function of time). Both upstream statements
`navier_stokes_existence_and_smoothness_periodic` and `navier_stokes_breakdown_periodic` are
untouched. -/
theorem community_unique_pressure_gradient {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∀ x, ∀ t ≥ 0, gradient (p₁ · t) x = gradient (p₂ · t) x :=
  fun x _ ht => gradient_eq_of_velocity_eq h₁ h₂ (community_unique_velocity hν' h₁ h₂) x ht

/-- The pressure result inside OUR COPY of the community class at `f = 0` with the velocity
agreement taken as an explicit hypothesis (the brick behind `community_unique_pressure`; needs
no `0 < ν'` because `theorem_B_unique` is not consumed here): two members with the same datum
`u₀` whose velocities agree at every `x` and every `t ≥ 0` have pressures that agree up to a
function of time (`g t = p₁ 0 t - p₂ 0 t`). Both upstream statements are untouched. -/
theorem community_unique_pressure_of_velocity {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂)
    (hv : ∀ x, ∀ t ≥ 0, v₁ x t = v₂ x t) :
    ∃ g : ℝ → ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + g t := by
  refine ⟨fun t => p₁ 0 t - p₂ 0 t, ?_⟩
  intro x t ht
  exact eq_add_const_of_gradient_eq
    (fun y => TimeConstantWitness.pressure_slice h₁.pressure_smooth ht y)
    (fun y => TimeConstantWitness.pressure_slice h₂.pressure_smooth ht y)
    (fun y => gradient_eq_of_velocity_eq h₁ h₂ hv y ht) x

/-- The explicit form of the pressure result inside OUR COPY of the community class at `f = 0`
(no `∃`): two members with the same datum `u₀` and `0 < ν'` (consumed by `theorem_B_unique`
through the velocity capstone, not implied by membership) have `p₁ x t = p₂ x t + (p₁ 0 t -
p₂ 0 t)` at every `x` and every `t ≥ 0`; the function of time of `community_unique_pressure` is
exhibited, so a consumer needs no choice. The pressure is unique up to that function of time
only (the register refutes `p₁ = p₂` and the constant form). Both upstream statements
`navier_stokes_existence_and_smoothness_periodic` and `navier_stokes_breakdown_periodic` are
untouched. -/
theorem community_unique_pressure_explicit {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + (p₁ 0 t - p₂ 0 t) := by
  have hv := community_unique_velocity hν' h₁ h₂
  intro x t ht
  exact eq_add_const_of_gradient_eq
    (fun y => TimeConstantWitness.pressure_slice h₁.pressure_smooth ht y)
    (fun y => TimeConstantWitness.pressure_slice h₂.pressure_smooth ht y)
    (fun y => gradient_eq_of_velocity_eq h₁ h₂ hv y ht) x

/-! ## E5. Torus-side injectivity in tree spelling (P7 section 5; landed as asked by the handoff) -/

/-- L² injectivity of the coefficients on `C(T³, ℂ)` (ReconR6.lean:365 pattern, the reader's
clone ReproveInversion.lean against the built tree). -/
theorem eq_of_mFourierCoeff_eq {f g : C(UnitAddTorus (Fin 3), ℂ)}
    (h : ∀ n, mFourierCoeff (⇑f) n = mFourierCoeff (⇑g) n) : f = g := by
  have hrepr : (mFourierBasis (d := Fin 3)).repr (ContinuousMap.toLp (E := ℂ) 2 volume ℂ f)
      = (mFourierBasis (d := Fin 3)).repr (ContinuousMap.toLp (E := ℂ) 2 volume ℂ g) := by
    ext n
    rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_toLp, mFourierCoeff_toLp]
    exact h n
  have hLp : ContinuousMap.toLp (E := ℂ) 2 volume ℂ f = ContinuousMap.toLp (E := ℂ) 2 volume ℂ g :=
    (mFourierBasis (d := Fin 3)).repr.injective hrepr
  exact (ContinuousMap.toLp_inj (volume : Measure (UnitAddTorus (Fin 3)))).mp hLp

/-- (a) Injectivity of `coeff` on smooth one-periodic fields, by the inversion `u₀Real_coeff`
(three lines). -/
theorem eq_of_coeff_eq {u₁ u₂ : ℝ³ → ℝ³} (h₁ : ContDiff ℝ ∞ u₁) (p₁ : IsOnePeriodic u₁)
    (h₂ : ContDiff ℝ ∞ u₂) (p₂ : IsOnePeriodic u₂) (h : coeff u₁ = coeff u₂) : u₁ = u₂ :=
  calc u₁ = u₀Real (coeff u₁) := (u₀Real_coeff h₁ p₁).symm
    _ = u₀Real (coeff u₂) := by rw [h]
    _ = u₂ := u₀Real_coeff h₂ p₂

/-- (b) The same, by torus-side L² injectivity on the bundled descents of the complexified
components, read back at `fiber x` through `descend_fiber`, `Complex.ofReal_injective`, and
`PiLp.ext`. -/
theorem eq_of_coeff_eq' {u₁ u₂ : ℝ³ → ℝ³} (h₁ : ContDiff ℝ ∞ u₁) (p₁ : IsOnePeriodic u₁)
    (h₂ : ContDiff ℝ ∞ u₂) (p₂ : IsOnePeriodic u₂) (h : coeff u₁ = coeff u₂) : u₁ = u₂ := by
  funext x
  refine PiLp.ext fun j => ?_
  have hfc₁ : ContDiff ℝ ∞ (fun y : ℝ³ => ((u₁ y j : ℝ) : ℂ)) := contDiff_ofReal_component h₁ j
  have hfp₁ : IsOnePeriodic (fun y : ℝ³ => ((u₁ y j : ℝ) : ℂ)) :=
    isOnePeriodic_ofReal_component p₁ j
  have hfc₂ : ContDiff ℝ ∞ (fun y : ℝ³ => ((u₂ y j : ℝ) : ℂ)) := contDiff_ofReal_component h₂ j
  have hfp₂ : IsOnePeriodic (fun y : ℝ³ => ((u₂ y j : ℝ) : ℂ)) :=
    isOnePeriodic_ofReal_component p₂ j
  let g₁ : C(UnitAddTorus (Fin 3), ℂ) :=
    ⟨descend (fun y : ℝ³ => ((u₁ y j : ℝ) : ℂ)), continuous_descend hfc₁.continuous hfp₁⟩
  let g₂ : C(UnitAddTorus (Fin 3), ℂ) :=
    ⟨descend (fun y : ℝ³ => ((u₂ y j : ℝ) : ℂ)), continuous_descend hfc₂.continuous hfp₂⟩
  have hg : g₁ = g₂ := by
    refine eq_of_mFourierCoeff_eq fun n => ?_
    have hj : coeff u₁ n j = coeff u₂ n j := by rw [h]
    exact hj
  have e₁ : g₁ (fiber x) = ((u₁ x j : ℝ) : ℂ) := descend_fiber hfp₁ x
  have e₂ : g₂ (fiber x) = ((u₂ x j : ℝ) : ℂ) := descend_fiber hfp₂ x
  refine Complex.ofReal_injective ?_
  rw [← e₁, ← e₂, hg]

/-! ## E6. The consistency corollary (P7 section 6) -/

/-- Every member of OUR COPY of the class at `f = 0` with the constant datum `m` and `0 < ν'` is
the constant pair's velocity on `t ≥ 0` (the velocity capstone against
`T9Probe.const_pair_in_class`). -/
theorem const_datum_member_is_const (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν')
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p) :
    ∀ x, ∀ t ≥ 0, v x t = m :=
  community_unique_velocity hν' h (T9Probe.const_pair_in_class ν' m)

/-- In particular every witness of `T9Probe.capstone_fires_on_const_datum` (a member of OUR COPY
of the class at `f = 0` with the constant datum and `0 < ν'`) is the constant pair's velocity on
`t ≥ 0`. -/
theorem capstone_fires_on_const_datum_witness (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p ∧
        ∀ x, ∀ t ≥ 0, v x t = m := by
  obtain ⟨v, p, h⟩ := T9Probe.capstone_fires_on_const_datum m hν'
  exact ⟨v, p, h, const_datum_member_is_const m hν' h⟩

/-! ## E7. The vacuity / must-fail register (P8, plus the MUST-HOLD items of the design) -/

namespace T9cProbe

open T9Probe

/-! ## (1) Adding a smooth function of time alone to the pressure keeps membership -/

/-- The gradient of a spatial function plus a constant is the gradient of the function
(no differentiability needed: `fderiv_add_const` is unconditional at the pin). -/
theorem gradient_add_const_eq (q : ℝ³ → ℝ) (C : ℝ) (x : ℝ³) :
    gradient (fun y => q y + C) x = gradient q x := by
  simp only [gradient, fderiv_add_const]

/-- The uncurry of the shifted pressure is the uncurry of the pressure plus `g` of the
time coordinate (definitional). -/
theorem uncurry_pressure_add (p : ℝ³ → ℝ → ℝ) (g : ℝ → ℝ) :
    (↿(fun x t => p x t + g t) : ℝ³ × ℝ → ℝ) = fun q => (↿p) q + g q.2 := by
  funext q; rfl

/-- (1) A class member `(v, p)` at `f = 0` stays a class member when a smooth function of
time alone is added to the pressure: the momentum equation sees only the spatial gradient
of `p · t`, and `gradient (fun y => p y t + g t) x = gradient (p · t) x`. -/
theorem pressure_add_time_function_in_class {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v
      (fun x t => p x t + g t) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x t ht
    show derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      ν' • Δ (v · t) x - gradient (fun y => p y t + g t) x + (0 : ℝ³ → ℝ → ℝ³) x t
    rw [gradient_add_const_eq (fun y => p y t) (g t) x]
    exact h.navier_stokes x t ht
  · exact h.div_free
  · exact h.initial_condition
  · exact h.velocity_smooth
  · rw [uncurry_pressure_add p g]
    exact h.pressure_smooth.add ((hg.comp contDiff_snd).contDiffOn)
  · exact h.isOnePeriodic_velocity
  · intro t ht x i
    have hp := h.isOnePeriodic_pressure t ht x i
    show p (x + EuclideanSpace.single i 1) t + g t = p x t + g t
    rw [show p (x + EuclideanSpace.single i 1) t = p x t from hp]

/-- Corollary: a constant shift of the pressure keeps membership. -/
theorem pressure_add_const_in_class {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) (C : ℝ) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v
      (fun x t => p x t + C) :=
  pressure_add_time_function_in_class h (fun _ => C) contDiff_const

/-- Corollary: adding the time coordinate itself to the pressure keeps membership. -/
theorem pressure_add_id_in_class {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v
      (fun x t => p x t + t) :=
  pressure_add_time_function_in_class h id contDiff_id

/-! ## (2) The pressure form is sharp (must-fail) -/

/-- (2a) Pointwise equality of pressures is NOT a consequence of membership with the same
datum: the rest pair at `ν' = 1` and its pressure shift by `1` refute it at `(0, 0)`. -/
theorem pressure_not_unique :
    ¬ (∀ (ν' : ℝ), 0 < ν' → ∀ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ →
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ →
      ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t) := by
  intro H
  have h1 := rest_pair_in_class' 1
  have h2 := pressure_add_const_in_class h1 1
  have := H 1 one_pos _ _ _ _ _ h1 h2 0 0 le_rfl
  simp at this

/-- (2b) Equality of pressures up to a CONSTANT is NOT a consequence either: the rest pair
and its pressure shift by `t` would need the constant to be `0` at `t = 0` and `1` at
`t = 1`. -/
theorem pressure_not_unique_up_to_const :
    ¬ (∀ (ν' : ℝ), 0 < ν' → ∀ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ →
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ →
      ∃ C : ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + C) := by
  intro H
  have h1 := rest_pair_in_class' 1
  have h2 := pressure_add_id_in_class h1
  obtain ⟨C, hC⟩ := H 1 one_pos _ _ _ _ _ h2 h1
  have h0 := hC 0 0 le_rfl
  have h1' := hC 0 1 zero_le_one
  simp at h0 h1'
  linarith

/-! ## (3) Two DISTINCT members with the same nonzero datum exist (non-vacuity) -/

/-- (3) For every `ν' > 0` the hypothesis set of both W3 capstones (recon wording: "candidates";
both are frozen above, E3 and E4) is inhabited by two
DISTINCT pairs on a NONZERO datum: the capstone's witness on the shear datum, and the same
velocity with the pressure shifted by `1`.  The velocity conclusion is consistent with them
(same `v`); the pressure conclusion needs its function of time. -/
theorem two_members_same_datum {ν' : ℝ} (hν' : 0 < ν') :
    ∃ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
      u₀ ≠ 0 ∧
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ ∧
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ ∧
      p₁ ≠ p₂ := by
  obtain ⟨ε, hε, hne, ⟨v, p, hvp⟩, -⟩ := capstone_fires_on_testDatum hν'
  refine ⟨_, v, v, p, fun x t => p x t + 1, hne, hvp, pressure_add_const_in_class hvp 1, ?_⟩
  intro heq
  have := congrFun (congrFun heq 0) 0
  linarith

/-! ## (4) Different data are not forced equal -/

/-- (4) The datum hypothesis is load-bearing: the rest pair (datum `0`) and the constant pair
at datum `e₀` are both class members at `ν' = 1` and their velocities differ at `(0, 0)`. -/
theorem different_data_not_forced_equal :
    ∃ (ν' : ℝ), 0 < ν' ∧
      ∃ (u₀ u₀' : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀' (f := 0) v₂ p₂ ∧
        ∃ x, ∃ t ≥ 0, v₁ x t ≠ v₂ x t := by
  refine ⟨1, one_pos, 0, fun _ => EuclideanSpace.single (0 : Fin 3) (1 : ℝ),
    0, fun _ _ => EuclideanSpace.single (0 : Fin 3) (1 : ℝ), 0, fun _ _ => 0,
    rest_pair_in_class' 1, const_pair_in_class 1 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)),
    0, 0, le_rfl, ?_⟩
  intro h
  have := congrArg (fun w : ℝ³ => w 0) h
  simp at this

/-! ## (5) Membership says nothing about the sign of the viscosity -/

/-- (5) The class is inhabited at the zero datum for EVERY real viscosity (sign unconstrained);
the capstones' `0 < ν'` (recon wording: "the candidates'"; both are frozen above) is consumed by
`theorem_B_unique`, not implied by membership.  Non-uniqueness at `ν' ≤ 0` is NOT claimed. -/
theorem class_inhabited_all_visc (ν' : ℝ) :
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (0 : ℝ³ → ℝ³) (f := 0) v p :=
  ⟨_, _, rest_pair_in_class' ν'⟩

/-! ## (6) The constant datum has two named members -/

/-- (6) The constant pair is a member at the constant datum, and the capstone supplies a
member there too.  That the capstone member equals the constant pair in velocity is a corollary of
`community_unique_velocity` (recon wording: "the candidate ... not proved here"; the capstone is
frozen above as E3, and the identification is proved in this file as
`const_datum_member_is_const` and `capstone_fires_on_const_datum_witness`, E6). -/
theorem const_datum_two_members (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0)
      (fun _ _ => m) (fun _ _ => 0) ∧
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p :=
  ⟨const_pair_in_class ν' m, capstone_fires_on_const_datum m hν'⟩

/-! ## (7) Junk note: the coefficient flow of an arbitrary pair is a well-typed junk object -/

/-- (7) `coeff` of the time slice of an arbitrary pair is well typed but its inversion fails
off the class: for `v x _ := x` the slice is not periodic (`inversion_fails_off_class`). -/
theorem classFlow_junk : ∃ v : ℝ³ → ℝ → ℝ³, u₀Real (coeff (v · 0)) ≠ (v · 0) :=
  ⟨fun x _ => x, inversion_fails_off_class⟩

/-- (7') The same through the canonical `classFlow` spelling. -/
theorem classFlow_junk' : ∃ v : ℝ³ → ℝ → ℝ³, u₀Real (classFlow v 0) ≠ (v · 0) :=
  ⟨fun x _ => x, by rw [classFlow_zero_eq]; exact inversion_fails_off_class⟩

/-! ### (8) MUST HOLD: consistency with the Tier 9 flow sibling (written by the design pass) -/

/-- (8a) Any coefficient flow `c` in `theorem_B_unique`'s class (the sibling's clauses 1 to 5
and 7, on `Ici 0`) starting from `meanFree (coeff u₀)` agrees with `classFlow v` for EVERY class
member `v` on the datum `u₀`, provided the datum is mean-free (`coeff u₀ 0 = 0`, so that the two
initial fields coincide). The route of `community_unique_velocity`, stopped before the inversion. -/
theorem classFlow_eq_of_flow {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³} (h0 : coeff u₀ 0 = 0)
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (h1 : c 0 = meanFree (coeff u₀))
    (h2 : ∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t))
    (h3 : ∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2))
    (h4 : ∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ)))
    (h5 : ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = meanFree (coeff u₀) k + ∫ s in (0:ℝ)..t,
      ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)))
    (h7 : ∀ t ∈ Ici (0:ℝ), en (c t) ≤ en (meanFree (coeff u₀)) ∧
      ens (c t) ≤ ens (meanFree (coeff u₀)))
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    ∀ t ≥ 0, classFlow v t = c t := by
  intro t ht
  have hmf : meanFree (coeff u₀) = coeff u₀ := meanFree_of_mean_zero h0
  have hν : (0:ℝ) < 2 * Real.pi * ν' := by positivity
  obtain ⟨E₁, Z₁, hb₁⟩ := classFlow_budget h.velocity_smooth h.isOnePeriodic_velocity ht
  have hc₁ : ∀ k, ContinuousOn (fun s => classFlow v s k) (Icc (0:ℝ) t) :=
    fun k => classFlow_continuousOn h.velocity_smooth h.isOnePeriodic_velocity k ht
  have he₁ : ∀ s ∈ Icc (0:ℝ) t, ∀ k, classFlow v s k = coeff u₀ k +
      ∫ r in (0:ℝ)..s, ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • classFlow v r k
        + lerayProj k (convFull (classFlow v r) k)) :=
    class_member_integral_eq h ht
  have h1' : c 0 = coeff u₀ := by rw [h1, hmf]
  have he₂ : ∀ s ∈ Icc (0:ℝ) t, ∀ k, c s k = coeff u₀ k +
      ∫ r in (0:ℝ)..s, ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • c r k
        + lerayProj k (convFull (c r) k)) := by
    intro s hs k
    rw [← hmf]
    exact h5 s hs.1 k
  funext k
  exact theorem_B_unique (E := max E₁ (en (meanFree (coeff u₀))))
    (Z := max Z₁ (ens (meanFree (coeff u₀)))) hν ht
    (classFlow_zero h) h1' hc₁ (fun k => (h4 k).mono Icc_subset_Ici_self)
    (fun s hs => summable_classFlow h hs.1) (fun s hs => h3 s hs.1)
    (fun s hs => ⟨(hb₁ s hs).1.trans (le_max_left _ _), (hb₁ s hs).2.trans (le_max_left _ _)⟩)
    (fun s hs => ⟨(h7 s hs.1).1.trans (le_max_right _ _),
      (h7 s hs.1).2.trans (le_max_right _ _)⟩)
    (fun s hs => divFree_classFlow h hs.1) (fun s hs => (h2 s hs.1).2)
    he₁ he₂ t (right_mem_Icc.2 ht) k

/-- (8b) MUST HOLD, the Tier 9 instance: on a mean-free datum meeting the smallness hypothesis,
the flow `c` exhibited by `theorem_B_community_periodic_data_flow` IS the coefficient flow
`classFlow` of the member it exhibits, `galV (meanVec (coeff u₀)) (vReal c)`, at every `t ≥ 0`
(and of every other member on that datum, by (8a)). The `∃ κ` is the sibling's own. -/
theorem flow_witness_classFlow_eq :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ → coeff u₀ 0 = 0 →
      κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = meanFree (coeff u₀) ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0)
          (galV (meanVec (coeff u₀)) (vReal c)) (galP (meanVec (coeff u₀)) (pReal c)) ∧
        ∀ t ≥ 0, classFlow (galV (meanVec (coeff u₀)) (vReal c)) t = c t := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_data_flow
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' u₀ hu₀ h0 hsmall
  obtain ⟨c, h1, h2, h3, h4, h5, -, h7, hclass⟩ := H hν' hu₀ hsmall
  exact ⟨c, h1, hclass, classFlow_eq_of_flow hν' h0 h1 h2 h3 h4 h5
    (fun t ht => ⟨(h7 t ht).1, (h7 t ht).2.1⟩) hclass⟩

/-! ## (9) The velocity capstone's `∀ t ≥ 0` is sharp (the statement-shape critic's S9) -/

/-- A velocity that is the rest state for `t ≥ 0` and the constant `m` for `t < 0`. -/
def preHistory (m : ℝ³) : ℝ³ → ℝ → ℝ³ := fun _ t => if t < 0 then m else 0

/-- (9a) `preHistory m` with the zero pressure is a member of OUR COPY of the class at `f = 0`
on the zero datum for every real `ν'`: every field of the class only looks at `t ≥ 0`. -/
theorem preHistory_in_class (ν' : ℝ) (m : ℝ³) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (0 : ℝ³ → ℝ³) (f := 0)
      (preHistory m) (0 : ℝ³ → ℝ → ℝ) := by
  have hr := T9Probe.rest_pair_in_class' ν'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x t ht
    have e := hr.navier_stokes x t ht
    have hd : derivWithin (preHistory m x ·) (Ici 0) t =
        derivWithin ((0 : ℝ³ → ℝ → ℝ³) x ·) (Ici 0) t :=
      derivWithin_congr (fun s hs => if_neg (not_lt.2 hs)) (if_neg (not_lt.2 ht))
    have hs : (preHistory m · t) = ((0 : ℝ³ → ℝ → ℝ³) · t) :=
      funext fun _ => if_neg (not_lt.2 ht)
    have hx : preHistory m x t = (0 : ℝ³ → ℝ → ℝ³) x t := if_neg (not_lt.2 ht)
    rw [hd, hs, hx]
    exact e
  · intro x t ht
    have hs : (preHistory m · t) = ((0 : ℝ³ → ℝ → ℝ³) · t) :=
      funext fun _ => if_neg (not_lt.2 ht)
    rw [hs]
    exact hr.div_free x t ht
  · intro x
    exact if_neg (lt_irrefl _)
  · exact contDiffOn_const.congr fun q hq => if_neg (not_lt.2 hq.2)
  · exact hr.pressure_smooth
  · intro t _ x i
    rfl
  · exact hr.isOnePeriodic_pressure

/-- (9) SHARPNESS of `∀ t ≥ 0` in `community_unique_velocity`: two members of OUR COPY of the
class at `f = 0` with the same datum `0` and `ν' = 1` whose velocities differ at `t = -1` (the
class only looks at `t ≥ 0`); function equality `v₁ = v₂` is FALSE as a consequence of
membership, so the capstone's conclusion cannot be strengthened to it. -/
theorem velocity_not_unique_off_halfline :
    ∃ (ν' : ℝ), 0 < ν' ∧
      ∃ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ ∧
        v₁ ≠ v₂ := by
  refine ⟨1, one_pos, 0, 0, preHistory (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)), 0, 0,
    T9Probe.rest_pair_in_class' 1, preHistory_in_class 1 _, ?_⟩
  intro h
  have h1 := congrArg (fun w : ℝ³ => w 0) (congrFun (congrFun h 0) (-1))
  simp only [preHistory] at h1
  rw [if_pos (by norm_num : (-1:ℝ) < 0)] at h1
  simp at h1

end T9cProbe

end

end TheoremB
