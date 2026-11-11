/-
  TheoremB/CommunityData.lean
  Tier 9, wave W2 (Theorem B campaign, 13 Sep 2026): the mean-free algebra of
  a coefficient family, the zero-mode family (the constant datum on the
  coefficient side), THE CAPSTONE OF TIER 9 `theorem_B_community_periodic_data`
  with its witness-exposing sibling and its consistency corollary, and the
  registered probe section `T9Probe` (the vacuity / must-fail register of the
  blueprint's section 6).  Transcribed from sections D and E of the design
  probe `audit-tier9/design/final/Tier9Final.lean` (session directory, never
  a tracked file; compiled there at the pin, exit 0; sections D and E have no
  declaration with a placeholder proof, the probe's only two being the W3
  candidates of its section F, not transcribed); the frozen statements are
  those of `context/rung11-tier9-blueprint.md` section 4b (the CommunityData
  block) and the register statements those of its section 6, byte-identical,
  and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * The mean-free algebra (D1): `meanFree c k := if k = 0 then 0 else c k`,
    `meanVec c := toLp 2 fun j => (c 0 j).re`; `meanFree_zero` (a `simp`
    lemma), `meanFree_of_mean_zero` (a mean-zero family is its own mean-free
    part), `realField_meanFree`, `divFree_meanFree`, `summable_sob_meanFree`
    (reality, divergence-freeness and every Sobolev level pass to the
    mean-free part), `ens_meanFree` (the enstrophy is insensitive to the
    mean), `en_meanFree` (`en (meanFree c) = en c - ‖c 0‖²`),
    `uLift_meanFree_add` (the point split of the lift at the zero mode), and
    the mean split of the real datum `u₀Real_eq_meanVec_add` /
    `u₀Real_eq_meanVec_add'`:
    `u₀Real c = fun x => meanVec c + u₀Real (meanFree c) x` for an ℓ¹ family.
  * The zero-mode family (D2): `zeroMode m k := if k = 0 then castCV m else 0`;
    `u₀Real_zeroMode` (the constant datum IS `u₀Real (zeroMode m)`),
    `realField_zeroMode`, `summable_norm_zeroMode`, `meanFree_zeroMode`,
    `meanVec_zeroMode`, and `zeroMode_meets_all_but_mean_zero`: the zero-mode
    family meets every hypothesis of `theorem_B_community_periodic` except
    `c₀ 0 = 0`, which holds iff `m = 0`.
  * THE CAPSTONE `theorem_B_community_periodic_data` (D3): for every `ν' > 0`
    and every real-space datum `u₀` in the community's own
    `InitialVelocityConditionPeriodic (n := 3)` whose mean-free coefficient
    part is small in the sense
    `κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4`,
    `∃ v p, NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p`.
    Route: `datum_bridge` (DatumBridge.lean, W1) gives the coefficient field;
    its mean-free part is in the trap class of `theorem_B_community_periodic`
    (CommunityClass.lean, Tier 8b); the witness pair is boosted by the mean
    vector through `galilean_class` (Galilean.lean); the mean split and the
    inversion `u₀Real (coeff u₀) = u₀` identify the datum.
  * The witness-exposing sibling `theorem_B_community_periodic_data_flow`: the
    same hypotheses; the coefficient flow `c` at `ν := 2πν'` from the datum
    `meanFree (coeff u₀)` is exhibited with clauses 1 to 7 of
    `theorem_B_community_periodic_flow` (clauses 1 to 6 line-identical to
    CommunityClass.lean:1621-1629 under the substitution `ν ↦ 2πν'`,
    `c₀ ↦ meanFree (coeff u₀)`; clause 7 identical up to a line re-wrap,
    three lines here, two there, and the parentheses the compound term
    takes in application position, `en (meanFree (coeff u₀))`), together
    with the class membership of the
    explicit pair
    `(galV (meanVec (coeff u₀)) (vReal c), galP (meanVec (coeff u₀)) (pReal c))`.
  * The consistency corollary `theorem_B_community_periodic_of_data`: the
    `∃ v p` of `theorem_B_community_periodic` re-derived from the capstone at
    `u₀ := u₀Real c₀` through the round trip `coeff (u₀Real c₀) = c₀` and
    `meanFree_of_mean_zero`.
  * The register `T9Probe` (section E; non-frozen, registered: sixteen
    theorems, one ledger line each): the constant datum and the constant pair
    inhabit the class for every real `ν'` (`const_datum_in_class`,
    `const_pair_in_class`, `rest_pair_in_class'`); the constant datum is
    HANDLED, not excluded (`coeff_const`, `capstone_hyp_const_datum`,
    `capstone_fires_on_const_datum`); the shear datum inhabits the class, its
    coefficient field is the shear, and the smallness hypothesis holds on it
    for a nonzero `ε` (`testDatum_in_class`, `coeff_testDatum`,
    `capstone_hyp_testDatum`); the capstone fires on the shear NON-TRIVIALLY
    (`capstone_fires_on_testDatum`: both trivial candidates fail for every
    pressure); the inversion FAILS off the class (`inversion_fails_off_class`,
    on the identity field); the shear is not constant (`shear_not_const`); the
    smallness hypothesis is NOT universal on the class
    (`capstone_hyp_not_universal`); the mean enters no hypothesis
    (`capstone_hyp_shifted_iff`, `ivc_const_add`,
    `capstone_fires_on_shifted_shear`).  Its helpers are the public clones, on
    the `cc` names, of the PRIVATE `W3Probe` pair-datum facts stated there on
    `pe1`, `pBox`, `probeVec`, `pairDatum` (`zero_notMem_ccBox`,
    `ccPair_zero_mode`, `ccBox_symm`, `conjVel_ccVec`,
    `realField_ccPair_ccVec`, `dotR_ccVec_ccpe1`, `dotR_ccVec_neg_ccpe1`,
    `divFree_ccPair_ccVec`, `summable_wsq_ccPair`, `summable_norm_ccPair`,
    `pair_tsum_sq`, `en_ccPair`, `ens_ccPair`, `norm_ccVec`), built on the
    PUBLIC `TimeConstantWitness` names (`ccPair`, `ccVec`, `ccBox`, `ccpe1`,
    `testDatum_eq`, `ccPair_eq_zero`, `ccVec_apply`, `ccpe1_ne_neg`,
    `norm_freq_ccpe1`, `norm_freq_neg_ccpe1`) and never un-privating
    anything, plus `divergence_const`, `ccpe1_ne_zero`, `testDatum_ccpe1`,
    `ccVec_ne_zero`, `meanFree_add`, `meanVec_add`, `meanVec_of_mean_zero`,
    `realField_add`, `coeff_const_add`, `testDatum_real`, `testDatum_summable`,
    `testDatum_zero_mode`, `smallness_factors_shift_invariant`,
    `meanVec_coeff_shifted_shear`, `no_time_constant_witness_on_shear`.

  HONEST SCOPE (binding wording, section 7 of the blueprint).
  * The upstream file carries the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown
    statement `navier_stokes_breakdown_periodic`.  The capstone
    `theorem_B_community_periodic_data` is the positive statement's
    CONCLUSION under a smallness hypothesis on the MEAN-FREE part of the
    datum's coefficient field,
    `κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀)) < (2π ν')⁴`, at
    `f = 0`; it says nothing about the positive statement for general data
    (the register's `capstone_hyp_not_universal` is the compiled failure of
    the hypothesis on a large shear) and nothing about the breakdown
    statement.  Both upstream placeholder proofs are untouched.  OUR COPY of the class
    is inhabited; the external file is not imported.
  * Existence only: the class has no uniqueness clause.  Uniqueness of the
    COEFFICIENT flow behind the witness is `theorem_B_unique`
    (FullUnique.lean:327), reachable through the flow sibling, whose clauses
    1 to 7 SUPPLY `theorem_B_unique`'s hypotheses on every window `Icc 0 T`
    with `E := en (meanFree (coeff u₀))`, `Z := ens (meanFree (coeff u₀))`
    (`theorem_B_unique` consumes neither `RealField`, nor clause 6, nor the
    `κ` bound).  Uniqueness inside the community class in real-space
    vocabulary is a sized candidate (W3), not a delivered result.
    [Delivered as Tier 9c the same day: `community_unique_velocity`,
    `community_unique_pressure` in `TheoremB/CommunityUnique.lean`.]
  * `κ` is that of `theorem_B_community_periodic` (hence of
    `theorem_B_joint_smooth`), of explicit form and exported as a compiled
    existential; the `∃ κ` of each capstone is re-chosen by statement (the
    house pattern) and is that `κ` by proof.  No numeric value of any
    constant is claimed.
  * The constant datum `u₀ = m` (mean `m`, mean-free part `0`) satisfies the
    smallness hypothesis for every `ν' > 0` (indeed for every `ν' ≠ 0`; at
    `ν' = 0` it reads `0 < 0`) and is HANDLED by the Galilean change, not
    excluded; the rest state is the case `m = 0`
    (`capstone_fires_on_const_datum`).
  * The mean vector `meanVec (coeff u₀)` enters no hypothesis: for
    `u₀ = m + w` with `w` mean-free the hypothesis is the hypothesis on `w`,
    for every `m` (`capstone_hyp_shifted_iff`); the mean is SEEN by `coeff`
    (`meanVec_coeff_shifted_shear`), DISCARDED by the hypothesis, and removed
    by `galilean_class`; nothing else is said about it.
  * Junk values (rule 10 of the blueprint's section 7): `descend` and
    `coeff` are total; outside `InitialVelocityConditionPeriodic` they are
    well-typed junk, and the register carries the compiled failure of the
    inversion for the identity field (`inversion_fails_off_class`).  The
    capstone's class hypothesis is what makes `coeff u₀` meaningful.
  * Nothing here is new mathematics: the Fourier inversion of a smooth
    periodic function (Mathlib supplies the pointwise inversion for
    continuous functions with summable coefficients at the pin) and the
    Galilean invariance are textbook; the deliverable is the
    machine-checking.  Priority is not claimed for anything.  The
    machine-checked Navier-Stokes work this file sits beside is named in the
    announcement and the README (uda-lab/leray-hopf, HeliCorgi's
    ns-mns2-flowmap-bridge, Miller, OpenAI's forced-breakdown certificate,
    Alpöge and Buckmaster); none of it is composed with, reproduced by, or
    superseded by anything here.
  * PROPOSED announcement wording (rule 6 of the blueprint's section 7, Tier
    9 instance; the user's call; quoted here, not asserted)
    [Adopted by the user on 13 Sep 2026, commit dc3bd8f]: "for every datum
    in the community's own periodic initial-velocity condition whose
    mean-free coefficient part is small in the sense
    `κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀)) < (2πν')⁴`, OUR
    copy of the community's periodic solution class
    `NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` is inhabited
    (compiled); this is the conclusion of the upstream positive statement
    `navier_stokes_existence_and_smoothness_periodic` under that smallness
    hypothesis with `f = 0`; nothing about general data, nothing about the
    breakdown statement `navier_stokes_breakdown_periodic`; both upstream
    statements are untouched; existence only; the Fourier inversion and the
    Galilean invariance are textbook."
  * This file edits no earlier file of the tree and un-privates nothing: the
    tree's private `freq_zero` (ModesFlow), `conjVel_zero` (RealityProp) and
    `nf_dotR_zero_left` (NSFull) are CLONED here as the public lemmas
    `freq_zero`, `conjVel_zero`, `dotR_zero_left` (private names are
    module-mangled, so no clash; measured by the probe's compilation next to
    the imported tree); the private `W3Probe`
    pair-datum facts are reached only through the public
    `TimeConstantWitness` clones and re-cloned in `T9Probe`.  Every other
    declaration consumed here is public in its file (the consumed tree
    modules, measured by identifier grep at build time: CommunityClass,
    DatumBridge, Galilean, SobolevNorms, NSGalerkin, NSFull, PeriodicLift,
    SpectralNorms; and Mathlib).  The helper lemmas of D
    (`freq_zero`, `conjVel_zero`, `dotR_zero_left`, `meanFree_of_ne`,
    `norm_meanFree_le`, `uLift_zeroMode`, `conjVel_castCV`, `ens_zeroMode`,
    `en_zero`, `ens_zero`) and of E (listed above) are shipped public and
    carry no ledger line.

  DEVIATION FROM THE PROBE'S PREAMBLE (statement-neutral, recorded).
  The design probe declared the three torus measure instances anonymously;
  here they are NAMED `cd_ms`, `cd_haar`, `cd_prob` (Descent.lean uses
  `ds_*`, DatumBridge.lean `db_*`; the tree's torus files use `cr_*`,
  `tsyn_*`, `ts_*`, `ce_*`), because auto-named local instances from two
  modules collide in a third module that imports both.  The bodies are the
  three-line block of FourierDeriv.lean lines 31-37.  Instances are not
  statements; every frozen statement is byte-identical to the blueprint.
  Galilean.lean declares none (it elaborates no torus integral).

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
local instance cd_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance cd_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance cd_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## D1. The mean-free algebra (R5 section 4) -/

/-- The mean-free part of a coefficient family: the zero mode killed. -/
def meanFree (c : (Fin 3 → ℤ) → Vel) : (Fin 3 → ℤ) → Vel := fun k => if k = 0 then 0 else c k

/-- The real mean vector: the real part of the zero mode, packed into `ℝ³`. -/
def meanVec (c : (Fin 3 → ℤ) → Vel) : ℝ³ := WithLp.toLp 2 fun j => (c 0 j).re

lemma freq_zero : freq (0 : Fin 3 → ℤ) = 0 := by
  ext i; simp [freq]

lemma conjVel_zero : conjVel 0 = 0 := by
  ext j; simp [conjVel]

lemma dotR_zero_left (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

/-- The mean-free part has zero mode `0` (by definition; a `simp` lemma). -/
@[simp]
theorem meanFree_zero (c : (Fin 3 → ℤ) → Vel) : meanFree c 0 = 0 := by
  simp [meanFree]

lemma meanFree_of_ne {c : (Fin 3 → ℤ) → Vel} {k : Fin 3 → ℤ} (hk : k ≠ 0) :
    meanFree c k = c k := by
  simp [meanFree, hk]

/-- A mean-zero family is its own mean-free part. -/
theorem meanFree_of_mean_zero {c : (Fin 3 → ℤ) → Vel} (h : c 0 = 0) : meanFree c = c := by
  funext k
  by_cases hk : k = 0
  · subst hk; simp [meanFree, h]
  · simp [meanFree, hk]

lemma norm_meanFree_le (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) : ‖meanFree c k‖ ≤ ‖c k‖ := by
  by_cases hk : k = 0
  · subst hk; simp
  · rw [meanFree_of_ne hk]

/-- Reality passes to the mean-free part: off the zero mode the values are those of `c`,
and at the zero mode `0 = conjVel 0`. -/
theorem realField_meanFree {c : (Fin 3 → ℤ) → Vel} (h : RealField c) : RealField (meanFree c) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [conjVel_zero]
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    rw [meanFree_of_ne hnk, meanFree_of_ne hk, h k]

/-- Divergence-freeness passes to the mean-free part: at the zero mode `dotR 0 _ = 0`. -/
theorem divFree_meanFree {c : (Fin 3 → ℤ) → Vel} (h : DivFree c) : DivFree (meanFree c) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [dotR_zero_left]
  · rw [meanFree_of_ne hk]; exact h k

/-- Every Sobolev level passes to the mean-free part, by comparison
(`‖meanFree c k‖ ≤ ‖c k‖` termwise). -/
theorem summable_sob_meanFree {c : (Fin 3 → ℤ) → Vel}
    (h : ∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c l‖ ^ 2) :
    ∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖meanFree c l‖ ^ 2 := fun m =>
  (h m).of_nonneg_of_le (fun l => by positivity)
    (fun l => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_meanFree_le c l) 2) (by positivity))

/-- The enstrophy is insensitive to the mean: `freq 0 = 0` kills the zero mode in `ens`
(the smallness hypothesis of the capstone is nevertheless spelled on the mean-free part in
BOTH factors, D3 of the blueprint). -/
theorem ens_meanFree (c : (Fin 3 → ℤ) → Vel) : ens (meanFree c) = ens c := by
  unfold ens
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk; simp [freq_zero]
  · rw [meanFree_of_ne hk]

/-- The energy of the mean-free part is the energy less the squared zero mode
(`Summable.tsum_eq_add_tsum_ite` at `0`, under `classical`). -/
theorem en_meanFree {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖ ^ 2) :
    en (meanFree c) = en c - ‖c 0‖ ^ 2 := by
  classical
  unfold en
  rw [h.tsum_eq_add_tsum_ite 0]
  have hterm : ∀ k, ‖meanFree c k‖ ^ 2 = if k = 0 then 0 else ‖c k‖ ^ 2 := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp
    · simp [meanFree, hk]
  rw [tsum_congr hterm]
  ring

/-- The point split of the lift at the zero mode: for an ℓ¹ family the `j`-th lift is the
zero mode's `j`-th entry (the character at `0` is `1`) plus the lift of the mean-free
part. -/
theorem uLift_meanFree_add {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖) (j : Fin 3)
    (x : ℝ³) : uLift j c x = c 0 j + uLift j (meanFree c) x := by
  classical
  rw [uLift_eq_charSum_fiber, uLift_eq_charSum_fiber]
  have hs : Summable fun k => c k j * mFourier k (fiber x) :=
    Summable.of_norm_bounded h (fun k => by
      rw [norm_mul, norm_mFourier_apply, mul_one]; exact PiLp.norm_apply_le (c k) j)
  rw [hs.tsum_eq_add_tsum_ite 0, mFourier_zero, ContinuousMap.one_apply, mul_one]
  congr 1
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk; simp
  · simp [meanFree, hk]

/-- **The mean split of the real datum**: `u₀Real c = meanVec c + u₀Real (meanFree c)`. -/
theorem u₀Real_eq_meanVec_add {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖) (x : ℝ³) :
    u₀Real c x = meanVec c + u₀Real (meanFree c) x := by
  ext j
  simp only [u₀Real, meanVec, PiLp.add_apply, PiLp.toLp_apply]
  rw [uLift_meanFree_add h j x, Complex.add_re]

/-- The mean split of the real datum as a function equality,
`u₀Real c = fun x => meanVec c + u₀Real (meanFree c) x` (the form the capstone rewrites
with). -/
theorem u₀Real_eq_meanVec_add' {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖) :
    u₀Real c = fun x => meanVec c + u₀Real (meanFree c) x :=
  funext fun x => u₀Real_eq_meanVec_add h x

/-! ## D2. The zero-mode family: the constant datum on the coefficient side (R5 section 4b) -/

/-- The coefficient family carrying only the zero mode. -/
def zeroMode (m : ℝ³) : (Fin 3 → ℤ) → Vel := fun k => if k = 0 then castCV m else 0

lemma uLift_zeroMode (m : ℝ³) (j : Fin 3) (x : ℝ³) : uLift j (zeroMode m) x = (m j : ℂ) := by
  rw [uLift_eq_charSum_fiber, tsum_eq_single 0 (fun k hk => by simp [zeroMode, hk])]
  simp [zeroMode, mFourier_zero, castCV]

/-- The constant datum IS `u₀Real` of the zero-mode family. -/
theorem u₀Real_zeroMode (m : ℝ³) : u₀Real (zeroMode m) = fun _ => m := by
  funext x; ext j
  simp [u₀Real, uLift_zeroMode]

lemma conjVel_castCV (m : ℝ³) : conjVel (castCV m) = castCV m := by
  ext j; simp [conjVel, castCV]

/-- The zero-mode family of a real vector is real (`conjVel (castCV m) = castCV m`, and
`0 = conjVel 0` off the zero mode). -/
theorem realField_zeroMode (m : ℝ³) : RealField (zeroMode m) := by
  intro k
  by_cases hk : k = 0
  · subst hk; simp [zeroMode, conjVel_castCV]
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    simp [zeroMode, hk, hnk, conjVel_zero]

/-- The zero-mode family is ℓ¹ (a single nonzero term, `summable_of_ne_finset_zero` at
`{0}`). -/
theorem summable_norm_zeroMode (m : ℝ³) : Summable fun k => ‖zeroMode m k‖ :=
  summable_of_ne_finset_zero (s := {0}) fun k hk => by
    simp only [Finset.mem_singleton] at hk
    simp [zeroMode, hk]

lemma ens_zeroMode (m : ℝ³) : ens (zeroMode m) = 0 := by
  unfold ens
  rw [tsum_eq_single 0 (fun k hk => by simp [zeroMode, hk])]
  simp [freq_zero]

/-- The mean-free part of the zero-mode family is `0`. -/
theorem meanFree_zeroMode (m : ℝ³) : meanFree (zeroMode m) = 0 := by
  funext k
  by_cases hk : k = 0
  · subst hk; simp
  · simp [meanFree, zeroMode, hk]

/-- The mean vector of the zero-mode family is `m` (the real part of `castCV m`). -/
theorem meanVec_zeroMode (m : ℝ³) : meanVec (zeroMode m) = m := by
  ext j; simp [meanVec, zeroMode, castCV]

lemma en_zero : en (0 : (Fin 3 → ℤ) → Vel) = 0 := by simp [en]

lemma ens_zero : ens (0 : (Fin 3 → ℤ) → Vel) = 0 := by simp [ens]

/-- The zero-mode family meets EVERY hypothesis of `theorem_B_community_periodic` except
`c₀ 0 = 0`, and `c₀ 0 = 0 ↔ m = 0`: the mean-zero hypothesis is the ONLY thing that excludes
the constant datum on the coefficient side. -/
theorem zeroMode_meets_all_but_mean_zero (m : ℝ³) (κ : ℝ) {ν : ℝ} (hν : 0 < ν) :
    (∀ q : ℕ, Summable fun l => ‖freq l‖ ^ (2 * q) * ‖zeroMode m l‖ ^ 2) ∧
    RealField (zeroMode m) ∧ DivFree (zeroMode m) ∧
    κ * en (zeroMode m) * ens (zeroMode m) < ν ^ 4 ∧
    (zeroMode m 0 = 0 ↔ m = 0) := by
  refine ⟨fun q => ?_, realField_zeroMode m, fun k => ?_, ?_, ?_⟩
  · exact summable_of_ne_finset_zero (s := {0}) fun k hk => by
      simp only [Finset.mem_singleton] at hk
      simp [zeroMode, hk]
  · by_cases hk : k = 0
    · subst hk; simp [zeroMode, freq_zero, dotR]
    · simp [zeroMode, hk, dotR_zero_left]
  · rw [ens_zeroMode, mul_zero]; positivity
  · constructor
    · intro h
      ext j
      have := congrArg (fun v : Vel => (v j).re) h
      simpa [zeroMode, castCV] using this
    · intro h; subst h; ext j; simp [zeroMode, castCV]

/-! ## D3. THE CAPSTONE and its two siblings -/

/-- **THE CAPSTONE OF TIER 9**, in the community's own statement shape over REAL-SPACE data.

The upstream file carries the positive statement `navier_stokes_existence_and_smoothness_periodic`
and the breakdown statement `navier_stokes_breakdown_periodic`; this theorem is exactly the
positive statement's CONCLUSION, for `f = 0`, under a smallness hypothesis on the MEAN-FREE
part of the datum's coefficient field, `κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀))
< (2π ν')⁴` (both factors on the mean-free part; `ens` is insensitive to the mean, `ens_meanFree`).
The mean vector `meanVec (coeff u₀)` enters no hypothesis: for `u₀ = m + w` with `w` mean-free
the hypothesis is the hypothesis on `w`, for every `m` (register: `capstone_hyp_shifted_iff` for
the shear instance; the general compiled fact is `T9Probe.coeff_const_add` with `meanFree_add`
and `meanFree_zeroMode`);
the mean is removed by the Galilean change `galilean_class` and nothing else is said about it.
It says nothing about the positive statement for general data and nothing about the breakdown
statement; both upstream placeholder proofs are untouched.  Existence only: the class has no uniqueness
clause; uniqueness of the coefficient flow behind the witness is `theorem_B_unique`
(FullUnique.lean:327) through the sibling `theorem_B_community_periodic_data_flow`.

The constant datum `u₀ = m` (mean `m`, mean-free part `0`) satisfies the hypothesis for every
`ν' > 0` (indeed for every `ν' ≠ 0`; at `ν' = 0` it reads `0 < 0`) and is handled by the
Galilean change, not excluded; the rest state is the case `m = 0`.
`κ` is that of `theorem_B_community_periodic`, of explicit form and exported as a compiled
existential.  Nothing here is new mathematics: the Fourier inversion of a smooth periodic
function (Mathlib supplies the pointwise inversion for continuous functions with summable
coefficients at the pin) and the Galilean invariance of Navier-Stokes are textbook.

Proof: `datum_bridge` (W1) gives the coefficient field of `u₀`; its mean-free part is in the
trap class of `theorem_B_community_periodic`; the witness pair is boosted by the mean vector
through `galilean_class`; `u₀Real_eq_meanVec_add'` and the inversion identify the datum. -/
theorem theorem_B_community_periodic_data :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ →
      κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 →
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' u₀ hu₀ hsmall
  obtain ⟨hl1, hsob, hreal, hdiv, hinv⟩ := datum_bridge hu₀
  obtain ⟨-, -, v, p, hclass⟩ := H hν' (summable_sob_meanFree hsob) (meanFree_zero _)
    (realField_meanFree hreal) (divFree_meanFree hdiv) hsmall
  have hc0 : Summable fun k => ‖coeff u₀ k‖ := by simpa using hl1 0
  have hu := u₀Real_eq_meanVec_add' hc0
  rw [hinv] at hu
  refine ⟨galV (meanVec (coeff u₀)) v, galP (meanVec (coeff u₀)) p, ?_⟩
  have hg := galilean_class (meanVec (coeff u₀)) hclass
  rwa [← hu] at hg

/-- **The witness-exposing sibling**: the same conclusion with the witness pair made explicit,
`v = galV (meanVec (coeff u₀)) (vReal c)`, `p = galP (meanVec (coeff u₀)) (pReal c)`, for a
coefficient flow `c` at `ν := 2πν'` from the mean-free datum, carrying clauses 1 to 7 of
`theorem_B_community_periodic_flow` (clauses 1 to 6 line-identical to CommunityClass.lean:1621-1629
under the substitution `ν ↦ 2πν'`, `c₀ ↦ meanFree (coeff u₀)`; clause 7 identical up to a line
re-wrap, three lines here, two there).  The class carries no uniqueness clause; this sibling
delivers existence with an exhibited witness, not uniqueness in the class.  Clauses 1 to 7
supply the hypothesis set of `theorem_B_unique` (FullUnique.lean:327) on every window `Icc 0 T`
with `E := en (meanFree (coeff u₀))`, `Z := ens (meanFree (coeff u₀))` (`theorem_B_unique`
consumes neither `RealField`, nor clause 6, nor the `κ` bound), so that uniqueness of the
COEFFICIENT flow behind the witness can be cited.  As for the capstone: the upstream file carries
the positive statement `navier_stokes_existence_and_smoothness_periodic` and the breakdown
statement `navier_stokes_breakdown_periodic`; this is the positive statement's conclusion under
the smallness hypothesis on the mean-free part, with the witness exhibited; nothing about general
data, nothing about the breakdown statement; both upstream placeholder proofs are untouched. -/
theorem theorem_B_community_periodic_data_flow :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ →
      κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = meanFree (coeff u₀) ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = meanFree (coeff u₀) k + ∫ s in (0:ℝ)..t,
          ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en (meanFree (coeff u₀)) ∧
          ens (c t) ≤ ens (meanFree (coeff u₀)) ∧
          κ * en (c t) * ens (c t) < (2 * Real.pi * ν') ^ 4) ∧
        -- the member of the community class is the boosted real pair of THIS flow
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0)
          (galV (meanVec (coeff u₀)) (vReal c)) (galP (meanVec (coeff u₀)) (pReal c)) := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_flow
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' u₀ hu₀ hsmall
  obtain ⟨hl1, hsob, hreal, hdiv, hinv⟩ := datum_bridge hu₀
  have hν : 0 < 2 * Real.pi * ν' := by positivity
  obtain ⟨c, h1, h2, h3, h4, h5, h6, h7, -, -, -, -, -, -, -, -, -, -, -, -, -, hclass⟩ :=
    H hν (summable_sob_meanFree hsob) (meanFree_zero _) (realField_meanFree hreal)
      (divFree_meanFree hdiv) hsmall
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ h2π] at hclass
  have hc0 : Summable fun k => ‖coeff u₀ k‖ := by simpa using hl1 0
  have hu := u₀Real_eq_meanVec_add' hc0
  rw [hinv] at hu
  refine ⟨c, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  have hg := galilean_class (meanVec (coeff u₀)) hclass
  rwa [← hu] at hg

/-- **CONSISTENCY (MUST HOLD)**: the Tier 9 capstone specialises to the `∃ v p` of
`theorem_B_community_periodic` at `u₀ := u₀Real c₀` (the round trip `coeff (u₀Real c₀) = c₀`
and `meanFree c₀ = c₀` for a mean-zero family).  The STATEMENT is a projection of
`theorem_B_community_periodic` and holds from Tier 8b alone; the check is on the ROUTE, which
opens with `theorem_B_community_periodic_data` (reader probe
`ShapeW2.of_data_statement_from_8b_alone`, session directory `build-w2/reader-shape/`).  Same
scope as the capstone: the upstream positive statement
`navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
`navier_stokes_breakdown_periodic` are both untouched; existence only. -/
theorem theorem_B_community_periodic_of_data :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      κ * en c₀ * ens c₀ < (2 * Real.pi * ν') ^ 4 →
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real c₀) (f := 0) v p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_data
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' c₀ hsob h0 hreal hdiv hsmall
  have hc' : ∀ q : ℕ, Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ q * ‖c₀ k‖ := fun q =>
    summable_weighted_norm h0 (hsob (q + 2))
  have hc : Summable fun k => ‖c₀ k‖ := by simpa using hc' 0
  have hrt : coeff (u₀Real c₀) = c₀ := coeff_u₀Real hreal hc
  refine H hν' (initialVelocityConditionPeriodic_u₀Real hsob h0 hreal hdiv) ?_
  rw [hrt, meanFree_of_mean_zero h0]
  exact hsmall

/-! # E. Probe section of CommunityData.lean (non-frozen, registered): the register -/

namespace T9Probe

open TimeConstantWitness

/-- divergence of a constant field is `0`. -/
theorem divergence_const (m : ℝ³) (x : ℝ³) : Community.divergence (fun _ => m) x = 0 := by
  rw [divergence_eq_sum]
  simp [fderiv_const_apply]

/-- REGISTER: every constant datum `u₀ := m` meets `InitialVelocityConditionPeriodic`. -/
theorem const_datum_in_class (m : ℝ³) :
    InitialVelocityConditionPeriodic (n := 3) (fun _ => m) :=
  ⟨⟨fun x => divergence_const m x, contDiff_const⟩, fun _ _ => rfl⟩

/-- REGISTER: the constant pair is in the class at datum `m` for EVERY real `ν'`. -/
theorem const_pair_in_class (ν' : ℝ) (m : ℝ³) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0)
      (fun _ _ => m) (fun _ _ => 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x t _
    simp
  · intro x t _
    exact divergence_const m x
  · intro x; rfl
  · exact contDiffOn_const
  · exact contDiffOn_const
  · intro t _ x i; rfl
  · intro t _ x i; rfl

/-- REGISTER: the rest pair at the zero datum (Pi-zero spellings), every viscosity. -/
theorem rest_pair_in_class' (ν' : ℝ) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (0 : ℝ³ → ℝ³) (f := 0)
      (0 : ℝ³ → ℝ → ℝ³) (0 : ℝ³ → ℝ → ℝ) :=
  const_pair_in_class ν' 0

/-- The coefficient field of the constant datum is the zero-mode family. -/
theorem coeff_const (m : ℝ³) : coeff (fun _ => m) = zeroMode m := by
  rw [← u₀Real_zeroMode m]
  exact coeff_u₀Real (realField_zeroMode m) (summable_norm_zeroMode m)

/-- REGISTER (constant datum): the capstone's smallness hypothesis holds for EVERY constant
datum and EVERY `ν' > 0` and every `κ` (mean-free part `0`). -/
theorem capstone_hyp_const_datum (m : ℝ³) (κ : ℝ) {ν' : ℝ} (hν' : 0 < ν') :
    κ * en (meanFree (coeff (fun _ => m))) * ens (meanFree (coeff (fun _ => m)))
      < (2 * Real.pi * ν') ^ 4 := by
  rw [coeff_const, meanFree_zeroMode, en_zero, mul_zero, zero_mul]
  positivity

/-- REGISTER (constant datum): the capstone FIRES on the constant datum (handled by the boost,
not excluded); at `m = 0` this is the rest state. -/
theorem capstone_fires_on_const_datum (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p := by
  obtain ⟨κ, -, H⟩ := theorem_B_community_periodic_data
  exact H hν' (const_datum_in_class m) (capstone_hyp_const_datum m κ hν')

/-! ### The shear datum (public clones of the private W3Probe pair-datum facts, R5) -/

lemma zero_notMem_ccBox : (0 : Fin 3 → ℤ) ∉ ccBox := by
  simp only [ccBox, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · intro h; have := congrFun h 0; simp [ccpe1] at this
  · intro h; have := congrFun h 0; simp [ccpe1] at this

lemma ccPair_zero_mode (v : Vel) : ccPair v 0 = 0 := ccPair_eq_zero zero_notMem_ccBox

lemma ccBox_symm : ∀ k ∈ ccBox, -k ∈ ccBox := by
  intro k hk
  simp only [ccBox, Finset.mem_insert, Finset.mem_singleton] at hk ⊢
  rcases hk with rfl | rfl
  · right; rfl
  · left; exact neg_neg _

lemma conjVel_ccVec (r : ℝ) : conjVel (ccVec r) = ccVec r := by
  ext j
  simp only [conjVel, PiLp.toLp_apply, ccVec_apply]
  split_ifs <;> simp

lemma realField_ccPair_ccVec (r : ℝ) : RealField (ccPair (ccVec r)) := by
  intro k
  by_cases hk : k ∈ ccBox
  · have hnk : -k ∈ ccBox := ccBox_symm k hk
    simp only [ccBox, Finset.mem_insert, Finset.mem_singleton] at hk hnk
    simp only [ccPair]
    rw [if_pos hnk, if_pos hk, conjVel_ccVec]
  · have hnk : -k ∉ ccBox := fun h => hk (by simpa using ccBox_symm (-k) h)
    rw [ccPair_eq_zero hk, ccPair_eq_zero hnk, conjVel_zero]

lemma dotR_ccVec_ccpe1 (r : ℝ) : dotR (ccVec r) (freq ccpe1) = 0 := by
  simp [dotR, ccVec, freq, ccpe1]

lemma dotR_ccVec_neg_ccpe1 (r : ℝ) : dotR (ccVec r) (freq (-ccpe1)) = 0 := by
  simp [dotR, ccVec, freq, ccpe1]

lemma divFree_ccPair_ccVec (r : ℝ) : DivFree (ccPair (ccVec r)) := by
  intro k
  by_cases hk : k ∈ ccBox
  · simp only [ccBox, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [ccPair]
    rw [if_pos hk]
    rcases hk with rfl | rfl
    · exact dotR_ccVec_ccpe1 r
    · exact dotR_ccVec_neg_ccpe1 r
  · rw [ccPair_eq_zero hk]; simp [dotR]

lemma summable_wsq_ccPair (v : Vel) (m : ℕ) :
    Summable fun l => ‖freq l‖ ^ (2 * m) * ‖ccPair v l‖ ^ 2 :=
  summable_of_ne_finset_zero (s := ccBox) fun k hk => by rw [ccPair_eq_zero hk]; simp

lemma summable_norm_ccPair (v : Vel) : Summable fun l => ‖ccPair v l‖ :=
  summable_of_ne_finset_zero (s := ccBox) fun k hk => by rw [ccPair_eq_zero hk]; simp

lemma pair_tsum_sq (w : (Fin 3 → ℤ) → ℝ) (v : Vel) :
    ∑' k, w k * ‖ccPair v k‖ ^ 2 = (w ccpe1 + w (-ccpe1)) * ‖v‖ ^ 2 := by
  have hsupp : ∀ k ∉ ccBox, w k * ‖ccPair v k‖ ^ 2 = 0 := by
    intro k hk; simp [ccPair_eq_zero hk]
  rw [tsum_eq_sum hsupp]
  simp only [ccBox]
  rw [Finset.sum_pair ccpe1_ne_neg]
  simp [ccPair, ccpe1_ne_neg, ccpe1_ne_neg.symm]
  ring

lemma en_ccPair (v : Vel) : en (ccPair v) = 2 * ‖v‖ ^ 2 := by
  have h := pair_tsum_sq (fun _ => 1) v
  simp only [one_mul] at h
  show ∑' k, ‖ccPair v k‖ ^ 2 = _
  rw [h]; ring

lemma ens_ccPair (v : Vel) : ens (ccPair v) = 2 * ‖v‖ ^ 2 := by
  have h := pair_tsum_sq (fun k => ‖freq k‖ ^ 2) v
  show ∑' k, ‖freq k‖ ^ 2 * ‖ccPair v k‖ ^ 2 = _
  rw [h, norm_freq_ccpe1, norm_freq_neg_ccpe1]
  norm_num

lemma norm_ccVec (r : ℝ) : ‖ccVec r‖ = |r| := by
  rw [ccVec, PiLp.norm_single, Complex.norm_real, Real.norm_eq_abs]

/-- REGISTER: the shear datum's real lift is in the class, for EVERY `ε`. -/
theorem testDatum_in_class (ε : ℝ) :
    InitialVelocityConditionPeriodic (n := 3) (u₀Real (W3Probe.testDatum ε)) := by
  rw [testDatum_eq]
  exact initialVelocityConditionPeriodic_u₀Real (summable_wsq_ccPair _) (ccPair_zero_mode _)
    (realField_ccPair_ccVec ε) (divFree_ccPair_ccVec ε)

/-- The round trip on the shear datum (the coefficient field of the real shear is the shear). -/
theorem coeff_testDatum (ε : ℝ) : coeff (u₀Real (W3Probe.testDatum ε)) = W3Probe.testDatum ε := by
  rw [testDatum_eq]
  exact coeff_u₀Real (realField_ccPair_ccVec ε) (summable_norm_ccPair _)

/-- REGISTER (shear datum): for every `κ, ν' > 0` there is a NONZERO `ε` for which the real
shear datum satisfies the capstone's smallness hypothesis. -/
theorem capstone_hyp_testDatum {κ ν' : ℝ} (hκ : 0 < κ) (hν' : 0 < ν') :
    ∃ ε : ℝ, ε ≠ 0 ∧
      κ * en (meanFree (coeff (u₀Real (W3Probe.testDatum ε)))) *
        ens (meanFree (coeff (u₀Real (W3Probe.testDatum ε)))) < (2 * Real.pi * ν') ^ 4 := by
  set ν : ℝ := 2 * Real.pi * ν' with hνdef
  have hν : 0 < ν := by positivity
  set r : ℝ := ν / (κ + 3) with hr
  have hrpos : 0 < r := by positivity
  refine ⟨r, hrpos.ne', ?_⟩
  rw [coeff_testDatum, testDatum_eq, meanFree_of_mean_zero (ccPair_zero_mode _), en_ccPair,
    ens_ccPair, norm_ccVec, sq_abs]
  have h1 : 4 * κ < (κ + 3) ^ 2 := by nlinarith [sq_nonneg (κ - 1)]
  have h2 : (κ + 3) ^ 2 ≤ (κ + 3) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hν4 : 0 < ν ^ 4 := by positivity
  have hkey : κ * (2 * r ^ 2) * (2 * r ^ 2) = 4 * κ * ν ^ 4 / (κ + 3) ^ 4 := by
    rw [hr]; field_simp; ring
  rw [hkey, div_lt_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2) hν4]

/-- REGISTER (MUST FIRE, NON-TRIVIALLY): for every `ν' > 0` there is a NONZERO shear datum
in the class on which the capstone fires AND on which both trivial candidates (`v := 0`,
`v := u₀` time-constant) fail for every pressure. -/
theorem capstone_fires_on_testDatum {ν' : ℝ} (hν' : 0 < ν') :
    ∃ ε : ℝ, ε ≠ 0 ∧
      u₀Real (W3Probe.testDatum ε) ≠ 0 ∧
      (∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
          (f := 0) v p) ∧
      ∀ p : ℝ³ → ℝ → ℝ,
        ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
            (f := 0) (fun _ _ => 0) p ∧
        ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
            (f := 0) (fun x _ => u₀Real (W3Probe.testDatum ε) x) p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_data
  obtain ⟨ε, hε, hsmall⟩ := capstone_hyp_testDatum hκ hν'
  refine ⟨ε, hε, W3Probe.u₀Real_testDatum_ne_zero hε, H hν' (testDatum_in_class ε) hsmall,
    fun p => ⟨W4Probe.rest_state_not_witness_for_nonzero hε ν' p,
      TimeConstantWitness.const_witness_fails hε hν'.ne' p⟩⟩

/-- REGISTER (junk value): `coeff` of a NON-periodic field is a well-typed junk object and the
inversion FAILS for it: `u₀Real (coeff u)` is always one-periodic, `u := id` is not.  The
capstone's `InitialVelocityConditionPeriodic` hypothesis is what makes `coeff u₀` meaningful. -/
theorem inversion_fails_off_class : u₀Real (coeff (fun x : ℝ³ => x)) ≠ fun x => x := by
  intro h
  have h1 := isOnePeriodic_u₀Real (coeff (fun x : ℝ³ => x)) 0 0
  rw [h] at h1
  have h2 := congrArg (fun v : ℝ³ => v 0) h1
  simp at h2

/-! ### RC5 (statement-shape critique): non-constancy, restrictiveness, and the mean does not
enter (critique/shape/ShapeCritic_section.lean, compiled in ShapeProbe.lean pass 2, exit 0) -/

lemma ccpe1_ne_zero : ccpe1 ≠ (0 : Fin 3 → ℤ) := by
  intro h0
  have := congrFun h0 0
  simp [ccpe1] at this

lemma testDatum_ccpe1 (ε : ℝ) : W3Probe.testDatum ε ccpe1 = ccVec ε := by
  rw [testDatum_eq]
  simp [ccPair]

lemma ccVec_ne_zero {ε : ℝ} (hε : ε ≠ 0) : ccVec ε ≠ 0 := by
  intro h
  have := congrArg (fun v : Vel => v 1) h
  simp [ccVec_apply] at this
  exact hε this

/-- REGISTER (non-constancy): the shear datum is NOT constant: if it were `fun _ => m`, the
round trip would force `testDatum ε = zeroMode m`, which fails at the mode `ccpe1`. -/
theorem shear_not_const {ε : ℝ} (hε : ε ≠ 0) (m : ℝ³) :
    u₀Real (W3Probe.testDatum ε) ≠ fun _ => m := by
  intro h
  have h1 : coeff (u₀Real (W3Probe.testDatum ε)) = zeroMode m := by
    rw [h]; exact coeff_const m
  rw [coeff_testDatum] at h1
  have h2 := congrFun h1 ccpe1
  rw [testDatum_ccpe1] at h2
  simp only [zeroMode, if_neg ccpe1_ne_zero] at h2
  exact ccVec_ne_zero hε h2

/-- REGISTER (the hypothesis is restrictive): for every `κ > 0`, `ν' > 0` there is a datum in
`InitialVelocityConditionPeriodic` that FAILS the smallness hypothesis (a large shear), so the
capstone is not a statement about all data in the class. -/
theorem capstone_hyp_not_universal {κ ν' : ℝ} (hκ : 0 < κ) (hν' : 0 < ν') :
    ∃ u₀ : ℝ³ → ℝ³, InitialVelocityConditionPeriodic (n := 3) u₀ ∧
      ¬ (κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4) := by
  set ν : ℝ := 2 * Real.pi * ν' with hνdef
  have hνpos : 0 < ν := by positivity
  set t : ℝ := 1 / κ with ht
  have htpos : 0 < t := by positivity
  have hκt : κ * t = 1 := by rw [ht]; exact mul_one_div_cancel hκ.ne'
  set ε : ℝ := ν * (1 + t) with hε
  refine ⟨u₀Real (W3Probe.testDatum ε), testDatum_in_class ε, ?_⟩
  rw [coeff_testDatum, testDatum_eq, meanFree_of_mean_zero (ccPair_zero_mode _), en_ccPair,
    ens_ccPair, norm_ccVec, sq_abs]
  push Not
  have h1 : 4 * t ≤ (1 + t) ^ 4 := by
    nlinarith [sq_nonneg t, pow_nonneg htpos.le 3, pow_nonneg htpos.le 4, mul_pos htpos htpos]
  have hν4 : 0 < ν ^ 4 := by positivity
  have hε4 : ε ^ 4 = ν ^ 4 * (1 + t) ^ 4 := by rw [hε, mul_pow]
  have hA : 4 * κ * ν ^ 4 * (4 * t) = 16 * ν ^ 4 := by
    have : 4 * κ * ν ^ 4 * (4 * t) = 16 * ν ^ 4 * (κ * t) := by ring
    rw [this, hκt, mul_one]
  calc ν ^ 4 ≤ 16 * ν ^ 4 := by linarith
    _ = 4 * κ * ν ^ 4 * (4 * t) := hA.symm
    _ ≤ 4 * κ * ν ^ 4 * (1 + t) ^ 4 := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = κ * (2 * ε ^ 2) * (2 * ε ^ 2) := by
        rw [show κ * (2 * ε ^ 2) * (2 * ε ^ 2) = 4 * κ * ε ^ 4 by ring, hε4]; ring

theorem meanFree_add (c d : (Fin 3 → ℤ) → Vel) : meanFree (c + d) = meanFree c + meanFree d := by
  funext k
  by_cases hk : k = 0 <;> simp [meanFree, hk]

theorem meanVec_add (c d : (Fin 3 → ℤ) → Vel) : meanVec (c + d) = meanVec c + meanVec d := by
  ext j
  simp [meanVec, Complex.add_re]

theorem meanVec_of_mean_zero {d : (Fin 3 → ℤ) → Vel} (h : d 0 = 0) : meanVec d = 0 := by
  ext j
  simp [meanVec, h]

theorem realField_add {c d : (Fin 3 → ℤ) → Vel} (hc : RealField c) (hd : RealField d) :
    RealField (c + d) := by
  intro k
  simp only [Pi.add_apply, hc k, hd k]
  ext j
  simp [conjVel]

/-- The coefficient field of `m + u₀Real d` for a real, ℓ¹, mean-zero `d` is `zeroMode m + d`:
the mean IS seen by `coeff`. -/
theorem coeff_const_add {m : ℝ³} {d : (Fin 3 → ℤ) → Vel} (hreal : RealField d)
    (hs : Summable fun k => ‖d k‖) (h0 : d 0 = 0) :
    coeff (fun x => m + u₀Real d x) = zeroMode m + d := by
  have hsum : Summable fun k => ‖(zeroMode m + d) k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_add_le _ _)
      ((summable_norm_zeroMode m).add hs)
  have hmv : meanVec (zeroMode m + d) = m := by
    rw [meanVec_add, meanVec_zeroMode, meanVec_of_mean_zero h0, add_zero]
  have hmf : meanFree (zeroMode m + d) = d := by
    rw [meanFree_add, meanFree_zeroMode, meanFree_of_mean_zero h0, zero_add]
  have hu : u₀Real (zeroMode m + d) = fun x => m + u₀Real d x := by
    rw [u₀Real_eq_meanVec_add' hsum, hmv, hmf]
  rw [← hu]
  exact coeff_u₀Real (realField_add (realField_zeroMode m) hreal) hsum

lemma testDatum_real (ε : ℝ) : RealField (W3Probe.testDatum ε) := by
  rw [testDatum_eq]; exact realField_ccPair_ccVec ε

lemma testDatum_summable (ε : ℝ) : Summable fun k => ‖W3Probe.testDatum ε k‖ := by
  rw [testDatum_eq]; exact summable_norm_ccPair _

lemma testDatum_zero_mode (ε : ℝ) : W3Probe.testDatum ε 0 = 0 := by
  rw [testDatum_eq]; exact ccPair_zero_mode _

/-- THE MEAN DOES NOT ENTER: for `u₀ = m + shear` both factors of the smallness hypothesis are
those of the shear itself, for EVERY `m`. -/
theorem smallness_factors_shift_invariant (m : ℝ³) (ε : ℝ) :
    en (meanFree (coeff (fun x => m + u₀Real (W3Probe.testDatum ε) x)))
        = en (W3Probe.testDatum ε) ∧
    ens (meanFree (coeff (fun x => m + u₀Real (W3Probe.testDatum ε) x)))
        = ens (W3Probe.testDatum ε) := by
  rw [coeff_const_add (testDatum_real ε) (testDatum_summable ε) (testDatum_zero_mode ε),
    meanFree_add, meanFree_zeroMode, meanFree_of_mean_zero (testDatum_zero_mode ε), zero_add]
  exact ⟨rfl, rfl⟩

/-- ... while the mean vector of `m + shear` is `m`: the mean is SEEN by `coeff` and DISCARDED
by the hypothesis. -/
theorem meanVec_coeff_shifted_shear (m : ℝ³) (ε : ℝ) :
    meanVec (coeff (fun x => m + u₀Real (W3Probe.testDatum ε) x)) = m := by
  rw [coeff_const_add (testDatum_real ε) (testDatum_summable ε) (testDatum_zero_mode ε),
    meanVec_add, meanVec_zeroMode, meanVec_of_mean_zero (testDatum_zero_mode ε), add_zero]

/-- REGISTER (the mean enters no hypothesis): the smallness hypothesis for `m + shear` is
LITERALLY the hypothesis for the shear, for every `m`. -/
theorem capstone_hyp_shifted_iff (m : ℝ³) (ε κ ν' : ℝ) :
    (κ * en (meanFree (coeff (fun x => m + u₀Real (W3Probe.testDatum ε) x))) *
        ens (meanFree (coeff (fun x => m + u₀Real (W3Probe.testDatum ε) x)))
        < (2 * Real.pi * ν') ^ 4) ↔
    (κ * en (W3Probe.testDatum ε) * ens (W3Probe.testDatum ε) < (2 * Real.pi * ν') ^ 4) := by
  rw [(smallness_factors_shift_invariant m ε).1, (smallness_factors_shift_invariant m ε).2]

/-- REGISTER (helper): adding a constant keeps a datum in the class. -/
theorem ivc_const_add {u : ℝ³ → ℝ³} (m : ℝ³) (hu : InitialVelocityConditionPeriodic (n := 3) u) :
    InitialVelocityConditionPeriodic (n := 3) (fun x => m + u x) :=
  ⟨⟨fun x => by rw [divergence_const_add]; exact hu.div_free x, contDiff_const.add hu.smooth⟩,
    fun x i => by
      show m + u (x + EuclideanSpace.single i 1) = m + u x
      rw [hu.isOnePeriodic x i]⟩

/-- NO time-constant velocity is a witness for the shear datum: the class's `initial_condition`
forces `w = u₀`, then `const_witness_fails`. -/
theorem no_time_constant_witness_on_shear {ε : ℝ} (hε : ε ≠ 0) {ν' : ℝ} (hν' : 0 < ν')
    (w : ℝ³ → ℝ³) (p : ℝ³ → ℝ → ℝ) :
    ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
        (f := 0) (fun x _ => w x) p := by
  intro hc
  have hw : w = u₀Real (W3Probe.testDatum ε) := funext fun x => hc.initial_condition x
  subst hw
  exact TimeConstantWitness.const_witness_fails hε hν'.ne' p hc

/-- REGISTER (MUST FIRE on every mean): the capstone fires on `m + shear` for EVERY mean `m`
(the proof takes the shear's own `ε`; that the same `ε` works is `capstone_hyp_shifted_iff`),
and the constant drift `v := m` is not the witness. -/
theorem capstone_fires_on_shifted_shear (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    ∃ ε : ℝ, ε ≠ 0 ∧
      (∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν'
          (fun x => m + u₀Real (W3Probe.testDatum ε) x) (f := 0) v p) ∧
      ∀ p : ℝ³ → ℝ → ℝ, ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν'
          (fun x => m + u₀Real (W3Probe.testDatum ε) x) (f := 0) (fun _ _ => m) p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_data
  obtain ⟨ε, hε, hsmall⟩ := capstone_hyp_testDatum hκ hν'
  refine ⟨ε, hε, H hν' (ivc_const_add m (testDatum_in_class ε)) ?_, fun p hc => ?_⟩
  · rw [capstone_hyp_shifted_iff]
    rw [coeff_testDatum, meanFree_of_mean_zero (testDatum_zero_mode ε)] at hsmall
    exact hsmall
  · apply W3Probe.u₀Real_testDatum_ne_zero hε
    funext x
    have h : m = m + u₀Real (W3Probe.testDatum ε) x := hc.initial_condition x
    have h' : u₀Real (W3Probe.testDatum ε) x = 0 := by
      have := congrArg (fun y : ℝ³ => y - m) h
      simpa using this.symm
    simpa using h'

end T9Probe

end

end TheoremB
