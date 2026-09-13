/-
  TheoremB/GeneralMean.lean
  Tier 9c, post-tag addendum W3d (Theorem B campaign, 13 Sep 2026): the general-mean consistency
  identity for the coefficient flow of a Galilean-boosted real pair, its Tier 9 instance on a datum
  of arbitrary mean, its constant-datum instance, and the smallness sibling of the Tier 9 existence
  capstone.  Transcribed from the probe `audit-tier9c/w3d/probe/ReconW3d.lean` (session directory,
  never a tracked file; compiled there at the pin by the probe agent and recompiled by the
  orchestrator: exit 0, 0 errors, no declaration with a placeholder proof, 19 of 19 `#print axioms`
  lines on `[propext, Classical.choice, Quot.sound]`); the 19 statements are those of
  `context/rung12-tier9c-blueprint.md` section 9 (the W3d block), byte-identical, and the proofs are
  the probe's.  Decisions D20 to D27 of that section govern this file.

  WHAT IS DELIVERED HERE.
  * The phase lemma `mFourierCoeff_descend_translate`: for a one-periodic `f : ℝ³ → ℂ` and a shift
    `a : ℝ³`, the coefficient of the descent of the translate `x ↦ f (x - a)` is the phase
    `mFourier (-k) (fiber a)` times the coefficient of the descent of `f`.  NO continuity
    hypothesis: Mathlib's `integral_add_right_eq_self` (the translation invariance of the torus
    Haar measure, whose instances `Pi.isAddLeftInvariant_volume` and
    `IsAddLeftInvariant.isAddRightInvariant` are found by instance search under the three named
    local instances below) carries none, so only periodicity is consumed; then
    `descend_translate_add` and `mFourier_apply_add` pointwise and `integral_const_mul`.  Its
    evaluated form `mFourier_neg_fiber` (`mFourier (-k) (fiber a) = exp (-(2πi Σᵢ kᵢ aᵢ))`,
    Mathlib's `fourier_coe_apply` coordinatewise and `Complex.exp_sum`) and the combined form
    `mFourierCoeff_descend_translate_exp`.  The five helpers `fiber_add`, `fiber_sub`,
    `eq_of_fiber_eq`, `descend_translate_add`, `mFourier_apply_add` are shipped public and carry
    no ledger line.  The phase of a translated function's coefficients is textbook bookkeeping.
  * THE GENERAL-MEAN CONSISTENCY IDENTITY `classFlow_galV_vReal`: for a coefficient flow
    `c : ℝ → (Fin 3 → ℤ) → Vel` that is real (`RealField (c t)`) and ℓ¹ (`Summable fun k => ‖c t k‖`)
    at the campaign time `t ≥ 0`, and ANY mean `m : ℝ³`,
    `classFlow (galV m (vReal c)) t k = zeroMode m k + mFourier (-k) (fiber ((t / (2π)) • m)) • c t k`:
    the coefficient flow of the boosted real pair is the zero mode `m` plus the phase-shifted flow.
    Route: `classFlow_apply`, the boost unfolded (`galV`, `vReal`, `u₀Real`, the clock
    `2π · (t / 2π) = t` by `mul_div_cancel₀`), ClassFlowODE.lean's `coeff_add` on the constant and
    the translate (the continuity of the real datum from `continuous_u₀Real`, PeriodicLift.lean's
    `contDiff_uLift` at order `0`; the periodicity from DatumBridge.lean's `isOnePeriodic_u₀Real`
    through `isOnePeriodic_translate`), CommunityData.lean's `T9Probe.coeff_const`, the phase lemma
    componentwise on the complexified components, and the round trip `coeff_u₀Real`.  Its
    campaign-clock exponential form `classFlow_galV_vReal_exp` (the phase
    `exp (-(i t Σᵢ kᵢ mᵢ))`; the class-clock phase `e^{-2πi (k·m) τ}` at `t = 2πτ`).  The two
    helpers `continuous_u₀Real`, `isOnePeriodic_translate` are shipped public and carry no ledger
    line.  The Galilean boost's effect on the modes (the mode `k` multiplied by the phase, the zero
    mode shifted by the mean) is textbook bookkeeping.
  * The Tier 9 instance on a datum of ARBITRARY mean,
    `T9cProbe.flow_witness_classFlow_eq_general_mean`: for every `0 < ν'` and every datum `u₀` in
    the community's own `InitialVelocityConditionPeriodic` whose mean-free coefficient part is small
    in the sense `κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀)) < (2πν')⁴`, the flow `c`
    re-obtained from CommunityClass.lean's `theorem_B_community_periodic_flow` at `ν := 2πν'` from
    the mean-free datum (the `obtain` pattern of CommunityData.lean's
    `theorem_B_community_periodic_data_flow`, keeping clause 2, reality and divergence-freeness, and
    clause 10 at `p = 0`, the ℓ¹ clause) starts at `meanFree (coeff u₀)`, is real, divergence-free
    and ℓ¹ at every `t ≥ 0`, its boosted real pair
    `(galV (meanVec (coeff u₀)) (vReal c), galP (meanVec (coeff u₀)) (pReal c))` is a member of OUR
    COPY of the class at `f = 0`, and the member's coefficient flow is `zeroMode (meanVec (coeff u₀))`
    plus the phase-shifted `c` at every `t ≥ 0` and every mode.  The `∃ κ` is that of
    `theorem_B_community_periodic_flow` (`κ` of explicit form, exported as a compiled existential; no
    numeric value of any constant is claimed anywhere in this file).  When the mean vanishes (`coeff u₀ 0 = 0`) the phase is `1` and
    the zero mode `0`, and the identity reduces to the shape of the W3c register item
    `T9cProbe.flow_witness_classFlow_eq` (`T9cProbe.general_mean_identity_mean_free`, through the
    two helpers `fiber_zero`, `zeroMode_zero`, shipped public with no ledger line).
  * The constant-datum instance `T9cProbe.general_mean_const_datum`: on `u₀ = fun _ => m` the
    instance exhibits a flow `c` with `c 0 = 0` whose boosted pair is a member of OUR COPY of the
    class at `f = 0` and `0 < ν'`, whose coefficient flow is `zeroMode m` at every `t ≥ 0` (the
    member's velocity is the constant `m` by CommunityUnique.lean's `const_datum_member_is_const`,
    E6, a consequence of the velocity capstone: uniqueness inside OUR COPY of the community class at
    `f = 0`, for the same datum and `0 < ν'`), and whose flow is the zero flow on `t ≥ 0`: the flow
    from the zero datum is identified as the zero flow through the identity's right side, the phase
    being a unit (PeriodicLift.lean's `norm_mFourier_apply`).
  * The smallness sibling `theorem_B_community_periodic_data_ens`: the Tier 9 existence capstone
    `theorem_B_community_periodic_data` (CommunityData.lean) with the enstrophy factor spelled on the
    full coefficient field, `κ · en (meanFree (coeff u₀)) · ens (coeff u₀) < (2πν')⁴`, obtained by
    one `rw [ens_meanFree]` through the equivalence `smallness_ens_iff` (`ens` is insensitive to the
    mean, CommunityData.lean's `ens_meanFree`; `en` is not, `en_meanFree`).  Same scope as the
    capstone: existence only, for every `0 < ν'`, `f = 0`, OUR COPY of the class, the datum in the
    community's own `InitialVelocityConditionPeriodic`; the smallness hypothesis stays a hypothesis
    on the mean-free part of the datum's coefficient field in the `en` factor, and the mixed spelling
    must not be read as the mean entering the threshold.  The D3 spelling of the capstone (on the
    mean-free part in both factors) stays the primary one (D24); this sibling exists for citation
    convenience.

  HONEST SCOPE (binding wording, section 7 of the blueprint, rules 1 to 14).
  * What this file is: consistency bookkeeping for the Tier 9 witness under a general mean, its
    constant-datum instance, and a citation convenience.  It delivers NO new uniqueness statement:
    the two uniqueness capstones of the tree stay CommunityUnique.lean's `community_unique_velocity`
    and `community_unique_pressure` (uniqueness inside OUR COPY of the community class at `f = 0`,
    for the same datum and `0 < ν'`; the velocity at every point and every `t ≥ 0`, the pressure
    unique up to a function of time), consumed here only through `const_datum_member_is_const`; no
    statement here is about `ν' ≤ 0`, forced data (`f ≠ 0`), general data beyond the smallness
    hypothesis, or competitors outside the class.
  * What it supersedes: the sentence of the blueprint's D12 (section 1b) and of the
    CommunityUnique.lean header (E7, item 8) that the general-mean identity is "NOT compiled and NOT
    claimed" is superseded by this file (D22): the identity is compiled here, with the phase
    `mFourier (-k) (fiber ((t / (2π)) • m))` and the zero mode `zeroMode m k`; the D12 text is kept
    where it stands (built files are not edited for prose).
  * Textbook, not new: the phase of a translated function's coefficients, the Galilean boost's
    effect on the modes and the mean spelling of the smallness hypothesis are textbook bookkeeping;
    nothing here is new mathematics; the deliverable is the machine-checking.  Priority is not
    claimed for anything.
  * The class is the community's own `NavierStokesExistenceAndSmoothnessPeriodic`, copied in
    CommunityClass.lean from the repository google-deepmind/formal-conjectures (D27: the copy is
    byte-identical to the fetched file with comments stripped, up to the namespace and the divergence
    notation); the upstream file carries the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement
    `navier_stokes_breakdown_periodic`; both upstream placeholder proofs are untouched; the sibling
    is, like the Tier 9 capstone, the conclusion of the positive statement under the smallness
    hypothesis with `f = 0`, existence only.
  * Junk values (rule 10): `coeff`, `u₀Real`, `descend` and `classFlow` are total; outside the
    stated hypotheses they are well-typed junk objects.  The identity carries the two hypotheses it
    needs (reality and ℓ¹ at the time `t`), the phase lemma carries periodicity, and the instance
    carries membership; nothing is said of `classFlow v` for a general `v`.
  * Consumed tree files, measured by identifier grep of the code (docstrings stripped):
    CommunityUnique (`const_datum_member_is_const`; the import, through which everything below is
    reached), ClassFlowODE (`classFlow`, `classFlow_apply`, `coeff_add`), CommunityClass
    (`NavierStokesExistenceAndSmoothnessPeriodic`, `InitialVelocityConditionPeriodic`,
    `IsOnePeriodic`, `fiber`, `u₀Real`, `vReal`, `pReal`, `theorem_B_community_periodic_flow`),
    CommunityData (`meanFree`, `meanVec`, `zeroMode`, `meanFree_zero`, `meanFree_zeroMode`,
    `meanVec_zeroMode`, `ens_meanFree`, `summable_sob_meanFree`, `realField_meanFree`,
    `divFree_meanFree`, `u₀Real_eq_meanVec_add'`, `theorem_B_community_periodic_data`, and the
    Tier 9 register `T9Probe`'s `coeff_const`, `meanVec_of_mean_zero`, `const_datum_in_class`,
    `capstone_hyp_const_datum`), DatumBridge (`coeff`, `coeff_apply`, `coeff_u₀Real`,
    `datum_bridge`, `isOnePeriodic_u₀Real`, `isOnePeriodic_ofReal_component`), Descent (`descend`,
    `descend_fiber`, `fiber_rep`, `rep`), Galilean (`galV`, `galP`, `galilean_class`), NSGalerkin
    (`Vel`, `RealField`, `DivFree`, `castCV`), PeriodicLift (`uLift`, `contDiff_uLift`,
    `norm_mFourier_apply`), SpectralNorms (`en`, `ens`), and Mathlib (`mFourier`, `mFourierCoeff`,
    `fourier_apply`, `fourier_coe_apply`, `integral_add_right_eq_self`, `integral_const_mul`,
    `contDiff_euclidean`, `Complex.exp_sum`, the `AddCircle` and `Circle` coercion lemmas,
    `PiLp.ext`).  `theorem_B_community_periodic_data_flow` (CommunityData) and the W3c register
    item `T9cProbe.flow_witness_classFlow_eq` are mirrored in shape, not consumed.  This file edits
    no earlier file of the tree and clones no private lemma: every declaration consumed here is
    public in its file.  The 9 helpers carry no ledger line; the 10 registered theorems carry one
    each, entries 475 to 484 of the gate's 484 (`TheoremB.<name>` for the seven in `TheoremB`,
    `TheoremB.T9cProbe.<name>` for the three register items, in the D21 order).

  DEVIATION FROM THE PROBE (statement-neutral, recorded).
  The probe declared the three torus measure instances as `pw_*`; here they are NAMED `gm_ms`,
  `gm_haar`, `gm_prob` (D20; CommunityUnique.lean uses `cu_*`, ClassFlowODE.lean `co_*`), because
  auto-named local instances from two modules collide in a third module that imports both; the
  bodies are the three-line block of FourierDeriv.lean lines 31-37.  The probe's namespace
  `W3dProbe` is replaced by `TheoremB` for the sixteen non-register declarations and by the reopened
  register `T9cProbe` for the three register items (D20, D21); the three register items are grouped
  at the end of the file in the D21 order (the probe interleaved them with the two helpers
  `fiber_zero`, `zeroMode_zero` and the smallness sibling; the dependencies allow the regrouping, and
  the two helpers precede the register in `TheoremB`).  One docstring line of the probe began with
  the word "lemma" and is re-wrapped so that no docstring line starts with a declaration keyword
  (the ruler reads such a line as a declaration).  Docstrings are the probe's, extended where a rule
  of section 7 asked for a clause (the hypotheses named, the mean-free smallness, the textbook
  note).  Instances, namespaces and docstrings are not statements; every statement is byte-identical
  to the blueprint's W3d block.  No sibling was added and no spec drift is recorded: every frozen
  statement is proved as written.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.CommunityUnique

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
local instance gm_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance gm_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance gm_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! # W3d : TheoremB/GeneralMean.lean (the probe `audit-tier9c/w3d/probe/ReconW3d.lean`) -/

/-! ## 1. The phase lemma: the coefficient of a translate -/

/-- `fiber` is additive (coordinatewise `AddCircle.coe_add`). -/
theorem fiber_add (x y : ℝ³) : fiber (x + y) = fiber x + fiber y := by
  funext l
  simp only [fiber, PiLp.add_apply, Pi.add_apply, AddCircle.coe_add]

/-- `fiber` respects subtraction (coordinatewise `AddCircle.coe_sub`). -/
theorem fiber_sub (x y : ℝ³) : fiber (x - y) = fiber x - fiber y := by
  funext l
  simp only [fiber, PiLp.sub_apply, Pi.sub_apply, AddCircle.coe_sub]

/-- Two points of `ℝ³` with the same fiber are identified by every one-periodic function
(both read back through the descent, `descend_fiber`). -/
theorem eq_of_fiber_eq {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f) {x y : ℝ³}
    (h : fiber x = fiber y) : f x = f y :=
  calc f x = descend f (fiber x) := (descend_fiber hf x).symm
    _ = descend f (fiber y) := by rw [h]
    _ = f y := descend_fiber hf y

/-- The descent of the translate `x ↦ f (x - a)`, read at the translated torus point
`z + fiber a`, is the descent of `f` at `z`: the two lifted points `rep (z + fiber a) - a` and
`rep z` project to the same torus point `z`. -/
theorem descend_translate_add {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f) (a : ℝ³)
    (z : UnitAddTorus (Fin 3)) :
    descend (fun x => f (x - a)) (z + fiber a) = descend f z := by
  show f (rep (z + fiber a) - a) = f (rep z)
  refine eq_of_fiber_eq hf ?_
  rw [fiber_sub, fiber_rep, fiber_rep, add_sub_cancel_right]

/-- The character is multiplicative in its torus argument (coordinatewise `toCircle_add`). -/
theorem mFourier_apply_add (n : Fin 3 → ℤ) (x y : UnitAddTorus (Fin 3)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- **THE PHASE LEMMA.**  The coefficient of the descent of the translate `x ↦ f (x - a)` is the
phase `mFourier (-k) (fiber a)` times the coefficient of the descent of `f`.  Route: the
translation invariance of the torus Haar measure (`integral_add_right_eq_self`, the `Measure.pi`
of the circle's Haar measure being right-invariant through `Pi.isAddLeftInvariant_volume` and
the commutative-group instance), then `descend_translate_add` and `mFourier_apply_add`
pointwise, then `integral_const_mul`.  No integrability hypothesis is consumed: the translation
invariance of the Bochner integral is unconditional, so only periodicity is needed.  The phase
of a translated function's coefficients is textbook bookkeeping. -/
theorem mFourierCoeff_descend_translate {f : ℝ³ → ℂ} (hper : IsOnePeriodic f) (a : ℝ³)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => f (x - a)) k
      = mFourier (-k) (fiber a) * mFourierCoeff (descend f) k := by
  unfold mFourierCoeff
  calc ∫ z, mFourier (-k) z • descend (fun x => f (x - a)) z
      = ∫ z, mFourier (-k) (z + fiber a) • descend (fun x => f (x - a)) (z + fiber a) :=
        (integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus (Fin 3))))
          (fun z => mFourier (-k) z • descend (fun x => f (x - a)) z) (fiber a)).symm
    _ = ∫ z, mFourier (-k) (fiber a) * (mFourier (-k) z • descend f z) := by
        congr 1
        funext z
        rw [descend_translate_add hper a z, mFourier_apply_add, smul_eq_mul, smul_eq_mul]
        ring
    _ = mFourier (-k) (fiber a) * ∫ z, mFourier (-k) z • descend f z :=
        integral_const_mul _ _

/-- The phase, evaluated: `mFourier (-k) (fiber a) = exp (-(2πi Σᵢ kᵢ aᵢ))`
(`fourier_coe_apply` coordinatewise, `Complex.exp_sum`). -/
theorem mFourier_neg_fiber (k : Fin 3 → ℤ) (a : ℝ³) :
    mFourier (-k) (fiber a)
      = Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (k i : ℝ) * a i : ℝ) : ℂ))) := by
  simp only [mFourier, ContinuousMap.coe_mk, fiber, Pi.neg_apply]
  have h1 : ∀ i : Fin 3, fourier (-k i) ((a i : ℝ) : AddCircle (1 : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((-k i : ℤ) : ℂ) * (a i : ℂ) / 1) := fun i =>
    fourier_coe_apply
  rw [Finset.prod_congr rfl fun i _ => h1 i, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The phase lemma with the phase written out. -/
theorem mFourierCoeff_descend_translate_exp {f : ℝ³ → ℂ} (hper : IsOnePeriodic f) (a : ℝ³)
    (k : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => f (x - a)) k
      = Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (k i : ℝ) * a i : ℝ) : ℂ)))
        * mFourierCoeff (descend f) k := by
  rw [mFourierCoeff_descend_translate hper a k, mFourier_neg_fiber]

/-! ## 2. The general-mean identity -/

/-- Continuity of the real datum of an ℓ¹ family (`contDiff_uLift` at order `0`,
`contDiff_euclidean`). -/
theorem continuous_u₀Real {c : (Fin 3 → ℤ) → Vel} (hc : Summable fun k => ‖c k‖) :
    Continuous (u₀Real c) := by
  have hu : ∀ j, ContDiff ℝ ((0 : ℕ) : ℕ∞) (uLift j c) := fun j =>
    contDiff_uLift j c 0 fun q hq => by
      obtain rfl : q = 0 := Nat.le_zero.mp hq
      simpa using hc
  have h : ContDiff ℝ ((0 : ℕ) : ℕ∞) (u₀Real c) := by
    rw [contDiff_euclidean]
    intro j
    exact Complex.reCLM.contDiff.comp (hu j)
  exact h.continuous

/-- A translate of a one-periodic function is one-periodic. -/
theorem isOnePeriodic_translate {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f) (a : ℝ³) :
    IsOnePeriodic (fun x => f (x - a)) := by
  intro x i
  show f (x + EuclideanSpace.single i 1 - a) = f (x - a)
  rw [add_sub_right_comm]
  exact hf (x - a) i

/-- **THE GENERAL-MEAN IDENTITY** (D12, rung12 section 8 item 7).  For a real ℓ¹ coefficient
flow `c` and any mean `m`, the coefficient flow of the boosted real pair is the zero mode `m`
plus the phase-shifted flow: `classFlow (galV m (vReal c)) t k
= zeroMode m k + mFourier (-k) (fiber ((t / (2π)) • m)) • c t k` at every campaign time
`t ≥ 0`.  Route: `classFlow_apply`, the boost unfolded (`galV`, `vReal`, the clock
`2π · (t / 2π) = t`), `coeff_add` on the constant and the translate, `coeff_const`, the
phase lemma componentwise, and the round trip `coeff_u₀Real`.  Only `RealField (c t)` and
`Summable ‖c t k‖` at the one time `t` are consumed by the proof (the frozen statement carries them
in the `∀ t ≥ 0` form; `classFlow` and `u₀Real` are total, rule 10; the identity carries the two
hypotheses it needs).  The Galilean boost's effect on the modes is
textbook bookkeeping; this is a consistency identity, not a uniqueness statement. -/
theorem classFlow_galV_vReal {m : ℝ³} {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hreal : ∀ t ≥ 0, RealField (c t)) (hl1 : ∀ t ≥ 0, Summable fun k => ‖c t k‖)
    {t : ℝ} (ht : 0 ≤ t) (k : Fin 3 → ℤ) :
    classFlow (galV m (vReal c)) t k
      = zeroMode m k + mFourier (-k) (fiber ((t / (2 * Real.pi)) • m)) • c t k := by
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfun : (fun x => galV m (vReal c) x (t / (2 * Real.pi)))
      = fun x => m + u₀Real (c t) (x - (t / (2 * Real.pi)) • m) := by
    funext x
    show m + WithLp.toLp 2 (fun j => (uLift j (c (2 * Real.pi * (t / (2 * Real.pi))))
      (x - (t / (2 * Real.pi)) • m)).re) = _
    rw [mul_div_cancel₀ t h2π]
    rfl
  have hcont : Continuous (u₀Real (c t)) := continuous_u₀Real (hl1 t ht)
  have hper : IsOnePeriodic (u₀Real (c t)) := isOnePeriodic_u₀Real (c t)
  rw [classFlow_apply, hfun,
    coeff_add (w := fun _ => m) (w' := fun x => u₀Real (c t) (x - (t / (2 * Real.pi)) • m))
      continuous_const (fun _ _ => rfl) (hcont.comp (continuous_id.sub continuous_const))
      (isOnePeriodic_translate hper _), T9Probe.coeff_const]
  congr 1
  refine PiLp.ext fun j => ?_
  rw [PiLp.smul_apply, smul_eq_mul, coeff_apply]
  have hca := coeff_apply (u₀Real (c t)) k j
  rw [mFourierCoeff_descend_translate (f := fun y => ((u₀Real (c t) y j : ℝ) : ℂ))
    (isOnePeriodic_ofReal_component hper j) _ k, ← hca, coeff_u₀Real (hreal t ht) (hl1 t ht)]

/-- The identity with the phase written out as an exponential in the campaign clock:
`exp (-(i t Σᵢ kᵢ mᵢ))` (the class-clock phase `e^{-2πi (k·m) τ}` at `t = 2πτ`). -/
theorem classFlow_galV_vReal_exp {m : ℝ³} {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hreal : ∀ t ≥ 0, RealField (c t)) (hl1 : ∀ t ≥ 0, Summable fun k => ‖c t k‖)
    {t : ℝ} (ht : 0 ≤ t) (k : Fin 3 → ℤ) :
    classFlow (galV m (vReal c)) t k
      = zeroMode m k
        + Complex.exp (-(Complex.I * ((t * ∑ i, (k i : ℝ) * m i : ℝ) : ℂ))) • c t k := by
  rw [classFlow_galV_vReal hreal hl1 ht k, mFourier_neg_fiber]
  congr 3
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hs : (∑ i, (k i : ℝ) * ((t / (2 * Real.pi)) • m) i : ℝ)
      = (t / (2 * Real.pi)) * ∑ i, (k i : ℝ) * m i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [PiLp.smul_apply, smul_eq_mul]; ring
  rw [hs]
  push_cast
  field_simp

/-! ## 3. Two helpers for the mean-free reduction (`fiber 0`, `zeroMode 0`) -/

/-- `fiber 0 = 0`. -/
theorem fiber_zero : fiber (0 : ℝ³) = 0 := by
  funext l
  simp [fiber]

/-- `zeroMode 0 = 0`. -/
theorem zeroMode_zero : zeroMode (0 : ℝ³) = 0 := by
  funext k
  by_cases hk : k = 0
  · subst hk
    refine PiLp.ext fun j => ?_
    simp [zeroMode, castCV]
  · simp [zeroMode, hk]

/-! ## 4. The smallness sibling (rung11 section 8 item 2) -/

/-- The two smallness spellings are equivalent: `ens` is insensitive to the mean
(`ens_meanFree`, the zero mode carries `‖freq 0‖ = 0`) while `en` is not (`en_meanFree`). -/
theorem smallness_ens_iff (κ ν' : ℝ) (u₀ : ℝ³ → ℝ³) :
    κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 ↔
    κ * en (meanFree (coeff u₀)) * ens (coeff u₀) < (2 * Real.pi * ν') ^ 4 := by
  rw [ens_meanFree]

/-- **The smallness sibling**, for citation convenience: the Tier 9 capstone with the enstrophy
factor spelled on the full coefficient field, `ens (coeff u₀)`.  One `rw [ens_meanFree]` from
`theorem_B_community_periodic_data`, whose frozen spelling (D3, on the mean-free part in both
factors) stays the primary one (D24): `ens` is insensitive to the mean (`ens_meanFree`) while
`en` is not (`en_meanFree`), so the mixed spelling must not be read as the mean entering the
threshold; the smallness hypothesis stays a hypothesis on the mean-free part of the datum's
coefficient field in the `en` factor.  Same scope as the capstone: existence only, for every
`0 < ν'`, `f = 0`, OUR COPY of the class, the datum in the community's own
`InitialVelocityConditionPeriodic`; the upstream statements are untouched; the `∃ κ` is the
capstone's own (of explicit form, exported as a compiled existential). -/
theorem theorem_B_community_periodic_data_ens :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ →
      κ * en (meanFree (coeff u₀)) * ens (coeff u₀) < (2 * Real.pi * ν') ^ 4 →
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_data
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' u₀ hu₀ hsmall
  exact H hν' hu₀ ((smallness_ens_iff κ ν' u₀).mpr hsmall)

/-! ## 5. The register (`T9cProbe` reopened, D20): the Tier 9 instance on a datum with any mean,
its mean-free reduction, and the constant-datum check -/

namespace T9cProbe

/-- **MUST HOLD, the general-mean instance** (D12): on ANY datum `u₀` in the community's own
`InitialVelocityConditionPeriodic` meeting the smallness hypothesis on the MEAN-FREE part of its
coefficient field, `κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀)) < (2πν')⁴`, with
`0 < ν'`, the flow `c` exhibited by `theorem_B_community_periodic_flow` at `ν := 2πν'` from
the mean-free datum is real and ℓ¹ at every `t ≥ 0`, the boosted real pair is a member of OUR
COPY of the class at `f = 0`, and the member's coefficient flow is the zero mode
`meanVec (coeff u₀)` plus the phase-shifted `c`.  Mirrors `theorem_B_community_periodic_data_flow`
(CommunityData.lean), keeping clause 2 (reality) and clause 10 at `p = 0` (the ℓ¹), then
`classFlow_galV_vReal`.  At a mean-free datum the phase is `1` and the zero mode `0`
(`general_mean_identity_mean_free` below), recovering the shape of
`T9cProbe.flow_witness_classFlow_eq` (CommunityUnique.lean).  The `∃ κ` is that of
`theorem_B_community_periodic_flow` (of explicit form, exported as a compiled existential; no numeric
value is claimed); existence with an
exhibited witness, not uniqueness: consistency bookkeeping, textbook, no new uniqueness
statement. -/
theorem flow_witness_classFlow_eq_general_mean :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ →
      κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = meanFree (coeff u₀) ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable fun k => ‖c t k‖) ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0)
          (galV (meanVec (coeff u₀)) (vReal c)) (galP (meanVec (coeff u₀)) (pReal c)) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, classFlow (galV (meanVec (coeff u₀)) (vReal c)) t k
          = zeroMode (meanVec (coeff u₀)) k
            + mFourier (-k) (fiber ((t / (2 * Real.pi)) • meanVec (coeff u₀))) • c t k) := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_community_periodic_flow
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' u₀ hu₀ hsmall
  obtain ⟨hl1, hsob, hreal, hdiv, hinv⟩ := datum_bridge hu₀
  have hν : 0 < 2 * Real.pi * ν' := by positivity
  obtain ⟨c, h1, h2, -, -, -, -, -, -, -, h10, -, -, -, -, -, -, -, -, -, -, hclass⟩ :=
    H hν (summable_sob_meanFree hsob) (meanFree_zero _) (realField_meanFree hreal)
      (divFree_meanFree hdiv) hsmall
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ h2π] at hclass
  have hc0 : Summable fun k => ‖coeff u₀ k‖ := by simpa using hl1 0
  have hu := u₀Real_eq_meanVec_add' hc0
  rw [hinv] at hu
  have hl1' : ∀ t ∈ Ici (0:ℝ), Summable fun k => ‖c t k‖ := fun t ht => by
    simpa using h10 t ht 0
  refine ⟨c, h1, h2, hl1', ?_, ?_⟩
  · have hg := galilean_class (meanVec (coeff u₀)) hclass
    rwa [← hu] at hg
  · intro t ht k
    exact classFlow_galV_vReal (fun s hs => (h2 s hs).1) hl1' ht k

/-- SANITY: at a mean-free datum the phase is `1` and the zero mode `0`, so the general-mean
identity reads `classFlow (galV (meanVec (coeff u₀)) (vReal c)) t k = c t k`, the shape of
`T9cProbe.flow_witness_classFlow_eq` (CommunityUnique.lean). -/
theorem general_mean_identity_mean_free {u₀ : ℝ³ → ℝ³} (h0 : coeff u₀ 0 = 0)
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hreal : ∀ t ≥ 0, RealField (c t)) (hl1 : ∀ t ≥ 0, Summable fun k => ‖c t k‖)
    {t : ℝ} (ht : 0 ≤ t) (k : Fin 3 → ℤ) :
    classFlow (galV (meanVec (coeff u₀)) (vReal c)) t k = c t k := by
  rw [classFlow_galV_vReal hreal hl1 ht k, T9Probe.meanVec_of_mean_zero h0, smul_zero,
    fiber_zero, zeroMode_zero, Pi.zero_apply, zero_add]
  have h1 : mFourier (-k) (0 : UnitAddTorus (Fin 3)) = 1 := by
    simp [mFourier]
  rw [h1, one_smul]

/-- REGISTER (constant datum): on `u₀ = fun _ => m` the general-mean instance exhibits a flow
`c` starting at `0` whose boosted member has `classFlow = zeroMode m` at every `t ≥ 0` (the
member's velocity is the constant `m` by `const_datum_member_is_const`, so its slice is the
constant datum and `coeff_const` applies), and the flow itself is the zero flow on `t ≥ 0`
(the identity's right side `zeroMode m k + phase • c t k` against `zeroMode m k`, the phase
being a unit).  The identification of the velocity is E6 of CommunityUnique.lean, a consequence
of the velocity capstone (uniqueness inside OUR COPY of the community class at `f = 0`, for the
same datum and `0 < ν'`); the member here is a member at `f = 0` with `0 < ν'`.  Consistency
bookkeeping on the constant datum; no new uniqueness statement. -/
theorem general_mean_const_datum :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ (m : ℝ³),
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = 0 ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0)
          (galV m (vReal c)) (galP m (pReal c)) ∧
        (∀ t ∈ Ici (0:ℝ), classFlow (galV m (vReal c)) t = zeroMode m) ∧
        (∀ t ∈ Ici (0:ℝ), c t = 0) := by
  obtain ⟨κ, hκ, H⟩ := flow_witness_classFlow_eq_general_mean
  refine ⟨κ, hκ, ?_⟩
  intro ν' hν' m
  obtain ⟨c, h1, -, -, hclass, hid⟩ :=
    H hν' (T9Probe.const_datum_in_class m) (T9Probe.capstone_hyp_const_datum m κ hν')
  rw [T9Probe.coeff_const, meanVec_zeroMode] at hclass hid
  rw [T9Probe.coeff_const, meanFree_zeroMode] at h1
  have hconst := const_datum_member_is_const m hν' hclass
  have hcf : ∀ t ∈ Ici (0:ℝ), classFlow (galV m (vReal c)) t = zeroMode m := by
    intro t ht
    have hs : (fun x => galV m (vReal c) x (t / (2 * Real.pi))) = fun _ => m :=
      funext fun x => hconst x _ (div_nonneg (Set.mem_Ici.mp ht) (by positivity))
    show coeff (fun x => galV m (vReal c) x (t / (2 * Real.pi))) = zeroMode m
    rw [hs, T9Probe.coeff_const]
  refine ⟨c, h1, hclass, hcf, ?_⟩
  intro t ht
  funext k
  have hk := hid t ht k
  rw [hcf t ht] at hk
  have h0 : mFourier (-k) (fiber ((t / (2 * Real.pi)) • m)) • c t k = 0 :=
    add_left_cancel (hk.symm.trans (add_zero _).symm)
  have hunit : mFourier (-k) (fiber ((t / (2 * Real.pi)) • m)) ≠ 0 := by
    intro h
    have hn := norm_mFourier_apply (-k) (fiber ((t / (2 * Real.pi)) • m))
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  exact (smul_eq_zero.mp h0).resolve_left hunit

end T9cProbe

end

end TheoremB
