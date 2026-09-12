# Mathlib upstreaming dossier

Prepared 29 Aug 2026, at tag `t5-torus-green` (101 audited theorems);
Unit 7 added 12 Sep 2026 at tag `t8b-community-green` (294 audited declarations).
Purpose: the campaign built several layers that are library-grade and
absent from Mathlib at pin `15a89b24`. This dossier lists them in
PR-ready units, with the generalization each would want before submission.
Acting on it (opening PRs, engaging reviewers) is outward-facing and
therefore the user's call; nothing here has been submitted anywhere.

## Unit 1 — the multi-dimensional derivative↔frequency bridge
**File**: `TheoremB/FourierDeriv.lean` (M4 wave 1; audited, tag m4-wave1-green).
**Content**: `fourierCoeff_hasDerivAt` (1-D periodic, all `n : ℤ` including 0),
the coordinate-peeling `integral_insertNth`, the monomial factorization
`mFourier_insertNth`, and the capstone `mFourierCoeff_deriv`
(∂ᵢ ↦ 2πi·nᵢ multiplier on `UnitAddTorus (Fin d)` at d = 3).
**Why Mathlib wants it**: the pin's Fourier-derivative theory is 1-D
interval-based; AddCircleMulti has no derivative layer at all.
**Generalization before PR**: arbitrary `Fintype d` (the proofs are
d-agnostic modulo `Fin 3` literals); align with Mathlib's preference for
`fourierCoeff` naming. The file-local MeasureSpace instances must be
reconciled with AddCircleMulti's own local instances (a known sharp edge —
Mathlib may prefer to EXPORT those instances, which would simplify every
consumer, ours included).

## Unit 2 — the lattice kernel and shell machinery
**Files**: `TheoremB/LatticeKernel.lean` (Tier 4) and the shell-count
lemmas inside `TheoremB/SpectralNorms.lean` (M2).
**Content**: `summable_freq_rpow_neg` (Σ‖k‖^s over ℤ³ converges for
s < −3, via natMax shell counts), `kernel_sum_le` (the shift-uniform
convolution-kernel bound at exponent 7/4), `weighted_interp` (the
(1/8, 7/8) Hölder interpolation between ℓ²-mass and weighted ℓ²-mass).
**Why**: these are the standard bricks of discrete harmonic analysis.
CORRECTION (2 Sep 2026): the pin is NOT bare here — `ZLattice.summable_norm_rpow`
exists and is what `summable_freq_rpow_neg` consumes (SpectralNorms.lean:84),
`Mathlib/Topology/Algebra/InfiniteSum/DiscreteConvolution.lean` exists at
the pin, and `tsum_mul_tsum_of_summable_norm` is in
`Analysis/Normed/Ring/InfiniteSum.lean`. What is plausibly absent is the
shift-uniform kernel bound at exponent 7/4 with shell counts and the
(1/8, 7/8) weighted interpolation; a PR must be scoped to those and cite
the existing API. The same caution applies to every "absent from Mathlib"
line in this dossier: each was read from the pinned sources, none was
checked against Mathlib master or open PRs, and "PR-ready" is a
self-assessment under Mathlib's 2026 policy on LLM-generated code.
**Generalization**: ℤ^d with the exponent window s < −d; the kernel lemma
at general conjugate exponents.

## Unit 3 — differentiation-adjacent series tools
**Content**: `hasDerivAt_finset_sum_sq` (DefectCalculus), the
finite-section energy-derivative pattern, and the interval-localized
Grönwall wrappers (`gronwall_const_source` in FullUnique — an
endpoint-free constant-source Grönwall needing derivative data only on
the open interior, which Mathlib's Gronwall.lean lacks: its lemmas demand
the left endpoint).
**Why**: the Ico-endpoint requirement in Mathlib's Grönwall family is a
recurring pain point; the Ioo-only form is strictly more applicable.

## Unit 4 — the ε/3 tail method as reusable lemmas
**Files**: `TheoremB/LimitPassage.lean`, `ConvContinuity.lean` (Tier 3).
**Content**: `tendsto_convFull_of_modes` and
`tendsto_convFull_uniformlyOn` are convolution-specific, but their core —
"mode-wise limits pass through an ℓ²×ℓ²-type bilinear tsum under a
uniform weighted-tail bound, where no summable uniform majorant exists" —
generalizes to a statement about bilinear maps on weighted ℓ² spaces.
Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) exists at the
pin; the tail-uniform variant does not.
**Generalization effort**: moderate; worth proposing as an extension next
to Tannery in `Analysis/Normed/Group/Tannery.lean`.

## Unit 5 — the product-coefficient identity
**File**: `TheoremB/CoeffExtract.lean` (Tier 5).
**Content**: `convFull_pairing_physical` — the Fourier coefficient of a
pointwise product of two L² synthesized functions equals the coefficient
convolution, proved entirely inside L² (the twist trick: absorb the
character into one factor, keep both slots L², use inner-product
continuity — no L¹ excursion, no convolution theorem).
**Why**: Mathlib has NO torus convolution theorem at the pin (verified by
Tier-5 recon); this is the natural first brick, and the L²-only proof is
short.
**Generalization**: state for two arbitrary `Lp ℂ 2` functions via their
coefficient families (our version is phrased through the synthesis
operator; the general form falls out by `repr` surjectivity).

## Unit 6 — small sharp edges worth reporting upstream (not PRs)
- `Analysis/ODE/Gronwall.lean`'s right-derivative hypotheses demand the
  LEFT endpoint (Ico), which interior-only knowledge cannot satisfy.
- Countable-product metrizability is Finite-index-only
  (`Topology/Metrizable/Basic.lean`), while first countability has the
  countable-pi instance; a countable-index `PseudoMetrizableSpace` pi
  instance would serve sequential-compactness users directly.
- AddCircleMulti's local (non-exported) MeasureSpace instances force
  every consumer to replicate a three-instance preamble verbatim, and
  auto-generated local-instance names collide across files on double
  import (we now name them explicitly per file).
- No named δ-integral lemma `∫ mFourier n = if n = 0 then 1 else 0`.

## Unit 7 — the within-convex Weierstrass M-test for series of functions
**File**: `TheoremB/WithinSeries.lean` (Tier 8b wave W2, tag
`t8b-joint-smooth-green`; `import Mathlib` only, 234 lines, six theorems,
all gated).
**Content**: on a convex set `s`, a series of functions with a summable
uniform bound on the within-derivatives is differentiable within `s`
with derivative the sum of the derivatives
(`summable_of_summable_hasFDerivWithinAt_of_convex`,
`hasFDerivWithinAt_tsum_of_convex`, `hasDerivWithinAt_tsum_of_convex`),
and is `C^N` within `s` when the iterated within-derivatives carry summable
uniform bounds, given unique differentials on `s`
(`iteratedFDerivWithin_tsum_apply_of_convex`, `contDiffOn_tsum_of_convex`);
at `s = univ` the engine recovers the shape of Mathlib's `contDiff_tsum`
(`contDiff_tsum_of_convex_univ`).
**Why Mathlib wants it**: `Analysis/Calculus/UniformLimitsDeriv.lean` proves
`hasFDerivAt_of_tendstoUniformlyOn` on OPEN sets only and
`Analysis/Calculus/SmoothSeries.lean` has `hasFDerivAt_tsum_of_isPreconnected`,
`contDiff_tsum` and their relatives on open preconnected sets or `univ`;
neither file has a `Within` or `On`-a-subset variant. Measured twice: at
the pin `15a89b24` (grep, two independent readers, 9 Sep 2026) and on
Mathlib master (the two files fetched from GitHub on 12 Sep 2026: seventeen
and eighteen declarations respectively, none with `Within` in its name or
a within-set hypothesis). Closed slabs `E × [0, ∞)` are the use case:
smoothness up to a boundary in time cannot be reached from the open-set
theorems. Not new mathematics: a direct ε/3 argument through the mean value
inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` for the
first-order half, and the `SmoothSeries` induction with `fderivWithin_congr`
transporting the pointwise-on-`s` induction hypothesis for the iterated half.
**Generalization before PR**: state the first-order half for an arbitrary
`NontriviallyNormedField` with `IsRCLikeNormedField` as `SmoothSeries` does
(ours is over `ℝ`, which is what the mean value inequality needs; the
convexity hypothesis is real by nature); consider the `TendstoUniformlyOn`
formulation of `UniformLimitsDeriv` as the primitive and derive the tsum
forms from it, as Mathlib does for the open case; name per Mathlib's
`_of_convex` / `Within` conventions. Sharp edges measured at the pin, to
mention in the PR: binders over the complement subtype must be written
`↥((↑T : Set ι)ᶜ)`; `tendsto_tsum_compl_atTop_zero` and
`Summable.sum_add_tsum_compl` use two spellings of the same subtype (defeq);
`contDiffOn_iff_continuousOn_differentiableOn` is stated at `ℕ∞` while the
iterated-derivative lemmas take `WithTop ℕ∞`. Subject to Mathlib's 2026
policy on LLM-generated code, as every unit here; opening the PR is the
user's call.

## Housekeeping notes recorded by the Tier-5 audit (repo-internal)
- `calibrated_integral_equation`/`calibrated_trap` (TorusStructure) are
  valid, audited, and currently unconsumed — the torus capstone re-derives
  the calibration inline; both paths verified to agree.
- `mode_equation_of_weak` carries two unused hypotheses (`hν`, `hzero`)
  in its frozen statement; harmless (they only weaken the lemma).
- The physical-identification lemmas' wiring status is tracked in the
  Tier-5 polish wave (`linear_pairing_physical`,
  `convection_pairing_physical`).
