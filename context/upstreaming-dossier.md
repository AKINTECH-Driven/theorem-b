# Mathlib upstreaming dossier

Prepared 29 Aug 2026, at tag `t5-torus-green` (101 audited theorems).
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

## Housekeeping notes recorded by the Tier-5 audit (repo-internal)
- `calibrated_integral_equation`/`calibrated_trap` (TorusStructure) are
  valid, audited, and currently unconsumed — the torus capstone re-derives
  the calibration inline; both paths verified to agree.
- `mode_equation_of_weak` carries two unused hypotheses (`hν`, `hzero`)
  in its frozen statement; harmless (they only weaken the lemma).
- The physical-identification lemmas' wiring status is tracked in the
  Tier-5 polish wave (`linear_pairing_physical`,
  `convection_pairing_physical`).
