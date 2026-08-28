# Rung 7 — Tier 5 blueprint: the function-space bridge

Status: route FIXED by the t5-recon fleet (28 Aug 2026, five missions, all
load-bearing APIs compile-verified at the pin). Contract unchanged.

## The goal

**`theorem_B_torus`**: synthesize the sealed coefficient flow into a genuine
velocity field on the unit 3-torus and prove, kernel-checked: for data
`u₀ : Fin 3 → L2T3` (components a.e. real, mean-zero, spectrally div-free,
finite spectral enstrophy, small), a global-in-time L²-continuous field
`u : ℝ → Fin 3 → L2T3` with `u 0 = u₀`, a.e. real, div-free, satisfying the
calibrated Navier-Stokes equation in (band-limited-)weak form at every
`t ≥ 0`, trapped (`‖u t‖² ≤ ‖u₀‖²`, spectral enstrophy descending), and
UNIQUE in its class (via coefficient extraction + `theorem_B_unique` —
a clause genuinely beyond the leray-hopf capstones, which prove existence
but no uniqueness of any kind).

## Design commitments (frozen)

1. Component-wise synthesis `u : ℝ → Fin 3 → L2T3` (Mathlib's mFourierBasis
   is scalar; matches leray-hopf's component convention). Every Tier-5 file
   replicates the AddCircleMulti local MeasureSpace preamble VERBATIM.
2. Synthesis = `mFourierBasis.repr.symm` on the component ℓ² families
   (BASE LAYER LANDED: TheoremB/TorusSynthesis.lean — velSeq, synth,
   mFourierCoeff_synth recovery, norm_synth_sq, sum_norm_synth_sq = en).
   No pointwise-series claims anywhere coefficients are only ℓ².
3. 2π convention (mission D, cross-checked by an independent hand
   derivation, both landing on the same invariant): the general rescale
   d_k(t) := λ·c_k(μt) matches the honest unit-torus system iff
   μ/λ = 2π and μν̃ = (2π)²ν. Chosen solution: **λ = 1, μ = 2π,
   ν_phys = ν̃/(2π)** — pure time reparametrization, amplitudes untouched,
   so Parseval and every trap clause transfer with NO constants, and
   `theorem_B_unique` applies VERBATIM to the un-rescaled coefficients.
   Smallness: κ_torus := κ/(2π)⁶ (through ens → ‖∇u‖² = (2π)²·ens and
   ν̃⁴ = (2π)⁴ν_phys⁴). The capstone states the equation with the EXPLICIT
   honest constants −ν_phys(2π)²‖k‖² and −2πi·convolution.
4. The v1 solution class is SPECTRAL-WEAK: tests = band-limited real
   div-free trig fields (mirrors leray-hopf's IsGalerkinTest; their own
   scope note (issue #146) precedents separated-variable/band-limited
   forms). The identification with the physical pairing ∫(u·∇)w·u is its
   own brick (E4) with a pre-agreed fallback: v1 ships spectral-weak only,
   honestly labeled, if E4 resists.
5. leray-hopf interop: v2/stretch. v1 records the alignment in docs
   (our div-free = their divSymbol = 0 verbatim; our tests = their
   IsGalerkinTest; spectral enstrophy vs their viscousFormSq differs by
   the documented (2π)²). Mission B compiled a full restatement of their
   L²σ vocabulary layer against our Mathlib (~160 lines) — held in
   reserve; a literal WeakFormNS instantiation needs a writable copy of
   the read-only clone (6,242-line closure) and is the user's call.

## Waves

- **W-synth** (base LANDED; S4 remains): L²-continuity of t ↦ synth(c t)
  on Ici 0 — ℓ²-continuity by ε/3 (mode continuity + tail_en_lt with
  budget 4·ens c₀, the Tier-4 defect pattern verbatim); the isometry
  makes L²-continuity free. Risk LOW.
- **W-2π**: the time-substitution lemma on interval integrals (τ = 2πt,
  intervalIntegral.integral_comp_mul_left, c ≠ 0 only) + the calibrated
  coefficient system conversion. Risk LOW; blocks W-eq statement freeze.
- **W-struct**: reality (mFourierCoeff of star = conj at −k — hand-rolled:
  root-level integral_conj + mFourier_neg — then repr injectivity),
  spectral div-freeness (verbatim from DivFree + recovery), mean-zero,
  spectral H¹ (ens as (2π)⁻²·gradient energy, stated spectrally — no
  torus Sobolev exists at the pin; labeled). Risk LOW-MED.
- **W-eq** (load-bearing): E1 band-test class; E2 pairing collapse
  (hasSum_prod_mFourierCoeff + tsum_eq_sum); E-core: the time-integrated
  spectral-weak equation per band test = finite combination of exported
  mode integral equations (the test truncates FIRST — no new limit
  swaps). E3 coefficient-shift lemma (absent from both codebases; small).
  E4 = THE HARDEST BRICK: physical-convection identification via
  Mathlib's Holder.lean pairing machinery (holderL L²×L²→L¹ + lpPairing —
  both compile-verified ON the 3-torus by mission C) + truncation, with
  the fallback of commitment 4. Risk: E1-core LOW-MED, E4 MED-HIGH.
- **W-extract**: uniqueness transfer NEEDS coefficient extraction (the
  Parseval bijection does not transfer classes for free): coefficient
  curves via repr (1-Lipschitz evaluation), budgets via Parseval, the
  mode equation recovered by testing single-mode band tests (lerayProj
  supplies the 2-dim div-free complement; (k, −k) real pairing polarizes
  back to the complex mode equation). Risk MED.
- **W-cap**: theorem_B_torus assembly against frozen stubs. Risk LOW.

## Traps carried forward

Verbatim local-instance preamble in EVERY file (or Lp types silently land
on the wrong measure); en/ens junk-tsum discipline (every clause carries
its Summable certificate, the Tier-4 standard); `integral_conj` is
ROOT-namespace; ContinuousMap.inner_toLp conjugates its FIRST argument;
mFourier_add's implicit-argument order; tsum_sum is
Summable.tsum_finsetSum; pow_le_pow_left is pow_le_pow_left₀; no lemma
names the δ-integral ∫ mFourier n (3-line derived proof from mission C's
probe); Lp has no NormedStarGroup (avoid norms of star inside Lp — work
at coefficient level).
