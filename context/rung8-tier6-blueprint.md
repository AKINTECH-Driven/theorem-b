# Rung 8 — Tier 6 blueprint: smoothness

Status: route FIXED by the t6-recon fleet (29 Aug 2026, four missions, all
load-bearing APIs compile-verified). Contract unchanged: kernel + gate
judge; statements freeze at declaration; adversarial audit before tags.

## The goal

**`theorem_B_smooth`**: every spectral Sobolev norm
`sob m c := ∑' k, ‖freq k‖^(2m)·‖c k‖²` propagates along the canonical
flow — if the datum has `sob m` finite, the flow keeps it finite with the
explicit bound `sob m (c t) ≤ sob m c₀·(1 + exp(K_m T))` on every window —
and, from all-levels finiteness, the flow has a genuinely smooth
representative: the ℤ³-periodic lift `u : ℝ → (Fin 3 → ℝ) → ℂ`, C^p in
space for every p, C¹ in time on t > 0, satisfying calibrated
Navier-Stokes POINTWISE. Small-data solutions in the Clay problem's own
regularity class.

## The decisive design facts (recon-established)

1. **The half-weight split** (correction to the naive plan): never split
   the full `‖k‖^(2m)` (any correlation slot carrying weight 2m pays a
   level-2m sum — fatal). Write `‖k‖^(2m) = ‖k‖^m·‖k‖^m`; one factor
   lifts the sequence `z_k := ‖k‖^m·‖c_k‖` (its ℓ² IS `sob m`, allowed
   linearly); only the other splits via `freq k = freq(k−l) + freq l`
   plus `(a+b)^m ≤ 2^(m−1)(a^m + b^m)` (Mathlib's `add_pow_le`,
   compile-verified in the exact lattice shape).
2. **The same window at every level**: piece A′ runs `conv_corr_sq_le`
   and `weighted_interp` on the LIFTED sequence — the (1/8, 7/8)
   interpolation and both Young clones (8/7,8) and (16/15,16) are the
   T4 lemmas verbatim under (en, ens) → (sob m, sob (m+1)); Cauchy–
   Schwarz in the split slot pays √Z₀ — level ONE, the trap, not level
   m−1.
3. **No induction**: each level closes with only (E₀, Z₀, ν, m) in the
   constant. `(sob m)' ≤ −2ν·sob(m+1) + ν·sob(m+1) + K_m·sob m`;
   linear Grönwall per level; ∀m is quantifier packaging.
4. **Galerkin-first, Fatou, uniqueness-identified**: estimates run on
   `galerkin_family`'s flows (finite sums — the private weight-generic
   `hasDerivAt_weighted_sum` calculus, made public in W1); zero mode
   absent (0 ∉ boxS); DivFree along flows re-derived via
   `divFree_propagates_on` (theorem_B_cont's incantation); bounds are
   box-free → Fatou (`weighted_limit_le`, the 10-line generalization of
   `ens_limit_le`) → rebuild the limit with the T3/T5-exported tools
   (mode_extraction, integral_equation_limit, IccExtend continuity) →
   `theorem_B_unique` pins the Sobolev-bounded limit to the canonical
   flow. Junk-tsum danger of estimating at the limit level directly is
   entirely avoided.
5. **The classical form is the periodic lift** (mission C verdict): no
   manifold structure on the torus exists at the pin (do not attempt);
   the honest strongest statement is `u_lift t x := ∑' k, c t k j ·
   ∏ᵢ fourier (k i) (x i)` — ℤ³-periodic, C^p in space for every p
   (SmoothSeries on ℝ³ with weighted-ℓ¹ majorants from sob levels,
   `Summable ‖freq‖^n‖c‖` via AM-GM against `summable_inv_freq_pow_four`),
   C¹ in time on t > 0 (mode ODE + hasDerivAt_tsum on Ioo slabs),
   satisfying calibrated NS pointwise (mode ODE summed against the
   characters; nonlinearity identified via convFull_pairing_physical +
   coefficient injectivity, not a raw Cauchy product; the M4
   mFourierCoeff_deriv capstone ties classical partials to 2πi·nᵢ).
   C^∞-in-time is a recorded stretch OUTSIDE the headline.

## Waves

- **W1 — SobolevNorms.lean**: `sob` + basic lemmas (sob_zero_eq_en,
  sob_one_eq_ens, nonneg, monotone-in-m on mean-zero, truncation) +
  PUBLIC weight-generic clones (finite collapse, summability-of-support,
  the weighted finite-sum derivative, weighted Fatou `weighted_limit_le`)
  + the splitting lemma + weighted ℓ¹ exports. Risk LOW.
- **W2 — the level-m absorbed pairing**: the T4 PairingBound template at
  level m (half-weight split, pieces A′/B′, Young clones public).
  Risk LOW-MED (template established; exponent bookkeeping).
- **W3 — Galerkin sob-propagation**: per-level finite Grönwall on
  galerkin_family's flows with box-free K_m. Risk LOW-MED.
- **W4 — limit + identification**: weighted Fatou through a re-run of
  the T3-style extraction (the exported tools suffice; the T3 capstone
  is the template) → `theorem_B_sobolev` → uniqueness identification
  with ns_full_global_flow's flow. Risk MED (assembly-scale).
- **W5 — the classical layer**: continuous representative; the periodic
  lift; spatial C^p; time C¹; the pointwise PDE. Risk MED-HIGH at the
  pointwise-PDE brick; fallback: all-levels sob + continuous
  representative, honestly labeled, with the pointwise clause v2.
- **W-cap — theorem_B_smooth**.

## Traps carried forward

`add_pow_le` IS at the pin (Algebra/Order/Ring/Basic:119) — one recon
mission missed it under other names; use it. freq_add is PRIVATE (derive
the triangle via freq_sub + freq_neg, 4 lines, compile-verified). The
~10 private helpers to clone public are listed in the recon output
(GalerkinTrap's weighted calculus, PairingBound's b2_young* family).
Named local instances in every torus-side file. All house junk-tsum,
cast-distribution, and rename traps as catalogued in memory.
