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

## Frozen interfaces (statements freeze here; recon-derived verbatim)

W1 file `TheoremB/SobolevNorms.lean`:

```
noncomputable def sob (m : ℕ) (c : (Fin 3 → ℤ) → Vel) : ℝ :=
  ∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2
```

plus: `sob_zero_eq_en`, `sob_one_eq_ens`, `sob_nonneg`; public
weight-generic clones `weighted_tsum_eq_sum` / `summable_weighted_of_support`
/ `hasDerivAt_weighted_finset_sum_sq` (GalerkinTrap's privates, arbitrary
weight `w : (Fin 3 → ℤ) → ℝ`); `sob_truncate_le`; `weighted_limit_le`
(generic-weight `en_limit_le`); the lift identities
`(‖freq k‖^m·x)² = ‖freq k‖^(2m)·x²` and
`‖freq k‖²·‖freq k‖^(2m) = ‖freq k‖^(2(m+1))`; `freq_triangle` (from
freq_sub); `two_pow_split : 0 ≤ a → 0 ≤ b → 1 ≤ m →
(a+b)^m ≤ 2^(m−1)·(a^m + b^m)` (compiled proof in the recon probe —
NNReal route or `add_pow_le`); the sob-ladder
(sob-m summable + support off 0 ⟹ summable at every j ≤ m via
one_le_norm_freq).

W2 file `TheoremB/SobolevPairing.lean` — the tier's center of mass:

```
theorem sobolev_pairing_absorbed {ν E Z : ℝ} (hν : 0 < ν) (hE : 0 ≤ E)
    (hZ : 0 ≤ Z) (m : ℕ) (hm : 1 ≤ m) :
    ∃ K, 0 < K ∧ ∀ {S : Finset (Fin 3 → ℤ)}, (0 : Fin 3 → ℤ) ∉ S →
      ∀ {c : (Fin 3 → ℤ) → Vel}, (∀ k ∉ S, c k = 0) →
        en c ≤ E → ens c ≤ Z →
        2 * |∑ k ∈ S, ‖freq k‖ ^ (2*m) * inner ℝ (convGal S c k) (c k)| ≤
          ν * sob (m+1) c + K * sob m c
```

NO RealField, NO DivFree (raw convGal; the consumer drops lerayProj via
inner_lerayProj_of_divFree before invoking this). All summability
finite-support-trivial. Proof = PairingBound T1+T2b line-isomorphic port
under the half-weight split; clone privates b2_term_norm_le,
b2_tsum_mul_le, b2_young8, b2_young16 (young lemmas port UNCHANGED).

W3 file `TheoremB/SobolevTrap.lean`:

```
theorem galerkin_sobolev_bound {ν : ℝ} (hν : 0 < ν) (E Z : ℝ)
    (hE : 0 ≤ E) (hZ : 0 ≤ Z) (m : ℕ) (hm : 1 ≤ m) :
    ∃ K, 0 < K ∧ ∀ {T : ℝ} {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t, ∀ k ∉ S, c t k = 0) → DivFree (c 0) →
      (∀ t ∈ Set.Icc 0 T, ∀ k, HasDerivAt (fun s => c s k)
        (-(ν * ‖freq k‖^2) • c t k + lerayProj k (convGal S (c t) k)) t) →
      (∀ t ∈ Set.Icc 0 T, en (c t) ≤ E ∧ ens (c t) ≤ Z) →
      ∀ t ∈ Set.Icc 0 T, sob m (c t) ≤ sob m (c 0) * (1 + Real.exp (K * T))
```

Derivative of t ↦ sob m (c t) goes through the finite collapse FIRST
(hen_deriv pattern); DivFree along the flow via divFree_propagates_on;
drop −ν·sob(m+1) ≤ 0; gronwall_const_source shift trick. Plus the ∀m
package (m = 0 straight from the en trap).

W4 file `TheoremB/TheoremBSobolev.lean`: route (α) — a fresh replay of
theorem_B_cont (FullUnique lines ~100–312; everything it uses is public)
with two insertions: W3 applied per box radius R (sob m (truncate) ≤
sob m c₀ makes the family's sob bounds UNIFORM IN R), and
weighted_limit_le after extraction. `theorem_B_sobolev` = theorem_B_cont's
statement + `Summable (fun l => ‖freq l‖^(2m)·‖c₀ l‖²)` hypothesis +
per-t sob bound and summability clauses. THEN
`ns_full_global_flow_sobolev`: theorem_B_unique identifies each horizon's
witness with the eternal flow (the 14-hypothesis pattern is written in
ns_full_global_flow's hA block; budgets exactly (en c₀, ens c₀)) ⟹ the
eternal flow's sob bound for all t ≥ 0. Tag v1 here: t6-sobolev-green.

W4 frozen capstone `theorem_B_sobolev` (declared here, before any builder
touches it — theorem_B_cont's statement with the level-m additions):

```
theorem theorem_B_sobolev :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ (m : ℕ), 1 ≤ m →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∃ K, 0 < K ∧ ∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) ∧
        (∀ t ∈ Icc (0:ℝ) T,
          Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
          sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * T)))
```

(K uniform across horizons — it depends only on (ν, m, en c₀, ens c₀);
the per-horizon witness flow is per-T exactly as in theorem_B_cont.)
Transfer capstone `ns_full_global_flow_sobolev`: mirrors
ns_full_global_flow's statement + the level-m summability hypothesis +
the eternal clause `∀ t, 0 ≤ t → sob m (c t) ≤ sob m c₀ *
(1 + Real.exp (K * t))` with per-t summability, by taking horizon T := t
and identifying via theorem_B_unique (budgets exactly (en c₀, ens c₀)).

W5 spec (mission C's verdict, statements freeze at first declaration
guided by this prose; W4 is landed so the chain is live). Steps (i)-(ii)
of C's sequence are DONE (sob = the H^m layer; summable_weighted_norm =
the weighted ℓ¹ export). Remaining bricks:

- **W5a — the continuous representative** (torus side; file
  TheoremB/ContinuousRep.lean; VERBATIM AddCircleMulti local MeasureSpace
  preamble with EXPLICITLY NAMED instances, prefix cr_). Define
  `uCont j c (hc : Summable fun k => ‖c k‖)` as the sup-norm tsum in
  C(T3, ℂ) of `fun k => c k j • mFourier k` (Summable in C from ℓ¹ since
  ‖mFourier k‖ = 1); identify `ContinuousMap.toLp ... (uCont j c hc) =
  synthT j c` via ContinuousMap.hasSum_of_hasSum_Lp + hasSum_synth +
  L² limit uniqueness; export coefficient recovery (mFourierCoeff of
  uCont = c · j via mFourierCoeff_synthT + toLp a.e.-congruence) and the
  everywhere-pointwise representation
  (hasSum_mFourier_series_apply_of_summable). Structural clauses
  (reality, spectral div-free, mean zero, Parseval) inherit from
  TorusSynthesis through the identification.
- **W5b — the ℤ³-periodic lift and spatial regularity** (ℝ³ side; file
  TheoremB/PeriodicLift.lean). `uLift j c : EuclideanSpace ℝ (Fin 3) → ℂ
  := fun x => ∑' k, c k j • ∏ i, fourier (k i) (↑(x i) : AddCircle 1)`;
  periodicity via AddCircle.coe_add_period; every term ContDiff ℝ ⊤
  (compiled probe: fourier_coe_apply + contDiff_exp + proj, ≈10 lines);
  `ContDiff ℝ p uLift` for every fixed p by contDiff_tsum with the
  m!·(2π‖freq k‖)^m iteratedFDeriv bounds (norm_iteratedFDeriv_comp_le;
  m fixed per slot so m! is harmless) against summable_weighted_norm;
  fiberwise insertNth-format spatial partials (hasDerivAt_tsum) matching
  the M4 mFourierCoeff_deriv consumption format; agreement of uLift with
  uCont ∘ coe (the lift descends).
- **W5c — the time layer** (file TheoremB/TimeLayer.lean). Along the
  eternal Sobolev flow: t ↦ uLift/uCont pointwise time derivative on
  t > 0 via hasDerivAt_tsum_of_isPreconnected on Ioo slabs (mode ODE on
  Ioi 0 from ns_full_global_flow(_sobolev); t-locally-uniform ℓ¹
  majorants from the per-time sob bounds + summable_weighted_norm;
  ∂_t u continuous via continuousOn_convFull machinery). First order
  ONLY — C^∞-in-time needs d/dt-of-convFull (absent) and stays a
  recorded stretch OUTSIDE the capstone.
- **W5-cap — theorem_B_smooth** (file TheoremB/TheoremBSmooth.lean):
  data ∀-level summable (statement shape: hypothesis
  `∀ p : ℕ, Summable (fun l => ‖freq l‖ ^ (2*p) * ‖c₀ l‖ ^ 2)`) + the
  standing small-data hypotheses ⟹ the eternal flow c (with all
  ns_full_global_flow clauses) admits the classical representative:
  per-time uCont/uLift, ℤ³-periodic, ContDiff ℝ p in space for every p,
  C¹ in time on t > 0, satisfying CALIBRATED NS pointwise everywhere
  (2π factors exactly as theorem_B_torus installs them: ν_phys = ν̃/(2π)
  convention recorded there; the mode ODE summed against characters;
  nonlinearity identified via convFull_pairing_physical +
  L2_ext_of_coeff coefficient injectivity — never a raw Cauchy
  product). Per-level sob clauses quoted from ns_full_global_flow_sobolev
  per m (the per-m/one-flow wording rule from the audit register
  applies).

Fallback ladder v1/v2/v3 — each rung independently taggable and honest:
v1 = t6-sobolev-green (W1-W4, LANDED); v2 = + continuous space-time
representative; v3 = full classical statement (t6-smooth-green).
Do not promise analytic-in-space (contDiff_tsum caps at ℕ∞) and never
claim C^∞-in-time in the capstone.

## Audit register (W1-W3 fleet, 29 Aug 2026 — 0 BLOCKER, 0 statement
MAJOR; all findings prose/docstring, fixed pre-tag)

Claim-wording rules for every outward description of this tier:
1. Never claim bare "explicit constants". The honest register: per-level
   constants OF EXPLICIT FORM — a closed formula in (ν, m) and the
   energy/enstrophy budgets, up to a single convergent lattice-kernel
   sum Σ‖k‖^(−7/2) — exported formally as compiled existence statements
   (∃ K, 0 < K).
2. Never claim a single compiled all-m flow statement. The honest form:
   for every m ≥ 1, the (unique — theorem_B_unique) eternal flow
   additionally satisfies the level-m clause; m = 0 is the trap clause
   itself (sob 0 = en). The one-flow-all-levels sentence is a
   meta-corollary through uniqueness, not a compiled theorem.
Prose amendments (delivered ≠ wave-bullet prose; frozen interfaces all
landed verbatim): W1's ladder is SUMMABILITY-monotone-in-m (no sob-mass
monotonicity lemma exists — add `sob_le_sob` only if W5 wants it); the
young clones are PRIVATE (sp_young8/16), publicize only on demand; the
"∀m package" is per-level theorems + the sob_zero_bound relabel, not a
∀m-quantified statement. sob_zero_bound is junk-symmetric by design
(summability comes from the trap at every use site).
Audit-recorded v2 item (future work, no frozen statement changes): the
dropped −ν·sob(m+1) margin + sob(m+1) ≥ sob m on mean-zero fields give
(sob m)' ≤ −(ν − K_m)·sob m, i.e. per-level EXPONENTIAL DECAY at rate
ν − K_m whenever K_m ≤ ν (a large-viscosity/small-budget subregime —
K_m ≥ 1 and scales like ν^(−7), ν^(−15)). Also recorded: K_m grows like
2^(16m) — harmless per fixed level and for spatial C^p, but any future
sum over m (C^∞-in-time analytics) must not treat K_m as tame.

## Traps carried forward

`add_pow_le` IS at the pin (Algebra/Order/Ring/Basic:119) — one recon
mission missed it under other names; use it. freq_add is PRIVATE (derive
the triangle via freq_sub + freq_neg, 4 lines, compile-verified). The
~10 private helpers to clone public are listed in the recon output
(GalerkinTrap's weighted calculus, PairingBound's b2_young* family).
Named local instances in every torus-side file. All house junk-tsum,
cast-distribution, and rename traps as catalogued in memory.
