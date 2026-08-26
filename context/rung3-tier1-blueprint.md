# Rung 3: Tier 1 blueprint (M2) — DRAFT, pending recon reconciliation

Session of 27 August 2026. Konstantinos (command), Claude (execution).
Status: DRAFT — statements not yet frozen. The recon sweep (Mathlib pin +
leray-hopf @ e704400) may adjust the toolbox; the mathematics below is stable.

## Route decision (proposed)

Tier 1 is built **Fourier-side**: the torus never appears as a measure space.
A velocity field is its coefficient family `c : ℤ³ → ℂ³` (or per-component,
architect's call at freeze time) with mean-zero `c 0 = 0`, and every norm is a
weighted `tsum`:

| Quantity | Definition | Analytic reading |
|---|---|---|
| `E c` | `Σ_k ‖c k‖²` | energy `‖u‖²` |
| `Z c` | `Σ_k ‖k‖² ‖c k‖²` | enstrophy `‖∇u‖²` |
| `D c` | `Σ_k ‖k‖⁴ ‖c k‖²` | dissipation `‖Δu‖²` |
| `S c` | `Σ_k ‖c k‖` | sup-norm majorant `‖u‖_∞ ≤ S c` |

This dodges every missing PDE brick (no Lp on 𝕋³, no Sobolev spaces, no weak
derivatives) while keeping the estimates *exactly* the classical ones: Parseval
turns Hölder–Sobolev–interpolation into weighted-ℓ² manipulations. The bridge
from a smooth NS solution to these sums (enstrophy balance, differentiation
under the sum) is deliberately OUT of Tier 1 — it is Tier 2/3 work, matching
the gap map's "structure first".

## The lemma ladder (proposed M2 decomposition)

- **M2.1 Lattice toolbox.**
  (a) `Σ_{k≠0} ‖k‖⁻⁴ < ∞` over ℤ³ (any s > 3; 4 suffices).
  (b) tsum Cauchy–Schwarz: `Σ a_k b_k ≤ √(Σ a_k²) √(Σ b_k²)` in usable form.
  (c) Reindexing sums along the bijection `l ↦ l + k` of ℤ³.
  (d) [sharp track only] shell bounds: `Σ_{0<‖k‖≤R} ‖k‖⁻² ≤ C₁ R` and
      `Σ_{‖k‖>R} ‖k‖⁻⁴ ≤ C₂/R`.
- **M2.2 Interpolation (pure Cauchy–Schwarz).** `Z c ^ 2 ≤ E c * D c`.
  Fourier-side proof of `‖∇u‖² ≤ ‖u‖ ‖Δu‖`. Small; first candidate GREEN.
- **M2.3 Crude Agmon + crude master inequality.** `S c ≤ C √(D c)` (single
  Cauchy–Schwarz against M2.1a). Yields the Z-only trap
  `-2νD + 2|b| ≤ 0 while C²·Z < 4ν²` — a genuine, weaker a priori estimate
  and the first full-chain GREEN. Decompose-until-something-passes.
- **M2.4 Sharp Agmon.** `S c ≤ C_A (Z c)^{1/4} (D c)^{1/4}` via the low/high
  split at radius R, optimized R ~ √(D/Z), using M2.1d. The scale-critical
  ingredient the E·Z region needs.
- **M2.5 Trilinear bound.** With the convection pairing as a double sum over
  `k + l + m = 0`: `|b(u,v,w)| ≤ S u · √(Z v) · √(E w)` (ℓ¹×ℓ²×ℓ²
  convolution: CS in l after reindexing, then sum k against S u).
  Specialize `w := Δu`: `|b(u,u,Δu)| ≤ S u · √(Z u) · √(D u)`.
- **M2.6 Master inequality (Tier 1 capstone).** Compose M2.4 + M2.5 + Young
  ((4/3,4)-split): for mean-zero c and any ν > 0,
  `-2ν D c + 2 |b c| ≤ -ν D c + (C/ν³) (Z c)³`.
  Corollary via M2.2: on the region `C·E·Z ≤ ν⁴` the right side is ≤ 0 —
  the hook that Tier 2 feeds into M1's `trap_forward_invariance`.

All constants abstract (`∃ C > 0` or explicit lattice constants where free),
per the gap map: structure first, sharp constants a named later task.

## Acceptance gate

Same doctrine as M1: `scripts/check_axioms.sh` extended with the new capstone
names; GREEN iff builds and axioms ⊆ {propext, Classical.choice, Quot.sound},
no sorryAx. Statements frozen only after this blueprint is reconciled with the
recon report; until then everything here is negotiable.

## Open architect items (to resolve on recon)

1. ℂ³-valued vs three scalar components vs abstract `c : ℤ³ → V` with V an
   inner-product space (cleanest: abstract V, instantiate later).
2. Whether to align coefficient types with leray-hopf's Fourier layer now
   (Tier 4 interop) or keep Tier 1 self-contained and bridge later.
3. Whether M2.1a exists in the pin (EisensteinSeries/ZLattice) or must be
   proved from shell counting.
4. Divergence-freeness: NOT needed anywhere in M2.2–M2.6 as stated (it enters
   only in Tier 2's use of the balance identity) — confirm and record.

## Recon reconciliation (27 Aug 2026, four-sweep recon @ this pin + leray-hopf e704400)

Verified facts that shaped the freeze:

1. **𝕋³ Fourier/Parseval is STOCK**: `Mathlib/Analysis/Fourier/AddCircleMulti.lean`
   (`UnitAddTorus d`, `mFourierBasis : HilbertBasis (d → ℤ) ℂ (Lp ℂ 2 volume)`,
   Parseval `hasSum_sq_mFourierCoeff`, Fubini bridge). Period hard-wired to 1,
   probability Haar. **No derivative↔frequency lemma in dim > 1** — that layer
   (`mFourierCoeff (∂ᵢ f) n = 2πi·nᵢ·mFourierCoeff f n`) is Tier 2 critical path,
   NOT Tier 1.
2. **leray-hopf @ e704400 is dependency-viable** (identical toolchain AND Mathlib
   pin, plain single-lib lakefile) and its `viscousFormSq 1 u` IS the enstrophy
   (spectral, (2π)²|k|² weights, `Torus3 = UnitAddTorus (Fin 3)` — same type as
   Mathlib's). It has NO |k|⁴ layer, NO interpolation-type trilinear estimate,
   NO Agmon — exactly the Tier 1 content. **Decision: defer the dependency to
   Tier 2** (one-time ~46k-line compile, no olean cache, against 2.8 GiB free
   disk; their mathlib inputRev is "master" — never `lake update` with it in the
   manifest). Tier 1 is self-contained spectral with BARE ‖k‖ Euclidean weights;
   the (2π)² factors are absorbed by abstract constants at the Tier-2 bridge.
3. **Lattice sums**: `ZLattice.summable_norm_rpow` (r < -rank, subtype-indexed,
   ambient norm) is stock; the flat `(Fin 3 → ℤ)`-indexed version must be built
   as a ~50-line bridge (span ℤ of `Pi.basisFun`, `Basis.restrictScalars` /
   `equivFun`, `Equiv.summable_iff`). `tsum_norm_rpow_le` is a whole-sum bound,
   NOT a tail bound — M2.1d shell estimates remain must-build (dyadic/box count).
4. **tsum toolbox stock**: `inner_le_Lp_mul_Lq_tsum_of_nonneg` (unbundled CS),
   `lp.tsum_mul_le_mul_norm` + `Real.HolderConjugate.two_two`,
   `Summable.tsum_le_tsum`-family (SummationFilter refactor: protected dot
   names), `Summable.sum_add_tsum_subtype_compl` for threshold splits,
   `Real/NNReal.young_inequality`, `geom_mean_le_arith_mean3_weighted`.
5. **Name-drift ledger** (pin-verified): `Memℒp`→`MemLp`, `snorm`→`eLpNorm`,
   `inner_mul_le_norm_mul_norm`→`norm_inner_le_norm`,
   `Real.IsConjExponent`→`Real.HolderConjugate`; bare `tsum_le_tsum` etc. are
   now protected `Summable.*`.

## FROZEN — M2 wave 1 (statements in TheoremB/SpectralNorms.lean)

With `freq : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3)` the cast embedding and
`en/ens/dis/spec1` the E/Z/D/S tsums over a `NormedAddCommGroup V`:

- W1 `summable_inv_freq_pow_four : Summable fun k ↦ (‖freq k‖ ^ 4)⁻¹`
- W2 `ens_sq_le_en_mul_dis : c 0 = 0 → Summable (dis-term) → ens c ^ 2 ≤ en c * dis c`
- W3 `exists_spec1_sq_le_dis : ∃ C, 0 < C ∧ ∀ c, c 0 = 0 → Summable (dis-term) →
      spec1 c ^ 2 ≤ C * dis c`  (crude Agmon, on squares per M1 precedent)
- W4 `exists_spec1_pow_four_le_ens_mul_dis : ∃ C, 0 < C ∧ ∀ c, c 0 = 0 →
      Summable (dis-term) → spec1 c ^ 4 ≤ C * (ens c * dis c)`  (sharp Agmon,
      on fourth powers; the M2.1d shell lemmas are the prover's internal
      decomposition, not frozen)

M2.5 (trilinear) and M2.6 (master) freeze AFTER wave 1 is green, aligned with
leray-hopf's `galerkinConvection` slot conventions (derivative on middle slot).

Smallest next move: probe the bridge APIs, then prove W1 → W2 → W3; W4 may
carry a sorry into the first M2 commit (kept OUT of AxiomCheck until proven).

## FROZEN — M2 wave 2 (trilinear majorant + master inequality; 27 Aug 2026, full-auto session)

Design decision: M2.5 is stated for the **convention-free majorant** — real
nonneg sequences, no convection form defined in Tier 1. Any concrete pairing
(leray-hopf's `galerkinConvection`, the PDE's `∫(u·∇)v·w`) is pointwise
dominated by it via the triangle inequality, with its (2π)-factors absorbed
into constants at the Tier-2 bridge. This keeps Tier 1 free of slot/sign
conventions while remaining exactly the classical ℓ¹×ℓ²×ℓ² estimate.

- **M2.5** `triMaj (a v w : (Fin 3 → ℤ) → ℝ) : ℝ :=
    ∑' k, a k * ∑' l, ‖freq l‖ * v l * w (-(k + l))`
  `triMaj_le : (∀k, 0 ≤ a k) → (∀l, 0 ≤ v l) → (∀m, 0 ≤ w m) →
    Summable a → Summable (fun l => ‖freq l‖^2 * v l^2) → Summable (fun m => w m^2) →
    triMaj a v w ≤ (∑' k, a k) * Real.sqrt (∑' l, ‖freq l‖^2 * v l^2) * Real.sqrt (∑' m, w m^2)`
  Proof: inner Cauchy–Schwarz in `l` (the w-factor reindexed along the
  involution `l ↦ -(k+l)` of ℤ³, `Equiv.tsum_eq`), then the outer sum against
  the constant bound.
- **M2.6** `master_inequality : ∃ K, 0 < K ∧ ∀ c, c 0 = 0 → (D-summable) →
    ∀ ν, 0 < ν →
    2 * triMaj (‖c ·‖) (‖c ·‖) (fun m => ‖freq m‖^2 * ‖c m‖) ≤
      ν * dis c + K / ν^3 * ens c^3`
  — the spectral majorant form of `Ż ≤ -ν‖Δu‖² + (C/ν³)Z³` (the -2νD term and
  the Tier-2 sign conventions live on the Tier-2 side of the interface).
  Proof: instantiate M2.5 (the w-slot's square-sum is exactly `dis c`), apply
  W4 on fourth powers to get `B⁴ ≤ C·(ens c)³·(dis c)³`, then close with the
  PURE-POLYNOMIAL Young step via the SOS certificate
  `27(p+q)⁴ − 256·p³q = (p−3q)²·(27p² + 14pq + 3q²) ≥ 0`
  (p := ν·D, q := K·Z³/ν³): it yields `(p+q)⁴ ≥ (256/27)p³q ≥ 16·B⁴` for
  `K ≥ 27C/16`, and the order-reflecting fourth power finishes without any
  real root ever appearing in a statement. Verified by hand-division; nlinarith
  hint: `mul_nonneg (sq_nonneg (p - 3*q)) (positivity : 0 ≤ 27p²+14pq+3q²)`.

M2 complete = W1-W4 + M2.5 + M2.6 GREEN. Tier-2 hook recorded for M3: with W2
(`D ≥ Z²/E`), the master inequality's RHS is ≤ 0 on the region
`K·E·Z ≤ ν⁴` — the composition into M1's `trap_forward_invariance` and
`riccati_window` (with `a := K/ν³`) is M3 work on a time-parametrized
trajectory with the enstrophy-balance inequality as the standing conditional
hypothesis.

## M3 (Tier 2) — the conditional Theorem B (same session, sealed with proof)

`TheoremB/ConditionalTheoremB.lean`, both audited:

- `conditional_trap`: ∃κ (uniform in c, ν, T — it is the master constant),
  such that for any trajectory `c : ℝ → (Fin 3 → ℤ) → V` that is mean-zero
  and D-summable on `[0,T)`, with E, Z continuous/differentiable as scalar
  histories, `E' ≤ 0`, and the BALANCE hypothesis
  `Z' ≤ -2ν·D + 2·triMaj(‖c‖,‖c‖,freq²‖c‖)`:
  small data `κ·E₀·Z₀ < ν⁴` gives, for all t: the smallness persists AND
  `Z t ≤ Z 0` AND `E t ≤ E 0`.  (Discharge of M1's `hZ'cond`: master
  inequality + W2 via the product chain `K·Z³ = (K·Z)·Z² ≤ (K·Z)·(E·D) =
  (K·E·Z)·D ≤ ν⁴·D`.)
- `conditional_safety_window`: same balance hypothesis plus positive
  enstrophy: the exact Riccati-orbit bound
  `Z t² ≤ Z 0² / (1 - 2(K/ν³)Z 0² t)` inside the window — the quantitative
  safety time, via M1's `riccati_window` at `a := K/ν³`.

The conditional layer's SOLE outstanding obligation (Tier 3): discharge the
balance hypothesis from the PDE — pointwise domination of the concrete
convection pairing by `triMaj` AND its summability (nested tsums return 0 on
non-summable inner sums), plus the enstrophy-balance identity for smooth
solutions (the dim>1 derivative↔frequency layer flagged at recon).

Campaign state after this session: M0 ✅ M1 ✅ M2 ✅ M3 ✅ (conditional; per
the rung-2 map, "already a publishable, announceable first at this tier" —
announcement is the architect's call, not the machine's). Tier 3 is the
months-scale layer and a fresh brief.
