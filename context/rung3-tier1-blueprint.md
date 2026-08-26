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
