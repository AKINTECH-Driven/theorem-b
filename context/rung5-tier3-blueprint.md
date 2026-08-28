# Rung 5 — Tier 3 blueprint: the Galerkin limit (DRAFT, pre-recon)

Status: DRAFT written 2026-08-28, immediately after `m5-complete` (37 capstones).
Statements below are CANDIDATES — they freeze only after the T3 recon wave
(workflow `t3-recon`) validates the API surface. The contract is unchanged:
kernel + `scripts/check_axioms.sh` judge everything; no new axioms; no
native_decide; honest reporting.

## What Tier 3 is

M5 delivered, for EVERY finite symmetric zero-free box `S`, a global trapped
unique Galerkin flow with constants UNIFORM in the box:

- `ns_galerkin_global_wellposed` : ∃κ ∀ν,S,c₀ (real, div-free, supported,
  κ·E₀·Z₀ < ν⁴) ∀T — existence + descent + uniqueness on [0,T];
- `ns_galerkin_global_flow` : the single eternal flow on [0,∞).

Tier 3 passes these flows through box exhaustion to the FULL Navier-Stokes
coefficient system on ℤ³ — turning the conditional Theorem B into an
unconditional small-data global existence theorem, entirely in Fourier
coefficient language (no torus measure theory on the critical path).

## The mathematical route (classical, chosen for least Lean friction)

Fix real, div-free `c₀ : (Fin 3 → ℤ) → Vel` with `E₀ := en c₀ < ∞`,
`Z₀ := ens c₀ < ∞`, `κ·E₀·Z₀ < ν⁴`.

1. **Box exhaustion.** `S_R := {k : k ≠ 0 ∧ ‖k‖_∞ ≤ R}` (finite, symmetric,
   zero-free; any exhausting sequence works). Truncate the datum to `S_R`;
   truncation only decreases en/ens (finite subsums of nonneg tsums), so the
   smallness hypothesis survives, and truncation preserves reality and
   div-freeness modewise.
2. **Uniform bounds.** The M5 flows `c^R` satisfy, for ALL t ≥ 0, uniformly
   in R: `en(c^R t) ≤ E₀`, `ens(c^R t) ≤ Z₀`, hence per mode
   `‖c^R t k‖ ≤ √E₀` and the KEY convolution bound
   `∑_l ‖c_l‖·‖freq(k−l)‖·‖c_{k−l}‖ ≤ √(en)·√(ens) ≤ √E₀·√Z₀`
   (Cauchy-Schwarz pairing ℓ² × ℓ²-with-enstrophy-weight, reindex l ↦ k−l).
   Therefore the mode-k velocity is bounded:
   `‖(c^R)'_k‖ ≤ ν‖freq k‖²·√E₀ + 2·√E₀·√Z₀` (lerayProj is 2-Lipschitz —
   already proved as `fldNorm_lerayProj_le` in GalerkinFlow.lean, private:
   RE-EXPORT). Mode-wise equicontinuity, uniform in R.
3. **Extraction.** One subsequence along which `c^R_k(t)` converges for every
   mode k, locally uniformly in t. Candidate Lean routes (recon decides):
   (a) product-space Ascoli: `Π_k C([0,T], closedBall 0 √E₀)` is compact
   metrizable (countable product of compact metrizables; (Fin 3 → ℤ) is
   countable) → sequential compactness → one subsequence for all modes;
   (b) imitate leray-hopf's own extraction if they built one (recon mission D).
   Diagonal-over-T: extract on [0,1], then [0,2], ... OR do the whole
   half-line with locally-uniform topology if Mathlib's Ascoli allows.
4. **The limit system.** Define the FULL convolution
   `convFull c k := -(∑' l, (I·dotR (c l) (freq (k−l))) • c (k−l))`
   (slot/prefactor conventions to be copied VERBATIM from convGal — recon
   mission E reports it; compatibility: for S-supported fields and k ∈ S,
   convFull = convGal's inner sum). The full system:
   `c'_k = −ν‖freq k‖²·c_k + lerayProj k (convFull c k)` for ALL k ≠ 0
   (and k = 0: mode stays 0 — or is included via freq 0 = 0 and
   lerayProj 0 conventions; decide at freeze).
5. **Limit passage.** Integral form of the mode ODE on [0,t] (FTC-2). The
   convection term converges along the subsequence: pointwise limits per
   mode + the UNIFORM TAIL BOUND `∑_{‖freq l‖>M} ‖c_l‖² ≤ Z₀/M²` (from the
   enstrophy bound) make the convolution sum converge uniformly in R —
   ε/3 with finite partial sums (discrete dominated convergence; hand-roll
   if Mathlib lacks it — recon mission C). Then dominated convergence under
   the interval integral (constant dominator), and FTC back: the limit
   solves the full system with two-sided HasDerivAt on (0,∞) (endpoint 0:
   same closed-window treatment as M5 if cheap, else Ici-interior form —
   decide at freeze; do NOT weaken silently).
6. **Trap in the limit.** For every finite F: `∑_F ‖c_k(t)‖² = lim_R ∑_F ≤ E₀`
   → `en(c t) ≤ E₀` via tsum_le_of_sum_le; same for ens. Strict smallness
   `κ·en·ens < ν⁴` propagates since the products of the limits are ≤ the
   uniform bounds κ·E₀·Z₀ < ν⁴. Reality and div-freeness pass modewise
   (closed conditions, componentwise limits).
7. **THEOREM B (unconditional, coefficient form).** ∃κ>0 ∀ν>0, ∀c₀ real,
   div-free, en/ens summable, κ·en(c₀)·ens(c₀) < ν⁴: ∃ flow c on [0,∞),
   c(0)=c₀, solving the full NS coefficient system, with
   en(c t) ≤ en(c₀), ens(c t) ≤ ens(c₀), κ·en·ens < ν⁴ for all t ≥ 0.
   (Uniqueness in the limit class is NOT claimed in Tier 3 v1 — the small-data
   uniqueness argument needs the full-system Gronwall with tails; record as
   a possible T3-W6 stretch, do not promise.)

## Wave plan

- **T3-W1 — the full system.** `TheoremB/NSFull.lean`: convFull (tsum),
  summability lemmas (reindex Equiv, CS pairing bound ≤ √en·√ens),
  compatibility with convGal on supported fields, tail bound from ens.
  Freeze after recon E.
- **T3-W2 — uniform flow estimates.** Re-export lerayProj Lipschitz; mode
  velocity bound; mode-wise Lipschitz continuity of the M5 flows uniform
  in R; truncation lemmas (en/ens decrease, smallness survives, real/div-free
  preserved).
- **T3-W3 — extraction.** The compactness wave (hardest; route fixed by
  recon A/D).
- **T3-W4 — limit passage.** Integral form, uniform convergence of the
  convection, FTC back to the ODE.
- **T3-W5 — THEOREM B.** Trap conclusions in the limit + the capstone.

## Known traps carried forward

- triMaj-style nested tsums return junk 0 on non-summable inner sums — every
  tsum in convFull carries its own summability lemma BEFORE use.
- tsum lemmas at the pin are protected `Summable.*`; `tsum_eq_sum` shape
  already used in GalerkinLocal/GalerkinFlow (ep_tsum_eq_sum pattern).
- Unascribed binders near Complex.I infer ℂ — ascribe every ∀ s : ℝ.
- Instance-path mismatches (PiLp vs WithLp): rw-then-exact, never simpa.
- fldNorm_lerayProj_le and friends are `private` in GalerkinFlow.lean —
  T3-W2 either re-proves or un-privates them (un-private is a statement-
  preserving edit, allowed; note it in the commit).
- `lake`/elan resolve from cwd — always cd into the pack.
