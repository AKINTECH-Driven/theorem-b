# DRAFT: A machine-checked small-data Theorem B for 3D Navier-Stokes, spectral form

Status: DRAFT for Konstantinos's review. Not published; publishing is his
call alone. Tone targets a Zulip post (short form) with the bones of a short
paper (long form). Every claim below is scoped to what the kernel accepted;
nothing is claimed beyond it. Supersedes the M3-scoped draft of 27 Aug.

## Short form (Zulip)

We have kernel-checked, in Lean 4 over Mathlib (pin `15a89b24`, toolchain
`v4.31.0-rc2`), an *unconditional* small-data existence-and-trapping theorem
for the 3D incompressible Navier-Stokes equations in spectral form on the
frequency lattice `ℤ³` of the 3-torus — 68 audited theorems, every one on
exactly `{propext, Classical.choice, Quot.sound}`.

The capstone (`theorem_B`): there is a universal constant `κ > 0` such that
for every viscosity `ν > 0` and every mean-zero, real, divergence-free
initial coefficient field `c₀ : ℤ³ → ℂ³` with summable energy
`E₀ = Σ‖c₀ₖ‖²` and enstrophy `Z₀ = Σ‖k‖²‖c₀ₖ‖²` satisfying `κ·E₀·Z₀ < ν⁴`,
on every finite horizon `[0, T]` there exists a coefficient flow of the FULL
Navier-Stokes system

    cₖ' = −ν‖k‖² cₖ + P_k( conv(c)ₖ ),    conv(c)ₖ = −Σ_l (i c_l·(k−l)) c_{k−l},

(`P_k` the mode-wise Leray projection, the convolution a genuine infinite
sum over `ℤ³`) which starts at the datum, is real and divergence-free
throughout, has genuinely summable energy and enstrophy series at every time
(exported in the statement, so no `tsum` in it can be the junk value of a
divergent series), satisfies the integral equation on the closed window and
the differential equation at every interior time, and is TRAPPED: energy and
enstrophy never exceed their initial values and the strict smallness
inequality survives.

The proof stack, each layer independently gated and adversarially audited:

1. **Tier 0** — ODE traps: forward invariance of `{κEZ < ν⁴}` by first-exit,
   and the Riccati comparison window.
2. **Tier 1** — spectral estimates on `ℤ³` tsums: `Z² ≤ E·D`, a sharp Agmon
   bound `S⁴ ≤ C·Z·D` via lattice shell counts, the ℓ¹×ℓ²×ℓ² trilinear
   majorant, and the master inequality `2B ≤ νD + (K/ν³)Z³`, closed by the
   polynomial identity `27(p+q)⁴ − 256p³q = (p−3q)²(27p²+14pq+3q²)` — no
   real root appears in any statement.
3. **Tier 2** — the conditional Theorem B composing 0×1.
4. **The Galerkin layer (M4-M5)** — the balance hypothesis DISCHARGED for
   the concrete spectral Galerkin system on every finite symmetric box:
   energy pairing exactly zero, enstrophy pairing dominated with constant
   exactly 2, reality and divergence-freeness self-propagating from data at
   `t = 0` alone; then global well-posedness of the trapped Galerkin flows —
   existence by uniform-step Picard-Lindelöf and seam-gluing induction
   (the trap re-secures the uniform bound at every seam), uniqueness by a
   defect-Gronwall, and one eternal flow per box serving all horizons.
5. **Tier 3** — the Galerkin limit: box exhaustion with trap bounds uniform
   in the box, a product-space Arzela-Ascoli extraction (one subsequence for
   all modes), dominated convergence passing each mode's integral equation
   to the limit, and Fatou-style finite-subsum arguments carrying the trap
   through. The zero mode's equation holds in the limit by mechanism, not
   fiat: divergence-freeness survives the limit and annihilates the
   zero-mode convection.

UPDATE (Tier 4, same day): both former non-claims are now CLAIMED and
kernel-checked — 84 audited theorems total:
- **`theorem_B_unique`** — uniqueness for the full system, UNCONDITIONAL
  in the enstrophy-bounded class: any two mode-continuous, divergence-free
  flows with summable energy/enstrophy series bounded by any budgets,
  satisfying the infinite-convolution integral equation from the same
  datum, agree at every time and every mode. No smallness, no dissipation
  hypothesis, no reality assumption. The proof is a finite-section energy
  method (the infinite sum is never differentiated): a box-free pairing
  bound through the lattice kernel at exponent `7/4` (summable because
  `7/2 > 3` in three dimensions), interpolation at `(1/8, 7/8)`, exact
  Young absorption into the dissipation, a Grönwall on the primitive, and
  tail sources that vanish along the box exhaustion precisely because of
  the summability certificates exported in `theorem_B`'s statement.
- **`ns_full_global_flow`** — ONE eternal solution on `[0, ∞)`: real,
  divergence-free, mode-continuous, honestly summable, satisfying the
  integral equation at every `t ≥ 0` and the ODE at every `t > 0`,
  trapped forever; per-horizon witnesses spliced with uniqueness erasing
  the seams. The exported continuity places every restriction of this
  flow back inside the uniqueness class, so the eternal flow is unique
  among its kind on every horizon.
As of our reconnaissance (28 Aug 2026, including a full sweep of the
leray-hopf repository, which proves existence but no uniqueness of any
kind), we found no prior machine-checked uniqueness theorem for 3D
Navier-Stokes in any proof assistant; corrections welcome.

UPDATE (Tier 5, next day): the function-space non-claim is now largely
CLAIMED — 101 audited theorems total:
- **`theorem_B_torus`** — the coefficient flow synthesized (via Mathlib's
  `mFourierBasis`) into a genuine velocity field on the UNIT 3-TORUS:
  global in time, L²-continuous components, a.e. real, spectrally
  divergence-free, mean-zero, with honestly summable enstrophy at every
  time (exported), satisfying the calibrated Navier-Stokes equation in
  band-limited weak form with the honest physical constants
  (`−ν(2π)²‖k‖²` dissipation, `2π`-weighted convection — independently
  re-derived from the PDE by the audit), trapped forever; the smallness
  constant transfers as `κ_torus = κ/(2π)⁶`.
- **`theorem_B_torus_unique`** — uniqueness in the torus class, pulled
  back through coefficient extraction; the existence witness inhabits
  the uniqueness class by the exported statement alone. A highlight of
  the proof: the weak-to-mode recovery tests the weak identity against
  the defect vector ITSELF (admissible because its divergence vanishes),
  collapsing uniqueness to `⟪D, D⟫ = 0`.
- Also proven (available, deliberately unwired from the capstone):
  the product-coefficient identity — the Fourier coefficient of a
  pointwise product of synthesized fields is the coefficient
  convolution — closed entirely inside L² by a twist trick.

What is STILL not claimed, precisely:
- The weak form is quantified over band-limited (trigonometric
  polynomial) divergence-free test fields, not arbitrary smooth tests
  (their density in L² is standard and cited, not formalized into the
  statement); no classical/pointwise solution concept is claimed.
- Identification with the leray-hopf weak solution classes (same
  Mathlib pin, interop mechanical up to conventions) remains future
  work; notably their scope excludes uniqueness entirely, so the
  uniqueness clauses here appear to be beyond any prior formalization.
- Endpoint derivatives: the flow satisfies the integral equation at all
  times; two-sided derivatives only at interior times.

Verification discipline: a deterministic gate accepts the build only if
`#print axioms` for all 68 capstones reports at most
`propext, Classical.choice, Quot.sound` and no `sorryAx`; statements frozen
at declaration; every commit preceded by an independent adversarial audit
(three parallel auditors at each summit). The audits drew blood twice at
summits: the M4 modeling audit caught a pressureless-class scoping that was
answered in-wave with the Leray layer, and the Tier-3 audit caught the
capstone's conclusion discarding its own summability certificates — fixed
before the tag by exporting them, which is why the statement is
junk-tsum-proof.

Repository tags: `m1-green` → `m2-complete` → `m3-conditional-green` →
`m4-wave1..4-green` → `m5-wave1/2-green`, `m5-complete` →
`t3-theorem-b-green` → `t4-wellposedness-green` → `t5-torus-green`. As of our 26-29 Aug 2026
reconnaissance we found no prior machine-checked small-data existence OR
uniqueness result for 3D Navier-Stokes in any proof assistant;
corrections welcome.

## Notes for the long form (not yet written)

- The convention-free majorant design: Tier 1 never fixes a Fourier
  normalization; all `2π` factors price into uniform constants at the
  bridge. The concrete convection carries the `−i` prefactor — the audit
  verified the i-free normalization is unphysical (vanishes without
  div-freeness).
- The two Lean-side load-bearing discoveries: (a) interval localization —
  ∀t-ODE forms are near-vacuous for constructed flows (backward blow-up),
  so the entire dynamical chain is stated on `Icc` with EventuallyEq
  transfer at interior points; (b) at this Mathlib pin, countable-product
  METRIZABILITY does not exist but first countability synthesizes, which is
  all sequential extraction needs.
- The ε/3 tail method: no summable uniform majorant exists for the
  convection limit (`Σ 1/|l|²` diverges over ℤ³), so plain dominated
  convergence/Tannery fails; the enstrophy tail bound `Σ_{|l|>M}‖c_l‖² ≤
  Z/M²` — uniform along all Galerkin flows — is what closes every limit.
- Credits: Konstantinos Tsantakos (command, architecture); Claude (Fable 5,
  Anthropic) as the proving engine under an orchestrated multi-agent
  workflow with adversarial verification; Mathlib community, especially the
  Ascoli, interval-integral FTC, and tsum layers this build stands on.
- Venue thought: Lean Zulip #maths first; arXiv note viable now that the
  result is unconditional; decide after Tier 4 (uniqueness) resolves or
  stalls.
