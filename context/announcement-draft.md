# DRAFT: A machine-checked small-data theory for 3D Navier-Stokes, from spectral to classical form

Status: DRAFT for Konstantinos's review. Not published; publishing is his
call alone. Tone targets a Zulip post (short form) with the bones of a short
paper (long form). Every claim below is scoped to what the kernel accepted;
nothing is claimed beyond it. Supersedes the M3-scoped draft of 27 Aug.

## Short form (Zulip)

We have kernel-checked, in Lean 4 over Mathlib (pin `15a89b24`, toolchain
`v4.31.0-rc2`), a small-data theory for the 3D incompressible
Navier-Stokes equations on the 3-torus that runs from an *unconditional*
existence-and-trapping theorem through uniqueness to a **classical,
pointwise** solution — 186 audited declarations (the axiom ledger:
theorems, one definition, and the compiled non-vacuity probes), every one
on exactly `{propext, Classical.choice, Quot.sound}`, none on `sorryAx`.

The object is the coefficient system on the frequency lattice `ℤ³`:

    cₖ' = −ν‖k‖² cₖ + P_k( conv(c)ₖ ),   conv(c)ₖ = −Σ_l (i c_l·(k−l)) c_{k−l},

with `P_k` the mode-wise Leray projection and the convolution a genuine
infinite sum over `ℤ³`. Write `E₀ = Σ‖c₀ₖ‖²`, `Z₀ = Σ‖k‖²‖c₀ₖ‖²`. The
standing hypothesis throughout is smallness in the form `κ·E₀·Z₀ < ν⁴`,
for a universal `κ > 0`, on mean-zero, real, divergence-free data.

What is proved, one line per layer:

- **Existence and trapping** (`theorem_B`) — a flow of the FULL system on
  every horizon: real and divergence-free throughout, with genuinely
  summable energy and enstrophy at every time (exported in the statement,
  so no `tsum` in it can be the junk value of a divergent series),
  satisfying the integral equation on the closed window and the ODE at
  every interior time, and TRAPPED — energy and enstrophy never exceed
  their initial values and the strict smallness survives.
- **Uniqueness, and one eternal flow** (`theorem_B_unique`,
  `ns_full_global_flow`) — uniqueness is unconditional in the
  enstrophy-bounded class: no smallness, no dissipation hypothesis, no
  reality assumed. The per-horizon witnesses splice into a single
  solution on `[0, ∞)`.
- **A velocity field on the torus** (`theorem_B_torus`,
  `theorem_B_torus_unique`) — the coefficient flow synthesized through
  Mathlib's `mFourierBasis` into an `L²` field satisfying calibrated
  Navier-Stokes in band-limited weak form, unique in its class.
- **Regularity, up to the classical form** (`theorem_B_sobolev`,
  `theorem_B_smooth_classical`, `theorem_B_smooth_classical_eq`) — every
  spectral Sobolev level propagates; and for data summable at EVERY
  level, the `ℤ³`-periodic lift is `C^p` in space for every `p`, `C¹` in
  time on `t > 0`, and satisfies, as ONE compiled statement,

      ∂ₜu = (ν/(2π)²)·Δu − (1/2π)(u·∇)u − ∇p

  POINTWISE — the viscous term identified with the actual Laplacian, the
  nonlinearity with the actual `(u·∇)u`, and the pressure an honest `ℓ¹`
  field whose gradient series is its compiled fiber derivative
  (`hasDerivAt_pressure_insertNth`). The two coefficients are quoted
  together on purpose: this un-rescaled lift is standard Navier-Stokes at
  viscosity `ν/(2π)` in the clock `τ = 2πt`.
- **Finite bandwidth and determining modes** (`theorem_B_bandwidth`,
  `theorem_B_modes`, `ns_full_global_flow_modes`) — the eternal flow
  keeps at most `Z₀/N²` of its energy outside the cube `‖k‖_∞ ≤ N`, for
  every `N` and forever; and two flows in the class whose low-mode defect
  (inside that cube) stays at most `δ` throughout a window synchronize
  at rate `νN² − K` down to a floor of order `δ`, with ONE constant `K`
  fixed at the class budgets before either flow is chosen.

What is and is not new, plainly. Nothing here is new mathematics: the
trap is Leray 1934 / Fujita-Kato 1964, uniqueness is
Prodi-Serrin-Ladyzhenskaya, Sobolev propagation is Foias-Temam 1989,
determining modes is Foias-Prodi 1967 in the rate form of
Hayden-Olson-Titi 2011, and **no mathematical priority is claimed for
any layer**. Nor is the method new: the axiom gate, frozen statements,
builder/auditor role split and agent doctrine are adopted from the
leray-hopf project. What is ours is the machine-checking of the
composition, hedged as follows. To our knowledge (reconnaissance 26 Aug
to 2 Sep 2026, the last pass a 41-agent prior-art audit; corrections
welcome), `theorem_B` + `theorem_B_unique` + `ns_full_global_flow` are
the first kernel-checked small-data GLOBAL well-posedness theorem for
the full 3D Navier-Stokes Fourier-coefficient system on the 3-torus: a
global strong (bounded-energy-and-enstrophy) solution, unique within the
bounded-enstrophy class on every finite horizon with no smallness or
dissipation hypothesis on the competitor, with a pointwise classical-form
lift, every Sobolev level propagated, and a rate-form determining-modes
theorem composed onto it. Two earlier machine-checked 3D Navier-Stokes
developments are strictly separate and are cited below: the first
machine-checked 3D NS EXISTENCE is leray-hopf's (weak, Leray-Hopf), and
a machine-checked 3D NS UNIQUENESS (local-in-time, mild, on `ℝ³`)
predates ours by ten days. The bare sentences "first machine-checked 3D
NS uniqueness / existence in any proof assistant" are therefore FALSE
and must not be used.

Related machine-checked work (as located on 2 Sep 2026; none re-built
by us, kernel status as reported by each author):
- **uda-lab/leray-hopf** (Tomoki Uda; Lean 4, same Mathlib pin
  `15a89b24`; Jul-Aug 2026): Leray-Hopf weak existence on `T³` and `ℝ³`,
  finite-horizon and global; kernel-only per its README; explicitly
  disclaims uniqueness and regularity. Our Galerkin/torus vocabulary and
  our verification doctrine follow its pattern.
- **HeliCorgi/ns-mns2-flowmap-bridge** (Lean 4 + Mathlib; commit
  `e8b71440`, 18/19 Aug 2026 — ten days before `theorem_B_unique`,
  877e2d7 of 28 Aug): local-in-time existence AND uniqueness of `H³`
  mild solutions on `ℝ³` within its Duhamel contract
  (`IsMildSolutionOn.unique`, `r3EndpointSafeProjectedMildSolution_unique`),
  standard-three-axiom audit file per its README; global regularity and
  small-data global theory explicitly out of scope. Missed by our 26-29
  Aug reconnaissance.
- **Miller, Vlasov mean-field derivation** (arXiv 2607.08986, Jul 2026):
  global existence and uniqueness for the nonlinear Vlasov equation,
  kernel-axiom-only — so "first machine-checked well-posedness of a
  nonlinear evolution PDE" is not ours either.
- **Armstrong-Kempe, De Giorgi-Nash-Moser in Lean** (arXiv 2604.05984,
  Apr 2026): elliptic regularity, kernel-axiom-only; not NS, but the
  earlier PDE regularity formalization.
- **navier-stokes.dev** (undated; 12 postulated axioms; no repository
  located): seen, not verifiable, not counted as prior art either way.
- Statement-only: google-deepmind/formal-conjectures PR #1457 (the
  community's periodic Clay wording, merged May 2026) and
  lean-dojo/LeanMillenniumPrizeProblems (sorry'd). Neither proves anything;
  the former is the natural alignment target for
  `theorem_B_smooth_classical_eq` and that probe has NOT been run.

The proof stack, every commit gated by the deterministic axiom check.
Independent adversarial audits were run before the tags through Tier 6
wave 4; the Tier 6 classical layer and all of Tier 7 were audited only by
their builders at tag time and independently audited POST-TAG on
2 Sep 2026 — an audit that found two statement-shape blockers in Tier 7
and one compiled-assembly gap in Tier 6, all fixed the same day and
recorded in the repository:

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
6. **Tier 4** — uniqueness by the finite-section energy method (the
   infinite sum is never differentiated) and the eternal flow, spliced
   from per-horizon witnesses with uniqueness erasing the seams.
7. **Tier 5** — the function-space bridge: synthesis into `L²` on the
   unit torus, the calibrated weak form, and uniqueness pulled back
   through coefficient extraction.
8. **Tier 6** — regularity: per-level Sobolev propagation with no
   induction on the level, then the periodic lift, its spatial `C^p` and
   time `C¹` regularity, the identification of every term of the
   equation with its classical counterpart, and their assembly into one
   compiled pointwise equation.
9. **Tier 7** — the bandwidth layer: a uniform-in-time finite-mode
   approximation, ambient energy decay at least at rate `2ν`, and
   determining modes with a threshold of explicit form (a closed formula
   up to the lattice-kernel constant, not a printable integer).

## The layers, in the order they landed

What follows is the build log, kept in the order the tiers were tagged.
Each block was written when its tier went green and is left as written;
the summary above is the current state.

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
kind), we had found no prior machine-checked uniqueness theorem for 3D
Navier-Stokes in any proof assistant. CORRECTED 2 Sep 2026: that
reconnaissance missed HeliCorgi/ns-mns2-flowmap-bridge (local-in-time
`H³` mild uniqueness on `ℝ³`, 18/19 Aug 2026). The defensible residue is
uniqueness on the 3-torus in the bounded-enstrophy class on every finite
horizon, with no smallness on the competitor; see "What is and is not
new" above.

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

UPDATE (Tier 6, 29 Aug 2026): the regularity half — 164 audited theorems.
- **`theorem_B_sobolev`** / **`ns_full_global_flow_sobolev`** — every
  spectral Sobolev norm propagates along the flow: for each `m ≥ 1`, a
  datum with `sob m` finite keeps it finite, with
  `sob m (c t) ≤ sob m c₀ · (1 + exp(K_m·t))`, `K_m` depending only on
  `(ν, m, E₀, Z₀)`. No induction on `m` — the global trap's `E₀, Z₀`
  replace all lower-order controls, so every level closes independently.
- **`theorem_B_smooth`** / **`theorem_B_smooth_classical`** — the smooth
  layer. For data whose spectrum is summable at EVERY Sobolev level, the
  eternal flow's `ℤ³`-periodic lift is `C^p` in space for every `p`, is
  `C¹` in time on `t > 0`, and satisfies Navier-Stokes in CLASSICAL
  form, POINTWISE:

      ∂ₜu = (ν/(2π)²)·Δu − (1/2π)(u·∇)u − ∇p

  with every COEFFICIENT of the equation explicit (`ν/(2π)²` and `1/2π`;
  the smallness threshold `κ` and the growth constants are compiled
  existentials of explicit form). The viscous term is identified with
  the actual Laplacian through the second spatial derivatives and the
  symbol `∑ᵢ(2πi·kᵢ)² = −(2π)²‖k‖²`; the nonlinearity with the actual
  `(u·∇)u` by a Cauchy product of absolutely convergent character series;
  and the Leray projection is split into convection minus a pressure
  gradient, the pressure an honest `ℓ¹` field carrying one weighted order
  and `∇p` its compiled fiber derivative (`hasDerivAt_pressure_insertNth`).
  The equation is ONE compiled statement, `theorem_B_smooth_classical_eq`
  (added 2 Sep 2026 after the audit noted the assembly had been prose).
  The all-levels clause is compiled for THIS ONE flow, each level's
  witness identified with the base flow through `theorem_B_unique`.

Tier-6 scope, in the wording its own audit register requires:
- Constants are **of explicit form** — closed formulas in `(ν, m)` and
  the energy/enstrophy budgets, up to a single convergent lattice-kernel
  sum `Σ‖k‖^(−7/2)`, exported as compiled existence statements. They are
  not printed numbers, and `K_m` grows like `2^(16m)`.
- **No analyticity** (`contDiff_tsum` caps at `ℕ∞`) and **no `C^∞` in
  time** (that needs a time derivative of the convection, which does not
  exist here). Both are excluded, not merely unproved.
- The coefficients `ν/(2π)²` (on `Δu`) and `1/2π` (on `(u·∇)u`) belong
  to the un-rescaled lift and must be quoted together; "physical
  viscosity" is not a well-defined phrase for it. They are consistent
  with, not contradictory to, the Tier 5 weak-form ledger: read in the
  clock `τ = 2πt` the lift is standard Navier-Stokes with viscosity
  `ν/(2π)`, Tier 5's number. Never quote either constant without its
  normalisation.

UPDATE (Tier 7, 29-30 Aug 2026; audited and corrected 2 Sep 2026):
determining modes — 186 audited declarations, tag `t7-complete`.
- **`theorem_B_bandwidth`** — along the eternal flow, the energy OUTSIDE
  the cube `‖k‖_∞ ≤ N` never exceeds `Z₀/N²`, at every time and for every
  `N > 0`. The flow stays within `Z₀/N²` in energy of its cube-`N`
  truncation, forever. (Audit record: as first tagged the statement
  quoted only three of the flow's seven clauses and was provable by the
  constant witness `c t := c₀`; the four dropped clauses — always present
  in the proof — were restored on 2 Sep and the tag re-laid.)
- **`theorem_B_modes`** — determining modes with a threshold of explicit
  form. Two flows in the enstrophy-bounded class, **with different
  initial data**, whose low-mode defect (in the cube `‖k‖_∞ ≤ N`) stays
  at most `δ` THROUGHOUT the window, satisfy

      en(u−v)(t) ≤ en(u−v)(0)·exp(−(νN² − K)·t) + νN²/(νN² − K)·δ

  for every `N` past `2ν + K < νN²`, with `K` the absorbed-pairing
  constant at the class budgets, fixed BEFORE either flow is chosen
  (re-quantified on 2 Sep 2026: as first tagged, `∃ K` sat after the
  flows, making the compiled constant formally per-pair). As `N` grows
  the floor tends to `δ`: the flow is recovered to the accuracy with
  which its low modes are known. `δ = 0` removes the floor and the defect
  decays exponentially at rate `νN² − K` — it does not vanish, and
  distinct flows do satisfy `δ = 0` (a single-mode Stokes datum above `N`
  paired with the zero flow).
- **`ns_full_global_flow_modes`** (2 Sep 2026) — the above composed onto
  two eternal small-data flows from different data, with one `K` for all
  windows, mean-zero along each flow derived rather than assumed.
- **`ns_full_global_flow_decay`** — the eternal flow's energy decays at
  least at rate `2ν`: `en(c t) ≤ en c₀ · e^(−2νt)`. Sharpness is true on
  paper (single-mode data attain it) and is not compiled.

Why the threshold reads `2ν + K < νN²` and not `K < νN²`: in this regime
every solution already decays at `2ν` unaided, so a determining-modes
statement that merely beat `0` would be describing the ambient decay and
calling it synchronization. The threshold is built into the frozen
statement, so no outward description can overstate the result without
changing it.

Tier-7 scope, and it is the important part: this is the Foias-Prodi
determining-modes theorem — classical, unconditional in 2D, conditional
in 3D. What is ours is that the small-data trap supplies the 3D
condition for all time and the composition is compiled
(`ns_full_global_flow_modes`), that the threshold is of explicit form,
and that the whole thing is machine-checked. **It is not novel in
principle, and no priority is claimed for it.** `K` is again a constant
of explicit form rather than a number, and since it carries `ν^(−15)`
the threshold `N` is astronomically large: this is a finiteness
statement, not a small count. Two further honesty notes: in the trap
class the estimate beats the ambient `2ν` decay only transiently (its
floor is at least `δ` while the ambient bound tends to zero), so its
content is the lock-on RATE; and in the enstrophy-bounded class without
smallness, where `theorem_B_modes` also applies, no decay at all is
proved, so there it is exactly the classical conditional result.

## Scope, verification, and tags

What is STILL not claimed, precisely:
- The Tier-5 weak form is quantified over band-limited (trigonometric
  polynomial) divergence-free test fields, not arbitrary smooth tests
  (their density in L² is standard and cited, not formalized into the
  statement). Tier 6 does NOT lift this caveat: its classical pointwise
  statement is about a different object — the `ℤ³`-periodic lift — and
  holds only for data whose spectrum is summable at every Sobolev level,
  not for general trap-class data.
- Identification with the leray-hopf weak solution classes (same
  Mathlib pin, interop mechanical up to conventions) remains future
  work; their scope excludes uniqueness entirely. The uniqueness clauses
  here go beyond leray-hopf, not beyond every prior formalization: see
  HeliCorgi under "Related machine-checked work".
- Endpoint derivatives: the flow satisfies the integral equation at all
  times; two-sided derivatives only at interior times.

Verification discipline: a deterministic gate accepts the build only if
`#print axioms` for all 186 audited declarations reports at most
`propext, Classical.choice, Quot.sound` and no `sorryAx`; statements
frozen at declaration, every strengthening landing as a new sibling with
the frozen statement re-verified byte-identical. Independent adversarial
audits (three to six parallel auditors) preceded every tag through Tier 6
wave 4; the Tier 6 classical layer and all of Tier 7 were self-audited by
their builders at tag time and independently audited post-tag on
2 Sep 2026. The audits drew blood at every stage, by design: M4 (a
pressureless-class scoping, answered in-wave with the Leray layer);
Tier 3 (the capstone discarding its own summability certificates — the
fix later powered Tier 4); Tier 4 and Tier 5 (the same composition-gap
pattern, existence not exporting what its uniqueness class needs);
Tier 6 (a `C¹`-in-time clause claimed by the goal but never proved, with
its lemma sitting unconsumed); and 2 Sep (the vacuous bandwidth
statement, the per-pair `K`, and the classical equation existing only as
an assembly of clauses). Every finding was fixed before, or in the case
of the post-tag audit immediately after, its tag; every finding made a
statement stronger.

Repository tags: `m1-green` → `m2-complete` → `m3-conditional-green` →
`m4-wave1..4-green` → `m5-wave1/2-green`, `m5-complete` →
`t3-theorem-b-green` → `t4-wellposedness-green` → `t5-torus-green` →
`t5-polish-green` → `t6-sobolev-green` → `t6-smooth-green` →
`t6-classical-green` → `t7-bandwidth-green` → `t7-modes-green` →
`t7-complete` → `t7-audited-green` (2 Sep 2026: the post-tag audit's
fixes; `t7-bandwidth-green` re-laid on the corrected statement). Priority, in its
only defensible form: to our knowledge (reconnaissance 26 Aug to 2 Sep
2026) the first kernel-checked small-data GLOBAL well-posedness — strong
class, unique in the bounded-enstrophy class on every finite horizon —
for the full 3D Navier-Stokes coefficient system on the 3-torus, beside
leray-hopf's earlier weak existence and HeliCorgi's earlier local mild
uniqueness on `ℝ³`; corrections welcome. No mathematical priority is
claimed for any layer, and none for the method. Before any outward
claim: build HeliCorgi and run its axiom audit ourselves, and register
the frozen capstones with Palomar or replay them through lean4checker —
priority currently rests on private git tags.

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
- Credits: Konstantinos Tsantakos (command, architecture); Claude
  (Anthropic — Fable 5 through Tier 6 and the 2 Sep audit and fixes,
  Opus 5 for Tier 7) as the proving engine under an orchestrated
  multi-agent workflow with adversarial verification; Mathlib community,
  especially the
  Ascoli, interval-integral FTC, and tsum layers this build stands on.
- Venue thought: Lean Zulip #maths first; arXiv note viable now that the
  result is unconditional; decide after Tier 4 (uniqueness) resolves or
  stalls.
