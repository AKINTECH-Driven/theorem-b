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
pointwise** solution, jointly smooth on the closed slab `ℝ³ × [0, ∞)` and,
for small data at `f = 0`, inhabiting our copy of the community's periodic
solution class (Tier 8b): 294 audited declarations (the axiom ledger:
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
- **The forced trap** (`theorem_B_forced`, `theorem_B_unique_forced`,
  `ns_full_global_flow_forced`, `forced_breakdown_threshold`): the same
  system driven by a small mean-zero, real, divergence-free force that
  enters through its energy (the squared `ℓ²` norm) only: a box
  `(Es, Zs)` with `κ_forced·Es·Zs ≤ ν⁴` and force budget `G ≤ ν²·Es`,
  `8G ≤ ν²·Zs` is never left, on every horizon and on `[0, ∞)`, unique in
  the enstrophy-bounded class; plus a breakdown threshold in the
  campaign's coefficient vocabulary. NOT a strengthening of the unforced
  chain at `g = 0`; see the Tier 8a section below.

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

Related machine-checked work (as located on 2 Sep 2026, two entries added
9 Sep 2026; none re-built by us, kernel status as reported by each author):
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
- **Alpöge-Buckmaster(-Coiculescu), forced Euler / Boussinesq / IPM
  blow-up** (Lean 4; made public 8 Sep 2026; located 9 Sep 2026):
  machine-checked finite-time singularity formation for FORCED equations
  of the Euler, Boussinesq and incompressible-porous-media family. Not
  Navier-Stokes, not small data, and the opposite direction to ours
  (blow-up under forcing, not unforced global regularity); kernel status
  as reported by its authors.
- **OpenAI, NavierStokesAndEuler** (Lean 4; public 8 Sep 2026;
  self-assessed certificate; located 9 Sep 2026): FORCED Navier-Stokes
  blow-up presented as answering the Clay statements (C)/(D) in the
  community Formal Conjectures wording, plus unforced Euler blow-up. The
  authors' assessment is their own; no independent audit is known to us,
  and we have not re-built it. Disjoint from this campaign in direction
  and in data class. Its periodic solution class
  (`NavierStokesExistenceAndSmoothnessPeriodic`) was reproduced verbatim
  on 9 Sep 2026 and elaborates at our pin (probe exit 0, the (D)
  statement itself left `sorry`); the rest state inhabits the class, so
  it is not cheaply empty. Inhabiting its `f = 0` case with
  `theorem_B_smooth_classical_eq` is NOT done: it needs the clock
  `τ = 2πt` (their `nu` is our `ν/(2π)`), a real-part bridge for our
  ℂ-valued lift, joint `C^∞` in `(x, t)` on `[0, ∞)` where we have `C^p`
  in `x` at each `t` and `C¹` in `t` on `t > 0` only, and a `derivWithin`
  at `t = 0`.
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
10. **Tier 8a**: the forced trap. A barrier lemma replacing the first-exit
    bootstrap (neither energy nor enstrophy is monotone under forcing), the
    forced Galerkin layer and its trapped eternal flows per box, the
    box-exhaustion limit with the force term passing through as a fixed
    `ℓ²` term, uniqueness with the force cancelling in the difference of two
    flows, the eternal splice, and the breakdown-threshold corollaries.
    Every wave F0 to F4 read by two independent adversarial readers
    before its commit.

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

## Tier 8a: the forced trap

UPDATE (Tier 8a, 9 Sep 2026): the box trap under a small force, in the
same coefficient vocabulary, built as pure siblings of the unforced chain
(no frozen statement edited): 226 audited declarations, tags
`t8a-forced-trap-green`, `t8a-forced-B-green` (`t8a-complete` is to be
laid on the F5 commit and was not yet laid when this was written).

The object is the same system driven mode by mode by a spectral force
`g`:

    cₖ' = −ν‖k‖² cₖ + P_k( conv(c)ₖ ) + gₖ(t),

with the force mean-zero, real, divergence-free, `ℓ²` at every time (the
summability certificate is a hypothesis of every existence capstone and
of the breakdown corollaries, not of `theorem_B_unique_forced`, and it is
load-bearing: `en (g t)` is a `tsum`, and a non-`ℓ²` force would meet any
budget with the junk value `0`), and per-mode CONTINUOUS in time on
`[0, ∞)`. The force enters through its energy `en (g t) = Σ‖gₖ(t)‖²` (the
squared `ℓ²` norm) ONLY: the enstrophy-side force pairing is taken against
the dissipation and Young-split, so no `H¹` bound on the force is needed.
The trap is a BOX `(Es, Zs)` rather than the datum's own energy and
enstrophy: with `κ·Es·Zs ≤ ν⁴`, a force budget `G ≤ ν²·Es`,
`8·G ≤ ν²·Zs`, data with `en c₀ ≤ Es`, `ens c₀ ≤ Zs`, and `en (g t) ≤ G`
at every time, the flow never leaves the box.

What is proved, one line per layer (files `TheoremB/ForcedTrap.lean`,
`ForcedGalerkin.lean`, `ForcedGalerkinFlow.lean`, `ForcedTheoremB.lean`,
`ForcedUnique.lean`, `ForcedProbe.lean`):

- **The forced conditional trap** (`forced_conditional_trap`): the Tier-2
  trap transplanted to a forced trajectory, with witness `κ_forced = 8·K`,
  `K` the master-inequality constant of `SpectralNorms.lean` (a pure
  lattice constant, not the determining-modes `K`). Under forcing neither
  energy nor enstrophy is monotone, so the first-exit bootstrap is
  replaced by a barrier lemma (`barrier_forward_invariance`: a level is
  never crossed if the derivative is nonpositive on a strip just above
  it), the one analysis brick not already in the tree. The forced Galerkin
  layer and its trapped eternal flow per box (waves F1, F2) are replays of
  the unforced ones with the force pairings Cauchy-Schwarzed.
- **Existence with the box trap** (`theorem_B_forced`): on every horizon
  `[0, T]`, a flow of the FULL forced system starting at the datum: real
  and divergence-free throughout, with summable energy and enstrophy at
  every time (exported), mode-continuous, satisfying the forced integral
  equation on the closed window and the forced ODE at every interior
  time, and never leaving the box. Per-horizon, by box exhaustion,
  Arzela-Ascoli and dominated convergence as in Tier 3; the force term
  passes through the limit as a fixed `ℓ²` term.
- **Uniqueness** (`theorem_B_unique_forced`): two mode-continuous,
  divergence-free flows on `[0, T]` from the same datum, with summable
  energy and enstrophy series bounded by any budgets, satisfying the
  forced integral equation under the same force, agree at every time and
  mode. The only hypothesis on the force is per-mode continuity on the
  window: no smallness, no reality, no mean-zero and no summability of the
  force are assumed, because the force cancels in the difference of two
  flows.
- **One eternal forced flow** (`ns_full_global_flow_forced`): a single
  flow on `[0, ∞)` with the clauses above at every `t ≥ 0` (the ODE at
  every `t > 0`), spliced from per-horizon witnesses along integer
  segments with uniqueness erasing the seams; inside the box forever.
  Uniqueness of the eternal flow itself is not a clause of the statement;
  it is the compiled corollary `eternal_forced_witnesses_agree`
  (`ForcedProbe.lean`): any two flows carrying the exported clause list
  (six of its seven clauses are used; the mode-ODE clause is not needed)
  agree on the half line.
- **A breakdown threshold, in coefficient vocabulary**
  (`forced_breakdown_threshold`, `forced_breakdown_threshold'`): the
  contrapositive of `theorem_B_forced` at the budget
  `G := min(ν²·Es, ν²·Zs/8)`: from trap-class data inside an admissible
  box, under an admissible force, if NO flow of the class stays confined
  to the box on `[0, T]`, then at some time `t ≥ 0` the force's energy
  exceeds `ν²·Es` or eight times it exceeds `ν²·Zs`. The primed form is
  the same at the natural box `(en c₀, ens c₀)` (it needs `0 < ens c₀`).
  Three audit notes in the docstring bind every reading: the hypothesis
  "no confined flow" is weaker than non-existence, and turning "a flow
  leaves the box" into it passes through `theorem_B_unique_forced`; the
  time in the conclusion is `∃ t ∈ Ici 0`, not localised to the horizon;
  and at `T = 0` the antecedent is always false, so `T = 0` is never to be
  cited.
- **The probes** (`ForcedProbe.lean`, nine gated declarations): for every
  `κ, ν > 0` a NONZERO datum and a NONZERO `ℓ²` force sit strictly inside
  the four box and force thresholds and inside the smallness threshold
  (`probe_forced_joint_hypotheses_strict`), and for every `ν > 0` there
  is such a pair on which both capstones fire
  (`probe_forced_capstones_fire_jointly`); the line force (unit shear on
  every mode `(n, 0, 0)`) meets every energy budget through the junk value
  and is rejected by the summability certificate alone
  (`probe_line_force_fails_only_certificate`); the constant zero witness
  passes four of the five non-equation clauses (the initial-condition
  clause is not stated) and fails each equation clause independently, and at `g = 0` a constant shear fails the ODE clause for
  every `ν > 0` (`probe_constant_witness_fails_equation_clauses`,
  `probe_constant_witness_fails_ode_unforced`); the force disjunct of the
  breakdown threshold is load-bearing, the corollary with its conclusion
  weakened to `False` being refuted for every candidate `κ`
  (`probe_no_confined_flow_inhabited`,
  `forced_breakdown_threshold_without_budget_fails`); and the F3-to-F4
  seam is compiled (`eternal_forced_flows_agree`,
  `eternal_forced_witnesses_agree`). Every witness except the line force
  of Probe 2 is a two-mode real shear on `{e₁, −e₁}`, the cheapest field
  with vanishing full convection.

What is NOT claimed, precisely:
- The breakdown threshold is a statement in the campaign's COEFFICIENT
  vocabulary. It is NOT the community's
  `navier_stokes_breakdown_periodic`, NOT its negation, and NOT a
  real-space statement: no velocity field, no pressure, no smoothness
  class and no time derivative of a physical field appears in it.
- At `g = 0` the forced chain is NOT a strengthening of the unforced one
  and must never be described as one: `κ_forced = 8·K` where the unforced
  trap has `K`, the smallness `κ·Es·Zs ≤ ν⁴` is non-strict, and the box
  `(Es, Zs)` is a stronger energy hypothesis than the frozen
  `κ·en c₀·ens c₀ < ν⁴`. The only compiled direction between the two
  chains is frozen ⇒ forced clause list at `g = 0`
  (`probe_forced_zero_feeds_frozen`,
  `probe_frozen_flow_inhabits_forced_clauses`).
- Forces are per-mode continuous in time; `L¹` or merely measurable
  forcing is out of scope. No `H¹` or sup-norm bound on the force is
  needed at the capstone level, and none is exported. No decay of the
  force, no attractor, and no forced Sobolev, smooth or classical layer.
- The thresholds are of explicit form, exported as compiled existentials,
  not numbers: `κ_forced = 8·K` is a closed formula up to the
  lattice-kernel sum, and the force thresholds `ν²·Es`, `ν²·Zs/8` are
  literal expressions. The `∃ κ` of the existence theorem and of the
  corollary are unlinked by statement and linked by proof, the house
  pattern.
- No priority is claimed for any of it. Nothing in Tier 8a is new
  mathematics: it is the classical forced small-data (small Grashof
  number) theory carried through a Galerkin approximation. Textbook
  sources, named as references and not verified against, chapter numbers
  unverified: Temam, Navier-Stokes Equations, Ch. III;
  Robinson-Rodrigo-Sadowski, The Three-Dimensional Navier-Stokes
  Equations, Ch. 6-7; Constantin-Foias, Navier-Stokes Equations, Ch. 10;
  Foias-Manley-Rosa-Temam, Navier-Stokes Equations and Turbulence, Ch. II.
  The forced file headers themselves disagree on two of these
  (`ForcedTrap`, `ForcedGalerkin` and `ForcedGalerkinFlow` cite
  Robinson-Rodrigo-Sadowski Ch. 6, the latter two also Constantin-Foias
  Ch. 6; `ForcedTheoremB` and `ForcedUnique` cite Ch. 6-7 and Ch. 10).

Relation to OpenAI's forced blow-up (8 Sep 2026; see "Related
machine-checked work"): the two results are complementary halves of the
forced periodic picture in the informal sense only. Theirs, as its authors present it, is that a
force can drive a periodic Navier-Stokes solution to breakdown; ours is
that a small force cannot drive small data out of the trap, and the
breakdown threshold is the quantitative form of the sentence "the force
has to push the fluid out of the trap": from trap-class data, a forced
breakdown in our class has to be driven past `ν²·Es` or `ν²·Zs/8` in force
energy at some time. Said plainly, at Tier 8a the two lived in different vocabularies,
their real-space community solution class against our coefficient system,
and they had NOT been composed. Tier 8b (below) changes exactly one thing:
the tree now carries OUR COPY of the community's periodic solution class
and inhabits it at `f = 0` with the small-data flow. Nothing about their
force, their blow-up or their breakdown statement is mentioned, derived,
refuted or aligned; both upstream `sorry`s are untouched.

Verification of the tier: every wave F0 to F4 passed two independent
adversarial readers BEFORE its commit, the rule Tier 7 did not meet (the
record is the commit messages; the persisted audit directories hold gate
reruns and probe files, not verdict files); the
readers' probes are persisted outside the tree and the essential ones are
now compiled in `ForcedProbe.lean`. Tags: `t8a-forced-trap-green` (waves
F0 and F1, `b25367e`), `t8a-forced-B-green` (F3, with the two F4 capstones
`theorem_B_unique_forced` and `ns_full_global_flow_forced` delivered early
in `ForcedTheoremB.lean`, `eda7da6`), `t8a-complete` (to be laid on the
F5 commit; laid on `2a4036b`). Gate GREEN 226/226 at that commit.

## Tier 8b: time-smoothness, and the community class inhabited

UPDATE (Tier 8b, 9 to 10 Sep 2026; PROPOSED WORDING, the user's call, per
rule 6 of the Tier 8 blueprint's audit register): the eternal small-data
flow is `C^∞` in time on the CLOSED half-line, jointly `C^∞` in `(x, t)`
on the closed slab `ℝ³ × [0, ∞)` together with its pressure, and, read
back as a real velocity and pressure in the clock `τ = t/(2π)`, it
inhabits OUR COPY of the community's periodic solution class at `f = 0`:
294 audited declarations, tags `t8b-time-smooth-green`,
`t8b-joint-smooth-green`, `t8b-community-green`. Files
`TheoremB/TimeSmooth.lean`, `WithinSeries.lean`, `JointSmooth.lean`,
`CommunityClass.lean`.

The proposed sentence: for data in the campaign's small class, OUR COPY of
the community's periodic solution class
`NavierStokesExistenceAndSmoothnessPeriodic (ν/(2π)) u₀ 0 v p` is
inhabited by the eternal flow (compiled); this is the conclusion of the
upstream positive statement restricted to that data class with `f = 0`;
both upstream statements are untouched.

What is proved, one line per wave:

- **Time-smoothness** (`theorem_B_time_smooth`, wave W1): the twenty
  clauses of the classical layer re-exported verbatim, plus a derivative
  chain `D` with `D 0 = c`, the Leibniz recurrence
  `D (n+1) = −ν‖k‖²·D n + P_k(S n)` with the Leibniz convection sums `S`
  exported alongside, each `D n` differentiating to `D (n+1)` on `t > 0`
  and having the right derivative `D (n+1) 0` within `[0, ∞)` at `t = 0`,
  continuous and in every weighted-`ℓ¹` window class at every order; and
  every mode `t ↦ cₖ(t)` is `C^∞` in time on the closed half-line. The
  route is the textbook bootstrap (differentiate the mode equation; the
  `n`-th derivative satisfies a Leibniz recurrence; weighted `ℓ¹` closes
  under the three operations). `∞` is `(⊤ : ℕ∞)`, not `ω`: no
  analyticity.
- **Joint smoothness on the closed slab** (`theorem_B_joint_smooth`, wave
  W2): the same flow, the twenty-two clauses re-exported, plus every
  weighted-`ℓ¹` order of the pressure and joint `C^∞` in `(x, t)` on
  `ℝ³ × [0, ∞)` (a `ContDiffOn` on the closed slab, not on its interior)
  of the velocity lift, component by component, and of the pressure lift.
  The engine is a within-convex Weierstrass M-test for series of functions
  (`TheoremB/WithinSeries.lean`, `import Mathlib` only): Mathlib's
  uniform-limit derivative theorem is open-set only at the pin, and no
  within-set variant exists there (grep-verified); the within-set form is
  absent from Mathlib, not new mathematics, and is a PR candidate.
- **The community class** (`theorem_B_community_periodic_flow` and
  `theorem_B_community_periodic`, waves W3 and W4): the six definitions of
  the class are copied into `TheoremB.Community` in the wording of
  google-deepmind/formal-conjectures as adapted in OpenAI's Comparator
  file; declaration by declaration with comments stripped the copy is
  identical to the upstream file except in exactly two places, the
  namespace and the `local notation` for the divergence (a claim that the
  namespace is the sole difference would be false and is not made); the
  upstream file is not imported. The pinned capstone re-exports the twenty
  classical clauses and adds one: the class at viscosity `ν/(2π)` is
  inhabited by `vReal c := (x, τ) ↦ Re u(x, 2πτ)` and
  `pReal c := (x, τ) ↦ 2π·Re p(x, 2πτ)` with the zero force. The bare
  capstone is the community's own shape: for every `ν' > 0` and every
  datum `u₀Real c₀` with `c₀` summable at every Sobolev level, mean-zero,
  real, divergence-free and `κ·en c₀·ens c₀ < (2πν')⁴`, the datum meets
  `InitialVelocityConditionPeriodic`, the zero force meets
  `ForceConditionPeriodic`, and there exist `v`, `p` in
  `NavierStokesExistenceAndSmoothnessPeriodic ν' (u₀Real c₀) 0 v p`.
  Existence only: the class carries no uniqueness clause; uniqueness of
  the coefficient flow behind `vReal c` is `theorem_B_unique`, through the
  first seven clauses of the pinned form. The real-part bridge and the
  clock change are textbook.

What this does and does not say about the upstream file. The upstream
file carries two statements, both `sorry`: the positive statement
`navier_stokes_existence_and_smoothness_periodic` (for every `ν > 0` and
every smooth, divergence-free, one-periodic datum there exist `v`, `p` in
the class at `f = 0`) and the breakdown statement
`navier_stokes_breakdown_periodic`. Our bare capstone is literally the
positive statement's conclusion restricted to the data class
`u₀ = u₀Real c₀` with the smallness condition above. It says nothing about
the positive statement for general data, nothing about the breakdown
statement, and it touches neither `sorry`. The class is inhabited for
trap-class data at `f = 0` only.

Probes in the tree (registered and gated): for every `ν' > 0` the bare
capstone fires on a NONZERO admissible datum; the rest velocity is not a
witness for nonzero data; under the class's `velocity_smooth` its
`derivWithin` and `fderiv` are genuine derivatives, not junk values; the
time-constant velocity `v x t := u₀ x` is excluded on the shear datum for
every `ν' ≠ 0` (at `ν' = 0` the stationary shear with `p = 0` solves
Euler, so the hypothesis is necessary); the derivative chain of the
time-smoothness capstone is pinned by its clauses (at most one chain per
flow); the within-convex engine recovers Mathlib's `contDiff_tsum` at
`s = univ`.

Constants: `κ` and the inherited Sobolev growth constants are of explicit
form, exported as compiled existentials; the window constants of the
time-derivative chain and the majorants of the slab lemma are untracked
existentials produced by the Leibniz induction. No numeric value of any
constant is claimed.

Textbook sources for the bootstrap and the M-test, named as references and
not verified against, chapter numbers unverified: Temam, Navier-Stokes
Equations, Ch. III; Robinson-Rodrigo-Sadowski, The Three-Dimensional
Navier-Stokes Equations, Ch. 6-7; Constantin-Foias, Navier-Stokes
Equations, Ch. 10.

Verification of the tier: every wave W1 to W4 passed two independent
adversarial readers BEFORE its commit (statement shape and vacuity; proof
and pin), with a reconnaissance probe compiled at the pin before each
build, every frozen statement checked byte-identical to the blueprint by
the builder, both readers and the orchestrator with independent
extractors, and the readers' probes persisted outside the tree with the
essential ones landed and gated. Gate GREEN 294/294 at the W4 commit.

Priority is not claimed for anything in this tier; nothing here is new
mathematics. The machine-checked Navier-Stokes work it sits beside is
listed under "Related machine-checked work" (leray-hopf, HeliCorgi,
Miller, OpenAI, Alpöge-Buckmaster); none of it is composed with,
reproduced by, or superseded by anything here.

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
  times; two-sided derivatives only at interior times. At Tier 8b the
  right derivative at `t = 0` within `[0, ∞)` is compiled for every mode
  and for the lifted velocity (that is what the community class asks
  for); nothing two-sided is claimed at the endpoint.

Verification discipline: a deterministic gate accepts the build only if
`#print axioms` for all 294 audited declarations reports at most
`propext, Classical.choice, Quot.sound` and no `sorryAx`; statements
frozen at declaration, every strengthening landing as a new sibling with
the frozen statement re-verified byte-identical. Independent adversarial
audits (three to six parallel auditors) preceded every tag through Tier 6
wave 4; the Tier 6 classical layer and all of Tier 7 were self-audited by
their builders at tag time and independently audited post-tag on
2 Sep 2026. Tier 8a returned to the pre-commit rule: every wave F0 to F4
passed two independent adversarial readers before its commit, with the
probes persisted outside the tree and the essential ones compiled in
`ForcedProbe.lean`; Tier 8b kept that rule for every wave W1 to W4, with a
reconnaissance probe compiled before each build. The audits drew blood at
every stage, by design: M4 (a
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
fixes; `t7-bandwidth-green` re-laid on the corrected statement) →
`t8a-forced-trap-green` → `t8a-forced-B-green` → `t8a-complete` (9 Sep
2026: Tier 8a, the forced trap; laid on the F5 commit `2a4036b`, which
adds `ForcedProbe.lean`) → `t8b-time-smooth-green` →
`t8b-joint-smooth-green` → `t8b-community-green` (9 to 10 Sep 2026:
Tier 8b, time-smoothness, joint smoothness on the closed slab, and the
community class inhabited at `f = 0`). Priority, in its
only defensible form: to our knowledge (reconnaissance 26 Aug to 2 Sep
2026) the first kernel-checked small-data GLOBAL well-posedness — strong
class, unique in the bounded-enstrophy class on every finite horizon —
for the full 3D Navier-Stokes coefficient system on the 3-torus, beside
leray-hopf's earlier weak existence and HeliCorgi's earlier local mild
uniqueness on `ℝ³`; corrections welcome. No mathematical priority is
claimed for any layer, and none for the method. Before any outward
claim: build HeliCorgi and run its axiom audit ourselves, and register
the frozen capstones with Palomar. The kernel replay through the
toolchain's `leanchecker` is done (12 Sep 2026: all 60 imported modules,
exit 0, empty output, per-module table in
`context/leanchecker-replay-2026-09-12.md`; the imports are not replayed,
and the umbrella module, which declares nothing, exceeded this machine's
memory). Priority currently rests on private git tags.

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
