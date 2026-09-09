# Theorem B: small-data global well-posedness for 3D Navier-Stokes on the torus, machine-checked in Lean 4

This repository is a Lean 4 / Mathlib formalization of a small-data theory for the
three-dimensional incompressible Navier-Stokes equations on the unit 3-torus, stated and
proved in Fourier coefficients. Starting from an unconditional existence-and-trapping
theorem for the full (infinite-convolution) coefficient system on the lattice `ℤ³`, the
development proves uniqueness in the enstrophy-bounded class, splices one eternal flow on
`[0, ∞)`, synthesizes it into an `L²` velocity field on the torus, propagates every
spectral Sobolev level, lifts the flow to a `ℤ³`-periodic field on `ℝ³` that satisfies the
classical equation pointwise, and adds energy decay, finite bandwidth, and a rate-form
determining-modes theorem on top. Tier 8a carries the trap under a small mean-zero, real,
divergence-free force that enters through its energy only, with uniqueness, one eternal
forced flow, and a breakdown threshold stated in the same coefficient vocabulary.

Every audited declaration is accepted by a deterministic axiom gate: the kernel reports
exactly `propext`, `Classical.choice`, `Quot.sound`, and never `sorryAx`.

Nothing here is new mathematics. See "Scope and non-claims" and "Related work" before
quoting any of it.

## Pin

| What | Value | Source |
|------|-------|--------|
| Lean toolchain | `leanprover/lean4:v4.31.0-rc2` | `lean-toolchain` |
| Mathlib | `15a89b2468bc01f1a6230d6e49ef5efc5286e502` (`15a89b24`) | `lake-manifest.json` (`lakefile.toml` requires `15a89b2468bc`) |

The build is only claimed at this pin. Moving either component is a re-verification event.

## Build and gate

Prerequisites: [`elan`](https://github.com/leanprover/elan). The toolchain is selected by
`lean-toolchain`; Mathlib is fetched by Lake at the manifest revision (a Mathlib cache
download via `lake exe cache get` is the usual shortcut, and is not required).

```sh
lake build                     # builds the TheoremB library (default target)
bash scripts/check_axioms.sh   # builds, then runs the axiom audit
```

The gate (`scripts/check_axioms.sh`) rebuilds the project, compiles `AxiomCheck.lean`,
and prints `#print axioms` for every audited declaration. It passes if and only if every
line reports at most `propext`, `Classical.choice`, `Quot.sound` and no `sorryAx`. The
script reports; it never repairs.

Expected result: the final line `GATE: GREEN`, preceded by the output of the 265
`#print axioms` commands in `AxiomCheck.lean` (theorems, one definition, and the
compiled non-vacuity probes), each on exactly the three kernel axioms. Any other outcome
is `GATE: RED` with exit status 1. In the campaign notes this state is written
"GREEN 265/265"; it was recorded on 9 Sep 2026 at the Tier 8b wave W2 state, the gate
having read 186/186 at `82a9ab6` (tag `t7-audited-green`, 2 Sep 2026), grown by one
Tier 8a wave at a time (190, 199, 208, 215, 217, 226 at `2a4036b`, tag `t8a-complete`),
by the Tier 8b wave W1 (22 frozen theorems and 3 chain-pinning probes, 251 at `0efba80`,
tag `t8b-time-smooth-green`), and by the Tier 8b wave W2 (14 frozen theorems, 265).

## Capstone theorems

Names are as declared (namespace `TheoremB`); the one-line statements are condensed from
the docstrings in the files named. Throughout, `Vel := EuclideanSpace ℂ (Fin 3)`, a
coefficient field is `(Fin 3 → ℤ) → Vel`, `freq k` is the raw lattice vector,
`en`/`ens` are the energy and enstrophy sums, and the standing smallness hypothesis is
`κ · en c₀ · ens c₀ < ν⁴` for a universal `κ > 0` exported as a compiled existential.

| Theorem | File | Statement (one line) |
|---------|------|----------------------|
| `theorem_B` | `TheoremB/TheoremBGlobal.lean` | Unconditional small-data existence on every finite horizon `[0, T]` for the full coefficient system: a flow starting at the datum, real and divergence-free, with genuinely summable energy and enstrophy at every time (exported), satisfying the infinite-convolution integral equation on the closed window and the ODE at every interior time, trapped (energy and enstrophy never exceed their initial values, strict smallness survives). Per-horizon: the witness may depend on `T`. |
| `theorem_B_unique` | `TheoremB/FullUnique.lean` | Uniqueness, unconditional in the enstrophy-bounded class: two mode-continuous, divergence-free flows on `[0, T]` from the same datum, with summable energy and enstrophy series bounded by any budgets `E, Z`, satisfying the full integral equation, agree at every time and mode. No smallness, no dissipation hypothesis, no reality assumed. |
| `ns_full_global_flow` | `TheoremB/FullUnique.lean` | One flow on `[0, ∞)`: starts at the datum, real, divergence-free, honestly summable energy and enstrophy at every time, integral equation at every `t ≥ 0`, ODE at every `t > 0`, trapped forever. Its exported mode continuity places every restriction inside the `theorem_B_unique` class. |
| `theorem_B_torus` | `TheoremB/TheoremBTorus.lean` | A velocity field `u : ℝ → Fin 3 → L2T3` on the unit 3-torus, global in time, `L²`-continuous components, a.e. real, spectrally divergence-free, mean-zero, energy and spectral enstrophy below their initial values forever, satisfying calibrated Navier-Stokes in band-limited weak form (`−ν(2π)²‖k‖²` dissipation, `2π`-weighted convection) against every finitely supported divergence-free test coefficient field; smallness `κ_t · ‖u₀‖² · ((2π)² Z₀) < ν⁴`. |
| `theorem_B_torus_unique` | `TheoremB/TheoremBTorus.lean` | Two members of the torus class (`L²`-continuous, spectrally divergence-free, mean-zero, enstrophy-budgeted, calibrated weak equation) from the same initial field agree at every time. |
| `theorem_B_sobolev` | `TheoremB/TheoremBSobolev.lean` | `theorem_B` with Sobolev persistence: for each `m ≥ 1` and level-`m` summable data, the witness keeps `sob m (c t) ≤ sob m c₀ · (1 + e^{KT})` with per-time level-`m` summability, `K` depending only on `(ν, m, en c₀, ens c₀)`. |
| `ns_full_global_flow_sobolev` | `TheoremB/TheoremBSobolev.lean` | The eternal flow with the level-`m` clause: for each fixed `m ≥ 1`, `sob m (c t) ≤ sob m c₀ · (1 + e^{Kt})` for all `t ≥ 0`, one horizon-uniform `K`. Per-`m` statement; all levels for the same flow follow through `theorem_B_unique`. |
| `theorem_B_smooth_classical` | `TheoremB/TheoremBSmooth.lean` | For data summable at every Sobolev level: the eternal flow's `ℤ³`-periodic lift is `C^p` in space for every `p`, differentiable in time at every point for `t > 0` with continuous time derivative, has second spatial fiber derivatives, the viscous term is `(ν/(2π)²)·Δu`, the pressure is `ℓ¹` with one weighted order, the Leray projection is convection minus pressure gradient mode by mode, and the convection is `−(1/2π)(u·∇)u` (nineteen clauses). |
| `theorem_B_smooth_classical_eq` | `TheoremB/ClassicalEquation.lean` | The same flow, all nineteen clauses re-exported, satisfies at every component `j`, torus point `x`, and `t > 0`, as one `HasDerivAt` in time: `∂ₜu_j = (ν/(2π)²)(Σᵢ ∂ᵢ²u)_j − (1/2π)(Σᵢ uᵢ ∂ᵢu_j) − ∂_j p`, each piece spelled out in full. |
| `theorem_B_time_smooth` | `TheoremB/TimeSmooth.lean` | The same flow, all twenty clauses of `theorem_B_smooth_classical_eq` re-exported verbatim, plus (clause 21) a derivative chain `D` with `D 0 = c`, the Leibniz recurrence `D (n+1) = −ν‖k‖²·D n + P_k (S n)` with `S n = Σ_{i+j=n} C(n,i)·convBil (D i) (D j)` exported alongside, each `D n` differentiating to `D (n+1)` on `t > 0`, with the right derivative `D (n+1) 0` within `Ici 0`, continuous on `Ici 0`, and in every weighted-ℓ¹ window class at every order (the same for `S n`); and (clause 22) every mode `t ↦ c t k` is `C^∞` in time on the CLOSED half-line `Ici 0`. Time only: joint smoothness in `(x, t)` is not claimed here. `∞` is `(⊤ : ℕ∞)`, not `ω`: no analyticity. |
| `theorem_B_joint_smooth` | `TheoremB/JointSmooth.lean` | The same flow, all twenty-two clauses of `theorem_B_time_smooth` re-exported verbatim, plus (clause 23) the pressure coefficients have every weighted-ℓ¹ order at every `t ≥ 0`, (clause 24) for every component `j` the velocity lift `(x, t) ↦ uLift j (c t) x` is `C^∞` jointly in `(x, t)` on the CLOSED slab `ℝ³ × [0, ∞)` (`ContDiffOn ℝ ∞ … (univ ×ˢ Ici 0)`), and (clause 25) the pressure lift `(x, t) ↦ pLift (c t) x` is `C^∞` jointly on the same closed slab. The engine is the Mathlib-only within-convex tsum theory of `TheoremB/WithinSeries.lean` (absent from Mathlib at the pin, grep-verified, not new mathematics). `∞` is `(⊤ : ℕ∞)`, not `ω`: no analyticity. |
| `ns_full_global_flow_decay` | `TheoremB/DecayFlow.lean` | The eternal flow additionally satisfies `en (c t) ≤ en c₀ · exp(−2νt)` for every `t ≥ 0`. The upper bound is compiled; sharpness is not. |
| `theorem_B_bandwidth` | `TheoremB/Bandwidth.lean` | The eternal flow, all seven clauses quoted, additionally has energy outside the cube `‖k‖_∞ ≤ N` at most `ens c₀ / N²`, for every `N > 0` and every `t ≥ 0`. |
| `theorem_B_modes` | `TheoremB/DeterminingModes.lean` | Determining modes: for class budgets `(ν, E, Z)` there is one `K > 0`, fixed before any horizon, tolerance, or pair of flows, such that for every `N` with `2ν + K < νN²`, two enstrophy-bounded flows (different data allowed) whose low-mode defect stays at most `δ` on `[0, T]` satisfy `en(u−v)(t) ≤ en(u−v)(0)·exp(−(νN² − K)t) + νN²/(νN² − K)·δ`. |
| `ns_full_global_flow_modes` | `TheoremB/ModesFlow.lean` | The above composed onto two eternal small-data flows from different data, every clause of `ns_full_global_flow` quoted for each plus the derived mean-zero clause, with one `K` for all windows. |
| `theorem_B_forced` | `TheoremB/ForcedTheoremB.lean` | Theorem B under a small force. For a box `(Es, Zs)` with `κ·Es·Zs ≤ ν⁴`, a force budget `G ≤ ν²·Es`, `8·G ≤ ν²·Zs`, mean-zero, real, divergence-free data with summable energy and enstrophy series inside the box, and a mean-zero, real, divergence-free, per-mode-continuous force on `[0, ∞)` whose energy series is summable at every time and bounded by `G`: on every `[0, T]` a flow starting at the datum, real and divergence-free, with honestly summable energy and enstrophy, mode-continuous, satisfying the forced integral equation on the closed window and the forced ODE at interior times, and staying inside the box. Per-horizon. Its `κ` is `8·K` and the smallness is non-strict, so at `g = 0` this is not a strengthening of `theorem_B`. |
| `theorem_B_unique_forced` | `TheoremB/ForcedTheoremB.lean` | Uniqueness for the forced integral equation in the enstrophy-bounded class: two mode-continuous, divergence-free flows on `[0, T]` from the same datum, with summable energy and enstrophy series bounded by any budgets, under the same per-mode-continuous force, agree at every time and mode. No smallness, no reality, and no hypothesis on the force beyond its per-mode continuity on the window. |
| `ns_full_global_flow_forced` | `TheoremB/ForcedTheoremB.lean` | One forced flow on `[0, ∞)`: starts at the datum, real, divergence-free, honestly summable, mode-continuous, forced integral equation at every `t ≥ 0`, forced ODE at every `t > 0`, inside the box forever. Uniqueness of the eternal flow is not a clause; it is the compiled corollary `eternal_forced_witnesses_agree` in `TheoremB/ForcedProbe.lean`. |
| `forced_breakdown_threshold` | `TheoremB/ForcedUnique.lean` | Breakdown threshold in the campaign's coefficient vocabulary, the contrapositive of `theorem_B_forced` at `G := min(ν²·Es, ν²·Zs/8)`: from trap-class data inside an admissible box, under a mean-zero, real, divergence-free, ℓ², per-mode-continuous force, if no flow of the class stays confined to the box on `[0, T]`, then at some `t ≥ 0` the force's energy exceeds `ν²·Es` or eight times it exceeds `ν²·Zs`. The hypothesis is weaker than non-existence; the time is not localised to the horizon; `T = 0` is vacuous. Not the community's `navier_stokes_breakdown_periodic`, not its negation, not real-space. The primed form `forced_breakdown_threshold'` is the same at the natural box `(en c₀, ens c₀)`. |

Both `theorem_B_smooth_classical` and its `_eq` sibling take data with
`∀ m, Summable (fun l => ‖freq l‖^(2m) · ‖c₀ l‖²)`; the lift is `uLift`, the pressure
comes from `pressureCoeff`.

## Repository layout

- `TheoremB.lean`: the library root; imports every module below.
- `TheoremB/`: the development, roughly in build order. Tier 0 ODE traps
  (`RiccatiTrap`); spectral estimates and the conditional theorem (`SpectralNorms`,
  `ConditionalTheoremB`); the Galerkin system and its trapped flows (`NSGalerkin`,
  `GalerkinTrap`, `GalerkinLocal`, `GalerkinFlow`, `RealityProp`); the box-exhaustion
  limit (`ModeExtraction`, `FlowBounds`, `LimitPassage`, `LimitHelpers`,
  `ConvContinuity`, `TheoremBGlobal`); uniqueness and the eternal flow
  (`LatticeKernel`, `DefectCalculus`, `PairingBound`, `TailBounds`, `FullUnique`);
  the torus bridge (`TorusSynthesis`, `TorusStructure`, `SpectralWeak`, `CoeffExtract`,
  `TheoremBTorus`, `PhysicalPairing`, `TestSeparation`, `LerayHopfVocab`); Sobolev
  propagation (`SobolevNorms`, `SobolevPairing`, `SobolevTrap`, `TheoremBSobolev`);
  the classical lift (`ContinuousRep`, `PeriodicLift`, `TimeLayer`, `Calibration`,
  `Nonlinearity`, `TheoremBSmooth`, `ClassicalEquation`); Tier 7 (`EnergyDecay`,
  `Bandwidth`, `WindowDecay`, `EnergyIntegrable`, `ModesWindow`, `DeterminingModes`,
  `ModesFlow`, `ModesProbe`, `GalerkinDecay`, `DecayFlow`); Tier 8a, the forced trap
  (`ForcedTrap`, `ForcedGalerkin`, `ForcedGalerkinFlow`, `ForcedTheoremB`, `ForcedUnique`,
  and the gated probes `ForcedProbe`); Tier 8b, time-smoothness of the eternal flow
  (`TimeSmooth`, wave W1), the Mathlib-only within-convex series engine (`WithinSeries`,
  wave W2, a PR candidate) and joint smoothness on the closed slab (`JointSmooth`, W2).
- `AxiomCheck.lean`: the audited-declaration ledger (265 `#print axioms` lines).
- `scripts/check_axioms.sh`: the gate.
- `context/`: campaign blueprints (`rung*-blueprint.md`), the announcement draft, the
  upstreaming dossier, and the discrete-twin skeleton (`NSSkeleton.lean`).
- `M1-HANDOFF.md`: the original Tier 0 handoff brief, kept as history.

## Scope and non-claims

- **Small data only.** Every existence, regularity, decay and bandwidth statement
  assumes `κ · E₀ · Z₀ < ν⁴` on mean-zero, real, divergence-free data. Uniqueness
  (`theorem_B_unique`, `theorem_B_torus_unique`, `theorem_B_modes`) is the exception:
  it is stated in the enstrophy-bounded class with no smallness on the competitor.
- **The forced chain (Tier 8a) is small data under a small force, on a box.**
  `theorem_B_forced`, `ns_full_global_flow_forced` and the breakdown threshold assume a
  box `(Es, Zs)` with `κ_forced·Es·Zs ≤ ν⁴` (non-strict; `κ_forced = 8·K_master`, with
  `K_master` the master-inequality constant of `TheoremB/SpectralNorms.lean`, not the
  determining-modes `K`), a force budget
  `G ≤ ν²·Es`, `8·G ≤ ν²·Zs`, and a mean-zero, real, divergence-free force that is ℓ²
  (the summability certificate is a hypothesis, and load-bearing) and per-mode continuous
  in time, entering only through its energy (the squared ℓ² norm); no `H¹` bound on the
  force is needed. At `g = 0` this is not a strengthening of the unforced chain and must
  not be described as one. The breakdown threshold is in the campaign's coefficient
  vocabulary: not the community's `navier_stokes_breakdown_periodic`, not its negation,
  not real-space; it has not been composed with OpenAI's forced blow-up. Nothing in
  Tier 8a is new mathematics (forced small-data theory: Temam, Navier-Stokes Equations,
  Ch. III; Robinson-Rodrigo-Sadowski, Ch. 6-7; Foias-Manley-Rosa-Temam, Ch. II; chapter
  numbers unverified, and the forced file headers disagree among themselves on the
  Robinson-Rodrigo-Sadowski chapter, Ch. 6 in `ForcedTrap`, `ForcedGalerkin` and
  `ForcedGalerkinFlow` against Ch. 6-7 in `ForcedTheoremB` and `ForcedUnique`), and no
  priority is claimed for it.
- **This is not a resolution of the Millennium problem** and makes no claim in that
  direction. Large-data global regularity is untouched.
- **Nothing here is new mathematics.** The trap is Leray 1934 / Fujita-Kato 1964,
  uniqueness is Prodi-Serrin-Ladyzhenskaya, Sobolev propagation is Foias-Temam 1989,
  determining modes is Foias-Prodi 1967 in the rate form of Hayden-Olson-Titi 2011. The
  method is not new either: the axiom gate, frozen statements, and builder/auditor
  doctrine are adopted from the leray-hopf project. What is ours is the machine-checked
  composition, hedged as in "Related work".
- **Constants are of explicit form, exported as compiled existentials.** `κ`, the
  Sobolev growth constants `K_m` and the determining-modes `K` are closed formulas in
  `(ν, m)` and the energy/enstrophy budgets up to one convergent lattice-kernel sum; the
  forced trap's `κ_forced = 8·K_master` (with `K_master` the master-inequality constant of
  `TheoremB/SpectralNorms.lean`, not the determining-modes `K`) depends on nothing but
  that lattice-kernel sum, neither `ν` nor `m`. None is a printed number. `K_m` grows like `2^(16m)` and `K` carries `ν^(−15)`, so the
  determining-modes threshold `N` is a finiteness statement, not a small count.
- **The classical lift's coefficients belong together.** The un-rescaled `ℤ³`-periodic
  lift satisfies `∂ₜu = (ν/(2π)²)Δu − (1/2π)(u·∇)u − ∇p`. In the clock `τ = 2πt` this is
  standard Navier-Stokes at viscosity `ν/(2π)`, the number that also appears in the
  Tier 5 weak-form ledger. Never quote either coefficient without its normalisation.
- **Time regularity is `C¹` on `t > 0` only**, and spatial regularity is `C^p` at each
  time for every finite `p`. Analyticity and `C^∞` in time are excluded, not merely
  unproved. Endpoint derivatives at `t = 0` are not stated; the flow satisfies the
  integral equation at all times and two-sided derivatives at interior times. Joint
  `C^∞` in `(x, t)` on `[0, ∞)`, as required by the community Formal Conjectures
  solution class, is not proved.
- **The Tier 5 weak form** is quantified over band-limited divergence-free test fields,
  not arbitrary smooth tests; their density is standard and cited, not formalized.
- **Identification with leray-hopf's weak solution classes** (same Mathlib pin) remains
  future work.

## Related work

Located by reconnaissance between 26 Aug and 9 Sep 2026. None of these repositories
was re-built by us; kernel status is as reported by each author. Corrections welcome.

- **uda-lab/leray-hopf** (Tomoki Uda; Lean 4, same Mathlib pin `15a89b24`; Jul-Aug
  2026): Leray-Hopf weak existence for 3D Navier-Stokes on `T³` and `ℝ³`, finite-horizon
  and global; explicitly disclaims uniqueness and regularity. The first machine-checked
  3D Navier-Stokes existence result known to us. Our Galerkin/torus vocabulary and our
  verification doctrine follow its pattern.
- **HeliCorgi/ns-mns2-flowmap-bridge** (Lean 4 + Mathlib; 18 Aug 2026): local-in-time
  existence and uniqueness of `H³` mild solutions on `ℝ³` within a Duhamel contract;
  small-data global theory explicitly out of scope. It predates `theorem_B_unique`
  (28 Aug 2026) by ten days, so the bare sentence "first machine-checked 3D
  Navier-Stokes uniqueness" is false and is not used here.
- **Miller, Vlasov mean-field derivation** (arXiv 2607.08986, Jul 2026): global
  existence and uniqueness for the nonlinear Vlasov equation, kernel-axiom-only; so
  "first machine-checked well-posedness of a nonlinear evolution PDE" is not ours either.
- **Alpöge-Buckmaster(-Coiculescu), forced Euler / Boussinesq / IPM blow-up** (Lean 4;
  made public 8 Sep 2026): machine-checked finite-time singularity formation for
  forced equations of the Euler, Boussinesq, and incompressible-porous-media family.
  Opposite direction to this repository (blow-up under forcing, not unforced small-data
  global regularity), and not Navier-Stokes.
- **OpenAI, NavierStokesAndEuler** (Lean 4; public 8 Sep 2026; self-assessed
  certificate): forced Navier-Stokes blow-up presented as answering the Clay statements
  (C)/(D) in the community Formal Conjectures wording, plus unforced Euler blow-up. The
  authors' assessment is their own; no independent audit is known to us. Disjoint from
  this repository in direction and in data class. Its periodic solution class
  (`NavierStokesExistenceAndSmoothnessPeriodic`) is the natural alignment target for
  `theorem_B_smooth_classical_eq`; see "Verification" for what has and has not been done
  about that.
- Statement-only: google-deepmind/formal-conjectures PR #1457 (the community's periodic
  Clay wording, merged May 2026) and lean-dojo/LeanMillenniumPrizeProblems (sorry'd).
  Neither proves anything.

Priority, in its only defensible form: to our knowledge, `theorem_B` +
`theorem_B_unique` + `ns_full_global_flow` are the first kernel-checked small-data
global well-posedness theorem (strong class, unique in the bounded-enstrophy class on
every finite horizon) for the full 3D Navier-Stokes coefficient system on the 3-torus,
beside leray-hopf's earlier weak existence and HeliCorgi's earlier local mild uniqueness
on `ℝ³`. No mathematical priority is claimed for any layer, and none for the method.

## Verification

- **Gate.** Every commit is gated by `scripts/check_axioms.sh` as described above.
  Statements are frozen at declaration; every strengthening lands as a new sibling with
  the frozen statement re-verified byte-identical.
- **Pre-tag audits.** Independent adversarial audits (three to six parallel auditors)
  preceded every tag from M4 through Tier 6 wave 4 (`m4-wave1..4-green`,
  `m5-*`, `t3-theorem-b-green`, `t4-wellposedness-green`, `t5-torus-green`,
  `t5-polish-green`, `t6-sobolev-green`). They found, and the builders fixed before
  tagging: a pressureless-class scoping (M4); the Tier 3 capstone discarding its own
  summability certificates; the same composition-gap pattern in Tiers 4 and 5 (existence
  not exporting what its uniqueness class needs); and a `C¹`-in-time clause claimed but
  not proved in Tier 6.
- **Post-tag audits, 2 Sep 2026.** The Tier 6 classical layer and all of Tier 7 were
  self-audited by their builders at tag time and independently audited afterwards. That
  audit found two statement-shape blockers in Tier 7 (`theorem_B_bandwidth` as first
  tagged was provable by the constant witness; `theorem_B_modes` quantified its `K` after
  the pair of flows) and one compiled-assembly gap in Tier 6 (the classical equation
  existed only as an assembly of clauses in prose), all fixed the same day at `82a9ab6`
  (`t7-audited-green`; `t7-bandwidth-green` re-laid on the corrected statement), with
  the audit record kept in the docstrings.
- **Priority claim corrected, 2 Sep 2026.** A 41-agent prior-art pass located
  HeliCorgi/ns-mns2-flowmap-bridge, which the 26-29 Aug reconnaissance had missed; the
  wording was corrected throughout (`b45ce9e`).
- **Tier 8a, 9 Sep 2026.** Every wave F0 to F4 passed two independent adversarial
  readers BEFORE its commit (the rule Tier 7 did not meet; the record is the commit
  messages); the readers' probes are
  persisted outside the tree, and the essential ones are now compiled and gated in
  `TheoremB/ForcedProbe.lean` (nine declarations: joint nonzero inhabitation with both
  capstones firing, the line force against the summability certificate, the constant
  witness against each equation clause, the force disjunct of the breakdown threshold,
  and the F3-to-F4 seam). Tags `t8a-forced-trap-green` (F0+F1, `b25367e`),
  `t8a-forced-B-green` (F3, `eda7da6`), `t8a-complete` (F5, `2a4036b`).
- **Tier 8b wave W1, 9 Sep 2026.** `TheoremB/TimeSmooth.lean`: the 24 frozen W1
  declarations of the Tier 8 blueprint (section 4b) byte-identical to the blueprint,
  checked by the builder, both readers and the orchestrator with independent extractors;
  two independent adversarial readers (statement shape and vacuity; proof and pin) BEFORE
  the commit, both CLEAN with minors only; the readers' chain-pinning probes landed and
  gated in the same file (`chain_unique`, `chain_unique_Ici`, `clause21_pinned`), the
  other probes (nonzero admissible datum, constant witness against clause 6, the
  rest-state chain, empty-window facts) persisted outside the tree. Tag
  `t8b-time-smooth-green`.
- **Tier 8b wave W2, 9 Sep 2026.** `TheoremB/WithinSeries.lean` (the six frozen engine
  statements, `import Mathlib` only) and `TheoremB/JointSmooth.lean` (the nine frozen
  slab and pressure statements and the capstone `theorem_B_joint_smooth`): the 16 frozen
  W2 items byte-identical to the blueprint (the capstone to its assembled text, since the
  blueprint spells it as "clauses 1 to 22 plus 23 to 25"), checked by the builder, both
  readers and the orchestrator with independent extractors; the engine and the slab-side
  idioms were re-proved as reconnaissance probes outside the tree before the wave; two
  independent adversarial readers (statement shape and vacuity; proof and pin) BEFORE
  the commit, both CLEAN with minors only; the seam probe to the community class
  (clause 24 composed with the real part and the clock gives the community's
  `velocity_smooth` shape) persisted outside the tree. Tag `t8b-joint-smooth-green`.
- **Cross-check, 9 Sep 2026.** OpenAI's Comparator (D) statement, in the community
  Formal Conjectures wording, was reproduced verbatim and compiled against this pin
  (Mathlib `15a89b24`, Lean `v4.31.0-rc2`): it elaborates (exit 0, the (D) statement
  itself left `sorry`), and the rest state inhabits the periodic solution class, so the
  class is not vacuous. Inhabiting its `f = 0` case with `theorem_B_smooth_classical_eq`
  is not done: it would need the clock `τ = 2πt` (so their `nu` is our `ν/(2π)`), a
  real-part bridge for our ℂ-valued lift, joint `C^∞` in `(x, t)` on `[0, ∞)`, and a
  `derivWithin` at `t = 0`. An independent replay of this repository through
  `lean4checker`, and registration of the frozen capstones, are pending; priority
  currently rests on git tags.

Repository tags, in order: `m1-green`, `m2-wave1-green`, `m2-complete`, `m3-conditional-green`,
`m4-wave1..4-green`, `m5-wave1/2-green`, `m5-complete`, `t3-theorem-b-green`,
`t4-wellposedness-green`, `t5-torus-green`, `t5-polish-green`, `t6-sobolev-green`,
`t6-smooth-green`, `t6-classical-green`, `t7-bandwidth-green`, `t7-modes-green`,
`t7-complete`, `t7-audited-green`, `t8a-forced-trap-green`, `t8a-forced-B-green`,
`t8a-complete`, `t8b-time-smooth-green`, `t8b-joint-smooth-green`.

## Credits

- Konstantinos Tsantakos (AKINTECH Driven Ltd): command and architecture.
- Claude (Anthropic), Fable 5 and Opus 5, as proving engines under an orchestrated
  multi-agent workflow with adversarial verification.
- Verification doctrine adapted from uda-lab/leray-hopf.
- The Mathlib community, especially the Ascoli, interval-integral FTC, and `tsum`
  layers this build stands on.

## License

No license has been designated yet; the choice is the owner's. Until a `LICENSE` file
is added, all rights are reserved.
