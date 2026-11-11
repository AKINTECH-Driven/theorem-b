# Theorem B: small-data global well-posedness for 3D Navier-Stokes on the torus, machine-checked in Lean 4

![Lean v4.31.0-rc2](https://img.shields.io/badge/Lean-v4.31.0--rc2-blue) ![Mathlib 15a89b24](https://img.shields.io/badge/Mathlib-15a89b24-blue)

This repository is a Lean 4 / Mathlib formalization of a small-data theory for the
three-dimensional incompressible Navier-Stokes equations on the unit 3-torus, stated and
proved in Fourier coefficients: existence, uniqueness in the enstrophy-bounded class, one
eternal flow, and regularity, decay and determining-mode statements built on it. Every
audited declaration is accepted by a deterministic axiom gate: the kernel reports exactly
`propext`, `Classical.choice`, `Quot.sound`, and never `sorryAx`.

All of it is claimed at one pin only: Lean `leanprover/lean4:v4.31.0-rc2` and Mathlib
`15a89b24`. The Lean sources are 70 files and 32,454 lines under `TheoremB/`, all imported by
the umbrella `TheoremB.lean`, and the gate prints `GATE: GREEN (484/484)`. The history through
13 Sep 2026 is 79 commits and 31 tags; the publication commits and the `v0.1.0` tag come on
top of that.

It was written by Claude (Anthropic), as the commit trailers record (Fable 5, Fable 5.1, and
Opus 5 for Tier 7): the Lean text (statements and proofs) and the reader reports were written
by Claude models running as Claude Code agents. The campaign design, tier ladder,
frozen-statement discipline, wording rules, gates and the decision to publish are the
author's: Konstantinos Tsantakos, founder of AKINTECH Driven Ltd, not a professional
mathematician. No human domain expert has reviewed the statements; the community-class copy
is byte-identical to upstream (the two definitions and six structures copied from the
upstream Navier-Stokes file are byte-identical to it with comments and blank lines stripped, except the
namespace and the divergence notation, made `local`, its `@[inherit_doc]` attribute dropped);
review of the statements is what we are asking for. The
byte-identity is pinned to the copied commit: the copy matches the upstream file content as of
commit `b9fc95eb75b048b195f3d01af4315ad3437ab157` (11 Sep 2026). Upstream has touched that
file since (see "Related work"). It was re-diffed on 11 Nov 2026 against the file as it stood at
upstream commit `e4e4a9b0b6031c663a293de43a0f29a379ae03e0` (the branch head that day; the file's
last change is `d9f6ffa8` of 29 Oct 2026). Upstream's own text of the copied declarations,
docstrings included, is the same there as at the copied commit; and declaration by declaration,
with comments, docstrings and blank lines removed from both sides, the copy differs from
upstream's text of those declarations in the same two places only (the file's other declarations
are not copied). Text was compared; nothing upstream was compiled (record:
`context/upstream-rediff-2026-11-11.md`).

Nothing here is new mathematics. See "Scope and non-claims" and "Related work" before
quoting any of it.

In one breath:

- Small data only: `κ·E₀·Z₀ < ν⁴` on mean-zero, real, divergence-free data. Uniqueness and the
  determining-modes comparison, both stated for enstrophy-bounded classes with no smallness,
  are the exceptions.
- Large-data global regularity is untouched.
- Nothing here is new mathematics, and no mathematical priority is claimed for any layer.
- Claimed only at the pin below (Lean `v4.31.0-rc2`, Mathlib `15a89b24`).
- Verify with `bash scripts/check_axioms.sh`: expect `GATE: GREEN (484/484)` after 484
  `#print axioms` lines.

## What is proved

Starting from an unconditional existence-and-trapping theorem for the full
(infinite-convolution) coefficient system on the lattice `ℤ³`, the development proves
uniqueness in the enstrophy-bounded class, splices one eternal flow on `[0, ∞)`, synthesizes
it into an `L²` velocity field on the torus, propagates every spectral Sobolev level, lifts
the flow to a `ℤ³`-periodic field on `ℝ³` that satisfies the classical equation pointwise,
and adds energy decay, finite bandwidth, and a rate-form determining-modes theorem on top.
Tier 8a carries the trap under a small mean-zero, real, divergence-free force that enters
through its energy only, with uniqueness, one eternal forced flow, and a breakdown threshold
stated in the same coefficient vocabulary.

## Pin

| What | Value | Source |
|------|-------|--------|
| Lean toolchain | `leanprover/lean4:v4.31.0-rc2` | `lean-toolchain` |
| Mathlib | `15a89b2468bc01f1a6230d6e49ef5efc5286e502` (`15a89b24`) | `lake-manifest.json` (`lakefile.toml` requires `15a89b2468bc`) |

The build is only claimed at this pin. Moving either component is a re-verification event.
Mathlib master was on `leanprover/lean4:v4.36.0-rc2` as checked on 11 Nov 2026, so the pin is
behind current Mathlib.

## Build and gate

Requirements: `bash`, `git`, `curl`, [`elan`](https://github.com/leanprover/elan), 16 GB RAM,
about 12 GB of free disk (20 GB recommended). macOS arm64 is the only platform exercised;
Linux is untested.

The toolchain is selected by `lean-toolchain`: the first `lake` call after installing elan
installs `v4.31.0-rc2` automatically. Never run `lake update`: it rewrites `lake-manifest.json`
and moves the Mathlib pin. The historical Tier 0 brief (`context/M1-HANDOFF.md`) still contains
a `lake update` line; it is superseded, do not run it. `MATHLIB_CACHE_USE_CLOUDFLARE` must stay
unset (the mirror did not hold this pin when checked on 20 Sep 2026).

Fetch the Mathlib cache with `lake exe cache get`: this is the recommended path and the only
one used here (its size for this pin, as recorded on 20 Sep 2026: 8,551 files, about 0.45 GB
download, 7.9 GB unpacked; the download itself was not timed).
A from-source Mathlib build at this pin was never attempted and its cost is unmeasured.

```sh
cat lean-toolchain                 # prints leanprover/lean4:v4.31.0-rc2
grep -c '"rev": "15a89b2468bc01f1a6230d6e49ef5efc5286e502"' lake-manifest.json   # prints 1
lake exe cache get                 # Mathlib oleans, recommended
lake build                         # builds the TheoremB library (default target)
bash scripts/check_axioms.sh       # builds, then runs the axiom audit
```

The gate (`scripts/check_axioms.sh`) rebuilds the project, compiles `AxiomCheck.lean`,
and prints `#print axioms` for every audited declaration. It joins wrapped lines, asserts that
the audited entries are exactly the `#print axioms` lines of `AxiomCheck.lean` (same count,
same names, every axiom list closed), and passes if and only if every line reports at most `propext`, `Classical.choice`, `Quot.sound`
and no `sorryAx`. The script reports; it never repairs.

Expected result: the final line `GATE: GREEN (484/484)`, preceded by the output of the 484
`#print axioms` commands in `AxiomCheck.lean` (theorems, one definition, and the
compiled non-vacuity probes), each on exactly the three kernel axioms. Any other outcome
is `GATE: RED (...)` with exit status 1; a failed build prints `GATE: RED (lake build failed)`.

To count the entries yourself, join wrapped lines first and count the pattern
`depends on axioms: [...]`; do not count with a quote-delimited regex, because eight
declaration names end in a prime and Lean prints them as `'name''`. For example

```sh
bash scripts/check_axioms.sh | awk '/\[/ && !/\]/ {buf=$0; next} buf!="" {buf=buf" "$0; if (index($0,"]")) {print buf; buf=""}; next} {print}' | grep -c 'depends on axioms: \['
grep -c '^#print axioms' AxiomCheck.lean
```

must print 484, and both commands must print the same number.

Cost. Measured fresh-clone rebuild, 20 Sep 2026 (Apple M4, 10 cores, 16 GiB): a clone of the
tracked tree at `1146a08` (74 tracked Lean files) with `.lake/packages` symlinked to an
already-cached Mathlib pin, so this measures the project's 70 modules plus the umbrella and the
ledger, not the cache download. `lake build`: 8638 jobs, exit 0, zero errors, wall time 2294 s
(38 min 14 s; user 454 s, sys 654 s). The machine was shared with seven audit agents for the
whole run, so the wall time is an upper bound. The gate printed `GATE: GREEN` (484 entries after
joining wrapped lines, none non-standard, no `sorryAx`; that run predates the `(484/484)`
suffix). `.lake/build` was 422 MB; free disk fell from 5.3 GiB to 3.2 GiB during the run and
returned to 7.4 GiB afterwards (build temporaries plus the concurrent agents' scratch, not
outputs). Not measured: the cache download on a machine without the pin, and a Linux runner.
Estimates, not measurements: the gate adds about 30 s on a built tree, and a full replay takes
45 to 50 minutes.

Four declarations carry a scoped `set_option maxHeartbeats 1000000 in` (five times the default,
one declaration each): `TheoremB/SobolevPairing.lean:110`, `TheoremB/Nonlinearity.lean:45` and
`:285`, `TheoremB/PairingBound.lean:251`. They are not a hidden global switch; expect those
modules to be the slow ones.

Kernel replay of every module through the toolchain's own `leanchecker`, after `lake build` has
succeeded:

```sh
bash scripts/replay_leanchecker.sh             # 70 modules; TSV + one log per module in .lake/leanchecker/
lake env leanchecker TheoremB.CommunityUnique  # one module: exit 0 and empty output = pass
lake env leanchecker TheoremB.NoSuchModule; echo $?   # 1: the checker is not a no-op
```

The script exits 2 early if the toolchain has no `leanchecker`. It skips the umbrella module
unless `REPLAY_ROOT=1` (on a 16 GiB machine the umbrella replay was killed twice by the
kernel's memory watchdog; 32 GB or more is untested). A full replay today covers 70 modules, not the 60 of the 12 Sep 2026 record.

Frozen statements and tags: `bash scripts/check_tags.sh` prints `TAGS: GREEN` when every
frozen capstone statement is identical at its tag and at HEAD and, for the eight tags whose
gate count the ladder below records, the ledger entry count matches. The publication commit
added comment-only notes to six Lean files (`ClassicalEquation`, `CommunityClass`,
`CommunityData`, `CommunityUnique`, `LerayHopfVocab`, `TheoremBSmooth`), so a whole-file hash of
one of those six differs from its tag while every statement is unchanged; compare them with
`git diff <tag> HEAD -- <file>` (comment lines only) or with `check_tags.sh`. The history through 13 Sep 2026 has 31 tags, 17 lightweight and 14 annotated, none
signed, so `git tag -v` cannot be used on them; verify by content:

```sh
git diff t9-unique-green HEAD -- TheoremB/CommunityUnique.lean   # comment-only lines (publication notes)
git show t3-theorem-b-green:TheoremB/TheoremBGlobal.lean | diff - TheoremB/TheoremBGlobal.lean && echo unchanged-since-tag
git show t7-audited-green:AxiomCheck.lean | grep -c '^#print axioms'    # 186, the number recorded for that tag
```

Further files: `REPRODUCING.md` (the reproduction record), `CHANGELOG.md` (one line per tag),
`CONTRIBUTING.md`, `CITATION.cff`, `scripts/check_tags.sh`.

The gate's count history. In the campaign notes this state is written "GREEN 484/484"; it was
recorded on 13 Sep 2026 at the Tier 9c addendum W3d state, the gate having read 186/186 at `82a9ab6` (tag `t7-audited-green`, 2 Sep 2026), grown by one
Tier 8a wave at a time (190, 199, 208, 215, 217, 226 at `2a4036b`, tag `t8a-complete`),
by the Tier 8b wave W1 (22 frozen theorems and 3 chain-pinning probes, 251 at `0efba80`,
tag `t8b-time-smooth-green`), by the Tier 8b wave W2 (14 frozen theorems, 265 at
`e5a8755`, tag `t8b-joint-smooth-green`), by the Tier 8b wave W3 (13 frozen theorems
and 5 datum-side probes, 283 at `ade27c8`), by the Tier 8b wave W4 (4 frozen
theorems and 7 capstone-level probes, 294 at `d59ddcd`, tag `t8b-community-green`), by the
Tier 9 wave W1 (45 frozen theorems, 339 at `ffb8406`, tag `t9-datum-bridge-green`), and by
the Tier 9 wave W2 (36 frozen theorems and 16 register probes, 391 at `332790f`, tag
`t9-complete`), by the Tier 9c wave W3a (30 frozen theorems, 421 at `2ea0d9c`), by the
Tier 9c wave W3b (23 frozen theorems, 444 at `43a0b29`), by the Tier 9c wave W3c (15
frozen theorems and 15 register probes, 474 at `68e12d2`, tag `t9-unique-green`), and by
the Tier 9c post-tag addendum W3d (7 frozen theorems and 3 register probes, 484 at
`b402d9a`).

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
| `theorem_B_community_periodic_flow` | `TheoremB/CommunityClass.lean` | The same flow, all twenty clauses of `theorem_B_smooth_classical_eq` re-exported verbatim, plus (clause 21): OUR COPY of the community's periodic solution class `NavierStokesExistenceAndSmoothnessPeriodic (ν/(2π)) (u₀Real c₀) 0 (vReal c) (pReal c)` is inhabited by this flow read back as a real velocity and pressure in the clock `τ = t/(2π)`, with the zero force. The class's two definitions and six structures are copied into `TheoremB.Community` from the community wording (google-deepmind/formal-conjectures as adapted in OpenAI's Comparator file); declaration by declaration, with comments and blank lines stripped, the copy differs from upstream's text of those declarations only in the namespace and the `local notation` for the divergence (whose `@[inherit_doc]` attribute is dropped); the upstream file is not imported. Verified again on 13 Sep 2026 against the file fetched from the default branch of google-deepmind/formal-conjectures (last content change of the declarations commit `b9fc95eb75b048b195f3d01af4315ad3437ab157` of 11 Sep 2026; both statement names present; both upstream placeholder proofs still `sorry`): the two definitions and six structures are byte-identical with comments and blank lines stripped, up to those two differences. Upstream has touched the file since: commit `bc1d2bc0` of 12 Sep 2026 (moved, same bytes); commit `6fbb54f2` of 18 Sep 2026 (the Lean module conversion: `module`, `public import`, `@[expose] public section` and one blank line); commit `d9f6ffa8` of 29 Oct 2026 (a linter option line before each breakdown statement). Re-diffed on 11 Nov 2026 against the file as it stood at upstream commit `e4e4a9b0`: no other line changed, and upstream's own text of the copied declarations, docstrings included, is the same there as at the copied commit (record: `context/upstream-rediff-2026-11-11.md`). |
| `theorem_B_community_periodic` | `TheoremB/CommunityClass.lean` | The community's own shape: for every `ν' > 0` and every datum `u₀Real c₀` with `c₀` summable at every Sobolev level, mean-zero, real, divergence-free and `κ · en c₀ · ens c₀ < (2πν')⁴`, the datum meets `InitialVelocityConditionPeriodic`, the zero force meets `ForceConditionPeriodic`, and there exist `v`, `p` with `NavierStokesExistenceAndSmoothnessPeriodic ν' (u₀Real c₀) 0 v p`. This is exactly the conclusion of the upstream positive statement `navier_stokes_existence_and_smoothness_periodic` restricted to that data class at `f = 0`; it says nothing about the positive statement for general data and nothing about `navier_stokes_breakdown_periodic`; both upstream `sorry`s are untouched. Existence only: the class has no uniqueness clause (uniqueness of the coefficient flow behind `vReal c` is `theorem_B_unique`). The rest state is not a witness for nonzero data (probe), and the time-constant velocity is excluded on the shear datum (probe). |
| `datum_bridge` | `TheoremB/DatumBridge.lean` | The datum bridge (Tier 9, wave W1): every `u₀ : ℝ³ → ℝ³` in the community's `InitialVelocityConditionPeriodic` (`C^∞`, one-periodic, divergence-free) has a coefficient field `coeff u₀` (the Fourier coefficients of the descent of each component to the unit 3-torus, `TheoremB/Descent.lean`) that is summable at every Sobolev level, real, divergence-free, and satisfies `u₀Real (coeff u₀) = u₀`: the pointwise Fourier inversion, from Mathlib's inversion for continuous torus functions with summable coefficients and the rapid decay of the coefficients of a smooth periodic function through `mFourierCoeff_deriv` at every order. Textbook; nothing here is new. |
| `theorem_B_community_periodic_data` | `TheoremB/CommunityData.lean` | The community's own statement shape over REAL-SPACE data (Tier 9, wave W2): for every `ν' > 0` and every `u₀` in `InitialVelocityConditionPeriodic` with `κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀)) < (2πν')⁴` (the smallness is on the MEAN-FREE part of the datum's coefficient field; the mean vector enters no hypothesis), there exist `v`, `p` with `NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` (OUR COPY of the class). The mean is removed by the Galilean change `v(x, τ) = m + w(x − τm, τ)` (`galilean_class`, `TheoremB/Galilean.lean`, a class-level fact proved from Mathlib and the community definitions only) and the mean-free part is fed to `theorem_B_community_periodic`. This is the conclusion of the upstream positive statement `navier_stokes_existence_and_smoothness_periodic` under that smallness hypothesis at `f = 0`; it says nothing about general data and nothing about `navier_stokes_breakdown_periodic`; both upstream `sorry`s are untouched. Existence only: the coefficient flow behind the witness is unique by `theorem_B_unique`, reached through the sibling below. The constant datum is handled by the boost, not excluded (register probe); the shear datum is nonzero, non-constant, small, and the capstone fires on it with both trivial candidates failing (register probes in `T9Probe`). |
| `theorem_B_community_periodic_data_flow` | `TheoremB/CommunityData.lean` | The witness-exposing sibling: the same hypotheses and conclusion with the witness pair exhibited as `(galV m (vReal c), galP m (pReal c))`, `m` the mean vector of `coeff u₀` and `c` the coefficient flow at `ν = 2πν'` from the mean-free datum, carrying clauses 1 to 7 of `theorem_B_community_periodic_flow` (they supply the hypotheses of `theorem_B_unique` on every window `[0, T]`). Existence with an exhibited witness, not uniqueness in the class. |
| `community_unique_velocity` | `TheoremB/CommunityUnique.lean` | Uniqueness of the velocity inside OUR COPY of the community class at `f = 0` (Tier 9c, wave W3c): two members `(v₁, p₁)`, `(v₂, p₂)` of `NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` with the same datum `u₀` and `0 < ν'` (consumed by `theorem_B_unique`, not implied by membership: the constant pair is a member for every real `ν'`) have `v₁ x t = v₂ x t` at every `x` and every `t ≥ 0`. A corollary of `theorem_B_unique` (Tier 4) at campaign viscosity `2πν'` through the datum bridge (Tier 9 W1) and the calibration in reverse (W3b: a member's coefficient flow `classFlow v t := coeff (v · (t/(2π)))` satisfies the campaign mode ODE and its integral form on every window, every constant computed), followed by the inversion `u₀Real_coeff` on the two slices. Textbook energy method in the enstrophy class; nothing new. Nothing about general data, `ν' ≤ 0`, forced data, competitors outside the class or `navier_stokes_breakdown_periodic`; the positive statement `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement are both untouched. The register (`T9cProbe`) compiles that the half-line `t ≥ 0` is sharp (two same-datum members differ at `t = -1`), that two distinct members on a nonzero datum exist, that different data are not forced equal, and that the class is inhabited for every real `ν'`. |
| `community_unique_pressure` | `TheoremB/CommunityUnique.lean` | Under the same hypotheses the pressures differ by a function of time alone: `∃ g : ℝ → ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + g t` (the `k = 0` pressure mode is free; the explicit form `p₁ x t = p₂ x t + (p₁ 0 t − p₂ 0 t)` and the gradient form are frozen beside it). The pressure is unique up to a function of time, and only that: the register compiles that `p₁ = p₂` and "up to a constant" both fail (every member's pressure shifted by a smooth function of time is a member). From the velocity capstone, the class equation and `is_const_of_fderiv_eq_zero` on `ℝ³`. |
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
- `TheoremB/`: the development (70 files, 32,454 lines of Lean, all imported by the umbrella),
  roughly in build order. Tier 0 ODE traps
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
  wave W2, a PR candidate), joint smoothness on the closed slab (`JointSmooth`, W2), and
  the community class (`CommunityClass`: the community's two definitions and six structures copied into
  `TheoremB.Community`, the real-part bridge, the datum-side conditions, and the two
  capstones with their probes; W3 and W4); Tier 9, the community's statement shape over
  real-space data (`Descent` and `DatumBridge`, wave W1: the descent of a one-periodic
  field to the torus and the datum bridge; `Galilean` and `CommunityData`, wave W2: the
  Galilean change on the closed slab, the mean-free algebra, the capstone with its
  witness-exposing sibling and consistency corollary, and the `T9Probe` register); Tier 9c,
  uniqueness inside our copy of the community class at `f = 0` (`SliceExtract`,
  `ConvectionCoeff` and `ClassParseval`, wave W3a: the slice extraction from the joint
  smoothness on the closed slab, the convection coefficient, Parseval and the window
  budgets; `ClassFlowODE`, wave W3b: the coefficient flow of a class member, the parametric
  integral, the calibration in reverse; `CommunityUnique`, wave W3c: the two capstones, the
  pressure siblings, the injectivity lemmas, the consistency corollaries and the `T9cProbe`
  register; `GeneralMean`, the post-tag addendum W3d: the phase of a translated field's
  coefficients, the general-mean consistency identity for the boosted witness, its Tier 9 and
  constant-datum instances, and the smallness sibling spelled `ens (coeff u₀)`).
- `AxiomCheck.lean`: the audited-declaration ledger (484 `#print axioms` lines).
- `scripts/check_axioms.sh`: the gate. `scripts/check_tags.sh`: frozen statements identical at
  their tags and at HEAD. `scripts/replay_leanchecker.sh`: per-module kernel replay.
- `.github/workflows/gate.yml`: the CI workflow: build and axiom gate, a per-module kernel
  replay on tags and manual runs, and the frozen-capstone tag check.
- `LICENSE`, `NOTICE`, `CITATION.cff`, `CHANGELOG.md`, `CONTRIBUTING.md`, `REPRODUCING.md`,
  `.mailmap`: licence and third-party attribution, citation metadata, one line per tag,
  contribution notes, the reproduction record, and the author-identity map.
- There is no statement-only file in `v0.1.0` (a `Statements.lean` is planned as `v0.1.1`): the
  capstones are named in the table above, frozen at tags and checked by `scripts/check_tags.sh`.
- `context/`: the campaign's working record (blueprints, gap map, replay records, the
  announcement draft, the drafted Mathlib PR, the upstreaming dossier, the discrete-twin
  skeleton `NSSkeleton.lean`); it is kept as a historical record, with its planning-time
  status headers; the publication commit adds only supersession notes and wording fixes,
  except the announcement draft, the PR text and the dossier, which were revised; the upstream
  re-diff record of 11 Nov 2026 (`context/upstream-rediff-2026-11-11.md`) was added after it. It is not
  part of the library.
- `context/audit-digest.md`: the sanitised per-wave record of the reader audits (verdicts,
  gate counts) behind the process claims under "Verification"; the raw reader reports are not
  published.
- `context/M1-HANDOFF.md`: historical record of the Tier 0 brief (26 Aug 2026); not
  instructions, superseded, do not run its build line.

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
- **Large-data global regularity is untouched.** Nothing here bears on the open problem for
  general data, and no claim in that direction is made.
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
- **Time regularity, by tier.** At Tier 6 (`theorem_B_smooth_classical`) the lift is `C^p` in
  space at each time for every finite `p` and `C¹` in time on `t > 0`. Tier 8b upgrades this for
  the same flow: every mode is `C^∞` in time on the closed half-line (`theorem_B_time_smooth`)
  and the velocity and pressure lifts are `C^∞` jointly in `(x, t)` on the closed slab
  `ℝ³ × [0, ∞)` (`theorem_B_joint_smooth`), which is what the community Formal Conjectures
  solution class asks for. Analyticity is excluded at every tier: `∞` is `(⊤ : ℕ∞)`, not `ω`.
  Two-sided derivatives at `t = 0` are not stated; the endpoint derivative is the right
  derivative within `[0, ∞)`.
- **The Tier 5 weak form** is quantified over band-limited divergence-free test fields,
  not arbitrary smooth tests; their density is standard and cited, not formalized.
- **Identification with leray-hopf's weak solution classes** (same Mathlib pin) remains
  future work.

## Related work

Located by reconnaissance between 26 Aug and 9 Sep 2026 and refreshed 20 Sep 2026. Third-party
facts marked "as checked on 11 Nov 2026" were re-read on that date; every other third-party
fact is as of 20 Sep 2026 and may have moved. None of these repositories was re-built by us;
kernel status is as reported by each author. Corrections welcome.

- **uda-lab/leray-hopf** (Tomoki Uda; Lean 4, same Mathlib pin `15a89b24`; Jul-Aug
  2026): Leray-Hopf weak existence for 3D Navier-Stokes on `T³` and `ℝ³`, finite-horizon
  and global; explicitly disclaims uniqueness and regularity. Our Galerkin/torus vocabulary
  and our verification doctrine follow its pattern. As checked on 11 Nov 2026: Apache-2.0,
  10 stars, default branch `main`, latest commit `e704400f` of 8 Aug 2026 (tag `v0.2.1`; tags
  `v0.2.0` and `v0.2.0-rc1` also exist); its README still claims no regularity beyond the
  energy class and neither uniqueness nor non-uniqueness; a Lean Reservoir entry exists.
- **HeliCorgi/ns-mns2-flowmap-bridge** (Lean 4 + Mathlib; 18 Aug 2026): local-in-time
  existence and uniqueness of `H³` mild solutions on `ℝ³` within a Duhamel contract; since
  23 Aug 2026 the repository states the actual incompressible equations for real
  divergence-free Schwartz data (`r3AdmissibleSchwartzDatum_navierStokes`), and on 5 Sep 2026
  added an explicit periodic shear solution as a witness (PR #92), not a well-posedness
  theorem; as of 20 Sep 2026 no paper and no tags. As checked on 11 Nov 2026: Apache-2.0,
  0 stars, latest commit `de518485` of 9 Sep 2026 on `main`. Small-data global theory is
  explicitly out of scope. It predates `theorem_B_unique` (28 Aug 2026) by ten days, so the
  bare sentence "first machine-checked 3D Navier-Stokes uniqueness" is false and is not used
  here.
- **Miller, Vlasov mean-field derivation** (arXiv 2607.08986, Jul 2026): global
  existence and uniqueness for the nonlinear Vlasov equation, kernel-axiom-only; so
  "first machine-checked well-posedness of a nonlinear evolution PDE" is not ours either.
  As checked on 11 Nov 2026 the paper is still v2, last revised 20 Jul 2026.
- **Bedrossian, Landau damping for Vlasov-Poisson in Lean** (arXiv 2609.16801, v1 of
  15 Sep 2026, no later version as checked on 11 Nov 2026; repository
  Jacob24876/LandauDamping-Public): nonlinear Landau damping on `T^d`, Gevrey `s > 1/3`,
  small backgrounds, as of 20 Sep 2026; kernel status as reported by its author.
- **Alpöge-Buckmaster(-Coiculescu), forced Euler / Boussinesq / IPM blow-up** (Lean 4;
  made public 8 Sep 2026; repository tristanbuckmaster/fluid_lean, one commit `d0124689` of
  8 Sep 2026 holding `euler-blowup`, `boussinesq-blowup` and `affinecore`; as checked on
  11 Nov 2026 it has 267 stars and declares no licence): machine-checked finite-time
  singularity formation for forced equations of the Euler, Boussinesq, and
  incompressible-porous-media family. Opposite direction to this repository (blow-up under
  forcing, not unforced small-data global regularity), and not Navier-Stokes. The IPM paper
  arXiv 2609.16470 (v1, 15 Sep 2026, 57 pages; as checked on 11 Nov 2026) is described by its
  authors as an LLM-assisted and Lean formalized proof. The authors said on 8 Sep 2026 that they
  believe they have a hypo-dissipative Navier-Stokes blow-up, withheld pending its Lean check;
  nothing had been released as of 20 Sep 2026.
- **OpenAI, NavierStokesAndEuler** (Lean 4; public 8 Sep 2026 (commit `8937a8f4`; extended
  10 Sep 2026 by commit `f9e8bc5b`, which adds a whole-space `R3/` layer with an `H³` local
  strong theory and weak-strong uniqueness, assembles the paper's whole-space Theorem 1.1 as
  one statement, and re-derives both breakdown statements from it; the periodic breakdown
  statement's text is unchanged); self-assessed certificate): forced Navier-Stokes blow-up
  presented by its authors as answering alternatives (C) and (D) of the standard problem
  statement, in the community Formal Conjectures wording, plus unforced Euler blow-up. The
  authors' assessment is their own; we have not re-built it. Several third-party rebuilds
  and checker runs have been posted since; the three read on 11 Nov 2026 are each
  self-published and each explicit that it checks the certificates, not the fit to the prose
  statement; none is a peer review, and we have verified none of them. As checked on 11 Nov 2026: swarm-ai-research/navier-stokes-lean-check
  (Apache-2.0) reports a build with exit 0, no `sorryAx`, standard axioms only, the community
  encoding of alternative (C) unmodified, and no nanoda replay;
  rayman813/navierstokes-lean-independent-rebuild (MIT; latest commit 11 Sep 2026) reports a
  build, standard axioms only and a Comparator check with the nanoda kernel at `f9e8bc5`, and
  states that it does not show statement fidelity; mobiusresearch/navier-stokes-theorem-1-1
  (Apache-2.0) reports that the whole-space Theorem 1.1 statement, as one theorem, was
  accepted by Lean and by nanoda, that deliberately weakened proofs were rejected, and that
  its bundled script runs no kernel. As of 20 Sep 2026 two further rebuilds were reported
  (francescoantoniodeluca, 12 Sep; mary-octavia, 13 Sep); they were not re-checked. As
  checked on 11 Nov 2026 the repository is Apache-2.0 with 2,130 stars and two commits on
  `main`, none newer; its README names Lean `v4.34.0-rc2`; the paper and the announcement
  page were not re-checked for revisions or corrections. The preprint arXiv:2610.08144
  (Bastounis, Circelli and Hansen; v1 of 6 Oct 2026, as checked on 11 Nov 2026) claims in its
  abstract that Lean verification of an AI autoformalisation gives no assurance that the
  original natural-language argument is correct, and says it shows mismatches in examples
  that include OpenAI's announced blow-up proof; we have not assessed that claim. Disjoint
  from this repository in direction and in data class. Its periodic solution class
  (`NavierStokesExistenceAndSmoothnessPeriodic`) is the natural alignment target for
  `theorem_B_smooth_classical_eq`; see "Verification" for what has and has not been done
  about that.
- awkronos/navier (pushed 20 Sep 2026, as of that date) re-derives both breakdown
  statements in its own carrier and proves periodic classical uniqueness (9 Sep 2026); its
  unforced statements A and B are marked open.
- Statement-only: google-deepmind/formal-conjectures PR #1457 (the community's periodic
  wording of the standard problem statement, merged May 2026) and lean-dojo's repository of
  sorry'd statements of the standard open problems (Apache-2.0, 71 stars, latest commit
  `603053dc` of 10 Sep 2026 as checked on 11 Nov 2026; its Navier-Stokes file was read at
  `fd52071` during the late-August 2026 reconnaissance). Neither proves anything. As of 11 Sep 2026 (commit `b9fc95eb`) the
  Navier-Stokes file of formal-conjectures marks both breakdown statements `research solved`
  with a link to OpenAI's commit `8937a8f4`, and keeps both existence-and-smoothness
  statements, including the periodic one that `theorem_B_community_periodic_data` inhabits at
  zero force for small mean-free data, `research open`. As checked on 11 Nov 2026 the current
  file (touched since by `bc1d2bc0` of 12 Sep 2026 (moved, same bytes), `6fbb54f2` of
  18 Sep 2026 (the Lean module conversion: `module`, `public import`, `@[expose] public section`
  and one blank line) and `d9f6ffa8` of 29 Oct 2026 (a linter option line before each breakdown
  statement); no other line changed, as diffed on 11 Nov 2026) still marks
  the two existence-and-smoothness statements `research open` and the two breakdown
  statements `research solved` with the same link, and all four bodies are `sorry`.
- Seen, not verifiable by us, not counted as prior art either way: the self-described
  global-regularity or regularity-pillar Lean repositories DavidFox998/navier-stokes
  (24 Aug 2026), navindutta/navier-stokes-3d-bkm-lean4 (20 Aug 2026), a regularity-proof
  repository by BenFrohman (17 Sep 2026, carries `sorry`), and
  aidilamrym-ops/navier-stokes-formalization (20 Sep 2026), all as of 20 Sep 2026; none was
  built here and none of their headline statements was checked against a textbook statement.

Position relative to earlier work: `theorem_B` + `theorem_B_unique` + `ns_full_global_flow`
give small-data global well-posedness (strong class, unique in the bounded-enstrophy class on
every finite horizon) for the full 3D Navier-Stokes coefficient system on the 3-torus, beside
leray-hopf's earlier weak existence and HeliCorgi's earlier local mild uniqueness on `ℝ³`.
No mathematical priority is claimed for any layer, and none for the method.

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
- **Tier 8b wave W3, 9 Sep 2026.** `TheoremB/CommunityClass.lean` part 1: the six
  definitions of the community's periodic solution class byte-copied into
  `TheoremB.Community` (identical to the persisted copy of OpenAI's Comparator wording
  declaration by declaration with comments stripped; the only differences from the
  upstream file are the namespace and the `local notation` for the divergence, whose
  `@[inherit_doc]` attribute is dropped), the
  bridge objects `vReal`, `pReal`, `u₀Real`, the coordinate-derivative and Laplacian
  bridges for the lifts, the reality and periodicity lemmas, the divergence-free and
  smoothness conditions on the real datum, the zero force's condition, and five
  registered datum-side probes (a nonzero admissible datum, its nonzero real value, the
  rest pair failing the class, the constant flow failing the mode equation). 16 frozen
  W3 items and the 8 community declarations byte-identical (builder, both readers,
  orchestrator); two independent readers CLEAN before the commit. Nothing is inhabited
  in this wave; no tag (the ladder tags after W4).
- **Tier 8b wave W4, 10 Sep 2026.** `TheoremB/CommunityClass.lean` part 2: the endpoint
  derivative of the character sum within `Ici 0`, the clock-transported `derivWithin` of
  the real velocity, and the two capstones (`theorem_B_community_periodic_flow`, pinned
  to the flow by the twenty classical clauses; `theorem_B_community_periodic`, the
  community's own shape). Four frozen statements byte-identical (the pinned capstone to
  the recheck skeleton's spliced text, since the blueprint spells its classical block as
  a placeholder); two independent adversarial readers CLEAN before the commit; seven
  registered capstone-level probes: the capstones fire on a nonzero datum (also with the
  datum explicit), the rest velocity is not a witness for nonzero data, the class's
  `derivWithin` and `fderiv` are genuine derivatives under `velocity_smooth`, and the
  time-constant velocity is excluded on the shear datum for every `ν' ≠ 0` (the
  statement-shape reader's probe, landed). Tag `t8b-community-green`. Tier 8b complete.
- **Tier 9 blueprint, 13 Sep 2026** (`context/rung11-tier9-blueprint.md`, commit `1e971bd`,
  prose only): six reconnaissance probes compiled at the pin, one design, two adversarial
  critiques (statement shape, feasibility: zero blockers and zero majors each), and a final
  probe that PROVES the whole tier before any build (the W1 interface, the capstone, its
  sibling and the consistency corollary; its only two placeholder-proof declarations are
  the deferred W3 candidates); 113 statements extracted from it verbatim into the blueprint (35 + 17 + 21 + 22 frozen,
  16 register, 2 W3 candidates).
- **Tier 9 wave W1, 13 Sep 2026.** `TheoremB/Descent.lean` and `TheoremB/DatumBridge.lean`:
  the descent of a one-periodic field to the torus, the fiber-slice brick for
  `mFourierCoeff_deriv`, the derivative bridge at every order, the coefficient field
  `coeff`, its decay, summability, reality and divergence-freeness, the round trip and the
  inversion, and the capstone `datum_bridge`. 52 frozen statements byte-identical (builder,
  both readers, orchestrator); two independent readers before the commit (statement shape
  and vacuity: twelve compiled probe theorems; proof and pin: an independent gate run, a
  double-import instance test, and the inversion re-proved by an L²-injectivity route);
  gate GREEN 339/339. Tag `t9-datum-bridge-green` (`ffb8406`).
- **Tier 9 wave W2, 13 Sep 2026.** `TheoremB/Galilean.lean` (the Galilean change on the
  closed slab as a class-level fact; no measure instance; compiles standalone) and
  `TheoremB/CommunityData.lean` (the mean-free algebra, `theorem_B_community_periodic_data`,
  its witness-exposing sibling, the consistency corollary, and sixteen register probes:
  the constant datum is in the class and the capstone fires on it for every `ν' > 0`; the
  shear datum is nonzero, non-constant, in the class and small, the capstone fires on it
  and both trivial candidates fail; the smallness hypothesis is restrictive on the class;
  the mean enters no hypothesis; `coeff` of a non-periodic field is junk and the inversion
  fails for the identity). 43 frozen statements and the 16 register statements
  byte-identical; two independent readers before the commit, both CLEAN (the proof reader
  re-proved `galilean_class` by two other tactic routes and the capstone from the frozen W1
  interface); gate GREEN 391/391. Tag `t9-complete` (`332790f`). Tier 9 complete; W3
  (uniqueness inside the class in real-space vocabulary) sized and deferred, its two
  statements never in the tree (built as Tier 9c the same day; below).
- **Kernel replay of the Tier 9 modules, 13 Sep 2026.** The four new modules replayed
  through the toolchain's `leanchecker` at `332790f` (exit 0, empty output each; record in
  `context/leanchecker-replay-2026-09-13-tier9.md`; the imports are the modules replayed on
  12 Sep, unchanged since).
- **Tier 9c blueprint, 13 Sep 2026** (`context/rung12-tier9c-blueprint.md`, commit `55a7a0b`,
  prose only): eight reconnaissance probes compiled at the pin, which closed the whole
  interface of the deferred W3 before any design (every statement proved by its owner probe;
  the calibration in reverse with every constant computed, no discrepancy), one design whose
  final probe proves every frozen statement end to end with both capstones on the standard
  three axioms, two adversarial critiques (statement shape: zero blockers and zero majors,
  six minors applied; feasibility: clean, the five proposed modules compiled as a module
  chain), and the blueprint with its fenced statements byte-identical to the final probe.
- **Tier 9c wave W3a, 13 Sep 2026.** `TheoremB/SliceExtract.lean`, `ConvectionCoeff.lean`,
  `ClassParseval.lean`: the four slices of the class equation at fixed time are continuous
  and one-periodic and the time-derivative slice is `C^∞`, the compactness bounds on every
  window, the Laplacian coefficient `−(2π)²‖freq n‖²`, the product coefficient with a nonzero
  mean mode and the convection coefficient matched to `−2π · convFull`, Parseval for the
  energy and the enstrophy as equalities and the window budgets. 30 frozen statements
  byte-identical; two independent readers before the commit (0 blockers, 0 majors; the
  Laplacian coefficient re-proved by a second route and checked exactly on the shear datum);
  gate GREEN 421/421 (`2ea0d9c`).
- **Tier 9c wave W3b, 13 Sep 2026.** `TheoremB/ClassFlowODE.lean`: the coefficient flow of a
  class member in the campaign clock, defined once; dominated continuity and differentiation
  of the torus parametric integral; the forward FTC; the pressure-gradient coefficient and its
  Leray kill at every mode; and the calibration in reverse: the class equation read through
  the coefficients is the campaign mode ODE at `ν = 2πν'` (for every real `ν'`), with its
  integral form on every window. 24 fenced declarations byte-identical; two independent
  readers before the commit (both CLEAN; the constant ledger of the mode ODE re-derived by
  hand against the built file; the FTC and the divergence-free derivative re-proved by second
  routes); gate GREEN 444/444 (`43a0b29`).
- **Tier 9c wave W3c, 13 Sep 2026.** `TheoremB/CommunityUnique.lean`:
  `community_unique_velocity` and `community_unique_pressure` (byte-identical to the Tier 9
  blueprint's candidate statements), the pressure's gradient, velocity-hypothesis and explicit
  forms, the `theorem_B_unique` window wrapper, the injectivity lemmas, the consistency
  corollaries (every member on a constant datum is the constant pair in velocity), and the
  `T9cProbe` register (the pressure form and the half-line are sharp; two distinct members on
  a nonzero datum; different data not forced equal; the class inhabited for every real `ν'`;
  the coefficient flow of a non-member is junk; consistency with Tier 9's flow sibling on a
  mean-free datum). 15 frozen and 15 registered statements byte-identical; two independent
  readers before the commit (0 blockers, 0 majors; the capstone route re-derived by hand; the
  pressure capstone and the coefficient injectivity re-proved by second routes); gate GREEN
  474/474 (`68e12d2`). Tag `t9-unique-green`. Tier 9c complete.
- **Kernel replay of the Tier 9c modules, 13 Sep 2026.** The five new modules replayed
  through the toolchain's `leanchecker` (exit 0, empty output each; record in
  `context/leanchecker-replay-2026-09-13-tier9c.md`).
- **Tier 9c post-tag addendum W3d, 13 Sep 2026.** `TheoremB/GeneralMean.lean`: the
  coefficient of a translated one-periodic field carries the phase `mFourier (-k) (fiber a)`
  (no continuity needed); the general-mean consistency identity, the boosted witness's
  coefficient flow is `zeroMode m` plus the phase-twisted mean-free flow, under reality and
  ℓ¹ at the time alone; its instance on the Tier 9 witness for a datum of arbitrary mean and
  its constant-datum instance (the flow from the zero datum is the zero flow, through the
  velocity capstone); the smallness sibling spelled `ens (coeff u₀)` with the equivalence of
  the two spellings. 19 statements byte-identical to the blueprint's section 9; two
  independent readers before the commit (both CLEAN; the phase lemma re-proved by the
  opposite substitution, the sign checked by hand and on a half-period translate of a
  character); gate GREEN 484/484 (`b402d9a`). No tag. Also on 13 Sep 2026: the textbook
  theorem numbers checked against online tables of contents and previews (the verified ones
  entered in the announcement, the rest kept hedged), and the upstream file re-verified.
- **Cross-check, 9 Sep 2026.** OpenAI's Comparator (D) statement at commit `8937a8f4` (not
  repeated on `f9e8bc5b`), in the community
  Formal Conjectures wording, was reproduced verbatim and compiled against this pin
  (Mathlib `15a89b24`, Lean `v4.31.0-rc2`): it elaborates (exit 0, the (D) statement
  itself left `sorry`), and the rest state inhabits the periodic solution class, so the
  class is not vacuous. Inhabiting its `f = 0` case with the eternal flow is now done
  (Tier 8b, 9 to 10 Sep 2026): the clock `τ = t/(2π)` (their `nu` is our `ν/(2π)`), the
  real-part bridge for the ℂ-valued lift, joint `C^∞` in `(x, t)` on the closed slab and
  the `derivWithin` at `t = 0` are all compiled, and `theorem_B_community_periodic`
  inhabits OUR COPY of the class for trap-class data at `f = 0` (nothing beyond that
  class of data is claimed; both upstream statements are untouched). An independent kernel replay of every imported module through the toolchain's
  `leanchecker` was done on 12 Sep 2026 (60 of 60 modules, exit 0, empty output;
  `scripts/replay_leanchecker.sh`, record in
  `context/leanchecker-replay-2026-09-12.md`; the umbrella module, which declares
  nothing, could not be loaded on a 16 GiB machine); registration of the frozen
  capstones is pending; the dated git tags are the record. A reproducer running
  `scripts/replay_leanchecker.sh` today replays 70 modules, not the 60 of the 12 Sep record.

Repository tags, in order (31 tags through 13 Sep 2026): `m1-green`, `m2-wave1-green`, `m2-complete`, `m3-conditional-green`,
`m4-wave1..4-green`, `m5-wave1/2-green`, `m5-complete`, `t3-theorem-b-green`,
`t4-wellposedness-green`, `t5-torus-green`, `t5-polish-green`, `t6-sobolev-green`,
`t6-smooth-green`, `t6-classical-green`, `t7-modes-green`,
`t7-complete`, `t7-audited-green`, `t7-bandwidth-green` (re-laid 2 Sep 2026),
`t8a-forced-trap-green`, `t8a-forced-B-green`,
`t8a-complete`, `t8b-time-smooth-green`, `t8b-joint-smooth-green`, `t8b-community-green`,
`t9-datum-bridge-green`, `t9-complete`, `t9-unique-green`.

## Credits

- Konstantinos Tsantakos, founder of AKINTECH Driven Ltd, not a professional mathematician:
  the campaign design, tier ladder, frozen-statement discipline, wording rules, gates and the
  decision to publish.
- Claude (Anthropic), as the commit trailers record (Fable 5, Fable 5.1, and Opus 5 for
  Tier 7): the Lean text (statements and proofs) and the reader reports, written by Claude
  models running as Claude Code agents under an orchestrated multi-agent workflow with
  adversarial verification. 78 of the 79 commits through 13 Sep 2026 carry the
  `Co-Authored-By` trailer of one of these models. `CITATION.cff` lists the human author only.
- All commits are by one author under three local git identities; see `.mailmap`. The hosting
  page may show 28 commits and 3 annotated tags under an author it cannot link to an
  account. History is not rewritten, because that would change every hash quoted here and
  re-lay all 31 tags.
- Verification doctrine adapted from uda-lab/leray-hopf.
- The Mathlib community, especially the Ascoli, interval-integral FTC, and `tsum`
  layers this build stands on.

## License

Apache License 2.0; see `LICENSE`. Third-party material and its attribution are listed in
`NOTICE`. The licence covers the Lean code and repository materials; it does not purport to
license mathematical facts or theorems themselves.
