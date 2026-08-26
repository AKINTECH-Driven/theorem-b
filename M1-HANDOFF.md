# M1 Handoff Brief: Tier 0 of the Theorem B campaign

You are Claude Code, working on Konstantinos's machine. This pack is M1 of a
campaign whose goal is Tier 2: a machine-checked a priori estimate for the 3D
incompressible Navier-Stokes equations (conditional Theorem B). Context lives
in `rung2-gap-map.md` (campaign map) and `NSSkeleton.lean` (the kernel-checked
discrete twins these theorems continue). Read both if present.

## Mission

Close the four `sorry`s in `TheoremB/RiccatiTrap.lean`, identified as S1..S4,
until `scripts/check_axioms.sh` prints `GATE: GREEN`.

That means: everything compiles, and `#print axioms` for
`TheoremB.trap_forward_invariance` and `TheoremB.riccati_window` reports at
most `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.

## Setup

1. Ensure elan is installed. The toolchain pin is `leanprover/lean4:v4.31.0-rc2`
   (in `lean-toolchain`); elan fetches it automatically.
2. From the pack root: `lake update && lake exe cache get && lake build`.
   The Mathlib pin `15a89b2468bc` matches uda-lab/leray-hopf @ e704400 for
   future interop (Tier 4). If the short rev fails to resolve, copy the full
   `mathlib` rev out of leray-hopf's `lake-manifest.json`, or as a fallback
   repin to current master and note the change in your report.
3. `chmod +x scripts/check_axioms.sh`.

## The contract (binding)

1. **Statements are frozen.** The four theorem statements are the deliverable
   interface. If one cannot be proved as written (missing hypothesis, wrong
   constant, false as stated), do not silently repair, weaken, or strengthen
   it. Stop, write down the precise obstruction, and report. Route decisions
   are architect calls, made upstairs.
2. **No new axioms, ever.** The gate enforces this mechanically. Do not add
   `axiom` declarations, do not `native_decide`, do not disable the gate.
3. **Candidate lemma names in the blueprints are educated guesses, not
   facts.** Verify every one with `exact?`, `apply?`, Loogle, LeanSearch, or
   grepping Mathlib source before relying on it. Expected load-bearing area:
   `Mathlib.Analysis.Calculus.MeanValue` (the `Convex.*_of_deriv_*` family),
   `HasDerivAt.inv` / `HasDerivAt.pow` chain-rule lemmas, `ContinuousOn.mul`,
   `csInf` membership lemmas for closed bounded-below sets, and standard
   ordered-field algebra (`div_le_div_iff`, `inv_le_inv`, `mul_le_mul`).
4. **Order of battle: S1, then S3, then S2, then S4.** S1 is the smallest win
   and S2 depends on it; S4 is algebra on top of S3. One sorry at a time; a
   partial day that closes S1 alone is a good day.
5. **If stuck on one sorry for more than about an hour**, decompose: extract
   the blocking step as its own named lemma with its own sorry, prove the
   rest, and report the residue precisely. Never thrash.
6. **Honesty in reporting.** Nothing is "done" until the gate is GREEN on
   your machine. Report exactly what the gate printed.

## Proof sketches (already in the file as docstrings)

- S1: wrap the mean-value antitonicity lemma on `Icc x y`.
- S3: linearize via `phi := (Z ^ 2)⁻¹`; chain rule gives
  `deriv phi = -2 * deriv Z / Z ^ 3 ≥ -2a`; mean value inequality; rearrange.
- S2: first-exit bootstrap on the closed bad set
  `{t | ν4 ≤ κ * E t * Z t}`; its infimum would be a bad point that steps 3
  and 4 of the docstring show is inside the region; contradiction; then S1
  finishes.
- S4: invert the S3 inequality; the window hypothesis keeps the denominator
  positive.

## Report template (paste back when done)

```
M1 REPORT
Toolchain: <lake env lean --version>
Mathlib rev: <from lake-manifest.json>
Gate output: <full output of scripts/check_axioms.sh>
Sorries closed: S1 [ ] S3 [ ] S2 [ ] S4 [ ]
Statement changes requested: <none, or the precise obstruction>
Lemma names that differed from the blueprint guesses: <list>
Wall time and rough token/effort notes: <for the campaign ledger>
```

## After GREEN

Commit with the gate output in the commit message, tag `m1-green`, and stop.
Tier 1 (the master inequality on the torus) is a separate brief; do not start
it inside this session.
