# Changelog

One line per tag, in creation order: date, tag, gate count where the README ladder records
one, and what the tag froze. History through 13 Sep 2026: 79 commits and 31 tags (17
lightweight, 14 annotated, none signed). The gate counts are the README's.

## After v0.1.0 (untagged)

Changes made on `main` on 13 Nov 2026, after the `v0.1.0` tag. None of them touches a Lean
source, a file under `scripts/` or a pin, and the tag stays at `506866f`. Commits that change
only this file are not listed; `9096d38` is one.

- `3918e83`, the CI workflow only: lean-action's Reservoir eligibility check is off, and the cache cleanup, the axiom gate and the entry count now also run after an earlier step has failed (the job still ends red then);
- `8808247`, documentation and workflow comments only: the README and `REPRODUCING.md` record what the four CI runs at `506866f` and `3918e83` measured, and the build times replace the estimate of 1 to 3 hours in `REPRODUCING.md`;
- `37f7ac7`, documentation and workflow comments only: the README and `REPRODUCING.md` record the first CI run of the kernel replay, at `9096d38`, with `REPLAY: GREEN (70 modules)`, and what that run does not show.

Why the workflow changed: at `506866f` the two CI runs, one in each of two copies of this
repository that were private at the time, built the project and then failed at the Reservoir
check. It passes only for a public repository with at least 2 stars, an OSI-approved licence
and a `lake-manifest.json`. As a failed step it skipped the cache cleanup, the axiom gate and
the entry count, so the gate did not run in CI at the `v0.1.0` commit. At `3918e83`, which
differs from `506866f` in the workflow file only, the two runs were green:
`GATE: GREEN (484/484)`, entry count 484 of 484, `TAGS: GREEN`.

Correction in `8808247`: at the `v0.1.0` tag, a comment in the workflow and section 8 of
`REPRODUCING.md` say that lean-action's axiom audit covers 483 of the 484 entries of the
ledger `AxiomCheck.lean`. That is wrong. The tag keeps the wrong wording in both places;
`main` has the corrected wording in both. The audit selects by module, and a local Lean check
on 13 Nov 2026 found all 484 ledger names defined in modules of the `TheoremB` library.

Kernel replay in CI: the replay job, which runs only on a tag push or when started by hand,
first ran on 13 Nov 2026, in run 43467205427. It ran at `9096d38`, which differs from
`506866f` in the workflow file, `CHANGELOG.md`, the README and `REPRODUCING.md` only. The job
printed `REPLAY: GREEN (70 modules)`: each module imported by `TheoremB.lean` was replayed
through the toolchain's `leanchecker` with exit 0 and an empty log. What that does not show:
the imports, Mathlib included, and the umbrella module are not replayed; the checker prints
nothing on success, so nothing counts the declarations checked; it is the toolchain's own
checker; it is one run, on a GitHub-hosted Linux runner, with no check that must fail; and
no test with a declaration that the checker must reject is on record. The README ("Kernel
replay in CI") and `REPRODUCING.md` (sections 6 and 8, with the link to the run) have the
record and these limits.

Also recorded in `37f7ac7`: push run 43456108021 at `9096d38` failed at its first attempt in
the Mathlib cache download and passed when the failed job was re-run. The replay job does not
run on a push to `main`.

Correction in `37f7ac7`: at the `v0.1.0` tag, step 7 of section 4 of `REPRODUCING.md` pairs
the 2,357 s of the 12 Sep 2026 replay record with that record's 60 modules. That is wrong:
the sum includes 73 s for the umbrella module's row, which was killed (exit 137), and the 60
modules sum to 2,284 s. The tag keeps the wrong wording; `main` has the corrected figures in
the same step.

Narrowed in `37f7ac7`: at the tag, a comment in the README's replay commands says of the
missing-module check `# 1: the checker is not a no-op`. On `main` it reads
`# 1: a missing module is an error`, because that check shows only that a missing module is
reported, not that a wrong proof would be (`REPRODUCING.md`, section 6, sixth point).

## v0.1.0 (2026-11-12)

The publication commit. It adds:

- licence and notices: `LICENSE` (Apache-2.0) and `NOTICE`, with comment-only notices in the Lean sources;
- the gate count check: `scripts/check_axioms.sh` joins wrapped lines, asserts the audited entries against the ledger by count and by name and prints `GATE: GREEN (484/484)`, or `GATE: RED (lake build failed)` when the build fails;
- the tag check: `scripts/check_tags.sh`, which prints `TAGS: GREEN` when every frozen capstone statement is identical at its tag and at HEAD;
- the reproduction recipe: `REPRODUCING.md`, and an early exit 2 in `scripts/replay_leanchecker.sh` when the toolchain has no `leanchecker`;
- the CI workflow: `.github/workflows/gate.yml`;
- the citation file `CITATION.cff` and `CONTRIBUTING.md`;
- the sanitised audit record `context/audit-digest.md`, and `M1-HANDOFF.md` moved to `context/` as a historical record;
- package metadata in `lakefile.toml` (version, description, keywords, licence);
- prose corrections in the README and the context documents.

The upstream re-diff of 11 Nov 2026 is recorded in `context/upstream-rediff-2026-11-11.md`: as
text, the copied community-class declarations are unchanged since the copied commit `b9fc95eb` in
the upstream file as it stood at commit `e4e4a9b0` that day (nothing upstream was compiled). The
README and the announcement fact sheet say the same.

## Tags before v0.1.0

- 2026-08-27 `m1-green`: M1 complete, the four open steps in `RiccatiTrap.lean` closed.
- 2026-08-27 `m2-wave1-green`: M2 wave 1, the spectral layer (W1 to W3) proved.
- 2026-08-27 `m2-complete`: M2 complete, sharp Agmon, trilinear majorant and master inequality.
- 2026-08-27 `m3-conditional-green`: M3, the conditional Theorem B (Tier 2), all ten capstones.
- 2026-08-27 `m4-wave1-green`: M4 wave 1, the derivative-to-frequency bridge on the 3-torus (12 capstones).
- 2026-08-27 `m4-wave2-green`: M4 wave 2, the conditional trap discharged for abstract Galerkin flows (14 capstones).
- 2026-08-27 `m4-wave3-green`: M4 wave 3, the finite-mode Navier-Stokes trap (20 capstones).
- 2026-08-27 `m4-wave4-green`: M4 wave 4, reality propagation and the zero-data trap (22 capstones).
- 2026-08-27 `m5-wave1-green`: M5 wave 1, the interval-localized Galerkin chain and uniqueness (29 capstones).
- 2026-08-28 `m5-wave2-green`: M5 wave 2, global well-posedness of the trapped Galerkin system.
- 2026-08-28 `m5-complete`: M5 wave 3, the eternal Galerkin flow.
- 2026-08-28 `t3-theorem-b-green`: Tier 3, Theorem B for the full Navier-Stokes coefficient system, unconditional.
- 2026-08-28 `t4-wellposedness-green`: Tier 4, uniqueness and the eternal flow.
- 2026-08-29 `t5-torus-green`: Tier 5, Theorem B on the torus, the function-space bridge.
- 2026-08-29 `t5-polish-green`: Tier 5 polish, the record closed.
- 2026-08-29 `t6-sobolev-green`: Tier 6 v1, the small-data eternal flow stays in every H^m for all time.
- 2026-08-29 `t6-smooth-green`: Tier 6 v3, `theorem_B_smooth`, the small-data eternal flow is classically regular.
- 2026-08-29 `t6-classical-green`: Tier 6 complete, classical Navier-Stokes, pointwise.
- 2026-08-29 `t7-modes-green`: Tier 7, audit probes for the summit.
- 2026-08-29 `t7-complete`: Tier 7 complete, the eternal flow decays at rate 2nu.
- 2026-09-02 `t7-audited-green` (gate 186/186): Tier 6 and 7 post-tag audit, fixes landed.
- 2026-09-02 `t7-bandwidth-green`: `theorem_B_bandwidth`, corrected (re-laid 2 Sep 2026).
- 2026-09-09 `t8a-forced-trap-green`: Tier 8a waves F0 and F1, the forced trap and the forced Galerkin layer.
- 2026-09-09 `t8a-forced-B-green`: Tier 8a waves F0 to F3, the forced Theorem B and the forced eternal flow.
- 2026-09-09 `t8a-complete` (gate 226/226): Tier 8a complete, the forced trap (waves F0 to F5).
- 2026-09-09 `t8b-time-smooth-green` (gate 251/251): Tier 8b wave W1, time-smoothness of the eternal flow.
- 2026-09-09 `t8b-joint-smooth-green` (gate 265/265): Tier 8b wave W2, joint smoothness on the closed slab.
- 2026-09-12 `t8b-community-green` (gate 294/294): Tier 8b wave W4, the community class inhabited at f = 0 for trap-class data; Tier 8b complete.
- 2026-09-13 `t9-datum-bridge-green` (gate 339/339): Tier 9 wave W1, the datum bridge between real-space data and coefficient data.
- 2026-09-13 `t9-complete` (gate 391/391): Tier 9 complete, the community's own statement shape over real-space data (`theorem_B_community_periodic_data`).
- 2026-09-13 `t9-unique-green` (gate 474/474): Tier 9c complete, uniqueness inside the copy of the community class at f = 0 (`community_unique_velocity`, `community_unique_pressure`).

The Tier 9c addendum (module `GeneralMean`, gate 484/484 at `b402d9a`) came after the last
tag and is carried by v0.1.0.
