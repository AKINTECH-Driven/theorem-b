# Changelog

One line per tag, in creation order: date, tag, gate count where the README ladder records
one, and what the tag froze. History through 13 Sep 2026: 79 commits and 31 tags (17
lightweight, 14 annotated, none signed). The gate counts are the README's.

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
