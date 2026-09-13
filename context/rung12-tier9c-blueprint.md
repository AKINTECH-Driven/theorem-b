# Rung 12: Tier 9c blueprint (W3): uniqueness inside OUR COPY of the community class at f = 0, in real-space vocabulary

Status: PLANNING (13 Sep 2026, session `ca018cdf-179f-4d35-ac64-e4ff4bc5b398`): **nothing
built; gate untouched at HEAD `dc3bd8f`** (the announcement adoption, prose only, on top of
`ff89dd0` (Tier 9 prose), `332790f` (W2, tag `t9-complete`), `ffb8406` (W1, tag
`t9-datum-bridge-green`), `1e971bd` (the Tier 9 blueprint); 30 tags; 70 commits). The gate was
RE-RUN by the orchestrator on 13 Sep 2026 at the start of this chat: `bash scripts/check_axioms.sh`
reported GATE: GREEN with 391 `depends on axioms` entries, every one on exactly `[propext,
Classical.choice, Quot.sound]`, no `sorryAx` (counted on the bracket pattern after joining
wrapped lines; a quote-delimited regex undercounts to 386 because five ledger names end in a
prime: `ns_galerkin_trap_leray'`, `defect_vanishes_on'`, `forced_breakdown_threshold'`,
`u₀Real_eq_meanVec_add'`, `T9Probe.rest_pair_in_class'`); the log is
`audit-tier9c/gate/baseline-gate.log` in the session directory. Working tree clean at the
start of this pass (no untracked file). Disk 8.0 GiB free. Kernel replays on record: all 60
modules at `5dfce7a` (`context/leanchecker-replay-2026-09-12.md`) and the four Tier 9 modules at
`332790f` (`context/leanchecker-replay-2026-09-13-tier9.md`); every module W3 adds is replayed by
`lake env leanchecker TheoremB.<Module>` before its tag. No tracked file is touched by the
planning pass; it writes only this file (in `context/`, as `rung12-tier9c-blueprint.md`) and its
probes (in the session directory `audit-tier9c/`).

**Reconnaissance state (the orchestrator, 13 Sep 2026, workflow `wf_1999ecfc-e65`, eight
probes in parallel, 23 minutes, every agent returned; structured reports in
`audit-tier9c/recon/recon-results.json`, the inventory in `recon/recon-summary.md`, the traps in
`recon/traps-all.md`, the measured names in `recon/verified-names-all.md`; the agents' own
compiles all exit 0; the orchestrator's independent recompile of the eight probes runs to
`recon/orchestrator-recompile/SUMMARY.txt` and is cited by the blueprint before the planning
commit).** The agreed interface I1 to I15 (statements fixed in the recon brief, restated
VERBATIM with `sorry` under `-- INTERFACE (P<n>)` wherever a probe consumed another's result)
is CLOSED: P1 (`recon/P1/ReconP1.lean`, 0 sorry, 21 declarations) PROVES I1 to I7 outright
(the time-derivative slice is continuous AND `C^∞`, `contDiff_time_deriv_slice`; the four
slices of the class equation are continuous and one-periodic; the compactness bounds I4 to I6
through `IsCompact.exists_bound_of_continuousOn` on `closedBall 0 2 ×ˢ Icc a b` and
periodicity; the Laplacian coefficient I7 through the iterated bridge at `q = 2`); P2
(`recon/P2/ReconP2.lean`, 5 sorry = the P1 interface I1 to I5) PROVES the generic dominated
continuity and differentiation of the torus parametric integral (Mathlib only) and I8, I9
modulo P1; P3 (`recon/P3/ReconP3.lean`, 0 sorry, 18 declarations) PROVES I10 outright (the
product coefficient with a nonzero mean mode through `tsum_char_mul`, `uCont` and
`shearEquiv`; the convection coefficient matched to `−2π · convFull`); P4
(`recon/P4/ReconP4.lean`, 9 sorry = interface stubs) PROVES R6's `class_member_mode_ode` (I12)
and `class_member_integral_eq` (I13) VERBATIM modulo I2, I3, I7, I8, I9, I10, I11, I14, with
EVERY CONSTANT COMPUTED and no discrepancy (the `−(2π)²` of the Laplacian bridge against the
`1/(2π)` of the clock gives `−2πν'‖k‖²`; the `−2π` of the convection bridge against the same
`1/(2π)` gives `+ convFull`; the gradient mode `(2πi k_j p̂)_j` is killed by `lerayProj k` for
every `k`, `k = 0` included); P5 (`recon/P5/ReconP5.lean`, 1 sorry = the velocity capstone)
PROVES the forward FTC I14, the constancy lemma, the `theorem_B_unique` window wrapper
`unique_of_windows` (H4 = budgets per window per flow, `max` inside), the clock identities,
and `community_unique_pressure` VERBATIM modulo `community_unique_velocity`; P6
(`recon/P6/ReconP6.lean`, 2 sorry = I5, I6) PROVES R6's `en_coeff_eq` and `ens_coeff_eq`
VERBATIM as equalities and I11 modulo I5, I6; P7 (`recon/P7/ReconP7.lean`, 3 sorry = I8, I11,
I13) PROVES `community_unique_velocity` VERBATIM modulo I8, I11, I13 (window `T := 2πt`,
`ν := 2πν'`, budgets `max`, then W1's inversion `u₀Real_coeff` on the two slices: NO
torus-side injectivity lemma is consumed; `eq_of_mFourierCoeff_eq` and `eq_of_coeff_eq` are
landed in tree spelling anyway, optional), and the constant-datum consistency corollary; P8
(`recon/P8/ReconP8.lean`, 0 sorry, 14 declarations) PROVES the register (every member's
pressure shifted by a smooth function of time is a member; `p₁ = p₂` and "up to a constant"
both FAIL on the rest pair; two DISTINCT members with the same nonzero datum exist for every
`ν' > 0`; different data are not forced equal; the class is inhabited for every real `ν'`; the
junk note). Consequence: the composition check of the design can be STRONGER than the house
pattern requires: one final probe with every frozen statement PROVED end to end and both
capstones on exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx` anywhere (as
Tier 9's `Tier9Final.lean` was for W1 and W2). Risk: LOW (was MED at R6). Size measured by
the probes: about 240 (P1) + 200 (P2) + 200 (P3) + 350 (P4) + 60 (P5, pressure and FTC) + 270
(P6) + 130 (P7) + 220 (P8 register) lines of mathematics, about 1700 lines with docstrings.

**Layout proposal (the orchestrator's default; the design refines with reasons; the R6
four-wave shape compressed to three since everything is proved):** W3a = the descent side,
three leaf files: `TheoremB/SliceExtract.lean` (P1), `TheoremB/ClassParseval.lean` (P6:
Parseval for `en`/`ens`, the budgets, H3), `TheoremB/ConvectionCoeff.lean` (P3); W3b = the
time side, `TheoremB/ClassFlowODE.lean` (P2's parametric integral, P5's forward FTC and
clock identities, P4's calibration in reverse, I12, I13); W3c = `TheoremB/CommunityUnique.lean`
(P7's `classFlow` and H1/H3/H5, P5's wrapper, THE TWO CAPSTONES, P5's pressure bricks, P7's
consistency corollary, optionally the injectivity lemmas, and the register `namespace T9cProbe`
from P8). Each file imports the least it needs (measured, not inferred: the feasibility critic
compiles each proposed import set). Unused binders in the agreed interface (I8's and I11's
`hT`, I12's `hν'`, I14's `hT`, P2's `ha` in item (2)) are the design's call BEFORE freezing
(proposal: drop them; record that the mode ODE holds for every real `ν'`); the two capstones
of rung11 §4c are frozen as written and are not touched.

Pin: Lean `4.31.0-rc2`, Mathlib `15a89b24`. Contract unchanged: kernel + gate judge;
statements freeze at declaration; independent adversarial reader BEFORE any tag; every probe
and every copy of a built file lives in the session directory `audit-tier9c/`, never in
`/private/tmp` (wiped without notice). The house rule since Tier 8b: every earlier Lean file is
frozen (Tiers 1 to 9 included: `Descent.lean`, `DatumBridge.lean`, `Galilean.lean`,
`CommunityData.lean` are now frozen too); private lemmas are cloned with a prefix, never
un-privated; new files only, plus the two registration files `TheoremB.lean` and
`AxiomCheck.lean` (append-only).

Provenance: W3 is the uniqueness half that Tier 9 sized and deferred (rung11 §1b D8, §4c, §5 W3
row, §8 item 4; the design appendix "W3 (uniqueness) sizing, restated from R6"). Tier 9
delivered existence: `theorem_B_community_periodic_data` (the community's own `∃ v p` shape over
`InitialVelocityConditionPeriodic` data under a smallness hypothesis on the mean-free part) and
its witness-exposing sibling `theorem_B_community_periodic_data_flow`, whose clauses 1 to 7
SUPPLY `theorem_B_unique`'s hypotheses for the coefficient flow behind the witness. W3 closes
the other direction: EVERY member of OUR COPY of the class at `f = 0` has a coefficient flow in
`theorem_B_unique`'s class, so two members with the same datum have the same velocity, and
pressures that differ by a function of time. Nothing here is new mathematics: it is the
energy-method uniqueness in the enstrophy class (Tier 4, `theorem_B_unique`), textbook, read
back through the datum bridge (Tier 9 W1) and the Fourier inversion; the deliverable is
machine-checking, with the status of every constant stated per constant (§7).

**Extension of the status header (the blueprint pass, 13 Sep 2026).** The paragraphs above are
the orchestrator's skeleton, carried verbatim; what follows records the evidence state at the
time this file was written.

- HEAD re-read by this pass: `git rev-parse --short HEAD` = `dc3bd8f`; `git status --porcelain`
  empty (0 lines) at the start and at the end of this pass; 30 tags (`git tag | wc -l`); 72 lines
  of `git log --oneline` (the skeleton's "70 commits" was its own count; this pass commits nothing
  and did not investigate the difference); the newest ladder tag is `t9-complete` = `332790f`.
  Nothing under the repository was touched by the design pass, by either critic, or by this pass:
  every one of them writes only under the session directory `audit-tier9c/`. Disk: 5.8 GiB free
  at the start of this pass (`df -h`; the skeleton's 8.0 GiB was measured before the critics' probes
  and oleans). No `lean` process was running when this pass compiled its probe.
- Evidence state, by whom and where (session directory `audit-tier9c/`, absolute prefix
  `/Users/konstantinosa.tsantakos/.claude/projects/-Users-konstantinosa-tsantakos-Documents/ca018cdf-179f-4d35-ac64-e4ff4bc5b398/audit-tier9c/`):
  - RECONNAISSANCE (eight agents, 13 Sep): `recon/P1/ReconP1.lean` (exit 0, 0 sorry), `recon/P2/ReconP2.lean`
    (exit 0, 5 sorry = the P1 interface I1 to I5), `recon/P3/ReconP3.lean` (exit 0, 0 sorry),
    `recon/P4/ReconP4.lean` (exit 0, 9 sorry = interface stubs), `recon/P5/ReconP5.lean` (exit 0, 1 sorry =
    the velocity capstone as interface), `recon/P6/ReconP6.lean` (exit 0, 2 sorry = I5, I6),
    `recon/P7/ReconP7.lean` (exit 0, 3 sorry = I8, I11, I13), `recon/P8/ReconP8.lean` (exit 0, 0 sorry); each
    with a `notes.md`; structured reports in `recon/recon-results.json`; the inventory
    `recon/recon-summary.md`; the traps `recon/traps-all.md`; the names `recon/verified-names-all.md`. The
    ORCHESTRATOR'S independent recompile of the eight probes, `recon/orchestrator-recompile/SUMMARY.txt`
    and `VERIFIED.md`: every probe exit 0, 0 errors, the sorry counts as the agents reported, every `sorryAx`
    entering only through an `-- INTERFACE` stub whose owner probe proves the statement, the interface
    statements identical modulo whitespace across the probes that restate them. Read by this pass, not
    recompiled.
  - DESIGN (the design pass, 13 Sep): `design/DesignFinal.lean` (2328 lines, sha256
    `4daed37c739a1fb985c5cbea1880b2ef0002743486e645497f53c72264b7d057`, exit 0, 0 errors, 0 sorry decls,
    80 of 80 `#print axioms` lines on the standard triple, log `design/compile1.log`), its generator
    `design/make_design_final.py`, the import probes `design/imports/` and `design/design.md`. Read by
    this pass.
  - STATEMENT-SHAPE CRITIC (13 Sep): `critique/shape/ShapeProbe.lean` (16 audited declarations plus two
    `example`s, `compile3.log` exit 0, 0 errors, 0 warnings, 0 sorry, 16/16 axiom lines standard; its
    independent recompile of `DesignFinal.lean`, `recompile-DesignFinal.log`, exit 0), `critique/shape/report.md`:
    0 BLOCKER, 0 MAJOR, 6 MINOR; required changes: none; recommended (A) the register item (9) and (B) the
    two sibling docstrings; optional (C), (D), (E). Read by this pass.
  - FEASIBILITY CRITIC (13 Sep): `critique/feasibility/DesignFinal.copy.lean` (recompile, exit 0),
    `FeasCompose.lean` (exit 0, 3 sorry decls = I8, I11, I13 sorry'd; both capstones proved from them;
    `sorryAx` reaches the capstones only through those three), `FeasComposeP.lean` (exit 0, 1 sorry decl = the
    velocity capstone; the pressure proved from it), `FeasDoubleImport.lean` (exit 0, no instance collision),
    the module chain `critique/feasibility/dag/` (the five proposed files compiled as REAL MODULES under
    exactly the §1a import lines with `lean --root`, `dag/SUMMARY.txt`: five exit 0, axiom lines 16, 6, 8,
    23, 27, all standard), `critique/feasibility/report.md`: CLEAN, 0 BLOCKER, 0 MAJOR, 4 MINOR, five required
    changes. Read by this pass.
  - THIS PASS (the blueprint author, 13 Sep): `design/final/Tier9cFinal.lean` (2431 lines, sha256
    `7a2a108ce42e78c8b6098e53d2c2edb0d4d7a80a201085b4cd41df49d6d43772`), derived from `design/DesignFinal.lean` by
    `design/final/make_final.py` with the critics' changes applied (shape MINOR 1, 2, 4, 5; feasibility
    required change 1; every replacement matched exactly once), COMPILED BY THIS PASS with `lake env lean`
    at the pin on its own first compile: exit 0, 0 `: error`, 0 `declaration uses` (0 sorry declarations),
    83 `#print axioms` lines and EVERY one exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
    anywhere; 5 warnings, exactly the four unused `hT` binders of §1b D6 (lines 947, 977, 1186, 1231) and the
    pin's `τ` linter note (line 1029); the `hν'` warning of the design is gone (D14). Log
    `design/final/compile1.log`. `tools/check_capstone.py` on both capstones against the orchestrator's
    `design/final/expected_community_unique_{velocity,pressure}.txt`: byte-identical, 5 lines each.
    `tools/banned_words.sh` on `Tier9cFinal.lean`: CLEAN; U+2014 and U+2013 counts 0. The fenced blocks of
    §4 and §6 are extracted from that file by `design/final/gen_blueprint.py` (a copy of Tier 9's,
    adapted) through the orchestrator's own `tools/byte_identity.decls_in_file`, and
    `tools/byte_identity.py` was re-run by this pass on this file against `Tier9cFinal.lean` for every
    `#### W` block (the counts are in the §4 preamble).
- Every PROVED mark in §3, §4 and §6 cites `design/final/Tier9cFinal.lean` (the probe that holds the
  proof in its final text, section and line) and, where the proof was copied, the recon probe of origin.
- Format note: the `#### W<n>` headers of §4 put a colon after `W3<x>` (rule 8 of §7 forbids em-dashes
  in new prose; the `^#### W` prefix the orchestrator's tools grep for is unchanged). The em-dashes in
  this file are exactly those inside the rung11 §7 rules carried VERBATIM (rules 1, 2 and 3; rule 5
  carries one en-dash); no sentence written by this pass carries one (§7 grep record).

## 1. Goals and non-goals

**Goal.** The two CANDIDATE statements of rung11 §4c, frozen as written (byte-identical; the
namespace is this pass's decision, §1b):

- `community_unique_velocity`: two members `(v₁, p₁)`, `(v₂, p₂)` of
  `NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0)` with `0 < ν'` have
  `v₁ x t = v₂ x t` for every `x` and every `t ≥ 0`.
- `community_unique_pressure`: under the same hypotheses, `∃ g : ℝ → ℝ, ∀ x, ∀ t ≥ 0,
  p₁ x t = p₂ x t + g t` (the pressure is unique only up to a function of time; the `k = 0`
  pressure mode is free; never claim `p₁ = p₂`; the register compiles the failure of `p₁ = p₂`
  and of "up to a constant").

No smallness hypothesis: `theorem_B_unique` is unconditional in the enstrophy-bounded class, and
a class member's coefficient flow is enstrophy-bounded on every window by smoothness on the
compact torus. The route (R6, this pass's recon P1 to P8): a class member `(v, p)` gives the
coefficient flow `classFlow v t := coeff (v · (t / (2 * Real.pi)))` (the campaign clock
`t = 2πτ`, `ν = 2πν'`); the seven hypothesis groups of `theorem_B_unique` are supplied per flow
(H1 init from `initial_condition`; H2 mode continuity by dominated continuity of the torus
parametric integral; H3 summability from W1's `summable_sob_coeff` on each slice; H4 budgets from
Parseval and compactness; H5 `DivFree` from W1's `divFree_coeff` on each slice; H6 the integral
equation from differentiation under the integral, the Laplacian coefficient, the product
coefficient, the reverse of `convection_classical`, the Leray step and the forward FTC); then
`theorem_B_unique` at `ν = 2πν'` on every window, and W1's inversion `u₀Real_coeff` on the two
slices gives `v₁ · t = v₂ · t`. Pressure: equal velocities give equal pressure gradients through
the class equation, and a function with zero gradient on `ℝ³` is constant
(`is_const_of_fderiv_eq_zero`).

**Non-goals.** Forced data (`f ≠ 0`). Any statement about the upstream positive statement for
general data. The breakdown statement `navier_stokes_breakdown_periodic`. Uniqueness OUTSIDE the
class (a non-smooth competitor; weak solutions). Analyticity. Numeric constants. Any priority
claim (§7). Editing any Tier 1 to 9 file.

**Doctrine (binding; it produced twelve waves with zero blockers across Tiers 8a, 8b and 9).**
Per wave, one Workflow: one builder (statements byte-for-byte from §4; only bodies change; if a
frozen statement cannot be proved as written, keep it, add a sibling, record spec drift; register
every frozen theorem in BOTH `TheoremB.lean` and `AxiomCheck.lean`; local measure instances
NAMED with a file-unique prefix inside `noncomputable section`; no file-level `maxHeartbeats`; a
docstring on every frozen declaration; run the gate), then two readers in parallel
(statement-shape/vacuity with cheap-witness and inhabitation probes; proof-and-pin with
Mathlib-name probes, an independent gate run and a double-import instance test), then a fix pass
for blockers and majors. Then the ORCHESTRATOR re-runs the gate, re-checks byte-identity of every
frozen statement against this file with its own script (`audit-tier9c/tools/byte_identity.py`,
`check_capstone.py`; recompute block line bounds with `grep -n "^#### W"` before every run; a
build-log insert above the blocks moves them; the runs are persisted under
`audit-tier9c/build-w*/orchestrator/`), runs the banned-words grep on every new file, commits
with the harness trailer (`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`), lays the
ladder tag of §5, writes the build-log entry into this file at commit time, and updates memory.

**Extension of §1 (this pass; the statement critic's MINOR 3, applied by extension, not by editing the
verbatim bullets).** In both Goal bullets above, "two members of `NavierStokesExistenceAndSmoothnessPeriodic
(n := 3) ν' u₀ (f := 0)`" means two members `(v₁, p₁)`, `(v₂, p₂)` of OUR COPY of the community class
(`CommunityClass.lean:153-198`, §2) with the SAME datum `u₀`, at `f = 0`, with `0 < ν'` (consumed by
`theorem_B_unique`, not implied by membership); nothing is said about `ν' ≤ 0`, forced data, general
data, or competitors outside the class. The two statements are byte-identical to rung11 §4c lines 953 to
975 (status header; `tools/check_capstone.py`).

### 1a. File layout and import DAG (new files only; the design's layout, confirmed by both critics)

The skeleton's five-file, three-wave layout is KEPT with one refinement (the design's): `ClassParseval.lean`
imports `SliceExtract.lean` (the budgets I11 consume the compactness bounds I5 and I6), so W3a has two
leaves and one dependent file rather than three leaves; and the coefficient flow `classFlow` is DEFINED in
`ClassFlowODE.lean` (section D0), the earliest file that needs a `classFlow` spelling, with the H1/H3/H5
facts about a class member in `CommunityUnique.lean`. The import sets below are MEASURED (the design's
section probes under smaller import lists, and the feasibility critic's module chain).

| File (wave) | Section of `Tier9cFinal.lean` | Contents (probe) | Frozen / helpers / registered | Imports (least; measured) |
|---|---|---|---|---|
| `TheoremB/SliceExtract.lean` (W3a) | A, lines 63 to 434 | P1 entire (I1 to I7, the time-derivative slice `C^∞`, the Laplacian / gradient / convection slices continuous and one-periodic, the three compactness bounds, the Laplacian coefficient) plus the slice facts of P4 sections 1 and 4 consumed downstream (`continuous_ofReal_component`, `isOnePeriodic_add/sub`, `isOnePeriodic_fderiv` generic, `isOnePeriodic_convTerm`, `continuous_convTerm`); the four frozen slice facts now carry docstrings (feasibility required change 1, D18) | 16 frozen theorems / 34 helpers / 16 ledger lines | `TheoremB.DatumBridge`, `TheoremB.Galilean` (design: `design/imports/ProbeA_DatumBridge_Galilean.lean`, exit 0; feasibility chain: `dag/SliceExtract.log`, exit 0, 16 axiom lines, 119 s) |
| `TheoremB/ConvectionCoeff.lean` (W3a) | B, lines 436 to 692 | P3 entire (the character-series coefficient with a nonzero mean mode, discrete Young, `coeffC_mul`, the derivative factor, I10, `coeff_convection`) | 6 frozen / 12 helpers / 6 ledger lines | `TheoremB.DatumBridge` (design: `design/imports/ProbeB_DatumBridge.lean`, exit 0; chain: `dag/ConvectionCoeff.log`, exit 0, 6 axiom lines, 70 s) |
| `TheoremB/ClassParseval.lean` (W3a) | C, lines 694 to 982 | P6 entire (scalar Parseval on the descent, `en_coeff_eq`, `ens_coeff_eq`, the bounded-integrand bound, the two `≤` feeders, I11 `classFlow_budget`, H3 `summable_flow`) | 8 frozen / 9 helpers (1 def `descendC`) / 8 ledger lines | `TheoremB.SliceExtract` (design: sections A+B+C compile against `DatumBridge`+`Galilean` alone, `design/imports/ProbeABC_DatumBridge_Galilean.lean`, exit 0; chain: `dag/ClassParseval.log`, exit 0, 8 axiom lines, 109 s; C uses exactly three names of A: `exists_bound_velocity`, `exists_bound_space_deriv`, `continuous_ofReal_component`) |
| `TheoremB/ClassFlowODE.lean` (W3b) | D, lines 984 to 1681 | D0 `classFlow` (P7 section 1) and `classFlow_zero_eq`; P2 entire (dominated continuity and differentiation of the torus parametric integral, the `Vel` packing, I8, I9); P5's forward FTC I14; P4 entire (the Leray kill of the pressure gradient, `coeff` linearity, the pressure-gradient coefficient, DivFree bookkeeping, `laplacian_coeff_vel`, `convection_coeff_vel`, I12, I13; I12 and I13 without the unused `hν'`, D14) | 1 def + 23 frozen theorems / 18 helpers / 23 ledger lines | `TheoremB.ClassParseval`, `TheoremB.ConvectionCoeff`, `TheoremB.CommunityData` (design: `ProbeABCD_DatumBridge_Galilean.lean` fails with EXACTLY ONE unknown identifier, `dotR_zero_left`, the public clone at `CommunityData.lean:226` consumed by `lerayProj_pressure_gradient_coeff`'s `n = 0` case; chain: `dag/ClassFlowODE.log`, exit 0, 23 axiom lines, 25 s; D uses 13 names of A, `coeff_convection` of B, `classFlow_budget` of C) |
| `TheoremB/CommunityUnique.lean` (W3c) | E, lines 1683 to 2335 | P7 sections 1 (H1), 2 (H3, H5), 4 (THE VELOCITY CAPSTONE), 5 (injectivity), 6 (consistency); P5 sections 2 (constancy), 4 (the wrapper), 3 (THE PRESSURE CAPSTONE and its two siblings), the explicit form (D15); `namespace T9cProbe`: P8 entire, the two MUST-HOLD items of the design, and the sharpness item (9) of the statement critic (D16) | 15 frozen / 7 helpers / 15 registered probes + 2 register helpers + 1 register def / 30 ledger lines | `TheoremB.CommunityData`, `TheoremB.ClassFlowODE` (chain: `dag/CommunityUnique.log`, exit 0, 27 axiom lines at the design's count, 53 s; E uses six names of D and uses `classFlow_budget` of ClassParseval DIRECTLY at two sites, the velocity capstone and `T9cProbe.classFlow_eq_of_flow`, reached through ClassFlowODE's import; feasibility M3) |

Import DAG (arrows point at the importer):

```
CommunityClass ─→ Descent ─→ DatumBridge ─┬→ SliceExtract ─→ ClassParseval ─┐
CommunityClass ─→ Galilean ───────────────┘                                  ├→ ClassFlowODE ─→ CommunityUnique
                  DatumBridge ─→ ConvectionCoeff ────────────────────────────┤                   ↑
                  DatumBridge, Galilean ─→ CommunityData ────────────────────┴───────────────────┘
```

Measured versus inferred. The tree-side imports were measured by the design (`design/imports/`, each probe =
the section text under a smaller import list, compiled with `lake env lean`; exit codes in
`design/imports/SUMMARY.txt`): `ProbeB_DatumBridge.lean` exit 0, so ConvectionCoeff needs nothing from
Galilean; `ProbeA_DatumBridge_Galilean.lean` exit 0; `ProbeABC_DatumBridge_Galilean.lean` exit 0, 0 errors,
0 sorry, so the three W3a files need no tree module beyond `DatumBridge` and `Galilean`;
`ProbeABCD_DatumBridge_Galilean.lean` exit 1 with exactly one error, `Unknown identifier dotR_zero_left`
(ClassFlowODE therefore imports `TheoremB.CommunityData`; a second clone with a file prefix would duplicate a
public lemma, not taken). The intra-W3 arrows (ClassParseval → SliceExtract; ClassFlowODE → ClassParseval +
ConvectionCoeff; CommunityUnique → ClassFlowODE) were compiled as a module chain by the feasibility critic
(`critique/feasibility/dag/`, `lean --root` with the tree's oleans symlinked into a session olean dir; five
files exit 0 under exactly the proposed import lines, `dag/SUMMARY.txt`; feasibility required change 2
applied here, superseding the design's sentence that the arrows could not be compiled outside the tree).
Cross-file use was measured by the critic's `xdeps.py` (`03-xdeps.txt`): no back edge, no cycle. Section E
needs `CommunityData` for `T9Probe.const_pair_in_class`, `capstone_fires_on_const_datum`,
`capstone_fires_on_testDatum`, `rest_pair_in_class'`, `inversion_fails_off_class`, `meanFree_of_mean_zero`,
`theorem_B_community_periodic_data_flow`, and `FullUnique` (transitive under CommunityClass) for
`theorem_B_unique`. The builder brief may reuse `dag/chain.sh` as the pre-commit import test (feasibility M2).

Name-clash record (the design's Python scan of every `theorem/lemma/def/abbrev/structure/instance` name in
`TheoremB/*.lean`, namespaces tracked, against the 176 names declared by the eight probes plus the five file
names, `T9cProbe`, `classFlow_zero_eq`, `coeff_clock`: 0 clashes; the feasibility critic's short-name scan of
the 163 declarations of `DesignFinal.lean` against every public AND private name of the tree: 0 clashes;
none of the 335 private tree names is even mentioned, so no same-name clone exists and nothing is
un-privated). The three names this pass adds (`preHistory`, `preHistory_in_class`,
`velocity_not_unique_off_halfline`, all under `T9cProbe`; `community_unique_pressure_explicit` under
`TheoremB`) were grepped by this pass against `TheoremB/*.lean` (quoted `--include='*.lean'`): 0 hits. No
file `SliceExtract`, `ClassParseval`, `ConvectionCoeff`, `ClassFlowODE`, `CommunityUnique` exists under
`TheoremB/`. The zsh `grep -E` form with `\b` inside an alternation is rejected by the machine's `ugrep`
("empty (sub)expression"): use a Python scan or plain `grep -rn --include='*.lean' "theorem <name>"`. Names
the probes REUSE from the tree and do not redeclare: `contDiff_ofReal_component`,
`isOnePeriodic_ofReal_component`, `continuous_fderiv_apply_single`, `contDiff_space_slice`,
`derivWithin_time_slice`, `hasDerivWithinAt_time_slice`, `fderiv_space_slice`, `laplacian_translate`,
`gradient_translate`, `descend_fiber`, `continuous_descend`, `mFourierCoeff_descend_dirIter`,
`mFourierCoeff_descend_fderiv`, `mFourierCoeff_finset_sum`, `summable_sob_coeff`,
`summable_norm_freq_pow_mul_coeff`, `divFree_coeff`, `u₀Real_coeff`, `uCont`, `mFourierCoeff_uCont`,
`tsum_char_mul`, `shearEquiv`, `convFull_apply`, `continuousOn_convFull`, `lerayProj_continuous`,
`lerayProj_add/sub/smul`, `fderiv_apply_expand`, `gradient_apply_eq_fderiv_single`,
`laplacian_apply_component`, `laplacian_eq_sum_second`, `TimeConstantWitness.pressure_slice`,
`theorem_B_unique`.

### 1b. Decisions (D1 to D13 taken by the design and confirmed by both critics; D14 to D19 taken by this pass)

- **D1 (namespace).** The two capstones live in plain `namespace TheoremB`, as the Tier 9 capstones do, so
  that they are cited as `TheoremB.community_unique_velocity` and `TheoremB.community_unique_pressure`;
  every frozen theorem of the five files is in `TheoremB`; the register is `namespace TheoremB.T9cProbe`
  (the Tier 9 habit `T9Probe`, a fresh name so the two registers never collide). Reason: the capstones are
  consumed by name in the announcement and the README rows; a sub-namespace would make the citation differ
  from Tier 9's. CONFIRMED by the statement critic (item 7: a namespace is not part of the statement text;
  the ruler reads byte-identical).
- **D2 (ONE spelling of the coefficient flow).** `classFlow v t := coeff (v · (t / (2 * Real.pi)))` is
  DEFINED ONCE, in `ClassFlowODE.lean` (D0, `Tier9cFinal.lean:991`, P7's text), with
  `classFlow_apply` (`rfl`), `classFlow_clock` (P7's spelling `classFlow v (2πτ) = coeff (v · τ)`) and the
  unconditional `classFlow_zero_eq`. The frozen interface statements I8, I9, I11, I12, I13 KEEP R6's inline
  spelling `coeff (v · (t / (2 * Real.pi))) k` VERBATIM (P2, P4, P6, P7 consumed them so; P7 measured that the
  inline spelling and `fun s => classFlow v s k` are accepted by `theorem_B_unique` with no `show`, both
  through intermediate `have`s and by direct plugging). The statements that USE `classFlow` are P7's:
  `classFlow_zero` (H1), `summable_classFlow` (H3), `divFree_classFlow` (H5), `classFlow_clock`, the two
  register junk items, and the two MUST-HOLD items. P2's, P5's and P8's local restatements of `classFlow` are
  dropped; P5's inline `classFlow_clock`, `clock_cancel`, `two_pi_ne_zero`, `classFlow_two_pi_mul` are dropped
  (subsumed by P7's `classFlow_clock`); P5/P8's unconditional `classFlow_zero` is renamed `classFlow_zero_eq`
  so that P7's H1 keeps the name `classFlow_zero`. CONFIRMED by the statement critic (item 8: `def classFlow`
  occurs once in the probe and is fenced once here).
- **D3 (the inversion).** `community_unique_velocity` inverts through W1's `u₀Real_coeff` on the two smooth
  one-periodic slices (a three-step `calc`, P7 verbatim); NO torus-side injectivity lemma is consumed by
  either capstone. `eq_of_mFourierCoeff_eq` (L² injectivity on `C(T³, ℂ)`, the reader's ReproveInversion
  clone in tree spelling), `eq_of_coeff_eq` (by the inversion) and `eq_of_coeff_eq'` (by torus-side
  injectivity, the independent route) ARE shipped, FROZEN and registered in `CommunityUnique.lean` (E5): the
  Tier 9 handoff asked for the former to be landed, the two `eq_of_coeff_eq` proofs certify each other, and
  the cost is three ledger lines. CONFIRMED by both critics (the feasibility chain compiles E5 on the standard
  triple; the statement critic's S5 shows why the inversion needs periodicity).
- **D4 (the H4 shape).** Budgets per window per flow: I11 `classFlow_budget` gives, for every `T ≥ 0`, an
  `∃ E Z` for ONE flow; the capstone takes `max E₁ E₂`, `max Z₁ Z₂` (P7 verbatim). The wrapper
  `unique_of_windows` (P5, the exact hypothesis shape a class-member flow supplies, budgets per window per
  flow, the maxima inside) is FROZEN and registered as the citable form of the Tier 4 consumption; its funext
  sibling `unique_of_windows'` is a shipped helper. The capstone's proof calls `theorem_B_unique` directly
  (P7's text, kept because it documents the seven groups by name), not through the wrapper. CONFIRMED by the
  statement critic (item 4 and S6: the frozen I11 quantifies `∃ E Z` BEFORE `∀ t ∈ Icc 0 T`; the pointwise
  form is trivial and cannot discharge it).
- **D5 (frozen / shipped / registered).** FROZEN (fenced in §4, byte-identity enforced, one ledger line each;
  83 in all after D15 and D16): the agreed interface I1 to I14 as stated (I1 to I7 in A, I10 in B, I11 in C,
  I8, I9, I12, I13, I14 in D), the `C^∞` form of I2, the six slice facts of A, the two Parseval EQUALITIES and
  their two `≤` feeders, the scalar Parseval brick, H3 in the flow spelling, the four `coeff` linearity rules,
  the pressure-gradient coefficient and its Leray kill (every `n`), `divFree_slice`, `divFree_deriv`, the two
  `Vel`-packed coefficient facts, the parametric-integral quartet of P2, `classFlow` and its three rules, the
  H1/H3/H5 facts, the constancy lemma, the wrapper, THE TWO CAPSTONES, the pressure's gradient form, its
  velocity-hypothesis form and its explicit form (D15), the three injectivity lemmas, the two consistency
  corollaries. SHIPPED helpers (copied by the builder from the section, not fenced, not registered; 80 in all,
  listed per file in §4): every other declaration of `Tier9cFinal.lean` outside the register. REGISTERED
  probes (the register `T9cProbe`, fenced in §6 for the reader, registered; 15): P8's eleven items, the two
  MUST-HOLD items, and the two sharpness items of D16 (the register's def `preHistory` and its two helpers
  `gradient_add_const_eq`, `uncurry_pressure_add` carry no ledger line). Reason for freezing the interface
  items and not only the capstones: they are what a later wave (a forced-data or a general-data uniqueness)
  would consume, and the recon agreed them; freezing them stops their drift. CONFIRMED by the feasibility
  critic (81 fenced declarations = 80 theorems + `def classFlow` at the design's count, no orphan in either
  direction between the fences and the audit block).
- **D6 (unused binders, amended by D14).** KEPT as agreed: I8's `hT`, I11's `hT`, I14's `hT`, and the helper
  `summable_flow_clock`'s `hT` (four `unused variable` warnings in `design/final/compile1.log`, plus the pin's
  `τ` note on `continuous_space_slice_of_continuousOn`; five in all). Reason: dropping `hT` from I11 would make
  `T` un-inferable at `obtain ⟨E, Z, _⟩ := classFlow_budget …` and force an explicit `T`, a shape change for a
  linter note; `Icc 0 T` is empty for `T < 0`, so `hT` carries no content in I8, I11, I14 (the statement
  critic's S6', "content-free rather than weakening"); the tree already tolerates one such warning
  (`mapsTo_galCurve`). The one binder DROPPED by the design is `ha : 0 ≤ a` from the two P2 HELPERS
  `hasDerivAt_coeff_of_dominated` and `hasDerivAt_coeff_vel` (not interface items; every hypothesis there is
  on the open window), with I9's call site adjusted (P2 item (2)'s own recommendation). I12's `hν'` is a
  different case and is handled by D14.
- **D7 (tags).** ONE tag, `t9-unique-green`, laid after W3c (the capstone wave) by the orchestrator after both
  readers and the gate; W3a and W3b commit without a tag (their commit messages carry the gate count). Reason:
  a tag marks a citable state, and only the capstone wave is citable; every proof is already compiled, so the
  intermediate waves are transcription and need no ladder rung of their own. Before the tag, every new module
  is replayed by `lake env leanchecker TheoremB.<Module>` (status header).
- **D8 (registration and the ledger).** Registered = every frozen theorem plus the 15 register theorems;
  `def`s are fenced but not ledger lines (`classFlow`; the register's `preHistory`). Per wave: W3a 16 + 6 + 8
  = 30 lines (SliceExtract, ConvectionCoeff, ClassParseval), gate 391 → 421; W3b 23 lines (ClassFlowODE),
  421 → 444; W3c 15 + 15 = 30 lines (CommunityUnique, `TheoremB.<name>` and `TheoremB.T9cProbe.<name>`),
  444 → 474. Import lines: 3 + 1 + 1 in each of `TheoremB.lean` and `AxiomCheck.lean`. The 83 `#print axioms`
  lines at the end of `Tier9cFinal.lean` are exactly the future ledger lines (namespaces included) and all
  read the standard triple. Gate bookkeeping (feasibility M4, required change 5): three REGISTERED names end
  in a prime (`contDiff_space_slice'`, `eq_of_coeff_eq'`, `T9cProbe.classFlow_junk'`), so a quote-delimited
  regex would count 471 where the gate's bracket pattern (after joining wrapped lines) counts 474; the
  bracket pattern is the ruler, as the status header says for the five older primed names.
- **D9 (the announcement).** PROPOSED wording only, after `t9-unique-green`, the user's call, under rules 12
  to 14: "inside OUR COPY of the community's periodic solution class
  `NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` with `0 < ν'` and `f = 0`, two members with the
  same datum have the same velocity at every point and every `t ≥ 0`, and pressures that differ by a
  function of time alone (compiled, `community_unique_velocity`, `community_unique_pressure`); this is a
  corollary of the coefficient-side uniqueness `theorem_B_unique` (Tier 4) through the datum bridge (Tier 9
  W1), the textbook energy method in the enstrophy class; nothing about `ν' ≤ 0`, forced data, general data,
  competitors outside the class, or the breakdown statement `navier_stokes_breakdown_periodic`; the positive
  statement `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement are both untouched;
  priority hedged as in rule 12 (HeliCorgi's local mild uniqueness on `ℝ³` and uda-lab/leray-hopf are the
  neighbours)."
- **D10 (`convection_coeff_vel`).** Proved from ConvectionCoeff's `coeff_convection` in three lines (P3's bonus
  already did the `fderiv_apply_expand` bookkeeping) instead of P4's inline expansion; P4's two helpers
  `continuous_fderiv_single_component`, `isOnePeriodic_conv_component` are therefore not shipped. Statement
  unchanged (byte-identical to P4); recorded as a proof drift, compiled.
- **D11 (duplicates).** One copy of each duplicated helper, in the earliest section that needs it; the merge
  table is in the header of `Tier9cFinal.lean` (`continuous_ofReal_component` from P2/P4/P6;
  `isOnePeriodic_fderiv` in P4's generic form replacing P1's `ℝ³` lambda form, accepted by every P1 use up
  to beta; `isOnePeriodic_gradient` in P1's lambda form, accepted by P4's use; `contDiff_space_slice'` (any
  codomain, P4) replacing P1's scalar clone; `continuous_gradient_of_contDiff` (P1) replacing P4's
  `continuous_gradient`).
- **D12 (MUST-HOLD, the flow sibling).** COMPILED (§6 items 8a, 8b): the skeleton's item is FALSE as written
  for a datum with a nonzero mean (the Galilean boost multiplies the mode `k` by `e^{-2πi k·m t}` and shifts
  the zero mode by `m`, so `classFlow` of the boosted witness is not the mean-free flow `c`), and TRUE,
  compiled, for a mean-free datum (`coeff u₀ 0 = 0`): `T9cProbe.classFlow_eq_of_flow` (any flow in
  `theorem_B_unique`'s class from `meanFree (coeff u₀)` equals `classFlow v` of EVERY member `v` on the datum,
  on `Ici 0`; the capstone's route stopped before the inversion) and `T9cProbe.flow_witness_classFlow_eq`
  (the Tier 9 instance on the sibling's own witness). The general-mean identity
  (`classFlow (galV m (vReal c)) t k = e^{-2πi k·m t} c t k + m δ_{k0}`) is NOT compiled and NOT claimed (open
  item, §8).
- **D13 (tools).** The three orchestrator tools are not edited by the design pass nor by this pass (the Tier 9
  D13 reason: they are the instrument this deliverable is measured with); `design/final/make_final.py` and
  `design/final/gen_blueprint.py` are this pass's own (copies of the Tier 9 pattern), and `gen_blueprint.py`
  imports `tools/byte_identity.decls_in_file` so the fenced blocks are extracted by the ruler itself.
- **D14 (this pass), the unused `hν'` DROPPED from I12 and I13** (the statement critic's MINOR 4, offered as
  optional; the skeleton's layout proposal asked for it). `class_member_mode_ode` no longer takes
  `(hν' : 0 < ν')`, and `class_member_integral_eq`, whose `hν'` fed only I12, drops it too; the four call
  sites (I13's use of I12; the two uses of I13 in the velocity capstone; the use in
  `T9cProbe.classFlow_eq_of_flow`) are adjusted; compiled in `Tier9cFinal.lean` (the design's `hν'` linter
  warning is gone). Reason: the rung11 D9 precedent (RC6 there): nothing is built yet, so a stronger frozen
  statement, one hypothesis fewer, costs nothing now, while a weaker one would be frozen for the life of the
  tree; the statement now says what is proved (the mode ODE holds for every real `ν'`; positivity is consumed
  only by `theorem_B_unique`), which is what the design's D6 and the I12 docstring already recorded. This
  departs from the recon's agreed I12/I13 text (P4 and P7 consumed them with `hν'`); the orchestrator's
  cross-probe check of the interface (`recon/orchestrator-recompile/VERIFIED.md`) is superseded for these two
  names by this pass's compile. The two capstones are unchanged (`check_capstone.py`).
- **D15 (this pass), the explicit form of the pressure result is FROZEN and REGISTERED**
  (`community_unique_pressure_explicit`, E4, `Tier9cFinal.lean:1971`;
  the statement critic's MINOR 5 offered it as an optional shipped helper). Statement: `∀ x, ∀ t ≥ 0,
  p₁ x t = p₂ x t + (p₁ 0 t - p₂ 0 t)` under the capstone's hypotheses; proof: the velocity capstone then the
  body of `community_unique_pressure_of_velocity` (the critic's `pressure_of_velocity_explicit`, S4c, with
  the velocity hypothesis discharged). Reason for freezing rather than shipping: it is the form a consumer can
  use without `Classical.choose`, hence capstone-facing, and a capstone-facing statement is frozen so that it
  cannot drift; cost one ledger line. The frozen `community_unique_pressure` keeps the design's own proof
  (not re-routed through the explicit form), so its route note is unchanged.
- **D16 (this pass), register item (9), the sharpness of `∀ t ≥ 0`** (the statement critic's MINOR 1,
  recommended): `T9cProbe.preHistory` (def), `T9cProbe.preHistory_in_class` and
  `T9cProbe.velocity_not_unique_off_halfline`, statements and proofs from `critique/shape/ShapeProbe.lean`
  S9, re-compiled in `Tier9cFinal.lean` (`2289`,
  `2321`), registered (+2 ledger lines). What it settles: two members of
  OUR COPY of the class at `f = 0` with the same datum `0` and `ν' = 1` have `v₁ ≠ v₂` (they differ at
  `t = -1`), so the velocity capstone's `∀ t ≥ 0` cannot be dropped and function equality `v₁ = v₂` is FALSE
  as a consequence of membership. Without it a reader can ask why the conclusion is not `v₁ = v₂`.
- **D17 (this pass), the statement critic's MINOR 3 applied by EXTENSION, not by editing the verbatim
  bullets.** The skeleton's §1 is carried VERBATIM by the orchestrator's instruction; the extension paragraph
  after the bullets says "OUR COPY of the community class", "the same datum", "`f = 0`" and "`0 < ν'`
  consumed by `theorem_B_unique`" in one sentence. Recorded in §8 as a change taken in a different form than
  the critic wrote it.
- **D18 (this pass), docstrings on the four frozen slice facts** (feasibility required change 1, booked for
  the W3a builder brief): written by this pass into `Tier9cFinal.lean` under rules 12 to 14
  (`isOnePeriodic_laplacian_slice`, `isOnePeriodic_gradient_slice`, `continuous_gradient_slice`,
  `continuous_laplacian_slice`), so the builder copies rather than writes them; the 23 bare shipped helpers
  named by the critic need none by the rule. The two sibling docstrings of the statement critic's MINOR 2 are
  applied VERBATIM (the critic's text) to `community_unique_pressure_gradient` and
  `community_unique_pressure_of_velocity`.
- **D19 (this pass), the two critics agree everywhere;** no conflict needed the more conservative reading.
  Where a critic's change was optional, this pass took it (D14, D15) or took it in a different form (D17) and
  says so; where the design and a critic differed (D6 versus MINOR 4 on `hν'`), the critic's stronger
  statement won for the reason in D14.

## 2. The external target

Unchanged from rung11 §2 (OUR COPY of the six community definitions, `CommunityClass.lean:153-198`,
byte-identical to the upstream file's; the two upstream statements
`navier_stokes_existence_and_smoothness_periodic` and `navier_stokes_breakdown_periodic`, both
untouched). W3 adds NO definition to §2; it consumes the class's five fields
(`navier_stokes`, `div_free`, `initial_condition`, `velocity_smooth`, `pressure_smooth`) and the
two periodicity fields. The upstream file carries no uniqueness statement; W3's capstones are
about OUR COPY of the class at `f = 0`, nothing about general data, nothing about the breakdown
statement, both upstream placeholder proofs untouched.

## 3. Gap table (every gap between the tree at HEAD and the capstones)

| # | Gap | Where it bites | Closed by (wave, declaration) | Status |
|---|---|---|---|---|
| G1 | The class equation holds pointwise at fixed time; the campaign consumes COEFFICIENT flows, so each of its four terms must be a continuous one-periodic space slice at every `τ ≥ 0` (integrable descent, coefficient termwise) | H6, the mode ODE | W3a SliceExtract: I2 `continuous_time_deriv_slice`, I3 `isOnePeriodic_time_deriv_slice`, `continuous_convection_slice`/`continuous_convTerm`, `isOnePeriodic_convection_slice`/`isOnePeriodic_convTerm`, `continuous_laplacian_slice`, `isOnePeriodic_laplacian_slice`, `continuous_gradient_slice`, `isOnePeriodic_gradient_slice` | PROVED (`Tier9cFinal.lean` A; ReconP1.lean) |
| G2 | The within-derivative on `Ici 0` is not a derivative at `τ = 0` and the class only gives `derivWithin`; differentiation under the integral needs `HasDerivAt` | I9 | W3a I1 `hasDerivAt_time_slice` (for `τ > 0`, from Galilean.lean's `derivWithin_time_slice` and `hasDerivWithinAt_time_slice`); I14's `hd` is demanded only on `Ioo 0 T` | PROVED (`Tier9cFinal.lean` A; ReconP1.lean) |
| G3 | Domination: the parametric-integral theorems need a uniform bound in `x` on a window in time; the torus is compact but the slab is not | I8, I9, I11 | W3a I4 `exists_bound_time_deriv_slice`, I5 `exists_bound_velocity`, I6 `exists_bound_space_deriv` (`IsCompact.exists_bound_of_continuousOn` on `closedBall 0 2 ×ˢ Icc a b`, moved to every `x` by periodicity through `descend_fiber`; `norm_rep_le`: `‖rep z‖ ≤ 2`) | PROVED (`Tier9cFinal.lean` A; ReconP1.lean) |
| G4 | No Laplacian coefficient in the tree (the bridge `mFourierCoeff_descend_dirIter` is per direction) | the viscous term of the mode ODE | W3a I7 `laplacian_coeff` (`laplacian_eq_sum_second` at `C^2`, `dirIter i 2`, three directions, `sum_sq_twist`: `∑ᵢ (2πi nᵢ)² = -(2π)²‖freq n‖²`) and its `Vel` packing `laplacian_coeff_vel` (W3b) | PROVED (`Tier9cFinal.lean` A, D; ReconP1.lean, ReconP4.lean) |
| G5 | No product coefficient with a NONZERO mean mode in the tree (`tsum_char_mul` gives the Cauchy product of two character series; the read-off needs an ℓ¹ certificate and `uCont` asks for no zero mode) | the convection coefficient | W3a ConvectionCoeff: `mFourierCoeff_charSeries` (the `Vel`-packing trick through `uCont 0`), discrete Young `summable_norm_conv` (through the public `shearEquiv`), `coeffC_mul` (R6 3.iv VERBATIM) | PROVED (`Tier9cFinal.lean` B; ReconP3.lean) |
| G6 | The class's convection term is `fderiv ℝ (v · τ) x (v x τ)`, the campaign's is `convFull` on coefficients; the two must be matched with the constant computed | H6 | W3a I10 `convection_coeff_eq_convFull` (`-2π · (convFull (coeff u) n) j`, the `hdot` block of `convection_classical` in reverse), `coeff_convection`; W3b `convection_coeff_vel` | PROVED (`Tier9cFinal.lean` B, D; ReconP3.lean, ReconP4.lean) |
| G7 | Parseval for `en` and `ens` of a real-space slice (H4 needs numeric budgets; the tree's `en`/`ens` are coefficient-side sums) | H4 | W3a ClassParseval: `hasSum_sq_mFourierCoeff_descend` (scalar, on the descent), `en_coeff_eq`, `ens_coeff_eq` (R6 3.iii VERBATIM, EQUALITIES; the `(2π)^(-2)` through `mFourierCoeff_descend_fderiv` per `(i, j)`), `en_coeff_le_of_bound`, `ens_coeff_le_of_bound`, I11 `classFlow_budget` (`E := C²`, `Z := (2π)^(-2)·3·D²`, UNTRACKED existentials from I5, I6) | PROVED (`Tier9cFinal.lean` C; ReconP6.lean) |
| G8 | H2 and the derivative of the flow in time: the coefficient of a time-dependent field is continuous and differentiable in time (differentiation under the torus integral, absent from the tree) | H2, I12 | W3b ClassFlowODE: `continuousOn_coeff_of_dominated`, `hasDerivAt_coeff_of_dominated` (Mathlib's `continuousOn_of_dominated`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the probability torus), the `Vel` packing `continuousOn_coeff_vel`, `hasDerivAt_coeff_vel`, then I8 `classFlow_continuousOn`, I9 `hasDerivAt_classFlow` (the clock `s ↦ s/(2π)`, `HasDerivAt.scomp`) | PROVED (`Tier9cFinal.lean` D; ReconP2.lean) |
| G9 | `coeff` is not known to be linear over pointwise sums, differences, real scalars; the class equation must be read coefficient by coefficient | I12 | W3b `mFourierCoeff_add/sub/neg/const_mul` (helpers), `coeff_add`, `coeff_sub`, `coeff_smul` (no hypothesis), `coeff_neg` (no hypothesis) | PROVED (`Tier9cFinal.lean` D; ReconP4.lean) |
| G10 | The pressure gradient's coefficient and its Leray kill at EVERY mode (`k = 0` included) | I12 | W3b `pressure_gradient_coeff` (`(2πi nⱼ) p̂(n)` packed), `lerayProj_pressure_gradient` (R6 copy, `k ≠ 0`), `lerayProj_pressure_gradient_coeff` (every `n`) | PROVED (`Tier9cFinal.lean` D; ReconP4.lean) |
| G11 | `DivFree` of every slice and of the DERIVATIVE of a mode (so that `lerayProj k` is the identity on the left-hand side of the ODE) | I12 | W3b `divFree_slice` (W1's `divFree_coeff` on the slice), `lerayProj_of_divFree`, `divFree_deriv` (`HasDerivAt.fun_sum` on the pairing, `HasDerivAt.unique` against the eventually-zero function) | PROVED (`Tier9cFinal.lean` D; ReconP4.lean) |
| G12 | THE CALIBRATION IN REVERSE: the class equation at `ν'` in the clock `t = 2πτ` IS the campaign mode ODE at `ν = 2πν'`, every constant computed (`(1/(2π))·[ν'(-(2π)²‖k‖²) - (-2π)·convFull - ∇p̂] = -2πν'‖k‖² • c + convFull - (1/(2π)) • ∇p̂`, then `lerayProj k`) | H6 | W3b I12 `class_member_mode_ode` (R6 3.vi with the unused `hν'` dropped, D14; every real `ν'`) | PROVED (`Tier9cFinal.lean` D, line 1511; ReconP4.lean; the constant ledger is checked by the kernel through `field_simp; ring`) |
| G13 | The integral form on every window (`theorem_B_unique` consumes H6 as an integral equation on `Icc 0 T`, not as an ODE on `Ioi 0`) | H6 | W3b I14 `integral_eq_of_hasDerivAt` (forward FTC, P5) and I13 `class_member_integral_eq` (R6 3.vi' with the unused `hν'` dropped, D14; the right-hand side continuous through I8, `continuousOn_convFull` with I11's budgets, `lerayProj_continuous`; the initial value from `initial_condition`) | PROVED (`Tier9cFinal.lean` D, lines 1231, 1622; ReconP5.lean, ReconP4.lean) |
| G14 | H1, H3, H5 in `theorem_B_unique`'s spelling for `classFlow v` | the capstone | W3c `classFlow_zero`, `summable_classFlow` (W1's `summable_sob_coeff` at `m = 0, 1`), `divFree_classFlow` | PROVED (`Tier9cFinal.lean` E1; ReconP7.lean) |
| G15 | The two flows' budgets are per-flow existentials; `theorem_B_unique` wants ONE `E, Z` | the capstone | W3c: `max` inside the capstone (P7) and in the wrapper `unique_of_windows` (P5) | PROVED (`Tier9cFinal.lean` E2, E3; ReconP5.lean, ReconP7.lean) |
| G16 | From equal coefficient flows back to equal velocities at every `(x, t)` | the capstone | W3c `community_unique_velocity`: `classFlow_clock` (window `T := 2πt`) then W1's `u₀Real_coeff` on both slices | PROVED (`Tier9cFinal.lean` E3, line 1828; ReconP7.lean; PROVED from the sorry'd interface alone in `critique/feasibility/FeasCompose.lean`, the house pattern) |
| G17 | From equal velocities to the pressure: equal gradients through the class equation, then a function with zero gradient on `ℝ³` is constant | the pressure capstone | W3c `gradient_eq_of_velocity_eq`, `eq_add_const_of_gradient_eq` (`is_const_of_fderiv_eq_zero`), `community_unique_pressure` with `g t := p₁ 0 t - p₂ 0 t`, and the explicit form `community_unique_pressure_explicit` (D15) | PROVED (`Tier9cFinal.lean` E4, lines 1918, 1971; ReconP5.lean; the `g` evaluated by the statement critic, S4c) |
| G18 | Non-vacuity and sharpness of the two statements (the class inhabited by two DISTINCT members with the same nonzero datum; the pressure form sharp; the datum load-bearing; the sign of `ν'` unconstrained by membership; the flow of an arbitrary pair is junk) | the reader round | W3c `T9cProbe` (P8's eleven items) | PROVED (`Tier9cFinal.lean` E7; ReconP8.lean; re-proved against the tree by the statement critic, S1 to S3, S5) |
| G19 | Consistency with Tier 9: the exhibited witness's `classFlow` and the exhibited flow `c` | MUST HOLD | W3c `T9cProbe.classFlow_eq_of_flow`, `flow_witness_classFlow_eq` (mean-free datum; the general-mean identity is not claimed, D12) | PROVED (the design pass; `Tier9cFinal.lean:2220`) |
| G20 | The constant-datum case: every member on `u₀ = m` is the constant pair in velocity | consistency with the Galilean witness | W3c `const_datum_member_is_const`, `capstone_fires_on_const_datum_witness` | PROVED (`Tier9cFinal.lean` E6; ReconP7.lean) |
| G21 | The velocity capstone's `∀ t ≥ 0` was not shown sharp by the design's register (statement critic MINOR 1) | the reader round | W3c `T9cProbe.preHistory_in_class`, `velocity_not_unique_off_halfline` (D16) | PROVED (`critique/shape/ShapeProbe.lean` S9; re-compiled in `Tier9cFinal.lean:2321`) |

## 4. Frozen interfaces (statements freeze here)

Conventions. PROVED = full proof in `design/final/Tier9cFinal.lean` (compiled by this pass, exit 0 at the
pin, 0 sorry declarations), copied from the cited recon probe where the statement is unchanged, or glue
written by the design pass (only §6 items 8a and 8b, `classFlow_zero_eq`, `continuous_gradient_slice`,
`convection_coeff_vel`'s body) or by this pass (D15's body, from the statement critic's S4c). There is NO
COMPILED-only (sorry) statement in this blueprint. Every fenced statement below is extracted VERBATIM from
`Tier9cFinal.lean` by `design/final/gen_blueprint.py` through the orchestrator's own
`tools/byte_identity.decls_in_file` (statement = from the declaration keyword to the ` :=` that starts the
body, trailing whitespace stripped; comment lines inside statements count; named arguments `(n := 3)`,
`(f := 0)` are not body separators), so `tools/byte_identity.py <this file> <lo> <hi>
design/final/Tier9cFinal.lean` reports byte-identical by construction; recompute the block bounds with
`grep -n "^#### W"` before every run (a build-log insert above the blocks moves them). Re-run by this pass on
this file: W3a SliceExtract 16/16, W3a ConvectionCoeff 6/6, W3a ClassParseval 8/8, W3b ClassFlowODE 24/24
(23 theorems + `def classFlow`), W3c CommunityUnique 15/15, the §6 register 16/16 (15 theorems + `def
preHistory`); `check_capstone.py` on both capstones: byte-identical, 5 lines each. Route notes cite the
probe and declaration that proves each statement, with the line in `Tier9cFinal.lean`.

The preamble every built file keeps (the Tier 9 house pattern): `open Set Filter Topology MeasureTheory
InnerProductSpace UnitAddTorus`, `open scoped ContDiff Laplacian ComplexConjugate`, `local notation "ℝ³" =>
EuclideanSpace ℝ (Fin 3)`, `namespace TheoremB`, `open Community` (NOT exported by CommunityClass),
`noncomputable section`, and the three local measure instances NAMED with a file-unique prefix INSIDE the
section (`se_*`, `cc_*`, `cp_*`, `co_*`, `cu_*`, the prefixes the feasibility chain compiled;
`Tier9cFinal.lean` uses `df_*`) in every file that elaborates `mFourierCoeff` or unfolds `coeff` (all five
files do: A through `laplacian_coeff`, B and C throughout, D through the parametric integral, E through
`eq_of_mFourierCoeff_eq` and `T9cProbe`). NO file-level `set_option maxHeartbeats` (none was needed:
`Tier9cFinal.lean` compiles without any). A docstring on every frozen declaration under the rules of §7
(every frozen declaration of `Tier9cFinal.lean` now carries one, D18; the builder keeps them). Every unused
binder of D6 is kept and the linter warning expected (five in all, listed in the status header).

### 4a. Tier 9c, W3a (descent side: slices, the convection coefficient, Parseval and the budgets)

#### W3a: `TheoremB/SliceExtract.lean` (probe `design/final/Tier9cFinal.lean` section A, lines 63 to 434, exit 0, 0 sorry decls)

```
theorem isOnePeriodic_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) : IsOnePeriodic (fun x => derivWithin (v x ·) (Ici 0) τ)

theorem isOnePeriodic_laplacian_slice {v : ℝ³ → ℝ → ℝ³} (hper : ∀ t ≥ 0, IsOnePeriodic (v · t))
    {τ : ℝ} (hτ : 0 ≤ τ) : IsOnePeriodic (fun x => Δ (v · τ) x)

theorem isOnePeriodic_gradient_slice {p : ℝ³ → ℝ → ℝ} (hper : ∀ t ≥ 0, IsOnePeriodic (p · t))
    {τ : ℝ} (hτ : 0 ≤ τ) : IsOnePeriodic (fun x => gradient (p · τ) x)

theorem hasDerivAt_time_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (x : ℝ³) {τ : ℝ} (hτ : 0 < τ) : HasDerivAt (v x ·) (derivWithin (v x ·) (Ici 0) τ) τ

theorem continuous_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (fun x => derivWithin (v x ·) (Ici 0) τ)

theorem contDiff_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : ContDiff ℝ ∞ (fun x => derivWithin (v x ·) (Ici 0) τ)

theorem exists_bound_time_deriv_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {a b : ℝ} (ha : 0 ≤ a) : ∃ C : ℝ, ∀ x, ∀ τ ∈ Icc a b, ‖derivWithin (v x ·) (Ici 0) τ‖ ≤ C

theorem exists_bound_velocity {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {a b : ℝ} (ha : 0 ≤ a) : ∃ C : ℝ, ∀ x, ∀ τ ∈ Icc a b, ‖v x τ‖ ≤ C

theorem exists_bound_space_deriv {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {a b : ℝ} (ha : 0 ≤ a) : ∃ C : ℝ, ∀ x, ∀ τ ∈ Icc a b, ‖fderiv ℝ (v · τ) x‖ ≤ C

theorem contDiff_space_slice' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : ℝ³ → ℝ → F} (hw : ContDiffOn ℝ ∞ (↿w) slab) {τ : ℝ} (hτ : 0 ≤ τ) :
    ContDiff ℝ ∞ (w · τ)

theorem continuous_gradient_slice {p : ℝ³ → ℝ → ℝ} (hp : ContDiffOn ℝ ∞ (↿p) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (gradient (p · τ))

theorem contDiff_laplacian {V : ℝ³ → ℝ³} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => Δ V x)

theorem continuous_laplacian_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (fun x => Δ (v · τ) x)

theorem continuous_convection_slice {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (fun x => fderiv ℝ (v · τ) x (v x τ))

theorem isOnePeriodic_convection_slice {v : ℝ³ → ℝ → ℝ³}
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsOnePeriodic (fun x => fderiv ℝ (v · τ) x (v x τ))

theorem laplacian_coeff {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab) (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) (j : Fin 3) (n : Fin 3 → ℤ) : mFourierCoeff (descend fun x => (((Δ (v · τ) x) j : ℝ) : ℂ)) n = (((-((2 * Real.pi) ^ 2 * ‖freq n‖ ^ 2)) : ℝ) : ℂ) * mFourierCoeff (descend fun x => ((v x τ j : ℝ) : ℂ)) n
```
PROVED (full proofs in `Tier9cFinal.lean` A, every one copied from `recon/P1/ReconP1.lean` except
`contDiff_space_slice'` (P4:220) and `continuous_gradient_slice`'s one-line body, glue). Route notes: I3
`isOnePeriodic_time_deriv_slice` (P1:53, `derivWithin_congr` with the `EqOn` on `Ici 0`; line
78); `isOnePeriodic_laplacian_slice` (P1:72, `laplacian_translate` at
`eᵢ`; 101); `isOnePeriodic_gradient_slice` (P1:86, `gradient_translate`;
118); I1 `hasDerivAt_time_slice` (P1:101; 133);
I2 `continuous_time_deriv_slice` (P1:121, `continuousOn_fderivWithin` at `1 ≤ ∞`, `clm_apply`,
`comp_continuous`; 154); `contDiff_time_deriv_slice` (P1:135,
`ContDiffOn.fderivWithin` at `∞ + 1 ≤ ∞` by `le_rfl`; 168); I4
`exists_bound_time_deriv_slice` (P1:196; 232), I5 `exists_bound_velocity`
(P1:204; 242), I6 `exists_bound_space_deriv` (P1:212, `opNorm_comp_le` with
`norm_inl_le_one ℝ ℝ³ ℝ`; 252); `contDiff_space_slice'` (P4:220;
271); `continuous_gradient_slice` (P1:243 through P4's generic slice;
289); `contDiff_laplacian` (P1:282, componentwise through
`laplacian_ofReal_component` and `dirIter`; Mathlib has no smoothness rule for `Δ` at the pin;
328); `continuous_laplacian_slice` (P1:297; 347);
`continuous_convection_slice` (P1:303; 353);
`isOnePeriodic_convection_slice` (P1:309, the beta-redex `have` restatement;
359); I7 `laplacian_coeff` (P1:332, `laplacian_ofReal_component`,
`laplacian_eq_sum_dirIter`, `mFourierCoeff_finset_sum`, `mFourierCoeff_descend_dirIter` at `q = 2`,
`sum_sq_twist`; 386). The four slice facts that carried no docstring in the design
(`isOnePeriodic_laplacian_slice`, `isOnePeriodic_gradient_slice`, `continuous_gradient_slice`,
`continuous_laplacian_slice`) carry one in `Tier9cFinal.lean` (D18); statements unchanged (docstrings are
invisible to the byte-identity tool).
Shipped helpers (34, not fenced, not registered; copied from the section): `one_le_infty`, `two_le_infty`,
`infty_add_one_le`, `uniqueDiffOn_slab`, `isOnePeriodic_laplacian`, `isOnePeriodic_gradient`,
`isOnePeriodic_fderiv` (P4's generic form), `time_deriv_slice_eq`, `continuousOn_fderivWithin_slab`,
`continuousOn_time_deriv_joint`, `contDiffOn_fderivWithin_slab`, `contDiffOn_time_deriv_joint`, `rep1_mem`,
`norm_rep1_le`, `rep_apply`, `norm_rep_le`, `rep_mem_closedBall`, `window` (abbrev), `isCompact_window`,
`window_subset_slab`, `time_deriv_slice_rep`, `velocity_rep`, `fderiv_slice_rep`,
`continuous_gradient_of_contDiff`, `laplacian_ofReal_component`, `dirIter_two_apply`,
`laplacian_apply_eq_sum_dirIter`, `laplacian_eq_sum_dirIter`, `sum_sq_twist`, `continuous_ofReal_component`,
`isOnePeriodic_add`, `isOnePeriodic_sub`, `isOnePeriodic_convTerm`, `continuous_convTerm`.

#### W3a: `TheoremB/ConvectionCoeff.lean` (probe `design/final/Tier9cFinal.lean` section B, lines 436 to 692, = ReconP3.lean verbatim, exit 0, 0 sorry decls)

```
theorem mFourierCoeff_charSeries {a : (Fin 3 → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖)
    (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => ∑' k, a k * mFourier k z) n = a n

theorem summable_norm_conv {a b : (Fin 3 → ℤ) → ℂ}
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    Summable fun k => ‖∑' l, a l * b (k - l)‖

theorem coeffC_mul {f g : ℝ³ → ℂ} (hfp : IsOnePeriodic f) (hgp : IsOnePeriodic g)
    (hf : Continuous f) (hg : Continuous g)
    (hfs : Summable fun k => ‖mFourierCoeff (descend f) k‖) (hgs : Summable fun k => ‖mFourierCoeff (descend g) k‖)
    (n : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => f x * g x) n = ∑' l, mFourierCoeff (descend f) l * mFourierCoeff (descend g) (n - l)

theorem mFourierCoeff_factor {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (i j : Fin 3) (m : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) m
      = (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * coeff u m j

theorem convection_coeff_eq_convFull {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) (j : Fin 3) (n : Fin 3 → ℤ) : ∑ i : Fin 3, mFourierCoeff (descend fun x => ((u x i : ℝ) : ℂ) * (((fderiv ℝ u x (EuclideanSpace.single i 1)) j : ℝ) : ℂ)) n = ((-(2 * Real.pi) : ℝ) : ℂ) * (convFull (coeff u) n) j

theorem coeff_convection {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (n : Fin 3 → ℤ) (j : Fin 3) :
    coeff (fun x => fderiv ℝ u x (u x)) n j
      = ((-(2 * Real.pi) : ℝ) : ℂ) * (convFull (coeff u) n) j
```
PROVED (`Tier9cFinal.lean` B, `recon/P3/ReconP3.lean` lines 43 to 295 verbatim). Route notes:
`mFourierCoeff_charSeries` (P3:50, Route A, the `Vel`-packing through `uCont 0 c hc` and
`mFourierCoeff_uCont`; a nonzero mean mode allowed; 446);
`summable_norm_conv` (P3:95, discrete Young ℓ¹ ∗ ℓ¹ ⊆ ℓ¹ through `Summable.mul_of_nonneg`,
`shearEquiv.summable_iff`, `Summable.prod`; 491); `coeffC_mul` (P3:110, R6 3.iv
VERBATIM with `coeffC` unfolded; bundled descents, `hasSum_mFourier_series_apply_of_summable`,
`tsum_char_mul`; 506); `mFourierCoeff_factor` (P3:173, `(2πi mᵢ) · coeff u m j` through
`mFourierCoeff_descend_dirIter` at `q = 1`; 569); I10
`convection_coeff_eq_convFull` (P3:241, `Summable.tsum_finsetSum`, the `hdot` block of
`convection_classical` with `c := coeff u`, `convFull_apply` (Nonlinearity.lean:241), `push_cast; ring`: the
`-2π` is COMPUTED; 637); `coeff_convection` (P3:276,
`fderiv_apply_expand`, `Complex.ofReal_sum`, `mFourierCoeff_finset_sum`; 672).
Shipped helpers (12): `summable_conv_shear`, `summable_conv_term`, `dirDeriv_ofReal_component'`,
`factor_eq_dirDeriv`, `continuous_factor`, `isOnePeriodic_factor`, `summable_norm_coeff_factor`,
`summable_norm_coeff_component`, `vel_tsum_apply` (unconsumed, kept verbatim as the measured
component-extraction form), `convection_term_coeff`, `summable_convection_term`, `isOnePeriodic_mul`.

#### W3a: `TheoremB/ClassParseval.lean` (probe `design/final/Tier9cFinal.lean` section C, lines 694 to 982, = ReconP6.lean with the P1 interface proved, exit 0, 0 sorry decls)

```
theorem hasSum_sq_mFourierCoeff_descend {g : ℝ³ → ℂ} (hg : Continuous g)
    (hp : IsOnePeriodic g) :
    HasSum (fun n => ‖mFourierCoeff (descend g) n‖ ^ 2)
      (∫ z : UnitAddTorus (Fin 3), ‖g (rep z)‖ ^ 2)

theorem en_coeff_eq {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hcont : Continuous u) :
    Summable (fun n => ‖coeff u n‖ ^ 2) ∧
    en (coeff u) = ∫ z : UnitAddTorus (Fin 3), ‖u (rep z)‖ ^ 2

theorem ens_coeff_eq {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hu : ContDiff ℝ 1 u) :
    Summable (fun n => ‖freq n‖ ^ 2 * ‖coeff u n‖ ^ 2) ∧
    ens (coeff u) = (2 * Real.pi) ^ (-2 : ℤ) *
      ∑ i : Fin 3, ∫ z : UnitAddTorus (Fin 3),
        ‖fderiv ℝ u (rep z) (EuclideanSpace.single i 1)‖ ^ 2

lemma integral_le_of_bound {F : UnitAddTorus (Fin 3) → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ z, F z ≤ C) : ∫ z, F z ≤ C

lemma en_coeff_le_of_bound {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hcont : Continuous u)
    {C : ℝ} (hC : ∀ x, ‖u x‖ ≤ C) : en (coeff u) ≤ C ^ 2

lemma ens_coeff_le_of_bound {u : ℝ³ → ℝ³} (hper : IsOnePeriodic u) (hu : ContDiff ℝ 1 u)
    {D : ℝ} (hD : ∀ x, ‖fderiv ℝ u x‖ ≤ D) :
    ens (coeff u) ≤ (2 * Real.pi) ^ (-2 : ℤ) * (3 * D ^ 2)

theorem classFlow_budget {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T,
      en (coeff (v · (t / (2 * Real.pi)))) ≤ E ∧ ens (coeff (v · (t / (2 * Real.pi)))) ≤ Z

theorem summable_flow {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable (fun l => ‖coeff (v · τ) l‖ ^ 2) ∧
    Summable (fun l => ‖freq l‖ ^ 2 * ‖coeff (v · τ) l‖ ^ 2)
```
PROVED (`Tier9cFinal.lean` C, `recon/P6/ReconP6.lean` lines 30 to 236 and 250 to 330 verbatim; the two
`-- INTERFACE (P1)` stubs replaced by section A's I5, I6). Route notes: `hasSum_sq_mFourierCoeff_descend`
(P6:53, `hasSum_sq_mFourierCoeff` on `ContinuousMap.toLp`, `mFourierCoeff_toLp`, `coeFn_toLp`;
716); `en_coeff_eq` (P6:87, R6 3.iii-a VERBATIM, an EQUALITY:
`hasSum_sum` over the three components, `integral_finsetSum`; 750); `ens_coeff_eq` (P6:180,
R6 3.iii-b VERBATIM, an EQUALITY at `ContDiff ℝ 1`: `mFourierCoeff_descend_fderiv` per `(i, j)`,
`norm_sq_twist`, `sum_sq_coord_eq_norm_freq_sq`, `HasSum.mul_left ((2π)^(-2))`; 843);
`integral_le_of_bound` (P6:229, `integral_mono`, `probReal_univ`; 892);
`en_coeff_le_of_bound` (P6:259; 910); `ens_coeff_le_of_bound` (P6:268, `le_opNorm`,
`PiLp.norm_single`; 919); I11 `classFlow_budget` (P6:295, `E := C²`,
`Z := (2π)^(-2)·(3·D²)` from I5, I6 on `Icc 0 (T/(2π))`, `hs.of_le (WithTop.coe_le_coe.2 le_top)` for the
`C^1` input; 946); `summable_flow` (P6:314, H3 at every `τ ≥ 0`;
965).
Shipped helpers (9): `contDiff_one_ofReal_component`, `descendC` (def), `integrable_norm_sq_descend`,
`fderiv_ofReal_component`, `norm_sq_twist`, `sum_sq_coord_eq_norm_freq_sq`,
`norm_freq_sq_mul_norm_coeff_sq_eq`, `continuous_fderiv_apply_single_vec`, `summable_flow_clock`.

### 4b. Tier 9c, W3b (time regularity: the flow, the parametric integral, the forward FTC, the calibration in reverse, the mode ODE, the integral equation)

#### W3b: `TheoremB/ClassFlowODE.lean` (probe `design/final/Tier9cFinal.lean` section D, lines 984 to 1681, exit 0, 0 sorry decls)

The canonical spelling (P7 section 1; the only `def` of the file, fenced, not a ledger line), the torus
parametric integral (P2 sections (1) to (4); the `ha` binder of the two helpers (2) and (3b) dropped, D6),
the forward FTC (P5 section 1), and the calibration in reverse (P4 sections 0' to 5; I12 and I13 without
`hν'`, D14):

```
def classFlow (v : ℝ³ → ℝ → ℝ³) (t : ℝ) : (Fin 3 → ℤ) → Vel

theorem classFlow_apply (v : ℝ³ → ℝ → ℝ³) (t : ℝ) (k : Fin 3 → ℤ) :
    classFlow v t k = coeff (v · (t / (2 * Real.pi))) k

theorem classFlow_clock (v : ℝ³ → ℝ → ℝ³) (τ : ℝ) :
    classFlow v (2 * Real.pi * τ) = coeff (v · τ)

theorem classFlow_zero_eq (v : ℝ³ → ℝ → ℝ³) : classFlow v 0 = coeff (v · 0)

theorem continuousOn_coeff_of_dominated {G : ℝ³ → ℝ → ℂ} {a b C : ℝ} (ha : 0 ≤ a)
    (hG : ContinuousOn (↿G) slab) (hper : ∀ τ ≥ 0, IsOnePeriodic (G · τ))
    (hC : ∀ x, ∀ τ ∈ Icc a b, ‖G x τ‖ ≤ C) (n : Fin 3 → ℤ) :
    ContinuousOn (fun τ => mFourierCoeff (descend (G · τ)) n) (Icc a b)

theorem hasDerivAt_coeff_of_dominated {G G' : ℝ³ → ℝ → ℂ} {a b C : ℝ}
    (hcont : ∀ τ ∈ Ioo a b, Continuous (G · τ)) (hcont' : ∀ τ ∈ Ioo a b, Continuous (G' · τ))
    (hper : ∀ τ ∈ Ioo a b, IsOnePeriodic (G · τ))
    (hper' : ∀ τ ∈ Ioo a b, IsOnePeriodic (G' · τ))
    (hd : ∀ x, ∀ τ ∈ Ioo a b, HasDerivAt (G x ·) (G' x τ) τ)
    (hC : ∀ x, ∀ τ ∈ Ioo a b, ‖G' x τ‖ ≤ C) (n : Fin 3 → ℤ) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo a b) :
    HasDerivAt (fun τ => mFourierCoeff (descend (G · τ)) n)
      (mFourierCoeff (descend (G' · τ₀)) n) τ₀

theorem continuousOn_coeff_vel {V : ℝ³ → ℝ → ℝ³} {a b C : ℝ} (ha : 0 ≤ a)
    (hV : ContinuousOn (↿V) slab) (hper : ∀ τ ≥ 0, IsOnePeriodic (V · τ))
    (hC : ∀ x, ∀ τ ∈ Icc a b, ‖V x τ‖ ≤ C) (k : Fin 3 → ℤ) :
    ContinuousOn (fun τ => coeff (V · τ) k) (Icc a b)

theorem hasDerivAt_coeff_vel {V V' : ℝ³ → ℝ → ℝ³} {a b C : ℝ}
    (hcont : ∀ τ ∈ Ioo a b, Continuous (V · τ)) (hcont' : ∀ τ ∈ Ioo a b, Continuous (V' · τ))
    (hper : ∀ τ ∈ Ioo a b, IsOnePeriodic (V · τ))
    (hper' : ∀ τ ∈ Ioo a b, IsOnePeriodic (V' · τ))
    (hd : ∀ x, ∀ τ ∈ Ioo a b, HasDerivAt (V x ·) (V' x τ) τ)
    (hC : ∀ x, ∀ τ ∈ Ioo a b, ‖V' x τ‖ ≤ C) (k : Fin 3 → ℤ) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ioo a b) :
    HasDerivAt (fun τ => coeff (V · τ) k) (coeff (V' · τ₀) k) τ₀

theorem classFlow_continuousOn {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) (k : Fin 3 → ℤ) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => coeff (v · (t / (2 * Real.pi))) k) (Icc (0:ℝ) T)

theorem hasDerivAt_classFlow {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) (k : Fin 3 → ℤ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => coeff (v · (s / (2 * Real.pi))) k)
      ((1 / (2 * Real.pi) : ℝ) •
        coeff (fun x => derivWithin (v x ·) (Ici 0) (t / (2 * Real.pi))) k) t

theorem integral_eq_of_hasDerivAt {f g : ℝ → Vel} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0:ℝ) T)) (hg : ContinuousOn g (Icc (0:ℝ) T))
    (hd : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt f (g t) t) :
    ∀ t ∈ Icc (0:ℝ) T, f t = f 0 + ∫ s in (0:ℝ)..t, g s

theorem lerayProj_pressure_gradient {k : Fin 3 → ℤ} (hk : k ≠ 0) (phat : ℂ) :
    lerayProj k (WithLp.toLp 2 fun j => (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * phat) = 0

theorem coeff_add {w w' : ℝ³ → ℝ³} (hw : Continuous w) (hwp : IsOnePeriodic w)
    (hw' : Continuous w') (hwp' : IsOnePeriodic w') (n : Fin 3 → ℤ) :
    coeff (fun x => w x + w' x) n = coeff w n + coeff w' n

theorem coeff_sub {w w' : ℝ³ → ℝ³} (hw : Continuous w) (hwp : IsOnePeriodic w)
    (hw' : Continuous w') (hwp' : IsOnePeriodic w') (n : Fin 3 → ℤ) :
    coeff (fun x => w x - w' x) n = coeff w n - coeff w' n

theorem coeff_smul (a : ℝ) (w : ℝ³ → ℝ³) (n : Fin 3 → ℤ) :
    coeff (fun x => a • w x) n = ((a : ℝ) : ℂ) • coeff w n

theorem coeff_neg (w : ℝ³ → ℝ³) (n : Fin 3 → ℤ) :
    coeff (fun x => -w x) n = -coeff w n

theorem pressure_gradient_coeff {p : ℝ³ → ℝ → ℝ} (hp : ContDiffOn ℝ ∞ (↿p) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (p · t)) {τ : ℝ} (hτ : 0 ≤ τ) (n : Fin 3 → ℤ) :
    coeff (fun x => gradient (p · τ) x) n =
      WithLp.toLp 2 fun j => (2 * Real.pi * Complex.I * ((n j : ℤ) : ℂ)) *
        mFourierCoeff (descend fun x => ((p x τ : ℝ) : ℂ)) n

theorem lerayProj_pressure_gradient_coeff {p : ℝ³ → ℝ → ℝ} (hp : ContDiffOn ℝ ∞ (↿p) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (p · t)) {τ : ℝ} (hτ : 0 ≤ τ) (n : Fin 3 → ℤ) :
    lerayProj n (coeff (fun x => gradient (p · τ) x) n) = 0

theorem divFree_slice {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {τ : ℝ} (hτ : 0 ≤ τ) : DivFree (coeff (v · τ))

theorem divFree_deriv {c : ℝ → (Fin 3 → ℤ) → Vel} {k : Fin 3 → ℤ} {d : Vel} {t : ℝ} (ht : 0 < t)
    (hd : HasDerivAt (fun s => c s k) d t) (h0 : ∀ s ≥ 0, dotR (c s k) (freq k) = 0) :
    dotR d (freq k) = 0

theorem laplacian_coeff_vel {v : ℝ³ → ℝ → ℝ³} (hv : ContDiffOn ℝ ∞ (↿v) slab)
    (hper : ∀ t ≥ 0, IsOnePeriodic (v · t)) {τ : ℝ} (hτ : 0 ≤ τ) (n : Fin 3 → ℤ) :
    coeff (fun x => Δ (v · τ) x) n =
      (((-((2 * Real.pi) ^ 2 * ‖freq n‖ ^ 2)) : ℝ) : ℂ) • coeff (v · τ) n

theorem convection_coeff_vel {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (n : Fin 3 → ℤ) :
    coeff (fun x => fderiv ℝ u x (u x)) n = ((-(2 * Real.pi) : ℝ) : ℂ) • convFull (coeff u) n

theorem class_member_mode_ode {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    ∀ t > 0, ∀ k, HasDerivAt (fun s => coeff (v · (s / (2 * Real.pi))) k)
      ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • coeff (v · (t / (2 * Real.pi))) k
        + lerayProj k (convFull (coeff (v · (t / (2 * Real.pi)))) k)) t

theorem class_member_integral_eq {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, coeff (v · (t / (2 * Real.pi))) k = coeff u₀ k +
      ∫ s in (0:ℝ)..t, ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) •
          coeff (v · (s / (2 * Real.pi))) k
        + lerayProj k (convFull (coeff (v · (s / (2 * Real.pi)))) k))
```
PROVED. Route notes, the flow: `classFlow`, `classFlow_apply`, `classFlow_clock` (`recon/P7/ReconP7.lean` 38
to 53 verbatim, lines 991 to 1000); `classFlow_zero_eq` (P5:65's
`classFlow_zero` renamed, line 1008). The parametric integral (`recon/P2/ReconP2.lean`
76 to 286; the five `-- INTERFACE (P1)` stubs replaced by section A): `continuousOn_coeff_of_dominated`
(P2:99, `MeasureTheory.continuousOn_of_dominated` with the constant bound;
1037); `hasDerivAt_coeff_of_dominated` (P2:125,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `Ioo a b`, `.2`;
1063); `continuousOn_coeff_vel` (P2:188, `continuousOn_pi` and the
ℝ-linear `PiLp.continuousLinearEquiv` symm; 1121); `hasDerivAt_coeff_vel`
(P2:209, `hasDerivAt_pi`; 1142); I8 `classFlow_continuousOn` (P2:249, I5 on
`Icc 0 (T/(2π))`, `mapsTo_clock`; 1185); I9 `hasDerivAt_classFlow` (P2:263,
window `Ioo (τ/2) (2τ)`, I1 to I4, `HasDerivAt.scomp (x := t) (h := …)`; 1201).
The forward FTC: `integral_eq_of_hasDerivAt` (`recon/P5/ReconP5.lean` 73 to 85 verbatim;
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` on `0..t`, `hf.mono (Icc_subset_Icc le_rfl ht.2)`, no
`t = 0` case split; line 1231). The calibration in reverse
(`recon/P4/ReconP4.lean` 72 to 145, 163 to 218, 229 to 321, 366 to 373, 399 to 585; the nine `-- INTERFACE`
stubs replaced by sections A, B, C and this section; `convection_coeff_vel`'s body from `coeff_convection`,
D10): `lerayProj_pressure_gradient` (P4:100, R6 copy, `(2πi kⱼ) p̂` packed as `(2πi p̂) • castCV (freq k)`,
`lerayProj_smul_castCV_freq`; 1275); `coeff_add`/`coeff_sub` (P4:164, :179,
`PiLp.ext`, `mFourierCoeff_add/sub` through `integral_add/sub` and `integrable_of_continuous`;
1323, 1338); `coeff_smul`, `coeff_neg` (P4:194, :206, NO hypothesis,
`integral_const_mul`, `integral_neg`; 1353, 1365); `pressure_gradient_coeff`
(P4:237, `gradient_apply_eq_fderiv_single`, `ofRealCLM` `HasFDerivAt`, `mFourierCoeff_descend_fderiv` at
`ContDiff ℝ 1` by `of_le (by decide)`; 1387); `lerayProj_pressure_gradient_coeff`
(P4:264, every `n`, the `n = 0` case by `PiLp.ext` + `simp` with `dotR_zero_left` of CommunityData;
1414); `divFree_slice` (P4:281, W1's `divFree_coeff`;
1431); `divFree_deriv` (P4:296; 1446); `laplacian_coeff_vel` (P4:367, I7
packed; 1474); `convection_coeff_vel` (statement P4:378, body from B's
`coeff_convection`; 1484); I12 `class_member_mode_ode` (P4:417, R6 3.vi with `hν'`
dropped (D14): I9's derivative, `HasDerivAt.congr_deriv`, the class equation solved for the Laplacian term,
`coeff_add` twice, `coeff_smul`, `laplacian_coeff_vel`, `convection_coeff_vel`, the constants by
`field_simp; ring` on `PiLp.ext`, then `lerayProj k` of both sides through `lerayProj_of_divFree`
(`divFree_deriv`), `lerayProj_sub/add`, `lerayProj_real_smul`, the pressure gradient killed; holds for every
real `ν'`; 1511); I13 `class_member_integral_eq` (P4:527, R6 3.vi' with `hν'`
dropped (D14): I8, I11's budgets with the finite-sum bounds `sum_le_tsum` for `continuousOn_convFull`
(FullUnique.lean:349 pattern), `lerayProj_continuous`, I12 on `Ioo 0 T`, the initial value by `funext` +
`zero_div` + `initial_condition`, then I14; 1622).
Shipped helpers (18): `continuous_space_slice_of_continuousOn`, `continuousOn_time_slice_of_continuousOn`,
`continuousOn_uncurry_ofReal_component`, `hasDerivAt_ofReal_component`, `norm_ofReal_component_le`,
`mapsTo_clock`, `hasDerivAt_clock`, `dotR_castCV_freq`, `lerayProj_smul_castCV_freq`, `mFourierCoeff_add`,
`mFourierCoeff_sub`, `mFourierCoeff_neg`, `mFourierCoeff_const_mul`, `isOnePeriodic_ofReal_scalar`,
`lerayProj_of_divFree`, `class_eq_force_free`, `real_smul_eq_coe_smul_vel`, `lerayProj_real_smul`.

### 4c. Tier 9c, W3c (the two capstones, the pressure and its explicit form, the injectivity lemmas, the consistency corollaries, the register)

#### W3c: `TheoremB/CommunityUnique.lean` (probe `design/final/Tier9cFinal.lean` section E, lines 1683 to 2335, exit 0, 0 sorry decls)

H1, H3, H5 for a class member (P7 sections 1 and 2), the constancy lemma and the wrapper (P5); THE TWO
CAPSTONES (rung11 §4c, byte-identical), the pressure's two siblings and its explicit form (D15);
injectivity in tree spelling (P7 section 5, D3) and the consistency corollaries (P7 section 6):

```
theorem classFlow_zero {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    classFlow v 0 = coeff u₀

theorem summable_classFlow {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun l => ‖classFlow v t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖classFlow v t l‖ ^ 2)

theorem divFree_classFlow {ν' : ℝ} {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    {t : ℝ} (ht : 0 ≤ t) : DivFree (classFlow v t)

theorem eq_add_const_of_gradient_eq {q₁ q₂ : ℝ³ → ℝ}
    (h₁ : Differentiable ℝ q₁) (h₂ : Differentiable ℝ q₂)
    (h : ∀ x, gradient q₁ x = gradient q₂ x) :
    ∀ x, q₁ x = q₂ x + (q₁ 0 - q₂ 0)

theorem unique_of_windows {ν : ℝ} (hν : 0 < ν) {c₀ : (Fin 3 → ℤ) → Vel}
    {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel} (h10 : c₁ 0 = c₀) (h20 : c₂ 0 = c₀)
    (h1cont : ∀ k, ∀ T ≥ 0, ContinuousOn (fun s => c₁ s k) (Icc (0:ℝ) T))
    (h2cont : ∀ k, ∀ T ≥ 0, ContinuousOn (fun s => c₂ s k) (Icc (0:ℝ) T))
    (h1sum : ∀ t ≥ 0, Summable (fun l => ‖c₁ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ t l‖ ^ 2))
    (h2sum : ∀ t ≥ 0, Summable (fun l => ‖c₂ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₂ t l‖ ^ 2))
    (h1b : ∀ T ≥ 0, ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T, en (c₁ t) ≤ E ∧ ens (c₁ t) ≤ Z)
    (h2b : ∀ T ≥ 0, ∃ E Z : ℝ, ∀ t ∈ Icc (0:ℝ) T, en (c₂ t) ≤ E ∧ ens (c₂ t) ≤ Z)
    (h1div : ∀ t ≥ 0, DivFree (c₁ t)) (h2div : ∀ t ≥ 0, DivFree (c₂ t))
    (h1eq : ∀ T ≥ 0, ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k)))
    (h2eq : ∀ T ≥ 0, ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k))) :
    ∀ t ≥ 0, ∀ k, c₁ t k = c₂ t k

theorem community_unique_velocity {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∀ x, ∀ t ≥ 0, v₁ x t = v₂ x t

theorem community_unique_pressure {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∃ g : ℝ → ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + g t

theorem community_unique_pressure_gradient {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∀ x, ∀ t ≥ 0, gradient (p₁ · t) x = gradient (p₂ · t) x

theorem community_unique_pressure_of_velocity {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂)
    (hv : ∀ x, ∀ t ≥ 0, v₁ x t = v₂ x t) :
    ∃ g : ℝ → ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + g t

theorem community_unique_pressure_explicit {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³}
    {v₁ v₂ : ℝ³ → ℝ → ℝ³} {p₁ p₂ : ℝ³ → ℝ → ℝ}
    (h₁ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁)
    (h₂ : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂) :
    ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + (p₁ 0 t - p₂ 0 t)

theorem eq_of_mFourierCoeff_eq {f g : C(UnitAddTorus (Fin 3), ℂ)}
    (h : ∀ n, mFourierCoeff (⇑f) n = mFourierCoeff (⇑g) n) : f = g

theorem eq_of_coeff_eq {u₁ u₂ : ℝ³ → ℝ³} (h₁ : ContDiff ℝ ∞ u₁) (p₁ : IsOnePeriodic u₁)
    (h₂ : ContDiff ℝ ∞ u₂) (p₂ : IsOnePeriodic u₂) (h : coeff u₁ = coeff u₂) : u₁ = u₂

theorem eq_of_coeff_eq' {u₁ u₂ : ℝ³ → ℝ³} (h₁ : ContDiff ℝ ∞ u₁) (p₁ : IsOnePeriodic u₁)
    (h₂ : ContDiff ℝ ∞ u₂) (p₂ : IsOnePeriodic u₂) (h : coeff u₁ = coeff u₂) : u₁ = u₂

theorem const_datum_member_is_const (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν')
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p) :
    ∀ x, ∀ t ≥ 0, v x t = m

theorem capstone_fires_on_const_datum_witness (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p ∧
        ∀ x, ∀ t ≥ 0, v x t = m
```
PROVED. Route notes, E1 and E2 (`recon/P7/ReconP7.lean` 55 to 98; `recon/P5/ReconP5.lean` 89 to 165):
`classFlow_zero` (P7:56, `unfold classFlow; rw [zero_div]`, `funext` of `initial_condition`;
1689); `summable_classFlow` (P7:80, `summable_sob_coeff` at `m = 0, 1` with
`rw [classFlow_apply, mul_zero, pow_zero, one_mul]` / `rw [classFlow_apply, mul_one]`;
1713); `divFree_classFlow` (P7:94; 1727);
`eq_add_const_of_gradient_eq` (P5:97, `fderiv_sub`, `(toDual ℝ ℝ³).symm.injective`,
`is_const_of_fderiv_eq_zero`; 1743); `unique_of_windows` (P5:116,
`@theorem_B_unique ν (max E₁ E₂) (max Z₁ Z₂) t …` at `right_mem_Icc`; 1762).
E3, THE VELOCITY CAPSTONE (`recon/P7/ReconP7.lean` 130 to 179 verbatim, with the I13 call sites without
`hν'`, D14; line 1828): window `T := 2πt` (`mul_nonneg (by positivity) ht`),
`ν := 2πν'`, I11 twice and the maxima, I8 in the `fun s => classFlow v₁ s k` shape, I13, `theorem_B_unique
(E := max E₁ E₂) (Z := max Z₁ Z₂)` with `classFlow_zero`, `summable_classFlow`, `divFree_classFlow`,
evaluated at `⟨hT, le_refl _⟩`; then `classFlow_clock` and `funext`, then the three-step `calc` through
`u₀Real_coeff` on both slices. Periodicity enters at H2 (`h₁.isOnePeriodic_velocity`), H3/H5
(`periodic_slice`), H6 (through I12's slices) and last at the inversion (the statement critic, item 5a:
without it two non-periodic pairs have equal `classFlow` and different velocities, S5). E4, THE PRESSURE
CAPSTONE (`recon/P5/ReconP5.lean` 209 to 220 verbatim with the interface stub replaced by the theorem above,
line 1918): `g t := p₁ 0 t - p₂ 0 t`, `eq_add_const_of_gradient_eq` with
`TimeConstantWitness.pressure_slice` and `gradient_eq_of_velocity_eq`; `community_unique_pressure_gradient`
(P5:224; 1938); `community_unique_pressure_of_velocity` (P5:233, no
`0 < ν'`; 1950); `community_unique_pressure_explicit` (this pass,
D15: the velocity capstone then the body of the previous theorem;
1971). The docstrings of the two siblings are the statement critic's
MINOR 2 text verbatim (D18). E5 and E6 (`recon/P7/ReconP7.lean` 185 to 247 verbatim):
`eq_of_mFourierCoeff_eq` (P7:185, `mFourierBasis_repr`, `mFourierCoeff_toLp`, `repr.injective`,
`ContinuousMap.toLp_inj`; 1987); `eq_of_coeff_eq` (P7:198, three lines through
`u₀Real_coeff`; 2000); `eq_of_coeff_eq'` (P7:207, the torus-side route through bundled
descents, `descend_fiber`, `Complex.ofReal_injective`, `PiLp.ext`; 2009);
`const_datum_member_is_const` (P7:234, one term against `T9Probe.const_pair_in_class`;
2036); `capstone_fires_on_const_datum_witness` (P7:242;
2044).
Shipped helpers (7): `smooth_slice`, `periodic_slice`, `fderiv_eq_of_gradient_eq`, `unique_of_windows'`,
`slice_eq_of_velocity_eq`, `derivWithin_eq_of_velocity_eq`, `gradient_eq_of_velocity_eq`. The register
`namespace T9cProbe` is fenced in §6.

## 5. Wave plan

**Doctrine (binding; it produced twelve waves with zero blockers across Tiers 8a, 8b and 9).**
Per wave, one Workflow: one builder (statements byte-for-byte from §4; only bodies change; if a
frozen statement cannot be proved as written, keep it, add a sibling, record spec drift; register
every frozen theorem in BOTH `TheoremB.lean` and `AxiomCheck.lean`; local measure instances
NAMED with a file-unique prefix inside `noncomputable section`; no file-level `maxHeartbeats`; a
docstring on every frozen declaration; run the gate), then two readers in parallel
(statement-shape/vacuity with cheap-witness and inhabitation probes; proof-and-pin with
Mathlib-name probes, an independent gate run and a double-import instance test), then a fix pass
for blockers and majors. Then the ORCHESTRATOR re-runs the gate, re-checks byte-identity of every
frozen statement against this file with its own script (`audit-tier9c/tools/byte_identity.py`,
`check_capstone.py`; recompute block line bounds with `grep -n "^#### W"` before every run; a
build-log insert above the blocks moves them; the runs are persisted under
`audit-tier9c/build-w*/orchestrator/`), runs the banned-words grep on every new file, commits
with the harness trailer (`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`), lays the
ladder tag of §5, writes the build-log entry into this file at commit time, and updates memory.

The orchestrator's tools for the byte-identity step are `audit-tier9c/tools/byte_identity.py` (block bounds
by `grep -n "^#### W"` on THIS file) and `tools/check_capstone.py` with the two expected-text files
`design/final/expected_community_unique_velocity.txt` and `…_pressure.txt` (written by the orchestrator from
rung11 §4c lines 953 to 975; run by this pass against `Tier9cFinal.lean`: byte-identical, 5 lines each); the
banned-words grep is `tools/banned_words.sh` (its only permitted hits are the rung11 rule lines carried
verbatim in this file, §7).

| Wave | Files | Delivers (source in `Tier9cFinal.lean`) | Copied verbatim / glue / new | Risk | Lines / sessions | Ledger (+`#print axioms` lines) | Tag |
|---|---|---|---|---|---|---|---|
| W3a | `SliceExtract.lean`, `ConvectionCoeff.lean`, `ClassParseval.lean` | sections A, B, C: I1 to I7, the slice facts, I10, `coeffC_mul`, the two Parseval equalities, I11, H3 (16 + 6 + 8 frozen theorems; 34 + 12 + 9 helpers) | Verbatim: P1 (all but two merges), P3 (all), P6 (all), the P4 slice facts; glue: `continuous_gradient_slice`'s body; the four slice-fact docstrings of D18 are in the probe; new: the three file headers (instances `se_*`, `cc_*`, `cp_*`) | LOW (compiled end to end in `DesignFinal.lean` and `Tier9cFinal.lean`, and as a module chain by the feasibility critic; three transcriptions with a one-file import chain, SliceExtract before ClassParseval) | measured on the critic's split files: 400 + 288 + 322 = 1010 lines, about 1070 with headers; 1 builder session, 1 reader round | 30 lines: 391 → 421 (16 + 6 + 8), 3 import lines in each registration file | none |
| W3b | `ClassFlowODE.lean` | section D: `classFlow`, the parametric integral, I8, I9, I14, `coeff` linearity, the pressure gradient, DivFree, I12, I13 (1 def + 23 frozen theorems; 18 helpers) | Verbatim: P7 section 1, P2 (all but the `ha` drop), P5's I14, P4 (all but `convection_coeff_vel`'s body and the `hν'` drop of D14); glue: `classFlow_zero_eq`, `convection_coeff_vel`; new: the file header (instances `co_*`), docstrings on the P4 helpers (about 30 lines) | LOW (compiled; the one substantive file; the mathematically load-bearing I12 and I13 keep their proofs unchanged under D14) | 745 lines on the split file, 760 to 790 with the helper docstrings; 1 builder session, 1 reader round (the proof reader re-derives the constant ledger of I12 by hand) | 23 lines: 421 → 444, 1 import line each | none |
| W3c | `CommunityUnique.lean` | section E: H1/H3/H5, the wrapper, THE TWO CAPSTONES, the pressure siblings and the explicit form, the injectivity lemmas, the consistency corollaries, the register `T9cProbe` (15 registered theorems + `preHistory` + 2 helpers) | Verbatim: P7 (all), P5 sections 2 to 4, P8 (all but the local `classFlow`), the statement critic's S9 (item 9); this pass's `community_unique_pressure_explicit`; the design's §6 items 8a, 8b; new: the file header (instances `cu_*`), the announcement's PROPOSED sentence in the header (D9), the supersession note for the Tier 9 "sized candidate" sentences (§8 item 11) | LOW (compiled; the capstones byte-identical to rung11 §4c and to the orchestrator's expected files; the composition also compiled from the sorry'd interface by the feasibility critic) | 625 lines on the split file at the design's count, about 720 with the header and the D15/D16 additions (about 65 lines); 1 builder session, 1 reader round (the shape reader runs the §6 register and probes the hypotheses' load-bearing status) | 30 lines: 444 → 474 (15 + 15), 1 import line each | `t9-unique-green` |

Ledger arithmetic from 391: 391 + 30 + 23 + 30 = 474, every line on the standard triple; the 83
`#print axioms` lines at the end of `Tier9cFinal.lean` are the future ledger lines verbatim (namespaces
included; 68 as `TheoremB.<name>`, 15 as `TheoremB.T9cProbe.<name>`). Three registered names end in a prime
(D8): count `depends on axioms: [...]` on the bracket pattern after joining wrapped lines, never with a
quote-delimited regex (which reads 471). Registration formats, read from the tree by the feasibility critic:
`TheoremB.lean` = 64 bare `import TheoremB.<File>` lines (last: `import TheoremB.CommunityData`);
`AxiomCheck.lean` = the same 64 import lines + 391 `#print axioms` lines (the Tier 9 register under
`TheoremB.T9Probe.<name>` from line 441); `lakefile.toml` declares `[[lean_lib]] name = "TheoremB"` with
default roots, so a new module enters `lake build` only through its import line in `TheoremB.lean` (a
forgotten line leaves the module unbuilt and `AxiomCheck.lean` fails at its import; both files must be
touched per wave). Ladder: `t9-complete` (332790f) → W3a commit → W3b commit → W3c commit +
`t9-unique-green`; a `lake env leanchecker TheoremB.<Module>` replay of every new module before the tag
(status header); every wave in its own chat, never in the same chat as any other tier's work. Sessions: three
builder sessions and three reader rounds, about 3 to 4 sessions in all (the recon's "6 to 8 sessions, MED" of
rung11 §8 item 4 is superseded: the recon did the mathematics; both critics agree, no estimate differs by
more than 10 percent). Compile budget for the gate after W3c: the five modules build in about 6 minutes in
sequence with a sibling process running (119 + 70 + 109 + 25 + 53 s measured on the chain); `lake build`
parallelises the leaves.

## 6. Vacuity / must-fail register (compiled; land in `namespace T9cProbe` of `CommunityUnique.lean`)

All fifteen theorems (and the def `preHistory`) are PROVED in `design/final/Tier9cFinal.lean` E7 (lines 2051
to 2335) on the standard triple; eleven are `recon/P8/ReconP8.lean` verbatim (41 to 187, the junk items
rewritten with `classFlow_zero_eq`), two are the design's (8a, 8b), two are the statement critic's
(`critique/shape/ShapeProbe.lean` S9, item 9, D16). Registered (15 ledger lines); the two register helpers
`gradient_add_const_eq`, `uncurry_pressure_add` are shipped, not registered; `preHistory` is fenced (its
statement is its body, the byte-identity tool cuts at ` :=`) and carries no ledger line. The fenced
statements are extracted from `Tier9cFinal.lean` like the frozen ones (byte-identity recommended, not
required, rung11 D6; re-run by this pass: 16/16).

```
theorem pressure_add_time_function_in_class {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v
      (fun x t => p x t + g t)

theorem pressure_add_const_in_class {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) (C : ℝ) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v
      (fun x t => p x t + C)

theorem pressure_add_id_in_class {ν' : ℝ} {u₀ : ℝ³ → ℝ³}
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v
      (fun x t => p x t + t)

theorem pressure_not_unique :
    ¬ (∀ (ν' : ℝ), 0 < ν' → ∀ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ →
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ →
      ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t)

theorem pressure_not_unique_up_to_const :
    ¬ (∀ (ν' : ℝ), 0 < ν' → ∀ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ →
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ →
      ∃ C : ℝ, ∀ x, ∀ t ≥ 0, p₁ x t = p₂ x t + C)

theorem two_members_same_datum {ν' : ℝ} (hν' : 0 < ν') :
    ∃ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
      u₀ ≠ 0 ∧
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ ∧
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ ∧
      p₁ ≠ p₂

theorem different_data_not_forced_equal :
    ∃ (ν' : ℝ), 0 < ν' ∧
      ∃ (u₀ u₀' : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀' (f := 0) v₂ p₂ ∧
        ∃ x, ∃ t ≥ 0, v₁ x t ≠ v₂ x t

theorem class_inhabited_all_visc (ν' : ℝ) :
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (0 : ℝ³ → ℝ³) (f := 0) v p

theorem const_datum_two_members (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0)
      (fun _ _ => m) (fun _ _ => 0) ∧
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p

theorem classFlow_junk : ∃ v : ℝ³ → ℝ → ℝ³, u₀Real (coeff (v · 0)) ≠ (v · 0)

theorem classFlow_junk' : ∃ v : ℝ³ → ℝ → ℝ³, u₀Real (classFlow v 0) ≠ (v · 0)

theorem classFlow_eq_of_flow {ν' : ℝ} (hν' : 0 < ν') {u₀ : ℝ³ → ℝ³} (h0 : coeff u₀ 0 = 0)
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (h1 : c 0 = meanFree (coeff u₀))
    (h2 : ∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t))
    (h3 : ∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2))
    (h4 : ∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ)))
    (h5 : ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = meanFree (coeff u₀) k + ∫ s in (0:ℝ)..t,
      ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)))
    (h7 : ∀ t ∈ Ici (0:ℝ), en (c t) ≤ en (meanFree (coeff u₀)) ∧
      ens (c t) ≤ ens (meanFree (coeff u₀)))
    {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p) :
    ∀ t ≥ 0, classFlow v t = c t

theorem flow_witness_classFlow_eq :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ → coeff u₀ 0 = 0 →
      κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = meanFree (coeff u₀) ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0)
          (galV (meanVec (coeff u₀)) (vReal c)) (galP (meanVec (coeff u₀)) (pReal c)) ∧
        ∀ t ≥ 0, classFlow (galV (meanVec (coeff u₀)) (vReal c)) t = c t

def preHistory (m : ℝ³) : ℝ³ → ℝ → ℝ³

theorem preHistory_in_class (ν' : ℝ) (m : ℝ³) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (0 : ℝ³ → ℝ³) (f := 0)
      (preHistory m) (0 : ℝ³ → ℝ → ℝ)

theorem velocity_not_unique_off_halfline :
    ∃ (ν' : ℝ), 0 < ν' ∧
      ∃ (u₀ : ℝ³ → ℝ³) (v₁ v₂ : ℝ³ → ℝ → ℝ³) (p₁ p₂ : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₁ p₁ ∧
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v₂ p₂ ∧
        v₁ ≠ v₂
```

What each item settles:

1. **The pressure form is the SHARP form** (`pressure_add_time_function_in_class` and its two corollaries):
   every member `(v, p)` stays a member under `p ↦ p + g t` for every smooth `g` (the momentum equation
   sees only the spatial gradient), so the `∃ g : ℝ → ℝ` of `community_unique_pressure` cannot be tightened;
   `pressure_not_unique` refutes `p₁ = p₂` pointwise (the rest pair and its shift by `1` at `(0, 0)`),
   `pressure_not_unique_up_to_const` refutes the `∃ C` form (the shift by `t` needs `C = 0` at `t = 0` and
   `C = 1` at `t = 1`). The smoothness `hg : ContDiff ℝ ∞ g` is load-bearing: the rest pair with the pressure
   shifted by a STEP in time is NOT a member (the statement critic's S8, not carried).
2. **Non-vacuity** (`two_members_same_datum`): for every `ν' > 0` the hypothesis set of BOTH capstones is
   inhabited by two DISTINCT pairs on a NONZERO datum (the Tier 9 witness on the shear datum and the same
   velocity with the pressure shifted by `1`); the velocity conclusion is consistent with them (same `v`) and
   the pressure conclusion needs its function of time. Re-proved against the tree by the statement critic
   (S1).
3. **The datum is load-bearing** (`different_data_not_forced_equal`): the rest pair and the constant pair at
   `e₀` are members at `ν' = 1` with different velocities.
4. **Membership says nothing about the sign of `ν'`** (`class_inhabited_all_visc`): the rest pair is a member
   for EVERY real `ν'` (the statement critic compiled the rest pair at `ν' = 0` and `ν' = -1`, S1b, S1c); the
   capstones' `0 < ν'` is consumed by `theorem_B_unique`, not implied by membership; nothing is claimed at
   `ν' ≤ 0` (rule 14).
5. **The constant datum** (`const_datum_two_members` with `const_datum_member_is_const` and
   `capstone_fires_on_const_datum_witness` of §4c): the constant pair and the Tier 9 witness are both members
   on `u₀ = m`, and the velocity capstone identifies every member's velocity with `m` on `t ≥ 0`, consistent
   with the Galilean witness.
6. **Junk note** (`classFlow_junk`, `classFlow_junk'`; rule 10): `classFlow` is total; for a pair outside the
   class (`v x _ := x`) it is a well-typed object whose inversion fails (`inversion_fails_off_class`); every
   docstring that mentions `classFlow v` for a general `v` says so. Sharpened by the statement critic (S5,
   not carried): two NON-periodic pairs have EQUAL `classFlow` at every time and DIFFERENT velocities, so
   coefficient equality transfers to velocity equality only through `u₀Real_coeff`, which needs the slice
   smooth and one-periodic.
7. **MUST HOLD, consistency with Tier 9** (`classFlow_eq_of_flow`, `flow_witness_classFlow_eq`; D12): on a
   MEAN-FREE datum (`coeff u₀ 0 = 0`) meeting the smallness hypothesis, the flow `c` exhibited by
   `theorem_B_community_periodic_data_flow` is `classFlow` of the member it exhibits (and of every member on
   that datum) at every `t ≥ 0`; proved by `theorem_B_unique` with the sibling's clauses 1 to 5 and 7 on one
   side and W3's H1 to H6 on the other, the `∃ κ` being the sibling's own. For a datum with a nonzero mean the
   identity is not `classFlow v = c` (the boost changes the phases and the zero mode); the general-mean form
   is an open item (§8), not a failure of the design.
8. **The velocity capstone's `∀ t ≥ 0` is SHARP** (`preHistory_in_class`,
   `velocity_not_unique_off_halfline`; D16): `preHistory m` (the rest state for `t ≥ 0`, the constant `m` for
   `t < 0`) with the zero pressure is a member on the zero datum for every real `ν'` (every field of the class
   only looks at `t ≥ 0`); so at `ν' = 1`, datum `0`, `f = 0`, two members have `v₁ ≠ v₂` (they differ at
   `t = -1`) while agreeing at every `t ≥ 0`; function equality `v₁ = v₂` is FALSE as a consequence of
   membership, and the capstone's conclusion cannot be strengthened to it.
9. **Quantifier order, compiled by the statement critic (S4, not carried):** with the `∃ g` of the pressure
   capstone moved inside `∀ x` the statement is TRIVIAL with no class hypothesis (`g := fun _ => p₁ x t -
   p₂ x t`), so the frozen order (`∃ g` outside `∀ x, ∀ t ≥ 0`) is the only one with content; the `g` the
   proof produces is `t ↦ p₁ 0 t - p₂ 0 t`, now a frozen statement of its own (`community_unique_pressure_explicit`,
   D15), so no `x`-dependence is smuggled. Also compiled and not carried: the pointwise `∀ t, ∃ E Z` is trivial
   (S6; the frozen I11 quantifies `E, Z` before `t`); a step function is continuous at `0` and not
   `ContinuousOn (Icc 0 2)` (S7; I8 is window continuity, not a point fact).
10. **COMPOSITION, PROVED THREE WAYS:** both capstones on the standard triple in `DesignFinal.lean` and in
    `Tier9cFinal.lean` (interface proved); with `sorryAx` entering ONLY through I8, I11, I13 in
    `critique/feasibility/FeasCompose.lean` (interface sorry'd; the H1/H3/H5 bricks and the pressure bricks
    interface-free); the pressure from the sorry'd velocity capstone in `FeasComposeP.lean`.
    `const_datum_member_is_const` and `capstone_fires_on_const_datum_witness` CONSUME the velocity capstone and
    are on the standard triple, which confirms by composition that it is proved, not sorry'd.
11. **NOT PROBED (and out of scope):** the general-mean identity of D12; a competitor outside the class (a
    non-smooth or non-periodic pair: the capstones say nothing about it); `f ≠ 0`; `ν' ≤ 0` (the class is
    inhabited there, item 4, and `theorem_B_unique` is not available there; nothing is claimed).

## 7. Audit register

Claim-wording rules 1 to 11 of rung11 §7, carried over VERBATIM (copy them from
`context/rung11-tier9-blueprint.md` §7 including the Tier 9 amendments), binding on every
docstring, header, commit message, tag message and announcement sentence of this tier; plus the
W3 additions:

12. **Uniqueness wording.** Say "uniqueness inside OUR COPY of the community class at `f = 0`",
    never "uniqueness of Navier-Stokes solutions"; the pressure is unique up to a function of
    time, never "the pressure is unique"; the result is a corollary of `theorem_B_unique`
    (Tier 4) through the datum bridge (Tier 9 W1), the energy method in the enstrophy class,
    textbook, nothing new; priority hedged and named where it arises (HeliCorgi's local mild
    uniqueness on `ℝ³` and uda-lab/leray-hopf are the neighbours; OpenAI and Alpöge-Buckmaster
    for the breakdown side).
13. **The Tier 9 capstones' "existence only" wording stays as written** (they are frozen); W3's
    capstones are what makes uniqueness citable in the class, said in W3's own docstrings and, as
    PROPOSED wording only after the capstone ships, in the announcement (the user decides; the
    Tier 9 section was adopted as written on 13 Sep 2026, the Tier 8b section is still proposed).
14. **Hypotheses named.** Every sentence describing a capstone names `0 < ν'` (consumed by
    `theorem_B_unique`, not implied by membership: the constant pair is a member for every real
    `ν'`), the same datum `u₀`, `f = 0`, and OUR COPY of the class; nothing about `ν' ≤ 0`.

The rung11 §7 text, carried VERBATIM (rules 1 to 9, the Tier 9 amendments, rules 10 and 11):

Claim-wording rules, carried over VERBATIM from rung10 §7 and binding on every
docstring, header, commit message, tag message and announcement sentence of
this tier:

1. **Constants.** Never the bare two-word phrase (the adjective "explicit"
   directly before "constants"); always say of what form and how exported. 8b: "`κ` and the
   inherited Sobolev growth constants are of explicit form, exported as
   compiled existentials; the window constants of the time-derivative
   chain (`WindowL1`, `hbound`, the `u`-majorants) are UNTRACKED
   existentials produced by the Leibniz induction" — the design's blanket
   phrase overclaimed and is withdrawn. 8a: "`κ_forced = 8·K` is of
   explicit form up to the lattice-kernel sum `C_K`, exported as a compiled
   existential; the force thresholds `G ≤ ν²·Es`, `8·G ≤ ν²·Zs` are literal
   expressions". No numeric value of any constant anywhere.
2. **No resolution-prize language** (neither the prize's name nor the
   institute's, no verb of resolution, no priority superlatives — no claim of
   being the first to machine-check anything), even though the upstream
   docstrings use such language. The statement critic's grep of the design probes for the
   banned-word list (its report carries the list; it covers the bare
   constants phrase, the prize and institute names, the priority
   superlatives, and claims of newness) returned no hits. Re-grep before
   every tag; this file is written to return no hits itself.
3. **Priority hedged and named**: leray-hopf, HeliCorgi, Miller; OpenAI and
   Alpöge-Buckmaster now too. Nothing here is new mathematics: the
   bootstrap, the M-test, the real-part bridge, the barrier lemma and the
   small-Grashof regime are textbook. The within-convex tsum engine is
   "absent from Mathlib at the pin (grep-verified), not new mathematics" —
   never "genuinely new".
4. **Name both upstream statements** (§2a) and position the 8b result as
   the POSITIVE statement's conclusion restricted to the trap class with
   `f = 0`; say it touches neither upstream `sorry`. The 8a corollary is
   "Comparator-adjacent, coefficient language", with the corrected
   hypothesis wording ("no flow confined to the box", §4a F4).
5. **Existence only** for `theorem_B_community_periodic` (the class has no
   uniqueness clause); point to `theorem_B_unique` via clauses 1–7 of the
   pinned form.
6. **Proposed announcement sentence (user's call, and NOT before W4
   ships):** "for data in the campaign's small class, OUR copy of the
   community's periodic solution class
   `NavierStokesExistenceAndSmoothnessPeriodic (ν/(2π)) u₀ 0 v p` is
   inhabited by the eternal flow (compiled); this is the conclusion of
   the upstream positive statement restricted to that data class with
   `f = 0`; both upstream statements are untouched."

Tier 9 additions to the rules (binding here, same force):

7. **The datum.** Tier 9's capstone quantifies over real-space data in the
   community's own `InitialVelocityConditionPeriodic`; its smallness
   hypothesis is on the MEAN-FREE part of the datum's coefficient field
   (`κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀)) < (2π ν')⁴`),
   which must be said in every sentence that describes the capstone; never
   "for every small datum" without saying small in which quantity. The
   constant datum `u₀ = m` (mean `m`, mean-free part `0`) satisfies the
   hypothesis for every `ν'` and is handled by the Galilean change, not
   excluded; the rest state is the case `m = 0`.
8. **Textbook, not new.** The Fourier inversion for smooth periodic functions
   (Mathlib supplies the pointwise inversion for continuous functions with
   summable coefficients at the pin: `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`)
   and the Galilean invariance are textbook; say so; no claim of newness for
   either; no priority claim; no em-dashes in new prose.
9. **Existence only** for the Tier 9 capstone as well; uniqueness of the
   COEFFICIENT flow is `theorem_B_unique`; uniqueness inside the community
   class in real-space vocabulary is a sized candidate (W3), not a delivered
   result, until and unless it ships.

**Amendments to the verbatim rules above, applied by this pass (where the verbatim text and an
amendment differ, the amendment governs; the verbatim text is kept so that the skeleton can be
diffed against this file):**

- Rule 1, Tier 9 instance: "`κ` is that of `theorem_B_community_periodic` (hence of
  `theorem_B_joint_smooth`), of explicit form and exported as a compiled existential; the
  decay constants `C_q` of the datum bridge and the sup bounds `M` are UNTRACKED existentials
  produced by `choose`; the `√3` and `(√3/2π)^q` factors are literal expressions". No numeric
  value of any constant anywhere.
- Rule 6, Tier 9 instance (ADOPTED by the user on 13 Sep 2026 as written, after the capstone
  shipped with W2; the record of the proposal: PROPOSED only; the user's call; NOT before the capstone ships with
  W2, `t9-complete`): "for every datum in the community's own periodic initial-velocity
  condition whose mean-free coefficient part is small in the sense `κ · en (meanFree (coeff
  u₀)) · ens (meanFree (coeff u₀)) < (2πν')⁴`, OUR copy of the community's periodic solution
  class `NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` is inhabited (compiled); this
  is the conclusion of the upstream positive statement
  `navier_stokes_existence_and_smoothness_periodic` under that smallness hypothesis with
  `f = 0`; nothing about general data, nothing about the breakdown statement
  `navier_stokes_breakdown_periodic`; both upstream statements are untouched; existence only;
  the Fourier inversion and the Galilean invariance are textbook." The announcement carries the
  diff record of rung10 §2a.
- Rule 7, CORRECTED (RC1, statement critic M1, compiled `capstone_hyp_const_datum_fails_at_
  zero_visc`): the last sentence reads "The constant datum `u₀ = m` (mean `m`, mean-free part
  `0`) satisfies the hypothesis for every `ν' > 0` (indeed for every `ν' ≠ 0`; at `ν' = 0` it
  reads `0 < 0`) and is handled by the Galilean change, not excluded; the rest state is the
  case `m = 0`." The verbatim "for every `ν'`" is false as written and must not be copied into
  any docstring; `Tier9Final.lean` carries the corrected sentence. Rule 7's second sentence
  gains (RC2): the mean vector `meanVec (coeff u₀)` enters no hypothesis (register
  `capstone_hyp_shifted_iff`); the mean is removed by the Galilean change and nothing else is
  said about it.
- Rule 10 (new, from the design). **Junk values.** `descend` and `coeff` are total; outside
  `InitialVelocityConditionPeriodic` they are well-typed junk, and the register carries the
  compiled failure of the inversion for `id`. Every docstring that mentions `coeff u` for a
  general `u` says so.
- Rule 11 (new). **The seven clauses.** Never "exactly the hypothesis set of `theorem_B_unique`"
  (statement critic M3): the seven clauses of the flow sibling SUPPLY `theorem_B_unique`'s
  hypotheses on every window `Icc 0 T` with `E := en (meanFree (coeff u₀))`, `Z := ens (meanFree
  (coeff u₀))`; `theorem_B_unique` consumes neither `RealField`, nor clause 6, nor the `κ` bound
  (FullUnique.lean:327-345). Never "VERBATIM" for the clause block without the measured
  qualification of D10.

Tier 9c instances of the amended rules (this pass; same force):

- Rule 1, Tier 9c instance: "the budgets `E := C ^ 2`, `Z := (2 * Real.pi) ^ (-2 : ℤ) * (3 * D ^ 2)` of I11
  are UNTRACKED existentials produced by the compactness bounds I5, I6 (`IsCompact.exists_bound_of_continuousOn`);
  the constants of the calibration, `(2π)²` in I7, `2π` in I10, `2πν'` in I12, are literal expressions
  computed by the kernel". No numeric value of any constant anywhere; never the bare two-word phrase.
- Rule 6, Tier 9c instance: the PROPOSED sentence of §1b D9, the user's call, NOT before the capstone ships
  with W3c (`t9-unique-green`); the Tier 9 sentence stays adopted as written; the Tier 8b sentence stays
  proposed.
- Rule 9, superseded WHEN W3c lands and not before: "uniqueness inside the community class in real-space
  vocabulary is a sized candidate (W3), not a delivered result, until and unless it ships" becomes true in
  its second half at `t9-unique-green`; the Tier 9 headers that quote it are not edited (built files are not
  edited for prose); the `CommunityUnique.lean` header records the supersession (§8 item 11).
- Rule 10, Tier 9c instance: `classFlow` is total (register items 6 and 8; every docstring that mentions
  `classFlow v` for a general `v` says so).

**Banned-words grep record of this pass** (the orchestrator's `tools/banned_words.sh`, with its byte em-dash
test, plus a Python count of U+2014 and U+2013): `design/final/Tier9cFinal.lean`: CLEAN, U+2014 = 0,
U+2013 = 0; this file, run after generation: every hit is inside the rung11 §7 text carried VERBATIM above
(rule 2's own negated priority phrase, flagged by the script's definite-article test, and the three
em-dashes inside rules 1, 2 and 3); the one en-dash is rule 5's, verbatim; no sentence written by this pass
carries a hit, an em-dash or an en-dash (the exact hit lines are recorded in the §8 record of this pass's
tool runs, written after generation). The W3-phrase grep of the statement critic (`uniqueness of Navier`,
`pressure is unique` without `up to`, the ordinal, the n-word adjective, `resolv`) was re-run by this pass on
both files: 0 hits in new prose. The feasibility critic's trap T1 was re-worded by this pass ("the earliest
`LEAN_PATH` root") because the critic's wording contained the script's definite-article pattern.

**Byte-identity record of this pass.** Both capstones: byte-identical to the orchestrator's
`design/final/expected_community_unique_velocity.txt` and `…_pressure.txt` through
`tools/check_capstone.py` (exit 0, 5 lines each) against `Tier9cFinal.lean`. The fenced blocks of §4 and §6
are extracted from `Tier9cFinal.lean` by the ruler's own `decls_in_file`, so `tools/byte_identity.py` on
this file reports byte-identical by construction (re-run after generation on every `^#### W` block and the
§6 register; counts in the §4 preamble). Statement drift of `Tier9cFinal.lean` against `DesignFinal.lean`,
complete: I12 and I13 without `hν'` (D14); `community_unique_pressure_explicit` added (D15);
`preHistory`, `preHistory_in_class`, `velocity_not_unique_off_halfline` added (D16); everything else
byte-identical (the feasibility critic's 81 fenced declarations of the design are the 81 of this file
except the two D14 statements). Statement drift of the design against the probes, unchanged: the `ha` drop
of D6 and the rename `classFlow_zero_eq` (D2); proof drift D10.

**Statement-shape facts to carry (from the recon, the design, the critics and this pass):**

- The mode ODE I12 holds for every real `ν'` and now says so (no `hν'`, D14); I13 likewise. The budgets of
  I11 and the window facts I8, I14 carry an unused `hT` (`Icc 0 T` is empty for `T < 0`; content-free, not
  weakening, S6').
- The pressure is unique up to a function of time ONLY; the register compiles the failure of `p₁ = p₂` and
  of the `∃ C` form; `g t := p₁ 0 t - p₂ 0 t` is a genuine function of time, exhibited by
  `community_unique_pressure_explicit`.
- The velocity is unique on `t ≥ 0` ONLY; the register compiles two members with `v₁ ≠ v₂` (item 8).
- The class's ContDiffOn set `Set.univ ×ˢ Set.Ici 0` is accepted where `slab` is asked (abbrev, no rewrite);
  the class's `∀ t ≥ 0, IsOnePeriodic (v · t)` passes to `hper : ∀ τ ≥ 0, …` unchanged.
- The inline spelling `coeff (v · (s / (2 * Real.pi))) k` and `fun s => classFlow v s k` are accepted by
  `theorem_B_unique` with no `show` (one delta at default transparency), both through intermediate `have`s
  and by direct plugging (P7, `ReconP7Measure.lean`); `theorem_B_unique` takes ONE `E` and ONE `Z` for both
  flows (FullUnique.lean:327 to 345), supplied as `max E₁ E₂`, `max Z₁ Z₂`.
- `coeff_smul` and `coeff_neg` hold with NO continuity or periodicity hypothesis (`integral_const_mul`,
  `integral_neg` are unconditional); `coeff_add`, `coeff_sub` need both for both fields.
- The whole convection chain never asks for a zero mode: `mFourierCoeff_charSeries` and `coeffC_mul` hold
  with `a 0 ≠ 0`; the derivative factor's coefficient vanishes at the mean mode through the `(2πi mᵢ)` factor.
- `hasDerivAt_coeff_of_dominated` takes every hypothesis on the open window `Ioo a b` and needs no endpoint
  version; `theorem_B_unique` consumes derivatives only through the integral equation (I13 through I14 with
  `hd` on `Ioo 0 T`).
- Byte-identity rule, as in rung11: it covers the instantiation (`(f := 0)`, `(n := 3)`), the one-line
  spellings of the VERBATIM interface statements (I1, I2, I3, I4, I5, I6, I7, I10, `coeffC_mul` are ONE-LINE
  statements in P1/P3 and in `Tier9cFinal.lean`; the builder keeps them on one line), comment lines inside
  statements (none in W3), and a `def` whose statement is its body (`preHistory`: the tool cuts at ` :=`, so
  the fenced text is the signature; the body `fun _ t => if t < 0 then m else 0` is checked by eye).
- Spec drift to record when W3 lands: none in the frozen tree (no earlier file is edited); the Tier 9
  headers' "sized candidate" sentences become stale and are recorded as superseded in the W3c header, not
  struck.

**Pin traps measured in this tier's probes** (carry into every builder brief; the full verbatim list with
file:line evidence is `recon/traps-all.md`, 60 items; the ones every wave meets, then the critics' and this
pass's additions):

- `IsCompact.exists_bound_of_continuousOn'` (primed) is the multiplicative version; the additive twin for
  `Vel`, `ℝ³`, CLM codomains is the unprimed `IsCompact.exists_bound_of_continuousOn`.
- `ContinuousLinearMap.norm_inl_le_one` takes `𝕜 E F` EXPLICITLY (`norm_inl_le_one ℝ ℝ³ ℝ`);
  `opNorm_comp_le` takes the outer map first.
- At `WithTop ℕ∞`, `le_top` closes neither `1 ≤ ∞` nor `∞ + 1 ≤ ∞`; `WithTop.coe_le_coe.2 le_top`,
  `by decide`, `by simp` close the former, `le_rfl` (`ENat.coe_top_add_one` is rfl) the latter;
  `hs.of_le (WithTop.coe_le_coe.2 le_top)` at `ContDiff ℝ 1`; `ContDiff.continuous_fderiv(_apply)` take
  `hn : n ≠ 0` (`by simp` at `∞`), `hu.differentiable (by norm_num)` at `1`.
- The periodicity lemmas applied at `x i` deliver `(fun x => …) (x + e) = (fun x => …) x` UN-beta-reduced;
  `rw` fails on a beta-reduced goal; restate through a `have` with the reduced type, then `rw` (P1's
  `isOnePeriodic_convection_slice`; P6's `set … with hg` variant).
- `derivWithin_congr` takes the `EqOn` first and the point equality second; membership in `Ici 0` is
  definitionally `0 ≤ τ`.
- `HasDerivAt.scomp` has the point IMPLICIT and `t / (2π)` is not a higher-order pattern: pass `(x := t)
  (h := fun s : ℝ => s / (2 * Real.pi))`.
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` returns `Integrable ∧ HasDerivAt`; take `.2`; `hF_meas`
  as `eventually_of_mem (Ioo_mem_nhds …)`; the measure pinned as `(volume : Measure (UnitAddTorus (Fin 3)))`;
  `norm_mFourier_apply` is a TREE lemma (PeriodicLift.lean:113); `Complex.norm_real` lives in
  Analysis/Complex/Norm.lean.
- The ℝ-linear `(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm` packs a
  `HasDerivAt`/`ContinuousOn` over ℝ into `Vel` with no `restrictScalars`; the smul in I9 is the plain
  ℝ-action on `Vel` (measured with `pp.explicit`).
- `PiLp.norm_single` takes `p` AND the family explicitly (`PiLp.norm_single 2 (fun _ : Fin 3 => ℂ) 0 (a k)`);
  `PiLp.single_apply` then `if_pos rfl`; `EuclideanSpace.single_apply`/`norm_single` deprecated.
- `Summable.tsum_finsetSum` carries a `SummationFilter`; the working swap is `Finset.sum_congr rfl (fun i
  (_ : i ∈ Finset.univ) => …)` then `← Summable.tsum_finsetSum (fun i (_ : i ∈ Finset.univ) => …)`;
  `Summable.prod` (needs `CompleteSpace`) gives the marginal in one step.
- `coeffC_mul` instantiated with named `(f := …) (g := …)` and consumed via `.trans` handles the beta-redex
  `descend fun x => (fun x => …) x * (fun x => …) x`; a `rw` with the product lambda would not match;
  `rw [factor_eq_dirDeriv …]` matches only when the lambda is the whole argument.
- `Continuous.add` yields `Continuous (f + g)` (the Pi sum): state the lambda type explicitly in a `have`
  before `coeff_add` (P4's `hDCc`).
- `lerayProj_smul` is ℂ-scalar only; a real scalar on `Vel` is first rewritten as the cast complex scalar
  (`real_smul_eq_coe_smul_vel`, `lerayProj_real_smul`).
- The class's force term at `(f := 0)` elaborates as `(0 : ℝ³ → ℝ → ℝ³) x τ` and goes by `simp only
  [Pi.zero_apply, add_zero]`; inside a `show` it must carry the ascription.
- `gradient f x` is definitionally `(toDual 𝕜 F).symm (fderiv 𝕜 f x)`: gradient equality is fderiv
  equality by `(toDual ℝ ℝ³).symm.injective`; `gradient_add_const` does not exist at the pin (`unfold
  gradient` then `fderiv_add_const`).
- `theorem_B_unique`'s `ν E Z T` are ∀-binders in the TYPE: set the budgets positionally or with `(E := …)
  (Z := …)`; `positivity` does not consume `ht : t ≥ 0` for `0 ≤ 2 * Real.pi * t` (`mul_nonneg (by
  positivity) ht`).
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` accepts `a = b`; `Set.Icc_subset_Icc_right` does not
  grep at the pin (`Icc_subset_Icc le_rfl h`); `sub_right_injective` is the to_additive of
  `div_right_injective` (not greppable by its own name).
- A slice after `≠`/`=` must be parenthesised (`≠ (v · 0)`); `contDiff_id` is accepted for `fun t => t` only
  up to the delta of `id`.
- `simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_mul_sum]` also pulls the constant out of the
  other side; finish with `zpow_neg, zpow_ofNat, ← mul_assoc, inv_mul_cancel₀, one_mul`.
- `HasSum.congr_fun` takes `∀ x, g x = f x` with `g` the NEW function (un-symmed).
- A let-bound `g : C(T³, ℂ)`: `exact hj` with `hj : coeff u₁ n j = coeff u₂ n j` closes `mFourierCoeff (⇑g₁)
  n = mFourierCoeff (⇑g₂) n` (rfl through the let; `simpa` does not).
- `probReal_univ` fires on the torus volume through the three local named instances; the probe-unique
  instances compile alongside the tree's `cd_*` (no collision; every new file names its own; the feasibility
  critic's `FeasDoubleImport.lean` re-measured it with `df_*` next to ContinuousRep, FourierDeriv,
  CoeffExtract and DatumBridge).
- The register's `preHistory` (item 8): `derivWithin_congr` on `Ici 0` with `if_neg (not_lt.2 hs)`,
  `contDiffOn_const.congr fun q hq => if_neg (not_lt.2 hq.2)` for `velocity_smooth`, and the seven class
  fields in the order `navier_stokes, div_free, initial_condition, velocity_smooth, pressure_smooth,
  isOnePeriodic_velocity, isOnePeriodic_pressure` under `refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩` (P8's
  measured order); the final `simp at h1` closes `m 0 = (0 : ℝ³) 0` after `if_pos (by norm_num : (-1:ℝ) < 0)`.
- T1 (feasibility critic, NEW). Lean's module lookup stops at the earliest `LEAN_PATH` root that contains a
  `TheoremB` directory: a session olean dir prepended to `LEAN_PATH` makes `import TheoremB.DatumBridge` fail
  with "object file … does not exist" although the tree's olean is later on the path; symlink every
  `.lake/build/lib/lean/TheoremB/*` into the session olean dir (`dag/chain.sh`, second attempt: five exit 0).
- T2 (feasibility critic, NEW). `lean --root=<srcdir> -o <olean> -i <ilean> <file>` compiles a session file
  AS A MODULE (`--root` fixes the module name `TheoremB.X` from the path); a proposed module chain can be
  compiled in the session directory without touching the tree, which is how §1a's intra-W3 arrows were
  measured.
- T5 (feasibility critic, NEW, generator). A probe line range that ends inside the NEXT declaration's
  docstring compiles to "unexpected token 'end'; expected 'lemma'" at the file's `end`; cut ranges at a
  blank line before a `/--`.
- T6 (feasibility critic). `simp [mFourierCoeff]` does not close the zero-mode coefficient of a constant on
  `UnitAddTorus (Fin 3)`; add `mFourier_zero` (Analysis/Fourier/AddCircleMulti.lean:61).
- T7 (feasibility critic, harness). The Bash tool's `run_in_background` with an inner `&` reports "completed"
  at once while the child `lean` keeps running; without an inner `&` the notification arrives at the real
  exit (this pass's compile, about 3 minutes with no sibling process).
- zsh: quote every `echo` string (a bare `==`/`====` expands); `--include='*.lean'` quoted; `grep -c` on zero
  matches exits 1; `set -- $r` does not word-split; the machine's `grep` is `ugrep` and rejects `\b` inside a
  `( |$|\b)` alternation; the sorry warning is `declaration uses`, the error format is "error:" mid-line.
- One compile of a probe importing `TheoremB.CommunityData` takes 2 to 4 minutes with sibling processes
  running; `Tier9cFinal.lean` (2431 lines) took about 3 minutes alone.

Pin traps carried forward from rung11 §7 (all in force), verbatim:

Pin traps measured in this tier's probes (recon, design, critics, this pass; carry into every
builder brief; the tree-wide traps of rung10 §7 remain in force):

- `open Community` is NOT exported by CommunityClass; autoImplicit is on under `lake env lean`,
  so an unopened `IsOnePeriodic` silently auto-binds ("Function expected at IsOnePeriodic").
- Dot-notation on `hf : IsOnePeriodic f` is looked up in `TheoremB.Community.IsOnePeriodic`; a
  lemma named `TheoremB.IsOnePeriodic.foo` is invisible to `hf.foo` (the error names
  `Function.foo`); declare `theorem Community.IsOnePeriodic.foo` inside `namespace TheoremB`.
- The three MeasureSpace local instances must sit INSIDE `noncomputable section` (else
  `lean.dependsOnNoncomputable`); the `Fact ((0:ℝ) < 1)` instance is NOT needed at the pin.
- `sub_zsmul` is the to_additive of `zpow_sub`: `(m - n) • a = m • a + -(n • a)`; add
  `sub_eq_add_neg`. `Int.induction_on` alternatives are `zero`/`succ`/`pred`.
- The three coercion spellings `(↑s : UnitAddCircle)`, `((s : ℝ) : AddCircle (1:ℝ))`,
  `(QuotientAddGroup.mk s : AddCircle (1:ℝ))` are the SAME `Expr`; `fiber x i =
  QuotientAddGroup.mk (x i)` is `rfl` at default transparency, `with_reducible rfl` FAILS.
- `contDiff_succ_iff_fderiv_apply` has a THIRD conjunct at the pin (`n = ω → AnalyticOnNhd`);
  `contDiff_infty_iff_fderiv` + `contDiff_clm_apply_iff` is the route to `ContDiff ℝ ∞` of a
  directional derivative; `ContDiff.differentiable` needs `∞ ≠ 0` (`by simp`).
- `integral_finset_sum` is deprecated (2026-04-08): `integral_finsetSum`. `Summable.of_norm_bounded`
  takes `hg` FIRST at this pin. `Summable.tsum_eq_add_tsum_ite` needs `[DecidableEq]`
  (`classical`). `uCont_apply` is a `HasSum` statement: `(uCont_apply j c hc z).tsum_eq` then `rfl`
  for `smul = mul`.
- A `let`-bound `g : C(T³, ℂ)`: state the summability on `descend f` first and apply
  `Summable.of_norm` by term; `simpa` does not see through the `let`; `rfl` closes
  `mFourierCoeff (⇑g) n = coeff u n j` at default transparency.
- `fderiv_comp_sub` and `iteratedFDeriv_comp_sub` are unconditional (FDeriv/Add.lean:930,
  FTaylorSeries.lean:969) but NOT usable as bare `rw` patterns under a lambda: give `f`
  explicitly or go through a wrapper lemma. `ContDiffAt.laplacian_add` wants the Pi sum with
  an explicit `(… : ℝ³ → ℝ³)` ascription; `laplacian_const` is function-level.
- `HasFDerivWithinAt.comp_hasFDerivAt` / `.comp_hasDerivWithinAt` take the point FIRST; the
  curve `σ ↦ (x - σ • m, σ)` needs the `_of_eq` variant with `rfl`; `hasDerivAt_id' τ`,
  `hasDerivAt_const τ x₀`, `hasFDerivAt_const c x` take their points explicitly.
- `(2 : WithTop ℕ∞) ≤ ∞`: `exact_mod_cast le_top` FAILS, `simp` no progress, `norm_num` fails;
  `WithTop.coe_le_coe.2 le_top` and `by decide` succeed (R4 `CastProbe.lean`).
- `push_neg` is deprecated (warning): `push Not` compiles (this pass, `capstone_hyp_not_universal`).
- The pin's unused-simp-argument linter names `PiLp.toLp_apply` in the `Vel`-packing `simp only`
  (not `Complex.real_smul`); deleting it compiles (feasibility, re-measured by this pass). The
  file-level `maxHeartbeats 400000` is unnecessary (feasibility, re-measured by this pass:
  `Tier9Final.lean` compiles without it).
- zsh: a bare `==` in an `echo` string expands (`=R2 not found`); quote every echo string.
  `set -- $r` does not word-split. `grep -c` on zero matches exits 1 and the Bash tool reports
  a failure although the output is right. Lean's sorry warning uses backticks (grep
  `declaration uses`); the error format is "error:" mid-line (grep `: error`).
- `tools/byte_identity.py` could not see `abbrev` and `tools/banned_words.sh`'s `grep -P`
  em-dash test was a no-op on macOS grep; both FIXED by the orchestrator (§8 item 8).

Textbook sources (cited, not ours; NO copy on this machine; theorem numbers UNVERIFIED and to be filled by a
reader with the books, hedged until then): as rung11 §7 (Temam Ch. III; Robinson-Rodrigo-Sadowski Ch. 6 and
7; Constantin-Foias Ch. 10; Foias-Manley-Rosa-Temam Ch. II; Grafakos on the torus); for the uniqueness in the
enstrophy class the relevant chapter is the one on strong solutions and their uniqueness in each of the
Navier-Stokes texts; for differentiation under the integral sign any measure-theory text. Priority hedged and
named where it arises: leray-hopf (weak existence), HeliCorgi/ns-mns2-flowmap-bridge (local mild uniqueness
on `ℝ³`, 18 Aug 2026), Miller, Alpöge-Buckmaster, OpenAI (the breakdown side); nothing here is new
mathematics (the energy-method uniqueness in the enstrophy class, the differentiation under the torus
integral and the Fourier inversion are textbook) and no priority is claimed.

Honesty ledger for this pass:

| Grade | Items |
|---|---|
| Compiled by THIS pass (exit 0) | `design/final/Tier9cFinal.lean` (`lake env lean` at the pin, `design/final/compile1.log`: exit 0, 0 errors, 0 sorry decls, 83 of 83 `#print axioms` lines on the standard triple, no `sorryAx`, 5 warnings = the four `hT` binders of D6 and the `τ` note) |
| Checked by THIS pass with the orchestrator's tools (unedited) | `tools/check_capstone.py` on both capstones against `design/final/expected_*.txt` (exit 0, byte-identical, 5 lines each); `tools/byte_identity.py` on this file against `Tier9cFinal.lean` for every `^#### W` block and the §6 register (counts in the §4 preamble); `tools/banned_words.sh` on `Tier9cFinal.lean` (CLEAN) and on this file (hits only in the verbatim rung11 block); the Python counts of U+2014 and U+2013 on both files |
| Generated by THIS pass | `Tier9cFinal.lean` from `DesignFinal.lean` by `design/final/make_final.py` (every replacement matched exactly once; 2328 → 2431 lines); this file from `design/final/blueprint_template.md` by `design/final/gen_blueprint.py` (the skeleton's status header, §1, §2 and §7 text and the rung11 §7 rules and traps inserted VERBATIM by line range; every fenced block extracted by the ruler's `decls_in_file`) |
| Read by this pass, not re-compiled | the eight recon probes and their `notes.md`, `recon-summary.md`, `traps-all.md`, `verified-names-all.md`, `recon-results.json`, `orchestrator-recompile/SUMMARY.txt` and `VERIFIED.md` (all eight exit 0, sorry counts as reported); `design/DesignFinal.lean`, `design/compile1.log`, `design/design.md`, `design/make_design_final.py`, `design/gen_design.py`, `design/design_template.md`; `critique/shape/ShapeProbe.lean`, `compile3.log`, `report.md`; `critique/feasibility/report.md` and the file list it cites; the skeleton; rung11 §§1 to 8 and its build log; Tier 9's `design.md`, `Tier9Final.lean`, `gen_blueprint.py`, `make_final.py` (format only); the tree by grep: `FullUnique.lean:327` (name only), the import lines of `CommunityClass.lean` through `CommunityData.lean` as the design lists them; `git rev-parse`, `git tag`, `git log --oneline`, `git status`, `df -h`, `ps` |
| Reported by the critics or the recon, not verified here | every Mathlib signature and line number they cite; the critics' exit codes, axiom outputs and timings; the module-chain compile (`dag/`); the import probes (`design/imports/`); the cross-file use table (`03-xdeps.txt`); the name-clash scans; the 176/163/335 counts; the split-file line counts |
| Derived, not compiled | the line and session estimates; the ledger arithmetic (391 → 421 → 444 → 474); the wording rules; D14's "strictly stronger" (a statement with one hypothesis fewer, compiled, trivially implies the old one); the general-mean identity of D12 (stated as NOT claimed) |
| Cited, not ours | the textbook sources above (theorem numbers unverified) |
| Not run | `scripts/check_axioms.sh` (the baseline log `gate/baseline-gate.log` was read: GREEN 391); `lake build`; `lake env leanchecker`; the module chain; nothing under the repository was written; the three orchestrator tools were not edited (D13) |
| ORCHESTRATOR, independently (13 Sep, before this pass) | the gate baseline (`bash scripts/check_axioms.sh`, GREEN 391, counted on the bracket pattern); the eight recon probes recompiled (`recon/orchestrator-recompile/`); the two expected-text files for `check_capstone.py` written from rung11 §4c |

ORCHESTRATOR'S RE-RUN (13 Sep 2026, before the planning commit; every run persisted under
`audit-tier9c/design/final/orchestrator/`, inserted at the end of §7 so that no line this file cites moves):
`design/final/Tier9cFinal.lean` recompiled by the orchestrator with `lake env lean` at the pin: exit 0, 0
errors, 0 sorry declarations, 83 of 83 `#print axioms` lines on exactly `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`, 5 warnings (the four `hT` binders of D6 and the `τ` note), sha256
`7a2a108ce42e78c8b6098e53d2c2edb0d4d7a80a201085b4cd41df49d6d43772`, identical to the author's
(`SUMMARY.txt`, `Tier9cFinal.log`). `tools/byte_identity.py` on this file against the probe, block bounds
recomputed by `grep -n "^#### W"` (the orchestrator closes each block at the next header, so its bounds read
519 to 598, 599 to 644, 645 to 701, 702 to 866, 867 to 1044, and the §6 register 1045 to 1214): 16/16, 6/6,
8/8, 24/24, 15/15, 16/16 (`byte_identity_planning.log`). `tools/check_capstone.py` on both capstones
against `design/final/expected_community_unique_velocity.txt` and `expected_community_unique_pressure.txt`
(written by the orchestrator from rung11 §4c before the design pass): byte-identical, 5 lines each.
`tools/banned_words.sh`: `Tier9cFinal.lean` CLEAN; this file 4 hits, every one inside the rung11 §7 rule
text carried verbatim (lines 1248, 1254, 1255, 1265) plus rule 5's en-dash at line 1273, the known
exemption; Python count U+2014 = 3 and U+2013 = 1 in this file, 0 and 0 in the probe
(`banned_words_blueprint.log`, `banned_words_probe.log`). The eight recon probes were recompiled by the
orchestrator before the design pass (`recon/orchestrator-recompile/VERIFIED.md`: every probe exit 0, the
sorry counts and the `sorryAx` cones as the agents reported, the interface statements identical modulo
whitespace across the probes that restate them). Repository: `git status --short` empty, HEAD `dc3bd8f`, 30
tags, `git log --oneline | wc -l` = 72 (the skeleton's "70 commits" was carried from a memory note, not
counted; 72 is the count, which settles §8 item 14). Disk 5.6 GiB free after the critics' probes (the
`audit-tier9c/` directory itself is 5.8 MB: the feasibility critic's module chain symlinked the tree's
oleans rather than copying them).

## 8. Open blockers and decisions for the user

None blocks W3a. Open items, each with the decision this blueprint takes and what remains the user's call;
the changes of the two critics and their disposition are listed in item 12 (none silently dropped):

1. **The namespace** (D1). DECIDED: plain `TheoremB` for every frozen theorem; `T9cProbe` for the register.
   User's call: none, unless the capstones are wanted under a sub-namespace (not recommended: the Tier 9
   capstones are cited as `TheoremB.<name>`).
2. **The tag ladder** (D7). DECIDED: one tag `t9-unique-green` after W3c; W3a and W3b commit without a tag;
   every new module replayed by `lake env leanchecker TheoremB.<Module>` before the tag. User's call: whether
   an intermediate tag after W3b (`t9c-mode-ode-green`) is wanted for the calibration in reverse; cost nil;
   not recommended (nothing is citable before the capstone).
3. **The announcement wording** (D9, rules 12 to 14). PROPOSED only, after `t9-unique-green`; the user
   decides, as with the Tier 9 section (adopted 13 Sep 2026). The one-sentence form, written out: "Inside
   OUR COPY of the community's periodic solution class `NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p`
   with `0 < ν'` and `f = 0`, two members with the same datum `u₀` have the same velocity at every point and
   every `t ≥ 0` and pressures that differ by a function of time alone (compiled,
   `community_unique_velocity`, `community_unique_pressure`, `community_unique_pressure_explicit`); this is a
   corollary of `theorem_B_unique` (Tier 4) through the datum bridge (Tier 9 W1), the textbook energy method
   in the enstrophy class; nothing about `ν' ≤ 0`, forced data, general data, competitors outside the class or
   the breakdown statement `navier_stokes_breakdown_periodic`; the positive statement
   `navier_stokes_existence_and_smoothness_periodic` and the breakdown statement are both untouched; the
   neighbours are HeliCorgi's local mild uniqueness on `ℝ³` and uda-lab/leray-hopf; nothing here is new
   mathematics." Whether to name the neighbours in the sentence itself or in the surrounding paragraph is the
   user's call.
4. **Shipping the injectivity lemmas** (D3). DECIDED: `eq_of_mFourierCoeff_eq`, `eq_of_coeff_eq`,
   `eq_of_coeff_eq'` frozen and registered in `CommunityUnique.lean` (three ledger lines; the handoff asked for
   the former). User's call: drop `eq_of_coeff_eq'` (the second proof) to save a line; not recommended (it is
   the only consumer of the torus-side lemma).
5. **The unused binders** (D6, D14). DECIDED: `hν'` dropped from I12 and I13 (D14, compiled); the four `hT`
   binders kept (content-free; dropping I11's would change its shape). User's call: strip the `hT` binders in
   the built files at the cost of one explicit `T` at every `classFlow_budget` call site; not recommended for
   this tier.
6. **The explicit pressure form** (D15). DECIDED: frozen and registered (one ledger line). User's call: ship
   it as an unregistered helper instead (the statement critic's wording); cost nil either way; not
   recommended (a consumer-facing statement should not be able to drift).
7. **The MUST-HOLD for a datum with a nonzero mean** (D12). DECIDED: the mean-free instance is compiled (§6
   item 7); the general identity `classFlow (galV m (vReal c)) t k = e^{-2πi (k·m) t} c t k + m δ_{k0}` is NOT
   compiled and NOT claimed. User's call: whether to commission it as a register item in a later wave (about
   80 lines: the coefficient of a translated field is the phase-shifted coefficient, `mFourierCoeff` of
   `x ↦ f (x - a)`, plus the zero-mode shift); not needed by any capstone.
8. **The smallness sibling** (rung11 §8 item 2), **trailer uniformity** (rung11 §8 item 6), **textbook
   theorem numbers** (rung11 §8 item 7), **the upstream hash and the upstream statement name in the
   announcement** (rung11 §8 item 5, carried from rung10 §8 item 1 and the Tier 8b handoff): carried,
   unchanged, still the user's call; W3 adds the uniqueness chapter references (§7) with the same hedge.
9. **`vel_tsum_apply`** (P3) is shipped unconsumed (kept verbatim as the measured component-extraction form).
   User's call: drop it; cost nil either way.
10. **Docstrings.** Every frozen declaration of `Tier9cFinal.lean` carries one (D18 closed the design's §8
    item 9 for the frozen statements); the helpers of D still carry the probes' short ones or none, which the
    rule allows; the builder writes the file headers (the announcement's PROPOSED sentence in
    `CommunityUnique.lean`'s header, marked proposed) and the reader round checks each docstring against
    rules 12 to 14. Not a decision, a work item.
11. **The Tier 9 headers' "sized candidate" sentences** (`CommunityData.lean` header, rung11 rule 9) become
    stale when W3c lands; by the house rule built files are not edited for prose; the W3c header records the
    supersession and the README rows say so. User's call: none.
12. **The critics' changes and their disposition (none silently dropped).** Statement critic: (A) register
    item (9) APPLIED (D16); (B) the two sibling docstrings APPLIED verbatim (D18); (C) the §1 bullet wording
    APPLIED BY EXTENSION, not in place (D17: the skeleton's §1 is carried verbatim by the orchestrator's
    instruction, so the words are added in the paragraph that follows the bullets; the critic itself left the
    form to this pass); (D) `hν'` dropped APPLIED (D14; the critic offered it as optional and the skeleton
    proposed it); (E) the explicit form APPLIED IN A STRONGER FORM (D15: frozen and registered rather than a
    shipped helper; the frozen `community_unique_pressure` keeps its own proof); MINOR 6 (the four verbatim
    rung11 lines will always hit the banned-words grep) RECORDED in §7 as the known exemption. Feasibility
    critic: required change 1 (the four slice-fact docstrings) APPLIED in the probe (D18); 2 (§1a
    "cannot be compiled outside the tree") APPLIED (§1a, the critic's wording); 3 (the CommunityUnique row
    note) APPLIED (§1a); 4 (traps T1, T2, T5) APPLIED (§7, T1 re-worded to avoid the script's own pattern,
    T6 and T7 added too); 5 (the three primed registered names) APPLIED (D8, §5). REJECTED: nothing. The two
    capstones of rung11 §4c were asked to change by no critic and are unchanged (`check_capstone.py`). The
    design's D6 (keep `hν'`) is overruled by D14 with the reason given there; every other design decision
    stands.
13. **The interface agreement of the recon** (I12, I13). DECIDED: the two statements freeze WITHOUT `hν'`
    (D14); the recon's cross-probe identity check (`VERIFIED.md`) remains true for the other fifteen interface
    names and is superseded for these two by `Tier9cFinal.lean`. User's call: restore the agreed text with
    `hν'` (the design's form is `DesignFinal.lean:1493` and `:1603`; the change back costs four call sites);
    not recommended (a weaker statement frozen for the life of the tree).
14. **The `git log` count.** The skeleton says 70 commits, `git log --oneline | wc -l` says 72 on this pass;
    nothing was committed by anyone in between as far as `git status` and the tag list show (30 tags, HEAD
    `dc3bd8f` unchanged). User's call: none; recorded so that the next status header counts one way and says
    which.
15. **Record of this pass's tool runs on the generated file** (written after generation; the numbers are
    those of the file as committed, this item sitting below every line it cites so that its insertion moved
    none of them). `tools/banned_words.sh` on this file: 4 hits, at lines 1248 (rule 1's em-dash), 1254
    (rule 2's em-dash), 1255 (rule 2's own negated priority phrase, the script's definite-article test) and
    1265 (rule 3's em-dash), every one inside the rung11 §7 text carried VERBATIM; Python counts U+2014 = 3
    (those three lines) and U+2013 = 1 (line 1273, rule 5, verbatim); `Tier9cFinal.lean`: CLEAN, 0 and 0.
    `tools/byte_identity.py` on this file against `design/final/Tier9cFinal.lean` with the bounds from
    `grep -n "^#### W"`: lines 519 to 598 (SliceExtract) 16/16; 599 to 644 (ConvectionCoeff) 6/6; 645 to 699
    (ClassParseval) 8/8; 702 to 864 (ClassFlowODE) 24/24; 867 to 994 (CommunityUnique) 15/15; the §6
    register, lines 1045 to 1214, 16/16; no context line inside any fence. `tools/check_capstone.py` on
    both capstones against the orchestrator's expected files: byte-identical, 5 lines each. The tree grep
    for the four new names (`preHistory`, `preHistory_in_class`, `velocity_not_unique_off_halfline`,
    `community_unique_pressure_explicit`) under `TheoremB/`: 0 hits. The zsh trap T3 (`set -- $r` does not
    word-split) bit this pass once when looping over the block bounds; the runs above use explicit
    arguments.

Smallest next move: W3a. One Workflow: the builder transcribes `design/final/Tier9cFinal.lean` section A
(lines 63 to 434) into `TheoremB/SliceExtract.lean` (imports `TheoremB.DatumBridge`, `TheoremB.Galilean`;
instances `se_*`), section B (436 to 692) into `TheoremB/ConvectionCoeff.lean` (imports
`TheoremB.DatumBridge`; instances `cc_*`) and section C (694 to 982) into `TheoremB/ClassParseval.lean`
(imports `TheoremB.SliceExtract`; instances `cp_*`), each with the preamble of §4, the probe's docstrings
kept on every frozen declaration, no file-level `maxHeartbeats`, statements byte-for-byte from §4a. The
builder adds the three import lines to `TheoremB.lean` and to `AxiomCheck.lean` with the 30 `#print axioms`
lines of §4a (the names as in `Tier9cFinal.lean`'s audit block A, B, C), runs `bash scripts/check_axioms.sh`
(expected: GATE: GREEN, 421 lines counted on the bracket pattern, every one on the standard triple), and
re-checks byte-identity of every W3a statement against §4a of this file with `tools/byte_identity.py`
(bounds by `grep -n "^#### W"`). The wave then goes to the two readers (statement shape and vacuity;
proof and pin with a double-import instance test and an independent gate run) before the commit; no tag.

BUILD LOG (the planning commit carries none).

13 Sep 2026, Tier 9c wave W3a BUILT: `TheoremB/SliceExtract.lean` (517 lines, instances `se_*`, imports
`TheoremB.DatumBridge` and `TheoremB.Galilean`), `TheoremB/ConvectionCoeff.lean` (382 lines, `cc_*`, imports
`TheoremB.DatumBridge`) and `TheoremB/ClassParseval.lean` (422 lines, `cp_*`, imports `TheoremB.SliceExtract`
only: ConvectionCoeff was not needed, the build confirmed it): the 30 frozen W3a declarations of §4a (16 + 6 + 8
theorems) byte-identical, checked by the builder, both readers and the orchestrator with
`tools/byte_identity.py` (16/16, 6/6, 8/8; bounds 519-598, 599-644, 645-701 at the planning commit, unchanged by
this entry, which sits below every block); every proof closed with the final probe's own proof
(`design/final/Tier9cFinal.lean` sections A, B, C, cut at the probe's own markers, lines 64-434, 437-692,
695-982); no sibling added, no spec drift, no earlier Lean file edited, no private lemma cloned, no file-level
`maxHeartbeats`; registered in `TheoremB.lean` and `AxiomCheck.lean` (3 import lines each after `import
TheoremB.CommunityData`; 30 ledger lines, the first 30 audit lines of the probe verbatim, so the SliceExtract
block's ledger order is the probe's audit order rather than the file's declaration order, same set). Gate GREEN
421/421 (builder, both readers independently, orchestrator twice: before and after the comment-only edits below;
counted on the bracket pattern after joining wrapped lines; the quote-delimited regex reads 415 because six
ledger names now end in a prime, the five older ones plus `contDiff_space_slice'`; every entry exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`). Two independent readers BEFORE the commit: reader A
(statement shape and vacuity) 0 blockers, 0 majors, 6 minors, with seventeen compiled probe theorems in
`build-w3a/reader-shape/ShapeW3a.lean` (exit 0, 0 sorry, all on the standard triple): the Laplacian coefficient
I7 computed on the shear datum by an independent route agrees with the frozen theorem at every mode (the value
`−(2π)² · ccVec ε` at the mode `ccpe1`, `0` at the mode `0`); the frozen budget shape (`∃ E Z` before
`∀ t ∈ Icc 0 T`) is the strong one, the pointwise shape being provable for every `v`; the periodicity
hypothesis of the time-derivative slice fact is load-bearing (the jointly smooth non-periodic field
`(x, t) ↦ t • x` has the non-periodic derivative slice `x ↦ x`); `en` and `ens` of the shear read `2ε²` through
the frozen Parseval equalities; the shear's convection coefficient VANISHES on both sides of I10 (recorded
honestly) while a two-mode field has a nonzero one, so I10 is not `0 = 0` in general; `C := 0` cannot discharge
the velocity bound on the shear member; `norm_rep_le`'s `2` is slack (`√3` sharp, statement-neutral). Reader B
(proof and pin) CLEAN with 3 minors, an independent gate run (421, both counts documented), the three
minimal-import probes (each module imports exactly what §1a says), the double-import test
(`build-w3a/reader-proof/DoubleImport.lean`: ClassParseval with ConvectionCoeff, CommunityData, ContinuousRep,
FourierDeriv, CoeffExtract and DatumBridge plus a downstream named instance triple and one elaborated torus
integral, exit 0; and `DoubleImportNoInst.lean`: the local instances do not leak into an importer), every
Mathlib and tree name of the read proofs found at the pin, I7 RE-PROVED by a second route
(`build-w3a/reader-proof/ReproveI7.lean`: `laplacian_eq_sum_second`, `fderiv_right` and `clm_apply`, the
first-order bridge applied twice per direction; standard three axioms), and both constant ledgers (I7:
`∑ i (2πi nᵢ)² = −(2π)²‖freq n‖²`; I10: the `−2π` against `convection_classical`'s `−(2π)` at
Nonlinearity.lean:296) re-derived by hand in its report. The minors (the headers' capstone pointer named neither
the same datum nor `0 < ν'`; a recon-era "modulo the P1 interface" on `classFlow_budget` and its section heading
although SliceExtract discharges the interface; "the torus L² norm" where the statements carry the integral of
the squared norm; two probe labels P3/P4 in docstrings) were fixed by the orchestrator with comment-only edits
before the commit (`build-w3a/orchestrator-final/`, the gate re-run after them: GREEN 421/421); the unused `hT`
binders of `classFlow_budget` and `summable_flow_clock` stay as D6 says (two linter warnings, the only ones of
the three modules). Recorded facts: (1) the three local measure instance triples are NAMED and sit inside
`noncomputable section`; the tree's global `AddCircle.measureSpace 1` answers `#synth` in an importer, so
nothing leaks; (2) the probe's `-- SECTION` markers are dropped and its `/-! # A. W3a : … (P1) -/` headings kept
(provenance); (3) several frozen statements stand on single lines longer than 100 characters because the recon
brief stated the interface on one line and the fences were extracted from the probe verbatim (frozen text, not
re-wrapped); (4) disk 5.6 GiB before and after. No tag (ladder §5). Workflow `wf_fba1e9f2-1e9`; records under
`audit-tier9c/build-w3a/`.
