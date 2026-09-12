# Rung 11 (Tier 9 blueprint): the community's statement shape over real-space data

Status: PLANNING (13 Sep 2026): **nothing built; gate untouched at HEAD
`03b1656`** (the leanchecker-replay commit, on top of the dossier Unit 7 commit
`5dfce7a` and the Tier 8b tag `t8b-community-green` = `d59ddcd`; 28 tags; 67
commits). The gate was RE-RUN by the orchestrator on 12/13 Sep 2026 at `5dfce7a`
(the Lean tree is identical at `03b1656`, a prose-and-script commit): `bash
scripts/check_axioms.sh` reported GATE: GREEN with 294 `depends on axioms`
entries, every one on exactly `[propext, Classical.choice, Quot.sound]` (counted
with wrapped lines joined; no `sorryAx`); the log is kept as
`audit-tier9/gate/baseline-gate.log` in the session directory. Working tree at
the start of the planning pass: `scripts/replay_leanchecker.sh` was untracked;
it was committed as `03b1656` by another session of the same author while the
reconnaissance ran (found by the design pass, re-verified by `git log` twice
since); the working tree is clean at the planning commit. No tracked Lean file
is touched by the planning pass; it writes only this file (in `context/`) and
its probes (in the session directory `audit-tier9/`).

Pin: Lean `4.31.0-rc2`, Mathlib `15a89b24`. Contract unchanged: kernel + gate
judge; statements freeze at declaration; independent adversarial reader
BEFORE any tag; every probe and every copy of a built file lives in the
session directory `audit-tier9/`, never in `/private/tmp` (wiped without
notice; the Tier 8 planning pass lost every probe that way).

Provenance: Tier 9 is the datum-side completion of Tier 8b (rung10 §1b, §2).
Tier 8b inhabits OUR COPY of the community class
`NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` for data of the form
`u₀ = u₀Real c₀` with `c₀` a coefficient field in the campaign's trap class.
Tier 9 quantifies over REAL-SPACE data `u₀ : ℝ³ → ℝ³` meeting the community's
own `InitialVelocityConditionPeriodic` and produces the same conclusion under a
smallness hypothesis on the mean-free part of the datum. Nothing here is new
mathematics: the Fourier inversion of a smooth periodic function and the
Galilean invariance of Navier-Stokes are textbook; the deliverable is
machine-checking, with the status of every constant stated per constant (§7).

**Extension of the status header (the blueprint pass, 13 Sep 2026).** The paragraphs above
are the orchestrator's skeleton, carried verbatim; what follows records the evidence state at
the time this file was written.

- HEAD re-read by this pass: `git rev-parse --short HEAD` = `03b1656` ("Kernel replay through
  the toolchain leanchecker: 60 of 60 imported modules exit 0", `scripts/replay_leanchecker.sh`),
  on top of the dossier commit `5dfce7a`; `git status --short` empty; 28 tags; the newest
  ladder tag is still `t8b-community-green` = `d59ddcd`. The skeleton's original sentence said
  the replay script was untracked and uncommitted; that was true when the skeleton was written
  (12 Sep, late) and false by the time of the design pass; the orchestrator corrected the status
  paragraph above before the planning commit (the design pass found the commit; this pass and
  the orchestrator re-verified it by `git log`). Nothing under the repository was touched by the design pass, by either critic, or by this
  pass: every one of them writes only under the session directory `audit-tier9/`. Disk: 7.2 GB
  free at the start of this pass.
- Evidence state, by whom and where (session directory `audit-tier9/`, absolute prefix
  `/Users/konstantinosa.tsantakos/.claude/projects/-Users-konstantinosa-tsantakos-Documents/f281f76f-53ac-48b2-9228-0cfa7b9859e9/audit-tier9/`):
  - RECONNAISSANCE (six agents, 12 and 13 Sep): `recon/R1/ReconR1.lean` (exit 0, 0 sorry),
    `recon/R2/ReconR2.lean` (exit 0, 0 sorry), `recon/R3/ReconR3.lean` (exit 0, 2 sorry = the
    two R2 bricks), `recon/R4/ReconR4.lean` (exit 0, 0 sorry), `recon/R5/ReconR5.lean` (exit 0,
    0 sorry), `recon/R6/ReconR6.lean` (exit 0, 9 sorry, all sizing statements); each with a
    `notes.md`; structured reports in `recon/recon-results.json`. Read by this pass, not
    recompiled.
  - DESIGN (the design pass, 13 Sep): `design/DesignFinal.lean` (1462 lines, sha256
    `af9b86c6…e10`, exit 0, 2 sorry decls = the W3 candidates, log `design/compile-final.log`)
    and `design/design.md`. Read by this pass.
  - STATEMENT-SHAPE CRITIC (13 Sep): `critique/shape/ShapeProbe.lean` (DesignFinal.lean lines
    1-1435 verbatim plus `namespace ShapeCritic`, 30 declarations; pass 2 `compile2.log` exit
    0; 0 sorry in the critic section), `critique/shape/report.md`: 0 BLOCKER, 0 MAJOR, 7
    MINOR, required changes RC1 to RC6. Read by this pass.
  - FEASIBILITY CRITIC (13 Sep): `critique/feasibility/DesignFinal_recompile.lean` (exit 0),
    `FeasTransfer.lean` (exit 0, 0 sorry: the three rep/descend spellings are one object),
    `FeasInversion.lean` (exit 0, 0 sorry: an independent route to the inversion),
    `FeasCompose.lean` (exit 0: the capstone from the sorry'd interface), `FeasGalilean.lean`
    (exit 0: section C stands alone), `DesignFinal_noHeartbeats.lean` and
    `DesignFinal_simpfix.lean` (exit 0), `critique/feasibility/report.md`: 0 BLOCKER, 0 MAJOR,
    7 MINOR, six required changes. Read by this pass.
  - THIS PASS (the blueprint author, 13 Sep): `design/final/Tier9Final.lean` (1657 lines,
    sha256 `9a52de83a5bb0b13a918c38e6f68889726c039cc8d3f163b23aeeef14324d739`), derived from
    `design/DesignFinal.lean` by `design/final/make_final.py` with the critics' required changes
    applied (RC1, RC2, RC3 in the feasibility critic's wording, RC5, RC6; feasibility items 2
    and 3), COMPILED BY THIS PASS with `lake env lean` at the pin: exit 0, 0 `: error`, exactly
    2 `declaration uses sorry` (lines 1610 and 1618, the two W3 candidates), 25 of the 26
    `#print axioms` lines on exactly `[propext, Classical.choice, Quot.sound]` and the 26th
    (`T9Candidate.community_unique_velocity`) on `sorryAx` as declared; the only warning is an
    unused binder name in the R4-verbatim helper `mapsTo_galCurve` (log
    `design/final/compile1.log`). The fenced blocks of §4 and §6 are extracted from that file by
    `design/final/gen_blueprint.py` through the orchestrator's own
    `tools/byte_identity.decls_in_file`, and `tools/byte_identity.py` was re-run by this pass on
    this file against `Tier9Final.lean` (the counts are in the §4 preamble).
- Every PROVED mark in §4 cites `design/final/Tier9Final.lean` (the probe that holds the proof
  in its final text) and, where the proof was copied, the recon probe of origin.
- Format note (feasibility critic, M6): the `#### W<n>` headers of §4 put a colon after
  `W<n>` where rung10 put an em-dash, because rule 8 of §7 forbids em-dashes in new prose; the
  `^#### W` prefix the orchestrator's tools grep for is unchanged. The em-dashes in this file are
  exactly those inside the rung10 §7 rules carried VERBATIM (rules 1, 2 and 3; rule 5 carries
  one en-dash); the orchestrator removed the two in its own skeleton prose (the title and the W2
  bullet of §1) before the planning commit; the count is recorded in §7 with the banned-words
  grep record.

## 1. Goals and non-goals

**Goal.** Turn `theorem_B_community_periodic` (Tier 8b, the community's
`∃ v p` shape over coefficient data `u₀Real c₀`) into the community's own
statement shape over real-space data:

- (W1, the datum bridge) for every `u₀ : ℝ³ → ℝ³` with
  `InitialVelocityConditionPeriodic u₀` (`ContDiff ℝ ∞`, one-periodic,
  divergence-free), a coefficient field `coeff u₀ : (Fin 3 → ℤ) → Vel` (the
  Fourier coefficients of the descent of each component to
  `UnitAddTorus (Fin 3)`), with `u₀ = u₀Real (coeff u₀)` (pointwise inversion),
  `RealField (coeff u₀)`, `DivFree (coeff u₀)`, and summability at EVERY
  Sobolev level (rapid decay through `mFourierCoeff_deriv` at every order).
- (W2, the mean) the community's condition does NOT include mean zero, while
  the campaign's trap class needs `c₀ 0 = 0`. The mean is removed by the
  Galilean change `v(x, τ) = m + w(x − τm, τ)`, `p(x, τ) = q(x − τm, τ)`,
  which preserves periodicity, divergence-freeness, joint smoothness on the
  closed slab and the equation (`∂_τ v + (v·∇)v = ∂_τ w + (w·∇)w` at the
  moved point). Capstone: for every `ν' > 0` and every `u₀` in
  `InitialVelocityConditionPeriodic` with
  `κ · en (meanFree (coeff u₀)) · ens (meanFree (coeff u₀)) < (2π ν')⁴`,
  `∃ v p, NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p`: the
  upstream positive statement's conclusion under a smallness hypothesis on
  the MEAN-FREE part of the datum, with `κ` of explicit form exported as a
  compiled existential.
- (W3, a candidate to SIZE, not to promise) uniqueness inside the community
  class in real-space vocabulary: two members of the class with the same
  datum agree; needs the bridge from a class member back to a coefficient
  flow in `theorem_B_unique`'s class.

**Non-goals.** The breakdown statement `navier_stokes_breakdown_periodic`
(nothing about it). Large data (the smallness hypothesis stays). Analyticity.
Forced data (`f ≠ 0`). Any numeric constant. Any priority claim (§7). Any
statement about the upstream positive statement for general data: the
capstone is that statement's conclusion under a smallness hypothesis on the
datum's mean-free part; both upstream `sorry`s are untouched.

**Doctrine (binding; it produced ten waves with zero blockers across Tiers
8a and 8b).** Per wave, one Workflow: one builder (statements byte-for-byte
from §4; only bodies change; if a frozen statement cannot be proved as
written, keep it, add a sibling, record spec drift; register every frozen
theorem in BOTH `TheoremB.lean` and `AxiomCheck.lean`; run the gate), then
two readers in parallel (statement-shape/vacuity with cheap-witness and
inhabitation probes; proof-and-pin with Mathlib-name probes and an
independent gate run), then a fix pass for blockers and majors. Then the
ORCHESTRATOR re-runs the gate, re-checks byte-identity of every frozen
statement against this file with its own script
(`audit-tier9/tools/byte_identity.py`, `check_capstone.py`; recompute block
line bounds with `grep -n "^#### W"` before every run), commits with the
harness trailer, and lays the ladder tag of §5. All Tier 1 to 8 files are
never edited; private lemmas are cloned, never un-privated; new files only,
plus the two registration files.

### 1a. File layout and import DAG (new files only; the design's layout, confirmed by both critics)

| File | Wave | Content (`Tier9Final.lean` section) | Imports |
|---|---|---|---|
| `TheoremB/Descent.lean` | W1 | A: `Community.IsOnePeriodic.add_freq` / `.fderiv_apply`, `rep1`/`rep`/`descend`, `descend_fiber`, `fiber_rep`, `isOpenQuotientMap_fiber`, `continuous_descend`, the fiber-slice brick `hasDerivAt_descend_insertNth`, the consumed R1 coefficient facts, `mFourierCoeff_descend_fderiv`, `dirDeriv`/`dirIter` and the iterated bridge `mFourierCoeff_descend_dirIter`, `descend_uLift_eq_uCont`, `mFourierCoeff_descend_uLift`; the three local measure instances copied verbatim from `FourierDeriv.lean:31-37` | `TheoremB.CommunityClass` |
| `TheoremB/DatumBridge.lean` | W1 | B: `coeff`, decay (`exists_bound_coeff_mul_norm_freq_pow`, `_vel_`), the ℓ¹ and Sobolev certificates at every order, `realField_coeff` (unconditional), `divFree_coeff`, the round trip `coeff_u₀Real`, `isOnePeriodic_u₀Real`, the INVERSION `u₀Real_coeff`, the W1 capstone `datum_bridge`; the three local instances | `TheoremB.Descent` |
| `TheoremB/Galilean.lean` | W2 | C: R4 verbatim (`galV`, `galP`, `slab`, `galΦ`, the translation lemmas, the joint within-derivative decomposition, `derivWithin_galV_time`, `convection_galV`, `laplacian_galV_space`, `gradient_galP_space`, periodicity/divergence transfer, `galilean_class`); Mathlib and the `Community` definitions ONLY; NO local measure instances (measured standalone: `critique/feasibility/FeasGalilean.lean`, exit 0) | `TheoremB.CommunityClass` |
| `TheoremB/CommunityData.lean` | W2 | D: `meanFree`, `meanVec`, their algebra (R5), `zeroMode`, `meanFree_of_mean_zero`, THE CAPSTONE, the witness-exposing sibling, the consistency corollary; E: the register `namespace T9Probe` (§6, sixteen registered probe theorems including the five of RC5); the three local instances | `TheoremB.DatumBridge`, `TheoremB.Galilean` |

DAG: `CommunityClass ← Descent ← DatumBridge ← CommunityData` and
`CommunityClass ← Galilean ← CommunityData`. `TheoremB.lean` gains 4 import lines;
`AxiomCheck.lean` gains 4 import lines and the `#print axioms` lines of §5. Name clashes: the
design's grep of the tree (quoted `--include='*.lean'`; the unquoted form silently reports 0
under zsh) found no declaration named `coeff`, `descend`, `rep`, `rep1`, `meanFree`, `meanVec`,
`galV`, `galP`, `zeroMode`, `dirDeriv`, `dirIter`, `datum_bridge`,
`theorem_B_community_periodic_data`, and no file named Descent/DatumBridge/Galilean/
CommunityData (the one `Descent` hit is a section comment, `PeriodicLift.lean:225`). The
tree's `freq_zero`, `conjVel_zero`, `dotR_zero_left` exist only as PRIVATE lemmas (ModesFlow,
RealityProp, NSFull); the public clones in CommunityData.lean do not clash (private names are
module-mangled) and compiled next to the imported tree in `Tier9Final.lean`.

### 1b. Decisions (D1 to D8 taken by the design and confirmed by both critics; D9 to D13 taken by this pass)

- **D1, ONE spelling of rep/descend: R2's wins.** `rep1 z := ((AddCircle.equivIco 1 0 z :
  Ico 0 (0+1)) : ℝ)`, `rep z := WithLp.toLp 2 fun i => rep1 (z i)`, `descend {α : Sort*}
  (f : ℝ³ → α) z := f (rep z)`. Reasons: (i) `descend` must be `Sort`-polymorphic (R3 and R6
  fixed `ℂ`): W1 descends the complexified components, `descend_fiber` is used at `α := ℂ` and
  at `fun x => fderiv ℝ f x v`, and W3 would descend `ℝ³`-valued and time-dependent fields;
  (ii) R2's bricks (`sliceLine`, `fiber_sliceLine`) use `rep1` as a named coordinate map;
  (iii) R3's and R6's `rep` are definitionally R2's with `rep1` inlined. MEASURED by the
  feasibility critic (`FeasTransfer.lean`, exit 0, 0 sorry): R3's and R6's `rep`/`descend`/
  `coeff` re-declared verbatim are `rfl`-equal to the design's at default transparency, while
  `with_reducible rfl` FAILS (the plain defs `rep1`, `coeffC` block reducible unfolding); R2's
  original texts compile UNCHANGED against the design's definitions; R3's `LatPeriodic` texts
  need only the two brick calls retargeted; R6's `coeff_u₀Real` needs one `show`. The three
  recon spellings are ONE object; any transfer between them goes through `rfl`/`coeff_apply`/
  `unfold`, never `with_reducible`/`simp` alone. R2's `local instance : Fact ((0:ℝ) < 1)` is
  NOT needed (`rep1_coe` compiled without it in the design and in every feasibility probe).
- **D2, ONE periodicity vocabulary: the class's `IsOnePeriodic`.** R3's `LatPeriodic` is
  dropped; R2's inline `∀ g x, f (x + freq g) = f x` becomes the lemma
  `Community.IsOnePeriodic.add_freq` (Sort-polymorphic, declared as `theorem
  Community.IsOnePeriodic.add_freq` inside `namespace TheoremB` so that dot-notation
  `hf.add_freq` works, R2's measured trap); R2's `fderiv_apply_add_freq` and R3's
  `dirDeriv_periodic` merge into `Community.IsOnePeriodic.fderiv_apply` (any normed codomain,
  no differentiability hypothesis). Every frozen statement about a real-space field takes
  `IsOnePeriodic` (and, where needed, `ContDiff ℝ ∞`), i.e. exactly the fields of
  `InitialVelocityConditionPeriodic`. CONFIRMED by the statement critic: `#check
  @TheoremB.descend_fiber` prints `TheoremB.Community.IsOnePeriodic f`, no auto-bound.
- **D3, the smallness is spelled on the MEAN-FREE part in BOTH factors:**
  `κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4`.
  Reasons: it is §1 and rule 7 of §7 verbatim; `en` genuinely differs (`en_meanFree`:
  `en (meanFree c) = en c - ‖c 0‖²`) while `ens` does not (`ens_meanFree`), and a mixed
  spelling invites the misreading that the mean enters the threshold; the `ens (coeff u₀)` form
  is one `rw [ens_meanFree]` away and is NOT frozen (user's call, §8 item 2). The statement
  critic confirmed D3 as the right freeze.
- **D4, the witness-exposing sibling IS frozen** (`theorem_B_community_periodic_data_flow`):
  the same hypotheses, and the conclusion exhibits the coefficient flow `c` at `ν := 2πν'` from
  the datum `meanFree (coeff u₀)` with clauses 1 to 7 of `theorem_B_community_periodic_flow`
  (they supply the hypothesis set of `theorem_B_unique`, FullUnique.lean:327, on every window
  `Icc 0 T`) and the class membership of the explicit pair
  `(galV (meanVec (coeff u₀)) (vReal c), galP (meanVec (coeff u₀)) (pReal c))`. Reasons: it is
  what lets `theorem_B_unique` be cited for the coefficient flow behind the witness (rules 5
  and 9), it is the input a W3 build would consume, and it is PROVED in `Tier9Final.lean` at
  the cost of one `obtain` with 22 components. Cost: one registered theorem.
- **D5, the consistency corollary IS frozen** (`theorem_B_community_periodic_of_data`, a
  MUST-HOLD of §6): the `∃ v p` of `theorem_B_community_periodic` re-derived from the new
  capstone at `u₀ := u₀Real c₀` through the round trip `coeff (u₀Real c₀) = c₀` and
  `meanFree_of_mean_zero`. PROVED.
- **D6, what is frozen vs shipped.** Frozen (fenced in §4, byte-identity enforced, one
  `#print axioms` line per frozen THEOREM; defs are frozen but carry no ledger line): the
  interface statements. Shipped helpers (`lemma`s in `Tier9Final.lean`, listed by name in the
  route notes): PROVED there, the builder copies them, not fenced, not registered. The probe
  section (§6) is registered as in Tier 8b ("non-frozen, registered"): its statements are
  fenced here for the reader and extracted from `Tier9Final.lean` like the frozen ones;
  byte-identity of probe statements is recommended, not required.
- **D7, `realField_coeff` is UNCONDITIONAL** (every `u : ℝ³ → ℝ³`, no smoothness, no
  periodicity): the complexified components are real-valued pointwise, and
  `mFourierCoeff_neg_of_real` needs only that; for a non-integrable descent `mFourierCoeff` is
  the junk `0` and `0 = conj 0`. Recorded so that no reader asks for the missing hypothesis;
  confirmed by both critics (the feasibility critic's `realField_coeff_alt` proves it a second
  way).
- **D8, W3 is DEFERRED** (recommendation, §5 and the appendix of `design/design.md`): not
  needed for the capstone; sized at about 1300 lines and 6 to 8 sessions (R6, both critics
  agree) against about 1800 to 1900 lines and 4 sessions for the whole of W1 + W2, whose
  content is already proved; the existence-only wording is already agreed (rules 5 and 9); the
  flow sibling already lets `theorem_B_unique` be cited. Its two statements are frozen as
  CANDIDATE only (§4c), never promised.
- **D9 (this pass), RC6 APPLIED: `hc2` dropped from the frozen `mFourierCoeff_descend_uLift`.**
  The ℓ² input of the tree's `mFourierCoeff_uCont` is derived inside by the frozen
  `summable_sq_of_summable_norm hc`; the statement is strictly stronger, its only consumer
  (`coeff_u₀Real`) loses one line; compiled in `Tier9Final.lean`. Reason: the statement critic
  offered it as optional; nothing is built yet, so a stronger frozen statement costs nothing
  now and a weaker one would be frozen for the life of the tree.
- **D10 (this pass), the two critics' wordings for the seven clauses: the feasibility critic's
  governs.** RC3's replacement docstring says "VERBATIM (... clause 7 re-wrapped)"; the
  feasibility critic asks that "byte-copied ... VERBATIM" be replaced by "clauses 1 to 6
  line-identical to CommunityClass.lean:1621-1629 under the substitution; clause 7 identical up
  to a line re-wrap (three lines here, two there)". The second is the more conservative reading
  (it says less and everything it says was measured), so it is used in BOTH the docstring
  (`Tier9Final.lean`) and the route note (§4b); the rest of RC3 (no uniqueness clause; the
  clauses SUPPLY `theorem_B_unique`'s hypotheses on every window; what is not consumed) is
  applied verbatim.
- **D11 (this pass), no file-level `maxHeartbeats`** (feasibility item 2): deleted from
  `Tier9Final.lean` (compiles without it, re-measured here) and forbidden in every built file;
  a declaration that ever needs more gets `set_option maxHeartbeats N in` on that declaration
  only, the tree's habit.
- **D12 (this pass), RC5 APPLIED: five register items added to `T9Probe`** (`shear_not_const`,
  `capstone_hyp_not_universal`, `ivc_const_add`, `capstone_hyp_shifted_iff`,
  `capstone_fires_on_shifted_shear`, with their helpers), statements and proofs from
  `critique/shape/ShapeCritic_section.lean`, re-compiled in `Tier9Final.lean`. They are what RC2's
  docstring sentence cites; the ledger of §5 counts them (+5). `ivc_const_add` closes the design's
  §8 item 6 and the feasibility critic's M7 in one lemma.
- **D13 (this pass), the orchestrator's tools are NOT edited by this pass** (feasibility item 4:
  the em-dash test of `tools/banned_words.sh` and the `abbrev` DECL regex of
  `tools/byte_identity.py`). Reason: those tools are the instrument this deliverable is measured
  with; changing them from inside the deliverable would let the author move the ruler. The fix
  is recorded as the orchestrator's action BEFORE the W1 gate (§8 item 8) with the exact
  replacement text, and this pass compensated on its side (a Python count of U+2014 and U+2013;
  `abbrev slab` in its own fenced block and checked by eye, §4b).

## 2. The external target

The community class is OUR COPY, `namespace TheoremB.Community` in
`TheoremB/CommunityClass.lean:153-198`: the six definitions (`divergence`, `IsOnePeriodic`,
`InitialVelocityCondition`, `InitialVelocityConditionPeriodic`, `ForceCondition`,
`ForceConditionPeriodic`, `NavierStokesExistenceAndSmoothness`,
`NavierStokesExistenceAndSmoothnessPeriodic`) are quoted verbatim in rung10 §2a together with
the diff record against the upstream file (IDENTICAL except two lines: the namespace and the
divergence notation; "only the namespace line differs" must not be written). Tier 9 adds
nothing to the class and re-copies nothing (the statement critic's byte-level check: no
`structure`, no `def divergence`, no `def IsOnePeriodic` in the design probe; one `import
TheoremB.CommunityClass`, one `open Community`, every use elaborating to `TheoremB.Community.*`).

Both upstream statements, named: (a) the positive statement
`navier_stokes_existence_and_smoothness_periodic (nu) (hnu : nu > 0) (u₀)
(hu₀ : InitialVelocityConditionPeriodic u₀) : ∃ v p,
NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (f := 0) v p` and (b) the breakdown statement
`navier_stokes_breakdown_periodic`. Both upstream `sorry`s are untouched. The upstream
docstrings use resolution-prize language; ours do not (§7).

The Tier 8b bare capstone, VERBATIM from `TheoremB/CommunityClass.lean:1801-1810`:

```
theorem theorem_B_community_periodic :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      κ * en c₀ * ens c₀ < (2 * Real.pi * ν') ^ 4 →
      InitialVelocityConditionPeriodic (n := 3) (u₀Real c₀) ∧
      ForceConditionPeriodic (n := 3) (f := 0) ∧
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real c₀)
          (f := 0) v p
```

**What changes in Tier 9: the datum, and nothing else.** The 8b capstone quantifies over a
COEFFICIENT field `c₀` (all Sobolev levels summable, mean zero, real, divergence-free, small)
and produces the class at the real datum `u₀Real c₀`. The Tier 9 capstone
(`theorem_B_community_periodic_data`, §4b) quantifies over a REAL-SPACE field `u₀ : ℝ³ → ℝ³`
under the community's own hypothesis `InitialVelocityConditionPeriodic (n := 3) u₀` (the very
hypothesis of the upstream positive statement) and the smallness hypothesis
`κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4` on the
MEAN-FREE part of its coefficient field; the conclusion is the 8b conclusion's third conjunct
with `u₀` in place of `u₀Real c₀`, i.e. exactly the upstream positive statement's conclusion,
`∃ v p, NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p`. The 8b
conclusion's first conjunct has become the hypothesis; its second conjunct
(`forceConditionPeriodic_zero`, CommunityClass.lean:213) is unchanged in the tree and not
restated. The 8b mean-zero hypothesis `c₀ 0 = 0` is gone: the mean is removed by the Galilean
change, not excluded. `ν'`, `(f := 0)` and the `2π` clock change of `vReal`/`pReal` (rung10 §2b)
are as in 8b: the coefficient flow runs at `ν := 2πν'`.

The datum vocabulary is new to the tree (W1): `coeff u n := WithLp.toLp 2 fun j =>
mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n`, the Fourier coefficients of the descent
of each complexified component to `UnitAddTorus (Fin 3)`; `meanFree c k := if k = 0 then 0 else
c k`; `meanVec c := WithLp.toLp 2 fun j => (c 0 j).re`. The mean split `u₀Real c = fun x =>
meanVec c + u₀Real (meanFree c) x` (R5) and the inversion `u₀Real (coeff u₀) = u₀` (W1)
identify a datum in the class with `m + u₀Real d` for `m := meanVec (coeff u₀)`,
`d := meanFree (coeff u₀)`, and `d` is in the trap class of `theorem_B_community_periodic`.
The inversion is textbook (Mathlib supplies the pointwise inversion for continuous torus
functions with summable coefficients at the pin,
`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`); the Galilean invariance is textbook.
Nothing here is new mathematics; the deliverable is the machine-checking.

## 3. Gap table (every gap between the tree at HEAD and the capstone)

| # | Gap | Where it bites | Closed by (wave, declaration) | Status |
|---|---|---|---|---|
| G1 | No descent `ℝ³ → UnitAddTorus (Fin 3)` of a one-periodic function in the tree (only the section direction `fiber` (CommunityClass.lean:1285), `uLift_eq_charSum_fiber`) | every coefficient of a real datum | W1 `rep1`/`rep`/`descend`, `descend_fiber`, `fiber_rep` | PROVED (`Tier9Final.lean` A2; ReconR2.lean sections 2, 7) |
| G2 | ℤ³-invariance from the class's one-step `IsOnePeriodic` | `descend_fiber` | W1 `Community.IsOnePeriodic.add_freq` | PROVED (`Tier9Final.lean` A1; ReconR2.lean section 1) |
| G3 | Continuity of the descent (the torus is not a normed space; only `Continuous` transfers) | bundling into `C(T³, ℂ)` for the sup bound and the inversion | W1 `isOpenQuotientMap_fiber`, `continuous_descend` | PROVED (`Tier9Final.lean` A3; ReconR2.lean sections 3, 4; re-proved independently in ReconR6.lean) |
| G4 | `mFourierCoeff_deriv` (FourierDeriv.lean:129) needs `HasDerivAt` along `insertNth` fibers; no bridge from `fderiv` on `ℝ³` | the derivative-to-frequency identity for descended fields | W1 `sliceLine`, `hasDerivAt_sliceLine`, `hasDerivAt_descend_insertNth` (consumed by `exact`), `hasDerivAt_descend_dirDeriv` | PROVED (`Tier9Final.lean` A4, A6; ReconR2.lean section 5) |
| G5 | Rapid decay of the coefficients of a smooth periodic function at EVERY order; summability of every polynomial weight | the Sobolev hypothesis `∀ m` and the ℓ¹ hypotheses of the tree lemmas | W1 `dirIter`, `mFourierCoeff_descend_dirIter`, `exists_bound_coeff_mul_norm_freq_pow`, `summable_norm_freq_pow_mul_coeff(_sq)` | PROVED (`Tier9Final.lean` A6, B1; ReconR3.lean sections 2 to 5, now brick-free) |
| G6 | `Vel`-packing of the ℓ¹ certificates (R3 packed only the squared form) | `Summable ‖coeff u k‖` for the mean split; `datum_bridge` | W1 `norm_toLp_le_sqrt3_mul` (helper), `exists_bound_coeff_vel_mul_norm_freq_pow`, `summable_weight_coeff` | PROVED (`Tier9Final.lean` B2, glue) |
| G7 | `RealField (coeff u)` for real `u` (R3 unresolved) | trap-class membership of `meanFree (coeff u₀)` | W1 `realField_coeff` (unconditional; R1's `mFourierCoeff_neg_of_real`) | PROVED (`Tier9Final.lean` B3; independently `FeasInversion.lean` `realField_coeff_alt`) |
| G8 | `DivFree (coeff u)` from `∀ x, divergence u x = 0` | trap-class membership | W1 `divFree_coeff` (bridge at `q = 1`, `divergence_eq_sum` (CommunityClass.lean:783), `mFourierCoeff_finset_sum`) | PROVED (`Tier9Final.lean` B3; ReconR3.lean section 8) |
| G9 | Round trip `coeff (u₀Real c) = c` | consistency corollary; the shear-datum and constant-datum register items | W1 `coeff_u₀Real` (hypotheses `RealField c`, `Summable ‖c k‖`) | PROVED (`Tier9Final.lean` B4; ReconR3.lean section 7, ReconR6.lean section 1) |
| G10 | THE INVERSION `u₀Real (coeff u) = u` (R3 and R6 unresolved) | identifying the datum with the boosted witness's datum | W1 `u₀Real_coeff` (`hasSum_mFourier_series_apply_of_summable` + decay at `p = 0` + `descend_fiber` + `u₀Real_eq_of_lift`) | PROVED TWICE (`Tier9Final.lean` B4, the design's pointwise route; `FeasInversion.lean` `u₀Real_coeff_alt`, L² injectivity through R6's `eq_of_mFourierCoeff_eq`), both on the standard three axioms |
| G11 | The 8b capstone needs `c₀ 0 = 0`; the class does not impose a mean (R5: the mean-zero hypothesis is the ONLY obstruction, `zeroMode_meets_all_but_mean_zero`) | every datum with nonzero mean | W2 `meanFree` + algebra, `u₀Real_eq_meanVec_add'`, `galilean_class` | PROVED (`Tier9Final.lean` C, D1, D2; ReconR5.lean section 4, ReconR4.lean section 7) |
| G12 | No translation lemmas for `Δ`, `gradient`, divergence, `derivWithin` in the class vocabulary | `galilean_class` | W2 `laplacian_translate` (`iteratedFDeriv_comp_sub`, unconditional), `gradient_translate`, `divergence_translate`, `derivWithin_galV_time` | PROVED (`Tier9Final.lean` C; ReconR4.lean sections 2, 3; `FeasGalilean.lean` standalone) |
| G13 | Composition: datum bridge + mean split + boost + 8b capstone | THE CAPSTONE and its flow sibling | W2 `theorem_B_community_periodic_data`, `_data_flow` | PROVED (`Tier9Final.lean` D3, interface proved) AND PROVED from the sorry'd interface alone (`FeasCompose.lean`, the house pattern) |
| G14 | MUST-HOLD: the new capstone specialises to the old | consistency | W2 `theorem_B_community_periodic_of_data` | PROVED (`Tier9Final.lean` D3) |
| G15 | The register lacked non-constancy, restrictiveness of the hypothesis, and the compiled mean-invariance (statement critic M6) | vacuity audit | W2 `T9Probe.shear_not_const`, `capstone_hyp_not_universal`, `capstone_hyp_shifted_iff`, `capstone_fires_on_shifted_shear`, `ivc_const_add` (RC5) | PROVED (`Tier9Final.lean` E; `ShapeProbe.lean` section G) |
| G16 | Uniqueness inside the community class in real-space vocabulary | W3 candidate only | `T9Candidate.community_unique_velocity`, `_pressure` (R6 (2a), (2b)) | COMPILED (sorry), SIZED (design appendix), DEFERRED |
| G17 | Tooling: `byte_identity.py`'s DECL regex lacks `abbrev`; `banned_words.sh`'s em-dash test uses `grep -P` (a no-op on macOS) | the orchestrator's gate of every wave | §8 item 8 (orchestrator, before the W1 gate); this file puts `abbrev slab` in its own fenced block and `@[simp]` on its own line | DONE by the orchestrator, 13 Sep (§8 item 8) |

## 4. Frozen interfaces (statements freeze here)

Conventions. PROVED = full proof in `design/final/Tier9Final.lean` (compiled by this pass, exit
0 at the pin), copied from the cited recon probe where the statement is unchanged, or glue
written by the design pass; COMPILED = the statement elaborates there with a `sorry` body (only
§4c). Every fenced statement below is extracted VERBATIM from `Tier9Final.lean` by
`design/final/gen_blueprint.py` through the orchestrator's own `tools/byte_identity.decls_in_file`
(statement = from the declaration keyword to the ` :=` that starts the body, trailing whitespace
stripped; comment lines inside statements count; named arguments `(n := 3)`, `(f := 0)` are not
body separators), so `tools/byte_identity.py <this file> <lo> <hi> design/final/Tier9Final.lean`
reports byte-identical by construction; recompute the block bounds with `grep -n "^#### W"`
before every run. Re-run by this pass on this file: W1 Descent block 35/35, W1 DatumBridge 17/17,
W2 Galilean 20/20 (`abbrev slab`, invisible to the tool's DECL regex at that time, is in its own
fenced block and was checked by eye: identical; with the orchestrator's fixed tool, §8 item 8, the
block reads 21/21), W2 CommunityData 22/22, W3 candidate 2/2, the §6 register
16/16. The wave headers put a colon after `W<n>` (status header, format note). The tree
copies keep the file-level preamble of `Tier9Final.lean`: `open Set Filter Topology MeasureTheory
InnerProductSpace UnitAddTorus`, `open scoped ContDiff Laplacian ComplexConjugate`, `local
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)`, `namespace TheoremB`, `open Community` (NOT
exported by CommunityClass; R3's trap: an unopened `IsOnePeriodic` silently auto-binds),
`noncomputable section`, and the three local measure instances (FourierDeriv.lean:31-37,
verbatim) INSIDE the section (R6's trap) in `Descent.lean`, `DatumBridge.lean` and
`CommunityData.lean`, i.e. in every file that elaborates `mFourierCoeff` or unfolds `coeff`;
`Galilean.lean` needs none (feasibility item 6, measured standalone). NO file-level
`set_option maxHeartbeats` in any built file (D11). `@[simp]` sits on its own line above a frozen
declaration (`meanFree_zero`). Every frozen declaration carries a docstring under the
claim-wording rules of §7 (69 of the design's 135 declarations had none; the wave estimates of §5
include that work).

### 4a. Tier 9, W1

#### W1: `TheoremB/Descent.lean` (probe `design/final/Tier9Final.lean` section A, exit 0, 0 sorry decls)

Periodicity (R2 section 1; helpers `Community.IsOnePeriodic.sub_single`,
`Community.IsOnePeriodic.add_zsmul_single`, `freq_eq_three` shipped, not frozen):

```
theorem Community.IsOnePeriodic.add_freq {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f)
    (g : Fin 3 → ℤ) (x : ℝ³) : f (x + freq g) = f x

theorem Community.IsOnePeriodic.fderiv_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ³ → F} (hf : IsOnePeriodic f) (v : ℝ³) :
    IsOnePeriodic (fun x => fderiv ℝ f x v)
```
PROVED (`Tier9Final.lean` A1, copied from ReconR2.lean:52 `Community.IsOnePeriodic.add_freq`:
`Int.induction_on` with `sub_zsmul` + `sub_eq_add_neg`; `fderiv_apply` merges R2's
`fderiv_apply_add_freq` :162 and R3's `dirDeriv_periodic` :65 through `fderiv_comp_add_right`,
no differentiability).

The representative and the descent (R2 section 2, R3/R6 round trips):

```
def rep1 (z : UnitAddCircle) : ℝ

def rep (z : UnitAddTorus (Fin 3)) : ℝ³

def descend {α : Sort*} (f : ℝ³ → α) (z : UnitAddTorus (Fin 3)) : α

theorem rep1_coe (s : ℝ) : rep1 ((s : ℝ) : AddCircle (1 : ℝ)) = s - ⌊s⌋

theorem coe_rep1 (z : UnitAddCircle) : ((rep1 z : ℝ) : AddCircle (1 : ℝ)) = z

theorem rep_fiber (x : ℝ³) : rep (fiber x) = x - freq (fun i => ⌊x i⌋)

theorem fiber_rep (z : UnitAddTorus (Fin 3)) : fiber (rep z) = z

theorem descend_fiber {α : Sort*} {f : ℝ³ → α} (hf : IsOnePeriodic f) (x : ℝ³) :
    descend f (fiber x) = f x
```
PROVED (`Tier9Final.lean` A2, copied from ReconR2.lean:62-94: `AddCircle.coe_equivIco_mk_apply`
+ `Int.self_sub_floor` for `rep1_coe`, `AddCircle.coe_equivIco` for `coe_rep1`; `descend_fiber`
is R2 :84 with the hypothesis taken from `IsOnePeriodic` through `add_freq`; helper
`descend_comp_fiber`). `descend` is total and choice-free: for a non-periodic `f` it is a
well-typed junk object (§6, rule 10 of §7).

The open quotient map and continuity (R2 sections 3, 4; helpers `fiber_eq_piMap` (`rfl`),
`continuous_iff_continuous_comp_fiber`):

```
theorem isOpenQuotientMap_fiber : IsOpenQuotientMap (fiber : ℝ³ → UnitAddTorus (Fin 3))

theorem continuous_descend {E : Type*} [TopologicalSpace E] {f : ℝ³ → E}
    (hf : Continuous f) (hper : IsOnePeriodic f) : Continuous (descend f)
```
PROVED (`Tier9Final.lean` A3, copied from ReconR2.lean:104, :127: `IsOpenQuotientMap.piMap` of
`QuotientAddGroup.isOpenQuotientMap_mk` composed with `(PiLp.homeomorph 2 _).isOpenQuotientMap`;
`IsOpenQuotientMap.continuous_comp_iff` is stated composition-on-the-left, take `.symm`).

The fiber-slice brick (R2 section 5; helper `sliceLine_eq`):

```
def sliceLine (i : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ) : ℝ³

theorem fiber_sliceLine (i : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ) :
    fiber (sliceLine i y s) = i.insertNth (↑s : UnitAddCircle) y

theorem hasDerivAt_sliceLine (i : Fin 3) (y : UnitAddTorus (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sliceLine i y s) (EuclideanSpace.single i 1) t

theorem hasDerivAt_descend_insertNth {f : ℝ³ → ℂ} (hf : Differentiable ℝ f)
    (hper : IsOnePeriodic f) (i : Fin 3) (y : UnitAddTorus (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => descend f (i.insertNth (↑s : UnitAddCircle) y))
      (descend (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
        (i.insertNth (↑t : UnitAddCircle) y)) t
```
PROVED (`Tier9Final.lean` A4, copied from ReconR2.lean:135-186; `Fin.eq_self_or_eq_succAbove`
case split, `HasFDerivAt.comp_hasDerivAt` with the point explicit; the statement was consumed
by `exact` in `mFourierCoeff_deriv`, so the `(↑s : UnitAddCircle)` spelling is the tree's: R2
measured the three coercion spellings to be the same `Expr`).

Coefficient facts on the torus (R1, the consumed subset; the rest of R1 (`mFourierCoeff_add`,
`_const_smul`, `_neg'`, `_sub`, `_mFourier`, `_const`, `charSum_mean_split`,
`uLift_mean_split`, `coeffVel`, `norm_coeffVel_le`, `summable_of_decay` and siblings) is
available in ReconR1.lean and NOT frozen: no consumer in W1/W2):

```
theorem integrable_of_continuous {f : UnitAddTorus (Fin 3) → ℂ} (hf : Continuous f) :
    Integrable f (volume : Measure (UnitAddTorus (Fin 3)))

theorem norm_mFourierCoeff_le (g : C(UnitAddTorus (Fin 3), ℂ)) (n : Fin 3 → ℤ) :
    ‖mFourierCoeff g n‖ ≤ ‖g‖

theorem mFourierCoeff_neg_of_real {g : UnitAddTorus (Fin 3) → ℂ}
    (hg : ∀ z, conj (g z) = g z) (n : Fin 3 → ℤ) :
    mFourierCoeff g (-n) = conj (mFourierCoeff g n)

theorem mFourierCoeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → UnitAddTorus (Fin 3) → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (n : Fin 3 → ℤ) :
    mFourierCoeff (fun z => ∑ i ∈ s, f i z) n = ∑ i ∈ s, mFourierCoeff (f i) n

theorem summable_sq_of_summable_norm {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖) : Summable fun k => ‖c k‖ ^ 2

theorem u₀Real_eq_of_lift (c : (Fin 3 → ℤ) → Vel) (u : ℝ³ → ℝ³)
    (hu : ∀ x j, ((u x j : ℝ) : ℂ) = uLift j c x) :
    u₀Real c = u
```
PROVED (`Tier9Final.lean` A5, copied from ReconR1.lean:36, :62, :74, :162, :142 and
ReconR3.lean:430 for the general-`Finset` sum: `Continuous.integrable_of_hasCompactSupport` +
`(isClosed_tsupport _).isCompact`, `norm_integral_le_of_norm_le_const` + `probReal_univ`,
`integral_conj` + `mFourier_neg` + `starRingEnd_self_apply`, `integral_finsetSum` (the pinned
name; `integral_finset_sum` is deprecated), `Summable.le_tsum`, `PiLp.ext` +
`Complex.ofReal_re`).

The derivative bridge and its iteration (R2 section 6, R3 sections 1, 2; helpers
`continuous_fderiv_apply_single`, `continuous_dirDeriv`, `dirIter_zero`):

```
theorem mFourierCoeff_descend_fderiv {f : ℝ³ → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsOnePeriodic f) (i : Fin 3) (n : Fin 3 → ℤ) :
    mFourierCoeff (descend fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) n
      = (2 * Real.pi * Complex.I * (n i)) * mFourierCoeff (descend f) n

def dirDeriv (i : Fin 3) (f : ℝ³ → ℂ) : ℝ³ → ℂ

theorem contDiff_dirDeriv (i : Fin 3) {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirDeriv i f)

theorem dirDeriv_isOnePeriodic (i : Fin 3) {f : ℝ³ → ℂ} (hp : IsOnePeriodic f) :
    IsOnePeriodic (dirDeriv i f)

theorem hasDerivAt_descend_dirDeriv (i : Fin 3) {f : ℝ³ → ℂ} (hf : Differentiable ℝ f)
    (hp : IsOnePeriodic f) (y : UnitAddTorus (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => descend f (i.insertNth (↑s : UnitAddCircle) y))
      (descend (dirDeriv i f) (i.insertNth (↑t : UnitAddCircle) y)) t

def dirIter (i : Fin 3) (q : ℕ) (f : ℝ³ → ℂ) : ℝ³ → ℂ

theorem dirIter_succ (i : Fin 3) (q : ℕ) (f : ℝ³ → ℂ) :
    dirIter i (q + 1) f = dirDeriv i (dirIter i q f)

theorem contDiff_dirIter (i : Fin 3) {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f) (q : ℕ) :
    ContDiff ℝ ∞ (dirIter i q f)

theorem dirIter_isOnePeriodic (i : Fin 3) {f : ℝ³ → ℂ} (hp : IsOnePeriodic f) (q : ℕ) :
    IsOnePeriodic (dirIter i q f)

theorem mFourierCoeff_descend_dirIter (i : Fin 3) {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (q : ℕ) (n : Fin 3 → ℤ) :
    mFourierCoeff (descend (dirIter i q f)) n =
      (2 * Real.pi * Complex.I * (n i)) ^ q * mFourierCoeff (descend f) n
```
PROVED (`Tier9Final.lean` A6: ReconR2.lean:205 by `exact mFourierCoeff_deriv i …`;
ReconR3.lean:47-123: `contDiff_infty_iff_fderiv` + `contDiff_clm_apply_iff` for
`contDiff_dirDeriv`, `Function.iterate_succ_apply'` for `dirIter_succ`, induction on `q`
consuming the two bricks for the iterated bridge; the feasibility critic re-compiled R3's
original `LatPeriodic` texts against these definitions with only the two brick calls retargeted
(`FeasTransfer.lean`). The two induction lemmas are written `:= by induction q`, not with
equation-compiler alternatives, so the byte-identity tool cuts their statements at the body
separator).

The descent of a lift (R2 section 8, R3 section 7):

```
theorem descend_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (z : UnitAddTorus (Fin 3)) :
    descend (uLift j c) z = ∑' k, c k j * mFourier k z

theorem descend_uLift_eq_uCont (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) : descend (uLift j c) = ⇑(uCont j c hc)

theorem mFourierCoeff_descend_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc : Summable fun k => ‖c k‖) (n : Fin 3 → ℤ) :
    mFourierCoeff (descend (uLift j c)) n = c n j
```
PROVED (`Tier9Final.lean` A7, copied from ReconR2.lean:236, :241; ReconR3.lean:395 with `hc2`
DROPPED (D9, RC6): `uLift_eq_charSum_fiber` + `fiber_rep`, `(uCont_apply j c hc z).tsum_eq`
then `rfl` for `smul = mul`, `mFourierCoeff_uCont j c hc (summable_sq_of_summable_norm hc)`).

#### W1: `TheoremB/DatumBridge.lean` (probe `design/final/Tier9Final.lean` section B, exit 0, 0 sorry decls)

The coefficient field and the components:

```
def coeff (u : ℝ³ → ℝ³) (n : Fin 3 → ℤ) : Vel

theorem coeff_apply (u : ℝ³ → ℝ³) (n : Fin 3 → ℤ) (j : Fin 3) :
    coeff u n j = mFourierCoeff (descend fun x => ((u x j : ℝ) : ℂ)) n

theorem contDiff_ofReal_component {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => ((u x j : ℝ) : ℂ))

theorem isOnePeriodic_ofReal_component {u : ℝ³ → ℝ³} (hp : IsOnePeriodic u) (j : Fin 3) :
    IsOnePeriodic (fun x => ((u x j : ℝ) : ℂ))
```
PROVED (`Tier9Final.lean` B, ReconR3.lean:348 `coeffOf` renamed (R6's `coeff`); :327, :331:
`Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hu)`;
`coeff_apply` is `rfl`).

The sup bound and the decay (R3 sections 3, 4, 5; helpers `norm_twoPiI_mul`,
`exists_coord_norm_freq_le` (tree `norm_freq_le_sqrt3_mul_natMax`),
`exists_bound_coeff_mul_absCoord_pow`, `norm_freq_zero_rpow_neg_four`):

```
theorem exists_bound_mFourierCoeff_descend {g : ℝ³ → ℂ} (hg : Continuous g)
    (hp : IsOnePeriodic g) :
    ∃ M : ℝ, ∀ n : Fin 3 → ℤ, ‖mFourierCoeff (descend g) n‖ ≤ M

theorem exists_bound_coeff_mul_norm_freq_pow {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ, ‖mFourierCoeff (descend f) n‖ * ‖freq n‖ ^ q ≤ C

theorem summable_norm_freq_pow_mul_coeff {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (p : ℕ) :
    Summable fun n : Fin 3 → ℤ => ‖freq n‖ ^ p * ‖mFourierCoeff (descend f) n‖

theorem summable_norm_freq_pow_mul_coeff_sq {f : ℝ³ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : IsOnePeriodic f) (m : ℕ) :
    Summable fun n : Fin 3 → ℤ => ‖freq n‖ ^ (2 * m) * ‖mFourierCoeff (descend f) n‖ ^ 2
```
PROVED (`Tier9Final.lean` B1, copied from ReconR3.lean:129, :193, :245, :268: the bound is
`‖⟨descend g, continuous_descend⟩‖` through `norm_mFourierCoeff_le`; the decay is the iterated
bridge at order `q` plus `exists_coord_norm_freq_le`; summability is
`Summable.of_norm_bounded_eventually` against `C * ‖freq n‖ ^ (-4 : ℝ)` with `q := p + 4` and
the exception set `⊆ {0}` (the zero term of `summable_norm_freq_rpow`'s weight IS `0`,
`Real.zero_rpow`)). The decay constants `C_q` and the sup bounds `M` are UNTRACKED
existentials produced by `choose`; the `√3` and `(√3/2π)^q` factors are literal expressions
(rule 1 of §7).

The `Vel`-packed certificates (glue; helpers `norm_toLp_le_sqrt3_mul`,
`summable_vel_of_components`):

```
theorem exists_bound_coeff_vel_mul_norm_freq_pow {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u)
    (hp : IsOnePeriodic u) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ, ‖coeff u n‖ * ‖freq n‖ ^ q ≤ C

theorem summable_weight_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (p : ℕ) : Summable fun l => ‖freq l‖ ^ p * ‖coeff u l‖

theorem summable_sob_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (m : ℕ) : Summable fun l => ‖freq l‖ ^ (2 * m) * ‖coeff u l‖ ^ 2
```
PROVED (`Tier9Final.lean` B2: per-component decay chosen with `choose`, packed through
`‖(‖freq n‖ ^ q) • coeff u n‖` and `norm_toLp_le_sqrt3_mul` (R1's `norm_coeffVel_le` pattern,
`EuclideanSpace.norm_eq`), then the R3 cofinite argument verbatim; the packing `simp only` is
`[coeff, PiLp.smul_apply, Complex.real_smul]` (feasibility item 3: `PiLp.toLp_apply` was the
flagged unused argument and is gone); `summable_sob_coeff` is ReconR3.lean:353
`summable_weight_coeffOf` renamed).

Reality and divergence (R1 pattern; R3 section 8; helpers `dirDeriv_ofReal_component`,
`sum_dirDeriv_component_eq_divergence`):

```
theorem realField_coeff (u : ℝ³ → ℝ³) : RealField (coeff u)

theorem divFree_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u)
    (hdiv : ∀ x, Community.divergence u x = 0) : DivFree (coeff u)
```
PROVED (`realField_coeff`: `Tier9Final.lean` B3, `PiLp.ext`, `c3_conjVel_apply`,
`mFourierCoeff_neg_of_real` with `Complex.conj_ofReal`, NO hypothesis on `u` (D7);
`divFree_coeff`: ReconR3.lean:447 with the bricks discharged, `beta_reduce at hlin` after
`mFourierCoeff_finset_sum`).

The round trip, periodicity of the real datum, THE INVERSION, and the W1 capstone:

```
theorem coeff_u₀Real {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (hc : Summable fun k => ‖c k‖) : coeff (u₀Real c) = c

theorem isOnePeriodic_u₀Real (c : (Fin 3 → ℤ) → Vel) : IsOnePeriodic (u₀Real c)

theorem u₀Real_coeff {u : ℝ³ → ℝ³} (hu : ContDiff ℝ ∞ u) (hp : IsOnePeriodic u) :
    u₀Real (coeff u) = u

theorem datum_bridge {u : ℝ³ → ℝ³} (hu : InitialVelocityConditionPeriodic (n := 3) u) :
    (∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖coeff u l‖) ∧
    (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖coeff u l‖ ^ 2) ∧
    RealField (coeff u) ∧ DivFree (coeff u) ∧ u₀Real (coeff u) = u
```
PROVED (`coeff_u₀Real`: `Tier9Final.lean` B4, ReconR3.lean:402 `coeffOf_u₀Real` with the ℓ²
input no longer needed (D9); R6 :86 proves the same with a stronger hypothesis;
`isOnePeriodic_u₀Real`: the inline argument of `initialVelocityConditionPeriodic_u₀Real`
(CommunityClass.lean:876) made public; `u₀Real_coeff`: `u₀Real_eq_of_lift`, then per component
the bundled `g := ⟨descend f, continuous_descend⟩`, `Summable (mFourierCoeff g)` from
`summable_norm_freq_pow_mul_coeff` at `p = 0` (a `let`-bound `g` needs the summability stated
on `descend f` first and `Summable.of_norm` applied by term; `simpa` does not see through the
`let`), `hasSum_mFourier_series_apply_of_summable` (R1 `inversion`), `descend_fiber`,
`uLift_eq_charSum_fiber`, `tsum_congr` + `smul_eq_mul`; the feasibility critic proved the same
statement a second way, `FeasInversion.lean` `u₀Real_coeff_alt`, by L² injectivity
(`eq_of_mFourierCoeff_eq` from ReconR6.lean:365 + `mFourierCoeff_uCont` + `descend_fiber` +
`descend_uLift_eq_uCont`), standard three axioms; `datum_bridge`: the five conjuncts from the
five lemmas with `hu.smooth`, `hu.isOnePeriodic`, `hu.div_free`). The inversion and every
lemma consuming `coeff u` for a general `u` carry `ContDiff ℝ ∞ u ∧ IsOnePeriodic u` (or the
class); the statement critic confirmed (`#check @TheoremB.u₀Real_coeff`) and proved
`inversion_not_unconditional` (§6).

### 4b. Tier 9, W2

#### W2: `TheoremB/Galilean.lean` (probe `design/final/Tier9Final.lean` section C = ReconR4.lean verbatim, exit 0, 0 sorry decls)

Definitions (`slab` is an `abbrev` so it unifies with the class's literal `Set.univ ×ˢ Set.Ici
0`; the byte-identity tool's DECL regex does not parse `abbrev`, verify this one line by eye,
§8 item 8):

```
def galV (m : ℝ³) (w : ℝ³ → ℝ → ℝ³) : ℝ³ → ℝ → ℝ³

def galP (m : ℝ³) (q : ℝ³ → ℝ → ℝ) : ℝ³ → ℝ → ℝ
```

```
abbrev slab : Set (ℝ³ × ℝ)
```

```
def galΦ (m : ℝ³) : ℝ³ × ℝ → ℝ³ × ℝ
```
PROVED (definitions; `Tier9Final.lean` C, ReconR4.lean:21-30).

Smoothness transfer and the translation identities (helpers `contDiff_galΦ`, `mapsTo_galΦ`,
`uncurry_galV_eq`, `uncurry_galP_eq` (both `rfl`), `fderiv_translate`):

```
theorem contDiffOn_galV {m : ℝ³} {w : ℝ³ → ℝ → ℝ³}
    (hw : ContDiffOn ℝ ∞ (↿w) slab) : ContDiffOn ℝ ∞ (↿(galV m w)) slab

theorem contDiffOn_galP {m : ℝ³} {q : ℝ³ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ (↿q) slab) : ContDiffOn ℝ ∞ (↿(galP m q)) slab

theorem contDiff_space_slice {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : ContDiff ℝ ∞ (w · τ)

theorem laplacian_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : ℝ³ → F) (a x : ℝ³) :
    Δ (fun y => V (y - a)) x = Δ V (x - a)

theorem gradient_translate (p : ℝ³ → ℝ) (a x : ℝ³) :
    gradient (fun y => p (y - a)) x = gradient p (x - a)

theorem divergence_translate (V : ℝ³ → ℝ³) (a x : ℝ³) :
    Community.divergence (fun y => V (y - a)) x = Community.divergence V (x - a)

theorem divergence_const_add (m : ℝ³) (V : ℝ³ → ℝ³) (x : ℝ³) :
    Community.divergence (fun y => m + V y) x = Community.divergence V x
```
PROVED (`Tier9Final.lean` C, copied from ReconR4.lean:48-100: `ContDiffOn.comp` with `MapsTo`;
`laplacian_translate` for ANY codomain and NO differentiability,
`laplacian_eq_iteratedFDeriv_stdOrthonormalBasis` + `iteratedFDeriv_comp_sub`
(FTaylorSeries.lean:969); `fderiv_comp_sub`, `fderiv_const_add`).

The joint within-derivative decomposition and the boosted operators (helpers
`hasFDerivWithinAt_uncurry`, `hasFDerivAt_space_slice`, `fderiv_space_slice`,
`hasDerivWithinAt_time_slice`, `derivWithin_time_slice`, `hasDerivWithinAt_galCurve`,
`mapsTo_galCurve`, `hasDerivWithinAt_galV_time`, `clm_neg_one`):

```
theorem derivWithin_galV_time {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (m x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    derivWithin (galV m w x ·) (Ici 0) τ =
      derivWithin (w (x - τ • m) ·) (Ici 0) τ - fderiv ℝ (w · τ) (x - τ • m) m

theorem fderiv_galV_space {w : ℝ³ → ℝ → ℝ³} (m x : ℝ³) (τ : ℝ) :
    fderiv ℝ (galV m w · τ) x = fderiv ℝ (w · τ) (x - τ • m)

theorem convection_galV {w : ℝ³ → ℝ → ℝ³} (m x : ℝ³) (τ : ℝ) :
    fderiv ℝ (galV m w · τ) x (galV m w x τ) =
      fderiv ℝ (w · τ) (x - τ • m) m + fderiv ℝ (w · τ) (x - τ • m) (w (x - τ • m) τ)

theorem laplacian_galV_space {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (m x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    Δ (galV m w · τ) x = Δ (w · τ) (x - τ • m)

theorem gradient_galP_space {q : ℝ³ → ℝ → ℝ} (m x : ℝ³) (τ : ℝ) :
    gradient (galP m q · τ) x = gradient (q · τ) (x - τ • m)

theorem galV_zero {w : ℝ³ → ℝ → ℝ³} (m x : ℝ³) : galV m w x 0 = m + w x 0

theorem isOnePeriodic_galV {w : ℝ³ → ℝ → ℝ³} (m : ℝ³) {τ : ℝ}
    (h : IsOnePeriodic (w · τ)) : IsOnePeriodic (galV m w · τ)

theorem isOnePeriodic_galP {q : ℝ³ → ℝ → ℝ} (m : ℝ³) {τ : ℝ}
    (h : IsOnePeriodic (q · τ)) : IsOnePeriodic (galP m q · τ)

theorem divergence_galV {w : ℝ³ → ℝ → ℝ³} (m : ℝ³) {τ : ℝ}
    (h : ∀ x, Community.divergence (w · τ) x = 0) (x : ℝ³) :
    Community.divergence (galV m w · τ) x = 0
```
PROVED (`Tier9Final.lean` C, copied from ReconR4.lean:173-243; pin traps recorded there and
binding on the builder: `HasFDerivWithinAt.comp_hasFDerivAt` / `.comp_hasDerivWithinAt` take
the point FIRST; the curve `σ ↦ (x - σ • m, σ)` needs `comp_hasDerivWithinAt_of_eq … rfl`;
`hasDerivAt_id' τ` and `hasDerivAt_const τ x₀` take their points explicitly; `(2 : WithTop ℕ∞)
≤ ∞` is closed by `WithTop.coe_le_coe.2 le_top`, not by `exact_mod_cast`/`simp`/`norm_num`;
`ContDiffAt.laplacian_add` wants the Pi sum with an explicit `(… : ℝ³ → ℝ³)` ascription;
`fderiv_comp_sub` is not a bare `rw` pattern under a lambda).

The class transfer:

```
theorem galilean_class {ν' : ℝ} {w₀ : ℝ³ → ℝ³} {w : ℝ³ → ℝ → ℝ³} {q : ℝ³ → ℝ → ℝ} (m : ℝ³)
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' w₀ (f := 0) w q) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun x => m + w₀ x) (f := 0)
      (galV m w) (galP m q)
```
PROVED (`Tier9Final.lean` C, copied from ReconR4.lean:247: seven fields; `navier_stokes` by the
four rewrites, `simp only [Pi.zero_apply, add_zero]`, `rw [← hns]`, `abel`; Mathlib plus the
`Community` definitions only, no coefficient-side fact; textbook Galilean invariance, nothing
new). At drift `0` the pair is unchanged (`galV_zero_drift`, `galP_zero_drift`, statement
critic A4, §6). The boost for `f ≠ 0` is out of scope (R4 unresolved, not needed).

#### W2: `TheoremB/CommunityData.lean` (probe `design/final/Tier9Final.lean` sections D and E, exit 0, 0 sorry decls)

The mean-free algebra (R5 section 4; helpers `freq_zero`, `conjVel_zero`, `dotR_zero_left`
(public clones of private tree lemmas), `meanFree_of_ne`, `norm_meanFree_le`):

```
def meanFree (c : (Fin 3 → ℤ) → Vel) : (Fin 3 → ℤ) → Vel

def meanVec (c : (Fin 3 → ℤ) → Vel) : ℝ³
```

```
theorem meanFree_zero (c : (Fin 3 → ℤ) → Vel) : meanFree c 0 = 0
```

```
theorem meanFree_of_mean_zero {c : (Fin 3 → ℤ) → Vel} (h : c 0 = 0) : meanFree c = c

theorem realField_meanFree {c : (Fin 3 → ℤ) → Vel} (h : RealField c) : RealField (meanFree c)

theorem divFree_meanFree {c : (Fin 3 → ℤ) → Vel} (h : DivFree c) : DivFree (meanFree c)

theorem summable_sob_meanFree {c : (Fin 3 → ℤ) → Vel}
    (h : ∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c l‖ ^ 2) :
    ∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖meanFree c l‖ ^ 2

theorem ens_meanFree (c : (Fin 3 → ℤ) → Vel) : ens (meanFree c) = ens c

theorem en_meanFree {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖ ^ 2) :
    en (meanFree c) = en c - ‖c 0‖ ^ 2

theorem uLift_meanFree_add {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖) (j : Fin 3)
    (x : ℝ³) : uLift j c x = c 0 j + uLift j (meanFree c) x

theorem u₀Real_eq_meanVec_add {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖) (x : ℝ³) :
    u₀Real c x = meanVec c + u₀Real (meanFree c) x

theorem u₀Real_eq_meanVec_add' {c : (Fin 3 → ℤ) → Vel} (h : Summable fun k => ‖c k‖) :
    u₀Real c = fun x => meanVec c + u₀Real (meanFree c) x
```
PROVED (`Tier9Final.lean` D1, copied from ReconR5.lean:92-181 and :409; `meanFree_of_mean_zero`
is glue (`funext` + `by_cases`); `en_meanFree` via `Summable.tsum_eq_add_tsum_ite 0` under
`classical`; `uLift_meanFree_add` via the point split at `0`, `mFourier_zero`,
`ContinuousMap.one_apply`; the `@[simp]` attribute of `meanFree_zero` sits on its own line for
the byte-identity tool).

The zero-mode family (R5 section 4b; helpers `uLift_zeroMode`, `conjVel_castCV`,
`ens_zeroMode`, `en_zero`, `ens_zero`):

```
def zeroMode (m : ℝ³) : (Fin 3 → ℤ) → Vel

theorem u₀Real_zeroMode (m : ℝ³) : u₀Real (zeroMode m) = fun _ => m

theorem realField_zeroMode (m : ℝ³) : RealField (zeroMode m)

theorem summable_norm_zeroMode (m : ℝ³) : Summable fun k => ‖zeroMode m k‖

theorem meanFree_zeroMode (m : ℝ³) : meanFree (zeroMode m) = 0

theorem meanVec_zeroMode (m : ℝ³) : meanVec (zeroMode m) = m

theorem zeroMode_meets_all_but_mean_zero (m : ℝ³) (κ : ℝ) {ν : ℝ} (hν : 0 < ν) :
    (∀ q : ℕ, Summable fun l => ‖freq l‖ ^ (2 * q) * ‖zeroMode m l‖ ^ 2) ∧
    RealField (zeroMode m) ∧ DivFree (zeroMode m) ∧
    κ * en (zeroMode m) * ens (zeroMode m) < ν ^ 4 ∧
    (zeroMode m 0 = 0 ↔ m = 0)
```
PROVED (`Tier9Final.lean` D2, copied from ReconR5.lean:185-230, :414, :420;
`realField_zeroMode` and `summable_norm_zeroMode` are R5's inline arguments made standalone
(`summable_of_ne_finset_zero (s := {0})`)).

THE CAPSTONE, the witness-exposing sibling, the consistency corollary:

```
theorem theorem_B_community_periodic_data :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ →
      κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 →
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0) v p
```
PROVED (`Tier9Final.lean` D3, the composition check of the house pattern: `obtain ⟨κ, hκ, H⟩
:= theorem_B_community_periodic`; `datum_bridge hu₀`; `H` at `meanFree (coeff u₀)` with
`summable_sob_meanFree`, `meanFree_zero`, `realField_meanFree`, `divFree_meanFree` and the
hypothesis as stated; `u₀Real_eq_meanVec_add'` at `p = 0` of the ℓ¹ certificate, rewritten by
the inversion into `u₀ = fun x => meanVec (coeff u₀) + u₀Real (meanFree (coeff u₀)) x`;
`galilean_class (meanVec (coeff u₀))`; `rwa [← hu] at hg` (the lambda of `galilean_class`'s
datum matches the mean-split lambda syntactically: the design measured it, the feasibility
critic re-measured it with an `rfl` example)). PROVED A SECOND TIME from the SORRY'd interface
alone (`critique/feasibility/FeasCompose.lean`, exit 0: `datum_bridge`, `galilean_class`,
`u₀Real_eq_meanVec_add'` and the mean-free algebra with `sorry` bodies, the capstone's proof
text verbatim; `sorryAx` enters only through the interface), so the capstone depends on the
frozen STATEMENTS only. `InitialVelocityConditionPeriodic` of the shifted datum is neither
assumed nor needed (the class has no field on the datum beyond `initial_condition`,
CommunityClass.lean:181-198). Docstring: RC1 and RC2 applied (the constant datum satisfies the
hypothesis for every `ν' > 0`, indeed every `ν' ≠ 0`, and at `ν' = 0` it reads `0 < 0`; the
mean vector enters no hypothesis, register `capstone_hyp_shifted_iff`). The statement critic's
attacks A1 to A4 fail against this shape (§6). `κ` is that of `theorem_B_community_periodic`
(hence of `theorem_B_joint_smooth`), of explicit form and exported as a compiled existential.

```
theorem theorem_B_community_periodic_data_flow :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {u₀ : ℝ³ → ℝ³},
      InitialVelocityConditionPeriodic (n := 3) u₀ →
      κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = meanFree (coeff u₀) ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = meanFree (coeff u₀) k + ∫ s in (0:ℝ)..t,
          ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-((2 * Real.pi * ν') * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en (meanFree (coeff u₀)) ∧
          ens (c t) ≤ ens (meanFree (coeff u₀)) ∧
          κ * en (c t) * ens (c t) < (2 * Real.pi * ν') ^ 4) ∧
        -- the member of the community class is the boosted real pair of THIS flow
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' u₀ (f := 0)
          (galV (meanVec (coeff u₀)) (vReal c)) (galP (meanVec (coeff u₀)) (pReal c))
```
PROVED (`Tier9Final.lean` D3: `theorem_B_community_periodic_flow` at `ν := 2πν'`, `obtain` with
`c`, the seven kept clauses, thirteen dropped clauses and `hclass`; `mul_div_cancel_left₀` turns
the class at `(2πν')/(2π)` into the class at `ν'`; then as above). Clauses 1 to 6 are
line-identical to CommunityClass.lean:1621-1629 under the substitution `c₀ ↦ meanFree (coeff
u₀)`, `ν ↦ (2 * Real.pi * ν')`; clause 7 is identical up to a line re-wrap (three lines here,
two there) and the parentheses the substitution requires (`en (meanFree (coeff u₀))`), measured
by both critics (D10). Docstring: RC3 applied in the feasibility critic's wording: the class
carries no uniqueness clause, this sibling delivers existence with an exhibited witness, and
these seven clauses SUPPLY `theorem_B_unique`'s hypothesis set on every window `Icc 0 T` with
`E := en (meanFree (coeff u₀))`, `Z := ens (meanFree (coeff u₀))` (FullUnique.lean:327-345;
`RealField`, clause 6 and the `κ` bound are not consumed), so that uniqueness of the
COEFFICIENT flow behind the witness can be cited. The `∃ κ` is re-chosen by statement, as in
every capstone of the tree (the house pattern); "κ" means "the κ of
`theorem_B_community_periodic_flow`" by proof, not by statement.

```
theorem theorem_B_community_periodic_of_data :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      κ * en c₀ * ens c₀ < (2 * Real.pi * ν') ^ 4 →
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real c₀) (f := 0) v p
```
PROVED (`Tier9Final.lean` D3: `initialVelocityConditionPeriodic_u₀Real`,
`summable_weighted_norm h0 (hsob (q + 2))` at `q = 0` for the ℓ¹ certificate (the tree's own
incantation, CommunityClass.lean:880; `summable_weighted_norm` needs `c 0 = 0`,
SobolevNorms.lean:220), `coeff_u₀Real`, `meanFree_of_mean_zero`). Its hypothesis text is
exactly that of `theorem_B_community_periodic`; its conclusion is the third conjunct of the 8b
conclusion (statement critic).

### 4c. CANDIDATE (W3, uniqueness): sized, NOT promised, NOT part of the W1/W2 freeze

#### W3 (CANDIDATE, not frozen): `TheoremB/CommunityUnique.lean` (probe `design/final/Tier9Final.lean` section F, `namespace T9Candidate`, exit 0, 2 sorry decls)

```
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
```
COMPILED (sorry bodies; ReconR6.lean:172, :180; `#print axioms` shows `sorryAx`). If W3 is
ever built these two statements freeze as written (namespace to be decided then); the route and
the sizing are in the appendix of `design/design.md`, restated in §5. The pressure is unique
only up to a function of time (the `k = 0` pressure mode is free, R6 (3.vii)); never claim
`p₁ = p₂`. No docstring claims uniqueness in the class is delivered (statement critic, item 6).

## 5. Wave plan

**Doctrine (binding; it produced ten waves with zero blockers across Tiers
8a and 8b).** Per wave, one Workflow: one builder (statements byte-for-byte
from §4; only bodies change; if a frozen statement cannot be proved as
written, keep it, add a sibling, record spec drift; register every frozen
theorem in BOTH `TheoremB.lean` and `AxiomCheck.lean`; run the gate), then
two readers in parallel (statement-shape/vacuity with cheap-witness and
inhabitation probes; proof-and-pin with Mathlib-name probes and an
independent gate run), then a fix pass for blockers and majors. Then the
ORCHESTRATOR re-runs the gate, re-checks byte-identity of every frozen
statement against this file with its own script
(`audit-tier9/tools/byte_identity.py`, `check_capstone.py`; recompute block
line bounds with `grep -n "^#### W"` before every run), commits with the
harness trailer, and lays the ladder tag of §5. All Tier 1 to 8 files are
never edited; private lemmas are cloned, never un-privated; new files only,
plus the two registration files.

The orchestrator's tools for the byte-identity step are `audit-tier9/tools/byte_identity.py`
(block bounds by `grep -n "^#### W"` on THIS file) and `tools/check_capstone.py` with an
expected-text file for `theorem_B_community_periodic_data_flow` derived from
`Tier9Final.lean` lines 1167 onward, written by this pass as
`design/final/expected_theorem_B_community_periodic_data_flow.txt` (or compared
whitespace-insensitively), NOT by textual substitution into the tree's lines (feasibility M1,
statement critic M5, §6); the banned-words grep runs with the em-dash test replaced by a Python
count until §8 item 8 is done.

| Wave | Files | Delivers (source in `Tier9Final.lean`) | Copied verbatim / glue / new | Risk | Lines / sessions | Ledger (+`#print axioms` lines) | Tag |
|---|---|---|---|---|---|---|---|
| W1 | `Descent.lean`, `DatumBridge.lean` | section A (45 declarations: 35 frozen = 29 theorems + 6 defs, 10 helpers) and section B (25 declarations: 17 frozen = 16 theorems + 1 def, 8 helpers) | verbatim from R2 (periodicity, rep/descend, fiber, brick, C¹ bridge, descend of a lift), R1 (six coefficient facts), R3 (dirDeriv/dirIter, decay, summability, DivFree, round trip): about 520 lines; glue (`IsOnePeriodic.fderiv_apply`, `hasDerivAt_descend_dirDeriv`, the `Vel` packing, `realField_coeff`, `isOnePeriodic_u₀Real`): about 90 lines; new (`u₀Real_coeff`, `datum_bridge`): about 40 lines; two file preambles with the three local instances; docstrings for every frozen declaration (about 90 lines); registration | LOW (everything PROVED at the pin in one file, twice for the inversion; the build work is the split into two files, the docstrings and the gate) | about 800 to 850 lines in the two files + 47 registration lines / 2 sessions (1 builder, 1 reader round and fix) | +45 (29 + 16): 294 → 339 | `t9-datum-bridge-green` |
| W2 | `Galilean.lean`, `CommunityData.lean` | section C (35 declarations: 21 frozen = 17 theorems + 3 defs + 1 abbrev, 14 helpers), section D (32 declarations: 22 frozen = 19 theorems + 3 defs, 10 helpers), section E (41 declarations: 16 registered probe theorems, 25 helpers and clones) | verbatim from R4 (all of C, about 240 lines), R5 (mean-free algebra, zeroMode, the register and the pair-datum clones: about 330 lines), the statement critic's section G (the RC5 items: about 150 lines); glue (`meanFree_of_mean_zero`, `realField_zeroMode`, `summable_norm_zeroMode`, `en_zero`/`ens_zero`, `coeff_const`, `coeff_testDatum`: about 40 lines); new (the capstone, the flow sibling, the corollary, `capstone_hyp_*`, `capstone_fires_*`, `inversion_fails_off_class`: about 150 lines); two preambles (instances in CommunityData only); docstrings (about 90 lines); registration | LOW (all PROVED; the composition compiled three times: design, `FeasCompose.lean` from the sorry'd interface, `Tier9Final.lean`; the W3Probe/W4Probe/TimeConstantWitness public names the register cites are read and exercised) | about 1000 to 1050 lines in the two files + 52 registration lines / 2 sessions | +52 (17 + 19 + 16): 339 → 391 | `t9-complete` |
| W3 (optional, DEFERRED) | `TheoremB/CommunityUnique.lean` (name proposed) | R6 (2a), (2b) and the (3.i) to (3.vii) bridge | PROVED already in R6: `en_coeff_eq` (Parseval), `eq_of_mFourierCoeff_eq`, `lerayProj_pressure_gradient`; W1 now supplies `divFree_coeff` at each time and the `dirDeriv` bridge for the `ens` version; everything else new; the driver is the slice extraction from `ContDiffOn` on the closed half-slab (differentiation under the integral with the time-derivative slice's continuity), unmeasured pin territory | MED | about 1300 / 6 to 8 (both critics agree) | about +20 | `t9-unique-green` (proposed; only if built) |

Ledger: the gate goes from 294 to 339 after W1 and to 391 after W2, every line on exactly
`[propext, Classical.choice, Quot.sound]` (`Tier9Final.lean` already shows the standard triple
on every audited W1/W2 name and on the five RC5 items). Registration formats, read from the
tree: `TheoremB.lean` = 60 bare `import TheoremB.<File>` lines; `AxiomCheck.lean` = the same
60 import lines + 294 `#print axioms TheoremB.<name>` lines (probe names namespaced, e.g.
`TheoremB.T9Probe.<name>`); `scripts/check_axioms.sh` builds, runs AxiomCheck.lean and greps
`sorryAx` and non-standard axioms. W1 adds 2 import lines to each registration file and 45
`#print axioms` lines; W2 adds 2 + 2 import lines and 52 lines, 36 of them `TheoremB.<name>`
and 16 `TheoremB.T9Probe.<name>`; defs carry no ledger line. Order: W1 then W2, separate
sessions, never in the same chat as any W3 attempt. Ladder (each rung taggable and honest):
9-v1 = W1 (`t9-datum-bridge-green`: the datum bridge alone is a complete, gate-checkable
statement about the community's initial-velocity condition); 9-v2 = W1 + W2 (`t9-complete`);
the optional W3 rung `t9-unique-green` only if built, in a separate chat after `t9-complete`.

## 6. Vacuity / must-fail register (compiled; land in `T9Probe` of CommunityData.lean)

All items below are PROVED in `design/final/Tier9Final.lean` section E unless marked otherwise
(the ones marked `ShapeProbe.lean` are PROVED in `critique/shape/ShapeProbe.lean` section G,
pass 2 exit 0, standard three axioms, and NOT carried into the tree); each item carried is
registered (one `#print axioms` line) and stated in the probe's own namespace `T9Probe`, with
`open TimeConstantWitness` for the public pair-datum names (R5's clones of the PRIVATE
`W3Probe` facts, never un-privated: `zero_notMem_ccBox`, `ccPair_zero_mode`, `ccBox_symm`,
`conjVel_ccVec`, `realField_ccPair_ccVec`, `dotR_ccVec_(neg_)ccpe1`, `divFree_ccPair_ccVec`,
`summable_wsq_ccPair`, `summable_norm_ccPair`, `pair_tsum_sq`, `en_ccPair`, `ens_ccPair`,
`norm_ccVec`, helper `divergence_const`; the RC5 helpers `ccpe1_ne_zero`, `testDatum_ccpe1`,
`ccVec_ne_zero`, `meanFree_add`, `meanVec_add`, `meanVec_of_mean_zero`, `realField_add`,
`coeff_const_add`, `testDatum_real`, `testDatum_summable`, `testDatum_zero_mode`,
`smallness_factors_shift_invariant`, `meanVec_coeff_shifted_shear`,
`no_time_constant_witness_on_shear`). The fenced statements below are extracted from
`Tier9Final.lean` like the frozen ones (byte-identity recommended, not required, D6).

- MUST INHABIT (the constant datum), PROVED: `const_datum_in_class` (every `m : ℝ³` meets
  `InitialVelocityConditionPeriodic`), `const_pair_in_class` (the constant pair
  `(fun _ _ => m, fun _ _ => 0)` is in the class for EVERY real `ν'`, sign unconstrained: the
  class alone says nothing about viscosity; only the capstone does), `rest_pair_in_class'`
  (`m = 0`, Pi-zero spellings). Consequence for the reader: "in the class" for a constant
  datum is NOT evidence of anything; every must-fail item is checked on the SHEAR datum.

```
theorem const_datum_in_class (m : ℝ³) :
    InitialVelocityConditionPeriodic (n := 3) (fun _ => m)

theorem const_pair_in_class (ν' : ℝ) (m : ℝ³) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0)
      (fun _ _ => m) (fun _ _ => 0)

theorem rest_pair_in_class' (ν' : ℝ) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (0 : ℝ³ → ℝ³) (f := 0)
      (0 : ℝ³ → ℝ → ℝ³) (0 : ℝ³ → ℝ → ℝ)
```

- THE CONSTANT DATUM IS HANDLED, NOT EXCLUDED, PROVED: `coeff_const` (`coeff (fun _ => m) =
  zeroMode m`, through `u₀Real_zeroMode` and the round trip), `capstone_hyp_const_datum` (the
  smallness hypothesis holds for every constant datum, every `κ`, every `ν' > 0`: the
  mean-free part is `0`), `capstone_fires_on_const_datum` (the capstone fires on `u₀ = m`; at
  `m = 0` this is the rest state). Together with `zeroMode_meets_all_but_mean_zero` (§4b): the
  mean-zero hypothesis of the 8b capstone was the ONLY obstruction, and the boost removes it.
  Sharpened by the statement critic (`ShapeProbe.lean`, not carried): the hypothesis holds for
  every `ν' ≠ 0` (`capstone_hyp_const_datum_all_nonzero_visc`), FAILS at `ν' = 0` where it
  reads `0 < 0` (`capstone_hyp_const_datum_fails_at_zero_visc`; hence RC1: "for every
  `ν' > 0`", never "for every `ν'`"), and holds for the rest state in the Pi-zero spelling
  (`capstone_hyp_rest_state`).

```
theorem coeff_const (m : ℝ³) : coeff (fun _ => m) = zeroMode m

theorem capstone_hyp_const_datum (m : ℝ³) (κ : ℝ) {ν' : ℝ} (hν' : 0 < ν') :
    κ * en (meanFree (coeff (fun _ => m))) * ens (meanFree (coeff (fun _ => m)))
      < (2 * Real.pi * ν') ^ 4

theorem capstone_fires_on_const_datum (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun _ => m) (f := 0) v p
```

- MUST INHABIT, NONZERO AND NON-CONSTANT (the shear datum), PROVED: `testDatum_in_class`
  (every `ε`; membership needs no `ε ≠ 0`), `coeff_testDatum` (the round trip on the shear
  datum, needed to COMPUTE `meanFree (coeff (u₀Real (testDatum ε)))`), `capstone_hyp_testDatum`
  (for every `κ, ν' > 0` there is `ε ≠ 0`, namely `ε = 2πν'/(κ+3)`, with
  `κ · en · ens = 4κ(2πν')⁴/(κ+3)⁴ < (2πν')⁴`; R5's arithmetic at `ν := 2πν'`), and NOW
  `shear_not_const` (RC5: the shear is not `fun _ => m` for any `m`; the round trip would force
  `testDatum ε = zeroMode m`, which fails at the mode `ccpe1`). Non-constancy is the fact that
  matters for vacuity: the constant datum is exactly the case the boost trivialises. The joint
  statement `capstone_hypotheses_inhabited_nonconst` (both frozen hypotheses exactly as frozen,
  `u₀ ≠ 0`, `∀ m, u₀ ≠ fun _ => m`) is PROVED in `ShapeProbe.lean` (not carried; it is the
  conjunction of the carried items).

```
theorem testDatum_in_class (ε : ℝ) :
    InitialVelocityConditionPeriodic (n := 3) (u₀Real (W3Probe.testDatum ε))

theorem coeff_testDatum (ε : ℝ) : coeff (u₀Real (W3Probe.testDatum ε)) = W3Probe.testDatum ε

theorem capstone_hyp_testDatum {κ ν' : ℝ} (hκ : 0 < κ) (hν' : 0 < ν') :
    ∃ ε : ℝ, ε ≠ 0 ∧
      κ * en (meanFree (coeff (u₀Real (W3Probe.testDatum ε)))) *
        ens (meanFree (coeff (u₀Real (W3Probe.testDatum ε)))) < (2 * Real.pi * ν') ^ 4

theorem shear_not_const {ε : ℝ} (hε : ε ≠ 0) (m : ℝ³) :
    u₀Real (W3Probe.testDatum ε) ≠ fun _ => m
```

- THE HYPOTHESIS IS RESTRICTIVE (statement critic's attack A3: were the smallness hypothesis
  universal on the class, the capstone would be the full positive statement), PROVED as a
  compiled failure: `capstone_hyp_not_universal` (for every `κ, ν' > 0` the shear at
  `ε = 2πν'(1 + 1/κ)` is in the class and FAILS the hypothesis, `4κε⁴ ≥ 16(2πν')⁴`). So the
  capstone says nothing about general data, as its docstring says.

```
theorem capstone_hyp_not_universal {κ ν' : ℝ} (hκ : 0 < κ) (hν' : 0 < ν') :
    ∃ u₀ : ℝ³ → ℝ³, InitialVelocityConditionPeriodic (n := 3) u₀ ∧
      ¬ (κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4)
```

- THE MEAN ENTERS NO HYPOTHESIS (the honest content of W2, compiled as an identity, not
  prose), PROVED: `coeff_const_add` (`coeff (fun x => m + u₀Real d x) = zeroMode m + d`: the
  mean IS seen by `coeff`), `smallness_factors_shift_invariant` and
  `meanVec_coeff_shifted_shear` (both factors of the hypothesis on `m + shear` are the shear's;
  the mean vector is `m`, seen and DISCARDED), `capstone_hyp_shifted_iff` (the frozen
  hypothesis for `m + shear` is literally the hypothesis for the shear, every `m`),
  `ivc_const_add` (adding a constant keeps a datum in the class; R4's "unresolved" item and the
  design's §8 item 6, one lemma), `capstone_fires_on_shifted_shear` (the capstone FIRES on
  `m + shear` for every `m` with the same `ε`, and the boosted rest state `v := m` is not the
  witness).

```
theorem capstone_hyp_shifted_iff (m : ℝ³) (ε κ ν' : ℝ) :
    (κ * en (meanFree (coeff (fun x => m + u₀Real (W3Probe.testDatum ε) x))) *
        ens (meanFree (coeff (fun x => m + u₀Real (W3Probe.testDatum ε) x)))
        < (2 * Real.pi * ν') ^ 4) ↔
    (κ * en (W3Probe.testDatum ε) * ens (W3Probe.testDatum ε) < (2 * Real.pi * ν') ^ 4)

theorem ivc_const_add {u : ℝ³ → ℝ³} (m : ℝ³) (hu : InitialVelocityConditionPeriodic (n := 3) u) :
    InitialVelocityConditionPeriodic (n := 3) (fun x => m + u x)

theorem capstone_fires_on_shifted_shear (m : ℝ³) {ν' : ℝ} (hν' : 0 < ν') :
    ∃ ε : ℝ, ε ≠ 0 ∧
      (∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν'
          (fun x => m + u₀Real (W3Probe.testDatum ε) x) (f := 0) v p) ∧
      ∀ p : ℝ³ → ℝ → ℝ, ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν'
          (fun x => m + u₀Real (W3Probe.testDatum ε) x) (f := 0) (fun _ _ => m) p
```

- MUST FIRE, NON-TRIVIALLY (the cheap-witness attempts, compiled as negations), PROVED:
  `capstone_fires_on_testDatum`: for every `ν' > 0` there is `ε ≠ 0` such that the real shear
  datum is NONZERO (`W3Probe.u₀Real_testDatum_ne_zero`, CommunityClass.lean:1119), the
  capstone fires on it, AND for every pressure both trivial candidates fail: `v := 0` fails
  `initial_condition` (`W4Probe.rest_state_not_witness_for_nonzero`, :1899; the general sibling
  `rest_state_not_witness_of_ne_zero` is :1887), `v := fun x _ => u₀ x` fails `navier_stokes`
  (`TimeConstantWitness.const_witness_fails`, :2089, needs `ν' ≠ 0`, supplied by `hν'.ne'`).
  STRONGER, carried as the helper `no_time_constant_witness_on_shear`: NO time-constant
  velocity `fun x _ => w x` is a witness on the shear (the class's `initial_condition` forces
  `w = u₀`); its corollaries `no_rest_witness_on_shear`, `no_const_drift_witness_on_shear` and
  the one-statement form `capstone_conclusion_not_cheap` (both frozen hypotheses plus the three
  negated `∃ p` clauses) are PROVED in `ShapeProbe.lean` (not carried). Further cheap attempts,
  closed by the statement itself: `κ := 0` is excluded by `0 < κ`; the hypothesis is not
  vacuous (the shear and the constant datum inhabit it) and not universal
  (`capstone_hyp_not_universal`); the conclusion is not trivial (this item); `u₀ := 0` alone
  would be empty (rest state) and the capstone quantifies over an arbitrary datum in the class.

```
theorem capstone_fires_on_testDatum {ν' : ℝ} (hν' : 0 < ν') :
    ∃ ε : ℝ, ε ≠ 0 ∧
      u₀Real (W3Probe.testDatum ε) ≠ 0 ∧
      (∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
          (f := 0) v p) ∧
      ∀ p : ℝ³ → ℝ → ℝ,
        ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
            (f := 0) (fun _ _ => 0) p ∧
        ¬ NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real (W3Probe.testDatum ε))
            (f := 0) (fun x _ => u₀Real (W3Probe.testDatum ε) x) p
```

- JUNK VALUE (the hypothesis is load-bearing), PROVED: `inversion_fails_off_class`: `coeff` of a
  NON-periodic field is a well-typed junk object (`descend` is total through the `[0,1)³`
  representative) and the inversion FAILS for `u := id`, because `u₀Real (coeff u)` is
  one-periodic for EVERY coefficient field (`isOnePeriodic_u₀Real`) and `id` is not. The
  capstone's `InitialVelocityConditionPeriodic` hypothesis is what makes `coeff u₀` meaningful;
  the same applies to `coeff` of a non-integrable field (the torus integral of a junk descent is
  a junk number, and `realField_coeff` is true of it because `0 = conj 0`, D7). The statement
  critic's `inversion_not_unconditional : ¬ ∀ u, u₀Real (coeff u) = u` (`ShapeProbe.lean`) is
  this item in universal form. Attack A2 (`coeff ≡ 0` against `datum_bridge`) fails:
  `coeff_shear_ne_zero` (`ShapeProbe.lean`), and the fifth conjunct would force `u = 0`.

```
theorem inversion_fails_off_class : u₀Real (coeff (fun x : ℝ³ => x)) ≠ fun x => x
```

- MUST HOLD (consistency), PROVED: `theorem_B_community_periodic_of_data` (§4b): the new
  capstone specialises to the `∃ v p` of `theorem_B_community_periodic` at `u₀ := u₀Real c₀`.
- COMPOSITION, PROVED: `theorem_B_community_periodic_data` and `_data_flow` from the W1
  interface, `galilean_class` and the mean-free algebra (§4b), on the standard three axioms in
  `Tier9Final.lean` (interface proved) and with `sorryAx` entering only through the interface in
  `FeasCompose.lean` (interface sorry'd). `capstone_fires_on_shifted_shear` and
  `capstone_fires_on_testDatum` CONSUME the capstone and are on the standard triple, which
  confirms by composition that the capstone is proved, not sorry'd.
- THE INVERSION, PROVED TWICE (G10): the design's pointwise route (`Tier9Final.lean`
  `u₀Real_coeff`) and the feasibility critic's L² injectivity route (`FeasInversion.lean`
  `u₀Real_coeff_alt`), both on the standard three axioms.
- GALILEAN CHANGE, NO HIDDEN RESHAPING (attack A4): `galV_zero_drift : galV 0 w = w`,
  `galP_zero_drift : galP 0 q = q` (`ShapeProbe.lean`), so `theorem_B_community_periodic_of_data`
  really is the 8b `∃ v p` with the same pair up to `rfl`-level identities.
- SLICE GENUINENESS: inherited from Tier 8b (`W4Probe.differentiableWithinAt_time_slice_of_
  velocity_smooth`, `differentiableAt_space_slice_of_velocity_smooth`); the boosted pair's
  smoothness is `contDiffOn_galV`/`_galP`, so the same lemmas apply to the witness.
- QUANTIFIER ORDER (statement critic, item 3): `∃ κ, 0 < κ ∧ ∀ {ν'}, 0 < ν' → ∀ {u₀}, IVC u₀ →
  smallness → ∃ v p, class`: `κ` is class-uniform, before `ν'` and `u₀`, as in 8b. Compiled
  content of the hypothesis on the shear: `capstone_hyp_on_shear_explicit` (`ShapeProbe.lean`):
  `4κε⁴ < (2πν')⁴`.
- BYTE-IDENTITY of the seven clauses of the flow sibling against
  `theorem_B_community_periodic_flow` (CommunityClass.lean:1621-1633) with `ν ↦ (2 * Real.pi
  * ν')` and `c₀ ↦ meanFree (coeff u₀)`: clauses 1 to 6 are byte-identical after substitution;
  clause 7 is re-wrapped over three lines and parenthesised (`en (meanFree (coeff u₀))`, not the
  naive textual `en meanFree (coeff u₀)`); the expected-text file for `check_capstone.py` must
  be that form, not the naive textual substitution: derive it from `Tier9Final.lean` lines
  1167 onward (written by this pass as
  `design/final/expected_theorem_B_community_periodic_data_flow.txt`; `check_capstone.py` run on it
  against `Tier9Final.lean` by this pass: byte-identical) or compare whitespace-insensitively,
  never by textual substitution into the tree's lines (critic pass, 13 Sep; RC4 and feasibility
  item 1). Byte-identity of every frozen statement of §4 against `Tier9Final.lean`: re-run by
  this pass (§4 preamble); the orchestrator re-runs it against the BUILT files at every gate.
- NOT PROBED (and out of scope): the boost for `f ≠ 0` (R4 unresolved), a coefficient-side
  description of the boost (phase twist of the `k ≠ 0` modes), the nonzero-ness `u₀Real c ≠ 0`
  from `c ≠ 0` in general (R5 sidesteps it by the explicit shear datum; the round trip
  `coeff_u₀Real` now gives it for real ℓ¹ families: `c = coeff (u₀Real c)`, so `u₀Real c = 0`
  forces `c = coeff 0 = 0`; not compiled as a lemma, one line if wanted); a cheap coefficient
  flow `c` for the FLOW sibling (its clauses 1 to 7 are those of
  `theorem_B_community_periodic_flow`, whose shape was audited in 8b).

## 7. Audit register

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
- Rule 6, Tier 9 instance (PROPOSED only; the user's call; NOT before the capstone ships with
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

**Banned-words grep record of THIS file** (the orchestrator's `tools/banned_words.sh`, whose
em-dash test is a no-op on macOS, plus a Python count of U+2014 and U+2013; run by this pass
after generation, §8 item 8): script run after generation: 1 word-list hit in this file, at line 1245, which is the verbatim skeleton line of rule 2 (the rule's own negated priority phrase, flagged by the script's definite-article test); 0 word-list hits in `Tier9Final.lean`; the script's em-dash test printed its macOS usage error and tested nothing. Python count: U+2014 = 5 in this file, at lines 1, 111, 1238, 1244, 1255, every one inside text carried verbatim from the skeleton (the title; the W2 bullet of §1; rules 1, 2 and 3 of §7), and 0 in `Tier9Final.lean`; U+2013 = 1 in this file (line 1263, rule 5 of §7, verbatim) and 0 in `Tier9Final.lean`; no em-dash and no en-dash in any sentence written by this pass. (The line numbers are those after the record itself was inserted; the record adds no hit.)
ORCHESTRATOR'S RE-RUN (13 Sep 2026, after fixing both tools, §8 item 8, before the planning
commit): `tools/banned_words.sh` on this file now tests em-dashes for real; its hits are the
verbatim rung10 rule text only (rule 2's own negated priority phrase, flagged by the script's
definite-article test, and the em-dashes inside rules 1, 2 and 3 of §7); the
title and the W2 bullet of §1 no longer carry an em-dash; `Tier9Final.lean` CLEAN; the en-dash
of rule 5 is verbatim rung10 text. `tools/byte_identity.py` with `abbrev` in its DECL regex:
W1 Descent 35/35, W1 DatumBridge 17/17, W2 Galilean 21/21 (`abbrev slab` now seen by the tool),
W2 CommunityData 22/22, W3 candidate 2/2, §6 register 16/16; `check_capstone.py` on the flow
sibling: byte-identical to `design/final/expected_theorem_B_community_periodic_data_flow.txt`
(20 lines). The orchestrator also recompiled `Tier9Final.lean` (exit 0, 0 errors, 2 sorry decls,
25 of 26 `#print axioms` lines standard, sha256 `9a52de83a5bb0b13…` identical to the author's; log
`design/final/orchestrator-recompile.log`) and the seven recon probes
(`recon/orchestrator-recompile/VERIFIED.md`).

Textbook sources (cited, not ours; NO copy on this machine; theorem numbers UNVERIFIED and to
be filled by a reader with the books, hedged until then): Temam, *Navier-Stokes Equations:
Theory and Numerical Analysis*, Ch. III; Robinson-Rodrigo-Sadowski, *The Three-Dimensional
Navier-Stokes Equations* (CUP 2016), Ch. 6 and 7; Constantin-Foias, *Navier-Stokes Equations*,
Ch. 10; Foias-Manley-Rosa-Temam, *Navier-Stokes Equations and Turbulence* (CUP 2001), Ch. II;
for the Fourier inversion of smooth periodic functions and the rapid decay of their
coefficients, any text on Fourier series on the torus (Grafakos, *Classical Fourier Analysis*,
the chapter on the torus); for the Galilean invariance, the opening chapter of any of the
Navier-Stokes texts above. Priority hedged and named where it arises: leray-hopf (weak
existence), HeliCorgi/ns-mns2-flowmap-bridge (local mild uniqueness on `ℝ³`, 18 Aug 2026),
Miller, Alpöge-Buckmaster, OpenAI (the forced breakdown statement, the complementary half);
nothing here is new mathematics (Tier 9 included) and no priority is claimed.

Statement-shape facts to carry (from the critics and this pass):

- The `∃ κ` of the three Tier 9 capstones are unlinked by statement, each theorem re-chooses
  its own (the house pattern); "κ" means "the κ of `theorem_B_community_periodic`" by proof.
- The smallness hypothesis is on BOTH factors of the mean-free part (D3); its compiled content
  is `κ·0·0 < (2πν')⁴` on a constant datum (true iff `ν' ≠ 0`), `4κε⁴ < (2πν')⁴` on the shear,
  and literally the shear's hypothesis on `m + shear` for every `m` (`capstone_hyp_shifted_iff`).
- The mean is SEEN by `coeff` (`meanVec_coeff_shifted_shear = m`) and DISCARDED by the
  hypothesis; it is removed by `galilean_class`, which at drift `0` is the identity on the pair.
- The class has no field on the datum beyond `initial_condition` (CommunityClass.lean:181-198):
  `galilean_class` takes no datum-condition hypothesis and the shifted datum's
  `InitialVelocityConditionPeriodic` is a register helper (`ivc_const_add`), never a hypothesis.
- All equalities of the bridge (`u₀Real (coeff u) = u`, `coeff (u₀Real c) = c`, the fifth
  conjunct of `datum_bridge`) are FUNCTION equalities; every packing is `WithLp.toLp 2`;
  `coeff_apply` is `rfl`.
- Every frozen bridge lemma takes the class's `IsOnePeriodic` (one step
  `EuclideanSpace.single i 1`); the tree's `freq g` invariance is reached only through
  `Community.IsOnePeriodic.add_freq`.
- The three rep/descend spellings of R2, R3, R6 are ONE object at default transparency and NOT
  under `with_reducible` (`FeasTransfer.lean`).
- The `InitialVelocityConditionPeriodic` constructor is nested `⟨⟨div_free, smooth⟩,
  isOnePeriodic⟩`; the periodicity goal needs a `show` to beta-reduce the lambda before `rw`.
- Byte-identity rule, extended as in rung10: it covers the instantiation (`(f := 0)`, `(n :=
  3)`), comment lines inside statements (the flow sibling's one comment line counts), and the
  clause-7 re-wrap (expected text from `Tier9Final.lean`, never by substitution into the tree).
- Spec drift to record when W1 lands: none in the frozen tree (no earlier file is edited); the
  Tier 8b headers' sentence that the tree has no descent to the torus, if any reader finds one,
  is superseded and recorded in the Descent.lean header, not struck.

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

Honesty ledger for this pass:

| Grade | Items |
|---|---|
| Compiled by THIS pass (exit 0) | `design/final/Tier9Final.lean` (`lake env lean` at the pin: exit 0, 0 errors, 2 sorry decls = the W3 candidates, 25 of 26 `#print axioms` lines on the standard triple, log `design/final/compile1.log`); `tools/byte_identity.py` on this file vs `Tier9Final.lean` for every `^#### W` block and the §6 register (counts in the §4 preamble); the banned-words script and the Python em-dash count on this file (record above) |
| Read by this pass, not re-compiled | `design/DesignFinal.lean` and `design/compile-final.log` (exit 0, 2 sorry); the six recon probes, their `notes.md` and `recon/recon-results.json`; `critique/shape/ShapeProbe.lean`, `ShapeCritic_section.lean`, `compile1/2.log`, `report.md`; the seven feasibility probes, their logs and `report.md`; rung10 §§1b, 2, 3, 4b (W3/W4), 5b, 6b, 7, 8; the tree by grep: `CommunityClass.lean` :153-198 (through rung10 §2a), :207, :213, :236, :783, :876, :1071, :1119, :1285, :1615-1636, :1801-1810, :1887, :1899, :2089; `FullUnique.lean:327`; `FourierDeriv.lean:31-37`, `:129`; `SobolevNorms.lean:220`; `TheoremB.lean` and `AxiomCheck.lean` (60 imports each, 294 `#print axioms` lines); the tail of `gate/baseline-gate.log` (`GATE: GREEN`, exit 0); `git log`, `git tag`, `git status` |
| Reported by the critics or the recon, not verified here | every Mathlib signature and line number they cite; the recon exit codes; the critics' axiom outputs; the R6 sizing |
| Derived, not compiled | the line and session estimates; the ledger arithmetic (294 → 339 → 391); the wording rules; D9's "strictly stronger" (a statement with one hypothesis fewer, compiled, trivially implies the old one) |
| Cited, not ours | the textbook sources above (theorem numbers unverified) |
| Not run | `scripts/check_axioms.sh` (the baseline log of 12/13 Sep was read, not re-run); `lake build`; nothing under the repository was written; the orchestrator's tools were not edited (D13) |
| ORCHESTRATOR, independently (13 Sep, before the planning commit) | the gate baseline itself (`bash scripts/check_axioms.sh`, GREEN, 294 entries counted with wrapped lines joined); the seven recon probes recompiled (`recon/orchestrator-recompile/VERIFIED.md`); `Tier9Final.lean` recompiled (exit 0, 0 errors, 2 sorry decls, 25 of 26 standard, sha256 match); the two tools fixed and self-tested; byte-identity re-run on all six blocks with the fixed tool; `check_capstone.py` on the flow sibling; the banned-words grep re-run with a real em-dash test; `git log`/`git tag`/`git status` re-read (HEAD `03b1656`, 28 tags, clean) |

## 8. Open blockers and decisions for the user

None blocks W1. Open items, each with the decision this blueprint takes and what remains the
user's call:

1. **The replay script** (skeleton status header). DECIDED: nothing to do; it is committed at
   `03b1656` ("Kernel replay through the toolchain leanchecker"); the skeleton's "ONE untracked
   file" sentence is carried verbatim above and corrected in the status-header extension. User's
   call: whether to strike the stale sentence from the Tier 8b handoff prose.
2. **The smallness spelling** (D3). DECIDED: frozen on the MEAN-FREE part in BOTH factors,
   `κ * en (meanFree (coeff u₀)) * ens (meanFree (coeff u₀)) < (2 * Real.pi * ν') ^ 4`. User's
   call: whether to add a registered one-line sibling spelled `ens (coeff u₀)` (`rw
   [ens_meanFree]`); cost one theorem and one ledger line; not recommended (a mixed spelling
   invites the misreading that the mean enters the threshold).
3. **The pinned (witness-exposing) sibling** (D4). DECIDED: frozen, with RC3's docstring in the
   feasibility critic's wording (D10); existence only; the seven clauses SUPPLY
   `theorem_B_unique`'s hypotheses on every window. User's call: none, unless the sibling is to
   be dropped (not recommended: a W3 build would consume it, and it is the only statement that
   lets `theorem_B_unique` be cited for the witness).
4. **W3, build or defer** (D8). DECIDED: DEFER; the two statements are frozen as CANDIDATE only
   (§4c), sorry'd in the probe, never in the tree; tag `t9-unique-green` only if built, in a
   separate chat after `t9-complete`; the plan is the design's appendix. User's call: whether to
   build it at all (about 1300 lines, 6 to 8 sessions, MED).
5. **Announcement wording** (rule 6 of §7). PROPOSED only, after the capstone ships with W2
   (`t9-complete`); the proposed sentence is in the §7 amendments; whether to quote the upstream
   commit hash and the upstream statement name alongside the prose diff is the user's call
   (carried from rung10 §8 item 1 and the Tier 8b handoff).
6. **Trailer uniformity.** DECIDED for this tier: every Tier 9 commit ends with the harness
   trailer in force in the building session (the doctrine, §1). User's call: whether the
   trailers of the 66 earlier commits are to be made uniform (carried from the Tier 8b handoff;
   not done by this pass, which commits nothing).
7. **Textbook theorem numbers.** Need a reader with the books (carried from rung10 §8 item 8);
   the Fourier-series and Galilean references added above are hedged the same way.
8. **Tooling before the W1 gate (the orchestrator's action, D13).** DONE by the orchestrator on
   13 Sep 2026 before the planning commit: in `tools/banned_words.sh` the em-dash test is now the
   portable byte grep `grep -n $'\xe2\x80\x94' "$f"` (self-tested on a one-line file: exit 1
   with the hit); in `tools/byte_identity.py` `DECL` is
   `^(noncomputable def|theorem|lemma|def|abbrev|structure)\s+([^\s({:]+)` (the Galilean block
   now reads 21/21). `@[simp]` stays on its own line above a frozen declaration. Not edited by
   the blueprint pass (reason in D13).
9. **RC6 applied** (D9): `hc2` dropped from `mFourierCoeff_descend_uLift`; if the user prefers
   the tree-mirroring signature, the design's form is in `DesignFinal.lean:352` and the change
   back costs two lines; not recommended.
10. **RC3's wording** (D10): the feasibility critic's more conservative wording governs in the
    docstring and the route note; recorded here so that no reader restores "VERBATIM".
11. **Header format** (feasibility M6): colon after `W<n>` in the `#### W` headers, the
    `^#### W` prefix unchanged; a future byte-identity run must not "fix" it back to an em-dash.
12. **The `Fact ((0:ℝ) < 1)` instance**: DECIDED, not declared (measured unnecessary by the
    design and by every feasibility probe); the tree keeps its `haveI` habit inside
    `mFourierCoeff_deriv`.
13. **The shifted datum's class membership**: DECIDED, shipped as the register helper
    `T9Probe.ivc_const_add` (RC5), consumed by `capstone_fires_on_shifted_shear`, never by the
    capstone; the design's "three short lemmas" is one lemma (feasibility M7).
14. **Docstrings.** 69 of the design's 135 declarations carried none; every frozen declaration
    needs one under the rules of §7 (about 90 lines per wave, in the §5 estimates). Builder's
    work; the reader round checks each docstring against the rules.

Smallest next move: W1. The orchestrator fixes the two tools (item 8); then one Workflow:
transcribe `design/final/Tier9Final.lean` section A into `TheoremB/Descent.lean` and section B
into `TheoremB/DatumBridge.lean` (each with the file-level preamble of §4 and the three local
instances; no file-level `maxHeartbeats`; a docstring on every frozen declaration), add the two
import lines to `TheoremB.lean` and to `AxiomCheck.lean` with the 45 `#print axioms` lines, run
`bash scripts/check_axioms.sh` (expected: GATE: GREEN, 339 lines, every one on the standard
triple), re-check byte-identity of every W1 statement against §4a of this file, and hand the
wave to the two readers before any tag; `t9-datum-bridge-green` only after the fix pass.

BUILD LOG: empty at the planning commit.
