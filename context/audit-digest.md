# Audit digest: one row per audited wave

This repository says that two independent adversarial readers reviewed every wave of Tiers 8a, 8b, 9
and 9c before that wave was committed, with one exception: in 8a F5 the two readers were a
statement-shape reader and a claim-wording reader, and there was no proof-and-pin reader. The raw
reader reports and probe files sit in private session directories and are not published. This file
is the sanitised public record: one row per wave, taken from the structured result files of those
sessions (Tiers 9 and 9c only), from the commit message bodies, from the blueprints under
`context/` and from the replay records in this directory. A cell that no file backs reads "not
recorded"; nothing here is filled in by inference.

Where each row's reader cell comes from. For 8a F0 to F5 and 8b W1 to W4 (ten rows) the reader cells
rest on the wave commits' message bodies and on the prose of `context/rung10-tier8-blueprint.md`;
no structured reader result file exists for those waves. For Tier 9 W1 and W2 and Tier 9c W3a to
W3d (six rows) the reader cells rest on structured reader result files.

Column key. "Reader verdicts" gives the two readers' verdict words with their blocker, major and
(where recorded) minor counts. "Gates" is the number of `#print axioms` entries in the ledger at that
wave's commit, all on exactly `propext`, `Classical.choice`, `Quot.sound`, as the gate printed it.
"Kernel replay" is the result of re-checking the modules through the toolchain's `leanchecker`, as
recorded in `leanchecker-replay-2026-09-12.md`, `leanchecker-replay-2026-09-13-tier9.md` and
`leanchecker-replay-2026-09-13-tier9c.md`. "Commit" is the short hash of the wave commit.

| Wave | Date | Reader verdicts | Gates | Kernel replay | Commit |
|---|---|---|---|---|---|
| 8a F0, the forced trap | 2026-09-09 | both CLEAN; 0 blockers, 0 majors | 190 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | 2df651e |
| 8a F1, the forced Galerkin layer | 2026-09-09 | both CLEAN; 0 blockers, 0 majors | 199 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | b25367e |
| 8a F2, the forced Galerkin flow | 2026-09-09 | both CLEAN; 0 blockers, 0 majors | 208 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | a9ee93d |
| 8a F3, the forced Theorem B (with the two F4 capstones) | 2026-09-09 | both CLEAN; 0 blockers, 0 majors | 215 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | eda7da6 |
| 8a F4, the breakdown-threshold corollaries | 2026-09-09 | both CLEAN; 0 blockers, 0 majors (commit body) | 217 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | 01a17cf |
| 8a F5, capstone-level certificates and prose | 2026-09-09 | shape reader CLEAN on the probe file; claim-wording reader on the prose: 5 majors (all wording), fixed before the commit; no proof-and-pin reader (commit body) | 226 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | 2a4036b |
| 8b W1, time-smoothness | 2026-09-09 | both CLEAN; 0 blockers, 0 majors | 251 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | 0efba80 |
| 8b W2, joint smoothness on the closed slab | 2026-09-09 | both CLEAN; 0 blockers, 0 majors | 265 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | e5a8755 |
| 8b W3, the community class, part 1 | 2026-09-09 | both CLEAN; 0 blockers, 0 majors | 283 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | ade27c8 |
| 8b W4, the community class inhabited | 2026-09-12 | both CLEAN; 0 blockers, 0 majors (a third, wording reader also ran) | 294 | 60 of 60 modules exit 0 (whole-tree run of 12 Sep 2026) | d59ddcd |
| 9 W1, the datum bridge | 2026-09-13 | shape reader FINDINGS (0 blockers, 0 majors, 3 minors); proof reader CLEAN (0, 0, 2 minors) | 339 | `Descent`, `DatumBridge`: exit 0, empty output | ffb8406 |
| 9 W2, the mean and the capstone | 2026-09-13 | shape reader CLEAN (0, 0, 4 minors); proof reader CLEAN (0, 0, 5 minors) | 391 | `Galilean`, `CommunityData`: exit 0, empty output | 332790f |
| 9c W3a, the descent side | 2026-09-13 | proof reader CLEAN (0, 0, 3 minors); shape reader FINDINGS (0, 0, 6 minors) | 421 | `SliceExtract`, `ConvectionCoeff`, `ClassParseval`: exit 0, empty output | 2ea0d9c |
| 9c W3b, the time side | 2026-09-13 | proof reader CLEAN (0, 0, 5 minors); shape reader CLEAN (0, 0, 4 minors) | 444 | `ClassFlowODE`: exit 0, empty output | 43a0b29 |
| 9c W3c, the capstones | 2026-09-13 | shape reader CLEAN (0, 0, 3 minors); proof reader FINDINGS (0, 0, 3 minors) | 474 | `CommunityUnique`: exit 0, empty output | 68e12d2 |
| 9c W3d, the general-mean addendum | 2026-09-13 | shape reader CLEAN (0, 0, 5 minors); proof reader CLEAN (0, 0, 3 minors) | 484 | `GeneralMean`: exit 0, empty output | b402d9a |

Notes on cells.

- FINDINGS is the reader's own verdict word. In every row where it appears the recorded blocker and
  major lists are empty, so the findings were minor items (wording, docstrings, observations).
- For 8a F5 the commit body records a statement-shape reader on the probe file (CLEAN) and a
  claim-wording reader on the prose (five majors, all wording, all fixed before the commit); it
  records no proof-and-pin reader. F5 is the one wave whose two readers differ from the others.
- Majors raised by claim-wording readers on the prose were fixed before the commit in 8a F5 (five,
  all wording) and 8b W4 (one, a stale line count). None was recorded against the statements or
  proofs by the shape and proof readers.
- For 8a F2 the two flagged docstring overclaims were corrected in the follow-up commit `e30a41d`,
  not in `a9ee93d`, although the message of `a9ee93d` said they were fixed there.
- For Tiers 8a and 8b the replay was made once for the whole tree after the wave commits (at commit
  5dfce7a, 60 imported modules), not wave by wave. The Tier 9 and Tier 9c replays were made per
  module after the wave commit (the Tier 9 W1 modules `Descent` and `DatumBridge` at the W2 commit
  `332790f`). Both records say the Tier 9 and Tier 9c replays were run by the orchestrating
  session, not by an independent verifier, unlike the 12 Sep 2026 run. The umbrella module `TheoremB` itself could not be replayed
  (the checker was killed for memory), as `leanchecker-replay-2026-09-12.md` records.
- No blocker was recorded by the shape or proof reader of any of the 16 waves. For 8a and 8b that
  rests on commit messages and blueprint prose, not on raw reader reports; F5's readers were a
  shape reader and a claim-wording reader. An earlier, separate
  post-tag audit of Tiers 6 and 7 (2 Sep 2026) did find blockers; they were fixed in commit 82a9ab6,
  whose subject says "two blockers". That audit is not a wave row because it reviewed work that had
  already been tagged.

## How to read this

A "reader" was a Claude agent, run as a Claude Code subagent, given a finished wave and told to attack
it: one reader on statement shape and vacuity (does the theorem say what the prose says, is it
satisfiable, can a cheap witness inhabit it), one on the proofs and the pinned dependencies (in 8a
F5, a shape reader and a claim-wording reader instead). Where the records say so, the readers re-ran the gate and
wrote probe files against the tree. For every wave except F5 the commit messages state that the
frozen statements were byte-identical to the blueprint; they say who checked it (builder, readers,
orchestrator) only for some waves. For F5 the commit body records the gate run by the readers but
no byte-identity check. The readers were Claude
agents and not human experts: no human with expertise in the mathematics took part in these reviews, and the author, who is not a professional mathematician,
read the reports but did not replace the readers. The raw reports and probes are not published,
because they carry local machine details; this digest keeps only the verdicts and counts. Treat the
reader columns as a record of a process, not as independent evidence of correctness.

What an outsider can check without trusting any of this: run `scripts/check_axioms.sh`, which rebuilds
the library and prints `GATE: GREEN (484/484)` only if every ledger entry rests on exactly the three
standard axioms, and `scripts/check_tags.sh`, which prints `TAGS: GREEN` only if every frozen capstone
statement is identical at its tag and at the current tree and each tag's ledger count matches. The
kernel replay is reproducible with `scripts/replay_leanchecker.sh`. Those scripts and the Lean kernel,
not the readers, are the checks.
