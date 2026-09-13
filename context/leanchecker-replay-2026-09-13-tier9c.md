# Kernel replay through the toolchain's `leanchecker`: the five Tier 9c modules (13 Sep 2026)

Run at the wave commits of Tier 9c, toolchain `leanprover/lean4:v4.31.0-rc2`, checker
`~/.elan/toolchains/leanprover--lean4---v4.31.0-rc2/bin/leanchecker` (the binary that ships
inside the toolchain; nothing cloned, built or installed), on the same 16 GiB machine as the
12 and 13 Sep 2026 runs recorded in `leanchecker-replay-2026-09-12.md` and
`leanchecker-replay-2026-09-13-tier9.md`. Command per module: `lake env leanchecker <module>`
from the repository root, sequentially, exactly as `scripts/replay_leanchecker.sh` does per
module; each run was made after the module's commit, while the following wave was building.

| Module | wave, commit | exit | seconds (wall) | output bytes |
|---|---|---|---|---|
| `TheoremB.SliceExtract` | W3a, `2ea0d9c` | 0 | 36 | 0 |
| `TheoremB.ConvectionCoeff` | W3a, `2ea0d9c` | 0 | 6 | 0 |
| `TheoremB.ClassParseval` | W3a, `2ea0d9c` | 0 | 18 | 0 |
| `TheoremB.ClassFlowODE` | W3b, `43a0b29` | 0 | 22 | 0 |
| `TheoremB.CommunityUnique` | W3c, `68e12d2` (tag `t9-unique-green`) | 0 | 125 | 0 |

What this establishes: every declaration of the five modules added by Tier 9c (waves W3a,
W3b and W3c) is re-checked by the Lean kernel, through the toolchain's own checker, from the
environment provided by the modules they import. Those imports are the 60 modules replayed
on 12 Sep 2026 at `5dfce7a` and the four Tier 9 modules replayed on 13 Sep 2026 at
`332790f`; no Lean file of the tree other than the five new ones and the two registration
files (`TheoremB.lean`, `AxiomCheck.lean`, import and `#print axioms` lines only) changed
between `332790f` and `68e12d2`, so the earlier replays of the imports stand. The wall times
differ from the Tier 9 record (5 s per module there) because a wave build was running
alongside each replay and `CommunityUnique` is the largest of the five; a bogus module name
makes the checker exit 1 (checked again in this run; `bogus-module-check.log` in the session
directory), so an empty log with exit 0 is a pass, not a no-op.

What it does not establish, as before: the imports are not replayed again in this run (no
`--fresh`); the toolchain's own checker is not an external verifier; the umbrella module
`TheoremB` (imports only, no declarations of its own) and `AxiomCheck.lean` (the gate runs
it) are not replayed.

Run by the orchestrating session of Tier 9c, not by an independent verifier; the per-module
logs and `SUMMARY.txt` are persisted in the session directory `audit-tier9c/replay/`.
