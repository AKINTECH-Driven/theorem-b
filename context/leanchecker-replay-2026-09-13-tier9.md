# Kernel replay through the toolchain's `leanchecker`: the four Tier 9 modules (13 Sep 2026)

Run at commit `332790f` (tag `t9-complete`), toolchain `leanprover/lean4:v4.31.0-rc2`,
checker the toolchain's own `bin/leanchecker` (the binary
that ships inside the toolchain; nothing cloned, built or installed), on the same 16 GiB
machine as the 12 Sep 2026 run recorded in `leanchecker-replay-2026-09-12.md`. Command per
module: `lake env leanchecker <module>` from the repository root, sequentially, exactly as
`scripts/replay_leanchecker.sh` does per module.

| Module | exit | seconds (wall) | output bytes |
|---|---|---|---|
| `TheoremB.Descent` | 0 | 5 | 0 |
| `TheoremB.DatumBridge` | 0 | 5 | 0 |
| `TheoremB.Galilean` | 0 | 5 | 0 |
| `TheoremB.CommunityData` | 0 | 5 | 0 |

What this establishes: every declaration of the four modules added by Tier 9 (waves W1 and
W2, commits `ffb8406` and `332790f`) is re-checked by the Lean kernel, through the
toolchain's own checker, from the environment provided by the modules they import. Those
imports are among the 60 modules replayed on 12 Sep 2026 at `5dfce7a`; no Lean file of the
tree other than the four new ones and the two registration files (`TheoremB.lean`,
`AxiomCheck.lean`, import and `#print axioms` lines only) changed between `5dfce7a` and
`332790f`, so the 12 Sep replay of the imports stands.

What it does not establish, as on 12 Sep: the imports are not replayed again in this run
(no `--fresh`); the toolchain's own checker is not an external verifier; the umbrella module
`TheoremB` (imports only, no declarations of its own) and `AxiomCheck.lean` (the gate runs
it) are not replayed. The wall time of 5 s per module is consistent with the 12 Sep record
(its independent verifier measured 5 to 6 s per module with a warm file cache; its table
shows modules of comparable size at 5 to 9 s). A bogus module name makes the checker exit 1
(checked; the exit code is persisted as `audit-tier9/replay/bogus-module-check.txt` in the
session directory), so an empty log with exit 0 is a pass, not a no-op.

Run by the orchestrating session of Tier 9, not by an independent verifier (the 12 Sep run
had one); the per-module logs, `replay.tsv` and `env.txt` are persisted in the session
directory `audit-tier9/replay/`.
