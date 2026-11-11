# Kernel replay through `leanchecker`, 12 Sep 2026

Run at commit `5dfce7a` (the tree of tag `t8b-community-green` plus the dossier
commit), toolchain `leanprover/lean4:v4.31.0-rc2`, checker
the toolchain's own `bin/leanchecker` (the
checker that ships inside every Lean toolchain from v4.28.0; nothing was
cloned, built or installed), by `scripts/replay_leanchecker.sh`, on a 16 GiB machine with
10 cores. Started 2026-09-12T20:36:20Z; the summed
per-module checker time is 2,357 s (about 39 minutes of wall clock).

What one line means: `lake env leanchecker <module>` re-checks every
declaration of that module with the Lean kernel, starting from the
environment supplied by the module's imports (the imports themselves are not
replayed; no `--fresh` run was made, so Mathlib and each module's upstream
oleans are trusted as loaded). Success is silent: exit 0 and no output.
`leanchecker` is the toolchain's own checker, not an external verifier.

Result: all 60 imported modules of `TheoremB.lean` replayed with exit 0 and
empty output. An independent verifier (a second agent) re-derived the module
list from `TheoremB.lean`, checked the table for coverage (60 of 60, no
duplicate, no extra), found every log empty, and re-ran three modules itself
(`TheoremB.RiccatiTrap`, `TheoremB.JointSmooth`, `TheoremB.CommunityClass`:
exit 0, empty output, 5 to 6 s each with a warm file cache).

The umbrella module `TheoremB` (imports only; it declares nothing) was ALSO
attempted, twice, and both attempts ended with exit 137: the macOS memory
watchdog killed the checker at about 23 GB of compressed footprint
(`memorystatus: killing largest compressed process leanchecker [10465]
23322 MB` at 00:15:36 EEST; `[11331] 22800 MB` at 00:18:30 EEST on the
verifier's re-run). Nothing was printed before the kill, so no declaration was
reported bad; the environment-union load that this 61st entry represents did
not complete on this machine and is not claimed. Since the umbrella module
contributes no declaration of its own, the script now skips it by default
(`REPLAY_ROOT=1` includes it on a larger machine). The per-module table:

| Module | exit | seconds |
|---|---|---|
| `TheoremB.RiccatiTrap` | 0 | 36 |
| `TheoremB.SpectralNorms` | 0 | 9 |
| `TheoremB.ConditionalTheoremB` | 0 | 5 |
| `TheoremB.FourierDeriv` | 0 | 5 |
| `TheoremB.GalerkinTrap` | 0 | 56 |
| `TheoremB.NSGalerkin` | 0 | 106 |
| `TheoremB.RealityProp` | 0 | 104 |
| `TheoremB.GalerkinLocal` | 0 | 95 |
| `TheoremB.GalerkinFlow` | 0 | 60 |
| `TheoremB.NSFull` | 0 | 63 |
| `TheoremB.ModeExtraction` | 0 | 105 |
| `TheoremB.FlowBounds` | 0 | 52 |
| `TheoremB.LimitPassage` | 0 | 17 |
| `TheoremB.LimitHelpers` | 0 | 15 |
| `TheoremB.ConvContinuity` | 0 | 30 |
| `TheoremB.TheoremBGlobal` | 0 | 46 |
| `TheoremB.LatticeKernel` | 0 | 27 |
| `TheoremB.DefectCalculus` | 0 | 135 |
| `TheoremB.PairingBound` | 0 | 48 |
| `TheoremB.TailBounds` | 0 | 46 |
| `TheoremB.FullUnique` | 0 | 17 |
| `TheoremB.TorusSynthesis` | 0 | 11 |
| `TheoremB.TorusStructure` | 0 | 6 |
| `TheoremB.SpectralWeak` | 0 | 5 |
| `TheoremB.CoeffExtract` | 0 | 65 |
| `TheoremB.TheoremBTorus` | 0 | 63 |
| `TheoremB.PhysicalPairing` | 0 | 63 |
| `TheoremB.TestSeparation` | 0 | 58 |
| `TheoremB.LerayHopfVocab` | 0 | 53 |
| `TheoremB.SobolevNorms` | 0 | 70 |
| `TheoremB.SobolevPairing` | 0 | 64 |
| `TheoremB.SobolevTrap` | 0 | 60 |
| `TheoremB.TheoremBSobolev` | 0 | 54 |
| `TheoremB.ContinuousRep` | 0 | 54 |
| `TheoremB.PeriodicLift` | 0 | 58 |
| `TheoremB.TimeLayer` | 0 | 87 |
| `TheoremB.Calibration` | 0 | 50 |
| `TheoremB.Nonlinearity` | 0 | 92 |
| `TheoremB.TheoremBSmooth` | 0 | 89 |
| `TheoremB.ClassicalEquation` | 0 | 36 |
| `TheoremB.EnergyDecay` | 0 | 25 |
| `TheoremB.Bandwidth` | 0 | 12 |
| `TheoremB.WindowDecay` | 0 | 7 |
| `TheoremB.EnergyIntegrable` | 0 | 16 |
| `TheoremB.ModesWindow` | 0 | 7 |
| `TheoremB.DeterminingModes` | 0 | 5 |
| `TheoremB.ModesFlow` | 0 | 12 |
| `TheoremB.ModesProbe` | 0 | 7 |
| `TheoremB.GalerkinDecay` | 0 | 7 |
| `TheoremB.DecayFlow` | 0 | 6 |
| `TheoremB.ForcedTrap` | 0 | 9 |
| `TheoremB.ForcedGalerkin` | 0 | 8 |
| `TheoremB.ForcedGalerkinFlow` | 0 | 6 |
| `TheoremB.ForcedTheoremB` | 0 | 5 |
| `TheoremB.ForcedUnique` | 0 | 6 |
| `TheoremB.ForcedProbe` | 0 | 6 |
| `TheoremB.TimeSmooth` | 0 | 5 |
| `TheoremB.WithinSeries` | 0 | 5 |
| `TheoremB.JointSmooth` | 0 | 6 |
| `TheoremB.CommunityClass` | 0 | 9 |
| `TheoremB` | 137 | 73 |

Evidence outside the tree (session audit directory, `audit-tier8b/leanchecker/`):
`run1/replay.tsv`, `run1/env.txt`, the 61 per-module logs (all empty),
`verify/` with the verifier's expected list, its three re-runs, the umbrella
re-run under `/usr/bin/time -l`, and the kernel-log excerpt.
