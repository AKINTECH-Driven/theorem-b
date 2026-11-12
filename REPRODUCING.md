# Reproducing the Theorem B build

This file says what a reproduction checks, which versions it needs, the exact steps with the
last line each one should print, what never to run, and what each check does not establish.
Numbers marked "estimate" are not measurements; numbers marked "measured" come from the runs
named beside them. See the README sections "Build and gate" and "Scope and non-claims" for
the claims themselves.

## 1. What reproduction means here

Three independent checks:

1. **The gate is GREEN.** `bash scripts/check_axioms.sh` builds the library, compiles
   `AxiomCheck.lean`, and prints `GATE: GREEN (484/484)`: every one of the 484 `#print axioms`
   entries depends on at most `propext`, `Classical.choice` and `Quot.sound`, none on `sorryAx`,
   and the number of entries read equals the number of lines in the ledger.
2. **Per-module kernel replay.** `bash scripts/replay_leanchecker.sh` re-checks every declaration
   of each of the 70 modules with the toolchain's own `leanchecker`, and prints
   `REPLAY: GREEN (70 modules)`.
3. **Frozen statement text is identical at its tag and at HEAD.** `bash scripts/check_tags.sh`
   compares the statement text of each frozen capstone at the tag that froze it and at HEAD
   (trailing whitespace on a line is ignored), and prints `TAGS: GREEN`.

None of the three says anything about whether the statements mean what the README says; that
is a question of review (the README states that no human domain expert has reviewed them).

## 2. The pin

| Item | Value |
|---|---|
| Toolchain | `leanprover/lean4:v4.31.0-rc2` (`lean-toolchain`) |
| Lake | ships in the toolchain (`Lake version 5.0.0-src+5e44d5f` at the audit) |
| Mathlib | `15a89b2468bc01f1a6230d6e49ef5efc5286e502` (`lakefile.toml`, `lake-manifest.json`) |
| plausible | `744117af710b1c0400cd297c9ce91f8d0ad3a347` |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | `99c763c8a96d3d44fb4994e96eaa51ca4568449d` |
| proofwidgets | `1537e3fc7e680d64e06fe5fb95c4c9edee7941c2` |
| aesop | `7897ea6e5cfc6522d355083bdfa798377ab35e11` |
| Qq | `94346b7b49c36ae871639d1434232f057c193d60` |
| batteries | `5dd219c775e402f818b42cd3997b5cf21017babf` |
| Cli | `baf3e62fbb3502305076ca077e004aea78157c63` |

Every package in `lake-manifest.json` carries a full `rev`, so `lake build` on a clone checks
out exactly these commits. The pinned Mathlib itself declares the same toolchain.

The toolchain is a **release candidate**. As of the audit of 20 Sep 2026, the release page
`https://github.com/leanprover/lean4/releases/tag/v4.31.0-rc2` served the assets
`lean-4.31.0-rc2-darwin_aarch64.tar.zst` and `lean-4.31.0-rc2-linux.tar.zst`; elan installs
either on the first `lake` call in the clone. Mathlib master has moved on (it was on
`v4.36.0-rc2` as checked on 11 Nov 2026); this repository stays on its pin, and moving either
component is a re-verification event.

**Mathlib cache.** As of 20 Sep 2026 the pinned commit's cache files were served from
`https://lakecache.blob.core.windows.net/mathlib4` (11 of 11 sampled `.ltar` files returned
HTTP 200, uploaded the night the commit landed). There is no written retention policy, so
availability is measured, not guaranteed. To re-check, take any file name from
`~/.cache/mathlib` after a `lake exe cache get` and request it:

```sh
curl -sI "https://lakecache.blob.core.windows.net/mathlib4/f/<name>.ltar" | head -1
```

## 3. Requirements

- OS: exercised on macOS arm64 (Apple M4, 10 cores, 16 GiB). Linux and the GitHub-hosted
  runner are untested at the time of writing (the first CI run is the first Linux record).
- RAM: 16 GB is the only class on record for `lake build`, the gate and the per-module replay.
- Disk: 12 GB measured, 20 GB recommended. Measured parts: toolchain 2.6 GB, Mathlib checkout
  with oleans 6.8 GB, other packages 0.7 GB, `.lake/build` of this library 0.44 GB, the
  downloaded `.ltar` cache 0.45 GB.
- Tools: `git`, `curl`, `bash` (macOS 3.2 and Linux 5 both work for the scripts), `elan`.

## 4. Steps

Run from a fresh clone. Times are for the 10-core M4 unless marked.

1. `git clone <repository> theorem-b && cd theorem-b` (checkout the tag you want to verify).
2. Pin self-check: `cat lean-toolchain` prints `leanprover/lean4:v4.31.0-rc2`, and
   `grep '"rev": "15a89b2468bc01f1a6230d6e49ef5efc5286e502"' lake-manifest.json` finds a line.
3. `lake exe cache get` fetches the Mathlib oleans (8,551 files, about 0.45 GB download, 7.9 GB
   unpacked; not timed). Last line: the cache tool's summary of unpacked files. Leave
   `MATHLIB_CACHE_USE_CLOUDFLARE` unset (section 5).
4. `lake build`. Measured twice in a fresh clone of the tracked tree (`.lake/packages` reused
   from an already-cached Mathlib pin, so the Mathlib cache download is not in these numbers),
   both times 8638 jobs, exit 0, zero errors, 46 warning lines. On 20 Sep 2026 at 1146a08:
   wall time 2294 s (38 min 14 s; user 454 s, sys 654 s), with seven audit agents sharing the
   machine. On 12 Nov 2026 at 7da07fd: wall time 2703 s (45 min 3 s; user 438 s, sys 583 s),
   with other agent sessions active for part of the run (resource use not measured). The
   second run took about 18% longer and the cause was not investigated, so no claim is made
   that either time bounds an idle-machine run. A 4-core CI runner is estimated at 1 to 3 hours.
5. `bash scripts/check_axioms.sh`. Last line: `GATE: GREEN (484/484)` (20 s on 12 Nov 2026,
   run once straight after the build). On a failed build the last line is
   `GATE: RED (lake build failed)`; any other RED
   line names the cause. The gate joins output lines that Lean wrapped before counting, counts an entry for both output
   forms (`depends on axioms: [...]` and `does not depend on any axioms`), requires the audited names to be
   exactly the ledger's names and every axiom list to be closed, and exits 0 on GREEN, 1 on RED.
6. Count recipe, to see the 484 independently of the gate:
   `grep -c '^#print axioms' AxiomCheck.lean` prints `484`. Do not count with a
   quote-delimited regular expression on the output: wrapped entries are missed that way.
7. `bash scripts/replay_leanchecker.sh`. Last line: `REPLAY: GREEN (70 modules)`. The 12 Sep
   record took about 39 minutes of wall clock for 60 modules (2,357 s summed); the 70-module
   run is estimated at 45 to 50 minutes. One TSV line and one log per module go to
   `.lake/leanchecker/`. If the toolchain has no `leanchecker` the script exits 2 at once.
8. `bash scripts/check_tags.sh`. Last line: `TAGS: GREEN`. Needs every tag present locally
   (`git fetch --tags`).

What `check_tags.sh` covers and does not cover: it checks the capstones of the README table
(the statement text from the declaration line to the line that ends with `:=` or `:= by`, at
the tag and at HEAD; a `:=` inside the statement, as in a named argument `(n := 3)`, does not
end it), and for eight tags that the ledger had the entry count the README ladder records. It
does not check all 484 ledger entries. Limits: (a) identical statement text does not mean
identical meaning, because the definitions a statement mentions (`en`, `ens`, `Vel`,
`RealField`, the community structures) are not compared; the axiom gate and the kernel replay
are the checks for that. (b) It reads HEAD, the committed state, not the working tree, so a run
before a commit does not test uncommitted edits. (c) 13 of the 31 tags that exist through
13 Sep 2026 are in its table; the other 18 are not checked. Six Lean files carry comment-only
publication notes added in v0.1.0 (`ClassicalEquation.lean`, `CommunityClass.lean`,
`CommunityData.lean`, `CommunityUnique.lean`, `LerayHopfVocab.lean`, `TheoremBSmooth.lean`),
so a whole-file hash of one of them differs from its tag although every statement is
unchanged; use `bash scripts/check_tags.sh`, or `git diff <tag> HEAD -- <file>`, which shows
comment lines only. The script reads each tag's tree, so the tags must be present locally (`git fetch --tags`); in
CI that means `fetch-depth: 0`. The gate counts it compares against are the README's.

## 5. Never

- `lake update`: it re-resolves and rewrites `lake-manifest.json`. The historical Tier 0 brief
  under `context/` still contains a build line with it; that file is a historical record, not
  instructions.
- `MATHLIB_CACHE_USE_CLOUDFLARE=1`: as of 20 Sep 2026 the Cloudflare mirror returned HTTP 404
  for this pin's files, while the default endpoint served them.
- `REPLAY_ROOT=1` under 32 GB of RAM: it adds the umbrella module `TheoremB` to the replay.
  That replay was killed twice by the memory watchdog at about 23 GB of compressed footprint on
  the 16 GiB Mac. For the umbrella replay, 32 GB or more is the guess, untested; it has never
  succeeded and is not claimed.
- Publishing or using a tarball of a working tree: use git only (`.lake/` can hold stale
  build artefacts that no clone sees).

## 6. What the replay does and does not establish

Copied in substance from the three replay records in `context/` (12 Sep, 13 Sep Tier 9, 13 Sep
Tier 9c):

- `lake env leanchecker <module>` re-checks every declaration of that module with the Lean
  kernel, starting from the environment supplied by the module's imports. Success is silent:
  exit 0 and no output. A bogus module name makes it exit 1, so an empty log with exit 0 is a
  pass, not a no-op.
- The imports themselves are not replayed; no `--fresh` run was made, so Mathlib and each
  module's upstream oleans are trusted as loaded.
- `leanchecker` is the toolchain's own checker, not an external verifier.
- The umbrella module `TheoremB` (imports only, no declarations of its own) and
  `AxiomCheck.lean` (the gate runs it) are not replayed.
- The records were produced on one 16 GiB Mac. The 12 Sep record was checked by a second agent;
  the two 13 Sep records were run by the orchestrating session, not by an independent verifier.
  The 12 Sep record covers 60 modules; today's script covers 70.

## 7. Known costs

- Four declarations carry `set_option maxHeartbeats 1000000 in` (`SobolevPairing.lean:110`,
  `Nonlinearity.lean:45` and `:285`, `PairingBound.lean:251`); they mark the
  elaboration-heavy proofs.
- The umbrella-module replay limit above.
- First compiles measured during the campaign: the largest recent modules took 36 to 46 s each.
  Kernel replay of the six Tier 9c modules took 275 s in total with a wave build running
  alongside. Estimates for a clean build and the replay are marked as estimates in section 4;
  the first CI run should replace them.
- The history through 13 Sep 2026 has 79 commits and 31 tags (17 lightweight, 14 annotated,
  none signed). Those older tags are verified by content (step 8), not by signature. Future
  tags should be signed with `git tag -s`; that is an action outside the tree.

## 8. The record

- The three replay records: `context/leanchecker-replay-2026-09-12.md`,
  `context/leanchecker-replay-2026-09-13-tier9.md`,
  `context/leanchecker-replay-2026-09-13-tier9c.md`.
- The workflow `.github/workflows/gate.yml` runs the build, the gate and the entry count on
  every push to `main`, every tag and every pull request, together with lean-action's own
  axiom audit (library root `TheoremB`, 483 of 484 entries) and Reservoir-eligibility check,
  the replay on tags and on demand, and the tag check. The URL of the first green run and the gate log of the release commit
  are to be added here after the first push.

## 9. Reporting a failure

Open an issue with: the operating system and CPU, RAM, `lean --version`, `df -h` before and
after, the last 40 lines of the failing step, and the full gate log (`bash scripts/check_axioms.sh
| tee gate.log`).
