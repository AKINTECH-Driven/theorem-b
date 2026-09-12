#!/usr/bin/env bash
# replay_leanchecker.sh: independent kernel replay of every module of the Theorem B
# campaign through the toolchain's own `leanchecker` (shipped with Lean >= v4.28.0).
#
# For each module imported by TheoremB.lean runs
#   lake env leanchecker <module>
# which re-checks every declaration of that module with the Lean kernel, starting
# from the environment provided by its imports (the imports are not replayed;
# pass --fresh yourself for a single module if you want that, it is single-threaded
# and slow). Writes one TSV line per module: module, exit code, seconds, output size.
# Exit status: 0 iff every module replayed with exit 0. This script reports; it
# never repairs.
#
# The umbrella module TheoremB (imports only, no declarations of its own) is NOT
# replayed by default: it adds no declaration to check, and on a 16 GiB Mac its
# replay was killed twice by the kernel's memory watchdog at about 23 GB compressed
# footprint (12 Sep 2026, context/leanchecker-replay-2026-09-12.md). Set
# REPLAY_ROOT=1 to include it on a larger machine.
#
# Usage: [REPLAY_ROOT=1] bash scripts/replay_leanchecker.sh [outdir]   (default outdir: .lake/leanchecker)
set -uo pipefail
cd "$(dirname "$0")/.."
OUT="${1:-.lake/leanchecker}"
mkdir -p "$OUT"
TSV="$OUT/replay.tsv"
: > "$TSV"
echo "toolchain: $(cat lean-toolchain)" > "$OUT/env.txt"
echo "leanchecker: $(lake env which leanchecker)" >> "$OUT/env.txt"
echo "commit: $(git rev-parse HEAD 2>/dev/null)" >> "$OUT/env.txt"
echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$OUT/env.txt"
MODULES="$(grep -E '^import TheoremB\.' TheoremB.lean | sed 's/^import //')"
if [ "${REPLAY_ROOT:-0}" = "1" ]; then MODULES="$MODULES TheoremB"; fi
FAIL=0; N=0
for m in $MODULES; do
  N=$((N+1))
  S=$(date +%s)
  lake env leanchecker "$m" > "$OUT/$m.log" 2>&1
  RC=$?
  E=$(( $(date +%s) - S ))
  SZ=$(wc -c < "$OUT/$m.log" | tr -d ' ')
  printf '%s\t%s\t%s\t%s\n' "$m" "$RC" "$E" "$SZ" >> "$TSV"
  if [ "$RC" != "0" ]; then FAIL=$((FAIL+1)); fi
done
echo "modules: $N failed: $FAIL" | tee -a "$OUT/env.txt"
if [ "$FAIL" = "0" ]; then echo "REPLAY: GREEN ($N modules)"; exit 0; else echo "REPLAY: RED ($FAIL of $N modules failed)"; exit 1; fi
