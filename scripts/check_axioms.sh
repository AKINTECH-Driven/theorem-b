#!/usr/bin/env bash
set -euo pipefail

# check_axioms.sh: deterministic acceptance gate for the Theorem B campaign.
# Grant-guard for mathematics.  PASS (GREEN) if and only if:
#   1. the project and AxiomCheck.lean compile, and
#   2. no audited theorem depends on sorryAx, and
#   3. no audited theorem depends on any axiom outside the standard kernel
#      three: propext, Classical.choice, Quot.sound.
# Anything else is RED.  This script reports; it never repairs.

cd "$(dirname "$0")/.."

echo "== build =="
lake build 2>&1 | tail -5

echo "== axiom audit =="
OUT="$(lake env lean AxiomCheck.lean 2>&1)" || {
  echo "$OUT"
  echo "GATE: RED (AxiomCheck failed to compile)"
  exit 1
}
echo "$OUT"

if echo "$OUT" | grep -q "sorryAx"; then
  echo "GATE: RED (sorryAx present: unproved sorry in a dependency cone)"
  exit 1
fi

BAD="$(echo "$OUT" \
  | grep -o '\[[^]]*\]' \
  | tr -d '[]' | tr ',' '\n' | sed 's/^ *//; s/ *$//' | sort -u \
  | grep -v -e '^propext$' -e '^Classical\.choice$' -e '^Quot\.sound$' -e '^$' \
  || true)"

if [ -n "$BAD" ]; then
  echo "GATE: RED (unexpected axioms: $BAD)"
  exit 1
fi

echo "GATE: GREEN"
