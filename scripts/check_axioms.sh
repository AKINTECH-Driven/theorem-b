#!/usr/bin/env bash
set -euo pipefail

# check_axioms.sh: deterministic acceptance gate for the Theorem B campaign.
# Grant-guard for mathematics.  PASS (GREEN) if and only if:
#   1. the project and AxiomCheck.lean compile, and
#   2. no audited theorem depends on sorryAx, and
#   3. no audited theorem depends on any axiom outside the standard kernel
#      three: propext, Classical.choice, Quot.sound, and
#   4. the audited entries are exactly the `#print axioms` lines of
#      AxiomCheck.lean, by count and by name (entries Lean wraps over several
#      lines are joined before they are read; a truncated list is RED).
# Anything else is RED.  This script reports; it never repairs.

cd "$(dirname "$0")/.."

echo "== build =="
lake build 2>&1 | tail -5 || { echo "GATE: RED (lake build failed)"; exit 1; }

echo "== axiom audit =="
OUT="$(lake env lean AxiomCheck.lean 2>&1)" || {
  echo "$OUT"
  echo "GATE: RED (AxiomCheck failed to compile)"
  exit 1
}
OUT="${OUT//$'\r'/}"   # no carriage returns in what is read below
echo "$OUT"

if grep -q "sorryAx" <<<"$OUT"; then
  echo "GATE: RED (sorryAx present: unproved sorry in a dependency cone)"
  exit 1
fi

# join Lean's wrapped output: a line that opens '[' without closing it absorbs the following lines
JOINED="$(printf '%s\n' "$OUT" | awk '
  buf != "" { buf = buf " " $0; if (index($0, "]")) { print buf; buf = "" }; next }
  /\[/ && !/\]/ { buf = $0; next }
  { print }
  END { if (buf != "") print buf }')"

EXPECTED="$(grep -c '^#print axioms' AxiomCheck.lean || true)"
if [ "$EXPECTED" = "0" ]; then
  echo "GATE: RED (no #print axioms entries in AxiomCheck.lean)"
  exit 1
fi

# an entry is either "'NAME' depends on axioms: [...]" or "'NAME' does not depend on any axioms"
ENTRY_LINES="$(printf '%s\n' "$JOINED" | grep -E "depends on axioms: \[|does not depend on any axioms" || true)"
ENTRIES="$(printf '%s\n' "$ENTRY_LINES" | grep -c . || true)"
if [ "$ENTRIES" != "$EXPECTED" ]; then
  echo "GATE: RED (expected $EXPECTED axiom entries, found $ENTRIES)"
  exit 1
fi

# every axiom list must be closed and must end its line (a truncated list, or text after
# the closing bracket, could hide an axiom)
OPEN="$(printf '%s\n' "$ENTRY_LINES" | grep 'depends on axioms: \[' | grep -v '\][[:space:]]*$' || true)"
if [ -n "$OPEN" ]; then
  echo "GATE: RED (malformed axiom list in the output)"
  exit 1
fi

# the audited names must be exactly the ledger's names (a repeated entry cannot stand in for a missing one)
WANT="$(grep '^#print axioms' AxiomCheck.lean | awk '{print $3}' | sort)"
HAVE="$(printf '%s\n' "$ENTRY_LINES" \
  | sed -n -e "s/^'\(.*\)' depends on axioms: .*/\1/p" -e "s/^'\(.*\)' does not depend on any axioms.*/\1/p" | sort)"
if [ "$WANT" != "$HAVE" ]; then
  echo "GATE: RED (the audited names differ from the ledger in AxiomCheck.lean)"
  exit 1
fi

# axioms are read from the entry lines only
BAD="$(printf '%s\n' "$ENTRY_LINES" \
  | grep -o '\[[^]]*\]' \
  | tr -d '[]' | tr ',' '\n' | sed 's/^ *//; s/ *$//' | sort -u \
  | grep -v -e '^propext$' -e '^Classical\.choice$' -e '^Quot\.sound$' -e '^$' \
  || true)"

if [ -n "$BAD" ]; then
  echo "GATE: RED (unexpected axioms: $BAD)"
  exit 1
fi

echo "GATE: GREEN ($ENTRIES/$EXPECTED)"
