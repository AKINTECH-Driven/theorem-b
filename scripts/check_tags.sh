#!/usr/bin/env bash
# check_tags.sh: every frozen capstone is byte-identical (statement text) at HEAD and at the tag
# that froze it, and every tag's ledger has the entry count the README records for it.
# Reports; never repairs. Exit 0 iff every check passes.
set -uo pipefail
cd "$(dirname "$0")/.."
OUT="$(mktemp)"

# tag  gate-count-at-tag  capstone names frozen by that tag (README "Build and gate" and "Capstone theorems")
TABLE='
t3-theorem-b-green      -    theorem_B
t4-wellposedness-green  -    theorem_B_unique ns_full_global_flow
t5-torus-green          -    theorem_B_torus theorem_B_torus_unique
t6-sobolev-green        -    theorem_B_sobolev ns_full_global_flow_sobolev
t6-classical-green      -    theorem_B_smooth_classical
t7-audited-green        186  theorem_B_smooth_classical_eq ns_full_global_flow_decay theorem_B_bandwidth theorem_B_modes ns_full_global_flow_modes
t8a-complete            226  theorem_B_forced theorem_B_unique_forced ns_full_global_flow_forced forced_breakdown_threshold
t8b-time-smooth-green   251  theorem_B_time_smooth
t8b-joint-smooth-green  265  theorem_B_joint_smooth
t8b-community-green     294  theorem_B_community_periodic_flow theorem_B_community_periodic
t9-datum-bridge-green   339  datum_bridge
t9-complete             391  theorem_B_community_periodic_data theorem_B_community_periodic_data_flow
t9-unique-green         474  community_unique_velocity community_unique_pressure
'

# statement text of declaration $2 in tree-ish $1: from "theorem <name>" to the line that ENDS with ":=" or
# ":= by", which opens the body (a ":=" inside the statement, as in a named argument "(n := 3)", does not end it)
stmt() {
  local rev="$1" name="$2" path
  path="$(git grep -l -E "^(theorem|lemma|noncomputable def|def) $name([[:space:]]|$)" "$rev" -- TheoremB | head -1 | cut -d: -f2-)"
  [ -n "$path" ] || { echo "MISSING $name at $rev"; return 1; }
  git show "$rev:$path" | awk -v n="$name" '
    !on && $0 ~ ("^(theorem|lemma|noncomputable def|def) " n "([[:space:]]|$)") { on = 1 }
    on { line = $0; sub(/[[:space:]]+$/, "", line); print line; if (line ~ /:=([[:space:]]*by)?$/) exit }'
}

echo "$TABLE" | while read -r tag count names; do
  [ -n "$tag" ] || continue
  git rev-parse -q --verify "refs/tags/$tag" >/dev/null || { echo "FAIL no tag $tag"; continue; }
  kind="$(git cat-file -t "$tag")"
  if [ "$count" != "-" ]; then
    have="$(git show "$tag:AxiomCheck.lean" | grep -c '^#print axioms')"
    [ "$have" = "$count" ] && echo "ok   $tag ledger $have" || echo "FAIL $tag ledger $have expected $count"
  fi
  for n in $names; do
    if diff <(stmt "$tag" "$n") <(stmt HEAD "$n") >/dev/null; then
      echo "ok   $tag ($kind) $n byte-identical at HEAD"
    else
      echo "FAIL $tag ($kind) $n differs between tag and HEAD"
    fi
  done
done | tee "$OUT"
FAILS="$(grep -c '^FAIL' "$OUT" || true)"; rm -f "$OUT"
[ "$FAILS" = "0" ] && { echo "TAGS: GREEN"; exit 0; } || { echo "TAGS: RED ($FAILS failures)"; exit 1; }
