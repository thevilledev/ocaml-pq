#!/bin/sh
# Check every formal artifact: build the Lean proofs, reject incomplete
# proofs, print the axioms the headline theorems depend on, and model-check
# the TLA+ specifications.
#
# Requirements: elan (Lean toolchain from formal/lean/lean-toolchain), a
# Java runtime, and tla2tools.jar (set TLA2TOOLS, or place it in formal/tla).
set -eu

here=$(cd "$(dirname "$0")" && pwd)

echo "== Lean: fetching the prebuilt Mathlib cache"
(cd "$here/lean" && lake exe cache get)

echo "== Lean: rejecting sorry, admit, and new axioms"
if grep -rnwE 'sorry|admit' "$here/lean/OcamlPq" "$here/lean/OcamlPq.lean" ||
   grep -rnE '^[[:space:]]*axiom[[:space:]]' "$here/lean/OcamlPq" "$here/lean/OcamlPq.lean"; then
  echo "incomplete proof or new axiom found" >&2
  exit 1
fi

echo "== Lean: building all proofs"
(cd "$here/lean" && lake build OcamlPq)

echo "== Lean: axioms used by the headline theorems"
audit=$(cd "$here/lean" && lake env lean OcamlPq/Audit.lean 2>&1)
printf '%s\n' "$audit"
# Only Lean's standard axioms may appear. sorryAx would reveal an incomplete
# proof, Lean.ofReduceBool a native_decide or bv_decide proof.
unexpected=$(printf '%s\n' "$audit" | sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' |
  tr ',' '\n' | tr -d ' ' | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$unexpected" ] || printf '%s\n' "$audit" | grep -qE ':[0-9]+:[0-9]+: error'; then
  echo "unexpected axioms or errors in the audit: $unexpected" >&2
  exit 1
fi

echo "== TLA+: model checking"
sh "$here/tla/check.sh"

echo "All formal checks passed."
