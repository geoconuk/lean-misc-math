#!/usr/bin/env bash
# Does the axiom audit actually reject anything?
#
# An audit that silently passes everything is worse than no audit at all, and that is a
# realistic failure mode: `#audit_axioms` reads `env.header.moduleData`, so a change in
# Lean's internals could leave it iterating over an empty array and reporting success
# for zero declarations. Nothing else in CI would notice.
#
# This script plants a deliberately unsound module, builds an audit over it, and fails
# if the audit does *not* reject it.
set -euo pipefail
cd "$(dirname "$0")/.."

dir="MiscMath/SelfTest"
cleanup() { rm -rf "$dir"; }
trap cleanup EXIT
cleanup
mkdir -p "$dir"

cat > "$dir/Planted.lean" <<'LEAN'
-- Planted by scripts/self-test-audit.sh. Deleted when it finishes.
theorem planted_sorry : 2 + 2 = 5 := by sorry
LEAN

cat > "$dir/Audit.lean" <<'LEAN'
-- Planted by scripts/self-test-audit.sh. Deleted when it finishes.
import MiscMath.SelfTest.Planted
import MiscMath.Meta.AxiomAudit
#audit_axioms
LEAN

echo "self-test: building an audit over a module containing 'sorry' (expected to FAIL)"
output="$(lake build MiscMath.SelfTest.Audit 2>&1 || true)"

if grep -q "axiom audit FAILED" <<<"$output"; then
  if grep -q "sorryAx" <<<"$output"; then
    echo "self-test passed: the audit rejected the planted sorry"
    exit 0
  fi
  echo "self-test FAILED: the audit rejected the module but did not name sorryAx"
else
  echo "self-test FAILED: the audit did not reject a module containing 'sorry'."
  echo "The audit may have silently stopped inspecting declarations. Do not trust a"
  echo "green build until this is understood."
fi

echo "--- build output ---"
printf '%s\n' "$output"
exit 1
