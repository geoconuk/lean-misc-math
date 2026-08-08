#!/usr/bin/env bash
# Every result module must be imported by the root MiscMath.lean.
#
# The axiom audit in MiscMath/Audit.lean can only see declarations that are
# transitively imported. A result file that nobody imports would still be compiled
# (the lean_lib globs everything) but would escape the audit entirely. This script
# closes that gap, and also flags imports left behind by a deleted file.
set -euo pipefail
cd "$(dirname "$0")/.."

root="MiscMath.lean"
status=0

# Modules that are infrastructure, not results, and so are not expected in the root.
is_exempt() {
  case "$1" in
    MiscMath.Audit | MiscMath.Meta.*) return 0 ;;
    *) return 1 ;;
  esac
}

while IFS= read -r file; do
  # MiscMath/Foo/Bar.lean -> MiscMath.Foo.Bar
  module="$(printf '%s' "${file%.lean}" | tr '/' '.')"
  if is_exempt "$module"; then
    continue
  fi
  if ! grep -qE "^import[[:space:]]+${module}[[:space:]]*$" "$root"; then
    echo "error: $file is not imported by $root (expected line: 'import $module')"
    status=1
  fi
done < <(find MiscMath -name '*.lean' | sort)

# And the reverse: no imports in the root pointing at files that no longer exist.
while IFS= read -r module; do
  file="$(printf '%s' "$module" | tr '.' '/').lean"
  if [[ ! -f "$file" ]]; then
    echo "error: $root imports $module but $file does not exist"
    status=1
  fi
done < <(grep -oE '^import[[:space:]]+MiscMath\.[A-Za-z0-9_.]+' "$root" | awk '{print $2}')

if [[ $status -eq 0 ]]; then
  echo "import check passed: $root imports every result module"
fi
exit $status
