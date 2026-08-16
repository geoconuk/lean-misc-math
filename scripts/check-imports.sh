#!/usr/bin/env bash
# Every module under MiscMath/ must be reachable from the root MiscMath.lean.
#
# The axiom audit in MiscMath/Audit.lean can only see declarations that are
# transitively imported. A file that nobody imports would still be compiled (the
# lean_lib globs everything) but would escape the audit entirely. This script closes
# that gap, and also flags imports left behind by a deleted file.
#
# Reachability is transitive, not direct. A result may be split across several modules
# — a roof module carrying the statements and its supporting modules underneath — and
# only the roof needs naming in MiscMath.lean; the audit sees the rest through it. The
# modules the root names directly are the *result modules*, and they are what
# check-conventions.sh holds to the documentation conventions.
set -euo pipefail
cd "$(dirname "$0")/.."

root="MiscMath.lean"
status=0

# The MiscMath modules a given file imports.
imports_of() {
  grep -oE '^import[[:space:]]+MiscMath\.[A-Za-z0-9_.]+' "$1" | awk '{print $2}' || true
}

# Modules that are infrastructure, not library content, and so are not expected to be
# reachable from the root.
is_exempt() {
  case "$1" in
    MiscMath.Audit | MiscMath.Meta.*) return 0 ;;
    *) return 1 ;;
  esac
}

# Transitive closure of the root's imports, to a fixpoint.
reachable="$(imports_of "$root" | sort -u)"
while :; do
  next="$reachable"
  for module in $reachable; do
    file="$(printf '%s' "$module" | tr '.' '/').lean"
    if [[ -f "$file" ]]; then
      next="$next
$(imports_of "$file")"
    fi
  done
  next="$(printf '%s\n' $next | sort -u)"
  if [[ "$next" == "$reachable" ]]; then
    break
  fi
  reachable="$next"
done

module_is_reachable() {
  for module in $reachable; do
    if [[ "$module" == "$1" ]]; then
      return 0
    fi
  done
  return 1
}

while IFS= read -r file; do
  # MiscMath/Foo/Bar.lean -> MiscMath.Foo.Bar
  module="$(printf '%s' "${file%.lean}" | tr '/' '.')"
  if is_exempt "$module"; then
    continue
  fi
  if ! module_is_reachable "$module"; then
    echo "error: $file is not reachable from $root"
    echo "    import it from $root, or from a module that is"
    status=1
  fi
done < <(find MiscMath -name '*.lean' | sort)

# And the reverse: no import anywhere pointing at a file that no longer exists.
for module in $reachable; do
  file="$(printf '%s' "$module" | tr '.' '/').lean"
  if [[ ! -f "$file" ]]; then
    echo "error: $module is imported but $file does not exist"
    status=1
  fi
done

if [[ $status -eq 0 ]]; then
  echo "import check passed: every module under MiscMath/ is reachable from $root"
fi
exit $status
