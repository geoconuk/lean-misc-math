#!/usr/bin/env bash
# Every module under MiscMath/ must be reachable from the root MiscMath.lean, and named by
# an `import all` in MiscMath/Audit.lean.
#
# The axiom audit in MiscMath/Audit.lean can only see declarations that are imported. A
# file that nobody imports would still be compiled (the lean_lib globs everything) but
# would escape the audit entirely. This script closes that gap, and also flags imports left
# behind by a deleted file.
#
# Under Lean's module system reachability is not enough for the audit. A plain import shows
# only a module's public declarations, and `import all` shows its private ones as well, but
# only for the module it names: it does not reach through that module to what it imports.
# So the audit names every module with `import all`, and the second check below fails if a
# module is missing from that list.
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

# The MiscMath modules a given file imports, whatever the import's visibility: `import`,
# `public import`, `meta import`, `import all` and their combinations.
imports_of() {
  grep -oE '^(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?MiscMath(\.[A-Za-z0-9_]+)*([[:space:]]|$)' "$1" \
    | awk '{print $NF}' || true
}

# The MiscMath modules a given file imports with `import all`.
all_imports_of() {
  grep -oE '^(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+all[[:space:]]+MiscMath(\.[A-Za-z0-9_]+)*([[:space:]]|$)' "$1" \
    | awk '{print $NF}' || true
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

# Every module the audit must cover is named by an `import all` in the audit module:
# the root, the infrastructure, and every result and support module.
audit="MiscMath/Audit.lean"
audited="$(all_imports_of "$audit" | sort -u)"
while IFS= read -r file; do
  module="$(printf '%s' "${file%.lean}" | tr '/' '.')"
  if [[ "$module" == "MiscMath.Audit" ]]; then
    continue
  fi
  if ! grep -qxF "$module" <<<"$audited"; then
    echo "error: $module is not named by an \`import all\` in $audit"
    echo "    add \`import all $module\` there: the audit sees a module's private declarations"
    echo "    only through an \`import all\` that names it"
    status=1
  fi
done < <({ echo MiscMath.lean; find MiscMath -name '*.lean'; } | sort)

if [[ $status -eq 0 ]]; then
  echo "import check passed: every module under MiscMath/ is reachable from $root" \
    "and named by an \`import all\` in $audit"
fi
exit $status
