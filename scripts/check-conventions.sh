#!/usr/bin/env bash
# Textual guards on result files.
#
# These complement the axiom audit rather than duplicating it. The audit is semantic
# and authoritative for what a proof *depends on*; these checks catch things that
# never reach the proof term (elaboration options, documentation conventions) and give
# a pointed error message for the ones that do.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0

fail() {
  echo "error: $1"
  status=1
}

# forbid <file> <regex> <message> — fail if the pattern occurs, showing where.
forbid() {
  local file="$1" pattern="$2" message="$3" hits
  if hits="$(grep -nE "$pattern" "$file")"; then
    fail "$file $message"
    printf '%s\n' "$hits" | sed 's/^/    /'
  fi
}

# require <file> <regex> <message> — fail if the pattern is absent.
require() {
  local file="$1" pattern="$2" message="$3"
  if ! grep -qE "$pattern" "$file"; then
    fail "$file $message"
  fi
}

files=()
while IFS= read -r f; do
  files+=("$f")
done < <(find MiscMath -name '*.lean' -not -path 'MiscMath/Meta/*' -not -name 'Audit.lean' | sort)

# The *result modules* are the ones MiscMath.lean names directly; check-imports.sh lets
# everything else reach the audit through them. A result too large for one file is split
# into a roof module carrying the statements and supporting modules underneath, and it is
# the roof that has an informal statement, a source and a provenance to give — a module of
# shared machinery has none, and demanding them would only produce four empty headings. So
# the documentation conventions below apply to result files; the escape-hatch and
# elaboration-option checks, which guard the proofs rather than the exposition, apply to
# every file.
result_files=()
while IFS= read -r m; do
  f="$(printf '%s' "$m" | tr '.' '/').lean"
  if [[ -f "$f" ]]; then
    result_files+=("$f")
  fi
done < <(grep -oE '^import[[:space:]]+MiscMath\.[A-Za-z0-9_.]+' MiscMath.lean | awk '{print $2}')

is_result() {
  local f
  for f in ${result_files[@]+"${result_files[@]}"}; do
    if [[ "$f" == "$1" ]]; then
      return 0
    fi
  done
  return 1
}

if [[ ${#result_files[@]} -eq 0 ]]; then
  # A legitimate state: the repository starts empty, and a result is only committed
  # once it is one the author wants others to see.
  echo "note: no result files under MiscMath/ yet; checking infrastructure only"
fi

# MiscMath/Audit.lean is the module that *runs* the audit, so its own declarations are
# not imported into the audited environment and would escape the check. It must stay
# empty of results.
forbid MiscMath/Audit.lean '^[[:space:]]*(theorem|lemma|def|instance|abbrev)[[:space:]]' \
  'must contain only the #audit_axioms invocation: its own declarations are not covered by the audit it runs'

# Guarded because macOS still ships bash 3.2, where `"${empty[@]}"` trips `set -u`.
for file in ${files[@]+"${files[@]}"}; do
  # --- Escape hatches -------------------------------------------------------
  # The axiom audit already rejects the proof terms the first three produce; matching
  # them textually turns a puzzling axiom-audit failure into a clear message. The last
  # two the audit cannot see at all, since they affect compilation, not proof terms.
  #
  # The word boundary is deliberately blunt: any occurrence of the bare word counts, prose
  # included. Relaxing it so that a docstring can say "sorry-free" was tried and reverted —
  # a guard of this kind is worth more for being unambiguous than for being convenient, and
  # the cost of routing around it is one word.
  forbid "$file" '(^|[^[:alnum:]_.])sorry([^[:alnum:]_]|$)' 'uses sorry'
  forbid "$file" '^[[:space:]]*axiom[[:space:]]' 'declares an axiom'
  forbid "$file" '(^|[^[:alnum:]_.])native_decide([^[:alnum:]_]|$)' \
    'uses native_decide, which trusts the compiler rather than the kernel'
  forbid "$file" '^[[:space:]]*unsafe[[:space:]]' 'declares an unsafe definition'
  forbid "$file" '@\[implemented_by' 'uses @[implemented_by]'

  # --- Elaboration options --------------------------------------------------
  # autoImplicit is off repo-wide in lakefile.toml. Re-enabling it per file is the
  # easiest way to end up with a subtly wrong statement: a mistyped identifier
  # silently becomes a fresh universally quantified variable.
  forbid "$file" 'set_option[[:space:]]+(relaxedAutoImplicit|autoImplicit)[[:space:]]+true' \
    're-enables autoImplicit'
  forbid "$file" 'set_option[[:space:]]+debug\.' 'sets a debug option'

  # --- Documentation conventions -------------------------------------------
  # These are what make a statement reviewable without reading its proof, which is
  # the only defence against the failure mode the audit cannot catch. See README.
  #
  # Every file says what it is for; only a result file carries the full apparatus.
  require "$file" '^/-!' 'has no module docstring (/-! ... -/)'
  if is_result "$file"; then
    require "$file" '^## Informal statement' "has no '## Informal statement' section"
    require "$file" '^## Source' "has no '## Source' section"
    require "$file" '^## Provenance' "has no '## Provenance' section"
    require "$file" '## Sanity checks' "has no '## Sanity checks' section"
    require "$file" '^example ' 'has no sanity-check examples'
  fi
done

if [[ $status -eq 0 ]]; then
  echo "convention check passed: ${#files[@]} file(s), ${#result_files[@]} of them result module(s)"
fi
exit $status
