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
done < <(grep -oE '^(public[[:space:]]+)?import[[:space:]]+MiscMath\.[A-Za-z0-9_.]+' MiscMath.lean \
  | awk '{print $NF}')

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

# --- The module system, repository-wide -----------------------------------
# Palomar accepts a submission only if every Lean file in the repository -- not only the
# library, but Target/, Palomar/ and docs/ too -- begins with the `module` header and has at
# most 10,000 lines, and it checks this before building anything. The test below is the one
# Palomar applies (PalomarSubmission, scripts/source_requirements.py): after whitespace,
# `--` comments and ordinary `/- -/` comments, but not doc comments, the next token must be
# `module`. Tracked files only, as a submission sees them.
module_check="$(git ls-files -z '*.lean' | python3 -c '
import re, sys
MARK = re.compile(r"/-|-/")
CONT = re.compile(r"[A-Za-z0-9_\x27!?\u00c0-\u024f\u0370-\u03ff\u1f00-\u1fff\u2080-\u209c\u2100-\u214f]|\.[A-Za-z_]")
def has_module_header(t):
    i = 0
    while i < len(t):
        if t[i] in " \r\n":
            i += 1
        elif t.startswith("--", i):
            j = t.find("\n", i + 2)
            i = len(t) if j < 0 else j + 1
        elif t.startswith("/-", i) and not t.startswith(("/--", "/-!"), i):
            i += 3
            depth = 1
            while depth:
                m = MARK.search(t, i)
                if m is None:
                    return False
                depth += 1 if m.group() == "/-" else -1
                i = m.end()
        else:
            return t.startswith("module", i) and CONT.match(t, i + 6) is None
    return False
for path in sys.stdin.read().split("\0"):
    if not path or path.endswith("lakefile.lean"):
        continue
    text = open(path, encoding="utf-8").read()
    lines = text.count("\n") + (1 if text and not text.endswith("\n") else 0)
    if not has_module_header(text):
        print(f"{path} does not begin with the module header (ordinary comments may precede it)")
    if lines > 10000:
        print(f"{path} has {lines} lines; Palomar accepts at most 10,000")
')"
if [[ -n "$module_check" ]]; then
  while IFS= read -r line; do
    fail "$line"
  done <<<"$module_check"
fi

if [[ $status -eq 0 ]]; then
  echo "convention check passed: ${#files[@]} file(s), ${#result_files[@]} of them result module(s);" \
    "every tracked Lean file uses the module system"
fi
exit $status
