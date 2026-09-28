#!/usr/bin/env bash
# Re-check every proof in the library with an independent, verified checker.
#
# `lake build` establishes that Lean's kernel accepts every proof here. This script asks
# a second checker that shares no code with that kernel: con-leche
# (https://github.com/leanprover/con-leche), an external checker written in Lean and
# proven, in Lean, to accept only environments that have a set-theoretic model — so it
# cannot accept a proof of `False`, and it admits no axiom beyond `propext`,
# `Classical.choice` and `Quot.sound`. Every declaration the axiom audit covers is
# exported, together with its whole dependency cone into Mathlib and Lean core, and the
# cone is handed to con-leche. Acceptance is a second, independent
# verdict on the proofs and on the axiom set.
#
# What this does not check: statements. con-leche confirms that every accepted theorem
# holds in the model *as elaborated* — the part the kernel already guaranteed — and says
# nothing about whether a theorem is the one its docstring claims. Nothing here closes
# that gap; see README.md, "What this repository guarantees".
#
# This is a release gate, not a per-commit check: run it before tagging, and paste the
# summary line it prints into the release notes. It is kept out of CI because every run writes
# an export of a few hundred megabytes and checks it, which takes minutes.
#
# Both tools come with the Lean toolchain. From v4.35 the toolchain ships con-leche and the
# exporter `leanexport` (lean4export, upstreamed) beside `lean`; Palomar's verification runs the
# same binaries. The gate uses those of the toolchain `lean-toolchain` names, so nothing is
# fetched or built and the export format always matches the compiler that wrote the .olean
# files. Until 2026-09-28 the gate fetched con-leche at a pinned commit instead, built its
# consistency proof and printed the axioms of its two main theorems before trusting the binary;
# the pinned commit carried no toolchain pin for v4.35, and the toolchain ships the checker
# without its proof. So what the gate now takes on trust is that the bundled binary is built from
# con-leche's proven checker, as it trusts the rest of the toolchain; con-leche's theorem is
# `ConLeche.no_proof_of_False`, in its repository. The summary line records the toolchain and the
# SHA-256 of the binary that ran, so that a verdict names exactly what gave it.
#
# The check ends with a negative control, in the spirit of self-test-audit.sh: a copy of
# the export with one of this library's theorems retargeted to `False` must be rejected.
# A checker that accepts everything is worse than none.
set -euo pipefail
cd "$(dirname "$0")/.."

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
prefix="$(lake env lean --print-prefix)"
leanexport="$prefix/bin/leanexport"
con_leche="$prefix/bin/con-leche"
for tool in "$leanexport" "$con_leche"; do
  if [[ ! -x "$tool" ]]; then
    echo "check-conleche FAILED: $toolchain does not bundle $(basename "$tool"); Lean v4.35 and later do"
    exit 1
  fi
done
con_leche_sha="$(shasum -a 256 "$con_leche" | cut -c1-16)"

tools=".lake/conleche"
list="$tools/declarations.txt"
control_name_file="$tools/control-theorem.txt"
export_file="$tools/MiscMath.ndjson"
tampered="$tools/MiscMath.tampered.ndjson"
mkdir -p "$tools"
cleanup() { rm -f "$tampered"; }
trap cleanup EXIT

# The export must be of a green build: the same oleans the audit ran over.
lake build

# 1. The declarations to check: exactly the set `#audit_axioms` iterates, by the same
#    module predicate, from the same imports as MiscMath/Audit.lean — which are copied from
#    it: under the module system the audit sees a module's private declarations only through
#    an `import all` naming it, and so must this list. The list is written by Lean itself so
#    that names come out in the escaped spelling the exporter reads back. The same pass picks
#    the theorem for the negative control below: the first theorem of this library, in module
#    order, whose name is plain ASCII components, so that step 4 can find its record without
#    parsing JSON.
{
  echo "-- Written by scripts/check-conleche.sh. Not part of the library."
  echo "module"
  grep -E '^import all MiscMath' MiscMath/Audit.lean
  echo "meta import Lean"
  cat <<LEAN
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut out := ""
  let mut control : Option Name := none
  for i in [0 : names.size] do
    unless MiscMath.Meta.isAuditedModule names[i]! do continue
    for n in data[i]!.constNames do
      out := out ++ toString n ++ "\n"
      let isTheorem := match env.find? n with
        | some (.thmInfo _) => true
        | _ => false
      let plain := n.components.all fun c => match c with
        | .str .anonymous s => !s.isEmpty && s.all fun ch => ch.isAlphanum || ch == '_'
        | _ => false
      if control.isNone && isTheorem && plain then
        control := some n
  IO.FS.writeFile "$list" out
  match control with
  | some n => IO.FS.writeFile "$control_name_file" (toString n ++ "\n")
  | none => throwError "no plain-named theorem found for the negative control"
LEAN
} > "$tools/ListDeclarations.lean"
lake env lean "$tools/ListDeclarations.lean"
declarations=()
while IFS= read -r name; do
  declarations+=("$name")
done < "$list"
control_name="$(tr -d '[:space:]' < "$control_name_file")"
echo "check-conleche: ${#declarations[@]} declarations in MiscMath modules"

# 2. Export them with their dependency cone. The exporter emits each dependency before
#    the declaration that uses it, so the cone is closed. It reads private declarations too,
#    through the modules named. The names travel on the
#    command line, which macOS caps at 1 MiB — room for well over ten thousand; if the
#    library ever outgrows that, drop the `--` list and export the whole environment.
#    A missing constant is a panic that the compiled exporter prints and then ignores,
#    so its stderr is inspected rather than trusted.
echo "check-conleche: exporting the dependency cone"
lake env "$leanexport" MiscMath MiscMath.Meta.AxiomAudit -- "${declarations[@]}" \
  > "$export_file" 2> "$export_file.stderr"
if grep -q -i -E 'panic|not found|error' "$export_file.stderr"; then
  echo "check-conleche FAILED: the exporter reported a problem:"
  cat "$export_file.stderr"
  exit 1
fi
# con-leche counts one accepted declaration per def, theorem, opaque, axiom and inductive
# record, not the quotient records, which its own prelude installs; this counts the same.
records="$(grep -c -E '^\{"(thm|def|axiom|opaque|inductive)"' "$export_file" || true)"
axioms="$(grep -c -E '^\{"axiom"' "$export_file" || true)"
echo "check-conleche: $records declaration records in the export ($axioms axioms)"

# 3. The check. `--verified` is the default and the mode the consistency theorem is
#    about; it is spelled out so the invocation documents itself. Exit 0 is the only
#    verdict that carries the theorem: 1 is a rejection, 2 a feature con-leche does not
#    support, 3 an error. The accepted count must equal the export's record count, so
#    that a truncated export or a checker that skipped records cannot pass.
echo "check-conleche: running con-leche --verified"
start=$SECONDS
status=0
verdict="$("$con_leche" --verified "$export_file")" || status=$?
elapsed=$((SECONDS - start))
printf '%s\n' "$verdict"
if [[ $status -ne 0 ]]; then
  echo "check-conleche FAILED: con-leche exited $status (1 rejected, 2 declined, 3 error)"
  exit 1
fi
accepted="$(printf '%s\n' "$verdict" | sed -n -E 's/^con-leche: accepted ([0-9]+) declarations.*/\1/p')"
if [[ -z "$accepted" ]]; then
  echo "check-conleche FAILED: exit 0 without an 'accepted N declarations' verdict"
  exit 1
fi
if [[ "$accepted" != "$records" ]]; then
  echo "check-conleche FAILED: con-leche accepted $accepted declarations but the export holds $records"
  exit 1
fi

# 4. Negative control. Retarget the statement of one of this library's own theorems —
#    the one chosen in step 1 — to the hard-coded `False` that con-leche's main
#    corollary is about. It must be rejected, and rejected as invalid (exit 1), not
#    declined or errored. Names in the export are interned as chains of components, so
#    one pass rebuilds them as it goes and stops at the theorem record that carries the
#    chosen name; `False` itself is the constant record whose name has that spelling.
false_name="$(grep -m1 -E '^\{"in":[0-9]+,"str":\{"pre":0,"str":"False"\}\}$' "$export_file" \
  | sed -E 's/^\{"in":([0-9]+),.*/\1/' || true)"
false_expr="$(grep -m1 -E "^\{\"const\":\{\"name\":${false_name:-x},\"us\":\[\]\},\"ie\":[0-9]+\}\$" "$export_file" \
  | sed -E 's/.*"ie":([0-9]+)\}$/\1/' || true)"
if [[ -z "$false_name" || -z "$false_expr" ]]; then
  echo "check-conleche FAILED: could not find the constant False in the export"
  exit 1
fi
control_line="$(awk -v target="$control_name" '
  /^\{"in":/ {
    match($0, /"in":[0-9]+/);  k = substr($0, RSTART + 5, RLENGTH - 5)
    match($0, /"pre":[0-9]+/); p = substr($0, RSTART + 6, RLENGTH - 6)
    if ($0 ~ /"str":\{/) { match($0, /"str":"[^"]*"\}\}$/); c = substr($0, RSTART + 7, RLENGTH - 10) }
    else                  { match($0, /"i":[0-9]+/);          c = substr($0, RSTART + 4, RLENGTH - 4) }
    name[k] = (p == 0) ? c : name[p] "." c
    next
  }
  /^\{"thm":/ {
    match($0, /"name":[0-9]+/); k = substr($0, RSTART + 7, RLENGTH - 7)
    if (name[k] == target) { print NR; exit }
  }' "$export_file")"
if [[ -z "$control_line" ]]; then
  echo "check-conleche FAILED: no theorem record for $control_name in the export"
  exit 1
fi
sed -E "${control_line}s/\"type\":[0-9]+/\"type\":$false_expr/" "$export_file" > "$tampered"
echo "check-conleche: negative control — $control_name retargeted to False (expected to be REJECTED)"
status=0
control="$("$con_leche" --verified "$tampered")" || status=$?
printf '%s\n' "$control"
if [[ $status -ne 1 ]]; then
  echo "check-conleche FAILED: the tampered export was not rejected (exit $status, expected 1)."
  echo "Do not trust the acceptance above until this is understood."
  exit 1
fi

echo "con-leche check passed: accepted $accepted declarations — ${#declarations[@]} in MiscMath" \
  "modules with their dependency cone, $axioms axioms — the con-leche and exporter of" \
  "$toolchain (con-leche sha256 $con_leche_sha…), ${elapsed}s"
