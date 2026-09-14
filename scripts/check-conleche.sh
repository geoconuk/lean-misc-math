#!/usr/bin/env bash
# Re-check every proof in the library with an independent, verified checker.
#
# `lake build` establishes that Lean's kernel accepts every proof here. This script asks
# a second checker that shares no code with that kernel: con-leche
# (https://github.com/leanprover/con-leche), an external checker written in Lean and
# proven, in Lean, to accept only environments that have a set-theoretic model — so it
# cannot accept a proof of `False`, and it admits no axiom beyond `propext`,
# `Classical.choice` and `Quot.sound`. Every declaration the axiom audit covers is
# exported with lean4export together with its whole dependency cone into Mathlib and
# Lean core, and the cone is handed to con-leche. Acceptance is a second, independent
# verdict on the proofs and on the axiom set.
#
# What this does not check: statements. con-leche confirms that every accepted theorem
# holds in the model *as elaborated* — the part the kernel already guaranteed — and says
# nothing about whether a theorem is the one its docstring claims. Nothing here closes
# that gap; see README.md, "What this repository guarantees".
#
# This is a release gate, not a per-commit check: run it before tagging, and paste the
# summary line it prints into the release notes. It is kept out of CI because the first
# run clones and builds two tools, con-leche's proof included, and every run writes an
# export of a few hundred megabytes; warm, it takes a few minutes, most of it the export.
#
# Two revisions are pinned. lean4export reads this repository's compiled .olean files,
# so it must be built from the tag matching `lean-toolchain`; that tag is derived from
# the file and moves with it. con-leche is pinned to a commit below and need not share
# our toolchain — it embeds the `Nat` definitions of several toolchains (its `pins/`
# directory) — but it must carry the pin for ours; if it declines (exit 2) naming the
# toolchain, move the commit forward to one that has it. Neither tool is a Lake
# dependency of the library: both live under `.lake/conleche/`, which is gitignored.
#
# The check ends with a negative control, in the spirit of self-test-audit.sh: a copy of
# the export with one of this library's theorems retargeted to `False` must be rejected.
# A checker that accepts everything is worse than none.
#
# con-leche's theorem is only worth anything if it is really proven, so the first run
# at a given pin builds con-leche's whole proof (about fifteen minutes; Lake caches it)
# and confirms that the two theorems its README names rest on the three standard axioms
# alone — in particular not on `sorryAx`. What remains on trust is the same as for any
# verified checker: the Lean compiler and runtime that built it (its `Nat` arithmetic
# included), lean4export's faithfulness, and the unproven link from its `main` to the
# checked `checkDecls` that its README invites you to read; and that Lean's own kernel
# checked con-leche's proof.
set -euo pipefail
cd "$(dirname "$0")/.."

con_leche_repo="https://github.com/leanprover/con-leche"
con_leche_rev="c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0"   # master, 2026-09-14
lean4export_repo="https://github.com/leanprover/lean4export"

toolchain="$(tr -d '[:space:]' < lean-toolchain)"   # leanprover/lean4:v4.33.0
lean4export_rev="${toolchain#*:}"                    # v4.33.0

tools=".lake/conleche"
list="$tools/declarations.txt"
control_name_file="$tools/control-theorem.txt"
export_file="$tools/MiscMath.ndjson"
tampered="$tools/MiscMath.tampered.ndjson"
mkdir -p "$tools"
cleanup() { rm -f "$tampered"; }
trap cleanup EXIT

# Fetch one commit or tag of a repository into a directory and build the given targets
# there (none means the package's defaults). A marker file records the revision checked
# out, so a repeat run only asks Lake to rebuild, which is a no-op. Each tool builds with
# its own `lean-toolchain`, which elan honours per directory, so con-leche's toolchain may
# differ from ours.
fetch_and_build() {
  local dir="$1" repo="$2" rev="$3"
  shift 3
  if [[ ! -f "$dir/.rev" || "$(cat "$dir/.rev")" != "$rev" ]]; then
    echo "check-conleche: fetching $repo at $rev"
    if [[ ! -d "$dir/.git" ]]; then
      git init -q "$dir"
      git -C "$dir" remote add origin "$repo"
    fi
    git -C "$dir" fetch -q --depth 1 origin "$rev"
    git -C "$dir" checkout -q --detach FETCH_HEAD
    printf '%s\n' "$rev" > "$dir/.rev"
  fi
  (cd "$dir" && lake build "$@")
}

# con-leche's default targets are its checker, its consistency proof and the capstone
# module `ConLeche.MainTheorem` that states the two theorems its README names. Building
# them is Lean checking that proof; this then confirms the theorems rest on the three
# standard axioms alone, once per pinned revision.
verify_con_leche_proof() {
  local dir="$1"
  if [[ -f "$dir/.proof-checked" && "$(cat "$dir/.proof-checked")" == "$con_leche_rev" ]]; then
    return
  fi
  echo "check-conleche: printing the axioms of con-leche's main theorems"
  cat > "$dir/Axioms.lean" <<'LEAN'
-- Written by scripts/check-conleche.sh (of lean-misc-math). Not part of con-leche.
import ConLeche.MainTheorem
#print axioms ConLeche.no_False_declaration
#print axioms ConLeche.model_exists
LEAN
  local expected="'ConLeche.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound]
'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]"
  local actual
  actual="$(cd "$dir" && lake env lean Axioms.lean)"
  rm -f "$dir/Axioms.lean"
  printf '%s\n' "$actual"
  if [[ "$actual" != "$expected" ]]; then
    echo "check-conleche FAILED: con-leche's main theorems do not rest on the three standard axioms alone"
    exit 1
  fi
  printf '%s\n' "$con_leche_rev" > "$dir/.proof-checked"
}

fetch_and_build "$tools/lean4export" "$lean4export_repo" "$lean4export_rev" lean4export
fetch_and_build "$tools/con-leche" "$con_leche_repo" "$con_leche_rev"
verify_con_leche_proof "$tools/con-leche"
lean4export="$tools/lean4export/.lake/build/bin/lean4export"
con_leche="$tools/con-leche/.lake/build/bin/con-leche"

# The export must be of a green build: the same oleans the audit ran over.
lake build

# 1. The declarations to check: exactly the set `#audit_axioms` iterates, by the same
#    module predicate, from the same imports as MiscMath/Audit.lean. The list is
#    written by Lean itself so that names come out in the escaped spelling lean4export
#    reads back. The same pass picks the theorem for the negative control below: the
#    first theorem of this library, in module order, whose name is plain ASCII
#    components, so that step 4 can find its record without parsing JSON.
cat > "$tools/ListDeclarations.lean" <<LEAN
-- Written by scripts/check-conleche.sh. Not part of the library.
import MiscMath
import MiscMath.Meta.AxiomAudit
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
lake env lean "$tools/ListDeclarations.lean"
declarations=()
while IFS= read -r name; do
  declarations+=("$name")
done < "$list"
control_name="$(tr -d '[:space:]' < "$control_name_file")"
echo "check-conleche: ${#declarations[@]} declarations in MiscMath modules"

# 2. Export them with their dependency cone. lean4export emits each dependency before
#    the declaration that uses it, so the cone is closed. The names travel on the
#    command line, which macOS caps at 1 MiB — room for well over ten thousand; if the
#    library ever outgrows that, drop the `--` list and export the whole environment.
#    A missing constant is a panic that the compiled exporter prints and then ignores,
#    so its stderr is inspected rather than trusted.
echo "check-conleche: exporting the dependency cone"
lake env "$lean4export" MiscMath MiscMath.Meta.AxiomAudit -- "${declarations[@]}" \
  > "$export_file" 2> "$export_file.stderr"
if grep -q -i -E 'panic|not found|error' "$export_file.stderr"; then
  echo "check-conleche FAILED: lean4export reported a problem:"
  cat "$export_file.stderr"
  exit 1
fi
records="$(grep -c -E '^\{"(thm|def|axiom|opaque|quot|inductive)"' "$export_file" || true)"
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

con_leche_short="$(git -C "$tools/con-leche" rev-parse --short HEAD)"
echo "con-leche check passed: accepted $accepted declarations — ${#declarations[@]} in MiscMath" \
  "modules with their dependency cone, $axioms axioms — con-leche $con_leche_short," \
  "lean4export $lean4export_rev, toolchain $toolchain, ${elapsed}s"
