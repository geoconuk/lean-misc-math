# Working on this repository

Instructions for Claude Code sessions in this repository. Read
[README.md](README.md) for what the library is and
[CONTRIBUTING.md](CONTRIBUTING.md) for why the conventions exist; this file is the
operational summary.

## What makes this repository unusual

Proofs here are machine-generated and **nobody reads them**. Statements get a
best-effort read from the author, which is not a review. Everything about the workflow
follows from that: Lean's kernel already guarantees the proofs are correct, so the only
defect that can reach a user is **a statement that does not say what it appears to
say**. Effort goes into statements, not proof elegance.

Concretely, when generating a result, spend the care on:

- Stating it in **Mathlib's vocabulary**. A proof about a bespoke local definition is
  worth very little. If a new definition is unavoidable, ship a characterisation lemma
  tying it back to Mathlib's and say why under `## Relation to Mathlib`. This is not only
  style: a Palomar Challenge may import nothing but Lean core, Mathlib, Tau Ceti and
  CSLib, so a statement that cannot be expressed in Mathlib's vocabulary alone cannot be
  registered at all (step 6 below).
- **Truncated `Nat` subtraction and junk values** (`x / 0 = 0`, `Real.rpow` at bad
  arguments, degenerate empty cases). These make statements that are true and useless.
  Restate to avoid them where possible.
- **Non-vacuity.** Hypotheses that cannot be simultaneously satisfied make a theorem
  vacuously true and worthless. This is the single most likely way for a generated
  result to pass every check and still be worth nothing.

## Adding a result

1. Copy [`docs/TEMPLATE.lean`](docs/TEMPLATE.lean) to `MiscMath/<Area>/<Result>.lean`.
   `docs/examples/` holds filled-in models if it is present locally.
2. Fill in every docstring section — the convention check requires
   `## Informal statement`, `## Source`, `## Provenance` and `## Sanity checks`, and
   they are what make the statement reviewable without its proof.
3. Write the sanity checks. **If the theorem has hypotheses, a satisfiability witness
   is mandatory**, and it must cover universally quantified hypotheses, where an
   unsatisfiable assumption most easily hides. Note that such a witness usually cannot
   be discharged by `decide` — an unbounded `∀ n : ℕ` is not decidable — so expect to
   prove it. A witness you cannot discharge is telling you something about the
   statement; investigate before working around it.
4. Add the `import` line to `MiscMath.lean`, alphabetically.
5. Run the checks (below). All three must pass.
6. Say whether the result is worth registering with
   [Palomar](https://palomar-registry.org), which supplies the independent
   statement-versus-informal-claim read this repository cannot give itself. Its floor is
   not this repository's: the result must be affirmatively established as plausibly
   paper-worthy *and* as having a credible, identifiable research audience. A named
   theorem from the literature qualifies; a result admitted here only for being too small
   for Mathlib may well not. Novelty is not required. See
   [Palomar registration](CONTRIBUTING.md#palomar-registration). Make the recommendation
   and stop there. If George agrees, prepare the submission repository and hand it over;
   the entry ID and version go under `## Provenance` after he has registered it.

A result that outgrows one file — several theorems from one paper, say, over a shared model
— becomes a directory. Keep `MiscMath/<Area>/<Result>.lean` as the **roof**: it holds the
docstring, the sanity checks and the statements a reader should meet first, and it is the
only module `MiscMath.lean` names. The supporting modules go in
`MiscMath/<Area>/<Result>/`, and the roof imports them.

The two checks know the difference. `check-imports.sh` asks only that every module be
*reachable* from `MiscMath.lean`, so the audit still sees everything. `check-conventions.sh`
applies the four docstring sections and the `example` requirement to result modules — the
ones `MiscMath.lean` names — and to every module, result or support, the escape-hatch and
elaboration-option guards. A support module still needs a module docstring saying what it is
for and which roof it belongs to; it has no informal statement or source of its own to give.

Split when the file stops being navigable or its rebuild stops being quick, not by line
count. Do not split a single theorem away from the definitions its statement reads.

One further consequence: a Palomar Challenge may not import a support module either, so
registering a result that has grown a directory means restating its theorems from Mathlib
alone in the Challenge and letting the Solution depend on this repository.

## Checks

```bash
lake build && ./scripts/check-imports.sh && ./scripts/check-conventions.sh && ./scripts/self-test-audit.sh
```

Run that before declaring a result finished. While iterating, don't: a full `lake
build` re-elaborates `MiscMath/Audit.lean`, which imports the whole library and takes
a minute or two on its own. Check the single file you are editing instead:

```bash
lake build MiscMath.Area.Result
```

That is seconds once Mathlib is warm, and it catches everything except the
library-wide audit, which the file's own declarations cannot fail on their own anyway
unless you used a forbidden tactic.

`lake build` runs the axiom audit itself: `MiscMath/Audit.lean` invokes `#audit_axioms`
at elaboration time and is part of the default target, so a build that succeeds has
been audited. A successful audit prints, e.g.:

```
info: axiom audit passed: N declarations across M modules
      depend only on [propext, Classical.choice, Quot.sound]
```

If that line is missing from a successful build, something is wrong — investigate
rather than proceeding.

## Never

- **Never `sorry`, `native_decide`, `axiom`, `unsafe`, or `@[implemented_by]`.** The
  audit rejects the first three semantically and the convention check catches all five
  textually. Do not work around either; they are the point of the repository.
- **Never re-enable `autoImplicit`.** It is off in `lakefile.toml` so that a mistyped
  identifier cannot silently become a fresh universally quantified variable and change
  a statement.
- **Never weaken a check to make a result pass.** If a check is genuinely wrong, fix
  the check as its own change, with its own justification, separately from the result.
- **Never commit illustrative or throwaway proofs.** The published repository contains
  only results worth publishing on their own merits.
- **Never submit, publish, or post anything outside this repository.** That covers
  Palomar submissions, pull requests to Mathlib or Tau Ceti, Lean Pool projects, entries
  in the intentions registry, issues on other people's repositories, and social posts.
  Recommend freely, and once George has agreed, prepare the submission in full — then
  stop and hand it over. Preparing is the job; sending is his, and approval for one
  submission is not approval for the next.

## House style

Mathlib [naming](https://leanprover-community.github.io/contribute/naming.html) and
[style](https://leanprover-community.github.io/contribute/style.html), aimed at but not
enforced. Prefer the form an application will actually want, and ship both directions
when they differ — a primality criterion is more useful than the existential it is
contraposed from.

Search Mathlib before proving anything. If it is already there, say so under
`## Relation to Mathlib` rather than duplicating it, and reconsider whether the file
earns its place. Useful for this, in rough order of directness:

- `exact?` and `apply?` on the goal — settles it immediately when the lemma exists.
- `grep -rn "theorem <name_fragment>" .lake/packages/mathlib/Mathlib/` — Mathlib is
  checked out locally, and its naming convention makes this more effective than it
  sounds.
- `#loogle` / `#leansearch` (via the LeanSearchClient dependency) for search by shape
  or by natural language. These need network access.

Mathlib's naming convention is itself a search tool: a lemma about `a * b ≤ c` is
called something like `mul_le_of_…`. If you cannot guess a plausible name, that is
weak evidence it is not there.
