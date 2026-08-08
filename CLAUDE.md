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
  tying it back to Mathlib's and say why under `## Relation to Mathlib`.
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

## Checks

```bash
lake build && ./scripts/check-imports.sh && ./scripts/check-conventions.sh && ./scripts/self-test-audit.sh
```

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

## House style

Mathlib [naming](https://leanprover-community.github.io/contribute/naming.html) and
[style](https://leanprover-community.github.io/contribute/style.html), aimed at but not
enforced. Prefer the form an application will actually want, and ship both directions
when they differ — a primality criterion is more useful than the existential it is
contraposed from.

Search Mathlib before proving anything. If it is already there, say so under
`## Relation to Mathlib` rather than duplicating it, and reconsider whether the file
earns its place.
