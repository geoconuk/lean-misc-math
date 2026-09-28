# Working on this repository

Instructions for Claude Code sessions in this repository. Read
[README.md](README.md) for what the library is and
[CONTRIBUTING.md](CONTRIBUTING.md) for why the conventions exist; this file is the
operational summary.

## What makes this repository unusual

Proofs here are machine-generated and **nobody reads them**. Only a result's *advertised
statements* — the declarations its `## Informal statement` makes claims about, named under
its `## Provenance` — get a best-effort read from the author, which is not a review; every
other lemma and definition is proof, and may be read by no one. Everything about the
workflow follows from that: Lean's kernel already guarantees the proofs are correct, so the
only defect that can reach a user is **a statement that does not say what it appears to
say**. Effort goes into statements, not proof elegance.

Concretely, when generating a result, spend the care on:

- Stating it in **Mathlib's vocabulary**. A proof about a bespoke local definition is
  worth very little. If a new definition is unavoidable, ship a characterisation lemma
  tying it back to Mathlib's and say why under `## Relation to Mathlib`. This is not only
  style: a Palomar Challenge may import nothing but Lean core, Mathlib, Tau Ceti and
  CSLib, so a statement that cannot be expressed in Mathlib's vocabulary alone cannot be
  registered at all (step 7 below).
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
   they are what make the statement reviewable without its proof. Under `## Provenance`,
   name the advertised statements — the declarations the informal statement makes claims
   about, wherever they live. The read covers those, and nothing else is guaranteed one.
3. Write the sanity checks. **If the theorem has hypotheses, a satisfiability witness
   is mandatory**, and it must cover universally quantified hypotheses, where an
   unsatisfiable assumption most easily hides. Note that such a witness usually cannot
   be discharged by `decide` — an unbounded `∀ n : ℕ` is not decidable — so expect to
   prove it. A witness you cannot discharge is telling you something about the
   statement; investigate before working around it.
4. Add a `public import` line to `MiscMath.lean` and an `import all` line to
   `MiscMath/Audit.lean`, alphabetically in both. Every Lean file here uses the module
   system, which Palomar requires of every file in a submitted repository; the template
   shows the header, and `scripts/check-conventions.sh` fails on a file without it.
5. Run the checks (below). All three must pass.
6. Get a **read-back** of the advertised statements before they go for their best-effort
   read, following [`docs/READBACK.md`](docs/READBACK.md). Send them — as Lean source with
   docstrings and comments stripped, together with the definitions they are stated through,
   and nothing else — to a fresh subagent carrying that file's brief, and have it write out
   what they literally assert. Compare the rendering against the `## Informal statement` and
   against the source. Where they diverge the statement has drifted; fix it, re-run step 5,
   and read back again whatever changed — a rendering of an earlier version describes a
   statement that no longer exists, and counts for nothing. Record the rendering verbatim,
   with the model that wrote it and the date, in `docs/readbacks/<Area>/<Result>.md`, and
   say under `## Provenance` what the comparison found and where the rendering is.

   The constraint is what makes this worth doing: the read-back agent must not see the
   module docstring, the informal statement, the source, the declaration docstrings, or the
   rest of the file. Given any of them it paraphrases the intended meaning back and the
   exercise is worthless. Give it the advertised statements and the definitions they read,
   nothing else.

   This is the only guard here that does not assume its reader already knows what the
   statement was meant to say — which is exactly what makes an author's own read of a
   statement they specified the weakest link in the chain. The technique is
   [Prove2Me](https://prove2.me)'s: there the agent that drafts a mission's statements may
   not write their read-backs, a blind sub-agent renders each from the Lean alone, and that
   rendering is what the human captain, and then a moderator, compare against the source.
7. Say whether the result is worth registering with
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

The two checks know the difference. `check-imports.sh` asks that every module be
*reachable* from `MiscMath.lean`, and that every module — support modules included — be
named by an `import all` in `MiscMath/Audit.lean`: the audit sees a module's private
declarations only through an `import all` naming it, and that does not reach through a roof
to what it imports. `check-conventions.sh` applies the four docstring sections and the
`example` requirement to result modules — the ones `MiscMath.lean` names — and to every
module, result or support, the escape-hatch and elaboration-option guards. A support module
still needs a module docstring saying what it is for and which roof it belongs to; it has
no informal statement or source of its own to give. An advertised statement may live in a
support module — the natural-form theorems of `PoissonTrialsFixedMean` do — and the roof's
`## Provenance` names it wherever it lives. A declaration `## Provenance` does not name is
proof, in the roof or under it, and the roof's docstring should not describe one as though
it had been read.

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

Before a release is tagged, one more check runs by hand:

```bash
./scripts/check-conleche.sh
```

It exports every declaration the audit covers, with its dependency cone into Mathlib and
Lean core, and re-checks the lot with [con-leche](https://github.com/leanprover/con-leche),
an external checker proven in Lean to accept only environments with a set-theoretic model;
it then confirms the checker rejects a copy with one of our theorems retargeted to `False`.
It is a release gate and not a per-result check, by George's decision: it re-checks proofs,
the part the kernel already guarantees, and says nothing about statements. It is not in CI:
the first run at a given pin clones and builds the two tools under `.lake/conleche/`,
con-leche's consistency proof included (about fifteen minutes, then cached), and prints the
axioms of its two main theorems to confirm they rest on the standard three; after that a run
takes a few minutes. Paste the summary line it prints into the release notes. The two pinned
revisions are explained at the head of the script; the con-leche pin must move forward if a
toolchain bump outruns its `pins/`.

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

Beyond Mathlib, [Formalpedia](https://prove2.me/formalpedia) — Prove2Me's library of
agent-proved statements, searchable without an account at
`https://prove2.me/formalpedia?q=<words>` — is worth a look once the statement is drafted,
for a formalisation of the same theorem to hold ours against. It is a second rendering to
compare shapes with, not a source: nothing there outside a mission's audited core is
guaranteed a read by anyone, and nothing there can be a dependency here, since a Palomar
Challenge may import only Lean core, Mathlib, Tau Ceti and CSLib, and a statement read
through Formalpedia's definitions is not in Mathlib's vocabulary.
