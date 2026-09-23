# The blind read-back

A read-back is a rendering, into plain mathematical English, of what a Lean declaration
literally asserts, written by an agent that has been shown the declaration and nothing else.
It is the one reading a statement gets here from someone who does not already know what it
was meant to say. Every other guard — the author's read, the sanity checks, the informal
statement itself — is applied by someone who specified the statement and therefore tends to
see the intended meaning in it. A rendering produced blind is not exposed to that, and the
comparison between it and the `## Informal statement` is where drift shows.

It is machinery, not a reviewer. It produces evidence; the judgement about what a divergence
means stays with the author, and [README.md](../README.md#who-did-what) says exactly how much
weight it carries. The technique, and the checklist in the brief below, follow
[Prove2Me](https://prove2.me)'s mission-auditor role
([`references/mission_auditor.md`](https://github.com/prove2me/prove2me_workspace/blob/main/references/mission_auditor.md)
in its agent workspace), where the agent that drafts a mission's statements may not write
their read-backs, and a blind sub-agent's rendering is what the human captain, and then a
moderator, compare against the source. The wording here is this repository's own, as are the
traps it names.

This file is in two parts. The first is for the session running the read-back. The second is
the brief the auditor receives, and it is the *only* part the auditor receives.

## Part 1 — running a read-back

### What to send

Exactly this, and nothing else:

1. **The advertised statements** — the declarations the result's `## Provenance` names — as
   Lean source, with every docstring and comment stripped and the proof removed after the
   `:=`. A docstring is the intended meaning in the author's words; it is precisely what the
   auditor must not see. Names stay: the rendering has to say what it is rendering, and one
   test here, on a statement flipped on purpose and a control with a neutral name, found that
   a suggestive name did not bend the rendering — one test, not a guarantee.
2. **Every definition those statements read**, transitively, from this library — `def`,
   `abbrev`, `structure`, `notation`, and any instance that changes how a statement
   elaborates — stripped the same way. The auditor is told to unfold them, and can only do
   that if it has them. Mathlib's definitions are not sent: the auditor is expected to know
   them, and to say when a reading turns on one.
3. **The preamble** those declarations need in order to parse: the `import`, `open`,
   `variable` and `include` lines in scope, and the namespace.
4. **The brief** — Part 2 below, verbatim.

Not the module docstring, not the informal statement, not the source, not the proofs, not the
sanity checks, not the rest of the file, not the file's name, and nothing said in conversation
about what the result is. Given any of these the auditor paraphrases the intended meaning
back, and the exercise is worthless.

Use a **fresh subagent** — a context that has seen none of the result — one per result, or
one per statement when there are many. A subagent launched from the session that wrote the
result starts fresh; that is enough, provided the prompt holds only the four items above.

### What to do with the rendering

Compare it, clause by clause, against the `## Informal statement` and against the source.
Read it properly: the comparison is the step that fails in practice, not the rendering, and a
rendering that names the flip is worthless if it is skimmed. Where they diverge the statement
has drifted — fix the Lean, re-run the checks, and read back again whatever changed. A
rendering of an earlier version of a statement describes a statement that no longer exists;
it counts for nothing, and a result whose statements changed after their last read-back has
not had one.

The rendering may also be wrong, or may say something true that the informal statement left
out. Both are findings: the first is recorded as such beside the rendering; the second goes
into the informal statement or the docstring. Do not edit the rendering.

### Recording it

Keep the rendering, verbatim, in `docs/readbacks/<Area>/<Result>.md`, one file per result,
holding:

- the commit the declarations were taken at, and the names of every declaration and
  definition sent;
- the rendering itself, unedited, under a heading naming the declaration it renders;
- the model that wrote it, and the date;
- what the comparison found — the same words that go under the result's `## Provenance`,
  which says what the read-back surfaced and points at this file.

The point of keeping it is that the comparison can then be repeated by anyone, with the same
evidence the author had, in the thirty seconds the README asks for.

## Part 2 — the brief

*Everything from the rule below to the end of the file is what the auditor receives, together
with the Lean it is to render, and nothing else.*

---

You are given one or more Lean 4 declarations, any definitions they depend on, and the
preamble they need. Write out, in plain mathematical English, what each declaration literally
asserts. What you write is the artefact's own testimony: a human will compare it against what
the author intended, and any gap between the two is exactly what they are looking for.

1. **Render the code, not an intent.** Say only what the Lean says. Do not fill in from what
   a theorem of this shape usually claims, or from what its name suggests; if you recognise a
   famous statement, render what is in front of you, not what you remember. If the code claims
   less than you would expect, your rendering claims less.

2. **Account for every binder.** Every universally and existentially quantified variable,
   every explicit, implicit and instance argument, every typeclass assumption and every
   `variable` in scope appears in the rendering, with the type it ranges over — ℕ, ℤ, ℚ, ℝ, a
   `Fin n`, a `Finset` or a `Set`, a subtype such as the unit interval, a function space — and
   with what each coercion does. Omitting a hypothesis is the worst failure.

3. **State the quantifier order.** Say which objects are chosen before which, and which may
   depend on which. "There exist functions, chosen before $f$, such that for every $f$ …" and
   "for every $f$ there exist functions, which may depend on $f$, such that …" are different
   theorems, and the difference is the easiest thing to lose in a paraphrase.

4. **Unfold every non-standard definition.** If a statement reads through a definition
   supplied with it, say what that definition means, inline, in terms of standard notions;
   never use its name as if it were standard. Where the reading turns on a Mathlib definition
   — whether a covering number counts open or closed balls, what a sum over an empty index set
   is, how a function is extended outside its domain — say that it does, and on what, rather
   than deciding it.

5. **Surface degenerate and junk cases.** Say what the quantifiers silently include: $n = 0$,
   the empty set or index set, the constant function, the trivial type. Say where a total
   function returns a junk value the statement does not exclude — division by zero is zero,
   subtraction in ℕ truncates at zero, `Real.log`, `Real.sqrt` and real powers take values
   outside their mathematical domains, a supremum of an unbounded or empty set is a default —
   and whether the statement then still says anything at that point. If the hypotheses could
   be impossible to satisfy together, say so: a vacuous theorem is the classic trap.

6. **Preserve logical precision.** Keep the exact strength of every connective and relation:
   ≤ against <, ∃ against ∃!, ↔ against →, the direction of each inequality and inclusion,
   strict against non-strict monotonicity, monotone on a set against monotone everywhere,
   continuous against continuous on a set, a limit along which filter, almost everywhere
   against everywhere. Do not round to the "morally equivalent" claim.

7. **Write for a mathematician who does not read Lean.** Standard notation, LaTeX where it
   helps, no tactic talk, and no Lean syntax beyond the declaration names: $P_i$, not `P i`.

8. **No judgement, no advocacy.** Do not say whether the formalisation is correct, faithful,
   natural or well designed, and do not defend it. Do not guess what theorem it is meant to be
   or where it comes from. The discrepancies are for the human to find.

Format: one self-contained block per declaration, headed by the declaration's name, that can
be understood without the source in front of the reader. Introduce the binders in the order
the statement does, then the hypotheses, then the conclusion, then a final line headed *Edge
cases* for point 5. Completeness over elegance: this is fine print.
