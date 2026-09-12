# Palomar submissions

[Palomar](https://palomar-registry.org) is a registry of Lean-verified mathematics: it
takes a repository at a pinned commit, checks the proofs with Lean's kernel and with the
independent NanoDa kernel, has a language model assess whether the formal statement fairly
represents the mathematical claim, and — if nothing blocks — publishes the exact statement
and the review's comments.

This directory holds the per-submission files. Nothing here is part of the `MiscMath`
library: no module under `MiscMath/` imports anything from `Palomar/`, and the three
checks in [`scripts/`](../scripts) are all scoped to `MiscMath/`, so nothing here can
weaken them.

## Why this library submits at all

The point is not the listing. [README.md](../README.md) is explicit that the one thing
this repository cannot guarantee is "that a statement means what its docstring says it
means", and that a best-effort read by one person is not a review. Palomar's review is a
second, independent read of exactly that, and NanoDa is a second, independent kernel where
the [axiom audit](../MiscMath/Meta/AxiomAudit.lean) trusts only Lean's. Both check
something this repository currently takes on trust.

Palomar is not peer review, not a novelty certificate and not an endorsement, and being
listed there does not upgrade the best-effort read into a review. The claims in
[README.md](../README.md) stand unchanged.

## Layout

One submission is one Comparator configuration. Palomar's *selected project* for these
submissions is the repository root — the `MiscMath` Lean project itself — so a submission
adds no lakefile, toolchain or manifest of its own, and the Solution module is the library
file that actually ships rather than a copy of it.

```text
Palomar/<Result>/
  Challenge.lean        statement surface: the theorems, without proofs
  TypeCheck.lean        guards Challenge.lean against drift from the library
  comparator.json       which modules and declarations Comparator compares
  formalization.yaml    provenance, sources, automation disclosure, review status
```

## About the `sorry`s in `Challenge.lean`

A Challenge file states its theorems and leaves the proofs as deliberate holes; Comparator
fills them from the Solution module and rejects any Solution declaration depending on
`sorryAx`. Palomar's `CONTRIBUTING.md` says so directly: "Deliberate holes in Challenge
declarations are allowed."

That is the one place in this repository where `sorry` appears, and it is not an exception
to the rule in [CLAUDE.md](../CLAUDE.md) so much as the rule's mirror image — a Challenge
is a statement *asking* to be proved, and what proves it is the audited library theorem.
It is kept honest structurally rather than by promise:

- `Palomar/` is outside `MiscMath/`, so the Challenge reaches neither the axiom audit nor
  `scripts/check-conventions.sh`, and cannot launder a `sorry` into the library.
- No Challenge target is in `defaultTargets`, so `lake build` never elaborates one and
  the library's build stays warning-free.
- `TypeCheck.lean` re-checks each advertised statement against the shipped theorem, so the
  Challenge cannot quietly advertise something the library does not prove.

## Building and checking

```bash
lake build PalomarWynerChallenge            && lake build PalomarWynerTypeCheck
lake build PalomarHoeffdingChallenge        && lake build PalomarHoeffdingTypeCheck
lake build PalomarKolmogorovArnoldChallenge && lake build PalomarKolmogorovArnoldTypeCheck
```

Each Challenge elaborates the statement surface and reports one `declaration uses 'sorry'`
warning per compared theorem — five for Wyner, five for Hoeffding, three for
Kolmogorov–Arnold. Any other warning or error is a problem. Each TypeCheck reports nothing
if the Challenge still matches the library.

## Submissions

| Result | Challenge | Solution module | Status |
| --- | --- | --- | --- |
| [Wyner's spherical covering exponent](Wyner/Challenge.lean) | `Palomar.Wyner.Challenge` | `MiscMath.Geometry.SphereCoveringExponent` | registered, `PALOMAR-2026-08-23-000001` |
| [Hoeffding's extrema at a fixed mean](Hoeffding/Challenge.lean) | `Palomar.Hoeffding.Challenge` | `MiscMath.Probability.PoissonTrialsFixedMean` | registered, `PALOMAR-2026-09-07-000011` |
| [The Kolmogorov–Arnold representation theorem](KolmogorovArnold/Challenge.lean) | `Palomar.KolmogorovArnold.Challenge` | `MiscMath.Analysis.KolmogorovArnold` | registered, `PALOMAR-2026-09-11-000002` |

## Where this work lives

Palomar accepts **only public GitHub repositories** — its specification lists
private-repository support as future work — so a submission cannot be prepared in a
private mirror and submitted from there. What it does not require is that the commit sit
on the default branch: the form takes a full 40-character SHA, and the specification is
explicit that the pinned mechanical report, "not the run title or moving branch state", is
the authoritative result. A public branch is therefore enough, and is where each
submission starts, so that `main` carries none of it until that submission proves itself.
Wyner's has: it registered on 2026-08-23 and was folded into `main` afterwards, which is
the end state the first bullet below recommends. Hoeffding's took the same route:
prepared on `palomar-hoeffding`, rejected once at `dependency-provenance` for a Mathlib pin
that was not an ancestor of master, resubmitted, registered on 2026-09-07 and folded in.
Kolmogorov–Arnold's took the same route, on `palomar-kolmogorov-arnold`: its first
submission, at `ce03fc3`, passed mechanical verification and came back from the editorial
review with three prose corrections and no Lean change — a "only strengthenings" account of
the departures from the sources that ignored the omitted normalisation and independence
clauses, an unclear statement of what an earlier machine review had inspected, and an `n = 1`
witness `g = f/3` that is not continuous off the cube — corrected in `7a3052c`, which was
resubmitted, registered on 2026-09-11 as `PALOMAR-2026-09-11-000002`, and folded into `main`
by a plain merge, so that both submitted commits stay reachable. Its development repository
is a separate matter, discussed at the end of this section.

Two consequences worth remembering:

- **Do not delete the branch while a submission is outstanding.** The commit has to stay
  reachable for Palomar to fetch it. Only on registration does Palomar preserve the
  repository as a native fork under `PalomarArchive` with an immutable, ruleset-protected
  tag on the registered commit; before that, reachability is on us. After registration,
  merging the branch to `main` is the tidier end state — availability monitoring checks
  the original commit as well as the preserved one.
- **Abandoning costs nothing public.** The repository, commit and mechanical logs become a
  permanent public record from verification onward, but the editorial review and its
  outcome stay private unless we choose to register. A rejection is not published, and a
  submission can be withdrawn from any non-terminal state, which "leaves no public
  editorial outcome". If we drop the idea, the branch goes away and `main` never carried
  it.

One more, for a result that was developed elsewhere and copied in, as Kolmogorov–Arnold
was. The registry entry points at *this* repository, not at the development repository,
and that choice is sticky: Palomar's `CONTRIBUTING.md` requires every later version of an
entry — a Mathlib bump, a correction — to come from the same source repository, project
path and Comparator path, and a repository transfer needs operator review. This is the
repository that produces those versions, the copy under the audit and the release
discipline, and the copy a citation names; the development repository is kept as the
development it was built in, not as a release vehicle. It is disclosed instead under
`related_formalizations`, as the development the result was built in, and the roof's
`## Provenance` links to it — so it must be public before the submission goes in, or the
review meets a link it cannot follow. Palomar does not archive it from a submission here,
since it is neither a dependency nor a thin wrapper's substantive formalisation; that
arrangement is for a wrapper that *depends* on the development, which this library does
not, because its audit does not walk a dependency's declarations.

## The Mathlib pin must be an ancestor of `master`

Check this before every submission. It is the one precondition that fails silently in
advance and expensively at submission time.

Palomar's `dependency-provenance` stage rejects a submission whose pinned Mathlib revision
is not an ancestor of Mathlib's canonical `refs/heads/master`. The rejection is
`submission.invalid`, marked neither repairable nor retryable, and it lands *before*
anything is compiled — no Comparator run, no NanoDa replay, nothing learned about the
mathematics. The only remedy is a new commit and a new submission.

Which Mathlib tags qualify is not obvious from their names:

| Kind | Example | Ancestor of `master`? |
| --- | --- | --- |
| Minor release | `v4.33.0` | yes — cut on master through a pull request |
| Release candidate | `v4.34.0-rc2` | yes — likewise |
| **Patch release** | `v4.33.1` | **no** — cut on a release branch |

A patch release carries commits master has never seen; `v4.33.1` diverges from master by
one. Its subject line is the tell: minor releases and candidates end in a PR number,
patch releases do not.

This cost submission `eic7zf34a9x8` on 2026-09-07, which was pinned to `v4.33.1` after a
bump to the newest stable tag. The pin is back on `v4.33.0`, and `lakefile.toml` says why.
To check a candidate pin before relying on it:

```bash
gh api "repos/leanprover-community/mathlib4/compare/master...<sha>" --jq '.status'
```

`behind` or `identical` is fine; `diverged` is not.

## Submitting

At <https://submit.palomar-registry.org/>, with:

| Field | Value |
| --- | --- |
| Repository | `geoconuk/lean-misc-math` |
| Commit | the full 40-character SHA to be reviewed — not a branch or tag |
| Comparator configuration path | `Palomar/<Result>/comparator.json` |
| Project directory | leave empty (the project is the repository root) |
| Metadata path | `Palomar/<Result>/formalization.yaml` |
| Relationship | author/maintainer |

Submission requires GitHub sign-in to prove push access; the token is used once and not
stored. The repository, commit and configuration become a permanent public record from
verification onward, but the review and its outcome stay private unless you choose to
register. A later Mathlib bump is resubmitted as a new version under the same Palomar ID.
