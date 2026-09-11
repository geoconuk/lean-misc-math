/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# The Kolmogorov–Arnold representation theorem — advertised statements

This is the statement surface of the submission: the declarations a mathematical reader is
asked to audit. The proofs are in `MiscMath.Analysis.KolmogorovArnold`, which is the Solution
module of the accompanying Comparator configuration and is the file the library actually
ships; its own proof rests on twelve support modules beneath it. The `sorry`s below are the
deliberate holes Comparator fills.

Every continuous function on the `n`-cube is a superposition `∑_q g (∑_p λ_p ψ_q (x_p))` of a
single continuous outer function `g`, which depends on `f`, with continuous strictly
increasing inner functions `ψ_q` and positive constants `λ_p` that depend only on `n`. Three
statements, each implying the next, named for who is credited with the *statement* (not for
the proof route): the Lorentz–Sprecher form, which the proof establishes; Lorentz's form; and
Kolmogorov's, which carries the plain name because it is the theorem as proved in 1957 and as
usually cited.

## Informal statement

Fix `n`. Write `[0,1]ⁿ` for the closed unit cube.

**Lorentz–Sprecher form** (`kolmogorov_arnold_lorentz_sprecher`). There are positive
constants `λ₁, …, λₙ` and continuous strictly increasing functions `ψ₀, …, ψ₂ₙ : ℝ → ℝ`, all
depending only on `n`, such that every function `f` continuous on `[0,1]ⁿ` can be written
`f(x) = ∑_{q=0}^{2n} g(∑_{p=1}^{n} λ_p ψ_q(x_p))` on the cube, for some continuous
`g : ℝ → ℝ` depending on `f`.

**Lorentz's form** (`kolmogorov_arnold_lorentz`). There are continuous monotone increasing
`φ_{q,p} : ℝ → ℝ` (`q = 0, …, 2n`; `p = 1, …, n`) depending only on `n` such that every `f`
continuous on `[0,1]ⁿ` is `f(x) = ∑_{q=0}^{2n} Φ(∑_{p=1}^{n} φ_{q,p}(x_p))` on the cube for
some continuous `Φ : ℝ → ℝ`.

**Kolmogorov's form** (`kolmogorov_arnold`). As above but with `2n + 1` outer
functions: `f(x) = ∑_{q=0}^{2n} Φ_q(∑_{p=1}^{n} φ_{q,p}(x_p))`.

In every form the inner functions are quantified **before** `f`: one family serves every
`f`. That is the content of the theorem, and it is what distinguishes these statements from
the weaker `∀ f, ∃ φ` form that the `lean-eval` benchmark poses.

The statements are made for every `n`. The literature states `n ≥ 2`; the cases `n = 0`
and `n = 1` are true and trivial (`n = 1`: take `λ = 1`, every inner function the identity,
and `g` one third of a continuous extension of `f` from `[0,1]` to `ℝ` — `f ∘ clamp / 3` in
the Solution's sanity check; `f/3` itself need not be continuous off the cube).

## How to read these statements

Every statement below is written in Mathlib's vocabulary alone — `Continuous`,
`ContinuousOn`, `StrictMono`, `Monotone`, `Set.Icc` and finite sums — with no definition of
its own, so that each claim can be audited against the informal statement above without
first accepting a definition. Five things are worth knowing.

* **The cube.** `Icc (0 : Fin n → ℝ) 1` is the closed unit cube `[0,1]ⁿ`: the order on
  `Fin n → ℝ` is coordinatewise, so `x ∈ Icc 0 1` says exactly `0 ≤ x p ≤ 1` for every `p`.
  `f : (Fin n → ℝ) → ℝ` is asked to be continuous on the cube only (`ContinuousOn`), and the
  representation is asserted on the cube only.
* **The quantifier order.** `lam` and `ψ` (or `φ`) are bound *outside* the `∀ f`, and the
  outer function `g` (or `Φ`) *inside* it. The inner functions are universal for the
  dimension; only the outer function depends on `f`.
* **The indexing.** `Fin (2 * n + 1)` indexes the `2n + 1` outer terms, `Fin n` the
  coordinates. At `n = 2` the sum has five terms, at `n = 3` seven.
* **The inner functions live on all of `ℝ`.** They are continuous — and, where a form asks
  it, monotone — on the whole line, not just on `[0,1]`: a strengthening of the sources, which
  state them on `[0,1]` (extend linearly outside the interval). Likewise the outer function is
  continuous on `ℝ`, as in Hedberg's statement; the others place it on a compact interval.
* **There are no hypotheses beyond `n`.** Each statement is an existential, and the one
  assumption inside it — that `f` be continuous on the cube — is met by every polynomial, so
  there is no satisfiability witness to give; the guard an existence statement needs instead
  is that the conjunction of conditions asked for is satisfiable in a non-degenerate way. The
  Solution
  module proves the `n = 1` case of the Lorentz–Sprecher form outright, with no appeal to
  the theorem, and separates the three forms at the level of witnesses: at `n = 1` there is
  an inner family that witnesses Kolmogorov's form but admits no single outer function, and
  one that witnesses Lorentz's form but is not `λ_p ψ_q` with `λ_p > 0` and `ψ_q` strictly
  increasing. Those `example`s are not compared here; a reviewer will find them under
  `## Sanity checks` in the Solution module.

## Source

All five primaries were read on 2026-09-10 and each Lean statement compared against them.
What each states:

- **Kolmogorov**, *On the representation of continuous functions of several variables by
  superposition of continuous functions of one variable and addition*, Dokl. Akad. Nauk SSSR
  114 (1957) 953–956. Theorem: for `n ≥ 2` there are continuous real `ψ^{pq}` on `[0,1]` such
  that every continuous real `f` on the cube is `∑_{q=1}^{2n+1} χ_q(∑_p ψ^{pq}(x_p))` with the
  `χ_q` real and continuous. **No monotonicity in the statement**; a remark after his Lemma 3
  says the constructed `ψ^{pq}` are monotonically increasing and "this property could have been
  included in the formulation." `kolmogorov_arnold` follows the statement, not the remark.
- **Lorentz**, *Metric entropy, widths, and superpositions of functions*, Amer. Math. Monthly
  69 (1962) 469–485, Theorem 7 and (3): **continuous monotone increasing** inner functions
  with values in `[0,1]`, indexed by both `p` and `q` (not factored), and a **single** outer
  function continuous on `[0,s]`. `kolmogorov_arnold_lorentz` carries his monotonicity clause.
  His footnote: Kolmogorov's `2s+1` outer functions versus one is "only apparently weaker …
  in fact equivalent."
- **Sprecher**, *On the structure of continuous functions of several variables*, Trans. Amer.
  Math. Soc. 115 (1965) 340–355, Theorem 1: a single **monotonic increasing** `ψ` of class
  `Lip[ln 2 / ln(2N+2)]` — Hölder, with exponent below `1` — and the shift form
  `∑_{q=0}^{2n} χ(∑_p λ^p ψ(x_p + εq) + q)`; the powers `λ^p` may be replaced by any
  rationally independent `λ_p`. The factored form `λ_p ψ_q` is a corollary
  (`ψ_q(x) := ψ(x + εq) + q/∑λ_p`). Sprecher credits the single outer function to Lorentz.
- **Hedberg**, *The Kolmogorov superposition theorem*, Appendix II to H. S. Shapiro, *Topics
  in Approximation Theory*, Lecture Notes in Math. 187, Springer, 1971, 267–275, Theorem 1:
  `∑_{k=1}^{2n+1} g(∑_p λ_p φ_k(x_p))` with `φ_k ∈ C(I)`, ℚ-independent real `λ_p`, and
  **`g ∈ C(ℝ)`** — exactly the shape of `kolmogorov_arnold_lorentz_sprecher`. Remark 2: the
  `φ_k` can be taken **non-decreasing** by running the Baire argument in that closed subspace.
- **Kahane**, *Sur le théorème de superposition de Kolmogorov*, J. Approx. Theory 13 (1975)
  229–234, (5): the same form, with `Φ` the space of **increasing** continuous `φ : I → I`,
  `φ(0) = 0`, `φ(1) = 1`, `λ_p` distinct, positive, summing to 1, `g` continuous on `I`; and
  the remark (p. 231) that **quasi-every `φ ∈ Φ` is strictly increasing**. Kahane credits the
  factoring to Sprecher and the single outer function to Lorentz's book (1966, Ch. 11).

**Monotonicity, precisely.** Of the five primaries, every stated theorem that has it states
it *weakly*: Lorentz "monotone increasing", Sprecher "monotonic increasing", Hedberg
"non-decreasing", Kahane "croissantes". `kolmogorov_arnold_lorentz` therefore says
`Monotone`. The `StrictMono` in `kolmogorov_arnold_lorentz_sprecher` is **stronger than any
of the five stated theorems** and is a deliberate strengthening, sourced to Kahane's remark:
strictly increasing functions are a dense `Gδ` in the non-decreasing space, so the residual
set of good tuples meets them. It excludes constant inner functions. The refinement is not
new to the literature: S. A. Morris, *Hilbert 13: Are there any genuine continuous
multivariate real-valued functions?*, Bull. Amer. Math. Soc. 58 (2021) 107–118, Theorem 4.2,
states this exact shape — single `g`, factored `λ_p φ_k`, `n ≥ 2` — with strictly increasing
continuous inner functions, citing Hedberg for the strictness; the argument that yields it is
Kahane's. Morris is not among the five primaries the statements were read against.

**Other departures, all deliberate, in both directions.** Strengthened: statements for
every `n` (the sources: `n ≥ 2`; `n ≤ 1` is true and trivial); inner functions continuous on
all of `ℝ` rather than on `[0,1]`; outer function continuous on `ℝ`. Omitted: the conditions
the sources place on the objects they construct — Kahane's `φ(0) = 0`, `φ(1) = 1`, values in
`[0,1]` and `λ_p` distinct with `∑λ_p = 1`; Hedberg's ℚ-independence of the `λ_p`; Lorentz's
values in `[0,1]`; Sprecher's Hölder class. They are proof devices, and the conclusions here
neither assert nor imply them — the Lorentz–Sprecher form says nothing of the `λ_p` beyond
positivity. An existential conclusion that omits a conjunct is weaker in that respect, so
against each source's own formulation the statements here strengthen some clauses and omit
others, and neither contains the other as stated. The exception is Kolmogorov's: his
statement carries no condition beyond continuity, and `kolmogorov_arnold` strengthens it and
omits nothing. What all three match is the theorem as it is usually cited, which carries none
of the omitted conditions.

**Not targeted:** Sprecher's shift form above, as corrected by Köppen (2002) and
Braun–Griebel, Constr. Approx. 30 (2009), Thm 2.14. It is what "Sprecher's version" usually
means, which is why the name is `_lorentz_sprecher` and not `_sprecher` alone. The `n = 2`
instance in factored form has the shape of the theorem of S. Dzhenzher and A. Skopenkov,
*A structured proof of Kolmogorov's Superposition Theorem*, arXiv:2105.00408, who fix the
weights as `1` and `√2` and take continuous `φ_k : [0,1] → [0,1]`; ours asserts only
positivity of the weights and, in return, strictness of the `ψ_q`, so neither statement
contains the other.

## Relation to Mathlib

Nothing in Mathlib states or approaches this theorem, nor, when surveyed for this
development, anything in Tau Ceti. The statements use only `Continuous`, `ContinuousOn`,
`StrictMono`, `Monotone`, `Set.Icc` on `Fin n → ℝ` and finite sums, which is why this
Challenge imports nothing but Mathlib. The only other public Lean artefact known to us is
the statement, without proof, of the weaker `∀ f, ∃ g φ` form in `leanprover/lean-eval`.
-/

open Set

namespace MiscMath.Analysis

/-- **Kolmogorov–Arnold, Lorentz–Sprecher form.** Positive constants `λ_p` and continuous
strictly increasing `ψ_q : ℝ → ℝ`, depending only on `n`, such that every `f` continuous on
the cube is `∑_q g (∑_p λ_p ψ_q (x_p))` for some continuous `g`. Lorentz's single outer
function and Sprecher's factored inner functions, in the shape of Hedberg's Theorem 1 and
Kahane's (5); strict rather than weak monotonicity per Kahane's remark that quasi-every
increasing `φ` is strictly increasing. The strongest statement here and the one the
development proves. -/
theorem kolmogorov_arnold_lorentz_sprecher (n : ℕ) :
    ∃ (lam : Fin n → ℝ) (ψ : Fin (2 * n + 1) → ℝ → ℝ),
      (∀ p, 0 < lam p) ∧
      (∀ q, Continuous (ψ q)) ∧
      (∀ q, StrictMono (ψ q)) ∧
      ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ g : ℝ → ℝ, Continuous g ∧
          ∀ x ∈ Icc (0 : Fin n → ℝ) 1, f x = ∑ q, g (∑ p, lam p * ψ q (x p)) := by
  sorry

/-- **Kolmogorov–Arnold, Lorentz's form.** Continuous monotone increasing `φ_{q,p} : ℝ → ℝ`
depending only on `n` such that every `f` continuous on the cube is
`∑_q Φ (∑_p φ_{q,p} (x_p))` for a single continuous `Φ`. Lorentz (1962), Theorem 7 and (3),
whose statement includes the monotonicity. Derived from the Lorentz–Sprecher form by
`φ_{q,p} := λ_p • ψ_q`. -/
theorem kolmogorov_arnold_lorentz (n : ℕ) :
    ∃ φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ,
      (∀ q p, Continuous (φ q p)) ∧
      (∀ q p, Monotone (φ q p)) ∧
      ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ Φ : ℝ → ℝ, Continuous Φ ∧
          ∀ x ∈ Icc (0 : Fin n → ℝ) 1, f x = ∑ q, Φ (∑ p, φ q p (x p)) := by
  sorry

/-- **Kolmogorov–Arnold representation theorem** (Kolmogorov 1957). Continuous
`φ_{q,p} : ℝ → ℝ` depending only on `n` such that every `f` continuous on the cube is
`∑_q Φ_q (∑_p φ_{q,p} (x_p))` for continuous `Φ_q`. The theorem as originally proved and as
usually cited, hence the plain name. Follows from Lorentz's form by taking every `Φ_q` to be
the single `Φ`. -/
theorem kolmogorov_arnold (n : ℕ) :
    ∃ φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ,
      (∀ q p, Continuous (φ q p)) ∧
      ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ Φ : Fin (2 * n + 1) → ℝ → ℝ, (∀ q, Continuous (Φ q)) ∧
          ∀ x ∈ Icc (0 : Fin n → ℝ) 1, f x = ∑ q, Φ q (∑ p, φ q p (x p)) := by
  sorry

end MiscMath.Analysis
