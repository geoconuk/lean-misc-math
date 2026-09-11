/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.Extend
import MiscMath.Analysis.KolmogorovArnold.Representation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# The Kolmogorov–Arnold representation theorem

The theorem stated on all of `ℝ`, in three forms, each proved. Every continuous function on
the `n`-cube is a superposition `∑_q g (∑_p λ_p ψ_q (x_p))` of a single continuous outer
function `g`, which depends on `f`, with continuous strictly increasing inner functions `ψ_q`
and positive constants `λ_p` that depend only on `n`.

Three statements, each implying the next, named for who is credited with the *statement*
(not for the proof route): the Lorentz–Sprecher form, which the proof establishes; Lorentz's
form; and Kolmogorov's, which carries the plain name because it is the theorem as proved in
1957 and as usually cited. The two implications are proved here, and they are the whole
content of "stronger" at the level of theorems — all three are true, so as closed propositions
they are equivalent, and no claim of strictness between them is made or could be. What *is*
shown, in the sanity checks, is that each refinement is a genuine extra demand on the inner
functions: at `n = 1` there is an inner family that witnesses Kolmogorov's form but not
Lorentz's, and one that witnesses Lorentz's but is not of Lorentz–Sprecher shape.

**The proof** is the Baire-category argument of Hedberg (1971) and Kahane (1975), built in the
support modules under `MiscMath/Analysis/KolmogorovArnold/`. On the space of `(2n+1)`-tuples
of monotone continuous functions `[0,1] → ℝ` (`InnerSpace`), the tuples admitting a one-step
approximation of a given `f` form an open set (`Superposition`) which is dense (`Density`,
resting on Hedberg's red intervals in `Cells`, the staircase approximants of `Staircase` and
`Approximant`, and the rational levels of `Levels`, whose cell map is injective by the rational
independence of the `λ_p` from `RationalIndependence`). Intersecting over a countable dense set
of `f` and with the dense `Gδ` of strictly increasing tuples (`StrictlyIncreasing`) gives one
tuple that approximates every `f` in one step (`Generic`); iterating on the residual and
summing the geometric series gives exact representation on the cube (`Representation`).
`Extend` extends the inner functions from `[0,1]` to `ℝ` by `ψ(clamp t) + (t - clamp t)`, which
keeps them continuous and strictly increasing, and this module reads the representation back
on the cube.

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
and `n = 1` are true and trivial (`n = 1`: take every inner function to be the identity and
`g = f/3`), and the sanity checks below prove `n = 1` directly, without the theorem.

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
  `Lip[ln 2 / ln(2N+2)]` — Hölder, with exponent below `1`: his footnote 2 defines the class
  by `|ψ(x) − ψ(y)| ≤ c |x − y|^α`, and p. 343 notes that a `ψ` meeting his condition (1.7)
  cannot be in `Lip[1]` — and the shift form `∑_{q=0}^{2n} χ(∑_p λ^p ψ(x_p + εq) + q)`; the
  powers `λ^p` may be replaced by any rationally independent `λ_p`. The factored form
  `λ_p ψ_q` is a corollary (`ψ_q(x) := ψ(x + εq) + q/∑λ_p`). Sprecher credits the single
  outer function to Lorentz.
- **Hedberg**, *The Kolmogorov superposition theorem*, Appendix II to H. S. Shapiro, *Topics
  in Approximation Theory*, Lecture Notes in Math. 187, Springer, 1971, 267–275, Theorem 1:
  `∑_{k=1}^{2n+1} g(∑_p λ_p φ_k(x_p))` with `φ_k ∈ C(I)`, ℚ-independent real `λ_p`, and
  **`g ∈ C(ℝ)`** — exactly the shape of `kolmogorov_arnold_lorentz_sprecher`. Remark 2: the
  `φ_k` can be taken **non-decreasing** by running the Baire argument in that closed subspace.
- **Kahane**, *Sur le théorème de superposition de Kolmogorov*, J. Approx. Theory 13 (1975)
  229–234, (5): the same form, with `Φ` the space of **increasing** continuous `φ : I → I`,
  `φ(0) = 0`, `φ(1) = 1`, `λ_p` distinct, positive, summing to 1, `g` continuous on `I`; and
  the remark (p. 231) that **quasi-every `φ ∈ Φ` is strictly increasing**, since for rationals
  `ρ < ρ'` the set `{φ : φ(ρ+0) < φ(ρ'−0)}` is open and dense. Kahane credits the factoring
  to Sprecher and the single outer function to Lorentz's book (1966, Ch. 11).

**Monotonicity, precisely.** Of the five primaries, every stated theorem that has it states
it *weakly*: Lorentz "monotone increasing", Sprecher "monotonic increasing", Hedberg
"non-decreasing", Kahane "croissantes". `kolmogorov_arnold_lorentz` therefore says
`Monotone`. The `StrictMono` in `kolmogorov_arnold_lorentz_sprecher` is **stronger than any
of the five stated theorems** and is kept as a deliberate strengthening, sourced to Kahane's
remark: strictly increasing functions are a dense `Gδ` in the non-decreasing space, so the
residual set of good tuples meets them. It costs one lemma and excludes constant inner
functions. Decision by George, 2026-09-10. The refinement is not new to the literature:
S. A. Morris, *Hilbert 13: Are there any genuine continuous multivariate real-valued
functions?*, Bull. Amer. Math. Soc. 58 (2021) 107–118, Theorem 4.2, states this exact shape
— single `g`, factored `λ_p φ_k`, `n ≥ 2` — with strictly increasing continuous inner
functions, citing Hedberg pp. 272–273 for the strictness, where Hedberg's Remark 2 obtains
non-decreasing components; the argument that yields strictness is Kahane's. Morris was
checked on 2026-09-11 and is not among the five primaries the statements were read against.

Other departures, all strengthenings and all deliberate: statements for every `n` (the
sources: `n ≥ 2`; `n ≤ 1` is true and trivial); inner functions continuous on all of `ℝ`
rather than on `[0,1]` (extend linearly, which preserves monotonicity); outer function
continuous on `ℝ` (Hedberg states it so; the others use a compact interval — Tietze). The
sources' normalisations — `φ(0) = 0`, `φ(1) = 1`, values in `[0,1]`, `∑λ_p = 1`,
ℚ-independence of the `λ_p` — are proof devices and are not claimed. The `n = 2` instance in
factored form has the shape of the theorem of S. Dzhenzher and A. Skopenkov, *A structured
proof of Kolmogorov's Superposition Theorem*, arXiv:2105.00408, who fix the weights as `1`
and `√2` and take continuous `φ_k : [0,1] → [0,1]`; ours asserts only positivity of the
weights and, in return, strictness of the `ψ_q`, so neither statement contains the other.

Not targeted: Sprecher's shift form above, as corrected by Köppen (2002) and Braun–Griebel,
Constr. Approx. 30 (2009), Thm 2.14. It is what "Sprecher's version" usually means, which is
why the name is `_lorentz_sprecher` and not `_sprecher` alone.

## Provenance

Result selected and specified by George A. Constantinides, who has read its advertised
statements — `kolmogorov_arnold_lorentz_sprecher`, `kolmogorov_arnold_lorentz` and
`kolmogorov_arnold`, stated in Mathlib's vocabulary alone — against the informal claim above
and against the five primaries themselves on a best-effort basis, on 2026-09-10. The
statements were fixed and read *before* any of the proof was built: the development, in the
repository `github.com/geoconuk/kolmogorov-arnold`, was carried out against them as a fixed
target, and the statements here are those statements, unchanged. The statements and their
proofs were generated by Claude, and are kernel-verified and axiom-audited; the proofs are
read by nobody. Every other declaration in this file and in the modules under
`MiscMath/Analysis/KolmogorovArnold/` is proof, and may be read by no one. A best-effort read
is not a review — satisfy yourself that the statement says what you need before relying on
it. See the repository README.

Before that read, the three advertised statements were read back blind: each rendered into
English by an agent given it and nothing else — no informal statement, no source, no
docstring. All three renderings fixed the quantifier order, the single versus indexed outer
function, the factored versus general inner functions and the `n = 0` instance unprompted,
and agreed with the informal account above. One observation was passed on for the read: the
Lorentz–Sprecher form asserts nothing about the `λ_p` beyond positivity — their rational
independence is a proof device, not a claim. The monotonicity clause of Lorentz's form, added
after the comparison with the primaries, had a read-back of its own, which rendered it as
non-decreasing with constant inner functions admitted.

No [Palomar](https://palomar-registry.org) registration as of 2026-09-11; the entry ID and
version go here once there is one.

## Sanity checks

The derivations `kolmogorov_arnold_lorentz` and `kolmogorov_arnold` are themselves checks:
they show the Lorentz–Sprecher form is strong enough to yield the forms that are cited. The
`example`s prove the `n = 1` case of the Lorentz–Sprecher form outright, with no appeal to
the theorem, which demonstrates that the conjunction of conditions asked for in the
conclusion is satisfiable in a non-degenerate way — the guard an existence statement needs
in place of a satisfiability witness for hypotheses, of which there are none. Two further
`example`s separate the forms at the level of witnesses: the inner family `(t, 1 − t, 0)`
witnesses Kolmogorov's form but admits no single outer function (it would force
`f(0) = f(1)`), and `(t, t, 0)` — continuous, monotone, a single `Φ` serves every `f`, so a
Lorentz witness — is not `λ_p ψ_q` with `λ_p > 0` and `ψ_q` strictly increasing, because a
constant layer cannot be. So the single outer function and the strictly increasing factored
inner functions are each a real constraint, not a rewording; the second separates on exactly
the clause that is stronger than the five primaries' stated theorems.

## Relation to Mathlib

Nothing in Mathlib states or approaches this theorem. The statements use only `Continuous`,
`ContinuousOn`, `StrictMono`, `Monotone`, `Set.Icc` on `Fin n → ℝ`, and finite sums, so a
Palomar Challenge can restate them from Mathlib alone. The only other public Lean artefact
known to us is the statement, without proof, of the weaker `∀ f, ∃ g φ` form in
`leanprover/lean-eval`.
-/

open Set unitInterval

namespace MiscMath.Analysis

open KolmogorovArnold

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
  obtain ⟨lam, hlampos, hlam⟩ := exists_pos_linearIndependent_rat n
  obtain ⟨ψ, hψ, hrep⟩ := exists_universal_tuple_apply hlam
  refine ⟨lam, fun q => (ψ q).extend, hlampos, fun q => (ψ q).continuous_extend,
    fun q => (ψ q).extend_strictMono (hψ q), fun f hf => ?_⟩
  -- Restrict `f` to the cube, as a continuous map on `Fin n → I`.
  have hcoe : Continuous fun x : Fin n → I => fun p => (x p : ℝ) :=
    continuous_pi fun p => continuous_subtype_val.comp (continuous_apply p)
  have hmaps : ∀ x : Fin n → I, (fun p => (x p : ℝ)) ∈ Icc (0 : Fin n → ℝ) 1 :=
    fun x => ⟨fun p => (x p).2.1, fun p => (x p).2.2⟩
  obtain ⟨g, hg⟩ := hrep ⟨fun x => f fun p => (x p : ℝ), hf.comp_continuous hcoe hmaps⟩
  refine ⟨g, g.continuous, fun x hx => ?_⟩
  have := hg fun p => ⟨x p, hx.1 p, hx.2 p⟩
  rw [ContinuousMap.coe_mk] at this
  rw [this]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  exact ((ψ q).extend_of_mem ⟨hx.1 p, hx.2 p⟩).symm

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
  obtain ⟨lam, ψ, hlam, hψc, hψm, h⟩ := kolmogorov_arnold_lorentz_sprecher n
  refine ⟨fun q p t => lam p * ψ q t, fun q p => continuous_const.mul (hψc q), ?_, h⟩
  intro q p a b hab
  exact mul_le_mul_of_nonneg_left ((hψm q).monotone hab) (hlam p).le

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
  obtain ⟨φ, hφ, -, h⟩ := kolmogorov_arnold_lorentz n
  refine ⟨φ, hφ, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ, hrep⟩ := h f hf
  exact ⟨fun _ => Φ, fun _ => hΦ, hrep⟩

/-! ## Sanity checks -/

/-- The `n = 1` case of the Lorentz–Sprecher form, proved outright: every inner function the
identity, `λ = 1`, and `g = f ∘ clamp / 3`. Shows the conclusion's conjunction of conditions is
satisfiable without appeal to the theorem above. -/
example :
    ∃ (lam : Fin 1 → ℝ) (ψ : Fin (2 * 1 + 1) → ℝ → ℝ),
      (∀ p, 0 < lam p) ∧
      (∀ q, Continuous (ψ q)) ∧
      (∀ q, StrictMono (ψ q)) ∧
      ∀ f : (Fin 1 → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ g : ℝ → ℝ, Continuous g ∧
          ∀ x ∈ Icc (0 : Fin 1 → ℝ) 1, f x = ∑ q, g (∑ p, lam p * ψ q (x p)) := by
  refine ⟨fun _ => 1, fun _ => id, fun _ => one_pos, fun _ => continuous_id,
    fun _ => strictMono_id, fun f hf => ?_⟩
  -- Clamp into the cube, so that `f ∘ clamp` is continuous on all of `ℝ`.
  set c : ℝ → (Fin 1 → ℝ) := fun t _ => (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hc
  have hc_cont : Continuous c :=
    continuous_pi fun _ => continuous_subtype_val.comp continuous_projIcc
  have hc_maps : ∀ t, c t ∈ Icc (0 : Fin 1 → ℝ) 1 := fun t =>
    ⟨fun _ => (projIcc (0 : ℝ) 1 zero_le_one t).2.1,
     fun _ => (projIcc (0 : ℝ) 1 zero_le_one t).2.2⟩
  refine ⟨fun t => f (c t) / 3, (hf.comp_continuous hc_cont hc_maps).div_const 3, ?_⟩
  intro x hx
  have hx0 : x 0 ∈ Icc (0 : ℝ) 1 := ⟨hx.1 0, hx.2 0⟩
  have hcx : c (x 0) = x := by
    funext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [hc, projIcc_of_mem _ hx0]
  simp only [Fin.sum_univ_one, one_mul, id, hcx, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Kolmogorov's form at `n = 2`: the five-term representation of continuous functions of two
variables. Recorded so the indexing is visibly right: `2 * 2 + 1 = 5`. -/
example :
    ∃ φ : Fin 5 → Fin 2 → ℝ → ℝ,
      (∀ q p, Continuous (φ q p)) ∧
      ∀ f : (Fin 2 → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ Φ : Fin 5 → ℝ → ℝ, (∀ q, Continuous (Φ q)) ∧
          ∀ x ∈ Icc (0 : Fin 2 → ℝ) 1, f x = ∑ q, Φ q (∑ p, φ q p (x p)) :=
  kolmogorov_arnold 2

/-- Kolmogorov's form at `n = 3`: seven terms. This, not `n = 2`, is the case that bears on
Hilbert's 13th problem, which concerns functions of *three* variables: it writes every
continuous function on `[0,1]³` with continuous functions of one variable and addition, hence
with continuous functions of two variables, which Hilbert had conjectured impossible (Arnold's
1957 theorem refuted the conjecture first, with two-variable functions). -/
example :
    ∃ φ : Fin 7 → Fin 3 → ℝ → ℝ,
      (∀ q p, Continuous (φ q p)) ∧
      ∀ f : (Fin 3 → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ Φ : Fin 7 → ℝ → ℝ, (∀ q, Continuous (Φ q)) ∧
          ∀ x ∈ Icc (0 : Fin 3 → ℝ) 1, f x = ∑ q, Φ q (∑ p, φ q p (x p)) :=
  kolmogorov_arnold 3

/-- **Lorentz's form asks more of the inner functions than Kolmogorov's.** At `n = 1` the
inner family `(t, 1 − t, 0)` witnesses Kolmogorov's form — take `Φ₀ = f ∘ clamp` and
`Φ₁ = Φ₂ = 0` — but no single outer function works with it: `Φ(x) + Φ(1 − x) + Φ(0)` takes the
same value at `x = 0` and at `x = 1`, so it cannot represent `f x = x₀`. This separates on the
single outer function alone, before Lorentz's monotonicity clause is even considered. -/
example : ∃ φ : Fin 3 → Fin 1 → ℝ → ℝ,
    (∀ q p, Continuous (φ q p)) ∧
    (∀ f : (Fin 1 → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
      ∃ Φ : Fin 3 → ℝ → ℝ, (∀ q, Continuous (Φ q)) ∧
        ∀ x ∈ Icc (0 : Fin 1 → ℝ) 1, f x = ∑ q, Φ q (∑ p, φ q p (x p))) ∧
    ¬ (∀ f : (Fin 1 → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
      ∃ Φ : ℝ → ℝ, Continuous Φ ∧
        ∀ x ∈ Icc (0 : Fin 1 → ℝ) 1, f x = ∑ q, Φ (∑ p, φ q p (x p))) := by
  refine ⟨fun q _ t => if q = 0 then t else if q = 1 then 1 - t else 0, ?_, ?_, ?_⟩
  · intro q p
    dsimp only
    split_ifs <;> fun_prop
  · intro f hf
    set c : ℝ → (Fin 1 → ℝ) := fun t _ => (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hc
    have hc_cont : Continuous c :=
      continuous_pi fun _ => continuous_subtype_val.comp continuous_projIcc
    have hc_maps : ∀ t, c t ∈ Icc (0 : Fin 1 → ℝ) 1 := fun t =>
      ⟨fun _ => (projIcc (0 : ℝ) 1 zero_le_one t).2.1,
       fun _ => (projIcc (0 : ℝ) 1 zero_le_one t).2.2⟩
    refine ⟨fun q t => if q = 0 then f (c t) else 0, ?_, ?_⟩
    · intro q
      by_cases hq : q = 0
      · simp only [hq, if_true]
        exact hf.comp_continuous hc_cont hc_maps
      · simp only [hq, if_false]
        exact continuous_const
    · intro x hx
      have hx0 : x 0 ∈ Icc (0 : ℝ) 1 := ⟨hx.1 0, hx.2 0⟩
      have hcx : c (x 0) = x := by
        funext i
        obtain rfl : i = 0 := Subsingleton.elim i 0
        simp [hc, projIcc_of_mem _ hx0]
      rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 3)]
      simp [hcx]
  · intro h
    obtain ⟨Φ, -, hΦ⟩ := h (fun x => x 0) (continuous_apply 0).continuousOn
    have h0 := hΦ (fun _ => 0) ⟨fun _ => le_rfl, fun _ => zero_le_one⟩
    have h1 := hΦ (fun _ => 1) ⟨fun _ => zero_le_one, fun _ => le_rfl⟩
    simp +decide [Fin.sum_univ_three] at h0 h1
    linarith

/-- **The Lorentz–Sprecher form asks more again, and the extra is strictness.** At `n = 1`
the inner family `(t, t, 0)` is continuous and monotone, and a single `Φ` serves every `f` —
so it witnesses Lorentz's form — but it is not of the shape `λ_p ψ_q` with `λ_p > 0` and `ψ_q`
strictly increasing, because the constant layer would force `ψ₂ ≡ 0`. (Under weak
monotonicity it *would* be of that shape, which is why strictness is the clause that
distinguishes the two forms.) -/
example : ∃ φ : Fin 3 → Fin 1 → ℝ → ℝ,
    (∀ q p, Continuous (φ q p)) ∧
    (∀ q p, Monotone (φ q p)) ∧
    (∀ f : (Fin 1 → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
      ∃ Φ : ℝ → ℝ, Continuous Φ ∧
        ∀ x ∈ Icc (0 : Fin 1 → ℝ) 1, f x = ∑ q, Φ (∑ p, φ q p (x p))) ∧
    ¬ ∃ (lam : Fin 1 → ℝ) (ψ : Fin 3 → ℝ → ℝ),
        (∀ p, 0 < lam p) ∧ (∀ q, StrictMono (ψ q)) ∧ ∀ q p t, φ q p t = lam p * ψ q t := by
  refine ⟨fun q _ t => if q = 2 then 0 else t, ?_, ?_, ?_, ?_⟩
  · intro q p
    dsimp only
    split_ifs <;> fun_prop
  · intro q p
    dsimp only
    split_ifs
    · exact monotone_const
    · exact monotone_id
  · intro f hf
    set c : ℝ → (Fin 1 → ℝ) := fun t _ => (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) with hc
    have hc_cont : Continuous c :=
      continuous_pi fun _ => continuous_subtype_val.comp continuous_projIcc
    have hc_maps : ∀ t, c t ∈ Icc (0 : Fin 1 → ℝ) 1 := fun t =>
      ⟨fun _ => (projIcc (0 : ℝ) 1 zero_le_one t).2.1,
       fun _ => (projIcc (0 : ℝ) 1 zero_le_one t).2.2⟩
    -- `Φ t = (f(clamp t) − f(0)/3) / 2`; on the cube `2Φ(x₀) + Φ(0) = f(x) − f(0)/3 + f(0)/3`.
    set f0 : ℝ := f (fun _ => 0) with hf0
    refine ⟨fun t => (f (c t) - f0 / 3) / 2, ?_, ?_⟩
    · exact ((hf.comp_continuous hc_cont hc_maps).sub continuous_const).div_const 2
    · intro x hx
      have hx0 : x 0 ∈ Icc (0 : ℝ) 1 := ⟨hx.1 0, hx.2 0⟩
      have hcx : c (x 0) = x := by
        funext i
        obtain rfl : i = 0 := Subsingleton.elim i 0
        simp [hc, projIcc_of_mem _ hx0]
      have hc0 : c 0 = fun _ => 0 := by
        funext i
        simp [hc]
      simp +decide only [Fin.sum_univ_three, Fin.sum_univ_one, if_true, if_false,
        Fin.isValue]
      rw [hcx, hc0, ← hf0]
      ring
  · rintro ⟨lam, ψ, hlam, hψ, h⟩
    have e0 : (0 : ℝ) = lam 0 * ψ 2 0 := by simpa using h 2 0 0
    have e1 : (0 : ℝ) = lam 0 * ψ 2 1 := by simpa using h 2 0 1
    have hmono : ψ 2 0 < ψ 2 1 := hψ 2 zero_lt_one
    have hl : 0 < lam 0 := hlam 0
    linarith [mul_lt_mul_of_pos_left hmono hl]

end MiscMath.Analysis
