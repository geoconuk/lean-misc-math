/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/

import MiscMath.Probability.PoissonTrialsFixedMean.Bridge
import MiscMath.Probability.PoissonTrialsFixedMean.TailBounds


/-!
# The extremes of the number of successes in independent trials, at a fixed mean

## Informal statement

Consider `n` independent trials, the `j`-th succeeding with probability `p j` — what
Hoeffding calls *Poisson trials* — and let `S` be the number of successes. Fix the mean
`lam = ∑ j, p j`, and write `p̄ = lam / n` for the common success probability of the
homogeneous trials with the same mean. Three statements about how `S` varies over all
`p ∈ [0,1]ⁿ` with that mean:

1. **The binomial maximises `E[g S]` for grid-convex `g`** (Hoeffding's Theorem 3). If
   `g (k+2) - 2 g (k+1) + g k ≥ 0` for every `k` with `k + 2 ≤ n`, then

       E[g S] ≤ ∑_{k ≤ n} g k · C(n,k) · p̄^k (1 - p̄)^(n-k),

   the right-hand side being the same expectation for `n` identical trials at `p̄`. Under
   *strict* grid convexity, equality holds exactly when every `p j` equals `p̄`.

2. **The extrema have at most one interior value** (Hoeffding's Corollary 2.1). For an
   arbitrary `g`, with no convexity assumed, the maximum and the minimum of `E[g S]` over
   the fixed-mean box are attained at points whose coordinates take at most three distinct
   values, at most one of which is other than `0` and `1`.

3. **The tail is extremised by the binomial, away from the mean** (Hoeffding's Theorem 4,
   two of its three regimes). Writing `B(k; n, P) = P[Bin(n,P) ≤ k]`,

       k ≥ lam      ⟹  B(k; n, p̄) ≤ P[S ≤ k] ≤ 1,
       k ≤ lam - 1  ⟹  0 ≤ P[S ≤ k] ≤ B(k; n, p̄).

   So among all trial vectors with the given mean, the homogeneous one has the *lightest*
   lower tail at thresholds `k ≥ lam` and the *heaviest* at thresholds `k ≤ lam - 1`. All
   four bounds are attained. Note that the second regime is `k ≤ lam - 1` and not `k < lam`:
   the two differ on the gap below, and `thm4_lower_needs_le_sub_one` exhibits a point of it
   where the comparison reverses, so the narrower reading is the true one.

Everything is stated for an arbitrary finite index set `s : Finset ι` with `n = #s`, rather
than for `range n`. `hoeffding_thm4_range` restates Theorem 4 on `range n`, the form in which
it is usually quoted; Theorem 3 and Corollary 2.1 are given only in the general form, which
specialises to `range n` by `Finset.card_range`.

**Degenerate cases, not excluded by hypothesis.** At `s = ∅` the common probability
`lam / #s` is `0 / 0 = 0` and every statement below is true but empty: both sides of
Theorem 3 collapse to `g 0`, and Theorem 4's first regime to `1 ≤ 1`. Theorem 4's second
regime is vacuous whenever `lam < 1`, since `k` is a natural number and the regime asks
for `k ≤ lam - 1`; the sanity checks exhibit a point of it rather than leaving that to
chance. Neither degeneracy is ruled out, so a reader should know they are there.

## Source

W. Hoeffding, *On the distribution of the number of successes in independent trials*,
Annals of Mathematical Statistics **27** (1956), 713-721.

* Theorem 3 is p. 717, equations (22)-(23).
* Corollary 2.1 is p. 717, following Theorem 2.
* Theorem 4 is p. 718, equations (24)-(29).

**What is formalised, and what is not.** This matters more than usual here, because the
paper's Theorem 4 has three regimes and only two of them are below.

* Theorem 3 — formalised in full, and the inequality is proved under a *weaker* hypothesis
  than the paper's: Hoeffding assumes strict grid convexity throughout, but strictness is
  needed only for the equality clause. `hoeffding_thm3` therefore asks for `0 ≤ Δ²g` and
  `hoeffding_thm3_eq_iff` for `0 < Δ²g`; `hoeffding_thm3_eq_needs_strict` shows the split
  is forced.
* Corollary 2.1 — formalised in full, in both directions.
* Theorem 4 — the upper bound of (24), the lower bound of (26), and the trivial bounds
  `0 ≤ P[S ≤ c]` and `P[S ≤ c] ≤ 1` that accompany them, together with the paper's
  assertion that all of these bounds are attained.

  **Not formalised**, and in the first case not merely unattempted — the gap is where the
  looser reading of the second regime is actually false, which is what forces the
  hypothesis `c ≤ np - 1` rather than `c < np` (`thm4_lower_needs_le_sub_one`):
  equation (25), the middle regime `np - 1 < c < np`, whose bound is
  the auxiliary quantity `Q(c,p) = max_{0 ≤ s ≤ c} ∑_{k ≤ c-s} C(n-s,k) a^k (1-a)^(n-s-k)`
  with `a = (np-s)/(n-s)`; equation (29), which locates the maximising `s`; and the
  *uniqueness* half of the attainment statement ("attained only if `p₁ = ⋯ = pₙ = p`").

  The scope of what is missing is itself pinned down. Since `c` is an integer and the
  middle regime is an open interval of length `1`, it contains at most one integer
  (`thm4_gap_subsingleton`), which is `⌊lam⌋` (`thm4_gap_eq_floor`), and it contains none
  at all when the mean is a whole number (`thm4_gap_empty_of_natCast`). So the two regimes
  below cover every threshold except at most one, and cover all of them whenever `lam ∈ ℕ`.
* Theorems 1 and 2 of the paper are not formalised. Theorem 1 gives first-order conditions at
  an extremum; Theorem 2 characterises the set on which one is attained, and Corollary 2.1 is
  an immediate corollary of its part (i) (p. 717). The route taken here reaches Corollary 2.1
  differently, by a terminating exchange argument, so neither is needed.
* Theorem 5 — the two-sided `∑_{b ≤ k ≤ c} C(n,k) p̄^k (1-p̄)^(n-k) ≤ P[b ≤ S ≤ c] ≤ 1` for
  `0 ≤ b ≤ np ≤ c ≤ n` — is omitted by choice rather than by obstacle. Its *inequality* is a
  subtraction away from what is proved below, since `P[b ≤ S ≤ c] = P[S ≤ c] - P[S ≤ b-1]`
  and `binTail_le_tailLe` and `tailLe_le_binTail` supply the two halves. But what the paper's
  introduction leads with is Theorem 5's *uniqueness* clause — the lower bound is attained
  only at the constant vector, unless `b = 0` and `c = n` — and that rests on Theorem 2, so it
  is out of reach here for the same reason the equality clause of Theorem 4 is. Formalising
  the inequality alone would name a theorem after considerably less than the theorem.

**A caveat on the equality clause of Theorem 4.** The paper's attainment conditions carry
the bound `c < n` (`np ≤ c < n`, p. 718), and that bound is not decorative. No statement
below carries an equality clause for Theorem 4.

## Relation to Mathlib

Mathlib has the binomial distribution `ProbabilityTheory.binomial` (`Bin(n,p)`, a measure
on `ℕ`) and `ProbabilityTheory.setBernoulli`, the product of Bernoulli distributions with a
**common** parameter over a set. The *heterogeneous* product is available too, but by
construction rather than as an API: `MeasureTheory.Measure.pi` applied to a family of
`ProbabilityTheory.bernoulliMeasure`s is exactly it, and
`bernExp_eq_integral_pi_bernoulliMeasure` is the lemma that says so. What is missing is
everything built on it — no law of the number of successes under that product, no binomial
tail or cumulative distribution function, and, at the pinned revision, nothing from
Hoeffding's 1956 paper. (The `Hoeffding` that does appear in Mathlib, in
`Mathlib/Probability/Moments/SubGaussian.lean`, is the unrelated 1963 concentration
inequality.)

Four definitions are therefore introduced here — `bernWt`, `bernExp`, `tailLe` and
`binTail` — and each is tied back to Mathlib:

* `binTail_eq_binomial_real_Iic` identifies `binTail n P k` with `Bin(n,P).real (Set.Iic k)`,
  and `bernExp_const_eq_integral_binomial` identifies the model at a constant success
  probability with the integral against `Bin(n,P)`. Together these pin the comparator
  appearing on one side of every inequality below to Mathlib's binomial distribution, so
  the statements are not comparisons of one bespoke object against another.
* `bernExp_eq_integral_pi_bernoulliMeasure` identifies the model itself with the integral
  of `g ∘ (number of successes)` against `Measure.pi` of Mathlib's `bernoulliMeasure` —
  that is, against an honest product of independent, individually parameterised Bernoulli
  measures. This is the statement that says `bernWt` means what its docstring says.
* Independently of all three, the `## The statements` section restates all three results —
  Theorems 3 and 4 and Corollary 2.1 — with every definition unfolded by hand, into raw
  `Finset` sums, products and filters, and discharges those restatements by the proved
  theorems. So the headline statements can be read and checked without trusting any
  definition in this file.

## Provenance

Result selected and specified by George A. Constantinides, who has read the Lean statement
below against the informal claim above on a best-effort basis. The statement and its
proof were generated by Claude; the proof is read by nobody. Both are kernel-verified
and axiom-audited. A best-effort read is not a review — satisfy yourself that the
statement says what you need before relying on it. See the repository README.

Before that read, the Lean statement was read back blind: the statements of
`## The statements` were rendered into English by an agent given them and nothing else —
no informal statement, no source, no docstring. The rendering agreed with the informal
account above. It confirmed that the truncated `ℕ` subtraction in both displays is
harmless, since `C(#s, j)` vanishes wherever the exponent would truncate; that the
fixed-mean box is inhabited exactly when `0 ≤ lam ≤ #s`, so Corollary 2.1 hides no
vacuity; and that clause (b) of Corollary 2.1 is the three-value reading rather than the
stronger vertex one. It surfaced two things: the empty-`s` degeneracy recorded above,
which the docstring had not mentioned, and a summation variable in the equality clause of
Theorem 3 that shadowed the bound variable it was stated under, since renamed.

One error reached publication and was caught later, by an external accuracy review of
draft announcement posts rather than by a read-back or either check script. The gloss under
Theorem 4's display read "the *heaviest* below it", where the regime is `k ≤ lam - 1` and
not `k < lam`; on the gap between those two readings the comparison reverses, so the
sentence was false and sat directly under the display it appeared to restate.
`thm4_lower_needs_le_sub_one` now holds the counterexample. What is worth recording is
which guard failed: nothing here checks the English against the Lean it accompanies, the
read-back deliberately never sees the prose, and a false gloss above a true theorem is
exactly the shape that leaves. That is the residual risk this repository still carries.

This file is a refactoring of an earlier, unpublished formalisation of the same paper by
the same author.
-/


namespace MiscMath.Probability

open Finset

/-! ## The statements

The three results the informal statement above advertises, restated here **with every
definition local to this library unfolded by hand** — no `bernExp`, no `bernWt`, no
`tailLe`, no `binTail`, no `InBox` — so that each can be read and checked against the
informal claim without trusting a definition, and so that a reader who starts at this
module, as every supporting module's docstring says to, meets the statements here rather
than having to go looking for them.

Each is proved by its natural-form counterpart, which is where the mathematics is:
`hoeffding_thm3` and `hoeffding_thm3_eq_iff` in `ConvexExtremum`, `hoeffding_cor21` and
`hoeffding_cor21_min` in `ExtremalShapes`, `hoeffding_thm4` in `TailBounds`. Those state
the same results in the vocabulary the proofs use, and `Bridge` ties that vocabulary to
Mathlib's `ProbabilityTheory.binomial` and `ProbabilityTheory.bernoulliMeasure`. If any of
the definitions ever stopped meaning what its docstring says, the two forms would part
company and this section would fail to elaborate.

Together with `bernExp_eq_integral_pi_bernoulliMeasure` and `binTail_eq_binomial_real_Iic`
this means the headline statements can be checked twice over: once here against raw
`Finset` sums and products, and once against Mathlib's own probability vocabulary. -/

section Statements

variable {ι : Type*} [DecidableEq ι]

/-- **Hoeffding (1956), Theorem 3**, definition-free: the binomial maximises `E[g S]` at a
fixed mean, for `g` convex on the integer grid. Natural form: `hoeffding_thm3`. -/
theorem hoeffding_thm3_unfolded (s : Finset ι) (p : ι → ℝ) (g : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 ≤ g (k + 2) - 2 * g (k + 1) + g k) :
    ∑ A ∈ s.powerset, ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * g A.card
      ≤ ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : ℝ)
          * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ k
          * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - k) :=
  hoeffding_thm3 p g h0 h1 hg

/-- **The equality clause of Theorem 3**, definition-free: under *strict* grid convexity,
equality holds exactly at the constant vector. Natural form: `hoeffding_thm3_eq_iff`. -/
theorem hoeffding_thm3_eq_iff_unfolded (s : Finset ι) (p : ι → ℝ) (g : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 < g (k + 2) - 2 * g (k + 1) + g k) :
    (∑ A ∈ s.powerset, ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * g A.card
        = ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : ℝ)
            * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ k
            * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - k))
      ↔ ∀ i ∈ s, p i = (∑ j ∈ s, p j) / (s.card : ℝ) :=
  hoeffding_thm3_eq_iff p g h0 h1 hg

/-- **Hoeffding (1956), Corollary 2.1**, definition-free: the maximum of `E[g S]` over the
fixed-mean box is attained at a point whose coordinates strictly inside `(0,1)` are all
equal — at most three distinct values in all, at most one of them interior. `g` is
arbitrary. Natural form: `hoeffding_cor21`. -/
theorem hoeffding_cor21_unfolded (s : Finset ι) (lam : ℝ) (g : ℕ → ℝ) {p : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (hmean : ∑ i ∈ s, p i = lam) :
    ∃ q : ι → ℝ,
      ((∀ i ∈ s, 0 ≤ q i) ∧ (∀ i ∈ s, q i ≤ 1) ∧ ∑ i ∈ s, q i = lam)
        ∧ (∀ i ∈ s.filter (fun i => 0 < q i ∧ q i < 1),
            ∀ j ∈ s.filter (fun i => 0 < q i ∧ q i < 1), q i = q j)
        ∧ ∀ r : ι → ℝ,
            ((∀ i ∈ s, 0 ≤ r i) ∧ (∀ i ∈ s, r i ≤ 1) ∧ ∑ i ∈ s, r i = lam) →
              ∑ A ∈ s.powerset, ((∏ i ∈ A, r i) * ∏ i ∈ s \ A, (1 - r i)) * g A.card
                ≤ ∑ A ∈ s.powerset, ((∏ i ∈ A, q i) * ∏ i ∈ s \ A, (1 - q i)) * g A.card :=
  hoeffding_cor21 g ⟨h0, h1, hmean⟩

/-- **Corollary 2.1 in the minimising direction**, definition-free.
Natural form: `hoeffding_cor21_min`. -/
theorem hoeffding_cor21_min_unfolded (s : Finset ι) (lam : ℝ) (g : ℕ → ℝ) {p : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (hmean : ∑ i ∈ s, p i = lam) :
    ∃ q : ι → ℝ,
      ((∀ i ∈ s, 0 ≤ q i) ∧ (∀ i ∈ s, q i ≤ 1) ∧ ∑ i ∈ s, q i = lam)
        ∧ (∀ i ∈ s.filter (fun i => 0 < q i ∧ q i < 1),
            ∀ j ∈ s.filter (fun i => 0 < q i ∧ q i < 1), q i = q j)
        ∧ ∀ r : ι → ℝ,
            ((∀ i ∈ s, 0 ≤ r i) ∧ (∀ i ∈ s, r i ≤ 1) ∧ ∑ i ∈ s, r i = lam) →
              ∑ A ∈ s.powerset, ((∏ i ∈ A, q i) * ∏ i ∈ s \ A, (1 - q i)) * g A.card
                ≤ ∑ A ∈ s.powerset, ((∏ i ∈ A, r i) * ∏ i ∈ s \ A, (1 - r i)) * g A.card :=
  hoeffding_cor21_min g ⟨h0, h1, hmean⟩

/-- **Hoeffding (1956), Theorem 4**, definition-free, in its two extreme regimes: at
thresholds `k ≥ lam` the binomial has the lighter lower tail, at `k ≤ lam - 1` the heavier,
and the trivial bounds `0 ≤ P[S ≤ k] ≤ 1` accompany them. The middle regime
`lam - 1 < k < lam` is not claimed; `thm4_gap_subsingleton` bounds what that leaves out and
`thm4_lower_needs_le_sub_one` shows the second hypothesis cannot be relaxed to `k < lam`.
Natural form: `hoeffding_thm4`. -/
theorem hoeffding_thm4_unfolded (s : Finset ι) (p : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (k : ℕ) :
    ((∑ i ∈ s, p i) ≤ (k : ℝ) →
        (∑ j ∈ range (k + 1), (s.card.choose j : ℝ) * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ j
              * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - j)
            ≤ ∑ A ∈ s.powerset,
                ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * (if A.card ≤ k then (1 : ℝ) else 0))
          ∧ ∑ A ∈ s.powerset,
              ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * (if A.card ≤ k then (1 : ℝ) else 0)
                ≤ 1)
      ∧ ((k : ℝ) ≤ (∑ i ∈ s, p i) - 1 →
        (0 ≤ ∑ A ∈ s.powerset,
              ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * (if A.card ≤ k then (1 : ℝ) else 0))
          ∧ ∑ A ∈ s.powerset,
              ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * (if A.card ≤ k then (1 : ℝ) else 0)
                ≤ ∑ j ∈ range (k + 1), (s.card.choose j : ℝ)
                    * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ j
                    * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - j)) :=
  hoeffding_thm4 p h0 h1 k

end Statements

private lemma range_three : (range 3 : Finset ℕ) = {0, 1, 2} := by decide +kernel

/-! ## Sanity checks

Guards against the ways a correct proof can still accompany a useless statement. These are
`example`s: elaborated by the build, so one that stops holding breaks it, and exporting no
names. They are *not* reached by the axiom audit, which walks the named declarations a module
contributes to the environment, and an `example` contributes none. What covers them instead
is the textual escape-hatch scan in `scripts/check-conventions.sh`, which reads the file
rather than the environment.

The named `theorem`s of the supporting modules are part of the same defence and *are*
audited: `hoeffding_thm3_needs_le_one`, `hoeffding_thm3_needs_nonneg` and
`hoeffding_thm3_eq_needs_strict` in `ConvexExtremum`; `vertex_reduction_false`,
`vertex_reduction_min_false` and `vertex_reduction_fails_of_strictConvex` in `ExtremalShapes`;
the attainment and gap statements in `TailBounds`. So are the `private` declarations of this
file, which the audit walks under their mangled names. -/

section Sanity

/-! ### Non-vacuity: the hypotheses of each main theorem are simultaneously satisfiable

Every main statement here has hypotheses, including universally quantified ones, and an
unsatisfiable assumption is the most likely way for a generated statement to be worthless
while passing every other check. Each block below exhibits values satisfying all hypotheses
of one theorem at once. -/

/-- Theorem 3: three trials at `p ≡ 1/3` against `g k = k²`, which is strictly grid-convex
(`Δ²g ≡ 2`), so the hypotheses of `hoeffding_thm3` *and* of `hoeffding_thm3_eq_iff` hold
together. The universally quantified convexity hypothesis is discharged for every `k`, not
merely for the two in range. -/
example :
    (∀ i ∈ range 3, (0 : ℝ) ≤ (fun _ : ℕ => (1 : ℝ) / 3) i)
      ∧ (∀ i ∈ range 3, (fun _ : ℕ => (1 : ℝ) / 3) i ≤ 1)
      ∧ (∀ k, k + 2 ≤ (range 3).card →
          (0 : ℝ) < ((k : ℝ) + 2) ^ 2 - 2 * ((k : ℝ) + 1) ^ 2 + (k : ℝ) ^ 2) := by
  refine ⟨fun i _ => by norm_num, fun i _ => by norm_num, fun k _ => ?_⟩
  nlinarith [sq_nonneg (k : ℝ)]

/-- Theorem 4, **above** the mean: `p = (0, 3/8, 5/8)` has mean `1`, and `k = 1` satisfies the
regime hypothesis `lam ≤ k`. So the first half of `hoeffding_thm4` is not vacuous. -/
example :
    (∀ j ∈ range 3,
          (0 : ℝ) ≤ (fun j => if j = 0 then (0 : ℝ) else if j = 1 then 3 / 8 else 5 / 8) j)
      ∧ (∀ j ∈ range 3,
          (fun j => if j = 0 then (0 : ℝ) else if j = 1 then 3 / 8 else 5 / 8) j ≤ 1)
      ∧ (∑ j ∈ range 3, (if j = 0 then (0 : ℝ) else if j = 1 then 3 / 8 else 5 / 8))
          ≤ ((1 : ℕ) : ℝ) := by
  refine ⟨fun j _ => ?_, fun j _ => ?_, ?_⟩
  · dsimp only; split_ifs <;> norm_num
  · dsimp only; split_ifs <;> norm_num
  · norm_num [Finset.sum_range_succ]

/-- Theorem 4, **below** the mean: the regime `k ≤ lam - 1` forces `lam ≥ 1`, so it is worth
exhibiting a point of it. Three trials at `p ≡ 1/2` have mean `3/2`, and `k = 0` satisfies
`(k : ℝ) ≤ lam - 1`. So the second half of `hoeffding_thm4` is not vacuous either. -/
example :
    (∀ j ∈ range 3, (0 : ℝ) ≤ (fun _ : ℕ => (1 : ℝ) / 2) j)
      ∧ (∀ j ∈ range 3, (fun _ : ℕ => (1 : ℝ) / 2) j ≤ 1)
      ∧ ((0 : ℕ) : ℝ) ≤ (∑ _j ∈ range 3, (1 : ℝ) / 2) - 1 := by
  refine ⟨fun j _ => by norm_num, fun j _ => by norm_num, ?_⟩
  norm_num [Finset.sum_range_succ]

/-- Corollary 2.1: the fixed-mean box is inhabited at `s = {0,1}`, `lam = 1`, so
`hoeffding_cor21` and `hoeffding_cor21_min` have something to say there. -/
example : InBox ({0, 1} : Finset ℕ) 1 (fun _ => (1 : ℝ) / 2) := by
  refine ⟨fun i _ => by norm_num, fun i _ => by norm_num, ?_⟩
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  norm_num

/-- The attainment theorems: `0 ≤ lam ≤ #s` and both regime hypotheses are satisfiable at
`s = range 3`, `lam = 3/2`, with `k = 2` above the mean and `k = 0` below it. -/
example : (0 : ℝ) ≤ 3 / 2 ∧ (3 : ℝ) / 2 ≤ ((range 3).card : ℝ)
    ∧ (3 : ℝ) / 2 ≤ ((2 : ℕ) : ℝ) ∧ ((0 : ℕ) : ℝ) ≤ (3 : ℝ) / 2 - 1 := by
  refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
  rw [Finset.card_range]
  norm_num

/-! ### The conclusion at a concrete value

Three trials at `p = (0, 3/8, 5/8)`, mean `lam = 1`, threshold `k = 1 ≥ lam`. The model tail
is `49/64`, the comparator `B(1; 3, 1/3)` is `20/27`, and the theorem's conclusion — the
comparator is the smaller — is *derived* from `hoeffding_thm4_range`, not asserted. Both
constants are computed here by `norm_num` from the definitions, independently of the proofs
above. -/

/-- The worked instance's success probabilities. -/
private noncomputable def exThreeTrials : ℕ → ℝ :=
  fun j => if j = 0 then 0 else if j = 1 then 3 / 8 else 5 / 8

private theorem exThreeTrials_mean : (∑ j ∈ range 3, exThreeTrials j) = 1 := by
  norm_num [Finset.sum_range_succ, exThreeTrials]

/-- **The worked instance.** Both sides in closed form, and the inequality derived. -/
private theorem hoeffding_thm4_worked_instance :
    tailLe (range 3) exThreeTrials 1 = 49 / 64
      ∧ binTail 3 ((∑ j ∈ range 3, exThreeTrials j) / (3 : ℝ)) 1 = 20 / 27
      ∧ binTail 3 ((∑ j ∈ range 3, exThreeTrials j) / (3 : ℝ)) 1
          ≤ tailLe (range 3) exThreeTrials 1 := by
  have hmodel : tailLe (range 3) exThreeTrials 1 = 49 / 64 := by
    rw [tailLe, range_three,
      bernExp_triple (by norm_num) (by norm_num) (by norm_num)]
    norm_num [exThreeTrials]
  have hcomp : binTail 3 ((∑ j ∈ range 3, exThreeTrials j) / (3 : ℝ)) 1 = 20 / 27 := by
    rw [exThreeTrials_mean, binTail]
    norm_num [Finset.sum_range_succ]
  refine ⟨hmodel, hcomp, ?_⟩
  refine ((hoeffding_thm4_range exThreeTrials (fun j _ => ?_) (fun j _ => ?_) 1).1 ?_).1
  · unfold exThreeTrials; split_ifs <;> norm_num
  · unfold exThreeTrials; split_ifs <;> norm_num
  · rw [exThreeTrials_mean]; norm_num

/-- The instance is not an equality in disguise: the inequality is **strict** there, so the
comparison has content. -/
example : (20 : ℝ) / 27 < 49 / 64 := by norm_num

/-! The upper regime alone is not enough. The worked instance above has `lam ≤ k`, and the
only concrete point of the *lower* regime exhibited elsewhere in this section is
homogeneous, where the two sides coincide by construction and could not detect a reversed
inequality. So here is a heterogeneous one: `p = (1, 5/8, 3/8)` has mean `2`, and `k = 1`
satisfies `k ≤ lam - 1`. The model tail is `15/64`, the comparator `B(1; 3, 2/3)` is
`7/27`, and this time it is the *model* that is the smaller. -/

/-- The lower regime's success probabilities: heterogeneous, and none of them equal. -/
private noncomputable def exLowerRegime : ℕ → ℝ :=
  fun j => if j = 0 then 1 else if j = 1 then 5 / 8 else 3 / 8

private theorem exLowerRegime_mean : (∑ j ∈ range 3, exLowerRegime j) = 2 := by
  norm_num [Finset.sum_range_succ, exLowerRegime]

/-- **The worked instance in the lower regime.** Both sides in closed form, and the inequality
derived from `hoeffding_thm4_range` rather than asserted. -/
private theorem hoeffding_thm4_worked_instance_lower :
    tailLe (range 3) exLowerRegime 1 = 15 / 64
      ∧ binTail 3 ((∑ j ∈ range 3, exLowerRegime j) / (3 : ℝ)) 1 = 7 / 27
      ∧ tailLe (range 3) exLowerRegime 1
          ≤ binTail 3 ((∑ j ∈ range 3, exLowerRegime j) / (3 : ℝ)) 1 := by
  have hmodel : tailLe (range 3) exLowerRegime 1 = 15 / 64 := by
    rw [tailLe, range_three,
      bernExp_triple (by norm_num) (by norm_num) (by norm_num)]
    norm_num [exLowerRegime]
  have hcomp : binTail 3 ((∑ j ∈ range 3, exLowerRegime j) / (3 : ℝ)) 1 = 7 / 27 := by
    rw [exLowerRegime_mean, binTail]
    norm_num [Finset.sum_range_succ]
  refine ⟨hmodel, hcomp, ?_⟩
  refine ((hoeffding_thm4_range exLowerRegime (fun j _ => ?_) (fun j _ => ?_) 1).2 ?_).2
  · unfold exLowerRegime; split_ifs <;> norm_num
  · unfold exLowerRegime; split_ifs <;> norm_num
  · rw [exLowerRegime_mean]; norm_num

/-- Strict there too, and in the opposite direction to the instance above it: the two
regimes really do bound the model from opposite sides. -/
example : (15 : ℝ) / 64 < 7 / 27 := by norm_num

/-! ### The model rests on `Finset.prod_add`, invoked by name

If it is renamed or removed upstream, this file stops compiling — which is the point: the
normalisation of the model is that lemma and nothing else, and it needs no hypothesis on `p`
whatsoever. -/

example (s : Finset ℕ) (p : ℕ → ℚ) : ∑ A ∈ s.powerset, bernWt s p A = 1 := by
  simpa [bernWt] using (Finset.prod_add (fun i => p i) (fun i => 1 - p i) s).symm

/-! ### The gap left by the two regimes, at a concrete mean

At `lam = 3/2` the uncovered regime `lam - 1 < k < lam` holds exactly the threshold `k = 1`;
at the whole-number mean `lam = 2` it holds none. -/

example : ((3 : ℝ) / 2) - 1 < ((1 : ℕ) : ℝ) ∧ ((1 : ℕ) : ℝ) < (3 : ℝ) / 2 := by norm_num

example : (1 : ℕ) = ⌊(3 : ℝ) / 2⌋₊ := thm4_gap_eq_floor (by norm_num) (by norm_num)

example (k : ℕ) : ¬ (((2 : ℕ) : ℝ) - 1 < (k : ℝ) ∧ (k : ℝ) < ((2 : ℕ) : ℝ)) :=
  fun h => thm4_gap_empty_of_natCast h.1 h.2

end Sanity

end MiscMath.Probability
