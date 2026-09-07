/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

/-!
# Hoeffding's extrema of the number of successes at a fixed mean — advertised statement

This is the statement surface of the submission: the declarations a mathematical reader is
asked to audit. The proofs are in `MiscMath.Probability.PoissonTrialsFixedMean`, which is
the Solution module of the accompanying Comparator configuration and is the file the
library actually ships. The `sorry`s below are the deliberate holes Comparator fills.

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
   lower tail at thresholds `k ≥ lam` and the *heaviest* at thresholds `k ≤ lam - 1`. The
   second regime is `k ≤ lam - 1` and not `k < lam`: on the gap between those two readings
   the comparison reverses, so the narrower one is the true statement.

## How to read these statements

Every statement below is written **without any definition of its own**. The probability
model, the tail and the binomial comparator are all expanded into raw `Finset` sums,
products and filters, so that a reader can audit each claim against the informal statement
above without first accepting a definition. Four things are worth knowing.

* **The model.** `∑ A ∈ s.powerset, (∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * g A.card`
  is `E[g S]`: the sample space is the set of subsets `A ⊆ s` of successful trials, the
  weight of `A` is `∏_{i ∈ A} p i · ∏_{i ∉ A} (1 - p i)`, and `S` is `A.card`. Those
  weights sum to `1` by `Finset.prod_add` and no hypothesis on `p` whatsoever. That alone
  is not what makes it a probability model: at `p ≡ 2` on a single trial the two weights
  are `2` and `-1`, which sum to one and are not a distribution. The standing hypotheses
  `0 ≤ p i ≤ 1` are what make every weight nonnegative, and normalisation together with
  nonnegativity give the law of independent Bernoulli trials with those success
  probabilities.
* **The tail.** `P[S ≤ k]` is that same sum with `g` the indicator `if A.card ≤ k then 1
  else 0`, and the comparator `B(k; n, P)` is `∑_{j ≤ k} C(n,j) P^j (1-P)^(n-j)`. The
  Solution module identifies both with Mathlib's `ProbabilityTheory.binomial` and
  `ProbabilityTheory.bernoulliMeasure`; those identifications are not compared here,
  because a statement written in raw sums needs no such licence to be read.
* **Truncated subtraction is harmless.** `s.card - j` is `ℕ` subtraction, truncated at
  zero. In Theorem 3 the summation index never exceeds `s.card`, so no truncation occurs.
  In Theorem 4 the index `j` may exceed `s.card`, but `C(s.card, j) = 0` there, so the
  truncated terms vanish rather than contributing junk.
* **Degenerate cases are not excluded.** At `s = ∅` the mean `lam / #s` is `0 / 0 = 0` and
  every statement below is true but empty: both sides of Theorem 3 collapse to `g 0`, and
  Theorem 4's first regime to `1 ≤ 1`. Theorem 4's second regime is vacuous whenever
  `lam < 1`, since `k` is a natural number and the regime asks for `k ≤ lam - 1`. Neither
  is ruled out by hypothesis.

## Source

W. Hoeffding, *On the distribution of the number of successes in independent trials*,
Annals of Mathematical Statistics **27** (1956), 713-721.

* Theorem 3 is p. 717, equations (22)-(23).
* Corollary 2.1 is p. 717, following Theorem 2.
* Theorem 4 is p. 718, equations (24)-(29).

**What is formalised, and what is not.** This matters more than usual here, because the
paper's Theorem 4 has three regimes and only two of them are stated below.

* Theorem 3 is formalised in full, and the inequality is proved under a *weaker*
  hypothesis than the paper's: Hoeffding assumes strict grid convexity throughout, but
  strictness is needed only for the equality clause.
* Corollary 2.1 is formalised in full, in both directions.
* Of Theorem 4: the upper bound of (24), the lower bound of (26), and the trivial bounds
  `0 ≤ P[S ≤ c]` and `P[S ≤ c] ≤ 1` that accompany them. **Not** formalised: equation
  (25), the middle regime `np - 1 < c < np`; equation (29), which locates the maximising
  `s`; and the *uniqueness* half of the attainment statement.

  The scope of what is missing is itself pinned down in the Solution, in
  `MiscMath.Probability.PoissonTrialsFixedMean.TailBounds`. Since `c` is an integer and
  the middle regime is an open interval of length `1`, it holds at most one integer
  (`thm4_gap_subsingleton`), which is `⌊lam⌋` (`thm4_gap_eq_floor`), and none at all when
  the mean is a whole number (`thm4_gap_empty_of_natCast`). So the two regimes below
  settle every threshold except at most one, and all of them whenever `lam ∈ ℕ`. Those
  three are not compared here because they are declared in a supporting module rather
  than in the Solution module, but a reviewer who wants to check the scope claim will
  find them there.
* Theorems 1 and 2 of the paper are not formalised; the route taken to Corollary 2.1 is a
  terminating exchange argument that needs neither. Theorem 5 is omitted by choice: its
  inequality is a subtraction away from what is proved, but its *uniqueness* clause rests
  on Theorem 2, and formalising the inequality alone would name a theorem after
  considerably less than the theorem.

**A caveat on Theorem 4.** The paper's attainment conditions carry the bound `c < n`
(`np ≤ c < n`, p. 718), and that bound is not decorative. No statement below carries an
equality clause for Theorem 4.

## Relation to Mathlib

Mathlib has the binomial distribution `ProbabilityTheory.binomial` and
`ProbabilityTheory.setBernoulli`, the product of Bernoulli distributions with a **common**
parameter over a set. The *heterogeneous* product is available too, but by construction
rather than as an API: `MeasureTheory.Measure.pi` applied to a family of
`ProbabilityTheory.bernoulliMeasure`s is exactly it. What is missing is everything built on
it — no law of the number of successes under that product, no binomial tail or cumulative
distribution function, and, at the pinned revision, nothing from Hoeffding's 1956 paper. (The `Hoeffding` that does appear in Mathlib, in
`Mathlib/Probability/Moments/SubGaussian.lean`, is the unrelated 1963 concentration
inequality.)

The Solution module introduces four definitions — `bernWt`, `bernExp`, `tailLe` and
`binTail` — and ties each back to Mathlib's own probability vocabulary. None of them
appears below: every compared statement is expanded into `Finset` operations from Mathlib
alone, which is why this Challenge imports nothing but Mathlib.
-/

open Finset

namespace MiscMath.Probability

variable {ι : Type*} [DecidableEq ι]

/-! ## Theorem 3: the binomial maximises `E[g S]` at a fixed mean -/

/-- **Hoeffding (1956), Theorem 3**, definition-free: the binomial maximises `E[g S]` at a
fixed mean, for `g` convex on the integer grid. -/
theorem hoeffding_thm3_unfolded (s : Finset ι) (p : ι → ℝ) (g : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 ≤ g (k + 2) - 2 * g (k + 1) + g k) :
    ∑ A ∈ s.powerset, ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * g A.card
      ≤ ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : ℝ)
          * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ k
          * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - k) := by
  sorry

/-- **The equality clause of Theorem 3**, definition-free: under *strict* grid convexity,
equality holds exactly at the constant vector. -/
theorem hoeffding_thm3_eq_iff_unfolded (s : Finset ι) (p : ι → ℝ) (g : ℕ → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 < g (k + 2) - 2 * g (k + 1) + g k) :
    (∑ A ∈ s.powerset, ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * g A.card
        = ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : ℝ)
            * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ k
            * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - k))
      ↔ ∀ i ∈ s, p i = (∑ j ∈ s, p j) / (s.card : ℝ) := by
  sorry

/-! ## Corollary 2.1: the extremal shapes at a fixed mean -/

/-- **Hoeffding (1956), Corollary 2.1**, definition-free: the maximum of `E[g S]` over the
fixed-mean box is attained at a point whose coordinates strictly inside `(0,1)` are all
equal — at most three distinct values in all, at most one of them interior. `g` is
arbitrary: no convexity, no monotonicity. -/
theorem hoeffding_cor21_unfolded (s : Finset ι) (lam : ℝ) (g : ℕ → ℝ) {p : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (hmean : ∑ i ∈ s, p i = lam) :
    ∃ q : ι → ℝ,
      ((∀ i ∈ s, 0 ≤ q i) ∧ (∀ i ∈ s, q i ≤ 1) ∧ ∑ i ∈ s, q i = lam)
        ∧ (∀ i ∈ s.filter (fun i => 0 < q i ∧ q i < 1),
            ∀ j ∈ s.filter (fun i => 0 < q i ∧ q i < 1), q i = q j)
        ∧ ∀ r : ι → ℝ,
            ((∀ i ∈ s, 0 ≤ r i) ∧ (∀ i ∈ s, r i ≤ 1) ∧ ∑ i ∈ s, r i = lam) →
              ∑ A ∈ s.powerset, ((∏ i ∈ A, r i) * ∏ i ∈ s \ A, (1 - r i)) * g A.card
                ≤ ∑ A ∈ s.powerset, ((∏ i ∈ A, q i) * ∏ i ∈ s \ A, (1 - q i)) * g A.card := by
  sorry

/-- **Corollary 2.1 in the minimising direction**, definition-free. -/
theorem hoeffding_cor21_min_unfolded (s : Finset ι) (lam : ℝ) (g : ℕ → ℝ) {p : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (hmean : ∑ i ∈ s, p i = lam) :
    ∃ q : ι → ℝ,
      ((∀ i ∈ s, 0 ≤ q i) ∧ (∀ i ∈ s, q i ≤ 1) ∧ ∑ i ∈ s, q i = lam)
        ∧ (∀ i ∈ s.filter (fun i => 0 < q i ∧ q i < 1),
            ∀ j ∈ s.filter (fun i => 0 < q i ∧ q i < 1), q i = q j)
        ∧ ∀ r : ι → ℝ,
            ((∀ i ∈ s, 0 ≤ r i) ∧ (∀ i ∈ s, r i ≤ 1) ∧ ∑ i ∈ s, r i = lam) →
              ∑ A ∈ s.powerset, ((∏ i ∈ A, q i) * ∏ i ∈ s \ A, (1 - q i)) * g A.card
                ≤ ∑ A ∈ s.powerset, ((∏ i ∈ A, r i) * ∏ i ∈ s \ A, (1 - r i)) * g A.card := by
  sorry

/-! ## Theorem 4: the tail against the binomial, away from the mean -/

/-- **Hoeffding (1956), Theorem 4**, definition-free, in its two extreme regimes: at
thresholds `k ≥ lam` the binomial has the lighter lower tail, at `k ≤ lam - 1` the heavier,
with the trivial bounds `0 ≤ P[S ≤ k] ≤ 1` accompanying them as in the paper's display. The
middle regime `lam - 1 < k < lam` is not claimed, and it is not merely unattempted: it is
where the looser reading `k < lam` of the second regime is false. -/
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
                    * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - j)) := by
  sorry

end MiscMath.Probability
