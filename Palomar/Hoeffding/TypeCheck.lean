/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Probability.PoissonTrialsFixedMean

/-!
# The Challenge statements agree with the library

`Palomar/Hoeffding/Challenge.lean` restates five theorems of
`MiscMath.Probability.PoissonTrialsFixedMean` without their proofs, so that Palomar's
Comparator can check the shipped proofs against an independently readable statement
surface. Two copies of a statement can drift apart, and Comparator would only report it at
submission time.

Each `example` below ascribes the type written in `Challenge.lean` to the theorem the
library actually ships. Elaboration failure means the two have drifted. This is a local
convenience, not the authoritative check: Comparator compares the elaborated statements of
the two modules directly, and that is the check Palomar records. In particular, if a
statement is edited in `Challenge.lean` and here but not in the library, this file fails;
if it is edited in the library alone, this file fails; but a statement edited here and in
`Challenge.lean` in the same wrong way would pass. The file is not `sorry`-free by accident
either — it must not be, since it asserts the library's real theorems.

This module is deliberately outside `MiscMath/`, so it reaches neither
`MiscMath/Audit.lean` nor the three checks in `scripts/`, all of which are scoped to that
directory. Build it with `lake build PalomarHoeffdingTypeCheck`.
-/

open Finset

example : ∀ {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ) (g : ℕ → ℝ),
    (∀ i ∈ s, 0 ≤ p i) → (∀ i ∈ s, p i ≤ 1) →
    (∀ k, k + 2 ≤ s.card → 0 ≤ g (k + 2) - 2 * g (k + 1) + g k) →
    ∑ A ∈ s.powerset, ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * g A.card
      ≤ ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : ℝ)
          * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ k
          * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - k) :=
  @MiscMath.Probability.hoeffding_thm3_unfolded

example : ∀ {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ) (g : ℕ → ℝ),
    (∀ i ∈ s, 0 ≤ p i) → (∀ i ∈ s, p i ≤ 1) →
    (∀ k, k + 2 ≤ s.card → 0 < g (k + 2) - 2 * g (k + 1) + g k) →
    ((∑ A ∈ s.powerset, ((∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)) * g A.card
        = ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : ℝ)
            * ((∑ i ∈ s, p i) / (s.card : ℝ)) ^ k
            * (1 - (∑ i ∈ s, p i) / (s.card : ℝ)) ^ (s.card - k))
      ↔ ∀ i ∈ s, p i = (∑ j ∈ s, p j) / (s.card : ℝ)) :=
  @MiscMath.Probability.hoeffding_thm3_eq_iff_unfolded

example : ∀ {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ℝ) (g : ℕ → ℝ) {p : ι → ℝ},
    (∀ i ∈ s, 0 ≤ p i) → (∀ i ∈ s, p i ≤ 1) → (∑ i ∈ s, p i = lam) →
    ∃ q : ι → ℝ,
      ((∀ i ∈ s, 0 ≤ q i) ∧ (∀ i ∈ s, q i ≤ 1) ∧ ∑ i ∈ s, q i = lam)
        ∧ (∀ i ∈ s.filter (fun i => 0 < q i ∧ q i < 1),
            ∀ j ∈ s.filter (fun i => 0 < q i ∧ q i < 1), q i = q j)
        ∧ ∀ r : ι → ℝ,
            ((∀ i ∈ s, 0 ≤ r i) ∧ (∀ i ∈ s, r i ≤ 1) ∧ ∑ i ∈ s, r i = lam) →
              ∑ A ∈ s.powerset, ((∏ i ∈ A, r i) * ∏ i ∈ s \ A, (1 - r i)) * g A.card
                ≤ ∑ A ∈ s.powerset, ((∏ i ∈ A, q i) * ∏ i ∈ s \ A, (1 - q i)) * g A.card :=
  @MiscMath.Probability.hoeffding_cor21_unfolded

example : ∀ {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ℝ) (g : ℕ → ℝ) {p : ι → ℝ},
    (∀ i ∈ s, 0 ≤ p i) → (∀ i ∈ s, p i ≤ 1) → (∑ i ∈ s, p i = lam) →
    ∃ q : ι → ℝ,
      ((∀ i ∈ s, 0 ≤ q i) ∧ (∀ i ∈ s, q i ≤ 1) ∧ ∑ i ∈ s, q i = lam)
        ∧ (∀ i ∈ s.filter (fun i => 0 < q i ∧ q i < 1),
            ∀ j ∈ s.filter (fun i => 0 < q i ∧ q i < 1), q i = q j)
        ∧ ∀ r : ι → ℝ,
            ((∀ i ∈ s, 0 ≤ r i) ∧ (∀ i ∈ s, r i ≤ 1) ∧ ∑ i ∈ s, r i = lam) →
              ∑ A ∈ s.powerset, ((∏ i ∈ A, q i) * ∏ i ∈ s \ A, (1 - q i)) * g A.card
                ≤ ∑ A ∈ s.powerset, ((∏ i ∈ A, r i) * ∏ i ∈ s \ A, (1 - r i)) * g A.card :=
  @MiscMath.Probability.hoeffding_cor21_min_unfolded

example : ∀ {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ),
    (∀ i ∈ s, 0 ≤ p i) → (∀ i ∈ s, p i ≤ 1) → ∀ (k : ℕ),
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
  @MiscMath.Probability.hoeffding_thm4_unfolded
