/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/

import MiscMath.Probability.PoissonTrialsFixedMean.Model
import Mathlib.Probability.Distributions.Binomial

/-!
# The model and the comparator, in Mathlib's vocabulary

Part of `MiscMath.Probability.PoissonTrialsFixedMean`, whose module docstring states the
results and where the reader should start. This file ties the four definitions local to this
library — `bernWt`, `bernExp`, `tailLe`, `binTail` — back to Mathlib's
`ProbabilityTheory.binomial` and `ProbabilityTheory.bernoulliMeasure`, so that the results
are not comparisons of one bespoke object against another.
-/

namespace MiscMath.Probability

open Finset

/-! ## Relation to Mathlib's vocabulary

Four definitions are local to this library — `bernWt`, `bernExp` and `tailLe` from
`PoissonTrialsFixedMean.Model`, `binTail` from `PoissonTrialsFixedMean.BinomialTail` — and the
theorems are inequalities between them. This module ties all four back to Mathlib, so that the
results are not comparisons of one bespoke object against another.

* `bernExp_const_eq_integral_binomial` and `binTail_eq_binomial_real_Iic` identify the
  **comparator** — the right-hand side of Theorem 3 and one side of Theorem 4 — with
  Mathlib's `ProbabilityTheory.binomial`, as an integral and as a measure of `Set.Iic k`
  respectively.
* `bernExp_eq_integral_pi_bernoulliMeasure` identifies the **model** with the integral of
  `g ∘ (number of successes)` against `MeasureTheory.Measure.pi` of Mathlib's
  `ProbabilityTheory.bernoulliMeasure` — an honest product of independent, individually
  parameterised Bernoulli measures on `Bool`. This is the statement that says `bernWt` means
  what its docstring says it means. -/

section MathlibBridge

open MeasureTheory ProbabilityTheory

/-- **The comparator is Mathlib's binomial distribution.** At a constant success probability
`P` the model is the integral against `Bin(#s, P)`. -/
theorem bernExp_const_eq_integral_binomial {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : unitInterval) (g : ℕ → ℝ) :
    bernExp s (fun _ => (P : ℝ)) g = ∫ x, g x ∂(ProbabilityTheory.binomial s.card P) := by
  rw [ProbabilityTheory.integral_binomial, bernExp_const, ← Nat.range_succ_eq_Iic]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]

/-- **The binomial tail is the measure of `Set.Iic k` under Mathlib's binomial
distribution.** -/
theorem binTail_eq_binomial_real_Iic (n k : ℕ) (P : unitInterval) :
    binTail n (P : ℝ) k = (ProbabilityTheory.binomial n P).real (Set.Iic k) := by
  have hb := bernExp_const_eq_integral_binomial (range n) P (fun r => if r ≤ k then (1 : ℝ) else 0)
  rw [Finset.card_range] at hb
  have ht := tailLe_const (range n) k ((P : ℝ))
  rw [Finset.card_range] at ht
  have hfun : (fun r : ℕ => if r ≤ k then (1 : ℝ) else 0)
      = Set.indicator (Set.Iic k) (1 : ℕ → ℝ) := by
    funext r
    by_cases hr : r ≤ k
    · rw [if_pos hr, Set.indicator_of_mem (Set.mem_Iic.mpr hr)]
      rfl
    · rw [if_neg hr, Set.indicator_of_notMem (by simpa using hr)]
  rw [← ht, tailLe, hb, hfun, MeasureTheory.integral_indicator_one measurableSet_Iic]

variable {ι : Type*} [DecidableEq ι]

/-- The success indicator of a subset, as a point of `{x // x ∈ s} → Bool`. -/
private def toBoolFun (s : Finset ι) (A : Finset ι) : {x // x ∈ s} → Bool :=
  fun z => decide (z.1 ∈ A)

/-- The set of successes of a point of `{x // x ∈ s} → Bool`, as a `Finset ι`. -/
private def ofBoolFun (s : Finset ι) (ω : {x // x ∈ s} → Bool) : Finset ι :=
  (Finset.univ.filter (fun z : {x // x ∈ s} => ω z = true)).image Subtype.val

private lemma ofBoolFun_toBoolFun {s A : Finset ι} (hA : A ⊆ s) :
    ofBoolFun s (toBoolFun s A) = A := by
  ext x
  simp only [ofBoolFun, toBoolFun, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact hz
  · intro hx; exact ⟨⟨x, hA hx⟩, hx, rfl⟩

private lemma toBoolFun_ofBoolFun {s : Finset ι} (ω : {x // x ∈ s} → Bool) :
    toBoolFun s (ofBoolFun s ω) = ω := by
  funext z
  simp only [toBoolFun, ofBoolFun, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  by_cases hz : ω z = true
  · simp only [hz, decide_eq_true_eq]
    exact ⟨z, hz, rfl⟩
  · simp only [Bool.not_eq_true] at hz
    rw [hz]
    simp only [decide_eq_false_iff_not, not_exists]
    rintro ⟨w, hw⟩ ⟨hw1, hw2⟩
    cases hw2
    exact absurd hw1 (by rw [hz]; simp)

private lemma ofBoolFun_subset {s : Finset ι} (ω : {x // x ∈ s} → Bool) : ofBoolFun s ω ⊆ s := by
  intro x hx
  simp only [ofBoolFun, Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨z, -, rfl⟩ := hx
  exact z.2

private lemma card_filter_toBoolFun {s A : Finset ι} (hA : A ⊆ s) :
    (Finset.univ.filter (fun z : {x // x ∈ s} => toBoolFun s A z = true)).card = A.card := by
  have h := ofBoolFun_toBoolFun hA
  rw [ofBoolFun] at h
  calc (Finset.univ.filter (fun z : {x // x ∈ s} => toBoolFun s A z = true)).card
      = ((Finset.univ.filter (fun z : {x // x ∈ s} => toBoolFun s A z = true)).image
          Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := by rw [h]

/-- **The model is a product of Mathlib Bernoulli measures.** With one `Bool`-valued trial
per element of `s`, the `i`-th succeeding with probability `p i`, `bernExp s p g` is the
expectation of `g` applied to the number of successes.

The trials are indexed by `{x // x ∈ s}` and the product is `MeasureTheory.Measure.pi`, so
independence is Mathlib's, not a convention of this file; each factor is
`ProbabilityTheory.bernoulliMeasure true false ⟨p i, _⟩`, Mathlib's Bernoulli measure with
its own parameter. -/
theorem bernExp_eq_integral_pi_bernoulliMeasure {s : Finset ι} {p : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (g : ℕ → ℝ) :
    bernExp s p g
      = ∫ ω : {x // x ∈ s} → Bool,
            g (Finset.univ.filter (fun z => ω z = true)).card
          ∂(MeasureTheory.Measure.pi fun z : {x // x ∈ s} =>
              ProbabilityTheory.bernoulliMeasure true false
                ⟨p z.1, h0 z.1 z.2, h1 z.1 z.2⟩) := by
  classical
  set q : {x // x ∈ s} → unitInterval :=
    fun z => ⟨p z.1, h0 z.1 z.2, h1 z.1 z.2⟩ with hqdef
  set μ : Measure ({x // x ∈ s} → Bool) :=
    MeasureTheory.Measure.pi fun z => ProbabilityTheory.bernoulliMeasure true false (q z) with hμ
  have hwt : ∀ A ⊆ s, μ.real {toBoolFun s A} = bernWt s p A := by
    intro A hA
    have hsingle : ({toBoolFun s A} : Set ({x // x ∈ s} → Bool))
        = Set.pi Set.univ (fun z => {toBoolFun s A z}) := (Set.univ_pi_singleton _).symm
    rw [measureReal_def, hsingle, hμ, MeasureTheory.Measure.pi_pi, ENNReal.toReal_prod]
    have hterm : ∀ z : {x // x ∈ s},
        ((ProbabilityTheory.bernoulliMeasure true false (q z)) {toBoolFun s A z}).toReal
          = if z.1 ∈ A then p z.1 else 1 - p z.1 := by
      intro z
      by_cases hz : z.1 ∈ A
      · have hb : toBoolFun s A z = true := by simp [toBoolFun, hz]
        rw [hb, if_pos hz, ← measureReal_def,
          ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem (q z)
            (MeasurableSet.singleton true) rfl (by simp)]
      · have hb : toBoolFun s A z = false := by simp [toBoolFun, hz]
        rw [hb, if_neg hz, ← measureReal_def,
          ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem (q z)
            (MeasurableSet.singleton false) (by simp) rfl]
    rw [Finset.prod_congr rfl fun z _ => hterm z, Finset.prod_coe_sort s
      (fun i => if i ∈ A then p i else 1 - p i), Finset.prod_ite]
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hA, ← Finset.sdiff_eq_filter]
    rfl
  have hint : Integrable
      (fun ω : {x // x ∈ s} → Bool =>
        g (Finset.univ.filter (fun z => ω z = true)).card) μ := Integrable.of_finite
  rw [MeasureTheory.integral_fintype hint, bernExp]
  refine Finset.sum_bij' (fun A _ => toBoolFun s A) (fun ω _ => ofBoolFun s ω)
    (fun A _ => Finset.mem_univ _) (fun ω _ => Finset.mem_powerset.mpr (ofBoolFun_subset ω))
    (fun A hA => ofBoolFun_toBoolFun (Finset.mem_powerset.mp hA))
    (fun ω _ => toBoolFun_ofBoolFun ω) ?_
  intro A hA
  have hAs := Finset.mem_powerset.mp hA
  rw [hwt A hAs, card_filter_toBoolFun hAs, smul_eq_mul]

end MathlibBridge

end MiscMath.Probability
