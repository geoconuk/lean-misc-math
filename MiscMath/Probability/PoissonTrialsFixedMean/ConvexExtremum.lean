/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/

import MiscMath.Probability.PoissonTrialsFixedMean.Model

/-!
# Hoeffding's Theorem 3

Part of `MiscMath.Probability.PoissonTrialsFixedMean`, whose module docstring states the
result, its source and its scope, and where the reader should start. This file proves it:
the binomial maximises `E[g S]` at a fixed mean, for `g` convex on the integer grid.
-/

namespace MiscMath.Probability

open Finset

/-! ## Theorem 3: the binomial maximises `E[g S]` at a fixed mean

For `g` convex on the integer grid, `E[g S]` is maximised, among all `p` with a given mean,
by the **constant** vector — that is, by the binomial.

The proof is Hoeffding's two-coordinate exchange, in a form that **terminates**.
`bernExp_pair_le` is one exchange: the master identity with a sign supplied, needing only
*weak* grid convexity, with the range hypotheses imposed off the moved pair only (the
identity's factor never reads the moved coordinates). `exists_move` is the move, and it is
**not** the pairwise average, which never terminates for `#s ≥ 3`; it sends one coordinate
*exactly to* `μ` and gives its partner the slack, so one more coordinate is pinned at `μ` at
every step and the induction closes in at most `#s` steps. No compactness, no extreme-value
theorem and no limit of iterated averages appears anywhere.

Both halves of `p i ∈ [0,1]` are load-bearing for the inequality itself, not merely for its
interpretation: `hoeffding_thm3_needs_le_one` and `hoeffding_thm3_needs_nonneg` are witnesses
in which the model's weights are still perfectly well defined and still sum to `1`
(`sum_bernWt` has no hypothesis), yet the inequality **reverses**. -/

section Thm3

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

lemma bernWt_nonneg {s A : Finset ι} {p : ι → 𝕜} (hA : A ⊆ s)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) : 0 ≤ bernWt s p A := by
  refine mul_nonneg (Finset.prod_nonneg fun i hi => h0 i (hA hi)) ?_
  exact Finset.prod_nonneg fun i hi => by
    have := h1 i (Finset.mem_sdiff.mp hi).1
    linarith

/-- The convex factor of the master identity is `≥ 0`. The grid range consumed
is exactly the posed one: `#B + 2 ≤ #R + 2 = #s`. -/
lemma sum_bernWt_secondDiff_nonneg {R : Finset ι} {p : ι → 𝕜}
    (h0 : ∀ i ∈ R, 0 ≤ p i) (h1 : ∀ i ∈ R, p i ≤ 1) {g : ℕ → 𝕜}
    (hg : ∀ k, k ≤ R.card → 0 ≤ secondDiff g k) :
    0 ≤ ∑ B ∈ R.powerset, bernWt R p B * secondDiff g B.card := by
  refine Finset.sum_nonneg fun B hB => ?_
  have hBR : B ⊆ R := Finset.mem_powerset.mp hB
  exact mul_nonneg (bernWt_nonneg hBR h0 h1) (hg _ (Finset.card_le_card hBR))

/-- The strict version: with `p` in range some weight is positive, because the
weights sum to `1`, so a strictly convex `g` makes the factor strictly positive. -/
lemma sum_bernWt_secondDiff_pos {R : Finset ι} {p : ι → 𝕜}
    (h0 : ∀ i ∈ R, 0 ≤ p i) (h1 : ∀ i ∈ R, p i ≤ 1) {g : ℕ → 𝕜}
    (hg : ∀ k, k ≤ R.card → 0 < secondDiff g k) :
    0 < ∑ B ∈ R.powerset, bernWt R p B * secondDiff g B.card := by
  have hone : ∑ B ∈ R.powerset, (0 : 𝕜) < ∑ B ∈ R.powerset, bernWt R p B := by
    rw [Finset.sum_const, smul_zero, sum_bernWt]
    exact zero_lt_one
  obtain ⟨B₀, hB₀, hpos⟩ := Finset.exists_lt_of_sum_lt hone
  refine Finset.sum_pos' (fun B hB => ?_) ⟨B₀, hB₀, ?_⟩
  · have hBR : B ⊆ R := Finset.mem_powerset.mp hB
    exact mul_nonneg (bernWt_nonneg hBR h0 h1) (hg _ (Finset.card_le_card hBR)).le
  · have hBR : B₀ ⊆ R := Finset.mem_powerset.mp hB₀
    exact mul_pos hpos (hg _ (Finset.card_le_card hBR))

/-- **The exchange step.** A sum-preserving move of two coordinates that does
not decrease their product does not decrease `bernExp`, for `g` convex on the
grid. Only **weak** convexity is used, and the range hypotheses are imposed
**off the moved pair only** — `p i` and `p j` may be anything at all, because the
master identity's factor never reads them. -/
lemma bernExp_pair_le {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    {p q : ι → 𝕜} {g : ℕ → 𝕜}
    (hout : ∀ k ∈ s, k ≠ i → k ≠ j → q k = p k)
    (hsum : q i + q j = p i + p j) (hprod : p i * p j ≤ q i * q j)
    (h0 : ∀ k ∈ s, k ≠ i → k ≠ j → 0 ≤ p k) (h1 : ∀ k ∈ s, k ≠ i → k ≠ j → p k ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 ≤ secondDiff g k) :
    bernExp s p g ≤ bernExp s q g := by
  obtain ⟨R, hjR, hiR, hs, hcard⟩ := exists_pair_decomp hi hj hij
  subst hs
  have hRs : ∀ k ∈ R, k ∈ insert i (insert j R) := fun k hk =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)
  have hki : ∀ k ∈ R, k ≠ i := fun k hk h => hiR (h ▸ Finset.mem_insert_of_mem hk)
  have hkj : ∀ k ∈ R, k ≠ j := fun k hk h => hjR (h ▸ hk)
  have hout' : ∀ k ∈ R, q k = p k := fun k hk =>
    hout k (hRs k hk) (hki k hk) (hkj k hk)
  have key := bernExp_pair_sub hjR hiR p q g hout' hsum
  have hfac : 0 ≤ ∑ B ∈ R.powerset, bernWt R p B * secondDiff g B.card :=
    sum_bernWt_secondDiff_nonneg (fun k hk => h0 k (hRs k hk) (hki k hk) (hkj k hk))
      (fun k hk => h1 k (hRs k hk) (hki k hk) (hkj k hk)) (fun k hk => hg k (by omega))
  nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hfac]

/-- The strict exchange step: a *strictly* convex `g` and a *strict* increase of
the product give a strict increase of `bernExp`. -/
lemma bernExp_pair_lt {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    {p q : ι → 𝕜} {g : ℕ → 𝕜}
    (hout : ∀ k ∈ s, k ≠ i → k ≠ j → q k = p k)
    (hsum : q i + q j = p i + p j) (hprod : p i * p j < q i * q j)
    (h0 : ∀ k ∈ s, k ≠ i → k ≠ j → 0 ≤ p k) (h1 : ∀ k ∈ s, k ≠ i → k ≠ j → p k ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 < secondDiff g k) :
    bernExp s p g < bernExp s q g := by
  obtain ⟨R, hjR, hiR, hs, hcard⟩ := exists_pair_decomp hi hj hij
  subst hs
  have hRs : ∀ k ∈ R, k ∈ insert i (insert j R) := fun k hk =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk)
  have hki : ∀ k ∈ R, k ≠ i := fun k hk h => hiR (h ▸ Finset.mem_insert_of_mem hk)
  have hkj : ∀ k ∈ R, k ≠ j := fun k hk h => hjR (h ▸ hk)
  have hout' : ∀ k ∈ R, q k = p k := fun k hk =>
    hout k (hRs k hk) (hki k hk) (hkj k hk)
  have key := bernExp_pair_sub hjR hiR p q g hout' hsum
  have hfac : 0 < ∑ B ∈ R.powerset, bernWt R p B * secondDiff g B.card :=
    sum_bernWt_secondDiff_pos (fun k hk => h0 k (hRs k hk) (hki k hk) (hkj k hk))
      (fun k hk => h1 k (hRs k hk) (hki k hk) (hkj k hk)) (fun k hk => hg k (by omega))
  nlinarith [mul_pos (sub_pos.mpr hprod) hfac]

omit [DecidableEq ι] in
/-- One step of the induction: from any `p` not identically `μ` on `s`, a
sum-preserving pair move that strictly increases the pair product and strictly
decreases the number of coordinates away from `μ`.

This is **not** the pairwise average: averaging a pair leaves both coordinates off the mean
whenever the pair does not straddle it symmetrically, so iterated averaging only converges
and never terminates for `#s ≥ 3`. Instead one coordinate is sent *exactly to* `μ` and its
partner takes the slack. -/
lemma exists_move {s : Finset ι} {p : ι → 𝕜} {μ : 𝕜}
    (h0 : ∀ k ∈ s, 0 ≤ p k) (h1 : ∀ k ∈ s, p k ≤ 1)
    (hmean : ∑ k ∈ s, p k = s.card * μ) (hne : ∃ k ∈ s, p k ≠ μ) :
    ∃ (q : ι → 𝕜) (i j : ι), i ∈ s ∧ j ∈ s ∧ i ≠ j
      ∧ (∀ k ∈ s, 0 ≤ q k) ∧ (∀ k ∈ s, q k ≤ 1)
      ∧ (∑ k ∈ s, q k = s.card * μ)
      ∧ ((s.filter fun k => q k ≠ μ).card < (s.filter fun k => p k ≠ μ).card)
      ∧ (∀ k ∈ s, k ≠ i → k ≠ j → q k = p k)
      ∧ q i + q j = p i + p j
      ∧ p i * p j < q i * q j := by
  classical
  obtain ⟨k₀, hk₀s, hk₀⟩ := hne
  have hlow : ∃ i ∈ s, p i < μ := by
    by_contra hcon
    push Not at hcon
    have hlt : ∑ _k ∈ s, (μ : 𝕜) < ∑ k ∈ s, p k :=
      Finset.sum_lt_sum (fun k hk => hcon k hk)
        ⟨k₀, hk₀s, lt_of_le_of_ne (hcon k₀ hk₀s) (Ne.symm hk₀)⟩
    rw [Finset.sum_const, nsmul_eq_mul, hmean] at hlt
    exact lt_irrefl _ hlt
  have hhigh : ∃ j ∈ s, μ < p j := by
    by_contra hcon
    push Not at hcon
    have hlt : ∑ k ∈ s, p k < ∑ _k ∈ s, (μ : 𝕜) :=
      Finset.sum_lt_sum (fun k hk => hcon k hk) ⟨k₀, hk₀s, lt_of_le_of_ne (hcon k₀ hk₀s) hk₀⟩
    rw [Finset.sum_const, nsmul_eq_mul, hmean] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨i, his, hi⟩ := hlow
  obtain ⟨j, hjs, hj⟩ := hhigh
  have hij : i ≠ j := by rintro rfl; linarith
  refine ⟨Function.update (Function.update p i μ) j (p i + p j - μ), i, j, his, hjs, hij, ?_⟩
  set q := Function.update (Function.update p i μ) j (p i + p j - μ) with hqdef
  have hqi : q i = μ := by
    rw [hqdef, Function.update_of_ne hij, Function.update_self]
  have hqj : q j = p i + p j - μ := by rw [hqdef, Function.update_self]
  have hqk : ∀ k, k ≠ i → k ≠ j → q k = p k := fun k hki hkj => by
    rw [hqdef, Function.update_of_ne hkj, Function.update_of_ne hki]
  have hpi0 : 0 ≤ p i := h0 i his
  have hpj1 : p j ≤ 1 := h1 j hjs
  refine ⟨?_, ?_, ?_, ?_, fun k hk => hqk k, ?_, ?_⟩
  · intro k hk
    by_cases hki : k = i
    · subst hki; rw [hqi]; linarith
    by_cases hkj : k = j
    · subst hkj; rw [hqj]; linarith
    · rw [hqk k hki hkj]; exact h0 k hk
  · intro k hk
    by_cases hki : k = i
    · subst hki; rw [hqi]; linarith
    by_cases hkj : k = j
    · subst hkj; rw [hqj]; linarith
    · rw [hqk k hki hkj]; exact h1 k hk
  · have hij' : i ∈ s \ ({j} : Finset ι) := Finset.mem_sdiff.mpr ⟨his, by simp [hij]⟩
    have e1 : ∑ k ∈ s, q k = (p i + p j - μ) + ∑ k ∈ s \ {j}, (Function.update p i μ) k :=
      Finset.sum_update_of_mem hjs _ _
    have e2 : ∑ k ∈ s \ {j}, (Function.update p i μ) k = μ + ∑ k ∈ (s \ {j}) \ {i}, p k :=
      Finset.sum_update_of_mem hij' _ _
    have e3 : ∑ k ∈ s, p k = p j + ∑ k ∈ s \ {j}, p k := by
      have := Finset.sum_update_of_mem hjs p (p j)
      rwa [Function.update_eq_self] at this
    have e4 : ∑ k ∈ s \ {j}, p k = p i + ∑ k ∈ (s \ {j}) \ {i}, p k := by
      have := Finset.sum_update_of_mem hij' p (p i)
      rwa [Function.update_eq_self] at this
    rw [e1, e2, ← hmean, e3, e4]; ring
  · have hss : (s.filter fun k => q k ≠ μ) ⊆ (s.filter fun k => p k ≠ μ) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, ?_⟩
      by_cases hki : k = i
      · exact absurd (hki ▸ hqi) hk.2
      by_cases hkj : k = j
      · exact hkj ▸ hj.ne'
      · rw [← hqk k hki hkj]; exact hk.2
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hss).mpr ⟨i, ?_, ?_⟩)
    · exact Finset.mem_filter.mpr ⟨his, hi.ne⟩
    · exact fun hmem => (Finset.mem_filter.mp hmem).2 hqi
  · rw [hqi, hqj]; ring
  · rw [hqi, hqj]
    nlinarith [mul_pos (sub_pos.mpr hi) (sub_pos.mpr hj)]

/-- **Theorem 3, the inequality half.** For `g` convex on the integer grid
`0, …, #s - 2`, the constant vector `μ` maximises `bernExp` over all `[0,1]`-valued `p`
with mean `μ`. Only **weak** convexity is assumed. -/
theorem bernExp_le_const {s : Finset ι} {p : ι → 𝕜} {g : ℕ → 𝕜} {μ : 𝕜}
    (h0 : ∀ k ∈ s, 0 ≤ p k) (h1 : ∀ k ∈ s, p k ≤ 1)
    (hmean : ∑ k ∈ s, p k = s.card * μ)
    (hg : ∀ k, k + 2 ≤ s.card → 0 ≤ secondDiff g k) :
    bernExp s p g ≤ bernExp s (fun _ => μ) g := by
  classical
  suffices H : ∀ d : ℕ, ∀ p : ι → 𝕜, (s.filter fun k => p k ≠ μ).card ≤ d →
      (∀ k ∈ s, 0 ≤ p k) → (∀ k ∈ s, p k ≤ 1) → (∑ k ∈ s, p k = s.card * μ) →
      bernExp s p g ≤ bernExp s (fun _ => μ) g from
    H _ p le_rfl h0 h1 hmean
  intro d
  induction d with
  | zero =>
    intro p hcard _ _ _
    have hall : ∀ k ∈ s, p k = μ := by
      intro k hk
      by_contra hne
      have : k ∈ s.filter fun k => p k ≠ μ := Finset.mem_filter.mpr ⟨hk, hne⟩
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at this
      exact absurd this (Finset.notMem_empty k)
    exact le_of_eq (bernExp_congr hall g)
  | succ d ih =>
    intro p hcard hp0 hp1 hpmean
    by_cases hne : ∃ k ∈ s, p k ≠ μ
    · obtain ⟨q, i, j, his, hjs, hij, hq0, hq1, hqmean, hqcard, hqout, hqsum, hqprod⟩ :=
        exists_move hp0 hp1 hpmean hne
      exact le_trans (bernExp_pair_le his hjs hij hqout hqsum hqprod.le
          (fun k hk _ _ => hp0 k hk) (fun k hk _ _ => hp1 k hk) hg)
        (ih q (by omega) hq0 hq1 hqmean)
    · push Not at hne
      exact le_of_eq (bernExp_congr hne g)

/-- **The strict form.** Under strict grid convexity a single coordinate away
from `μ` already forces strict inequality. -/
theorem bernExp_lt_const {s : Finset ι} {p : ι → 𝕜} {g : ℕ → 𝕜} {μ : 𝕜}
    (h0 : ∀ k ∈ s, 0 ≤ p k) (h1 : ∀ k ∈ s, p k ≤ 1)
    (hmean : ∑ k ∈ s, p k = s.card * μ)
    (hg : ∀ k, k + 2 ≤ s.card → 0 < secondDiff g k)
    (hne : ∃ k ∈ s, p k ≠ μ) :
    bernExp s p g < bernExp s (fun _ => μ) g := by
  obtain ⟨q, i, j, his, hjs, hij, hq0, hq1, hqmean, -, hqout, hqsum, hqprod⟩ :=
    exists_move h0 h1 hmean hne
  exact lt_of_lt_of_le (bernExp_pair_lt his hjs hij hqout hqsum hqprod
      (fun k hk _ _ => h0 k hk) (fun k hk _ _ => h1 k hk) hg)
    (bernExp_le_const hq0 hq1 hqmean (fun k hk => (hg k hk).le))

/-- **The equality clause**, both directions. -/
theorem bernExp_eq_const_iff {s : Finset ι} {p : ι → 𝕜} {g : ℕ → 𝕜} {μ : 𝕜}
    (h0 : ∀ k ∈ s, 0 ≤ p k) (h1 : ∀ k ∈ s, p k ≤ 1)
    (hmean : ∑ k ∈ s, p k = s.card * μ)
    (hg : ∀ k, k + 2 ≤ s.card → 0 < secondDiff g k) :
    bernExp s p g = bernExp s (fun _ => μ) g ↔ ∀ k ∈ s, p k = μ := by
  constructor
  · intro heq
    by_contra hcon
    push Not at hcon
    exact absurd heq (ne_of_lt (bernExp_lt_const h0 h1 hmean hg hcon))
  · intro hall
    exact bernExp_congr hall g

/-- The **concave** companion, free from `g ↦ -g`: for `g` concave on the grid
the constant vector *minimises*. -/
theorem bernExp_ge_const_concave {s : Finset ι} {p : ι → 𝕜} {g : ℕ → 𝕜} {μ : 𝕜}
    (h0 : ∀ k ∈ s, 0 ≤ p k) (h1 : ∀ k ∈ s, p k ≤ 1)
    (hmean : ∑ k ∈ s, p k = s.card * μ)
    (hg : ∀ k, k + 2 ≤ s.card → secondDiff g k ≤ 0) :
    bernExp s (fun _ => μ) g ≤ bernExp s p g := by
  have key := bernExp_le_const (g := fun k => -g k) h0 h1 hmean (fun k hk => by
    have := hg k hk
    simp only [secondDiff] at this ⊢
    linarith)
  rw [bernExp_neg, bernExp_neg] at key
  linarith

end Thm3

section Thm3ClosedForm

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Hoeffding (1956), Theorem 3.** `S` is the number of successes in the
independent trials indexed by `s`, with success probabilities `p`, and `p̄` is
their average. For `g` convex on the integer grid `0, …, #s - 2`,

`E[g S] ≤ ∑_{k ≤ #s} g k · C(#s,k) · p̄^k (1 - p̄)^{#s-k}`.

The hypothesis is **weak** grid convexity; the paper asks for strict convexity, which is
needed only for the equality clause `hoeffding_thm3_eq_iff`. -/
theorem hoeffding_thm3 {s : Finset ι} (p : ι → 𝕜) (g : ℕ → 𝕜)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 ≤ g (k + 2) - 2 * g (k + 1) + g k) :
    bernExp s p g
      ≤ ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : 𝕜)
          * ((∑ i ∈ s, p i) / s.card) ^ k
          * (1 - (∑ i ∈ s, p i) / s.card) ^ (s.card - k) := by
  set μ : 𝕜 := (∑ i ∈ s, p i) / s.card with hμ
  have hmean : ∑ i ∈ s, p i = s.card * μ := by
    rw [hμ]
    rcases Nat.eq_zero_or_pos s.card with hc | hc
    · rw [hc, Finset.card_eq_zero.mp hc]
      simp
    · have : (s.card : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
  have hle := bernExp_le_const (s := s) (p := p) (g := g) (μ := μ) h0 h1 hmean hg
  rw [bernExp_const] at hle
  exact hle.trans_eq (Finset.sum_congr rfl fun k _ => by ring)

/-- The **equality clause**: under strict grid convexity, equality holds exactly
when every `p i` equals the average. -/
theorem hoeffding_thm3_eq_iff {s : Finset ι} (p : ι → 𝕜) (g : ℕ → 𝕜)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1)
    (hg : ∀ k, k + 2 ≤ s.card → 0 < g (k + 2) - 2 * g (k + 1) + g k) :
    (bernExp s p g
        = ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : 𝕜)
            * ((∑ i ∈ s, p i) / s.card) ^ k
            * (1 - (∑ i ∈ s, p i) / s.card) ^ (s.card - k))
      ↔ ∀ i ∈ s, p i = (∑ i ∈ s, p i) / s.card := by
  set μ : 𝕜 := (∑ i ∈ s, p i) / s.card with hμ
  have hmean : ∑ i ∈ s, p i = s.card * μ := by
    rw [hμ]
    rcases Nat.eq_zero_or_pos s.card with hc | hc
    · rw [hc, Finset.card_eq_zero.mp hc]
      simp
    · have : (s.card : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
  have hrhs : ∑ k ∈ range (s.card + 1), g k * (s.card.choose k : 𝕜) * μ ^ k
        * (1 - μ) ^ (s.card - k)
      = bernExp s (fun _ => μ) g := by
    rw [bernExp_const]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hrhs]
  exact bernExp_eq_const_iff h0 h1 hmean hg

end Thm3ClosedForm

/-! ### Necessity witnesses for Theorem 3

Each hypothesis of Theorem 3 is load-bearing, and each of the three witnesses below is a
machine-checked instance rather than an assertion. The two range witnesses are worth reading
carefully: the model's weights are perfectly well defined outside `[0,1]` and still sum to
`1` (`sum_bernWt` has no hypothesis at all), so what fails is `bernWt ≥ 0` — and then the
inequality **reverses**. -/

section Thm3Witnesses

/-- **The strictness in the convexity hypothesis is load-bearing exactly where
the equality clause needs it, and nowhere else.** At `#s = 2` with `g = id` —
convex on the grid (`secondDiff g ≡ 0`) but not strictly — `p = (0,1)` has mean
`1/2`, both sides are equal, and `p` is not constant. So
`bernExp_eq_const_iff` genuinely needs `0 < secondDiff g k`, while
`bernExp_le_const` is unaffected. -/
theorem hoeffding_thm3_eq_needs_strict :
    (∀ k, k + 2 ≤ (range 2).card → (0 : ℝ) ≤ secondDiff (fun m => (m : ℝ)) k)
      ∧ (∑ j ∈ range 2, (if j = 0 then (0 : ℝ) else 1)
          = (range 2).card * (1 / 2 : ℝ))
      ∧ bernExp (range 2) (fun j => if j = 0 then (0 : ℝ) else 1) (fun m => (m : ℝ))
          = bernExp (range 2) (fun _ => (1 / 2 : ℝ)) (fun m => (m : ℝ))
      ∧ ¬ (∀ j ∈ range 2, (if j = 0 then (0 : ℝ) else 1) = (1 / 2 : ℝ)) := by
  refine ⟨fun k _ => ?_, ?_, ?_, ?_⟩
  · have hz : secondDiff (fun m => (m : ℝ)) k = 0 := by simp only [secondDiff]; push_cast; ring
    rw [hz]
  · norm_num [Finset.sum_range_succ]
  · have h2 : (range 2 : Finset ℕ) = {0, 1} := by decide +kernel
    rw [h2, bernExp_pair (by norm_num), bernExp_pair (by norm_num)]
    norm_num
  · intro hall
    have := hall 0 (Finset.mem_range.mpr (by norm_num))
    norm_num at this

/-- **The bound `p i ≤ 1` cannot be dropped**, and not merely for interpretation:
the inequality **reverses**. Witness at `#s = 3`: `p = (3/2, 3/2, 0)`, which
keeps `0 ≤ p i` and has mean `1`, against `g = (0,0,5,11)`, strictly convex on
the grid (`secondDiff g = (5,1)`). The left-hand side is `45/4`, the comparator
is `11`.

This is not a counterexample to Theorem 3: `p` is not a probability vector, so
the witness lies outside the theorem's setting. It records that the setting is
load-bearing for the mathematics, not only for the reading. -/
theorem hoeffding_thm3_needs_le_one :
    (∀ j ∈ range 3, (0 : ℝ) ≤ (if j = 2 then 0 else 3 / 2))
      ∧ ¬ (∀ j ∈ range 3, (if j = 2 then (0 : ℝ) else 3 / 2) ≤ 1)
      ∧ (∀ k, k + 2 ≤ (range 3).card →
          (0 : ℝ) < secondDiff (fun m => if m = 2 then 5 else if m = 3 then 11 else 0) k)
      ∧ (∑ j ∈ range 3, (if j = 2 then (0 : ℝ) else 3 / 2) = (range 3).card * (1 : ℝ))
      ∧ bernExp (range 3) (fun _ => (1 : ℝ))
            (fun m => if m = 2 then 5 else if m = 3 then 11 else 0)
          < bernExp (range 3) (fun j => if j = 2 then (0 : ℝ) else 3 / 2)
            (fun m => if m = 2 then 5 else if m = 3 then 11 else 0) := by
  have h3 : (range 3 : Finset ℕ) = {0, 1, 2} := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _; split <;> norm_num
  · intro hall
    have := hall 0 (Finset.mem_range.mpr (by norm_num))
    norm_num at this
  · intro k hk
    simp only [Finset.card_range] at hk
    match k, hk with
    | 0, _ => norm_num [secondDiff]
    | 1, _ => norm_num [secondDiff]
  · norm_num [Finset.sum_range_succ]
  · rw [h3, bernExp_triple (by norm_num) (by norm_num) (by norm_num),
      bernExp_triple (by norm_num) (by norm_num) (by norm_num)]
    norm_num

/-- **The other bound `0 ≤ p i` cannot be dropped either**, so neither half of
`p i ∈ [0,1]` is redundant. Witness at `#s = 3`: `p = (-1,-1,1)`, which keeps
`p i ≤ 1` and has mean `-1/3`, against `g = (0,0,1,7)`, strictly convex on the
grid (`secondDiff g = (1,5)`). The left-hand side is `3`, the comparator is
`5/27`. -/
theorem hoeffding_thm3_needs_nonneg :
    (∀ j ∈ range 3, (if j = 2 then (1 : ℝ) else -1) ≤ 1)
      ∧ ¬ (∀ j ∈ range 3, (0 : ℝ) ≤ (if j = 2 then (1 : ℝ) else -1))
      ∧ (∀ k, k + 2 ≤ (range 3).card →
          (0 : ℝ) < secondDiff (fun m => if m = 2 then 1 else if m = 3 then 7 else 0) k)
      ∧ (∑ j ∈ range 3, (if j = 2 then (1 : ℝ) else -1)
          = (range 3).card * (-1 / 3 : ℝ))
      ∧ bernExp (range 3) (fun _ => (-1 / 3 : ℝ))
            (fun m => if m = 2 then 1 else if m = 3 then 7 else 0)
          < bernExp (range 3) (fun j => if j = 2 then (1 : ℝ) else -1)
            (fun m => if m = 2 then 1 else if m = 3 then 7 else 0) := by
  have h3 : (range 3 : Finset ℕ) = {0, 1, 2} := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _; split <;> norm_num
  · intro hall
    have := hall 0 (Finset.mem_range.mpr (by norm_num))
    norm_num at this
  · intro k hk
    simp only [Finset.card_range] at hk
    match k, hk with
    | 0, _ => norm_num [secondDiff]
    | 1, _ => norm_num [secondDiff]
  · norm_num [Finset.sum_range_succ]
  · rw [h3, bernExp_triple (by norm_num) (by norm_num) (by norm_num),
      bernExp_triple (by norm_num) (by norm_num) (by norm_num)]
    norm_num

end Thm3Witnesses

end MiscMath.Probability
