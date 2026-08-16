/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/

import MiscMath.Probability.PoissonTrialsFixedMean.BinomialTail
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Independent Bernoulli trials, at the `Finset` level

Infrastructure for `MiscMath.Probability.PoissonTrialsFixedMean`, which is where the results
are stated and where the reader should start. This file carries the model — `bernWt`,
`bernExp`, `tailLe` — and the master pair identity every argument in the library rests on.
`PoissonTrialsFixedMean.Bridge` identifies the model with a product of Mathlib
`ProbabilityTheory.bernoulliMeasure`s.
-/

namespace MiscMath.Probability

open Finset

/-! ## The model: independent Bernoulli trials, at the `Finset` level

The sample space is `s.powerset` — the possible sets of successful trials — the weight of a
success set `A` is

    bernWt s p A = (∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i),

and the statistic is `S = #A`, so that `bernExp s p g = E[g S]`. Nothing is assumed about
`p` in the definitions; the range hypotheses `0 ≤ p i ≤ 1` are carried by the theorems that
need them, and where they are *not* needed this is said.

Everything here is stated for an arbitrary index type, an arbitrary ground set `s : Finset ι`
and an arbitrary `CommRing`; the order and the range hypotheses enter only from Theorem 3
onwards. `bernExp_eq_integral_pi_bernoulliMeasure`, in `PoissonTrialsFixedMean.Bridge`,
identifies this with a product of Mathlib `bernoulliMeasure`s.

`bernExp_pair_sub` is the one computation of the development: every inequality in the two
sections that follow is this identity with a sign supplied. It is proved by splitting the
powerset on the two moved coordinates, which is `Finset.sum_powerset_insert` twice. -/

section Model

variable {ι : Type*} [DecidableEq ι] {𝕜 : Type*} [CommRing 𝕜]

/-- The Bernoulli product weight of the success set `A` among the trials `s`:
`(∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)`. No hypothesis on `p`. -/
def bernWt (s : Finset ι) (p : ι → 𝕜) (A : Finset ι) : 𝕜 :=
  (∏ i ∈ A, p i) * ∏ i ∈ s \ A, (1 - p i)

/-- `E[g S]`, where `S = #A` is the number of successes. -/
def bernExp (s : Finset ι) (p : ι → 𝕜) (g : ℕ → 𝕜) : 𝕜 :=
  ∑ A ∈ s.powerset, bernWt s p A * g A.card

/-- The second difference of `g` on the integer grid: `g (k+2) - 2 g (k+1) + g k`.
Grid convexity is `0 ≤ secondDiff g k`, strict grid convexity `0 < secondDiff g k`. -/
def secondDiff (g : ℕ → 𝕜) (k : ℕ) : 𝕜 := g (k + 2) - 2 * g (k + 1) + g k

@[simp] lemma bernWt_empty (p : ι → 𝕜) (A : Finset ι) :
    bernWt (∅ : Finset ι) p A = ∏ i ∈ A, p i := by
  simp [bernWt]

/-- The weights sum to `1`. This is `Finset.prod_add` and nothing else — in
particular it needs **no hypothesis on `p` at all**, which is what makes the
necessity witnesses for Theorem 3 possible: outside `[0,1]` the weights are still
a (signed) unit mass. -/
lemma sum_bernWt (s : Finset ι) (p : ι → 𝕜) :
    ∑ A ∈ s.powerset, bernWt s p A = 1 := by
  have h := Finset.prod_add (fun i => p i) (fun i => 1 - p i) s
  simpa [bernWt] using h.symm

/-- `bernWt s p A` only reads `p` on `s`. -/
lemma bernWt_congr {s A : Finset ι} {p q : ι → 𝕜} (hA : A ⊆ s)
    (h : ∀ i ∈ s, p i = q i) : bernWt s p A = bernWt s q A := by
  unfold bernWt
  congr 1
  · exact Finset.prod_congr rfl fun i hi => h i (hA hi)
  · exact Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_sdiff.mp hi).1]

/-- `bernExp s p g` only reads `p` on `s`. -/
lemma bernExp_congr {s : Finset ι} {p q : ι → 𝕜} (h : ∀ i ∈ s, p i = q i) (g : ℕ → 𝕜) :
    bernExp s p g = bernExp s q g := by
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [bernWt_congr (Finset.mem_powerset.mp hA) h]

lemma bernExp_neg (s : Finset ι) (p : ι → 𝕜) (g : ℕ → 𝕜) :
    bernExp s p (fun k => -g k) = -bernExp s p g := by
  simp only [bernExp, mul_neg, Finset.sum_neg_distrib]

lemma bernExp_zero_fun (s : Finset ι) (p : ι → 𝕜) :
    bernExp s p (fun _ => 0) = 0 := by
  rw [bernExp]
  exact Finset.sum_eq_zero fun A _ => by ring

lemma bernWt_insert_notMem {s A : Finset ι} {i : ι} (hi : i ∉ s) (hA : A ⊆ s) (p : ι → 𝕜) :
    bernWt (insert i s) p A = (1 - p i) * bernWt s p A := by
  have hiA : i ∉ A := fun h => hi (hA h)
  have hset : (insert i s) \ A = insert i (s \ A) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, hiA⟩
      · exact ⟨Or.inr h1, h2⟩
  have hnot : i ∉ s \ A := fun h => hi (Finset.mem_sdiff.mp h).1
  unfold bernWt
  rw [hset, Finset.prod_insert hnot]
  ring

lemma bernWt_insert_mem {s A : Finset ι} {i : ι} (hi : i ∉ s) (hA : A ⊆ s) (p : ι → 𝕜) :
    bernWt (insert i s) p (insert i A) = p i * bernWt s p A := by
  have hiA : i ∉ A := fun h => hi (hA h)
  have hset : (insert i s) \ (insert i A) = s \ A := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨h | h, hne, hx⟩
      · exact absurd h hne
      · exact ⟨h, hx⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, fun hx => hi (hx ▸ h1), h2⟩
  unfold bernWt
  rw [hset, Finset.prod_insert hiA]
  ring

end Model

section Split

variable {ι : Type*} [DecidableEq ι]

/-- Splitting a powerset sum on two distinct elements. Bookkeeping only: four
applications of `Finset.sum_powerset_insert`. -/
lemma sum_powerset_split_two {M : Type*} [AddCommMonoid M] {R : Finset ι} {i j : ι}
    (hj : j ∉ R) (hi : i ∉ insert j R) (F : Finset ι → M) :
    ∑ A ∈ (insert i (insert j R)).powerset, F A
      = ∑ B ∈ R.powerset,
          (F B + F (insert j B) + F (insert i B) + F (insert i (insert j B))) := by
  rw [Finset.sum_powerset_insert hi, Finset.sum_powerset_insert hj,
    Finset.sum_powerset_insert hj]
  simp only [Finset.sum_add_distrib]
  exact (add_assoc _ _ _).symm

variable {𝕜 : Type*} [CommRing 𝕜]

/-- The powerset sum split on the pair `{i, j}`: the inner bracket is the
three-point expectation of `g` given the successes outside the pair. -/
lemma bernExp_pair_expand {R : Finset ι} {i j : ι} (hj : j ∉ R) (hi : i ∉ insert j R)
    (p : ι → 𝕜) (g : ℕ → 𝕜) :
    bernExp (insert i (insert j R)) p g
      = ∑ B ∈ R.powerset, bernWt R p B *
          ((1 - p i) * (1 - p j) * g B.card
            + ((1 - p i) * p j + p i * (1 - p j)) * g (B.card + 1)
            + p i * p j * g (B.card + 2)) := by
  rw [bernExp, sum_powerset_split_two hj hi]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hBR : B ⊆ R := Finset.mem_powerset.mp hB
  have hjB : j ∉ B := fun h => hj (hBR h)
  have hBjR : B ⊆ insert j R := hBR.trans (Finset.subset_insert _ _)
  have hjBjR : insert j B ⊆ insert j R := Finset.insert_subset_insert _ hBR
  have hiB : i ∉ insert j B := by
    intro h
    rcases Finset.mem_insert.mp h with rfl | h'
    · exact hi (Finset.mem_insert_self _ _)
    · exact hi (Finset.mem_insert_of_mem (hBR h'))
  have w0 : bernWt (insert i (insert j R)) p B = (1 - p i) * ((1 - p j) * bernWt R p B) := by
    rw [bernWt_insert_notMem hi hBjR, bernWt_insert_notMem hj hBR]
  have w1 : bernWt (insert i (insert j R)) p (insert j B)
      = (1 - p i) * (p j * bernWt R p B) := by
    rw [bernWt_insert_notMem hi hjBjR, bernWt_insert_mem hj hBR]
  have w2 : bernWt (insert i (insert j R)) p (insert i B)
      = p i * ((1 - p j) * bernWt R p B) := by
    rw [bernWt_insert_mem hi hBjR, bernWt_insert_notMem hj hBR]
  have w3 : bernWt (insert i (insert j R)) p (insert i (insert j B))
      = p i * (p j * bernWt R p B) := by
    rw [bernWt_insert_mem hi hjBjR, bernWt_insert_mem hj hBR]
  have c1 : (insert j B).card = B.card + 1 := Finset.card_insert_of_notMem hjB
  have c2 : (insert i B).card = B.card + 1 :=
    Finset.card_insert_of_notMem (fun h => hiB (Finset.mem_insert_of_mem h))
  have c3 : (insert i (insert j B)).card = B.card + 2 := by
    rw [Finset.card_insert_of_notMem hiB, c1]
  rw [w0, w1, w2, w3, c1, c2, c3]
  ring

/-- **The master identity.** Along any move of the pair `(p i, p j)` that
preserves the *sum*, the expectation changes by the change in the **product**
times a factor that never reads `p i` or `p j`. No sign hypothesis, no
convexity, and no range hypothesis. -/
lemma bernExp_pair_sub {R : Finset ι} {i j : ι} (hj : j ∉ R) (hi : i ∉ insert j R)
    (p q : ι → 𝕜) (g : ℕ → 𝕜) (hout : ∀ k ∈ R, q k = p k)
    (hsum : q i + q j = p i + p j) :
    bernExp (insert i (insert j R)) q g - bernExp (insert i (insert j R)) p g
      = (q i * q j - p i * p j) * ∑ B ∈ R.powerset, bernWt R p B * secondDiff g B.card := by
  rw [bernExp_pair_expand hj hi q g, bernExp_pair_expand hj hi p g, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hBR : B ⊆ R := Finset.mem_powerset.mp hB
  have hw : bernWt R q B = bernWt R p B := bernWt_congr hBR (fun k hk => hout k hk)
  rw [hw, secondDiff]
  linear_combination (bernWt R p B * (g (B.card + 1) - g B.card)) * hsum

/-- Peel two distinct elements off a ground set. -/
lemma exists_pair_decomp {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∃ R : Finset ι, j ∉ R ∧ i ∉ insert j R ∧ insert i (insert j R) = s
      ∧ R.card + 2 = s.card := by
  refine ⟨s \ ({i, j} : Finset ι), by simp, by simp [hij], ?_, ?_⟩
  · ext x
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | ⟨h, -⟩)
      · exact hi
      · exact hj
      · exact h
    · intro hx
      by_cases h1 : x = i
      · exact Or.inl h1
      by_cases h2 : x = j
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨hx, by tauto⟩)
  · have hsub : ({i, j} : Finset ι) ⊆ s := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hi
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hj
    have h2 : ({i, j} : Finset ι).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
    have := Finset.card_sdiff_add_card_eq_card hsub
    omega

/-- `s` peeled at a distinct pair, with the explicit remainder `s \ {i,j}` — the
form the pair-move argument for Corollary 2.1 needs. -/
lemma pair_decomp {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    j ∉ s \ ({i, j} : Finset ι) ∧ i ∉ insert j (s \ ({i, j} : Finset ι))
      ∧ insert i (insert j (s \ ({i, j} : Finset ι))) = s := by
  refine ⟨by simp, by simp [hij], ?_⟩
  ext x
  simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | ⟨h, -⟩)
    · exact hi
    · exact hj
    · exact h
  · intro hx
    by_cases h1 : x = i
    · exact Or.inl h1
    by_cases h2 : x = j
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨hx, by tauto⟩)

end Split

/-! ### The closed form at a constant vector: the model is the binomial -/

section ClosedForm

variable {ι : Type*} [DecidableEq ι] {𝕜 : Type*} [CommRing 𝕜]

lemma bernWt_const {s A : Finset ι} (hA : A ⊆ s) (P : 𝕜) :
    bernWt s (fun _ => P) A = P ^ A.card * (1 - P) ^ (s.card - A.card) := by
  rw [bernWt, Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset hA]

/-- **At a constant vector the model is the binomial**: the powerset sum
collapses to `∑_{k ≤ #s} C(#s,k) P^k (1-P)^{#s-k} g k`. -/
theorem bernExp_const (s : Finset ι) (P : 𝕜) (g : ℕ → 𝕜) :
    bernExp s (fun _ => P) g
      = ∑ k ∈ range (s.card + 1),
          (s.card.choose k : 𝕜) * P ^ k * (1 - P) ^ (s.card - k) * g k := by
  have hpt : ∀ A ∈ s.powerset, bernWt s (fun _ => P) A * g A.card
      = (fun k => P ^ k * (1 - P) ^ (s.card - k) * g k) A.card := fun A hA => by
    rw [bernWt_const (Finset.mem_powerset.mp hA)]
  refine (Finset.sum_congr rfl hpt).trans ?_
  rw [Finset.sum_powerset_apply_card (fun k => P ^ k * (1 - P) ^ (s.card - k) * g k)]
  exact Finset.sum_congr rfl fun k _ => by rw [nsmul_eq_mul]; ring

/-- Explicit expansion on a two-element ground set, for the numerical witnesses. -/
lemma bernExp_pair {a b : ι} (hab : a ≠ b) (p : ι → 𝕜) (g : ℕ → 𝕜) :
    bernExp {a, b} p g
      = (1 - p a) * (1 - p b) * g 0 + ((1 - p a) * p b + p a * (1 - p b)) * g 1
        + p a * p b * g 2 := by
  have hb : b ∉ (∅ : Finset ι) := Finset.notMem_empty b
  have ha : a ∉ insert b (∅ : Finset ι) := by simpa using hab
  have hset : ({a, b} : Finset ι) = insert a (insert b (∅ : Finset ι)) := by simp
  rw [hset, bernExp_pair_expand hb ha]
  simp [bernWt]

/-- Explicit expansion on a three-element ground set, for the numerical witnesses. -/
lemma bernExp_triple {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : ι → 𝕜) (g : ℕ → 𝕜) :
    bernExp {a, b, c} p g
      = (1 - p c) * ((1 - p a) * (1 - p b) * g 0
            + ((1 - p a) * p b + p a * (1 - p b)) * g 1 + p a * p b * g 2)
        + p c * ((1 - p a) * (1 - p b) * g 1
            + ((1 - p a) * p b + p a * (1 - p b)) * g 2 + p a * p b * g 3) := by
  have hb : b ∉ ({c} : Finset ι) := by simpa using hbc
  have ha : a ∉ insert b ({c} : Finset ι) := by simp [hab, hac]
  have hps : ({c} : Finset ι).powerset = {∅, {c}} := by
    ext A; simp [Finset.subset_singleton_iff]
  rw [bernExp_pair_expand hb ha, hps, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp only [bernWt, Finset.prod_empty, Finset.sdiff_empty, Finset.prod_singleton,
    Finset.card_empty, Finset.card_singleton, Finset.sdiff_self, one_mul, mul_one,
    Nat.zero_add, Nat.reduceAdd]

end ClosedForm

/-! ### Conditioning on one trial, and the three-valued points -/

section ShapeEval

variable {ι : Type*} [DecidableEq ι] {𝕜 : Type*} [CommRing 𝕜]

/-- **Conditioning on one trial**: `E[g S] = (1 - p i) E[g S'] + p i E[g (S'+1)]`,
with `S'` the number of successes among the remaining trials. -/
lemma bernExp_insert {t : Finset ι} {i : ι} (hi : i ∉ t) (q : ι → 𝕜) (g : ℕ → 𝕜) :
    bernExp (insert i t) q g
      = (1 - q i) * bernExp t q g + q i * bernExp t q (fun r => g (r + 1)) := by
  classical
  rw [bernExp, Finset.sum_powerset_insert hi, bernExp, bernExp, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun A hA => ?_
    have hAt : A ⊆ t := Finset.mem_powerset.mp hA
    have hiA : i ∉ A := fun h => hi (hAt h)
    have hsd : (insert i t) \ A = insert i (t \ A) := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hy | hy, hy'⟩
        · exact Or.inl hy
        · exact Or.inr ⟨hy, hy'⟩
      · rintro (rfl | ⟨hy, hy'⟩)
        · exact ⟨Or.inl rfl, hiA⟩
        · exact ⟨Or.inr hy, hy'⟩
    have hnotmem : i ∉ t \ A := fun h => hi (Finset.mem_sdiff.mp h).1
    rw [bernWt, bernWt, hsd, Finset.prod_insert hnotmem]
    ring
  · refine Finset.sum_congr rfl fun A hA => ?_
    have hAt : A ⊆ t := Finset.mem_powerset.mp hA
    have hiA : i ∉ A := fun h => hi (hAt h)
    have hsd : (insert i t) \ (insert i A) = t \ A := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨hy | hy, hy'⟩
        · exact absurd hy hy'.1
        · exact ⟨hy, hy'.2⟩
      · rintro ⟨hy, hy'⟩
        exact ⟨Or.inr hy, fun h => hi (h ▸ hy), hy'⟩
    rw [bernWt, bernWt, hsd, Finset.prod_insert hiA, Finset.card_insert_of_notMem hiA]
    ring

/-- Peeling a coordinate pinned at `1`: it always succeeds, so the count shifts. -/
lemma bernExp_drop_one {s : Finset ι} {q : ι → 𝕜} {i : ι} (hi : i ∈ s) (hq : q i = 1)
    (g : ℕ → 𝕜) : bernExp s q g = bernExp (s.erase i) q (fun r => g (r + 1)) := by
  have hnot : i ∉ s.erase i := Finset.notMem_erase i s
  have h := bernExp_insert hnot q g
  rw [Finset.insert_erase hi, hq] at h
  rw [h]
  ring

/-- Peeling a coordinate pinned at `0`: it never succeeds, so nothing changes. -/
lemma bernExp_drop_zero {s : Finset ι} {q : ι → 𝕜} {i : ι} (hi : i ∈ s) (hq : q i = 0)
    (g : ℕ → 𝕜) : bernExp s q g = bernExp (s.erase i) q g := by
  have hnot : i ∉ s.erase i := Finset.notMem_erase i s
  have h := bernExp_insert hnot q g
  rw [Finset.insert_erase hi, hq] at h
  rw [h]
  ring

/-- All the `1`-coordinates peel off at once, shifting `g` by their number. -/
lemma bernExp_drop_ones {q : ι → 𝕜} (O : Finset ι) :
    ∀ (s : Finset ι), O ⊆ s → (∀ i ∈ O, q i = 1) → ∀ g : ℕ → 𝕜,
      bernExp s q g = bernExp (s \ O) q (fun r => g (r + O.card)) := by
  classical
  induction O using Finset.induction_on with
  | empty => intro s _ _ g; simp
  | @insert i O' hi ih =>
      intro s hsub hone g
      have hiS : i ∈ s := hsub (Finset.mem_insert_self _ _)
      have hO'sub : O' ⊆ s.erase i := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hj), hsub (Finset.mem_insert_of_mem hj)⟩
      have hstep := bernExp_drop_one hiS (hone i (Finset.mem_insert_self _ _)) g
      rw [hstep, ih (s.erase i) hO'sub (fun j hj => hone j (Finset.mem_insert_of_mem hj))
        (fun r => g (r + 1))]
      have hset : (s.erase i) \ O' = s \ insert i O' := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
        tauto
      have hcard : (insert i O').card = O'.card + 1 := Finset.card_insert_of_notMem hi
      rw [hset, hcard]
      congr 1

/-- All the `0`-coordinates peel off at once, changing nothing. -/
lemma bernExp_drop_zeros {q : ι → 𝕜} (Z : Finset ι) :
    ∀ (s : Finset ι), Z ⊆ s → (∀ i ∈ Z, q i = 0) → ∀ g : ℕ → 𝕜,
      bernExp s q g = bernExp (s \ Z) q g := by
  classical
  induction Z using Finset.induction_on with
  | empty => intro s _ _ g; simp
  | @insert i Z' hi ih =>
      intro s hsub hzero g
      have hiS : i ∈ s := hsub (Finset.mem_insert_self _ _)
      have hZ'sub : Z' ⊆ s.erase i := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hj), hsub (Finset.mem_insert_of_mem hj)⟩
      rw [bernExp_drop_zero hiS (hzero i (Finset.mem_insert_self _ _)) g,
        ih (s.erase i) hZ'sub (fun j hj => hzero j (Finset.mem_insert_of_mem hj)) g]
      congr 1
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
      tauto

/-- **The three-valued evaluation.** At a point taking only the values `1` (on
`O`), `0` (on `Z`) and one repeated `x` (elsewhere),

`E[g S] = ∑_{j ≤ r} C(r,j) x^j (1-x)^{r-j} g (a + j)`, `a = #O`, `r = #(s \ O \ Z)`.

This is `S = a + Bin(r, x)`, and it is what makes the extremal shapes of
Corollary 2.1 computable. -/
theorem bernExp_shape_eval {s : Finset ι} {q : ι → 𝕜} {x : 𝕜} {O Z : Finset ι}
    (hOs : O ⊆ s) (hZs : Z ⊆ s \ O) (hO : ∀ i ∈ O, q i = 1) (hZ : ∀ i ∈ Z, q i = 0)
    (hI : ∀ i ∈ ((s \ O) \ Z), q i = x) (g : ℕ → 𝕜) :
    bernExp s q g
      = ∑ j ∈ range (((s \ O) \ Z).card + 1),
          (((s \ O) \ Z).card.choose j : 𝕜) * x ^ j * (1 - x) ^ (((s \ O) \ Z).card - j)
            * g (O.card + j) := by
  classical
  rw [bernExp_drop_ones O s hOs hO g, bernExp_drop_zeros Z (s \ O) hZs hZ _,
    bernExp_congr hI _, bernExp_const]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]

end ShapeEval

/-! ### The lower tail -/

section Tail

variable {ι : Type*} [DecidableEq ι] {𝕜 : Type*} [CommRing 𝕜]

/-- `P[S ≤ k]`, the lower tail of the number of successes, as the expectation of
an indicator. -/
def tailLe (s : Finset ι) (p : ι → 𝕜) (k : ℕ) : 𝕜 :=
  bernExp s p (fun r => if r ≤ k then 1 else 0)

/-- **The comparator is the model at the constant vector**: `P[S ≤ k]` for `#s`
identical trials at success probability `P` is `binTail #s P k`. Stated
for an arbitrary ground set. -/
theorem tailLe_const (s : Finset ι) (k : ℕ) (P : 𝕜) :
    tailLe s (fun _ => P) k = binTail s.card P k := by
  rw [tailLe, bernExp_const, binTail]
  have hzero : ∀ j ∈ range (k + 1), j ∉ (range (s.card + 1)).filter (fun j => j ≤ k) →
      (s.card.choose j : 𝕜) * P ^ j * (1 - P) ^ (s.card - j) = 0 := by
    intro j hj hnot
    rw [Finset.mem_range] at hj
    have hjn : s.card < j := by
      by_contra hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩)
    rw [Nat.choose_eq_zero_of_lt hjn]
    simp
  have hsub : (range (s.card + 1)).filter (fun j => j ≤ k) ⊆ range (k + 1) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub hzero, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ k <;> simp [h]

/-- In the degenerate range `#s ≤ k` the tail is `1`: every success set is small
enough. This is `sum_bernWt`, so it holds for **every** `p` whatsoever. -/
theorem tailLe_eq_one {s : Finset ι} (p : ι → 𝕜) {k : ℕ} (hk : s.card ≤ k) :
    tailLe s p k = 1 := by
  have key : ∀ A ∈ s.powerset,
      bernWt s p A * (if A.card ≤ k then (1 : 𝕜) else 0) = bernWt s p A := by
    intro A hA
    have h : A.card ≤ k := le_trans (Finset.card_le_card (Finset.mem_powerset.mp hA)) hk
    simp [h]
  rw [tailLe, bernExp, Finset.sum_congr rfl key, sum_bernWt]

/-- **Below the ones the tail vanishes.** If fewer than `#O` successes are
allowed and `O` is pinned at `1`, the event `{S ≤ k}` is impossible. -/
lemma tailLe_eq_zero_of_lt {s : Finset ι} {q : ι → 𝕜} {O : Finset ι} {k : ℕ}
    (hOs : O ⊆ s) (hO : ∀ i ∈ O, q i = 1) (hk : k < O.card) : tailLe s q k = 0 := by
  rw [tailLe, bernExp_drop_ones O s hOs hO]
  have hz : (fun r : ℕ => (if r + O.card ≤ k then (1 : 𝕜) else 0)) = fun _ => (0 : 𝕜) := by
    funext r
    rw [if_neg (by omega)]
  rw [hz, bernExp_zero_fun]

end Tail

section TailShape

variable {ι : Type*} [DecidableEq ι]

/-- **The lower tail at a three-valued point is a shifted binomial tail.** -/
theorem tailLe_shape_eval {s : Finset ι} {q : ι → ℝ} {x : ℝ} {O Z : Finset ι} {k : ℕ}
    (hOs : O ⊆ s) (hZs : Z ⊆ s \ O) (hO : ∀ i ∈ O, q i = 1) (hZ : ∀ i ∈ Z, q i = 0)
    (hI : ∀ i ∈ ((s \ O) \ Z), q i = x) (hk : O.card ≤ k) :
    tailLe s q k = binTail ((s \ O) \ Z).card x (k - O.card) := by
  classical
  set I := (s \ O) \ Z with hIdef
  set c : ℕ → ℝ := fun j => (I.card.choose j : ℝ) * x ^ j * (1 - x) ^ (I.card - j) with hc
  have hval : tailLe s q k
      = ∑ j ∈ range (I.card + 1), c j * (if O.card + j ≤ k then (1 : ℝ) else 0) := by
    rw [tailLe, bernExp_shape_eval hOs hZs hO hZ hI]
  rw [hval, binTail]
  have hfil : ∑ j ∈ range (I.card + 1), c j * (if O.card + j ≤ k then (1 : ℝ) else 0)
      = ∑ j ∈ (range (I.card + 1)).filter (fun j => O.card + j ≤ k), c j := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  rw [hfil]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_range]
    omega
  · intro j hj hj'
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    have hjI : I.card < j := by omega
    simp only [hc, Nat.choose_eq_zero_of_lt hjI, Nat.cast_zero, zero_mul]

end TailShape

end MiscMath.Probability
