/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/

import MiscMath.Probability.PoissonTrialsFixedMean.ConvexExtremum
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Hoeffding's Corollary 2.1

Part of `MiscMath.Probability.PoissonTrialsFixedMean`, whose module docstring states the
result, its source and its scope, and where the reader should start. This file proves it:
the extrema of `E[g S]` over the fixed-mean box are attained where the coordinates take at
most one interior *value*.
-/

namespace MiscMath.Probability

open Finset

/-! ## Corollary 2.1: the extremal shapes at a fixed mean

Over the fixed-mean box

    InBox s lam p  ↔  (∀ i ∈ s, 0 ≤ p i ≤ 1)  ∧  ∑_{i ∈ s} p i = lam,

the extrema of `p ↦ bernExp s p g` — for an **arbitrary** `g`, with no convexity — are
attained at points whose coordinates take at most the three values `{0, x, 1}`: at most one
*value* is interior.

"At most one interior **value**" is not "at most one interior **coordinate**". The interior
value may be repeated, and the second reading — which says `p` is a *vertex* of the box — is
**false**: `bernExp` is multi-affine, not convex, so its maximum over a polytope need not sit
at a vertex. Both a general refutation and a concrete rational one are below
(`vertex_reduction_fails_of_strictConvex`, `vertex_reduction_false`), and at the refuting
witness the *correct* form does hold (`exHalf_atMostOneInteriorValue`).

The proof is a **terminating spread reduction**, not a compactness argument.
`exists_spread_move`: for an interior pair at fixed sum `σ`, the *spread* endpoint (`0` and
`σ` when `σ ≤ 1`; `1` and `σ - 1` when `σ ≥ 1`) stays in the box, strictly **decreases** the
pair product, and strictly decreases the number of interior coordinates.
`exists_spread_reduction`: so from any `p` in the box, at most `#s` spread moves reach a `q`
with `bernExp p ≤ bernExp q` at which every interior pair has `0 < pairFactor`.
`eq_of_pairFactor_pos_of_isMaxOn`: at a maximiser a pair with `0 < pairFactor` must already
be equal, since the *equalising* move raises the pair product by `((p i - p j)/2)²`.
Compactness enters in exactly one place, and only over `ℝ`: the *existence* of a maximiser
(`exists_isMaxOn_bernExp`). Everything before that is field-generic and finite. -/

section Box

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜]

/-- The fixed-mean box `{p | 0 ≤ p ≤ 1 on s, ∑_{s} p = lam}`. -/
def InBox (s : Finset ι) (lam : 𝕜) (p : ι → 𝕜) : Prop :=
  (∀ i ∈ s, 0 ≤ p i) ∧ (∀ i ∈ s, p i ≤ 1) ∧ ∑ i ∈ s, p i = lam

/-- The coordinates of `p` strictly inside `(0,1)`. Inside the box this is
exactly "not in `{0,1}`". -/
def interiorCoords (s : Finset ι) (p : ι → 𝕜) : Finset ι :=
  s.filter (fun i => 0 < p i ∧ p i < 1)

omit [DecidableEq ι] in
lemma interiorCoords_subset {s : Finset ι} {p : ι → 𝕜} {i : ι}
    (h : i ∈ interiorCoords s p) : i ∈ s := (Finset.mem_filter.mp h).1

omit [DecidableEq ι] in
lemma mem_interiorCoords {s : Finset ι} {p : ι → 𝕜} {i : ι} :
    i ∈ interiorCoords s p ↔ i ∈ s ∧ 0 < p i ∧ p i < 1 := Finset.mem_filter

/-- **Hoeffding's shape**: at most one interior *value*, so the coordinates take
at most the three values `{0, x, 1}` — the interior value may be repeated. -/
def AtMostOneInteriorValue (s : Finset ι) (p : ι → 𝕜) : Prop :=
  ∀ i ∈ interiorCoords s p, ∀ j ∈ interiorCoords s p, p i = p j

/-- At most one interior *coordinate* — equivalently, `p` is a vertex of the box.
This is the reading that `vertex_reduction_false` refutes. -/
def AtMostOneInteriorCoord (s : Finset ι) (p : ι → 𝕜) : Prop :=
  (interiorCoords s p).card ≤ 1

end Box

section Move

variable {ι : Type*} [DecidableEq ι] {𝕜 : Type*} [CommRing 𝕜]

/-- The factor `∑_{B ⊆ s \ {i,j}} bernWt B · Δ²g(#B)` of the master identity.
It never reads `p i` or `p j`. -/
def pairFactor (s : Finset ι) (p : ι → 𝕜) (g : ℕ → 𝕜) (i j : ι) : 𝕜 :=
  ∑ B ∈ (s \ ({i, j} : Finset ι)).powerset,
    bernWt (s \ ({i, j} : Finset ι)) p B * secondDiff g B.card

/-- **The master identity, on a ground set.** Along a sum-preserving move of the
pair `(i,j)`, `bernExp` changes by the change in the pair *product* times
`pairFactor`. No sign hypothesis and no convexity. -/
theorem bernExp_pair_move {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    {p q : ι → 𝕜} (g : ℕ → 𝕜)
    (hout : ∀ k ∈ s, k ≠ i → k ≠ j → q k = p k) (hsum : q i + q j = p i + p j) :
    bernExp s q g - bernExp s p g = (q i * q j - p i * p j) * pairFactor s p g i j := by
  obtain ⟨hjR, hiR, hs⟩ := pair_decomp hi hj hij
  have hout' : ∀ k ∈ s \ ({i, j} : Finset ι), q k = p k := by
    intro k hk
    rw [Finset.mem_sdiff] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact hout k hk.1 hk.2.1 hk.2.2
  have key := bernExp_pair_sub hjR hiR p q g hout' hsum
  rw [hs] at key
  exact key

section Update

variable {β : Type*}

lemma update_pair_left {p : ι → β} {i j : ι} (hij : i ≠ j) (a b : β) :
    (Function.update (Function.update p i a) j b) i = a := by
  rw [Function.update_of_ne hij, Function.update_self]

lemma update_pair_right {p : ι → β} {i j : ι} (a b : β) :
    (Function.update (Function.update p i a) j b) j = b := Function.update_self _ _ _

lemma update_pair_other {p : ι → β} {i j : ι} (a b : β) {k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    (Function.update (Function.update p i a) j b) k = p k := by
  rw [Function.update_of_ne hkj, Function.update_of_ne hki]

end Update

omit [DecidableEq ι] in
/-- A sum-preserving pair move preserves the total sum over `s`. -/
lemma sum_eq_of_pair_move {s : Finset ι} {i j : ι} (his : i ∈ s) (hjs : j ∈ s) (hij : i ≠ j)
    {p q : ι → 𝕜} (hout : ∀ k ∈ s, k ≠ i → k ≠ j → q k = p k)
    (hsum : q i + q j = p i + p j) : ∑ k ∈ s, q k = ∑ k ∈ s, p k := by
  classical
  have hsub : ({i, j} : Finset ι) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact his
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hjs
  have hzero : ∀ x ∈ s, x ∉ ({i, j} : Finset ι) → q x - p x = 0 := by
    intro x hxs hxn
    have h1 : x ≠ i := by rintro rfl; exact hxn (Finset.mem_insert_self _ _)
    have h2 : x ≠ j := by rintro rfl; exact hxn (by simp)
    rw [hout x hxs h1 h2]; ring
  have key : ∑ k ∈ ({i, j} : Finset ι), (q k - p k) = ∑ k ∈ s, (q k - p k) :=
    Finset.sum_subset hsub hzero
  rw [Finset.sum_pair hij, Finset.sum_sub_distrib] at key
  linear_combination hsum - key

end Move

section Extremal

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq ι] [IsStrictOrderedRing 𝕜] in
/-- The interior count strictly drops when one member of an interior pair is
pushed out of `(0,1)` and nothing outside the pair moves. -/
lemma interiorCoords_card_lt {s : Finset ι} {p q : ι → 𝕜} {i j : ι}
    (hi : i ∈ interiorCoords s p) (hj : j ∈ interiorCoords s p)
    (hqi : ¬ (0 < q i ∧ q i < 1))
    (hout : ∀ k ∈ s, k ≠ i → k ≠ j → q k = p k) :
    (interiorCoords s q).card < (interiorCoords s p).card := by
  have hsub : interiorCoords s q ⊆ interiorCoords s p := by
    intro k hk
    rw [mem_interiorCoords] at hk ⊢
    obtain ⟨hks, hkq⟩ := hk
    by_cases hki : k = i
    · exact absurd (hki ▸ hkq) hqi
    by_cases hkj : k = j
    · subst hkj; exact mem_interiorCoords.mp hj
    · rw [hout k hks hki hkj] at hkq; exact ⟨hks, hkq⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨i, hi, ?_⟩)
  intro hmem
  exact hqi (mem_interiorCoords.mp hmem).2

omit [DecidableEq ι] in
/-- **The spread move.** For an interior pair at fixed sum `σ`, send one
coordinate to `0` (when `σ ≤ 1`) or to `1` (when `σ ≥ 1`) and give the partner
the slack. The move stays in the box, strictly **decreases** the pair product,
and strictly decreases the number of interior coordinates — so it terminates in
at most `#s` steps. -/
lemma exists_spread_move {s : Finset ι} {lam : 𝕜} {p : ι → 𝕜} (hp : InBox s lam p)
    {i j : ι} (hi : i ∈ interiorCoords s p) (hj : j ∈ interiorCoords s p) (hij : i ≠ j) :
    ∃ q : ι → 𝕜, InBox s lam q ∧ (∀ k ∈ s, k ≠ i → k ≠ j → q k = p k)
      ∧ q i + q j = p i + p j ∧ q i * q j < p i * p j
      ∧ (interiorCoords s q).card < (interiorCoords s p).card := by
  classical
  obtain ⟨hp0, hp1, hpsum⟩ := hp
  obtain ⟨his, hpi0, hpi1⟩ := mem_interiorCoords.mp hi
  obtain ⟨hjs, hpj0, hpj1⟩ := mem_interiorCoords.mp hj
  rcases le_total (p i + p j) 1 with hσ | hσ
  · refine ⟨Function.update (Function.update p i 0) j (p i + p j), ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro k hk
        by_cases hki : k = i
        · subst hki; rw [update_pair_left hij]
        by_cases hkj : k = j
        · subst hkj; rw [update_pair_right]; linarith
        · rw [update_pair_other _ _ hki hkj]; exact hp0 k hk
      · intro k hk
        by_cases hki : k = i
        · subst hki; rw [update_pair_left hij]; exact zero_le_one
        by_cases hkj : k = j
        · subst hkj; rw [update_pair_right]; exact hσ
        · rw [update_pair_other _ _ hki hkj]; exact hp1 k hk
      · rw [sum_eq_of_pair_move his hjs hij
            (fun k _ hki hkj => update_pair_other _ _ hki hkj) ?_, hpsum]
        rw [update_pair_left hij, update_pair_right]; ring
    · exact fun k _ hki hkj => update_pair_other _ _ hki hkj
    · rw [update_pair_left hij, update_pair_right]; ring
    · rw [update_pair_left hij, update_pair_right, zero_mul]
      exact mul_pos hpi0 hpj0
    · refine interiorCoords_card_lt hi hj ?_ (fun k _ hki hkj => update_pair_other _ _ hki hkj)
      rw [update_pair_left hij]
      exact fun h => absurd h.1 (lt_irrefl 0)
  · refine ⟨Function.update (Function.update p i 1) j (p i + p j - 1), ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro k hk
        by_cases hki : k = i
        · subst hki; rw [update_pair_left hij]; exact zero_le_one
        by_cases hkj : k = j
        · subst hkj; rw [update_pair_right]; linarith
        · rw [update_pair_other _ _ hki hkj]; exact hp0 k hk
      · intro k hk
        by_cases hki : k = i
        · subst hki; rw [update_pair_left hij]
        by_cases hkj : k = j
        · subst hkj; rw [update_pair_right]; linarith
        · rw [update_pair_other _ _ hki hkj]; exact hp1 k hk
      · rw [sum_eq_of_pair_move his hjs hij
            (fun k _ hki hkj => update_pair_other _ _ hki hkj) ?_, hpsum]
        rw [update_pair_left hij, update_pair_right]; ring
    · exact fun k _ hki hkj => update_pair_other _ _ hki hkj
    · rw [update_pair_left hij, update_pair_right]; ring
    · rw [update_pair_left hij, update_pair_right, one_mul]
      nlinarith [mul_pos (sub_pos.mpr hpi1) (sub_pos.mpr hpj1)]
    · refine interiorCoords_card_lt hi hj ?_ (fun k _ hki hkj => update_pair_other _ _ hki hkj)
      rw [update_pair_left hij]
      exact fun h => absurd h.2 (lt_irrefl 1)

/-- **The spread reduction.** From *any* `p` in the box, finitely many
value-non-decreasing spread moves reach a `q` in the box on which every interior
pair has a **strictly positive** `pairFactor`. The induction is on the interior
count, so it terminates in at most `#s` steps: no compactness, no topology. -/
theorem exists_spread_reduction {s : Finset ι} {lam : 𝕜} {g : ℕ → 𝕜} {p : ι → 𝕜}
    (hp : InBox s lam p) :
    ∃ q : ι → 𝕜, InBox s lam q ∧ bernExp s p g ≤ bernExp s q g
      ∧ ∀ i ∈ interiorCoords s q, ∀ j ∈ interiorCoords s q, i ≠ j →
          0 < pairFactor s q g i j := by
  classical
  suffices H : ∀ d : ℕ, ∀ p : ι → 𝕜, (interiorCoords s p).card ≤ d → InBox s lam p →
      ∃ q : ι → 𝕜, InBox s lam q ∧ bernExp s p g ≤ bernExp s q g
        ∧ ∀ i ∈ interiorCoords s q, ∀ j ∈ interiorCoords s q, i ≠ j →
            0 < pairFactor s q g i j from
    H _ p le_rfl hp
  intro d
  induction d with
  | zero =>
    intro p hcard hp
    refine ⟨p, hp, le_rfl, fun i hi j _ _ => ?_⟩
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at hi
    exact absurd hi (Finset.notMem_empty i)
  | succ d ih =>
    intro p hcard hp
    by_cases hbad : ∃ i ∈ interiorCoords s p, ∃ j ∈ interiorCoords s p,
        i ≠ j ∧ pairFactor s p g i j ≤ 0
    · obtain ⟨i, hi, j, hj, hij, hF⟩ := hbad
      obtain ⟨q, hq, hout, hsum, hprod, hdrop⟩ := exists_spread_move hp hi hj hij
      have key := bernExp_pair_move (interiorCoords_subset hi) (interiorCoords_subset hj)
        hij g hout hsum
      have hAF : 0 ≤ (-(q i * q j - p i * p j)) * (-(pairFactor s p g i j)) :=
        mul_nonneg (by linarith) (by linarith)
      have hstep : bernExp s p g ≤ bernExp s q g := by nlinarith [key, hAF]
      obtain ⟨r, hr, hrle, hrcond⟩ := ih q (by omega) hq
      exact ⟨r, hr, hstep.trans hrle, hrcond⟩
    · push Not at hbad
      exact ⟨p, hp, le_rfl, hbad⟩

/-- **The pair criterion.** At a maximiser, a pair with `0 < pairFactor` must
already be *equal*: otherwise the equalising move — which raises the pair product
by `((p i - p j)/2)²` — strictly increases `bernExp`. Note the hypotheses: `i` and `j`
need only be distinct members of `s`; interiority is not used. -/
theorem eq_of_pairFactor_pos_of_isMaxOn {s : Finset ι} {lam : 𝕜} {g : ℕ → 𝕜} {p : ι → 𝕜}
    (hp : InBox s lam p) (hmax : ∀ r : ι → 𝕜, InBox s lam r → bernExp s r g ≤ bernExp s p g)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hF : 0 < pairFactor s p g i j) : p i = p j := by
  by_contra hne
  obtain ⟨hp0, hp1, hpsum⟩ := hp
  have hpi0 := hp0 i hi; have hpi1 := hp1 i hi
  have hpj0 := hp0 j hj; have hpj1 := hp1 j hj
  set m : 𝕜 := (p i + p j) / 2 with hm
  set q : ι → 𝕜 := Function.update (Function.update p i m) j m with hq
  have hqi : q i = m := update_pair_left hij m m
  have hqj : q j = m := update_pair_right m m
  have hqout : ∀ k ∈ s, k ≠ i → k ≠ j → q k = p k :=
    fun k _ hki hkj => update_pair_other _ _ hki hkj
  have hqsum : q i + q j = p i + p j := by rw [hqi, hqj, hm]; ring
  have hqbox : InBox s lam q := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      by_cases hki : k = i
      · subst hki; rw [hqi, hm]; linarith
      by_cases hkj : k = j
      · subst hkj; rw [hqj, hm]; linarith
      · rw [hqout k hk hki hkj]; exact hp0 k hk
    · intro k hk
      by_cases hki : k = i
      · subst hki; rw [hqi, hm]; linarith
      by_cases hkj : k = j
      · subst hkj; rw [hqj, hm]; linarith
      · rw [hqout k hk hki hkj]; exact hp1 k hk
    · rw [sum_eq_of_pair_move hi hj hij hqout hqsum, hpsum]
  have key := bernExp_pair_move hi hj hij g hqout hqsum
  have hprod : 0 < q i * q j - p i * p j := by
    rw [hqi, hqj, hm]
    have hd : p i - p j ≠ 0 := sub_ne_zero.mpr hne
    have h4 : 0 < (p i - p j) ^ 2 := by positivity
    nlinarith
  have hgt : bernExp s p g < bernExp s q g := by nlinarith [key, mul_pos hprod hF]
  exact absurd (hmax q hqbox) (not_le.mpr hgt)

/-- **Corollary 2.1, in reduction form.** Every maximiser of `bernExp` over the
fixed-mean box can be moved — *without changing the value*, so the image is again
a maximiser — to one whose coordinates take at most the three values `{0, x, 1}`.
Compactness enters only through the hypothesis `hmax` (that a maximiser exists at
all); the reduction itself is finite and constructive. -/
theorem exists_max_atMostOneInteriorValue {s : Finset ι} {lam : 𝕜} {g : ℕ → 𝕜} {p : ι → 𝕜}
    (hp : InBox s lam p) (hmax : ∀ r : ι → 𝕜, InBox s lam r → bernExp s r g ≤ bernExp s p g) :
    ∃ q : ι → 𝕜, InBox s lam q ∧ bernExp s q g = bernExp s p g
      ∧ AtMostOneInteriorValue s q := by
  obtain ⟨q, hq, hle, hcond⟩ := exists_spread_reduction (g := g) hp
  have heq : bernExp s q g = bernExp s p g := le_antisymm (hmax q hq) hle
  refine ⟨q, hq, heq, fun i hi j hj => ?_⟩
  by_cases hij : i = j
  · rw [hij]
  · have hqmax : ∀ r : ι → 𝕜, InBox s lam r → bernExp s r g ≤ bernExp s q g := by
      intro r hr; rw [heq]; exact hmax r hr
    exact eq_of_pairFactor_pos_of_isMaxOn hq hqmax (interiorCoords_subset hi)
      (interiorCoords_subset hj) hij (hcond i hi j hj hij)

/-- The minimum direction, by negating `g`, so nothing new is assumed. -/
theorem exists_min_atMostOneInteriorValue {s : Finset ι} {lam : 𝕜} {g : ℕ → 𝕜} {p : ι → 𝕜}
    (hp : InBox s lam p) (hmin : ∀ r : ι → 𝕜, InBox s lam r → bernExp s p g ≤ bernExp s r g) :
    ∃ q : ι → 𝕜, InBox s lam q ∧ bernExp s q g = bernExp s p g
      ∧ AtMostOneInteriorValue s q := by
  have hmax : ∀ r : ι → 𝕜, InBox s lam r →
      bernExp s r (fun k => -g k) ≤ bernExp s p (fun k => -g k) := by
    intro r hr
    rw [bernExp_neg, bernExp_neg]
    exact neg_le_neg (hmin r hr)
  obtain ⟨q, hq, heq, hshape⟩ := exists_max_atMostOneInteriorValue (g := fun k => -g k) hp hmax
  refine ⟨q, hq, ?_, hshape⟩
  rw [bernExp_neg, bernExp_neg] at heq
  linarith

/-- **The vertex reading fails in general, not just at one witness.** For `g`
strictly grid-convex, Theorem 3 says the *unique* maximiser over the fixed-mean
box is the constant vector `p ≡ μ`; when `0 < μ < 1` every one of its `#s`
coordinates is interior, so for `#s ≥ 2` no vertex can dominate it. -/
theorem vertex_reduction_fails_of_strictConvex {s : Finset ι} {g : ℕ → 𝕜} {μ : 𝕜}
    (hg : ∀ k, k + 2 ≤ s.card → 0 < secondDiff g k) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hs : 2 ≤ s.card) {q : ι → 𝕜} (hq : InBox s (s.card * μ) q)
    (hvertex : AtMostOneInteriorCoord s q) :
    bernExp s q g < bernExp s (fun _ => μ) g := by
  obtain ⟨h0, h1, hsum⟩ := hq
  refine bernExp_lt_const h0 h1 hsum hg ?_
  by_contra hcon
  push Not at hcon
  have hall : interiorCoords s q = s := by
    refine Finset.filter_true_of_mem fun k hk => ?_
    rw [hcon k hk]
    exact ⟨hμ0, hμ1⟩
  rw [AtMostOneInteriorCoord, hall] at hvertex
  omega

end Extremal

/-! ### Existence of the extremum over `ℝ` — the compactness input, discharged -/

section Existence

variable {ι : Type*} [DecidableEq ι]

/-- The **supported** box: coordinates off `s` are pinned at `0`. The box
`{p | InBox s lam p}` itself is closed but *not* bounded — coordinates off `s`
are unconstrained — so the compactness argument runs here instead, and
`bernExp_congr` says `bernExp` cannot tell the difference. -/
def suppBox (s : Finset ι) : Set (ι → ℝ) :=
  Set.univ.pi (fun i => if i ∈ s then Set.Icc (0 : ℝ) 1 else {(0 : ℝ)})

/-- Tychonoff: the supported box is compact. **No `Fintype ι` is needed.** -/
theorem isCompact_suppBox (s : Finset ι) : IsCompact (suppBox s) := by
  refine isCompact_univ_pi fun i => ?_
  by_cases h : i ∈ s <;> simp [h, isCompact_Icc]

/-- `bernExp` is continuous in `p` over `ℝ`. -/
theorem continuous_bernExp (s : Finset ι) (g : ℕ → ℝ) :
    Continuous (fun p : ι → ℝ => bernExp s p g) := by
  unfold bernExp bernWt
  fun_prop

omit [DecidableEq ι] in
/-- The mean slice is closed. -/
theorem isClosed_meanSlice (s : Finset ι) (lam : ℝ) :
    IsClosed {p : ι → ℝ | ∑ i ∈ s, p i = lam} :=
  isClosed_eq (by fun_prop) continuous_const

/-- The truncation of `p` to `s`. -/
def trunc (s : Finset ι) (p : ι → ℝ) : ι → ℝ := fun i => if i ∈ s then p i else 0

lemma trunc_agrees (s : Finset ι) (p : ι → ℝ) : ∀ i ∈ s, p i = trunc s p i := by
  intro i hi; simp [trunc, hi]

lemma bernExp_trunc (s : Finset ι) (p : ι → ℝ) (g : ℕ → ℝ) :
    bernExp s (trunc s p) g = bernExp s p g :=
  bernExp_congr (fun i hi => (trunc_agrees s p i hi).symm) g

lemma trunc_mem_suppBox {s : Finset ι} {lam : ℝ} {p : ι → ℝ} (hp : InBox s lam p) :
    trunc s p ∈ suppBox s ∩ {q : ι → ℝ | ∑ i ∈ s, q i = lam} := by
  obtain ⟨h0, h1, hsum⟩ := hp
  constructor
  · intro i _
    by_cases h : i ∈ s
    · simp only [trunc, h, if_true]
      exact ⟨h0 i h, h1 i h⟩
    · simp [trunc, h]
  · change ∑ i ∈ s, trunc s p i = lam
    rw [← hsum]
    exact Finset.sum_congr rfl fun i hi => by simp [trunc, hi]

lemma inBox_of_mem_suppBox {s : Finset ι} {lam : ℝ} {q : ι → ℝ}
    (hq : q ∈ suppBox s ∩ {r : ι → ℝ | ∑ i ∈ s, r i = lam}) : InBox s lam q := by
  obtain ⟨hb, hs⟩ := hq
  refine ⟨fun i hi => ?_, fun i hi => ?_, hs⟩
  · have := hb i (Set.mem_univ i); simp only [if_pos hi] at this; exact this.1
  · have := hb i (Set.mem_univ i); simp only [if_pos hi] at this; exact this.2

/-- **Existence of a maximiser over `ℝ`**, as soon as the box is nonempty. Only
the *supported* box is compact, which is why `bernExp_congr` is needed. -/
theorem exists_isMaxOn_bernExp {s : Finset ι} {lam : ℝ} (g : ℕ → ℝ) {p₀ : ι → ℝ}
    (hp₀ : InBox s lam p₀) :
    ∃ q : ι → ℝ, InBox s lam q ∧ ∀ r : ι → ℝ, InBox s lam r → bernExp s r g ≤ bernExp s q g := by
  set K : Set (ι → ℝ) := suppBox s ∩ {q : ι → ℝ | ∑ i ∈ s, q i = lam} with hK
  have hcomp : IsCompact K := (isCompact_suppBox s).inter_right (isClosed_meanSlice s lam)
  have hne : K.Nonempty := ⟨trunc s p₀, trunc_mem_suppBox hp₀⟩
  obtain ⟨q, hqK, hqmax⟩ := hcomp.exists_isMaxOn hne
    (Continuous.continuousOn (continuous_bernExp s g))
  refine ⟨q, inBox_of_mem_suppBox hqK, fun r hr => ?_⟩
  have hr' : trunc s r ∈ K := trunc_mem_suppBox hr
  have hle : bernExp s (trunc s r) g ≤ bernExp s q g := hqmax hr'
  rwa [bernExp_trunc] at hle

/-- Existence of a minimiser, by negating `g`. -/
theorem exists_isMinOn_bernExp {s : Finset ι} {lam : ℝ} (g : ℕ → ℝ) {p₀ : ι → ℝ}
    (hp₀ : InBox s lam p₀) :
    ∃ q : ι → ℝ, InBox s lam q ∧ ∀ r : ι → ℝ, InBox s lam r → bernExp s q g ≤ bernExp s r g := by
  obtain ⟨q, hq, hmax⟩ := exists_isMaxOn_bernExp (fun k => -g k) hp₀
  refine ⟨q, hq, fun r hr => ?_⟩
  have := hmax r hr
  rw [bernExp_neg, bernExp_neg] at this
  linarith

/-- **Hoeffding (1956), Corollary 2.1, over `ℝ` with no hypotheses at all** beyond
membership in the fixed-mean box: the maximum of `bernExp s · g` is attained at a
point whose coordinates take at most the three values `{0, x, 1}`.
`g` is arbitrary — no convexity, no monotonicity. -/
theorem hoeffding_cor21 {s : Finset ι} {lam : ℝ} (g : ℕ → ℝ) {p : ι → ℝ}
    (hp : InBox s lam p) :
    ∃ q : ι → ℝ, InBox s lam q ∧ AtMostOneInteriorValue s q
      ∧ ∀ r : ι → ℝ, InBox s lam r → bernExp s r g ≤ bernExp s q g := by
  obtain ⟨q₀, hq₀, hmax⟩ := exists_isMaxOn_bernExp g hp
  obtain ⟨q, hq, hval, hshape⟩ := exists_max_atMostOneInteriorValue hq₀ hmax
  exact ⟨q, hq, hshape, fun r hr => by rw [hval]; exact hmax r hr⟩

/-- The minimum direction of the same. -/
theorem hoeffding_cor21_min {s : Finset ι} {lam : ℝ} (g : ℕ → ℝ) {p : ι → ℝ}
    (hp : InBox s lam p) :
    ∃ q : ι → ℝ, InBox s lam q ∧ AtMostOneInteriorValue s q
      ∧ ∀ r : ι → ℝ, InBox s lam r → bernExp s q g ≤ bernExp s r g := by
  obtain ⟨q₀, hq₀, hmin⟩ := exists_isMinOn_bernExp g hp
  obtain ⟨q, hq, hval, hshape⟩ := exists_min_atMostOneInteriorValue hq₀ hmin
  exact ⟨q, hq, hshape, fun r hr => by rw [hval]; exact hmin r hr⟩

end Existence

/-! ### The shape data

At a point with at most one interior value the coordinates take only `0`, `1` and one
repeated value `x`. Counting them gives `(a, b, r)` and the mean equation `a + r·x = lam`,
so the extremal candidates are indexed by the pair `(a, b)` alone — at most `(#s + 1)²` of
them. -/

section Shape

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq ι] [IsStrictOrderedRing 𝕜] in
/-- The three-way partition of the box at a point: ones, zeros, interior. -/
lemma box_trichotomy {s : Finset ι} {lam : 𝕜} {q : ι → 𝕜} (hq : InBox s lam q) {i : ι}
    (hi : i ∈ s) : q i = 1 ∨ q i = 0 ∨ i ∈ interiorCoords s q := by
  obtain ⟨h0, h1, -⟩ := hq
  rcases eq_or_lt_of_le (h0 i hi) with h | hlt0
  · exact Or.inr (Or.inl h.symm)
  rcases eq_or_lt_of_le (h1 i hi) with h | hlt1
  · exact Or.inl h
  · exact Or.inr (Or.inr (mem_interiorCoords.mpr ⟨hi, hlt0, hlt1⟩))

omit [DecidableEq ι] in
/-- **The shape data and the mean equation.** Every point of the box with at
most one interior value is described by `a` coordinates at `1`, `b` at `0`, and
`r = #s - a - b` at a common `x`, with `a + r·x = lam`. -/
theorem shape_of_atMostOneInteriorValue {s : Finset ι} {lam : 𝕜} {q : ι → 𝕜}
    (hq : InBox s lam q) (hshape : AtMostOneInteriorValue s q) :
    ∃ x : 𝕜,
      (∀ i ∈ interiorCoords s q, q i = x)
      ∧ (s.filter (fun i => q i = 1)).card + (s.filter (fun i => q i = 0)).card
          + (interiorCoords s q).card = s.card
      ∧ ((s.filter (fun i => q i = 1)).card : 𝕜)
          + ((interiorCoords s q).card : 𝕜) * x = lam := by
  classical
  obtain ⟨h0, h1, hsum⟩ := hq
  obtain ⟨x, hx⟩ : ∃ x : 𝕜, ∀ i ∈ interiorCoords s q, q i = x := by
    rcases Finset.eq_empty_or_nonempty (interiorCoords s q) with hemp | ⟨i₀, hi₀⟩
    · exact ⟨0, by rw [hemp]; simp⟩
    · exact ⟨q i₀, fun i hi => hshape i hi i₀ hi₀⟩
  have hP0 : (s.filter (fun i => ¬ q i = 1)).filter (fun i => q i = 0)
      = s.filter (fun i => q i = 0) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact zero_ne_one, h⟩
  have hPI : (s.filter (fun i => ¬ q i = 1)).filter (fun i => ¬ q i = 0)
      = interiorCoords s q := by
    rw [Finset.filter_filter, interiorCoords]
    apply Finset.filter_congr
    intro i hi
    constructor
    · rintro ⟨hne1, hne0⟩
      exact ⟨lt_of_le_of_ne (h0 i hi) (Ne.symm hne0), lt_of_le_of_ne (h1 i hi) hne1⟩
    · rintro ⟨hlt0, hlt1⟩
      exact ⟨ne_of_lt hlt1, ne_of_gt hlt0⟩
  refine ⟨x, hx, ?_, ?_⟩
  · have hc1 := Finset.card_filter_add_card_filter_not (s := s) (fun i => q i = 1)
    have hc2 := Finset.card_filter_add_card_filter_not
      (s := s.filter (fun i => ¬ q i = 1)) (fun i => q i = 0)
    rw [hP0, hPI] at hc2
    omega
  · have hs1 := Finset.sum_filter_add_sum_filter_not s (fun i => q i = 1) q
    have hs2 := Finset.sum_filter_add_sum_filter_not
      (s.filter (fun i => ¬ q i = 1)) (fun i => q i = 0) q
    rw [hP0, hPI] at hs2
    have e1 : ∑ i ∈ s.filter (fun i => q i = 1), q i
        = ((s.filter (fun i => q i = 1)).card : 𝕜) := by
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
        nsmul_eq_mul, mul_one]
    have e0 : ∑ i ∈ s.filter (fun i => q i = 0), q i = 0 :=
      Finset.sum_eq_zero fun i hi => (Finset.mem_filter.mp hi).2
    have eI : ∑ i ∈ interiorCoords s q, q i = ((interiorCoords s q).card : 𝕜) * x := by
      rw [Finset.sum_congr rfl hx, Finset.sum_const, nsmul_eq_mul]
    rw [e1] at hs1
    rw [e0, eI] at hs2
    rw [hsum] at hs1
    linarith

end Shape

/-! ### The vertex reading, refuted concretely

The general refutation is `vertex_reduction_fails_of_strictConvex`. The rational instance
below is the same statement made concrete and machine-checked, and it also exhibits the
*correct* form holding at the same point. -/

section VertexRefutation

/-- The reduction with the **vertex** conclusion: every point of the box is
dominated by one with at most one interior *coordinate*. -/
def VertexReduction : Prop :=
  ∀ (s : Finset ℕ) (g : ℕ → ℚ) (lam : ℚ) (p : ℕ → ℚ), InBox s lam p →
    ∃ q : ℕ → ℚ, InBox s lam q ∧ AtMostOneInteriorCoord s q ∧ bernExp s p g ≤ bernExp s q g

/-- The same, for the minimum. -/
def VertexReductionMin : Prop :=
  ∀ (s : Finset ℕ) (g : ℕ → ℚ) (lam : ℚ) (p : ℕ → ℚ), InBox s lam p →
    ∃ q : ℕ → ℚ, InBox s lam q ∧ AtMostOneInteriorCoord s q ∧ bernExp s q g ≤ bernExp s p g

/-- `g = (1,0,1)`: strictly grid-convex, `secondDiff g 0 = 2 > 0`. -/
def gMax : ℕ → ℚ := fun k => if k = 1 then 0 else 1

/-- `g = (0,1,0)` — the witness for the minimum. -/
def gMin : ℕ → ℚ := fun k => if k = 1 then 1 else 0

/-- The witness point `p = (1/2, 1/2)` on `s = {0,1}` with `lam = 1`. -/
def exHalf : ℕ → ℚ := fun _ => 1 / 2

private lemma h01 : (0 : ℕ) ≠ 1 := by norm_num
private lemma hmem0 : (0 : ℕ) ∈ ({0, 1} : Finset ℕ) := by decide
private lemma hmem1 : (1 : ℕ) ∈ ({0, 1} : Finset ℕ) := by decide

lemma exHalf_inBox : InBox ({0, 1} : Finset ℕ) 1 exHalf := by
  refine ⟨fun i _ => by norm_num [exHalf], fun i _ => by norm_num [exHalf], ?_⟩
  rw [Finset.sum_pair h01]
  norm_num [exHalf]

/-- On `s = {0,1}` the value is `g 1 + (pair product)·secondDiff g 0`. -/
lemma bernExp_two (q : ℕ → ℚ) (g : ℕ → ℚ) (hq : q 0 + q 1 = 1) :
    bernExp ({0, 1} : Finset ℕ) q g = g 1 + q 0 * q 1 * (g 0 - 2 * g 1 + g 2) := by
  rw [bernExp_pair h01]
  have h : q 1 = 1 - q 0 := by linarith
  rw [h]; ring

private lemma exHalf_sum : exHalf 0 + exHalf 1 = 1 := by norm_num [exHalf]

private lemma gMax_vals : gMax 0 = 1 ∧ gMax 1 = 0 ∧ gMax 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [gMax]

private lemma gMin_vals : gMin 0 = 0 ∧ gMin 1 = 1 ∧ gMin 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [gMin]

lemma exHalf_value : bernExp ({0, 1} : Finset ℕ) exHalf gMax = 1 / 2 := by
  obtain ⟨g0, g1, g2⟩ := gMax_vals
  rw [bernExp_two _ _ exHalf_sum, g0, g1, g2]
  norm_num [exHalf]

/-- The witness point really is the maximiser: `2τ(1-τ) ≤ 1/2`. -/
theorem exHalf_isMax : ∀ r : ℕ → ℚ, InBox ({0, 1} : Finset ℕ) 1 r →
    bernExp ({0, 1} : Finset ℕ) r gMax ≤ bernExp ({0, 1} : Finset ℕ) exHalf gMax := by
  intro r hr
  obtain ⟨-, -, hsum⟩ := hr
  rw [Finset.sum_pair h01] at hsum
  obtain ⟨g0, g1, g2⟩ := gMax_vals
  have h : r 1 = 1 - r 0 := by linarith
  rw [bernExp_two _ _ hsum, exHalf_value, g0, g1, g2, h]
  nlinarith [sq_nonneg (2 * r 0 - 1)]

/-- On `s = {0,1}` two interior coordinates already break the vertex clause. -/
lemma two_le_interior_card {q : ℕ → ℚ}
    (h0 : (0 : ℕ) ∈ interiorCoords ({0, 1} : Finset ℕ) q)
    (h1 : (1 : ℕ) ∈ interiorCoords ({0, 1} : Finset ℕ) q) :
    2 ≤ (interiorCoords ({0, 1} : Finset ℕ) q).card := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ interiorCoords ({0, 1} : Finset ℕ) q := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h0
    · rw [Finset.mem_singleton] at hx; exact hx ▸ h1
  have hcard := Finset.card_le_card hsub
  rwa [show ({0, 1} : Finset ℕ).card = 2 from by decide] at hcard

/-- … uniquely: `2τ(1-τ) = 1/2` forces `τ = 1/2`. -/
theorem exHalf_unique_max : ∀ r : ℕ → ℚ, InBox ({0, 1} : Finset ℕ) 1 r →
    bernExp ({0, 1} : Finset ℕ) r gMax = 1 / 2 → r 0 = 1 / 2 ∧ r 1 = 1 / 2 := by
  intro r hr hval
  obtain ⟨-, -, hsum⟩ := hr
  rw [Finset.sum_pair h01] at hsum
  obtain ⟨g0, g1, g2⟩ := gMax_vals
  have h : r 1 = 1 - r 0 := by linarith
  rw [bernExp_two _ _ hsum, g0, g1, g2, h] at hval
  have hsq : (2 * r 0 - 1) ^ 2 = 0 := by linear_combination -2 * hval
  have hz : 2 * r 0 - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  exact ⟨by linarith, by linarith⟩

/-- … and it has **two** interior coordinates, so it is not a vertex. -/
theorem exHalf_not_vertex : ¬ AtMostOneInteriorCoord ({0, 1} : Finset ℕ) exHalf := by
  intro hv
  have hi0 : (0 : ℕ) ∈ interiorCoords ({0, 1} : Finset ℕ) exHalf :=
    mem_interiorCoords.mpr ⟨hmem0, by norm_num [exHalf], by norm_num [exHalf]⟩
  have hi1 : (1 : ℕ) ∈ interiorCoords ({0, 1} : Finset ℕ) exHalf :=
    mem_interiorCoords.mpr ⟨hmem1, by norm_num [exHalf], by norm_num [exHalf]⟩
  have := two_le_interior_card hi0 hi1
  rw [AtMostOneInteriorCoord] at hv
  omega

/-- … while **Hoeffding's own shape does hold there**: one interior value at two
coordinates. This is the whole distinction, in one witness. -/
theorem exHalf_atMostOneInteriorValue : AtMostOneInteriorValue ({0, 1} : Finset ℕ) exHalf :=
  fun _ _ _ _ => rfl

/-- On the box `{p | p 0 + p 1 = 1}` a vertex is `(1,0)` or `(0,1)`. -/
lemma vertex_two {q : ℕ → ℚ} (hq : InBox ({0, 1} : Finset ℕ) 1 q)
    (hv : AtMostOneInteriorCoord ({0, 1} : Finset ℕ) q) : q 0 * q 1 = 0 := by
  obtain ⟨h0, h1, hsum⟩ := hq
  rw [Finset.sum_pair h01] at hsum
  have hq00 := h0 0 hmem0
  have hq01 := h1 0 hmem0
  rcases eq_or_lt_of_le hq00 with h | hlt0
  · rw [← h, zero_mul]
  rcases eq_or_lt_of_le hq01 with h | hlt1
  · have hz : q 1 = 0 := by linarith
    rw [hz, mul_zero]
  · exfalso
    have hi0 : (0 : ℕ) ∈ interiorCoords ({0, 1} : Finset ℕ) q :=
      mem_interiorCoords.mpr ⟨hmem0, hlt0, hlt1⟩
    have hi1 : (1 : ℕ) ∈ interiorCoords ({0, 1} : Finset ℕ) q :=
      mem_interiorCoords.mpr ⟨hmem1, by linarith, by linarith⟩
    have := two_le_interior_card hi0 hi1
    rw [AtMostOneInteriorCoord] at hv
    omega

/-- **The vertex reading of Corollary 2.1 is FALSE (maximum direction).** At
`s = {0,1}`, `lam = 1`, `g = (1,0,1)`: the maximum `1/2` is attained only at
`(1/2,1/2)`, while every vertex of the box gives `0`. -/
theorem vertex_reduction_false : ¬ VertexReduction := by
  intro H
  obtain ⟨q, hq, hv, hle⟩ := H ({0, 1} : Finset ℕ) gMax 1 exHalf exHalf_inBox
  have hsum : q 0 + q 1 = 1 := by
    have h := hq.2.2; rwa [Finset.sum_pair h01] at h
  obtain ⟨g0, g1, g2⟩ := gMax_vals
  rw [exHalf_value, bernExp_two _ _ hsum, vertex_two hq hv, g1] at hle
  norm_num at hle

/-- **… and in the minimum direction too**, with `g = (0,1,0)`: the minimum `1/2`
is attained only at `(1/2,1/2)`, every vertex gives `1`. -/
theorem vertex_reduction_min_false : ¬ VertexReductionMin := by
  intro H
  obtain ⟨q, hq, hv, hle⟩ := H ({0, 1} : Finset ℕ) gMin 1 exHalf exHalf_inBox
  have hsum : q 0 + q 1 = 1 := by
    have h := hq.2.2; rwa [Finset.sum_pair h01] at h
  obtain ⟨g0, g1, g2⟩ := gMin_vals
  rw [bernExp_two _ _ exHalf_sum, bernExp_two _ _ hsum, vertex_two hq hv, g0, g1, g2] at hle
  norm_num [exHalf] at hle

end VertexRefutation

end MiscMath.Probability
