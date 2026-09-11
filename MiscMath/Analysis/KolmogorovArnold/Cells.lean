/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# The cell system

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; part of the density argument (Layer 2 of the development). Its
declarations are proof: machine-generated, kernel-checked and axiom-audited, and may be read by
no one.

Hedberg's *red intervals* (Lemma 2, p. 269), in general dimension and on the rescaled line
`u = N t`, so that every endpoint is an integer. There are `m` ranks `q : Fin m` (`m = 2n + 1` in
the application). Deleting from the line the open unit intervals `(q + m j, q + m j + 1)`, `j ∈ ℕ`,
leaves for each rank a sequence of closed **cells** of length `m - 1`,

  `cell q j = [q + m j - (m - 1), q + m j]`,

and the deleted intervals are the **gaps** of rank `q`. Two facts carry the whole argument:

* a point `u` lies in a gap of at most one rank, namely `badRank u = ⌊u⌋ mod m`, so every point
  `u ≥ 0` lies in a cell of every other rank (`badRank_eq_of_inGap`,
  `exists_mem_cell_of_not_inGap`); Hedberg's "except perhaps for one value of `i`", Kahane's
  "sauf au plus une";
* hence a point of the `n`-dimensional cube lies in a product of cells — a *red cube* — of at
  least `m - n` ranks (`le_card_red_add`), which for `m = 2n + 1` is `n + 1`: Hedberg's "at
  least three different ranks" for `n = 2`.

Also here: the index of a cell meeting `[0, N]` is at most `N`, which bounds the finite sums in
the staircase construction, and the diameter bound for a cell.
-/

open Finset

namespace MiscMath.Analysis.KolmogorovArnold

variable {m : ℕ}

/-- The right endpoint `q + m j` of the cell of rank `q` and index `j`. -/
def cellRight (q : Fin m) (j : ℕ) : ℝ := ((q : ℕ) : ℝ) + m * j

/-- The left endpoint `q + m j - (m - 1)` of the cell of rank `q` and index `j`. -/
def cellLeft (q : Fin m) (j : ℕ) : ℝ := ((q : ℕ) : ℝ) + m * j - (m - 1)

/-- The cell of rank `q` and index `j`: the closed interval `[q + m j - (m - 1), q + m j]`. -/
def cell (q : Fin m) (j : ℕ) : Set ℝ := Set.Icc (cellLeft q j) (cellRight q j)

/-- `u` lies in a gap of rank `q`: strictly between the right endpoint of some cell and the left
endpoint of the next. -/
def InGap (q : Fin m) (u : ℝ) : Prop := ∃ j : ℕ, cellRight q j < u ∧ u < cellRight q j + 1

theorem mem_cell {q : Fin m} {j : ℕ} {u : ℝ} :
    u ∈ cell q j ↔ cellLeft q j ≤ u ∧ u ≤ cellRight q j :=
  Iff.rfl

theorem one_le_cast_of_fin (q : Fin m) : (1 : ℝ) ≤ m := by
  exact_mod_cast q.pos

theorem cellLeft_succ (q : Fin m) (j : ℕ) : cellLeft q (j + 1) = cellRight q j + 1 := by
  unfold cellLeft cellRight
  push_cast
  ring

theorem cellLeft_le_cellRight (q : Fin m) (j : ℕ) : cellLeft q j ≤ cellRight q j := by
  unfold cellLeft cellRight
  linarith [one_le_cast_of_fin q]

theorem cellRight_nonneg (q : Fin m) (j : ℕ) : 0 ≤ cellRight q j := by
  unfold cellRight
  positivity

theorem cellRight_mono (q : Fin m) : Monotone (cellRight q) := by
  intro j j' h
  unfold cellRight
  have : (j : ℝ) ≤ j' := by exact_mod_cast h
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Cells of the same rank are separated by gaps of length one. -/
theorem cellRight_add_one_le_cellLeft {q : Fin m} {j j' : ℕ} (h : j' < j) :
    cellRight q j' + 1 ≤ cellLeft q j := by
  unfold cellLeft cellRight
  have h1 : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
  have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) m)
  linarith

theorem cellRight_mem_cell (q : Fin m) (j : ℕ) : cellRight q j ∈ cell q j :=
  ⟨cellLeft_le_cellRight q j, le_rfl⟩

theorem cellRight_add_one_mem_cell (q : Fin m) (j : ℕ) : cellRight q j + 1 ∈ cell q (j + 1) :=
  ⟨(cellLeft_succ q j).le, (cellLeft_succ q j).symm.le.trans (cellLeft_le_cellRight q (j + 1))⟩

/-- Two points of one cell are at distance at most `m - 1`. -/
theorem abs_sub_le_of_mem_cell {q : Fin m} {j : ℕ} {u v : ℝ} (hu : u ∈ cell q j)
    (hv : v ∈ cell q j) : |u - v| ≤ m - 1 := by
  have h1 : cellRight q j - cellLeft q j = m - 1 := by
    unfold cellLeft cellRight
    ring
  rw [abs_sub_le_iff]
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- A cell of index `j` that meets `[0, N]` has `j ≤ N`. -/
theorem le_of_cellLeft_le {q : Fin m} {j N : ℕ} {u : ℝ} (h1 : cellLeft q j ≤ u) (h2 : u ≤ N) :
    j ≤ N := by
  by_contra hlt
  have hlt : N < j := not_le.mp hlt
  have hm1 := one_le_cast_of_fin q
  have hj : (N : ℝ) + 1 ≤ j := by exact_mod_cast hlt
  have h3 : (m : ℝ) * (N + 1) ≤ m * j := mul_le_mul_of_nonneg_left hj (by linarith)
  have h4 : (N : ℝ) ≤ m * N := le_mul_of_one_le_left (Nat.cast_nonneg N) hm1
  have hq : (0 : ℝ) ≤ ((q : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold cellLeft at h1
  nlinarith

/-- The rank a point can be missed by: `⌊u⌋ mod m`. -/
noncomputable def badRank (m : ℕ) [NeZero m] (u : ℝ) : Fin m :=
  ⟨⌊u⌋₊ % m, Nat.mod_lt _ (NeZero.pos m)⟩

/-- A gap of rank `q` forces `⌊u⌋ = q + m j`, so the rank is `⌊u⌋ mod m`: a point lies in a gap
of **at most one** rank. -/
theorem badRank_eq_of_inGap [NeZero m] {q : Fin m} {u : ℝ} (h : InGap q u) : badRank m u = q := by
  obtain ⟨j, h1, h2⟩ := h
  have hk : cellRight q j = (((q : ℕ) + m * j : ℕ) : ℝ) := by
    unfold cellRight
    push_cast
    ring
  have hu : 0 ≤ u := (cellRight_nonneg q j).trans h1.le
  have hfloor : ⌊u⌋₊ = (q : ℕ) + m * j := by
    rw [Nat.floor_eq_iff hu]
    rw [hk] at h1 h2
    exact ⟨h1.le, h2⟩
  apply Fin.ext
  change (⌊u⌋₊ % m) = q
  rw [hfloor, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt q.isLt]

/-- A point `u ≥ 0` not in a gap of rank `q` lies in a cell of rank `q`. -/
theorem exists_mem_cell_of_not_inGap {q : Fin m} {u : ℝ} (hu : 0 ≤ u) (h : ¬ InGap q u) :
    ∃ j : ℕ, u ∈ cell q j := by
  have hm0 : 0 < m := q.pos
  set K : ℕ := ⌊u⌋₊ with hKdef
  have hK1 : (K : ℝ) ≤ u := Nat.floor_le hu
  have hK2 : u < K + 1 := Nat.lt_floor_add_one u
  set d : ℕ := K / m with hd
  set r : ℕ := K % m with hr
  have hKdr : m * d + r = K := Nat.div_add_mod K m
  have hrm : r < m := Nat.mod_lt K hm0
  have hKR : (K : ℝ) = m * d + r := by exact_mod_cast hKdr.symm
  have hrmR : (r : ℝ) + 1 ≤ m := by exact_mod_cast hrm
  have hqmR : ((q : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast q.isLt
  have hright : ∀ j : ℕ, cellRight q j = ((q : ℕ) : ℝ) + m * j := fun j => rfl
  have hleft : ∀ j : ℕ, cellLeft q j = ((q : ℕ) : ℝ) + m * j - (m - 1) := fun j => rfl
  rcases lt_trichotomy r (q : ℕ) with hlt | heq | hgt
  · -- `r < q`: the cell of index `d` ends at `q + m d ∈ [K + 1, K + m - 1]`.
    have hltR : (r : ℝ) + 1 ≤ (q : ℕ) := by exact_mod_cast hlt
    refine ⟨d, ?_, ?_⟩
    · rw [hleft]; linarith
    · rw [hright]; linarith
  · -- `r = q`: then `q + m d = K`; `u = K` is the right endpoint of the cell of index `d`, and
    -- `K < u < K + 1` would put `u` in a gap.
    have heqR : ((q : ℕ) : ℝ) = r := by exact_mod_cast heq.symm
    have hKq : cellRight q d = K := by rw [hright, hKR, heqR]; ring
    refine ⟨d, ?_, ?_⟩
    · rw [hleft]; linarith
    · rw [hKq]
      by_contra hlt
      have hlt : (K : ℝ) < u := not_le.mp hlt
      exact h ⟨d, by rw [hKq]; exact hlt, by rw [hKq]; exact hK2⟩
  · -- `q < r`: the cell of index `d + 1` ends at `q + m d + m ∈ [K + 1, K + m - 1]`.
    have hgtR : ((q : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast hgt
    have hright' : cellRight q (d + 1) = ((q : ℕ) : ℝ) + m * d + m := by
      rw [hright]; push_cast; ring
    have hleft' : cellLeft q (d + 1) = ((q : ℕ) : ℝ) + m * d + m - (m - 1) := by
      rw [hleft]; push_cast; ring
    refine ⟨d + 1, ?_, ?_⟩
    · rw [hleft']; linarith
    · rw [hright']; linarith

/-! ### Red cubes -/

variable {n : ℕ}

/-- A point `u` of the rescaled cube is **red** for rank `q` if each coordinate lies in a cell of
rank `q`, i.e. `u` lies in a product of cells of rank `q`. -/
def IsRed (q : Fin m) (u : Fin n → ℝ) : Prop := ∃ jv : Fin n → ℕ, ∀ p, u p ∈ cell q (jv p)

/-- A rank for which `u` is not red misses some coordinate, and so is that coordinate's bad rank. -/
theorem exists_badRank_eq_of_not_isRed [NeZero m] {q : Fin m} {u : Fin n → ℝ} (hu : ∀ p, 0 ≤ u p)
    (h : ¬ IsRed q u) : ∃ p, badRank m (u p) = q := by
  by_contra hcon
  apply h
  have : ∀ p, ∃ j, u p ∈ cell q j := fun p =>
    exists_mem_cell_of_not_inGap (hu p) fun hg => (not_exists.mp hcon p) (badRank_eq_of_inGap hg)
  exact Classical.skolem.mp this

/-- **Covering multiplicity.** A point of the `n`-cube with non-negative coordinates is red for at
least `m - n` ranks: there is a set `S` of ranks, all red for `u`, with `m ≤ #S + n`. For
`m = 2n + 1` this is `n + 1` ranks. -/
theorem exists_red_finset [NeZero m] {u : Fin n → ℝ} (hu : ∀ p, 0 ≤ u p) :
    ∃ S : Finset (Fin m), (∀ q ∈ S, IsRed q u) ∧ m ≤ S.card + n := by
  classical
  refine ⟨univ.filter fun q : Fin m => IsRed q u, fun q hq => (mem_filter.mp hq).2, ?_⟩
  have hsplit :=
    card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun q => IsRed q u)
  rw [card_univ, Fintype.card_fin] at hsplit
  have hsub : (univ.filter fun q : Fin m => ¬ IsRed q u) ⊆
      univ.image fun p => badRank m (u p) := by
    intro q hq
    rw [mem_filter] at hq
    obtain ⟨p, hp⟩ := exists_badRank_eq_of_not_isRed hu hq.2
    exact mem_image.mpr ⟨p, mem_univ p, hp⟩
  have hcard : (univ.filter fun q : Fin m => ¬ IsRed q u).card ≤ n :=
    (card_le_card hsub).trans (card_image_le.trans (by simp))
  omega

/-! ## Sanity checks -/

/-- With `m = 3` (so `n = 1`), the cells of rank `1` have length `2` and are
`[-1, 1], [2, 4], [5, 7], …`; the gaps between them are `(1, 2), (4, 5), …`. -/
example : cell (1 : Fin 3) 0 = Set.Icc (-1) 1 := by
  unfold cell cellLeft cellRight
  norm_num

example : cell (1 : Fin 3) 1 = Set.Icc 2 4 := by
  unfold cell cellLeft cellRight
  norm_num

/-- The point `3/2` lies in the gap `(1, 2)` of rank `1` … -/
example : InGap (1 : Fin 3) (3 / 2) :=
  ⟨0, by unfold cellRight; norm_num, by unfold cellRight; norm_num⟩

/-- … and so its bad rank is `1 = ⌊3/2⌋ mod 3`. -/
example : badRank 3 (3 / 2 : ℝ) = 1 :=
  badRank_eq_of_inGap (q := (1 : Fin 3))
    ⟨0, by unfold cellRight; norm_num, by unfold cellRight; norm_num⟩

/-- … while it lies in a cell of each of the other two ranks: `[0, 2]` of rank `2`, and `[1, 3]`
of rank `0` (index `1`). -/
example : (3 / 2 : ℝ) ∈ cell (2 : Fin 3) 0 ∧ (3 / 2 : ℝ) ∈ cell (0 : Fin 3) 1 := by
  unfold cell cellLeft cellRight
  norm_num

end MiscMath.Analysis.KolmogorovArnold
