/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Domination
import MiscMath.Computability.RedBluePebbleGame.LogBound
import Mathlib.Data.Fintype.Prod

/-!
# The red-blue pebble game: how much of the FFT graph `d` vertices can dominate

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

`card_le_bfly_of_dominated`: in the `2^k`-point FFT graph, a set of vertices dominated by `D` has
at most `|D| · log₂ (2|D|)` elements. This is the argument of Hong and Kung's Theorem 4.1, with its
constant corrected: they claim `2d log₂ d`, which is `0` at `d = 1` although a single vertex
dominates itself, and their induction uses that case.

The induction runs over the sub-butterflies of the fixed graph. The one of height `L` numbered `β`
(`InBlock L β`) has the levels up to `L` and the lanes whose bits from `L` up spell `β`. It splits
into two sub-butterflies of height `L - 1`, `A` and `B`, and its top level `C`. Each vertex of `C`
not in the dominator has one straight path to it through `A` and one through `B`. The straight
paths through `A` of vertices in distinct lanes of `A` are disjoint, and at most two vertices of
`C` share a lane of `A`. So at most `2|D ∩ A|` of them, and likewise at most `2|D ∩ B|`, escape
the dominator.
-/

namespace MiscMath.Computability.RedBluePebbleGame

open Finset Relation

/-! ## Bits -/

theorem xor_two_pow_xor_two_pow (x L : ℕ) : x ^^^ 2 ^ L ^^^ 2 ^ L = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem testBit_xor_two_pow_self (x L : ℕ) : (x ^^^ 2 ^ L).testBit L = !x.testBit L := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases x.testBit L <;> rfl

theorem xor_two_pow_div (x L : ℕ) : (x ^^^ 2 ^ L) / 2 ^ (L + 1) = x / 2 ^ (L + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
  have : ¬ L = i + (L + 1) := by omega
  simp [this]

theorem div_two_pow_eq (x L : ℕ) :
    x / 2 ^ L = 2 * (x / 2 ^ (L + 1)) + if x.testBit L then 1 else 0 := by
  have h := Nat.div_add_mod (x / 2 ^ L) 2
  rw [Nat.div_div_eq_div_mul, ← pow_succ] at h
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 := Nat.mod_two_eq_zero_or_one (x / 2 ^ L)
  split_ifs with hb
  · simp only [decide_eq_true_eq] at hb
    omega
  · simp only [decide_eq_true_eq] at hb
    omega

theorem xor_two_pow_lt {x L k : ℕ} (hx : x < 2 ^ k) (hL : L < k) : x ^^^ 2 ^ L < 2 ^ k :=
  Nat.xor_lt_two_pow hx (Nat.pow_lt_pow_right (by norm_num) hL)

/-! ## Sub-butterflies -/

variable {k : ℕ}

/-- `v` lies in the sub-butterfly of height `L` numbered `β`: at a level at most `L`, in a lane
whose bits from `L` up spell `β`. -/
abbrev InBlock (L β : ℕ) (v : Fin (k + 1) × Fin (2 ^ k)) : Prop :=
  (v.1 : ℕ) ≤ L ∧ (v.2 : ℕ) / 2 ^ L = β

/-- A straight path up lane `y`, from level `0` to level `l`, avoiding `D` if the lane does below
level `l`. -/
theorem straight_path (D : Finset (Fin (k + 1) × Fin (2 ^ k))) (y : Fin (2 ^ k)) :
    ∀ (l : ℕ) (hl : l ≤ k), (∀ v : Fin (k + 1) × Fin (2 ^ k), v.2 = y → (v.1 : ℕ) ≤ l → v ∉ D) →
      ReflTransGen (fun a b => fftEdge k a b ∧ a ∉ D ∧ b ∉ D)
        (⟨0, by omega⟩, y) (⟨l, by omega⟩, y) := by
  intro l
  induction l with
  | zero => exact fun _ _ => ReflTransGen.refl
  | succ l ih =>
    intro hl hD
    refine ReflTransGen.tail (ih (by omega) fun v hv hvl => hD v hv (by omega)) ⟨⟨rfl, Or.inl rfl⟩,
      hD _ rfl (by simp), hD _ rfl (by simp)⟩

/-- The vertices of the top level of a sub-butterfly that escape the dominator: at most twice the
number of dominator vertices in either half below. -/
theorem card_escaping_le (D W : Finset (Fin (k + 1) × Fin (2 ^ k))) (L β : ℕ) (hL : L + 1 ≤ k)
    (b : Bool)
    (hW : ∀ w ∈ W, (w.1 : ℕ) = L + 1 ∧ (w.2 : ℕ) / 2 ^ (L + 1) = β ∧ w ∉ D)
    (hdom : ∀ w ∈ W, Dominated (fftEdge k) (univ.filter (·.1 = 0)) D w) :
    W.card ≤ 2 * (D.filter (InBlock L (2 * β + if b then 1 else 0))).card := by
  classical
  -- The lane of `w`'s predecessor in the half selected by `b`.
  let g : Fin (k + 1) × Fin (2 ^ k) → ℕ := fun w =>
    if (w.2 : ℕ).testBit L = b then (w.2 : ℕ) else (w.2 : ℕ) ^^^ 2 ^ L
  have hg_lt : ∀ w : Fin (k + 1) × Fin (2 ^ k), g w < 2 ^ k := by
    intro w
    simp only [g]
    split_ifs
    · exact w.2.isLt
    · exact xor_two_pow_lt w.2.isLt (by omega)
  have hg_bit : ∀ w : Fin (k + 1) × Fin (2 ^ k), (g w).testBit L = b := by
    intro w
    simp only [g]
    split_ifs with h
    · exact h
    · rw [testBit_xor_two_pow_self]
      cases hb : (w.2 : ℕ).testBit L <;> cases b <;> simp_all
  have hg_div : ∀ w : Fin (k + 1) × Fin (2 ^ k), g w / 2 ^ (L + 1) = (w.2 : ℕ) / 2 ^ (L + 1) := by
    intro w
    simp only [g]
    split_ifs
    · rfl
    · exact xor_two_pow_div _ _
  have hg_edge : ∀ w : Fin (k + 1) × Fin (2 ^ k),
      (w.2 : ℕ) = g w ∨ (w.2 : ℕ) = g w ^^^ 2 ^ L := by
    intro w
    simp only [g]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (xor_two_pow_xor_two_pow _ _).symm
  -- Each escaping vertex has a dominator vertex straight below it, in the chosen half.
  have hkey : ∀ w ∈ W, g w ∈ (D.filter (InBlock L (2 * β + if b then 1 else 0))).image
      (fun p => (p.2 : ℕ)) := by
    intro w hw
    obtain ⟨hw1, hw2, hwD⟩ := hW w hw
    by_contra hnot
    set y : Fin (2 ^ k) := ⟨g w, hg_lt w⟩ with hy
    have hlane : ∀ v : Fin (k + 1) × Fin (2 ^ k), v.2 = y → (v.1 : ℕ) ≤ L → v ∉ D := by
      intro v hv hvl hvD
      apply hnot
      refine Finset.mem_image.2 ⟨v, Finset.mem_filter.2 ⟨hvD, hvl, ?_⟩, by rw [hv]⟩
      rw [hv, div_two_pow_eq, show ((y : Fin (2 ^ k)) : ℕ) = g w from rfl, hg_div, hw2, hg_bit]
    have hpath := straight_path D y L (by omega) hlane
    have hedge : fftEdge k (⟨L, by omega⟩, y) w := ⟨by simp [hw1], hg_edge w⟩
    have hfull := ReflTransGen.tail hpath ⟨hedge, hlane _ rfl (by simp), hwD⟩
    refine hdom w hw (⟨0, by omega⟩, y) ?_ (hlane _ rfl (by simp)) hfull
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  -- At most two escaping vertices share a lane below.
  have hfib : ∀ y ∈ W.image g, (W.filter fun w => g w = y).card ≤ 2 := by
    intro y _
    have hinj : Set.InjOn (fun w : Fin (k + 1) × Fin (2 ^ k) => (w.2 : ℕ))
        ↑(W.filter fun w => g w = y) := by
      intro v hv w hw hvw
      rw [Finset.mem_coe, Finset.mem_filter] at hv hw
      have h1 := (hW v hv.1).1
      have h2 := (hW w hw.1).1
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext hvw)
    have hmaps : Set.MapsTo (fun w : Fin (k + 1) × Fin (2 ^ k) => (w.2 : ℕ))
        ↑(W.filter fun w => g w = y) ↑({y, y ^^^ 2 ^ L} : Finset ℕ) := by
      intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rw [← hw.2]
      exact hg_edge w
    exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans Finset.card_le_two
  calc W.card ≤ 2 * (W.image g).card := Finset.card_le_mul_card_image W 2 hfib
    _ ≤ 2 * ((D.filter (InBlock L (2 * β + if b then 1 else 0))).image
          (fun p => (p.2 : ℕ))).card :=
        Nat.mul_le_mul_left 2 (Finset.card_le_card fun y hy => by
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
          exact hkey w hw)
    _ ≤ 2 * (D.filter (InBlock L (2 * β + if b then 1 else 0))).card :=
        Nat.mul_le_mul_left 2 Finset.card_image_le

/-- The domination bound on one sub-butterfly, by induction on its height. -/
theorem card_le_bfly_of_inBlock (D : Finset (Fin (k + 1) × Fin (2 ^ k))) :
    ∀ L, L ≤ k → ∀ (β : ℕ) (W : Finset (Fin (k + 1) × Fin (2 ^ k))), (∀ w ∈ W, InBlock L β w) →
      (∀ w ∈ W, Dominated (fftEdge k) (univ.filter (·.1 = 0)) D w) →
      (W.card : ℝ) ≤ bfly (D.filter (InBlock L β)).card := by
  classical
  intro L
  induction L with
  | zero =>
    intro _ β W hW hdom
    rcases W.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · simpa using bfly_nonneg _
    · have hw0 := hW w hw
      simp only [InBlock, pow_zero, Nat.div_one, Nat.le_zero] at hw0
      have hsub : W ⊆ {w} := by
        intro v hv
        have hv0 := hW v hv
        simp only [InBlock, pow_zero, Nat.div_one, Nat.le_zero] at hv0
        rw [Finset.mem_singleton]
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      have hwD : w ∈ D := by
        by_contra hwD
        refine hdom w hw w ?_ hwD ReflTransGen.refl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Fin.ext hw0.1
      have h1 : 1 ≤ (D.filter (InBlock 0 β)).card :=
        Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨hwD, by
          simp only [InBlock, pow_zero, Nat.div_one]; omega⟩⟩
      calc (W.card : ℝ) ≤ 1 := by exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
        _ = bfly 1 := bfly_one.symm
        _ ≤ bfly _ := bfly_mono h1
  | succ L ih =>
    intro hLk β W hW hdom
    -- The two halves below, and the top level.
    let WA := W.filter (InBlock L (2 * β))
    let WB := W.filter (InBlock L (2 * β + 1))
    let WC := W.filter fun w => (w.1 : ℕ) = L + 1
    let A := D.filter (InBlock L (2 * β))
    let B := D.filter (InBlock L (2 * β + 1))
    let C := D.filter fun v => (v.1 : ℕ) = L + 1 ∧ (v.2 : ℕ) / 2 ^ (L + 1) = β
    have hA := ih (by omega) (2 * β) WA (fun w hw => (Finset.mem_filter.1 hw).2)
      (fun w hw => hdom w (Finset.mem_filter.1 hw).1)
    have hB := ih (by omega) (2 * β + 1) WB (fun w hw => (Finset.mem_filter.1 hw).2)
      (fun w hw => hdom w (Finset.mem_filter.1 hw).1)
    -- Every vertex of the sub-butterfly lies in one of the three parts.
    have hcover : W.card ≤ WA.card + WB.card + WC.card := by
      refine (Finset.card_le_card (s := W) (t := WA ∪ WB ∪ WC) fun w hw => ?_).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      obtain ⟨h1, h2⟩ := hW w hw
      have h3 := div_two_pow_eq (w.2 : ℕ) L
      simp only [WA, WB, WC, Finset.mem_union, Finset.mem_filter, InBlock]
      by_cases hl : (w.1 : ℕ) = L + 1
      · exact Or.inr ⟨hw, hl⟩
      · by_cases hb : (w.2 : ℕ).testBit L
        · rw [if_pos hb] at h3
          exact Or.inl (Or.inr ⟨hw, by omega, by omega⟩)
        · rw [if_neg hb] at h3
          exact Or.inl (Or.inl ⟨hw, by omega, by omega⟩)
    -- The dominator splits the same way.
    have hDsum : A.card + B.card + C.card ≤ (D.filter (InBlock (L + 1) β)).card := by
      have hAB : Disjoint A B := by
        refine Finset.disjoint_left.2 fun v hvA hvB => ?_
        simp only [A, B, Finset.mem_filter, InBlock] at hvA hvB
        omega
      have hABC : Disjoint (A ∪ B) C := by
        refine Finset.disjoint_left.2 fun v hvAB hvC => ?_
        simp only [A, B, C, Finset.mem_union, Finset.mem_filter, InBlock] at hvAB hvC
        omega
      rw [← Finset.card_union_of_disjoint hAB, ← Finset.card_union_of_disjoint hABC]
      refine Finset.card_le_card fun v hv => ?_
      have h3 := div_two_pow_eq (v.2 : ℕ) L
      simp only [A, B, C, Finset.mem_union, Finset.mem_filter, InBlock] at hv
      simp only [Finset.mem_filter, InBlock]
      rcases hv with (⟨hvD, h1, h2⟩ | ⟨hvD, h1, h2⟩) | ⟨hvD, h1, h2⟩ <;>
        refine ⟨hvD, by omega, ?_⟩ <;> split_ifs at h3 <;> omega
    -- The top level: those in the dominator, and those escaping it.
    have hC : (WC.card : ℝ) ≤ C.card + 2 * ((min A.card B.card : ℕ) : ℝ) := by
      have hsplit : WC.card ≤ (WC.filter (· ∈ D)).card + (WC.filter (· ∉ D)).card := by
        rw [Finset.card_filter_add_card_filter_not]
      have hin : (WC.filter (· ∈ D)).card ≤ C.card := by
        refine Finset.card_le_card fun v hv => ?_
        simp only [WC, C, Finset.mem_filter] at hv ⊢
        exact ⟨hv.2, hv.1.2, (hW v hv.1.1).2⟩
      have hesc : ∀ w ∈ WC.filter (· ∉ D), (w.1 : ℕ) = L + 1 ∧
          (w.2 : ℕ) / 2 ^ (L + 1) = β ∧ w ∉ D := by
        intro w hw
        simp only [WC, Finset.mem_filter] at hw
        exact ⟨hw.1.2, (hW w hw.1.1).2, hw.2⟩
      have hdom' : ∀ w ∈ WC.filter (· ∉ D), Dominated (fftEdge k) (univ.filter (·.1 = 0)) D w :=
        fun w hw => hdom w (Finset.mem_filter.1 (Finset.mem_filter.1 hw).1).1
      have hescA := card_escaping_le D _ L β hLk false hesc hdom'
      have hescB := card_escaping_le D _ L β hLk true hesc hdom'
      simp only [Bool.false_eq_true, if_false, add_zero, if_true] at hescA hescB
      have : (WC.filter (· ∉ D)).card ≤ 2 * min A.card B.card := by
        rcases le_total A.card B.card with h | h
        · rw [min_eq_left h]; exact hescA
        · rw [min_eq_right h]; exact hescB
      push_cast
      exact_mod_cast (hsplit.trans (Nat.add_le_add hin this))
    calc (W.card : ℝ) ≤ WA.card + WB.card + WC.card := by exact_mod_cast hcover
      _ ≤ bfly A.card + bfly B.card + C.card + 2 * ((min A.card B.card : ℕ) : ℝ) := by
          linarith
      _ ≤ bfly (A.card + B.card + C.card) := bfly_combine _ _ _
      _ ≤ bfly (D.filter (InBlock (L + 1) β)).card := bfly_mono hDsum

/-- **The domination bound.** In the `2^k`-point FFT graph, a set of vertices dominated by `D` has
at most `|D| · log₂ (2|D|)` elements (none if `D` is empty). -/
theorem card_le_bfly_of_dominated {D W : Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hW : ∀ w ∈ W, Dominated (fftEdge k) (univ.filter (·.1 = 0)) D w) :
    (W.card : ℝ) ≤ bfly D.card := by
  classical
  have hall : ∀ v : Fin (k + 1) × Fin (2 ^ k), InBlock k 0 v := fun v =>
    ⟨by omega, Nat.div_eq_of_lt v.2.isLt⟩
  have h := card_le_bfly_of_inBlock D k le_rfl 0 W (fun w _ => hall w) hW
  rwa [Finset.filter_true_of_mem fun v _ => hall v] at h

end MiscMath.Computability.RedBluePebbleGame
