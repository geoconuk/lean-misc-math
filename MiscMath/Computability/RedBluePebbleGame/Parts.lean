/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
module

public import MiscMath.Computability.RedBluePebbleGame.Butterfly
public import MiscMath.Computability.RedBluePebbleGame.Partition
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The red-blue pebble game: how many parts a dominator partition of the FFT graph needs

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

This is Hong and Kung's Theorem 4.1, with its constant corrected. Each part of an `S`-dominator
partition of the `2^k`-point FFT graph is dominated by at most `S` vertices, so it has at most
`S log₂ (2S)` of them (`card_le_bfly_of_dominated`), and the parts add up to all `(k + 1) 2^k`
vertices (`fft_card_le_mul_bfly`). The single vertices, taken level by level, are an
`S`-dominator partition for every `S ≥ 1` (`fft_exists_isDominatorPartition`), so the least number
of parts is attained there.
-/

@[expose] public section

namespace MiscMath.Computability.RedBluePebbleGame

open Finset

/-- The parts of a partition add up to the whole. -/
theorem card_eq_sum_of_existsUnique {V : Type*} [Fintype V] {h : ℕ}
    {P : Fin h → Finset V} (hP : ∀ v, ∃! i, v ∈ P i) : Fintype.card V = ∑ i, (P i).card := by
  classical
  have hU : (univ : Finset (Fin h)).biUnion P = univ := by
    refine eq_univ_of_forall fun v => ?_
    obtain ⟨i, hi, -⟩ := hP v
    exact mem_biUnion.2 ⟨i, mem_univ _, hi⟩
  rw [← card_univ, ← hU, card_biUnion]
  intro i _ j _ hij
  refine disjoint_left.2 fun v hvi hvj => hij ?_
  obtain ⟨l, -, hl⟩ := hP v
  exact (hl i hvi).trans (hl j hvj).symm

variable {k : ℕ}

/-- **Theorem 4.1, with its constant corrected.** The parts of an `S`-dominator partition of the
`2^k`-point FFT graph number at least `(k + 1) 2^k / (S log₂ (2S))`. -/
theorem fft_card_le_mul_bfly {S h : ℕ} {P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hP : IsDominatorPartition (fftEdge k) (univ.filter (·.1 = 0)) S P) :
    ((k + 1) * 2 ^ k : ℝ) ≤ h * bfly S := by
  classical
  obtain ⟨hcov, hdom, -⟩ := hP
  have hcard : (k + 1) * 2 ^ k = ∑ i, (P i).card := by
    rw [← card_eq_sum_of_existsUnique hcov, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hpart : ∀ i, ((P i).card : ℝ) ≤ bfly S := fun i => by
    obtain ⟨D, hD, hDom⟩ := hdom i
    exact (card_le_bfly_of_dominated (dominates_iff.1 hDom)).trans (bfly_mono hD)
  calc ((k + 1) * 2 ^ k : ℝ) = (((k + 1) * 2 ^ k : ℕ) : ℝ) := by push_cast; ring
    _ = ∑ i, ((P i).card : ℝ) := by rw [hcard]; push_cast; rfl
    _ ≤ ∑ _i : Fin h, bfly S := sum_le_sum fun i _ => hpart i
    _ = h * bfly S := by simp

/-- The single vertices of the FFT graph, in the order of their levels, are an `S`-dominator
partition for every `S ≥ 1`: each dominates itself, and edges run from a level to the next. -/
theorem fft_exists_isDominatorPartition (k : ℕ) {S : ℕ} (hS : 1 ≤ S) :
    ∃ P : Fin ((k + 1) * 2 ^ k) → Finset (Fin (k + 1) × Fin (2 ^ k)),
      IsDominatorPartition (fftEdge k) (univ.filter (·.1 = 0)) S P := by
  classical
  refine ⟨fun n => {finProdFinEquiv.symm n}, fun v => ⟨finProdFinEquiv v, by simp,
    fun j hj => ?_⟩, fun n => ⟨{finProdFinEquiv.symm n}, by simpa using hS,
    dominates_of_subset le_rfl⟩, fun i j u hu v hv huv => ?_⟩
  · simp only [mem_singleton] at hj
    rw [hj, Equiv.apply_symm_apply]
  · simp only [mem_singleton] at hu hv
    subst hu hv
    rw [Fin.le_iff_val_le_val, ← Equiv.apply_symm_apply finProdFinEquiv i,
      ← Equiv.apply_symm_apply finProdFinEquiv j]
    set u := finProdFinEquiv.symm i
    set v := finProdFinEquiv.symm j
    -- The index of `(l, x)` is `x + 2^k l`, and an edge raises the level by one.
    change (u.2 : ℕ) + 2 ^ k * u.1 ≤ v.2 + 2 ^ k * v.1
    have hu2 := u.2.isLt
    rw [huv.1, Nat.mul_succ]
    omega

/-- The FFT graph is a computation DAG for every `k ≥ 1`: edges raise the level by one, the
inputs (level `0`) are the vertices with no predecessor, the vertices with no successor are the
outputs (level `k`), and the two levels differ. So the key lemma applies to it. -/
theorem fft_isComputationDAG {k : ℕ} (hk : 1 ≤ k) :
    IsComputationDAG (fftEdge k) (univ.filter (·.1 = 0)) (univ.filter (·.1 = Fin.last k)) := by
  have hlt : ∀ {u v : Fin (k + 1) × Fin (2 ^ k)}, Relation.TransGen (fftEdge k) u v →
      (u.1 : ℕ) < v.1 := by
    intro u v h
    induction h with
    | single h => rw [h.1]; omega
    | tail _ h ih => rw [h.1]; omega
  refine ⟨fun v h => (hlt h).false, fun v => ?_, fun v hv => ?_, ?_⟩
  · simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro hv u ⟨h, -⟩
      rw [hv] at h
      simp at h
    · intro h
      by_contra hv
      have hv' : (v.1 : ℕ) ≠ 0 := fun h' => hv (Fin.ext h')
      exact h (⟨(v.1 : ℕ) - 1, by omega⟩, v.2) ⟨by simp only; omega, Or.inl rfl⟩
  · simp only [mem_filter, mem_univ, true_and]
    by_contra hne
    have hv' : (v.1 : ℕ) < k := by
      have := v.1.isLt
      have : (v.1 : ℕ) ≠ k := fun h' => hne (Fin.ext (by simpa using h'))
      omega
    exact hv (⟨(v.1 : ℕ) + 1, by omega⟩, v.2) ⟨rfl, Or.inl rfl⟩
  · rw [disjoint_filter]
    intro v _ h0 hk'
    rw [h0] at hk'
    have := congrArg Fin.val hk'
    simp at this
    omega

end MiscMath.Computability.RedBluePebbleGame
