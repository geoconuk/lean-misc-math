/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Butterfly

/-!
# The red-blue pebble game: the two I/O bounds for the FFT graph

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

In a complete calculation of the `2^k`-point FFT graph every vertex holds a red pebble at some
point (`fft_exists_red`): the outputs end blue, the first pebble on a non-input comes from computing
it, and computing a vertex needs its predecessors red. Two bounds follow:

* `fft_two_pow_succ_le`: each of the `2^k` inputs is loaded and each of the `2^k` outputs stored,
  so `q ≥ 2^(k+1)`;
* `fft_mul_card_le`: Hong and Kung's key argument (`Trace.mul_card_newReds_le`) with the domination
  bound for the FFT graph (`card_le_bfly_of_dominated`) gives
  `S · (k + 1) 2^k ≤ (q + S) · 2S log₂ (4S)`.
-/

namespace MiscMath.Computability.RedBluePebbleGame

open Finset

variable {k S : ℕ}

/-- The butterfly's edges can be decided, which lets concrete calculations be checked by
`decide`. -/
instance fftEdge.decidableRel (k : ℕ) : DecidableRel (fftEdge k) := fun u v => by
  unfold fftEdge
  infer_instance

/-- The vertices of one level of the FFT graph number `2^k`. -/
theorem card_filter_fst_eq (a : Fin (k + 1)) :
    (univ.filter fun v : Fin (k + 1) × Fin (2 ^ k) => v.1 = a).card = 2 ^ k := by
  have : (univ.filter fun v : Fin (k + 1) × Fin (2 ^ k) => v.1 = a) = {a} ×ˢ univ := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, and_true]
  rw [this, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
    one_mul]

/-- In a complete calculation of the FFT graph, every vertex holds a red pebble at some point. -/
theorem fft_exists_red (hk : 1 ≤ k) (T : Trace (fftEdge k) (univ.filter (·.1 = 0)) S)
    (h0 : T.σ 0 = (∅, univ.filter (·.1 = 0)))
    (ht : T.σ T.t = (∅, univ.filter (·.1 = Fin.last k))) :
    ∀ v, ∃ j ≤ T.t, v ∈ (T.σ j).1 := by
  have hnotI : ∀ v : Fin (k + 1) × Fin (2 ^ k), (v.1 : ℕ) ≠ 0 →
      v ∉ univ.filter (fun v : Fin (k + 1) × Fin (2 ^ k) => v.1 = 0) := by
    intro v hv h
    simp only [mem_filter, mem_univ, true_and] at h
    exact hv (by rw [h, Fin.val_zero])
  -- Every vertex holds a pebble at some point, by induction down from the outputs.
  have hpeb : ∀ d, ∀ v : Fin (k + 1) × Fin (2 ^ k), (v.1 : ℕ) + d = k →
      ∃ j ≤ T.t, v ∈ (T.σ j).1 ∨ v ∈ (T.σ j).2 := by
    intro d
    induction d with
    | zero =>
      intro v hv
      refine ⟨T.t, le_rfl, Or.inr ?_⟩
      rw [ht]
      simp only [mem_filter, mem_univ, true_and]
      exact Fin.ext (by simp only [Fin.val_last]; omega)
    | succ d ih =>
      intro v hv
      let w : Fin (k + 1) × Fin (2 ^ k) := (⟨(v.1 : ℕ) + 1, by omega⟩, v.2)
      obtain ⟨j, hj, hw⟩ := ih w (by simp only [w]; omega)
      obtain ⟨i, hi, -, hp, -⟩ := T.exists_compute (hnotI w (by simp [w])) h0 j hj hw
      exact ⟨i, by omega, Or.inl (hp v ⟨rfl, Or.inl rfl⟩)⟩
  intro v
  have hvlt := v.1.isLt
  by_cases hvk : (v.1 : ℕ) = k
  · obtain ⟨j, hj, hv⟩ := hpeb 0 v (by omega)
    obtain ⟨i, hi, -, -, hR⟩ := T.exists_compute (hnotI v (by omega)) h0 j hj hv
    exact ⟨i + 1, by omega, by rw [hR]; exact mem_insert_self _ _⟩
  · let w : Fin (k + 1) × Fin (2 ^ k) := (⟨(v.1 : ℕ) + 1, by omega⟩, v.2)
    obtain ⟨j, hj, hw⟩ := hpeb (k - (v.1 : ℕ) - 1) w (by simp only [w]; omega)
    obtain ⟨i, hi, -, hp, -⟩ := T.exists_compute (hnotI w (by simp [w])) h0 j hj hw
    exact ⟨i, by omega, hp v ⟨rfl, Or.inl rfl⟩⟩

/-- **The trivial bound.** Every input is loaded and every output stored: `q ≥ 2^(k+1)`. -/
theorem fft_two_pow_succ_le {q : ℕ} (hk : 1 ≤ k)
    (h : HasCompleteCalculation (fftEdge k) (univ.filter (·.1 = 0))
      (univ.filter (·.1 = Fin.last k)) S q) :
    2 ^ (k + 1) ≤ q := by
  obtain ⟨T, h0, ht, hq⟩ := h.exists_trace
  have hred := fft_exists_red hk T h0 ht
  have hdisj : Disjoint (univ.filter fun v : Fin (k + 1) × Fin (2 ^ k) => v.1 = 0)
      (univ.filter fun v : Fin (k + 1) × Fin (2 ^ k) => v.1 = Fin.last k) := by
    rw [Finset.disjoint_filter]
    intro v _ hv0 hvk
    have := congrArg Fin.val (hv0.symm.trans hvk)
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have := T.card_add_card_le h0 (by rw [ht]) hdisj (fun x _ => hred x)
  rw [card_filter_fst_eq, card_filter_fst_eq, hq] at this
  rw [pow_succ]
  omega

/-- **The domination bound on I/O.** `S · (k + 1) 2^k ≤ (q + S) · 2S log₂ (4S)`. -/
theorem fft_mul_card_le {q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (univ.filter (·.1 = 0))
      (univ.filter (·.1 = Fin.last k)) S q) :
    (S : ℝ) * ((k + 1) * 2 ^ k) ≤ (q + S) * (2 * S * Real.logb 2 (4 * S)) := by
  obtain ⟨T, h0, ht, hq⟩ := h.exists_trace
  have hred := fft_exists_red hk T h0 ht
  have hall : T.newReds 0 T.t = univ := by
    refine eq_univ_of_forall fun v => ?_
    obtain ⟨j, hj, hv⟩ := hred v
    obtain ⟨i, hi, h₁, h₂⟩ := T.exists_new_red (by rw [h0]; exact Finset.notMem_empty v) j hv
    exact mem_biUnion.2 ⟨i, mem_Ico.2 ⟨by omega, by omega⟩, mem_sdiff.2 ⟨h₂, h₁⟩⟩
  have key := T.mul_card_newReds_le hS (bfly (2 * S)) (bfly_nonneg _)
    (fun D W hD hW => (card_le_bfly_of_dominated hW).trans (bfly_mono hD)) 0 (Nat.zero_le _)
  have hct : T.charges T.t = q := hq
  have hc0 : T.charges 0 = 0 := by simp [Trace.charges]
  rw [hall, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    bfly_two_mul, hct, hc0] at key
  push_cast at key
  linarith

end MiscMath.Computability.RedBluePebbleGame
