/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.Staircase
import MiscMath.Analysis.KolmogorovArnold.Levels

/-!
# The approximating tuple of inner functions

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; part of the density argument (Layer 2 of the development). Its
declarations are proof: machine-generated, kernel-checked and axiom-audited, and may be read by
no one.

Given a tuple `φ` of inner functions and integers `N, M ≥ 1`, the **approximant** of rank `q` is
the staircase of rank `q` on the `u = N t` line whose levels are the rational `level φ N M q j`
of `Levels.lean`. This is the tuple `(φ_1, …, φ_{2n+1})` of Hedberg's Lemma 2 (p. 269): constant
with a rational value on every cell of its rank, distinct values across cells and ranks, and —
the content of this module — **uniformly within `ε` of `φ_q`** once `N` exceeds the modulus of
continuity of the `φ_q` and `M` is large in terms of `N` (`abs_approximant_sub_lt`,
`dist_approximant_lt`). The value taken on a cell is `approximant_apply_of_mem_cell`.
-/

open unitInterval Finset

namespace MiscMath.Analysis.KolmogorovArnold

noncomputable section

variable {m : ℕ}

/-- The real levels of rank `q`: `j ↦ level φ N M q j`, cast to `ℝ`. -/
def levels (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) (j : ℕ) : ℝ := ((level φ N M q j : ℚ) : ℝ)

theorem levels_monotone (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) :
    Monotone (levels φ N M q) :=
  level_cast_monotone φ N hM q

theorem endValue_le_levels (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) (j : ℕ) :
    endValue φ N q j ≤ levels φ N M q j :=
  le_level φ N hM q j

theorem levels_lt (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) (j : ℕ) :
    levels φ N M q j < endValue φ N q j + m * (j + 1) / M :=
  level_lt φ N hM q j

/-- The approximant of rank `q`: the staircase of rank `q` with the levels of `φ`, rescaled to
`I`, with `N + 1` ramps (enough for every cell meeting `[0, N]`). -/
def approximant (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) : Inner :=
  stairInner N q (levels_monotone φ N hM q) (N + 1)

theorem approximant_apply (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) (t : I) :
    (approximant φ N hM q : C(I, ℝ)) t = stair q (levels φ N M q) (N + 1) (N * t) := rfl

/-- On a cell of rank `q` and index `j ≤ N + 1`, the approximant takes the level of that cell. -/
theorem approximant_apply_of_mem_cell (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M)
    (q : Fin m) {j : ℕ} (hj : j ≤ N + 1) {t : I} (ht : (N : ℝ) * t ∈ cell q j) :
    (approximant φ N hM q : C(I, ℝ)) t = levels φ N M q j := by
  rw [approximant_apply]
  exact stair_eq_of_mem_cell q _ hj ht

theorem cellRight_succ (q : Fin m) (j : ℕ) : cellRight q (j + 1) = cellRight q j + m := by
  unfold cellRight
  push_cast
  ring

/-- **The approximant is uniformly close to `φ_q`.** If `η` is a modulus of continuity of every
`φ_q` at `ε / 4`, `m / N < η` and `m (N + 2) / M ≤ ε / 4`, then the approximant of rank `q` is
within `ε / 2` of `φ_q` at every point of `I`. -/
theorem abs_approximant_sub_lt (φ : Fin m → Inner) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) {ε η : ℝ}
    (hη : ∀ q (s t : I), |(s : ℝ) - t| < η →
      |(φ q : C(I, ℝ)) s - (φ q : C(I, ℝ)) t| < ε / 4)
    (hNη : (m : ℝ) / N < η) (hMε : (m : ℝ) * (N + 2) / M ≤ ε / 4) (q : Fin m) (t : I) :
    |(approximant φ N hM q : C(I, ℝ)) t - (φ q : C(I, ℝ)) t| < ε / 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := one_le_cast_of_fin q
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set u : ℝ := N * t with hu
  have hu0 : 0 ≤ u := mul_nonneg hNR.le t.2.1
  have huN : u ≤ N := by
    rw [hu]
    exact mul_le_of_le_one_right hNR.le t.2.2
  -- The modulus bound is monotone in the cast-free form `m / N < η`, and `(m - 1) / N < η`.
  have hm1N : ((m : ℝ) - 1) / N < η := by
    refine lt_of_le_of_lt ?_ hNη
    exact div_le_div_of_nonneg_right (by linarith) hNR.le
  have hMε' : ∀ j : ℕ, j ≤ N + 1 → (m : ℝ) * (j + 1) / M ≤ ε / 4 := by
    intro j hj
    refine le_trans ?_ hMε
    have : (j : ℝ) + 1 ≤ N + 2 := by
      have : (j : ℝ) ≤ N + 1 := by exact_mod_cast hj
      linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by linarith)) hMR.le
  by_cases hgap : InGap q u
  · -- `u` lies in the gap after the cell of index `j`: the staircase is between two levels.
    obtain ⟨j, h1, h2⟩ := hgap
    have hj : j ≤ N := le_of_cellLeft_le ((cellLeft_le_cellRight q j).trans h1.le) huN
    have hstair := stair_mem_Icc_of_gap q (levels_monotone φ N hM q) (Nat.succ_le_succ hj)
      h1.le h2.le
    rw [approximant_apply]
    -- The clamped endpoint of cell `j` is `cellRight q j / N`, just below `t`.
    have hend : (cellEnd N q j : ℝ) = cellRight q j / N := by
      rw [coe_cellEnd, min_eq_right]
      rw [div_le_iff₀ hNR, one_mul]
      exact (h1.trans_le huN).le
    have hlow : |(cellEnd N q j : ℝ) - t| < η := by
      rw [hend, abs_sub_comm, abs_of_pos (by rw [sub_pos, div_lt_iff₀ hNR]; linarith)]
      calc (t : ℝ) - cellRight q j / N = (u - cellRight q j) / N := by rw [hu]; field_simp
        _ ≤ 1 / N := by
          apply div_le_div_of_nonneg_right _ hNR.le
          linarith
        _ ≤ m / N := div_le_div_of_nonneg_right hm1 hNR.le
        _ < η := hNη
    have hφlow := hη q (cellEnd N q j) t hlow
    -- The clamped endpoint of cell `j + 1` is at or above `t`, and within `m / N` of it.
    have hend' : (t : ℝ) ≤ cellEnd N q (j + 1) := by
      rw [coe_cellEnd, cellRight_succ]
      refine le_min t.2.2 ?_
      rw [le_div_iff₀ hNR]
      linarith
    have hhigh : |(cellEnd N q (j + 1) : ℝ) - t| < η := by
      rw [abs_of_nonneg (by linarith)]
      calc (cellEnd N q (j + 1) : ℝ) - t ≤ cellRight q (j + 1) / N - t := by
            rw [coe_cellEnd]; linarith [min_le_right (1 : ℝ) (cellRight q (j + 1) / N)]
        _ = (cellRight q j + m - u) / N := by rw [cellRight_succ, hu]; field_simp
        _ ≤ m / N := by
          apply div_le_div_of_nonneg_right _ hNR.le
          linarith
        _ < η := hNη
    have hφhigh := hη q (cellEnd N q (j + 1)) t hhigh
    have hl1 := endValue_le_levels φ N hM q j
    have hl2 := levels_lt φ N hM q (j + 1)
    have hl3 := hMε' (j + 1) (Nat.succ_le_succ hj)
    unfold endValue at hl1 hl2
    rw [abs_lt] at hφlow hφhigh ⊢
    push_cast at hl2 hl3
    constructor <;> linarith [hstair.1, hstair.2]
  · -- `u` lies in a cell of index `j`: the staircase takes the level of that cell.
    obtain ⟨j, hj⟩ := exists_mem_cell_of_not_inGap hu0 hgap
    have hjN : j ≤ N := le_of_cellLeft_le hj.1 huN
    rw [approximant_apply_of_mem_cell φ N hM q (Nat.le_succ_of_le hjN) hj]
    -- The clamped endpoint of the cell is at or above `t`, and within `(m - 1) / N` of it.
    have hend : (t : ℝ) ≤ cellEnd N q j := by
      rw [coe_cellEnd]
      refine le_min t.2.2 ?_
      rw [le_div_iff₀ hNR]
      linarith [hj.2]
    have hclose : |(cellEnd N q j : ℝ) - t| < η := by
      rw [abs_of_nonneg (by linarith)]
      calc (cellEnd N q j : ℝ) - t ≤ cellRight q j / N - t := by
            rw [coe_cellEnd]; linarith [min_le_right (1 : ℝ) (cellRight q j / N)]
        _ = (cellRight q j - u) / N := by rw [hu]; field_simp
        _ ≤ (m - 1) / N := by
          apply div_le_div_of_nonneg_right _ hNR.le
          have h1 : cellRight q j - cellLeft q j = m - 1 := by
            unfold cellLeft cellRight
            ring
          linarith [hj.1]
        _ < η := hm1N
    have hφ := hη q (cellEnd N q j) t hclose
    have hmono : (φ q : C(I, ℝ)) t ≤ endValue φ N q j := (φ q).monotone hend
    have hl1 := endValue_le_levels φ N hM q j
    have hl2 := levels_lt φ N hM q j
    have hl3 := hMε' j (Nat.le_succ_of_le hjN)
    unfold endValue at hl1 hl2 hmono
    rw [abs_lt] at hφ ⊢
    constructor <;> linarith

/-- **The approximant tuple is within `ε` of `φ`** in the sup metric on tuples, under the same
hypotheses. Stated for `m = 2n + 1` ranks, where the tuple type is `InnerTuple n`. -/
theorem dist_approximant_lt {n : ℕ} (φ : InnerTuple n) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {ε η : ℝ} (hε : 0 < ε)
    (hη : ∀ q (s t : I), |(s : ℝ) - t| < η →
      |(φ q : C(I, ℝ)) s - (φ q : C(I, ℝ)) t| < ε / 4)
    (hNη : ((2 * n + 1 : ℕ) : ℝ) / N < η) (hMε : ((2 * n + 1 : ℕ) : ℝ) * (N + 2) / M ≤ ε / 4) :
    dist (fun q => approximant φ N hM q : InnerTuple n) φ < ε := by
  rw [dist_pi_lt_iff hε]
  intro q
  rw [Subtype.dist_eq, ContinuousMap.dist_lt_iff hε]
  intro t
  rw [Real.dist_eq]
  exact lt_trans (abs_approximant_sub_lt φ hN hM hη hNη hMε q t) (by linarith)

end

end MiscMath.Analysis.KolmogorovArnold
