/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.Cells
import MiscMath.Analysis.KolmogorovArnold.InnerSpace

/-!
# Staircase functions

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; part of the density argument (Layer 2 of the development). Its
declarations are proof: machine-generated, kernel-checked and axiom-audited, and may be read by
no one.

The approximating inner functions of Hedberg's Lemma 2 (his property a)) are constant on each
cell of their rank and vary only across the gaps. Rather than define such a function piecewise,
it is written as a finite sum of clamped ramps,

  `stair q c J u = c 0 + ∑_{j < J} (c (j+1) - c j) · clamp01 (u - (q + m j))`,

where `clamp01 v = max 0 (min 1 v)` and `c : ℕ → ℝ` is the sequence of levels. Each ramp is `0`
up to the right endpoint of cell `j` and `1` from the left endpoint of cell `j + 1`, so on cell
`j` (for `j ≤ J`) the sum telescopes to `c j` (`stair_eq_of_mem_cell`), and across the gap
after cell `j` the value moves monotonically from `c j` to `c (j+1)` (`stair_mem_Icc_of_gap`).
Continuity and monotonicity (for monotone levels) are each one Mathlib lemma about finite sums
of continuous, respectively monotone, functions with non-negative coefficients — the reason for
this form over an `Int.floor`-based case split. `stairInner` packages `t ↦ stair q c J (N t)`
as an element of the inner-function space `Inner`.
-/

open Finset unitInterval

namespace MiscMath.Analysis.KolmogorovArnold

/-- The clamp of a real to `[0, 1]`: `max 0 (min 1 v)`. -/
def clamp01 (v : ℝ) : ℝ := max 0 (min 1 v)

theorem clamp01_of_nonpos {v : ℝ} (h : v ≤ 0) : clamp01 v = 0 := by
  unfold clamp01
  rw [min_eq_right (h.trans zero_le_one), max_eq_left h]

theorem clamp01_of_one_le {v : ℝ} (h : 1 ≤ v) : clamp01 v = 1 := by
  unfold clamp01
  rw [min_eq_left h, max_eq_right zero_le_one]

theorem clamp01_nonneg (v : ℝ) : 0 ≤ clamp01 v := le_max_left _ _

theorem clamp01_le_one (v : ℝ) : clamp01 v ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem monotone_clamp01 : Monotone clamp01 := fun _ _ h =>
  max_le_max le_rfl (min_le_min le_rfl h)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

variable {m : ℕ}

/-- The staircase of rank `q` with levels `c` and `J` ramps: constant `c j` on the cell of index
`j ≤ J`, moving from `c j` to `c (j + 1)` across the gap after it. -/
def stair (q : Fin m) (c : ℕ → ℝ) (J : ℕ) (u : ℝ) : ℝ :=
  c 0 + ∑ j ∈ range J, (c (j + 1) - c j) * clamp01 (u - cellRight q j)

theorem continuous_stair (q : Fin m) (c : ℕ → ℝ) (J : ℕ) : Continuous (stair q c J) := by
  unfold stair
  refine continuous_const.add (continuous_finsetSum _ fun j _ => continuous_const.mul ?_)
  exact continuous_clamp01.comp (continuous_id.sub continuous_const)

theorem monotone_stair (q : Fin m) {c : ℕ → ℝ} (hc : Monotone c) (J : ℕ) :
    Monotone (stair q c J) := by
  intro a b hab
  unfold stair
  refine add_le_add le_rfl (sum_le_sum fun j _ => ?_)
  exact mul_le_mul_of_nonneg_left (monotone_clamp01 (sub_le_sub_right hab _))
    (sub_nonneg.mpr (hc (Nat.le_succ j)))

/-- On the cell of index `j ≤ J`, the staircase takes the value `c j`. -/
theorem stair_eq_of_mem_cell (q : Fin m) (c : ℕ → ℝ) {J j : ℕ} (hj : j ≤ J) {u : ℝ}
    (hu : u ∈ cell q j) : stair q c J u = c j := by
  unfold stair
  rw [← sum_range_add_sum_Ico _ hj]
  have h1 : ∑ j' ∈ range j, (c (j' + 1) - c j') * clamp01 (u - cellRight q j') =
      ∑ j' ∈ range j, (c (j' + 1) - c j') := by
    refine sum_congr rfl fun j' hj' => ?_
    have := cellRight_add_one_le_cellLeft (q := q) (mem_range.mp hj')
    rw [clamp01_of_one_le (by linarith [hu.1]), mul_one]
  have h2 : ∑ j' ∈ Ico j J, (c (j' + 1) - c j') * clamp01 (u - cellRight q j') = 0 := by
    refine sum_eq_zero fun j' hj' => ?_
    have := cellRight_mono q (mem_Ico.mp hj').1
    rw [clamp01_of_nonpos (by linarith [hu.2]), mul_zero]
  rw [h1, h2, sum_range_sub, add_zero]
  ring

/-- Across the gap after the cell of index `j` (with `j + 1 ≤ J`), the staircase lies between
`c j` and `c (j + 1)`. -/
theorem stair_mem_Icc_of_gap (q : Fin m) {c : ℕ → ℝ} (hc : Monotone c) {J j : ℕ} (hj : j + 1 ≤ J)
    {u : ℝ} (h1 : cellRight q j ≤ u) (h2 : u ≤ cellRight q j + 1) :
    stair q c J u ∈ Set.Icc (c j) (c (j + 1)) := by
  constructor
  · rw [← stair_eq_of_mem_cell q c (Nat.le_of_succ_le hj) (cellRight_mem_cell q j)]
    exact monotone_stair q hc J h1
  · rw [← stair_eq_of_mem_cell q c hj (cellRight_add_one_mem_cell q j)]
    exact monotone_stair q hc J h2

/-- The staircase rescaled to `I`: `t ↦ stair q c J (N t)`, as an inner function. -/
def stairInner (N : ℕ) (q : Fin m) {c : ℕ → ℝ} (hc : Monotone c) (J : ℕ) : Inner :=
  ⟨⟨fun t => stair q c J (N * t),
    (continuous_stair q c J).comp (continuous_const.mul continuous_subtype_val)⟩,
   fun _ _ hab => monotone_stair q hc J
    (mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hab) (Nat.cast_nonneg N))⟩

@[simp] theorem stairInner_apply (N : ℕ) (q : Fin m) {c : ℕ → ℝ} (hc : Monotone c) (J : ℕ)
    (t : I) : (stairInner N q hc J : C(I, ℝ)) t = stair q c J (N * t) := rfl

end MiscMath.Analysis.KolmogorovArnold
