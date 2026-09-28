/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic

/-!
# The red-blue pebble game: the function `d · log₂ (2d)`

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

`bfly d = d · log₂ (2d)` bounds the number of vertices of the FFT graph that `d` vertices can
dominate (`Butterfly.lean`). It sharpens Hong and Kung's `2d log d`, which they claim for `d ≥ 2`
and which is `0` at `d = 1`, where a single vertex dominates itself, although their induction
applies it there; `bfly 1 = 1`. This file proves the inequalities that induction needs, the step
being `bfly_combine`, from `log₂ (1 + t) ≥ t` on `[0, 1]`, which is concavity of `log` (the
paper's lemma `H(p) ≥ 2p` on `[0, ½]` in another form).
-/

@[expose] public section

namespace MiscMath.Computability.RedBluePebbleGame

/-- The butterfly bound `d · log₂ (2d)`; its value at `d = 0` is `0`. -/
noncomputable def bfly (d : ℕ) : ℝ := d * Real.logb 2 (2 * d)

/-- `t ≤ log₂ (1 + t)` on `[0, 1]`, by concavity of `log` between `1` and `2`. -/
private lemma le_logb_two_one_add {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ≤ Real.logb 2 (1 + t) := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (0 : ℝ) ≤ 1 - t by linarith) h0
    (show 1 - t + t = 1 by ring)
  have e : (1 - t) • (1 : ℝ) + t • (2 : ℝ) = 1 + t := by
    simp only [smul_eq_mul]
    ring
  rw [e] at h
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  rw [Real.logb, le_div_iff₀ hL]
  exact h

/-- Fact (1): `bfly x + c ≤ bfly (x + c)`. -/
private lemma bfly_add_le (x c : ℕ) : bfly x + (c : ℝ) ≤ bfly (x + c) := by
  unfold bfly
  push_cast
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have h1 : (x : ℝ) * Real.logb 2 (2 * x) ≤ x * Real.logb 2 (2 * (x + c)) := by
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      simp
    · apply mul_le_mul_of_nonneg_left _ hx0
      have : (0 : ℝ) < x := by exact_mod_cast hx
      exact Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have h2 : (c : ℝ) ≤ c * Real.logb 2 (2 * (x + c)) := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp
    · have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
      have h3 : (1 : ℝ) ≤ Real.logb 2 (2 * (x + c)) := by
        calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one one_lt_two).symm
          _ ≤ Real.logb 2 (2 * (x + c)) :=
            Real.logb_le_logb_of_le one_lt_two (by norm_num) (by linarith)
      nlinarith
  linarith

/-- Fact (2): for `a ≤ b`, `bfly a + bfly b + 2a ≤ bfly (a + b)`. -/
private lemma bfly_pair_le {a b : ℕ} (hab : a ≤ b) :
    bfly a + bfly b + 2 * (a : ℝ) ≤ bfly (a + b) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp [bfly]
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    unfold bfly
    push_cast
    have hA : (0 : ℝ) < a := by exact_mod_cast ha
    have hB : (0 : ℝ) < b := by exact_mod_cast hb
    have hBne : (b : ℝ) ≠ 0 := hB.ne'
    have hAB : (a : ℝ) ≤ b := by exact_mod_cast hab
    have h2A : Real.logb 2 (2 * ((a : ℝ) + b)) = 1 + Real.logb 2 ((a : ℝ) + b) := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one one_lt_two]
    have hmono : Real.logb 2 (2 * (a : ℝ)) ≤ Real.logb 2 ((a : ℝ) + b) :=
      Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
    have k1 : (a : ℝ) * Real.logb 2 (2 * a) + a ≤ a * Real.logb 2 (2 * (a + b)) := by
      rw [h2A]
      have := mul_le_mul_of_nonneg_left hmono hA.le
      linarith
    have ht0 : (0 : ℝ) ≤ (a : ℝ) / b := div_nonneg hA.le hB.le
    have ht1 : (a : ℝ) / b ≤ 1 := (div_le_one₀ hB).mpr hAB
    have hsplit : Real.logb 2 (2 * ((a : ℝ) + b)) =
        Real.logb 2 (2 * (b : ℝ)) + Real.logb 2 (1 + (a : ℝ) / b) := by
      rw [← Real.logb_mul (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    have hlog := le_logb_two_one_add ht0 ht1
    have k2 : (b : ℝ) * Real.logb 2 (2 * b) + a ≤ b * Real.logb 2 (2 * (a + b)) := by
      rw [hsplit]
      have e : (b : ℝ) * ((a : ℝ) / b) = a := by field_simp
      have := mul_le_mul_of_nonneg_left hlog hB.le
      linarith
    linarith

theorem bfly_zero : bfly 0 = 0 := by
  simp [bfly]

theorem bfly_one : bfly 1 = 1 := by
  simp [bfly, Real.logb_self_eq_one]

theorem bfly_nonneg (d : ℕ) : 0 ≤ bfly d := by
  unfold bfly
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · apply mul_nonneg (Nat.cast_nonneg d)
    apply Real.logb_nonneg one_lt_two
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith

theorem bfly_mono {a b : ℕ} (h : a ≤ b) : bfly a ≤ bfly b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := bfly_add_le a k
  have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The step of the butterfly induction. -/
theorem bfly_combine (a b c : ℕ) :
    bfly a + bfly b + (c : ℝ) + 2 * ((min a b : ℕ) : ℝ) ≤ bfly (a + b + c) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    have h1 := bfly_pair_le hab
    have h2 := bfly_add_le (a + b) c
    linarith
  · rw [min_eq_right hab]
    have h1 := bfly_pair_le hab
    have h2 := bfly_add_le (a + b) c
    rw [Nat.add_comm b a] at h1
    linarith

theorem bfly_two_mul (S : ℕ) : bfly (2 * S) = 2 * S * Real.logb 2 (4 * S) := by
  unfold bfly
  push_cast
  rw [show (2 : ℝ) * (2 * (S : ℝ)) = 4 * S by ring]

end MiscMath.Computability.RedBluePebbleGame
