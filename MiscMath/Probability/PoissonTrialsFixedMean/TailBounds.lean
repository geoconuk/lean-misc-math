/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/

import MiscMath.Probability.PoissonTrialsFixedMean.ExtremalShapes
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Hoeffding's Theorem 4, in its two extreme regimes

Part of `MiscMath.Probability.PoissonTrialsFixedMean`, whose module docstring states the
result, its source and — importantly here — the scope of what is and is not claimed, and
where the reader should start. This file proves the two extreme regimes of Theorem 4, the
trivial bounds and the complement duality that accompany them, the attainment of all four
bounds, and the size of the regime that is left out.
-/

namespace MiscMath.Probability

open Finset

/-! ## Theorem 4: the tail against the binomial, away from the mean

If the mean number of successes is `lam`, then `k ≥ lam ⟹ P[S ≤ k] ≥ B(k; n, lam/n)` and
`k ≤ lam - 1 ⟹ P[S ≤ k] ≤ B(k; n, lam/n)`, with `n` the number of trials. So among all trial
vectors with the given mean, the homogeneous one has the *lightest* lower tail at thresholds
`k ≥ lam` and the *heaviest* at thresholds `k ≤ lam - 1`. The second regime is `k ≤ lam - 1`
and not `k < lam`; `thm4_lower_needs_le_sub_one` shows the difference is real.

**The idea in one line.** Corollary 2.1 reduces the theorem to the extremal shapes — `a`
coordinates at `1`, `b` at `0`, `r` at a common `x` — and there both halves are the same
statement about **one potential**. With `m + 1` trials, threshold `k` and mean `lam`,

    Φ(t) = B(k; m+1, t) + (m+1)·(t - lam/(m+1))·C(m,k)·t^k·(1-t)^(m-k),

so that `Φ(lam/(m+1))` is the binomial itself, `Φ(lam/m)` is the drop-a-zero comparator and
`Φ((lam-1)/m)` is the drop-a-one comparator: three points of one curve. And

    Φ'(t) = (m+1)·C(m,k)·(t - lam/(m+1))·h'(t),   h(t) = t^k (1-t)^(m-k),

because `C(m,k)·h` is *exactly* minus the derivative of the binomial tail
(`hasDerivAt_binTail`), so the two unbracketed terms cancel. The whole of Theorem 4 is
therefore the sign of `h'`, which changes once, at `m·t = k`; every hypothesis of the four
families below is exactly what puts the relevant interval on one side of that.

**The four families are stated at `m + 1` trials and, where a threshold drops, at `k + 1`**,
so that no `ℕ`-subtraction appears in them. That is not cosmetic: written with `k - 1`, the
drop-a-one family of the *upper* half is **false at `k = 0`**, where the truncation turns the
empty tail into the full one, and it then needs a `1 ≤ k` guard. Stated at `k + 1` the
offending cell cannot be expressed, so no guard is needed. -/

section Recursion

lemma binTail_succ_zero (m : ℕ) (P : ℝ) :
    binTail (m + 1) P 0 = (1 - P) * binTail m P 0 := by
  simp [binTail, pow_succ]
  ring

/-- **Conditioning on one trial**, read off `bernExp_insert`. -/
lemma binTail_succ_recursion (m k : ℕ) (P : ℝ) :
    binTail (m + 1) P (k + 1) = (1 - P) * binTail m P (k + 1) + P * binTail m P k := by
  have hnot : m ∉ range m := by simp
  have h := bernExp_insert (t := range m) (i := m) hnot
    (fun _ : ℕ => P) (fun r => if r ≤ k + 1 then (1 : ℝ) else 0)
  rw [← Finset.range_add_one] at h
  have hg : (fun r : ℕ => (if r + 1 ≤ k + 1 then (1 : ℝ) else 0))
      = fun r : ℕ => (if r ≤ k then (1 : ℝ) else 0) := by
    funext r
    by_cases hr : r ≤ k <;> simp [hr]
  rw [hg] at h
  have e1 : tailLe (range (m + 1)) (fun _ : ℕ => P) (k + 1) = binTail (m + 1) P (k + 1) := by
    rw [tailLe_const, Finset.card_range]
  have e2 : tailLe (range m) (fun _ : ℕ => P) (k + 1) = binTail m P (k + 1) := by
    rw [tailLe_const, Finset.card_range]
  have e3 : tailLe (range m) (fun _ : ℕ => P) k = binTail m P k := by
    rw [tailLe_const, Finset.card_range]
  rw [← e1, ← e2, ← e3]
  simpa only [tailLe] using h

/-- **The one-trial identity in the form the potential wants**:
`B(k; m+1, P) = B(k; m, P) - P·C(m,k)·h_{k,m}(P)`. -/
lemma binTail_succ (m k : ℕ) (P : ℝ) :
    binTail (m + 1) P k = binTail m P k - P * ((m.choose k : ℝ) * binShape k m P) := by
  cases k with
  | zero =>
      rw [binTail_succ_zero]
      simp only [binShape, Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero]
      rw [binTail]
      simp
      ring
  | succ j =>
      rw [binTail_succ_recursion]
      have h := binTail_succ_term m j P
      linear_combination (-P) * h

end Recursion

section Potential

/-- **The potential.** `lam` is the mean, `m + 1` the number of trials, `k` the
threshold. The added term vanishes at `t = lam/(m+1)` and is engineered so that
the derivative of the tail cancels against it. -/
noncomputable def binPot (m k : ℕ) (lam t : ℝ) : ℝ :=
  binTail (m + 1) t k
    + ((m : ℝ) + 1) * (t - lam / ((m : ℝ) + 1)) * ((m.choose k : ℝ) * binShape k m t)

/-- Its derivative: one product, one sign. -/
noncomputable def binPotD (m k : ℕ) (lam t : ℝ) : ℝ :=
  ((m : ℝ) + 1) * (t - lam / ((m : ℝ) + 1)) * ((m.choose k : ℝ) * binShapeD k m t)

lemma hasDerivAt_binPot (m k : ℕ) (lam t : ℝ) :
    HasDerivAt (binPot m k lam) (binPotD m k lam t) t := by
  have hA : HasDerivAt (fun p : ℝ => binTail (m + 1) p k)
      (-(((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t))) t := hasDerivAt_binTail m k t
  have hB : HasDerivAt (fun p : ℝ => ((m : ℝ) + 1) * (p - lam / ((m : ℝ) + 1)))
      ((m : ℝ) + 1) t := by
    simpa using (((hasDerivAt_id t).sub_const (lam / ((m : ℝ) + 1))).const_mul ((m : ℝ) + 1))
  have hC : HasDerivAt (fun p : ℝ => ((m.choose k : ℝ) * binShape k m p))
      ((m.choose k : ℝ) * binShapeD k m t) t := (hasDerivAt_binShape k m t).const_mul _
  have hval : -(((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t))
      + (((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t)
        + ((m : ℝ) + 1) * (t - lam / ((m : ℝ) + 1)) * ((m.choose k : ℝ) * binShapeD k m t))
      = binPotD m k lam t := by
    simp only [binPotD]; ring
  rw [← hval]
  exact hA.add (hB.mul hC)

/-- At the mean the potential **is** the binomial tail. -/
lemma binPot_at_mean (m k : ℕ) (lam : ℝ) :
    binPot m k lam (lam / ((m : ℝ) + 1)) = binTail (m + 1) (lam / ((m : ℝ) + 1)) k := by
  simp [binPot]

/-- At `lam/m` the potential is the **drop-a-zero** comparator. -/
lemma binPot_at_dropZero {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (lam : ℝ) :
    binPot m k lam (lam / (m : ℝ)) = binTail m (lam / (m : ℝ)) k := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcoef : ((m : ℝ) + 1) * (lam / (m : ℝ) - lam / ((m : ℝ) + 1)) = lam / (m : ℝ) := by
    field_simp
    ring
  rw [binPot, hcoef, binTail_succ]
  ring

/-- At `(lam-1)/m` the potential is the **drop-a-one** comparator, one threshold
lower. Stated at `k + 1`, so no `ℕ`-subtraction appears. -/
lemma binPot_at_dropOne {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (lam : ℝ) :
    binPot m (k + 1) lam ((lam - 1) / (m : ℝ)) = binTail m ((lam - 1) / (m : ℝ)) k := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcoef : ((m : ℝ) + 1) * ((lam - 1) / (m : ℝ) - lam / ((m : ℝ) + 1))
      = (lam - 1) / (m : ℝ) - 1 := by
    field_simp
    ring
  rw [binPot, hcoef, binTail_succ, binTail_succ_term m k]
  ring

end Potential

/-! ### The sign of `h'`, on the OPEN interval

The closed-interval form of `binShapeD_nonpos` would be **false**: at `t = 1`, `k = m` the
hypothesis `k ≤ m·t` holds while `C(m,m)·h'(1) = m > 0`. Both endpoints are excluded here,
and `monotoneOn_of_deriv_nonneg` asks for the sign on `interior` only, so nothing is lost. -/

section Sign

lemma binShapeD_nonneg {k m : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hmt : (m : ℝ) * t ≤ (k : ℝ)) : 0 ≤ (m.choose k : ℝ) * binShapeD k m t := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hm : m = 0 := by
      by_contra h
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      simp only [Nat.cast_zero] at hmt
      nlinarith
    subst hm
    simp [binShapeD]
  · rcases Nat.lt_or_ge k m with hkm | hmk
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, m = i + 1 + j + 1 := ⟨m - (i + 1) - 1, by omega⟩
      have e1 : i + 1 + j + 1 - (i + 1) = j + 1 := by omega
      simp only [binShapeD, e1]
      have hfac : ((i : ℝ) + 1) * t ^ i * (1 - t) ^ (j + 1)
            - ((j : ℝ) + 1) * t ^ (i + 1) * (1 - t) ^ j
          = t ^ i * (1 - t) ^ j * (((i : ℝ) + 1) - ((i : ℝ) + 1 + (j : ℝ) + 1) * t) := by
        ring
      have hbr : (0 : ℝ) ≤ ((i : ℝ) + 1) - ((i : ℝ) + 1 + (j : ℝ) + 1) * t := by
        push_cast at hmt
        linarith
      have hpos : (0 : ℝ) ≤ t ^ i * (1 - t) ^ j :=
        mul_nonneg (pow_nonneg ht0.le _) (pow_nonneg (by linarith) _)
      push_cast
      rw [hfac]
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hpos hbr)
    · have e1 : m - k = 0 := by omega
      simp only [binShapeD, e1, Nat.cast_zero, zero_mul, sub_zero, pow_zero, mul_one, Nat.zero_sub]
      have : (0 : ℝ) ≤ (k : ℝ) * t ^ (k - 1) :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht0.le _)
      exact mul_nonneg (Nat.cast_nonneg _) this

lemma binShapeD_nonpos {k m : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hmt : (k : ℝ) ≤ (m : ℝ) * t) : (m.choose k : ℝ) * binShapeD k m t ≤ 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hk : k = 0 := by
      by_contra h
      have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      simp only [Nat.cast_zero, zero_mul] at hmt
      linarith
    subst hk
    simp [binShapeD]
  · have hkm : k < m := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have : (k : ℝ) < (m : ℝ) := by nlinarith
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      simp only [binShapeD, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.cast_zero,
        zero_mul, zero_sub, pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel]
      have : (0 : ℝ) ≤ ((j : ℝ) + 1) * (1 - t) ^ j :=
        mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
      push_cast
      linarith
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, m = i + 1 + j + 1 := ⟨m - (i + 1) - 1, by omega⟩
      have e1 : i + 1 + j + 1 - (i + 1) = j + 1 := by omega
      simp only [binShapeD, e1]
      have hfac : ((i : ℝ) + 1) * t ^ i * (1 - t) ^ (j + 1)
            - ((j : ℝ) + 1) * t ^ (i + 1) * (1 - t) ^ j
          = t ^ i * (1 - t) ^ j * (((i : ℝ) + 1) - ((i : ℝ) + 1 + (j : ℝ) + 1) * t) := by
        ring
      have hbr : ((i : ℝ) + 1) - ((i : ℝ) + 1 + (j : ℝ) + 1) * t ≤ 0 := by
        push_cast at hmt
        linarith
      have hpos : (0 : ℝ) ≤ t ^ i * (1 - t) ^ j :=
        mul_nonneg (pow_nonneg ht0.le _) (pow_nonneg (by linarith) _)
      push_cast
      rw [hfac]
      have : t ^ i * (1 - t) ^ j * (((i : ℝ) + 1) - ((i : ℝ) + 1 + (j : ℝ) + 1) * t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpos hbr
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) this

end Sign

section Monotone

lemma binPot_differentiable (m k : ℕ) (lam : ℝ) : Differentiable ℝ (binPot m k lam) :=
  fun t => (hasDerivAt_binPot m k lam t).differentiableAt

lemma binPot_mono {m k : ℕ} {lam a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Set.Ioo a b, 0 ≤ binPotD m k lam t) :
    binPot m k lam a ≤ binPot m k lam b := by
  have hdiff := binPot_differentiable m k lam
  have hmono : MonotoneOn (binPot m k lam) (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hdiff.continuous.continuousOn
      hdiff.differentiableOn (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(hasDerivAt_binPot m k lam t).deriv]
        exact hd t ht)
  exact hmono (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab

lemma binPot_anti {m k : ℕ} {lam a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Set.Ioo a b, binPotD m k lam t ≤ 0) :
    binPot m k lam b ≤ binPot m k lam a := by
  have hdiff := binPot_differentiable m k lam
  have hanti : AntitoneOn (binPot m k lam) (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hdiff.continuous.continuousOn
      hdiff.differentiableOn (by
        intro t ht
        rw [interior_Icc] at ht
        rw [(hasDerivAt_binPot m k lam t).deriv]
        exact hd t ht)
  exact hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab

end Monotone

/-! ### The four one-parameter families

Each is a comparison of two binomial tails **at matched means**, one with a coordinate
dropped: `lam/(m+1)` against `lam/m` (a coordinate pinned at `0`) or against `(lam-1)/m` (a
coordinate pinned at `1`). -/

section Families

/-- **Drop a zero, above the mean.** At a fixed mean the lower tail is
nonincreasing in the number of trials, for `k ≥ lam`. -/
theorem binTail_succ_le_binTail_dropZero {m : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (hlam : lam ≤ (m : ℝ))
    {k : ℕ} (hk : lam ≤ (k : ℝ)) :
    binTail (m + 1) (lam / ((m : ℝ) + 1)) k ≤ binTail m (lam / (m : ℝ)) k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hz : lam = 0 := by simp only [Nat.cast_zero] at hlam; linarith
    subst hz
    simp only [Nat.cast_zero, zero_add, zero_div]
    rw [binTail_zero_prob, binTail_zero_prob]
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hab : lam / ((m : ℝ) + 1) ≤ lam / (m : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hm0]
      nlinarith
    have hb1 : lam / (m : ℝ) ≤ 1 := (div_le_one hm0).mpr hlam
    have ha0 : 0 ≤ lam / ((m : ℝ) + 1) := div_nonneg h0 (by linarith)
    rw [← binPot_at_mean m k lam, ← binPot_at_dropZero hm k lam]
    refine binPot_mono hab fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := ht
    have htpos : 0 < t := lt_of_le_of_lt ha0 ht1
    have htlt : t < 1 := lt_of_lt_of_le ht2 hb1
    have hmt : (m : ℝ) * t ≤ (k : ℝ) := by
      have : (m : ℝ) * t ≤ (m : ℝ) * (lam / (m : ℝ)) := by nlinarith
      rw [mul_div_cancel₀ _ (ne_of_gt hm0)] at this
      linarith
    have hsign := binShapeD_nonneg (k := k) (m := m) htpos htlt hmt
    have hshift : 0 ≤ t - lam / ((m : ℝ) + 1) := by linarith
    exact mul_nonneg (mul_nonneg (by linarith) hshift) hsign

/-- **Drop a one, above the mean.** One fewer trial, one lower threshold, one
less mean. -/
theorem binTail_succ_le_binTail_dropOne {m : ℕ} {lam : ℝ} (h1 : 1 ≤ lam)
    (hlam : lam ≤ (m : ℝ) + 1) {k : ℕ} (hk : lam ≤ (k : ℝ) + 1) :
    binTail (m + 1) (lam / ((m : ℝ) + 1)) (k + 1) ≤ binTail m ((lam - 1) / (m : ℝ)) k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hz : lam = 1 := by simp only [Nat.cast_zero] at hlam; linarith
    subst hz
    simp only [Nat.cast_zero, zero_add, div_one, sub_self, zero_div]
    rw [binTail_zero_prob, binTail_eq_one (1 : ℝ) (by omega)]
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hab : (lam - 1) / (m : ℝ) ≤ lam / ((m : ℝ) + 1) := by
      rw [div_le_div_iff₀ hm0 (by linarith)]
      nlinarith
    have ha0 : 0 ≤ (lam - 1) / (m : ℝ) := div_nonneg (by linarith) hm0.le
    have hb1 : lam / ((m : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    rw [← binPot_at_mean m (k + 1) lam, ← binPot_at_dropOne hm k lam]
    refine binPot_anti hab fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := ht
    have htpos : 0 < t := lt_of_le_of_lt ha0 ht1
    have htlt : t < 1 := lt_of_lt_of_le ht2 hb1
    have hmt : (m : ℝ) * t ≤ ((k : ℝ) + 1) := by
      have hstep : (m : ℝ) * t ≤ (m : ℝ) * (lam / ((m : ℝ) + 1)) := by nlinarith
      have hle : (m : ℝ) * (lam / ((m : ℝ) + 1)) ≤ lam := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    have hsign := binShapeD_nonneg (k := k + 1) (m := m) htpos htlt (by push_cast; linarith)
    have hshift : t - lam / ((m : ℝ) + 1) ≤ 0 := by linarith
    have : ((m : ℝ) + 1) * (t - lam / ((m : ℝ) + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hshift
    exact mul_nonpos_of_nonpos_of_nonneg this hsign

/-- **Drop a zero, below the mean** — the mirror of
`binTail_succ_le_binTail_dropZero`. The hypothesis `0 ≤ lam` of the mirror is
not needed here: `(k : ℝ) ≤ lam - 1` with `k : ℕ` already forces `lam ≥ 1`. -/
theorem binTail_dropZero_le_binTail_succ {m : ℕ} {lam : ℝ} (hlam : lam ≤ (m : ℝ))
    {k : ℕ} (hk : (k : ℝ) ≤ lam - 1) :
    binTail m (lam / (m : ℝ)) k ≤ binTail (m + 1) (lam / ((m : ℝ) + 1)) k := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h0 : (0 : ℝ) ≤ lam := by linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero] at hlam; linarith
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hab : lam / ((m : ℝ) + 1) ≤ lam / (m : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hm0]
      nlinarith
    have hb1 : lam / (m : ℝ) ≤ 1 := (div_le_one hm0).mpr hlam
    have ha0 : 0 ≤ lam / ((m : ℝ) + 1) := div_nonneg h0 (by linarith)
    rw [← binPot_at_mean m k lam, ← binPot_at_dropZero hm k lam]
    refine binPot_anti hab fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := ht
    have htpos : 0 < t := lt_of_le_of_lt ha0 ht1
    have htlt : t < 1 := lt_of_lt_of_le ht2 hb1
    have hmt : (k : ℝ) ≤ (m : ℝ) * t := by
      have hstep : (m : ℝ) * (lam / ((m : ℝ) + 1)) ≤ (m : ℝ) * t := by nlinarith
      have hge : lam - 1 ≤ (m : ℝ) * (lam / ((m : ℝ) + 1)) := by
        rw [mul_div_assoc', le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hsign := binShapeD_nonpos (k := k) (m := m) htpos htlt hmt
    have hshift : 0 ≤ t - lam / ((m : ℝ) + 1) := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hshift) hsign

/-- **Drop a one, below the mean** — the mirror of
`binTail_succ_le_binTail_dropOne`. Stated at threshold `k + 1`, which is where
the `1 ≤ k` guard of the `k - 1` phrasing went. -/
theorem binTail_dropOne_le_binTail_succ {m : ℕ} {lam : ℝ} (hlam : lam ≤ (m : ℝ) + 1)
    {k : ℕ} (hk : (k : ℝ) + 1 ≤ lam - 1) :
    binTail m ((lam - 1) / (m : ℝ)) k ≤ binTail (m + 1) (lam / ((m : ℝ) + 1)) (k + 1) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (1 : ℝ) ≤ lam := by linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero] at hlam; linarith
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hab : (lam - 1) / (m : ℝ) ≤ lam / ((m : ℝ) + 1) := by
      rw [div_le_div_iff₀ hm0 (by linarith)]
      nlinarith
    have ha0 : 0 ≤ (lam - 1) / (m : ℝ) := div_nonneg (by linarith) hm0.le
    have hb1 : lam / ((m : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    rw [← binPot_at_mean m (k + 1) lam, ← binPot_at_dropOne hm k lam]
    refine binPot_mono hab fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := ht
    have htpos : 0 < t := lt_of_le_of_lt ha0 ht1
    have htlt : t < 1 := lt_of_lt_of_le ht2 hb1
    have hmt : ((k : ℝ) + 1) ≤ (m : ℝ) * t := by
      have hstep : (m : ℝ) * ((lam - 1) / (m : ℝ)) ≤ (m : ℝ) * t := by nlinarith
      rw [mul_div_cancel₀ _ (ne_of_gt hm0)] at hstep
      linarith
    have hsign := binShapeD_nonpos (k := k + 1) (m := m) htpos htlt (by push_cast; linarith)
    have hshift : t - lam / ((m : ℝ) + 1) ≤ 0 := by linarith
    have hneg : ((m : ℝ) + 1) * (t - lam / ((m : ℝ) + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hshift
    change (0 : ℝ) ≤ ((m : ℝ) + 1) * (t - lam / ((m : ℝ) + 1))
        * ((m.choose (k + 1) : ℝ) * binShapeD (k + 1) m t)
    rw [← neg_mul_neg]
    exact mul_nonneg (neg_nonneg.mpr hneg) (neg_nonneg.mpr hsign)

end Families

/-! ### The pure-binomial residue

With Corollary 2.1 discharging the extremal structure, what is left of Theorem 4 is a
statement about `binTail` alone: `a` coordinates at `1`, `r` at `x`, the remaining
`n - a - r` at `0`, so the mean is `lam = a + r·x`. It follows from the four families by
induction on `n`, dropping one coordinate at a time. -/

section Residue

/-- **The residue, above the mean.** -/
theorem binTail_shape_le : ∀ (n a r : ℕ) (x : ℝ), a + r ≤ n → 0 ≤ x → x ≤ 1 →
    ∀ k : ℕ, ((a : ℝ) + r * x) ≤ (k : ℝ) →
      binTail n (((a : ℝ) + r * x) / (n : ℝ)) k ≤ binTail r x (k - a) := by
  intro n
  induction n with
  | zero =>
      intro a r x har _ _ k _
      have ha : a = 0 := by omega
      have hr : r = 0 := by omega
      subst ha; subst hr
      rw [binTail_eq_one _ (Nat.zero_le k), binTail_eq_one _ (Nat.zero_le _)]
  | succ m ih =>
      intro a r x har hx0 hx1 k hk
      have hrx : (0 : ℝ) ≤ (r : ℝ) * x := mul_nonneg (Nat.cast_nonneg r) hx0
      have hn1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hak : a ≤ k := by
        have : (a : ℝ) ≤ (k : ℝ) := by linarith
        exact_mod_cast this
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · by_cases hb : r ≤ m
        · have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hb
          have hlam : ((0 : ℕ) : ℝ) + (r : ℝ) * x ≤ (m : ℝ) := by
            have : (r : ℝ) * x ≤ (r : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
            push_cast
            linarith
          have h1 := binTail_succ_le_binTail_dropZero (m := m)
            (lam := ((0 : ℕ) : ℝ) + (r : ℝ) * x) (by push_cast; linarith) hlam (k := k) hk
          have h2 := ih 0 r x (by omega) hx0 hx1 k hk
          rw [hn1]
          exact le_trans h1 h2
        · have hrn : r = m + 1 := by omega
          subst hrn
          have hr0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by
            rw [hn1]; positivity
          have hmean : (((0 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) * x) / ((m + 1 : ℕ) : ℝ) = x := by
            rw [Nat.cast_zero, zero_add, mul_comm, mul_div_assoc, div_self hr0, mul_one]
          rw [hmean, Nat.sub_zero]
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hlamn : ((a' + 1 : ℕ) : ℝ) + (r : ℝ) * x ≤ (m : ℝ) + 1 := by
          have hrx' : (r : ℝ) * x ≤ (r : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
          have : ((a' + 1 : ℕ) : ℝ) + (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast har
          rw [hn1] at this
          linarith
        have hlam1 : (1 : ℝ) ≤ ((a' + 1 : ℕ) : ℝ) + (r : ℝ) * x := by
          have hone : (1 : ℝ) ≤ ((a' + 1 : ℕ) : ℝ) := by
            push_cast
            linarith [Nat.cast_nonneg (α := ℝ) a']
          linarith
        have h1 := binTail_succ_le_binTail_dropOne (m := m)
          (lam := ((a' + 1 : ℕ) : ℝ) + (r : ℝ) * x) hlam1 hlamn (k := k')
          (by push_cast at hk ⊢; linarith)
        have hcast : ((a' : ℕ) : ℝ) + (r : ℝ) * x
            = (((a' + 1 : ℕ) : ℝ) + (r : ℝ) * x) - 1 := by push_cast; ring
        have h2 := ih a' r x (by omega) hx0 hx1 k' (by rw [hcast]; push_cast at hk ⊢; linarith)
        rw [hcast] at h2
        have hidx : k' + 1 - (a' + 1) = k' - a' := by omega
        rw [hn1, hidx]
        exact le_trans h1 h2

/-- **The residue, below the mean.** The extra hypothesis `a ≤ k` is real: below
the mean it does *not* follow from `k ≤ lam - 1`, and where it fails the model
tail is identically zero — see `tailLe_eq_zero_of_lt`, which is how
`tailLe_le_binTail` covers that branch. -/
theorem binTail_shape_ge : ∀ (n a r : ℕ) (x : ℝ), a + r ≤ n → 0 ≤ x → x ≤ 1 →
    ∀ k : ℕ, a ≤ k → (k : ℝ) ≤ ((a : ℝ) + r * x) - 1 →
      binTail r x (k - a) ≤ binTail n (((a : ℝ) + r * x) / (n : ℝ)) k := by
  intro n
  induction n with
  | zero =>
      intro a r x har _ _ k _ hk
      have ha : a = 0 := by omega
      have hr : r = 0 := by omega
      subst ha; subst hr
      simp only [Nat.cast_zero, zero_mul, add_zero] at hk
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  | succ m ih =>
      intro a r x har hx0 hx1 k hak hk
      have hrx : (0 : ℝ) ≤ (r : ℝ) * x := mul_nonneg (Nat.cast_nonneg r) hx0
      have hn1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · by_cases hb : r ≤ m
        · have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hb
          have hlam : ((0 : ℕ) : ℝ) + (r : ℝ) * x ≤ (m : ℝ) := by
            have : (r : ℝ) * x ≤ (r : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
            push_cast
            linarith
          have h2 := ih 0 r x (by omega) hx0 hx1 k (Nat.zero_le k) hk
          have h1 := binTail_dropZero_le_binTail_succ (m := m)
            (lam := ((0 : ℕ) : ℝ) + (r : ℝ) * x) hlam (k := k) hk
          rw [hn1]
          exact le_trans h2 h1
        · have hrn : r = m + 1 := by omega
          subst hrn
          have hr0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by
            rw [hn1]; positivity
          have hmean : (((0 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) * x) / ((m + 1 : ℕ) : ℝ) = x := by
            rw [Nat.cast_zero, zero_add, mul_comm, mul_div_assoc, div_self hr0, mul_one]
          rw [hmean, Nat.sub_zero]
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hlamn : ((a' + 1 : ℕ) : ℝ) + (r : ℝ) * x ≤ (m : ℝ) + 1 := by
          have hrx' : (r : ℝ) * x ≤ (r : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
          have : ((a' + 1 : ℕ) : ℝ) + (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast har
          rw [hn1] at this
          linarith
        have h1 := binTail_dropOne_le_binTail_succ (m := m)
          (lam := ((a' + 1 : ℕ) : ℝ) + (r : ℝ) * x) hlamn (k := k')
          (by push_cast at hk ⊢; linarith)
        have hcast : ((a' : ℕ) : ℝ) + (r : ℝ) * x
            = (((a' + 1 : ℕ) : ℝ) + (r : ℝ) * x) - 1 := by push_cast; ring
        have h2 := ih a' r x (by omega) hx0 hx1 k' (by omega)
          (by rw [hcast]; push_cast at hk ⊢; linarith)
        rw [hcast] at h2
        have hidx : k' + 1 - (a' + 1) = k' - a' := by omega
        rw [hn1, hidx]
        exact le_trans h2 h1

end Residue

section Thm4

variable {ι : Type*} [DecidableEq ι]

/-- The shape data of a point of the box with at most one interior value,
packaged for the two halves of Theorem 4: the ones `O`, the zeros `Z`, and a
legal common interior value `y` (any value in `[0,1]` will do when the interior is
empty, and the mean equation still holds). -/
private lemma shape_data {s : Finset ι} {q : ι → ℝ} {lam : ℝ} (hq : InBox s lam q)
    (hshape : AtMostOneInteriorValue s q) :
    ∃ (O Z : Finset ι) (y : ℝ), O ⊆ s ∧ Z ⊆ s \ O ∧ (∀ i ∈ O, q i = 1) ∧ (∀ i ∈ Z, q i = 0)
      ∧ (∀ i ∈ (s \ O) \ Z, q i = y) ∧ 0 ≤ y ∧ y ≤ 1
      ∧ O.card + ((s \ O) \ Z).card ≤ s.card
      ∧ (O.card : ℝ) + (((s \ O) \ Z).card : ℝ) * y = lam := by
  classical
  obtain ⟨h0, h1, hsum⟩ := hq
  set O : Finset ι := s.filter (fun i => q i = 1) with hOdef
  set Z : Finset ι := s.filter (fun i => q i = 0) with hZdef
  obtain ⟨x, hx, hcount, hmean⟩ := shape_of_atMostOneInteriorValue ⟨h0, h1, hsum⟩ hshape
  have hIeq : (s \ O) \ Z = interiorCoords s q := by
    ext i
    simp only [Finset.mem_sdiff, hOdef, hZdef, Finset.mem_filter, interiorCoords,
      not_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, hne1⟩, hne0⟩
      refine ⟨hi, ?_, ?_⟩
      · exact lt_of_le_of_ne (h0 i hi) (Ne.symm (fun h => hne0 hi h))
      · exact lt_of_le_of_ne (h1 i hi) (fun h => hne1 hi h)
    · rintro ⟨hi, hlt0, hlt1⟩
      exact ⟨⟨hi, fun _ h => absurd h (ne_of_lt hlt1)⟩, fun _ h => absurd h (ne_of_gt hlt0)⟩
  have hOs : O ⊆ s := Finset.filter_subset _ _
  have hZs : Z ⊆ s \ O := by
    intro i hi
    rw [hZdef, Finset.mem_filter] at hi
    rw [Finset.mem_sdiff, hOdef, Finset.mem_filter]
    exact ⟨hi.1, fun h => by rw [hi.2] at h; exact zero_ne_one h.2⟩
  have hOval : ∀ i ∈ O, q i = 1 := fun i hi => (Finset.mem_filter.mp hi).2
  have hZval : ∀ i ∈ Z, q i = 0 := fun i hi => (Finset.mem_filter.mp hi).2
  have hIval : ∀ i ∈ (s \ O) \ Z, q i = x := by rw [hIeq]; exact hx
  have hmean' : (O.card : ℝ) + (((s \ O) \ Z).card : ℝ) * x = lam := by
    rw [hIeq]; exact hmean
  have hsum' : O.card + ((s \ O) \ Z).card ≤ s.card := by
    rw [hIeq]
    have hOc : O.card = (s.filter (fun i => q i = 1)).card := rfl
    have hZc : Z.card = (s.filter (fun i => q i = 0)).card := rfl
    omega
  rcases Finset.eq_empty_or_nonempty ((s \ O) \ Z) with hemp | ⟨i₀, hi₀⟩
  · refine ⟨O, Z, 0, hOs, hZs, hOval, hZval, ?_, le_rfl, zero_le_one, hsum', ?_⟩
    · rw [hemp]; simp
    · rw [hemp] at hmean' ⊢
      simpa using hmean'
  · have hq0 : q i₀ = x := hIval i₀ hi₀
    have hmem : i₀ ∈ s := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi₀).1).1
    exact ⟨O, Z, x, hOs, hZs, hOval, hZval, hIval, hq0 ▸ h0 i₀ hmem, hq0 ▸ h1 i₀ hmem,
      hsum', hmean'⟩

/-- **Theorem 4, above the mean.** For independent trials indexed by an
arbitrary `s`, with success probabilities `p` and mean `lam = ∑ p`, and any `k ≥ lam`,

`B(k; #s, lam/#s) ≤ P[S ≤ k]`.

No hypothesis beyond `0 ≤ p i ≤ 1` on `s`. -/
theorem binTail_le_tailLe {s : Finset ι} {p : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (k : ℕ)
    (hk : (∑ i ∈ s, p i) ≤ (k : ℝ)) :
    binTail s.card ((∑ i ∈ s, p i) / (s.card : ℝ)) k ≤ tailLe s p k := by
  classical
  have hp : InBox s (∑ i ∈ s, p i) p := ⟨h0, h1, rfl⟩
  obtain ⟨q, hq, hshape, hmin⟩ :=
    hoeffding_cor21_min (s := s) (fun r => if r ≤ k then (1 : ℝ) else 0) hp
  obtain ⟨O, Z, y, hOs, hZs, hOval, hZval, hIval, hy0, hy1, hcard, hmean⟩ :=
    shape_data hq hshape
  have hOk : O.card ≤ k := by
    have hnn : (0 : ℝ) ≤ (((s \ O) \ Z).card : ℝ) * y := mul_nonneg (Nat.cast_nonneg _) hy0
    have : (O.card : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hkey := binTail_shape_le s.card O.card ((s \ O) \ Z).card y hcard hy0 hy1 k
    (by rw [hmean]; exact hk)
  rw [hmean] at hkey
  have hval : tailLe s q k = binTail ((s \ O) \ Z).card y (k - O.card) :=
    tailLe_shape_eval hOs hZs hOval hZval hIval hOk
  have hle : tailLe s q k ≤ tailLe s p k := hmin p hp
  rw [hval] at hle
  exact le_trans hkey hle

/-- **Theorem 4, below the mean.** For `k ≤ lam - 1`, `P[S ≤ k] ≤ B(k; #s, lam/#s)`. -/
theorem tailLe_le_binTail {s : Finset ι} {p : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (k : ℕ)
    (hk : (k : ℝ) ≤ (∑ i ∈ s, p i) - 1) :
    tailLe s p k ≤ binTail s.card ((∑ i ∈ s, p i) / (s.card : ℝ)) k := by
  classical
  have hp : InBox s (∑ i ∈ s, p i) p := ⟨h0, h1, rfl⟩
  obtain ⟨q, hq, hshape, hmax⟩ :=
    hoeffding_cor21 (s := s) (fun r => if r ≤ k then (1 : ℝ) else 0) hp
  obtain ⟨O, Z, y, hOs, hZs, hOval, hZval, hIval, hy0, hy1, hcard, hmean⟩ :=
    shape_data hq hshape
  have hle : tailLe s p k ≤ tailLe s q k := hmax p hp
  by_cases hOk : O.card ≤ k
  · have hkey := binTail_shape_ge s.card O.card ((s \ O) \ Z).card y hcard hy0 hy1 k hOk
      (by rw [hmean]; exact hk)
    rw [hmean] at hkey
    have hval : tailLe s q k = binTail ((s \ O) \ Z).card y (k - O.card) :=
      tailLe_shape_eval hOs hZs hOval hZval hIval hOk
    rw [hval] at hle
    exact le_trans hle hkey
  · rw [tailLe_eq_zero_of_lt hOs hOval (by omega)] at hle
    refine le_trans hle ?_
    have hmn : (0 : ℝ) ≤ ∑ i ∈ s, p i := Finset.sum_nonneg fun i hi => h0 i hi
    have hmx : (∑ i ∈ s, p i) ≤ (s.card : ℝ) := by
      calc (∑ i ∈ s, p i) ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i hi => h1 i hi
        _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    refine binTail_nonneg (div_nonneg hmn (Nat.cast_nonneg _)) ?_
    rcases Nat.eq_zero_or_pos s.card with hc | hc
    · rw [hc]; simp
    · exact (div_le_one (by exact_mod_cast hc)).mpr hmx

end Thm4



/-! ### The trivial bounds, and the complement duality

Hoeffding's (24) and (26) each pair a substantial bound with a trivial one — `0 ≤ P[S ≤ c]`
and `P[S ≤ c] ≤ 1` — and the paper's proof gets each lower bound from an upper bound through
the identity `P(S ≤ c | p) = 1 - P(S ≤ n-c-1 | 1-p)`. Both are recorded here: the trivial
bounds because they are part of the displayed statement, and the duality because it is the
symmetry of the whole section, and is stated without `ℕ`-subtraction. -/

section Trivial

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- `P[S ≤ k]` is nonnegative. -/
theorem tailLe_nonneg {s : Finset ι} {p : ι → 𝕜} (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∀ i ∈ s, p i ≤ 1) (k : ℕ) : 0 ≤ tailLe s p k := by
  rw [tailLe, bernExp]
  refine Finset.sum_nonneg fun A hA => ?_
  refine mul_nonneg (bernWt_nonneg (Finset.mem_powerset.mp hA) h0 h1) ?_
  split_ifs
  · exact zero_le_one
  · exact le_rfl

/-- `P[S ≤ k]` is at most `1`. -/
theorem tailLe_le_one {s : Finset ι} {p : ι → 𝕜} (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∀ i ∈ s, p i ≤ 1) (k : ℕ) : tailLe s p k ≤ 1 := by
  have hle : tailLe s p k ≤ ∑ A ∈ s.powerset, bernWt s p A := by
    rw [tailLe, bernExp]
    refine Finset.sum_le_sum fun A hA => ?_
    have hw : 0 ≤ bernWt s p A := bernWt_nonneg (Finset.mem_powerset.mp hA) h0 h1
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact hw
  rwa [sum_bernWt] at hle

end Trivial

section Duality

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [CommRing 𝕜]

/-- Complementation `A ↦ s \ A` is an involution of `s.powerset`, so it leaves any sum over
the powerset unchanged. -/
lemma sum_powerset_sdiff {M : Type*} [AddCommMonoid M] (s : Finset ι) (F : Finset ι → M) :
    ∑ A ∈ s.powerset, F (s \ A) = ∑ A ∈ s.powerset, F A := by
  classical
  have hinj : ∀ x ∈ s.powerset, ∀ y ∈ s.powerset, s \ x = s \ y → x = y := by
    intro x hx y hy h
    rw [Finset.mem_powerset] at hx hy
    rw [← Finset.sdiff_sdiff_eq_self hx, h, Finset.sdiff_sdiff_eq_self hy]
  have himg : s.powerset.image (fun A => s \ A) = s.powerset := by
    ext B
    simp only [Finset.mem_image, Finset.mem_powerset]
    constructor
    · rintro ⟨A, -, rfl⟩; exact Finset.sdiff_subset
    · intro hB; exact ⟨s \ B, Finset.sdiff_subset, Finset.sdiff_sdiff_eq_self hB⟩
  calc ∑ A ∈ s.powerset, F (s \ A)
      = ∑ B ∈ s.powerset.image (fun A => s \ A), F B := (Finset.sum_image hinj).symm
    _ = ∑ B ∈ s.powerset, F B := by rw [himg]

/-- **Complementing the trials complements the success sets.** Replacing every `p i` by
`1 - p i` and every success set `A` by `s \ A` leaves the weight unchanged. -/
lemma bernWt_sdiff {s A : Finset ι} (hA : A ⊆ s) (p : ι → 𝕜) :
    bernWt s (fun i => 1 - p i) (s \ A) = bernWt s p A := by
  unfold bernWt
  rw [Finset.sdiff_sdiff_eq_self hA,
    Finset.prod_congr rfl (fun i (_ : i ∈ A) => show (1 : 𝕜) - (1 - p i) = p i by ring)]
  ring

/-- **The complement duality**, in the form Hoeffding uses (p. 720): with `n = #s` trials,
`P[S ≤ k | p] = 1 - P[S ≤ n - k - 1 | 1 - p]`. Stated as `k + j + 1 = n` so that no
`ℕ`-subtraction appears. -/
theorem tailLe_add_tailLe_compl {s : Finset ι} (p : ι → 𝕜) {k j : ℕ}
    (h : k + j + 1 = s.card) :
    tailLe s p k + tailLe s (fun i => 1 - p i) j = 1 := by
  classical
  have h2 : tailLe s (fun i => 1 - p i) j
      = ∑ A ∈ s.powerset, bernWt s p A * (if s.card - A.card ≤ j then (1 : 𝕜) else 0) := by
    rw [tailLe, bernExp,
      ← sum_powerset_sdiff s
        (fun A => bernWt s (fun i => 1 - p i) A * (if A.card ≤ j then (1 : 𝕜) else 0))]
    refine Finset.sum_congr rfl fun A hA => ?_
    have hAs := Finset.mem_powerset.mp hA
    rw [bernWt_sdiff hAs, Finset.card_sdiff_of_subset hAs]
  have key : ∑ A ∈ s.powerset, (bernWt s p A * (if A.card ≤ k then (1 : 𝕜) else 0)
        + bernWt s p A * (if s.card - A.card ≤ j then (1 : 𝕜) else 0))
      = ∑ A ∈ s.powerset, bernWt s p A := by
    refine Finset.sum_congr rfl fun A hA => ?_
    have hcard : A.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
    by_cases hk : A.card ≤ k
    · rw [if_pos hk, if_neg (by omega)]; ring
    · rw [if_neg hk, if_pos (by omega)]; ring
  rw [tailLe, bernExp, h2, ← Finset.sum_add_distrib, key, sum_bernWt]

end Duality

/-! ### Theorem 4, packaged, and the sharpness of its bounds

`hoeffding_thm4` puts the two regimes together in the shape of the paper's (24) and (26),
trivial bounds included. The three `exists_inBox_*` theorems then discharge the paper's
assertion that all four of those bounds are **attained**: each is realised by an explicit
point of the fixed-mean box, so none of them can be improved. (The *uniqueness* half of the
paper's attainment statement — that some of them are attained only at the constant vector —
is not formalised; see the caveat in the module docstring.) -/

section Thm4Packaged

variable {ι : Type*} [DecidableEq ι]

/-- **Hoeffding (1956), Theorem 4 — the two extreme regimes, with no hypothesis beyond
the box**, on an arbitrary ground set.

`tailLe s p k` is `P[S ≤ k]` for independent trials with success probabilities `p`, and
`binTail #s (lam/#s) k` is the same for `#s` identical trials at the common mean. The
comparison holds in one direction at thresholds `k ≥ lam` and the other at `k ≤ lam - 1`,
and the trivial bound of the paper's display accompanies each.

**Not claimed**: the middle regime `lam - 1 < k < lam` of the paper's (25), and the equality
clause of the paper's attainment statement. The middle regime is empty or a single
threshold: see `thm4_gap_subsingleton`. -/
theorem hoeffding_thm4 {s : Finset ι} (p : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (k : ℕ) :
    ((∑ i ∈ s, p i) ≤ (k : ℝ) →
        binTail s.card ((∑ i ∈ s, p i) / (s.card : ℝ)) k ≤ tailLe s p k
          ∧ tailLe s p k ≤ 1)
      ∧ ((k : ℝ) ≤ (∑ i ∈ s, p i) - 1 →
        0 ≤ tailLe s p k
          ∧ tailLe s p k ≤ binTail s.card ((∑ i ∈ s, p i) / (s.card : ℝ)) k) :=
  ⟨fun hk => ⟨binTail_le_tailLe h0 h1 k hk, tailLe_le_one h0 h1 k⟩,
   fun hk => ⟨tailLe_nonneg h0 h1 k, tailLe_le_binTail h0 h1 k hk⟩⟩

/-- Theorem 4 on `range n`, the form in which it is usually quoted. -/
theorem hoeffding_thm4_range {n : ℕ} (p : ℕ → ℝ)
    (h0 : ∀ j ∈ range n, 0 ≤ p j) (h1 : ∀ j ∈ range n, p j ≤ 1) (k : ℕ) :
    ((∑ j ∈ range n, p j) ≤ (k : ℝ) →
        binTail n ((∑ j ∈ range n, p j) / (n : ℝ)) k ≤ tailLe (range n) p k
          ∧ tailLe (range n) p k ≤ 1)
      ∧ ((k : ℝ) ≤ (∑ j ∈ range n, p j) - 1 →
        0 ≤ tailLe (range n) p k
          ∧ tailLe (range n) p k ≤ binTail n ((∑ j ∈ range n, p j) / (n : ℝ)) k) := by
  have h := hoeffding_thm4 (s := range n) p h0 h1 k
  rwa [Finset.card_range] at h

end Thm4Packaged

section Attainment

variable {ι : Type*} [DecidableEq ι]

/-- **The binomial bound of Theorem 4 is attained**, in either regime: the constant vector
`p ≡ lam/#s` lies in the fixed-mean box and its tail *is* the binomial tail. So neither
inequality of `hoeffding_thm4` can be strengthened. -/
theorem exists_inBox_tailLe_eq_binTail {s : Finset ι} {lam : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam ≤ (s.card : ℝ)) (k : ℕ) :
    ∃ p : ι → ℝ, InBox s lam p ∧ tailLe s p k = binTail s.card (lam / (s.card : ℝ)) k := by
  have hp1 : ∀ i ∈ s, lam / (s.card : ℝ) ≤ 1 := by
    intro i _
    rcases Nat.eq_zero_or_pos s.card with hc | hc
    · rw [hc]; simp
    · exact (div_le_one (by exact_mod_cast hc)).mpr h1
  have hpsum : ∑ _i ∈ s, lam / (s.card : ℝ) = lam := by
    rcases Nat.eq_zero_or_pos s.card with hc | hc
    · rw [Finset.card_eq_zero.mp hc] at h1 ⊢
      simp only [Finset.card_empty, Nat.cast_zero] at h1
      simp only [Finset.sum_empty]
      linarith
    · have hne : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hne]
  exact ⟨fun _ => lam / (s.card : ℝ),
    ⟨fun i _ => div_nonneg h0 (Nat.cast_nonneg _), hp1, hpsum⟩, tailLe_const s k _⟩

/-- **The upper bound `1` of the paper's (26) is attained.** Above the mean there is a point
of the fixed-mean box at which `P[S ≤ k] = 1`: pin `⌊lam⌋` trials at success, give the
fractional remainder to one further trial, and leave the rest at `0`. -/
theorem exists_inBox_tailLe_eq_one {s : Finset ι} {lam : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam ≤ (s.card : ℝ)) {k : ℕ} (hk : lam ≤ (k : ℝ)) :
    ∃ p : ι → ℝ, InBox s lam p ∧ tailLe s p k = 1 := by
  classical
  have hale : ((⌊lam⌋₊ : ℕ) : ℝ) ≤ lam := Nat.floor_le h0
  have has : ⌊lam⌋₊ ≤ s.card := by exact_mod_cast le_trans hale h1
  have hak : ⌊lam⌋₊ ≤ k := by exact_mod_cast le_trans hale hk
  obtain ⟨O, hOs, hOcard⟩ := Finset.exists_subset_card_eq has
  by_cases hx : lam = ((⌊lam⌋₊ : ℕ) : ℝ)
  · -- The mean is a whole number: pin `⌊lam⌋` trials at success and the rest at failure.
    have hp0 : ∀ i ∈ s, (0 : ℝ) ≤ (if i ∈ O then (1 : ℝ) else 0) := by
      intro i _; split_ifs <;> norm_num
    have hp1 : ∀ i ∈ s, (if i ∈ O then (1 : ℝ) else 0) ≤ 1 := by
      intro i _; split_ifs <;> norm_num
    have hpsum : ∑ i ∈ s, (if i ∈ O then (1 : ℝ) else 0) = lam := by
      have hA : ∑ i ∈ s \ O, (if i ∈ O then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun i hi => if_neg (Finset.mem_sdiff.mp hi).2
      have hB : ∑ i ∈ O, (if i ∈ O then (1 : ℝ) else 0) = (O.card : ℝ) := by
        rw [Finset.sum_congr rfl (fun i hi => if_pos hi), Finset.sum_const, nsmul_eq_mul,
          mul_one]
      rw [← Finset.sum_sdiff hOs, hA, hB, hOcard, zero_add]
      exact hx.symm
    have hI : ∀ i ∈ (s \ O) \ (s \ O), (if i ∈ O then (1 : ℝ) else 0) = 0 := by
      intro i hi
      rw [Finset.sdiff_self] at hi
      exact absurd hi (Finset.notMem_empty i)
    have htail : tailLe s (fun i => if i ∈ O then (1 : ℝ) else 0) k = 1 := by
      rw [tailLe_shape_eval (O := O) (Z := s \ O) (x := 0) hOs Finset.Subset.rfl
        (fun i hi => if_pos hi) (fun i hi => if_neg (Finset.mem_sdiff.mp hi).2) hI
        (by rw [hOcard]; exact hak), Finset.sdiff_self, Finset.card_empty]
      exact binTail_eq_one _ (Nat.zero_le _)
    exact ⟨fun i => if i ∈ O then 1 else 0, ⟨hp0, hp1, hpsum⟩, htail⟩
  · -- The mean is not a whole number: one further trial carries the remainder.
    have haltlam : ((⌊lam⌋₊ : ℕ) : ℝ) < lam := lt_of_le_of_ne hale (fun hcon => hx hcon.symm)
    have hacard : ⌊lam⌋₊ < s.card := by
      by_contra hcon
      have heq : s.card = ⌊lam⌋₊ := by omega
      rw [heq] at h1
      exact hx (le_antisymm h1 hale)
    have hne : (s \ O).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hOs, hOcard]
      omega
    obtain ⟨i₀, hi₀⟩ := hne
    have hi₀O : i₀ ∉ O := (Finset.mem_sdiff.mp hi₀).2
    have hx1 : lam - ((⌊lam⌋₊ : ℕ) : ℝ) ≤ 1 := by
      have := Nat.lt_floor_add_one lam
      linarith
    have hakk : ⌊lam⌋₊ < k := by
      have : ((⌊lam⌋₊ : ℕ) : ℝ) < (k : ℝ) := lt_of_lt_of_le haltlam hk
      exact_mod_cast this
    have hpv : ∀ i, (if i ∈ O then (1 : ℝ) else
        if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0)
        = (if i ∈ O then (1 : ℝ) else if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) :=
      fun _ => rfl
    have hpi₀ : (if i₀ ∈ O then (1 : ℝ) else
        if i₀ = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) = lam - ((⌊lam⌋₊ : ℕ) : ℝ) := by
      rw [if_neg hi₀O, if_pos rfl]
    have hp0 : ∀ i ∈ s, (0 : ℝ) ≤ (if i ∈ O then (1 : ℝ) else
        if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) := by
      intro i _
      split_ifs
      · norm_num
      · linarith
      · norm_num
    have hp1 : ∀ i ∈ s, (if i ∈ O then (1 : ℝ) else
        if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) ≤ 1 := by
      intro i _
      split_ifs
      · norm_num
      · exact hx1
      · norm_num
    have hpsum : ∑ i ∈ s, (if i ∈ O then (1 : ℝ) else
        if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) = lam := by
      have hB : ∑ i ∈ O, (if i ∈ O then (1 : ℝ) else
          if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) = (O.card : ℝ) := by
        rw [Finset.sum_congr rfl (fun i hi => if_pos hi), Finset.sum_const, nsmul_eq_mul,
          mul_one]
      have hA : ∑ i ∈ s \ O, (if i ∈ O then (1 : ℝ) else
          if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) = lam - ((⌊lam⌋₊ : ℕ) : ℝ) := by
        refine (Finset.sum_eq_single i₀ ?_ ?_).trans hpi₀
        · intro b hb hbne
          rw [if_neg (Finset.mem_sdiff.mp hb).2, if_neg hbne]
        · intro hcon; exact absurd hi₀ hcon
      rw [← Finset.sum_sdiff hOs, hA, hB, hOcard]
      ring
    have hIeq : (s \ O) \ ((s \ O).erase i₀) = {i₀} := Finset.sdiff_erase_self hi₀
    have hZval : ∀ i ∈ (s \ O).erase i₀, (if i ∈ O then (1 : ℝ) else
        if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) = 0 := by
      intro i hi
      rw [Finset.mem_erase] at hi
      rw [if_neg (Finset.mem_sdiff.mp hi.2).2, if_neg hi.1]
    have hIval : ∀ i ∈ (s \ O) \ ((s \ O).erase i₀), (if i ∈ O then (1 : ℝ) else
        if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) = lam - ((⌊lam⌋₊ : ℕ) : ℝ) := by
      intro i hi
      rw [hIeq, Finset.mem_singleton] at hi
      rw [hi]; exact hpi₀
    have htail : tailLe s (fun i => if i ∈ O then (1 : ℝ) else
        if i = i₀ then lam - ((⌊lam⌋₊ : ℕ) : ℝ) else 0) k = 1 := by
      rw [tailLe_shape_eval (O := O) (Z := (s \ O).erase i₀)
        (x := lam - ((⌊lam⌋₊ : ℕ) : ℝ)) hOs (Finset.erase_subset _ _)
        (fun i hi => if_pos hi) hZval hIval (by rw [hOcard]; omega),
        hIeq, Finset.card_singleton]
      exact binTail_eq_one _ (by rw [hOcard]; omega)
    exact ⟨_, ⟨hp0, hp1, hpsum⟩, htail⟩

/-- **The lower bound `0` of the paper's (24) is attained.** Below the mean there is a point
of the fixed-mean box at which `P[S ≤ k] = 0`: pin `k + 1` trials at success — which the
regime `k ≤ lam - 1` leaves room for — and spread the remaining mean evenly over the rest. -/
theorem exists_inBox_tailLe_eq_zero {s : Finset ι} {lam : ℝ} (h1 : lam ≤ (s.card : ℝ))
    {k : ℕ} (hk : (k : ℝ) ≤ lam - 1) :
    ∃ p : ι → ℝ, InBox s lam p ∧ tailLe s p k = 0 := by
  classical
  have has : k + 1 ≤ s.card := by
    have : ((k + 1 : ℕ) : ℝ) ≤ (s.card : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨O, hOs, hOcard⟩ := Finset.exists_subset_card_eq has
  have hOle : (O.card : ℝ) ≤ lam := by rw [hOcard]; push_cast; linarith
  have hOcs : (O.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.card_le_card hOs
  have hy0 : 0 ≤ (lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ)) :=
    div_nonneg (by linarith) (by linarith)
  have hy1 : (lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ)) ≤ 1 := by
    rcases eq_or_lt_of_le hOcs with heq | hlt
    · have hlam : lam = (O.card : ℝ) := le_antisymm (by rw [← heq] at h1; exact h1) hOle
      rw [hlam, sub_self, zero_div]
      norm_num
    · exact (div_le_one (by linarith)).mpr (by linarith)
  have hp0 : ∀ i ∈ s, (0 : ℝ) ≤ (if i ∈ O then (1 : ℝ) else
      (lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ))) := by
    intro i _; split_ifs
    · norm_num
    · exact hy0
  have hp1 : ∀ i ∈ s, (if i ∈ O then (1 : ℝ) else
      (lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ))) ≤ 1 := by
    intro i _; split_ifs
    · norm_num
    · exact hy1
  have hpsum : ∑ i ∈ s, (if i ∈ O then (1 : ℝ) else
      (lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ))) = lam := by
    have hB : ∑ i ∈ O, (if i ∈ O then (1 : ℝ) else
        (lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ))) = (O.card : ℝ) := by
      rw [Finset.sum_congr rfl (fun i hi => if_pos hi), Finset.sum_const, nsmul_eq_mul, mul_one]
    have hA : ∑ i ∈ s \ O, (if i ∈ O then (1 : ℝ) else
        (lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ)))
        = ((s.card : ℝ) - (O.card : ℝ))
            * ((lam - (O.card : ℝ)) / ((s.card : ℝ) - (O.card : ℝ))) := by
      rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_sdiff.mp hi).2),
        Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset hOs,
        Nat.cast_sub (Finset.card_le_card hOs)]
    rw [← Finset.sum_sdiff hOs, hA, hB]
    rcases eq_or_lt_of_le hOcs with heq | hlt
    · have hlam : lam = (O.card : ℝ) := le_antisymm (by rw [← heq] at h1; exact h1) hOle
      rw [hlam, sub_self, zero_div, mul_zero, zero_add]
    · have hd : ((s.card : ℝ) - (O.card : ℝ)) ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ring
  refine ⟨_, ⟨hp0, hp1, hpsum⟩, ?_⟩
  refine tailLe_eq_zero_of_lt hOs (fun i hi => if_pos hi) ?_
  rw [hOcard]
  omega

end Attainment

/-! ### What the two regimes leave out

The paper's Theorem 4 has a third regime, `lam - 1 < c < lam`, whose bound is the auxiliary
`Q(c,p)` of its (27); that regime is not formalised here. What *is* formalised is its size.
Since the threshold is an integer and the regime is an open interval of length `1`, it
contains at most one integer, namely `⌊lam⌋`, and none at all when the mean is a whole
number. So the two bounds above cover every threshold but one, and cover all of them
whenever `lam ∈ ℕ`. -/

section Gap

/-- Every threshold falls in one of Hoeffding's three regimes. -/
theorem thm4_regimes (lam : ℝ) (k : ℕ) :
    lam ≤ (k : ℝ) ∨ (k : ℝ) ≤ lam - 1 ∨ (lam - 1 < (k : ℝ) ∧ (k : ℝ) < lam) := by
  by_cases h1 : lam ≤ (k : ℝ)
  · exact Or.inl h1
  by_cases h2 : (k : ℝ) ≤ lam - 1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- **The uncovered regime holds at most one threshold.** -/
theorem thm4_gap_subsingleton {lam : ℝ} {k k' : ℕ}
    (hk : lam - 1 < (k : ℝ)) (hk' : (k : ℝ) < lam)
    (hl : lam - 1 < (k' : ℝ)) (hl' : (k' : ℝ) < lam) : k = k' := by
  have h1 : (k : ℝ) < (k' : ℝ) + 1 := by linarith
  have h2 : (k' : ℝ) < (k : ℝ) + 1 := by linarith
  have h1' : k < k' + 1 := by exact_mod_cast h1
  have h2' : k' < k + 1 := by exact_mod_cast h2
  omega

/-- **And that threshold is `⌊lam⌋`.** -/
theorem thm4_gap_eq_floor {lam : ℝ} {k : ℕ} (hk : lam - 1 < (k : ℝ)) (hk' : (k : ℝ) < lam) :
    k = ⌊lam⌋₊ := by
  have hlam0 : (0 : ℝ) ≤ lam := le_trans (Nat.cast_nonneg k) hk'.le
  have hle : k ≤ ⌊lam⌋₊ := Nat.le_floor hk'.le
  have hlt : ⌊lam⌋₊ < k + 1 := by
    rw [Nat.floor_lt hlam0]
    push_cast
    linarith
  omega

/-- **When the mean is a whole number the uncovered regime is empty**, so the two bounds of
`hoeffding_thm4` between them settle every threshold. -/
theorem thm4_gap_empty_of_natCast {n k : ℕ} (hk : (n : ℝ) - 1 < (k : ℝ))
    (hk' : (k : ℝ) < (n : ℝ)) : False := by
  have h1 : (n : ℝ) < (k : ℝ) + 1 := by linarith
  have h1' : n < k + 1 := by exact_mod_cast h1
  have h2' : k < n := by exact_mod_cast hk'
  omega

/-- **The lower regime cannot be widened to "below the mean".** Its hypothesis is
`k ≤ lam - 1`, and the difference from `k < lam` is not slack. At `p = (1, 1/2)` on two
trials the mean is `3/2`, and the threshold `k = 1` lies below it but outside the regime:
there `P[S ≤ 1] = 1/2` while `B(1; 2, 3/4) = 7/16`, so the binomial tail is the *lighter*
one and the inequality of `tailLe_le_binTail` runs the other way.

So the gap `lam - 1 < k < lam` is not merely a regime nobody attempted. It is where the
looser reading is false, which is why `hoeffding_thm4` carries the hypothesis it does. -/
theorem thm4_lower_needs_le_sub_one :
    ∃ p : ℕ → ℝ, (∀ i ∈ range 2, 0 ≤ p i) ∧ (∀ i ∈ range 2, p i ≤ 1)
      ∧ ((1 : ℕ) : ℝ) < ∑ i ∈ range 2, p i
      ∧ ¬ (tailLe (range 2) p 1
            ≤ binTail 2 ((∑ i ∈ range 2, p i) / ((range 2).card : ℝ)) 1) := by
  refine ⟨fun j => if j = 0 then 1 else 1 / 2, fun i _ => ?_, fun i _ => ?_, ?_, ?_⟩
  · dsimp only; split_ifs <;> norm_num
  · dsimp only; split_ifs <;> norm_num
  · norm_num [Finset.sum_range_succ]
  · have hsum : (∑ i ∈ range 2, (if i = 0 then (1 : ℝ) else 1 / 2)) = 3 / 2 := by
      norm_num [Finset.sum_range_succ]
    have hmodel : tailLe (range 2) (fun j => if j = 0 then (1 : ℝ) else 1 / 2) 1 = 1 / 2 := by
      rw [tailLe, show (range 2 : Finset ℕ) = {0, 1} by decide +kernel,
        bernExp_pair (by norm_num)]
      norm_num
    rw [hsum, hmodel, Finset.card_range, binTail]
    norm_num [Finset.sum_range_succ]

end Gap

end MiscMath.Probability
