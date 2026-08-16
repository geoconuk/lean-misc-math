/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

/-!
# The binomial tail, and its derivative in the success probability

Infrastructure for `MiscMath.Probability.PoissonTrialsFixedMean`, which is where the results
are stated and where the reader should start. Nothing here is a result on its own: this file
supplies the elementary object `binTail` and the one calculus fact about it that the argument
for Hoeffding's Theorem 4 needs. `PoissonTrialsFixedMean.Bridge` identifies `binTail` with
Mathlib's `ProbabilityTheory.binomial`.
-/

namespace MiscMath.Probability

open Finset

/-! ## The binomial tail

Mathlib has the binomial distribution but no partial sum, tail or cumulative distribution
function for it, and no derivative or monotonicity in either parameter. This section
supplies the elementary object and the one calculus fact about it that the argument for
Theorem 4 needs:

    binTail n P k = ∑_{j ≤ k} C(n,j) · P^j · (1-P)^(n-j)   ( = P[Bin(n,P) ≤ k] )

and

    d/dP binTail n P k = - n · C(n-1,k) · P^k · (1-P)^(n-1-k).

The derivative is proved by telescoping rather than by passing through `Polynomial`:
differentiating term by term and applying `j·C(n,j) = n·C(n-1,j-1)` and
`(n-j)·C(n,j) = n·C(n-1,j)` turns each summand into a difference of consecutive terms, and
`Finset.sum_range_sub'` collapses the sum.

Every exponent below is the `ℕ`-truncated one. That is deliberate, and it is where the care
is: at `j = 0` and at `j > n` the truncated powers are *wrong*, and in each case the
accompanying coefficient (`j`, or `n - j`, or `C(n,j)`) vanishes and kills the term. Stating
the derivative with `binShapeD`, which has no negative powers anywhere, is what makes the
statement true as written rather than true-up-to-edge-cases. -/

section BinTail

variable {𝕜 : Type*} [CommRing 𝕜]

/-- The binomial tail `P[Bin(n,P) ≤ k] = ∑_{j ≤ k} C(n,j) P^j (1-P)^(n-j)`.
Terms with `j > n` vanish because `C(n,j) = 0`, so no truncation guard on `k` is
needed. See `binTail_eq_binomial_real_Iic` for the identification with Mathlib's
`ProbabilityTheory.binomial`. -/
def binTail (n : ℕ) (P : 𝕜) (k : ℕ) : 𝕜 :=
  ∑ j ∈ range (k + 1), (n.choose j : 𝕜) * P ^ j * (1 - P) ^ (n - j)

/-- The shape `t^k (1-t)^(m-k)`; its `C(m,k)`-multiple is minus `1/(m+1)` times
the derivative of `binTail (m+1) · k`. -/
def binShape (k m : ℕ) (t : 𝕜) : 𝕜 := t ^ k * (1 - t) ^ (m - k)

/-- The derivative of `binShape`, written with **no negative powers**: the two
coefficients `k` and `m - k` kill the truncated exponents exactly where they
would otherwise be wrong. -/
def binShapeD (k m : ℕ) (t : 𝕜) : 𝕜 :=
  (k : 𝕜) * t ^ (k - 1) * (1 - t) ^ (m - k)
    - ((m - k : ℕ) : 𝕜) * t ^ k * (1 - t) ^ (m - k - 1)

lemma binTail_eq_sum_shape (n k : ℕ) (P : 𝕜) :
    binTail n P k = ∑ j ∈ range (k + 1), (n.choose j : 𝕜) * binShape j n P := by
  simp [binTail, binShape, mul_assoc]

/-- Peeling the top term off a tail. -/
lemma binTail_succ_term (n k : ℕ) (P : 𝕜) :
    binTail n P (k + 1) = binTail n P k + (n.choose (k + 1) : 𝕜) * binShape (k + 1) n P := by
  simp [binTail, binShape, Finset.sum_range_succ, mul_assoc]

/-- Above the number of trials the tail is `1`: it is the whole binomial
expansion of `(P + (1 - P))^n`. This is the edge case the `ℕ`-truncated exponent
`n - j` has to get right. -/
theorem binTail_eq_one {n k : ℕ} (P : 𝕜) (hk : n ≤ k) : binTail n P k = 1 := by
  have hsub : range (n + 1) ⊆ range (k + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  have hzero : ∀ j ∈ range (k + 1), j ∉ range (n + 1) →
      (n.choose j : 𝕜) * P ^ j * (1 - P) ^ (n - j) = 0 := by
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have key := add_pow P (1 - P) n
  rw [show P + (1 - P) = 1 from by ring, one_pow] at key
  rw [binTail, ← Finset.sum_subset hsub hzero]
  exact (Finset.sum_congr rfl fun j _ => by ring).trans key.symm

/-- At `P = 0` the tail is `1` for every `k`, including `k = 0` — the other edge
the truncation touches. -/
theorem binTail_zero_prob (n k : ℕ) : binTail n (0 : 𝕜) k = 1 := by
  rw [binTail, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj; simp [zero_pow hj]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h

end BinTail

section BinTailOrder

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The tail is nonnegative in the probability range — it is a probability. -/
theorem binTail_nonneg {n k : ℕ} {P : 𝕜} (h0 : 0 ≤ P) (h1 : P ≤ 1) : 0 ≤ binTail n P k :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _)) (pow_nonneg (by linarith) _)

end BinTailOrder

section BinTailDeriv

lemma hasDerivAt_binShape (k m : ℕ) (t : ℝ) :
    HasDerivAt (binShape k m) (binShapeD k m t) t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ k) ((k : ℝ) * t ^ (k - 1)) t := hasDerivAt_pow k t
  have hid : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ (m - k))
      (((m - k : ℕ) : ℝ) * (1 - t) ^ (m - k - 1) * (-1)) t := hid.fun_pow (m - k)
  have h3 : HasDerivAt (fun t : ℝ => t ^ k * (1 - t) ^ (m - k))
      ((k : ℝ) * t ^ (k - 1) * (1 - t) ^ (m - k)
        + t ^ k * (((m - k : ℕ) : ℝ) * (1 - t) ^ (m - k - 1) * (-1))) t := h1.mul h2
  have hval : (k : ℝ) * t ^ (k - 1) * (1 - t) ^ (m - k)
      + t ^ k * (((m - k : ℕ) : ℝ) * (1 - t) ^ (m - k - 1) * (-1)) = binShapeD k m t := by
    simp only [binShapeD]; ring
  rw [← hval]
  exact h3

/-- **The telescoping identity.** Summing the term-by-term derivatives of the
binomial tail collapses to a single term. The two `Nat.choose` identities
`j·C(n,j) = n·C(n-1,j-1)` and `(n-j)·C(n,j) = n·C(n-1,j)` turn each summand into
a difference of consecutive `C(m,·)·binShape` values. -/
lemma binTail_deriv_telescope (m k : ℕ) (t : ℝ) :
    ∑ j ∈ range (k + 1), (((m + 1).choose j : ℝ) * binShapeD j (m + 1) t)
      = -(((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t)) := by
  classical
  set tel : ℕ → ℝ := fun j =>
    if j = 0 then 0 else ((m : ℝ) + 1) * ((m.choose (j - 1) : ℝ) * binShape (j - 1) m t) with htel
  have key : ∀ j : ℕ, ((m + 1).choose j : ℝ) * binShapeD j (m + 1) t = tel j - tel (j + 1) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [htel, if_pos rfl, if_neg (Nat.succ_ne_zero 0), binShapeD, binShape,
        Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, Nat.zero_sub, Nat.sub_zero,
        Nat.add_sub_cancel]
      push_cast
      ring
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e1 : m + 1 - (i + 1) = m - i := by omega
      have e3 : m - (i + 1) = m - i - 1 := by omega
      have c1 : ((m + 1).choose (i + 1)) * (i + 1) = (m + 1) * m.choose i :=
        (Nat.add_one_mul_choose_eq m i).symm
      have c2 : (m + 1).choose (i + 1) * (m - i) = (m + 1) * m.choose (i + 1) := by
        have h1 := Nat.choose_succ_right_eq (m + 1) (i + 1)
        have h2 := Nat.add_one_mul_choose_eq m (i + 1)
        rw [e1] at h1
        rw [← h1, h2]
      have c1' : (((m + 1).choose (i + 1) : ℝ)) * ((i : ℝ) + 1)
          = ((m : ℝ) + 1) * (m.choose i : ℝ) := by exact_mod_cast c1
      have c2' : (((m + 1).choose (i + 1) : ℝ)) * ((m - i : ℕ) : ℝ)
          = ((m : ℝ) + 1) * (m.choose (i + 1) : ℝ) := by exact_mod_cast c2
      simp only [htel, if_neg (Nat.succ_ne_zero i), if_neg (Nat.succ_ne_zero (i + 1)),
        binShapeD, binShape, e1, e3, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      linear_combination (t ^ i * (1 - t) ^ (m - i)) * c1'
        - (t ^ (i + 1) * (1 - t) ^ (m - i - 1)) * c2'
  calc ∑ j ∈ range (k + 1), (((m + 1).choose j : ℝ) * binShapeD j (m + 1) t)
      = ∑ j ∈ range (k + 1), (tel j - tel (j + 1)) := Finset.sum_congr rfl fun j _ => key j
    _ = tel 0 - tel (k + 1) := Finset.sum_range_sub' tel (k + 1)
    _ = -(((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t)) := by
        simp only [htel, if_pos rfl, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
        ring

/-- **The derivative of a binomial tail in the success probability.**
`d/dP ∑_{j ≤ k} C(n,j) P^j (1-P)^(n-j) = - n · C(n-1,k) · P^k (1-P)^(n-1-k)`,
stated at `n = m + 1` so that no `ℕ`-subtraction appears in the coefficient. -/
theorem hasDerivAt_binTail (m k : ℕ) (t : ℝ) :
    HasDerivAt (fun p : ℝ => binTail (m + 1) p k)
      (-(((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t))) t := by
  have hfun : (fun p : ℝ => binTail (m + 1) p k)
      = fun p : ℝ => ∑ j ∈ range (k + 1), (((m + 1).choose j : ℝ) * binShape j (m + 1) p) := by
    funext p; exact binTail_eq_sum_shape _ _ _
  rw [hfun, ← binTail_deriv_telescope m k t]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_binShape j (m + 1) t).const_mul _

/-- The tail is nonincreasing in `P` on `[0,1]`: the derivative is `≤ 0` there. -/
theorem binTail_deriv_nonpos {m k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -(((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t)) ≤ 0 := by
  have h : (0 : ℝ) ≤ binShape k m t :=
    mul_nonneg (pow_nonneg ht0 _) (pow_nonneg (by linarith) _)
  have : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m.choose k : ℝ) * binShape k m t) :=
    mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) h)
  linarith

end BinTailDeriv

end MiscMath.Probability
