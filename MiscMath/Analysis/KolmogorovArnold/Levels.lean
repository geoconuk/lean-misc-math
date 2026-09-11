/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.Cells
import MiscMath.Analysis.KolmogorovArnold.InnerSpace
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Rational levels for the staircases

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; part of the density argument (Layer 2 of the development). Its
declarations are proof: machine-generated, kernel-checked and axiom-audited, and may be read by
no one.

Hedberg's approximating inner functions (Lemma 2, properties a) and b), p. 269) are constant on
each cell with a **rational** value, the values on distinct cells of one rank are distinct, and a
value taken on a cell of rank `i` differs from every value taken on a cell of rank `j ≠ i`.
Together with the rational independence of the `λ_p` (his Lemma 1′) this makes the *cell map*
`(q, j⃗) ↦ ∑_p λ_p · (value on cell (q, j_p))` injective, which is what lets the outer function
be prescribed cell by cell without conflict.

Here the levels are given by a closed formula rather than an inductive choice. With `b̂_{q,j}`
the right endpoint of the cell `(q, j)` in `t`-coordinates, clamped into `I`, and integers
`N, M ≥ 1`,

  `level φ N M q j = (m · (⌈(M · φ_q(b̂_{q,j}) - q) / m⌉ + j) + q) / M`.

The numerator is `≡ q (mod m)`, so levels of different ranks differ; the `+ j` makes the levels
of one rank strictly increasing even where `φ_q` is flat; and the ceiling places the level in
`[φ_q(b̂_{q,j}), φ_q(b̂_{q,j}) + m (j + 1) / M)`, so that for `M` large the staircase with these
levels is uniformly close to `φ_q`. Those are `le_level`, `level_lt`, `level_strictMono`,
`level_injective`; the cell map's injectivity from `LinearIndependent ℚ lam` is
`cellMap_injective`, the only place Layer 0 is used.
-/

open unitInterval

namespace MiscMath.Analysis.KolmogorovArnold

noncomputable section

variable {m : ℕ}

/-- The right endpoint of the cell `(q, j)` in `t`-coordinates, `(q + m j) / N`, clamped into
`I`. -/
def cellEnd (N : ℕ) (q : Fin m) (j : ℕ) : I := Set.projIcc 0 1 zero_le_one (cellRight q j / N)

theorem coe_cellEnd (N : ℕ) (q : Fin m) (j : ℕ) :
    (cellEnd N q j : ℝ) = min 1 (cellRight q j / N) := by
  rw [cellEnd, Set.coe_projIcc, max_eq_right]
  exact le_min zero_le_one (div_nonneg (cellRight_nonneg q j) (Nat.cast_nonneg N))

theorem cellEnd_mono (N : ℕ) (q : Fin m) : Monotone (cellEnd N q) := fun _ _ h =>
  Set.monotone_projIcc _ (div_le_div_of_nonneg_right (cellRight_mono q h) (Nat.cast_nonneg N))

/-- The value of the `q`-th inner function at the clamped right endpoint of the cell `(q, j)`. -/
def endValue (φ : Fin m → Inner) (N : ℕ) (q : Fin m) (j : ℕ) : ℝ :=
  (φ q : C(I, ℝ)) (cellEnd N q j)

theorem endValue_mono (φ : Fin m → Inner) (N : ℕ) (q : Fin m) : Monotone (endValue φ N q) :=
  fun _ _ h => (φ q).monotone (cellEnd_mono N q h)

/-- The integer numerator of a level: `m (⌈(M φ_q(b̂) - q) / m⌉ + j) + q`. -/
def levelNum (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) (j : ℕ) : ℤ :=
  m * (⌈(M * endValue φ N q j - (q : ℕ)) / m⌉ + j) + (q : ℕ)

/-- The level of the staircase of rank `q` on its cell of index `j`, a rational. -/
def level (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) (j : ℕ) : ℚ :=
  (levelNum φ N M q j : ℚ) / M

theorem level_cast (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) (j : ℕ) :
    ((level φ N M q j : ℚ) : ℝ) = (levelNum φ N M q j : ℝ) / M := by
  simp [level]

theorem levelNum_cast (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) (j : ℕ) :
    (levelNum φ N M q j : ℝ) =
      m * ((⌈(M * endValue φ N q j - (q : ℕ)) / m⌉ : ℝ) + j) + (q : ℕ) := by
  simp [levelNum]

/-- The level lies at or above the value of `φ_q` at the clamped right endpoint of its cell. -/
theorem le_level (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) (j : ℕ) :
    endValue φ N q j ≤ (level φ N M q j : ℝ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast q.pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [level_cast, levelNum_cast, le_div_iff₀ hMR]
  set a : ℝ := (M * endValue φ N q j - (q : ℕ)) / m with ha
  have h1 : a ≤ ⌈a⌉ := Int.le_ceil a
  have h2 : (m : ℝ) * a = M * endValue φ N q j - (q : ℕ) := by
    rw [ha]; field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hm.le
  have hj : (0 : ℝ) ≤ (m : ℝ) * j := by positivity
  nlinarith

/-- The level lies below `φ_q(b̂) + m (j + 1) / M`. -/
theorem level_lt (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) (j : ℕ) :
    (level φ N M q j : ℝ) < endValue φ N q j + m * (j + 1) / M := by
  have hm : (0 : ℝ) < m := by exact_mod_cast q.pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [level_cast, levelNum_cast, div_lt_iff₀ hMR]
  have e : (endValue φ N q j + m * (j + 1) / M) * M = M * endValue φ N q j + m * (j + 1) := by
    field_simp
  rw [e]
  set a : ℝ := (M * endValue φ N q j - (q : ℕ)) / m with ha
  have h1 : (⌈a⌉ : ℝ) < a + 1 := Int.ceil_lt_add_one a
  have h2 : (m : ℝ) * a = M * endValue φ N q j - (q : ℕ) := by
    rw [ha]; field_simp
  have h3 := mul_lt_mul_of_pos_left h1 hm
  nlinarith

/-- Within one rank the numerators strictly increase with the cell index. -/
theorem levelNum_lt_succ (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) (j : ℕ) :
    levelNum φ N M q j < levelNum φ N M q (j + 1) := by
  have hm : (0 : ℤ) < m := by exact_mod_cast q.pos
  have hmono : endValue φ N q j ≤ endValue φ N q (j + 1) := endValue_mono φ N q (Nat.le_succ j)
  have hceil : ⌈(M * endValue φ N q j - (q : ℕ)) / m⌉ ≤
      ⌈(M * endValue φ N q (j + 1) - (q : ℕ)) / m⌉ := by
    apply Int.ceil_mono
    have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm.le
    have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    exact div_le_div_of_nonneg_right (by nlinarith) hmR
  unfold levelNum
  push_cast
  nlinarith

theorem levelNum_strictMono (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) :
    StrictMono (levelNum φ N M q) :=
  strictMono_nat_of_lt_succ (levelNum_lt_succ φ N M q)

theorem level_strictMono (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) :
    StrictMono (level φ N M q) := by
  intro j j' h
  unfold level
  have hMQ : (0 : ℚ) < M := by exact_mod_cast hM
  exact div_lt_div_of_pos_right (by exact_mod_cast levelNum_strictMono φ N M q h) hMQ

theorem level_monotone (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) :
    Monotone (level φ N M q) :=
  (level_strictMono φ N hM q).monotone

/-- The real levels of one rank are monotone in the cell index. -/
theorem level_cast_monotone (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) (q : Fin m) :
    Monotone fun j => ((level φ N M q j : ℚ) : ℝ) := by
  intro a b h
  exact Rat.cast_le.mpr (level_monotone φ N hM q h)

/-- The numerator of a level of rank `q` is `≡ q (mod m)`. -/
theorem levelNum_emod (φ : Fin m → Inner) (N M : ℕ) (q : Fin m) (j : ℕ) :
    levelNum φ N M q j % m = (q : ℕ) := by
  unfold levelNum
  rw [add_comm, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast q.isLt)

/-- Equal levels come from the same rank and the same cell index. -/
theorem level_injective (φ : Fin m → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) :
    Function.Injective fun qj : Fin m × ℕ => level φ N M qj.1 qj.2 := by
  rintro ⟨q, j⟩ ⟨q', j'⟩ h
  simp only at h
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hnum : levelNum φ N M q j = levelNum φ N M q' j' := by
    unfold level at h
    exact_mod_cast (div_left_inj' hMQ).mp h
  have hq : q = q' := by
    apply Fin.ext
    have h1 := levelNum_emod φ N M q j
    have h2 := levelNum_emod φ N M q' j'
    rw [hnum] at h1
    exact_mod_cast h1.symm.trans h2
  subst hq
  have hj : j = j' := (levelNum_strictMono φ N M q).injective hnum
  rw [hj]

/-- **The cell map is injective** (Hedberg, Lemma 1′ with properties a) and b)): for rationally
independent `λ`, the value `∑_p λ_p · level(q, j_p)` determines the rank `q` and the cell
indices `j⃗`. Stated for `m = 2n + 1` ranks; the case `n = 0` is covered because then there is
a single rank. -/
theorem cellMap_injective {n : ℕ} {lam : Fin n → ℝ} (hlam : LinearIndependent ℚ lam)
    (φ : Fin (2 * n + 1) → Inner) (N : ℕ) {M : ℕ} (hM : 0 < M) :
    Function.Injective fun qj : Fin (2 * n + 1) × (Fin n → ℕ) =>
      ∑ p, lam p * ((level φ N M qj.1 (qj.2 p) : ℚ) : ℝ) := by
  rintro ⟨q, jv⟩ ⟨q', jv'⟩ h
  simp only at h
  -- The difference of the two rational coefficient vectors annihilates `lam`.
  have hsum : ∑ p, (level φ N M q (jv p) - level φ N M q' (jv' p)) • lam p = 0 := by
    have : ∀ p, (level φ N M q (jv p) - level φ N M q' (jv' p)) • lam p =
        lam p * ((level φ N M q (jv p) : ℚ) : ℝ) - lam p * ((level φ N M q' (jv' p) : ℚ) : ℝ) := by
      intro p
      rw [Rat.smul_def]
      push_cast
      ring
    simp only [this, Finset.sum_sub_distrib]
    rw [h, sub_self]
  have hzero := Fintype.linearIndependent_iff.mp hlam _ hsum
  have hlevel : ∀ p, level φ N M q (jv p) = level φ N M q' (jv' p) := fun p =>
    sub_eq_zero.mp (hzero p)
  have hpair : ∀ p, (q, jv p) = (q', jv' p) := fun p => level_injective φ N hM (hlevel p)
  have hjv : jv = jv' := funext fun p => congrArg Prod.snd (hpair p)
  have hq : q = q' := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- `n = 0`: a single rank.
      subst h0
      apply Fin.ext
      have := q.isLt
      have := q'.isLt
      omega
    · exact congrArg Prod.fst (hpair ⟨0, hpos⟩)
  rw [hq, hjv]

end

end MiscMath.Analysis.KolmogorovArnold
