/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.Localization.Integral
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Positive reals linearly independent over `ℚ`

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 0 of the development. Its declarations are proof:
machine-generated, kernel-checked and axiom-audited, and may be read by no one.

The inner sums of the superposition theorem have the shape `y_q(x) = ∑_l λ_l ψ_q (x_l)`, and
the constants `λ_1, …, λ_n` must be positive and linearly independent over `ℚ`: rational
independence is what stops two distinct points of the cube from being merged by every one of
the `2n + 1` inner sums at once.

Mathlib has no `LinearIndependent ℚ` result about any concrete family of reals, so this is
built here. The route is the cheap one: powers of a transcendental number are linearly
independent over `ℚ` more or less by the definition of transcendence, and Mathlib supplies an
explicit transcendental in `transcendental_liouvilleNumber`.

## What this module proves

For every `n`, there are `n` strictly positive real numbers that are linearly independent
over `ℚ`; that is, no non-trivial rational linear combination of them vanishes
(`exists_pos_linearIndependent_rat`).

## Source

Folklore. The construction — powers of a transcendental number — is the standard one; see
for instance the opening of any treatment of Kolmogorov's superposition theorem, where such
a family is fixed without comment. The transcendental used is Liouville's constant,
Liouville (1844), as formalised in Mathlib's `NumberTheory.Transcendental.Liouville`.

## Sanity checks

`example`s below exhibit the theorem at `n = 3`, and record that the `n = 0` case is
degenerate rather than informative — the empty family is vacuously independent, so the
content of the statement begins at `n = 1`. The theorem has no hypotheses, so there is no
satisfiability witness to give.

## Relation to Mathlib

Mathlib has `linearIndependent_pow` (`RingTheory/PowerBasis.lean`), but it is indexed by
`Fin (minpoly K x).natDegree`, which is `Fin 0` exactly when `x` is transcendental — so it
says nothing here. `Transcendental.linearIndependent_sub_inv`
(`RingTheory/Algebraic/LinearIndependent.lean`) is about the family `(x - a)⁻¹`, not powers.
The power case below appears to be absent.
-/

open Polynomial

namespace MiscMath.Analysis.KolmogorovArnold

/-- A real number transcendental over `ℤ` is transcendental over `ℚ`. -/
theorem transcendental_rat_of_transcendental_int {x : ℝ} (h : Transcendental ℤ x) :
    Transcendental ℚ x :=
  fun ha => h ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr ha)

/-- Distinct powers of a transcendental real are linearly independent over `ℚ`.

Stated with an arbitrary injective exponent family rather than `fun i => x ^ (i : ℕ)`, because
the application needs the exponents `1, …, n` rather than `0, …, n - 1`. -/
theorem linearIndependent_pow_of_transcendental {n : ℕ} {x : ℝ} (hx : Transcendental ℚ x)
    {e : Fin n → ℕ} (he : Function.Injective e) :
    LinearIndependent ℚ (fun i : Fin n => x ^ e i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  -- The relation `∑ i, c i • x ^ e i = 0` says exactly that `x` is a root of this polynomial.
  set p : ℚ[X] := ∑ j, C (c j) * X ^ e j with hp
  have haeval : aeval x p = 0 := by
    rw [hp]
    simpa [Algebra.smul_def] using hc
  have hp0 : p = 0 := by
    by_contra hne
    exact hx ⟨p, hne, haeval⟩
  have hcoeff : p.coeff (e i) = c i := by
    rw [hp, finsetSum_coeff]
    simp [coeff_C_mul, coeff_X_pow, he.eq_iff]
  rw [hp0, coeff_zero] at hcoeff
  exact hcoeff.symm

/-- **Layer 0.** For every `n` there exist `n` strictly positive reals that are linearly
independent over `ℚ`. -/
theorem exists_pos_linearIndependent_rat (n : ℕ) :
    ∃ lam : Fin n → ℝ, (∀ l, 0 < lam l) ∧ LinearIndependent ℚ lam := by
  -- Liouville's constant is transcendental; its absolute value is transcendental and positive.
  set x : ℝ := |liouvilleNumber 2| with hxdef
  have hLt : Transcendental ℚ (liouvilleNumber 2) :=
    transcendental_rat_of_transcendental_int (transcendental_liouvilleNumber (le_refl 2))
  have hx : Transcendental ℚ x := by
    rcases abs_choice (liouvilleNumber 2) with h | h
    · rwa [hxdef, h]
    · rw [hxdef, h]
      intro ha
      exact hLt (by simpa using ha.neg)
  have hne : liouvilleNumber 2 ≠ 0 := fun h0 => hLt (h0 ▸ isAlgebraic_zero)
  have hx0 : 0 < x := by rw [hxdef]; exact abs_pos.mpr hne
  refine ⟨fun l => x ^ ((l : ℕ) + 1), fun l => pow_pos hx0 _, ?_⟩
  exact linearIndependent_pow_of_transcendental hx (fun a b hab => Fin.ext (by omega))

/-! ## Sanity checks -/

example : ∃ lam : Fin 3 → ℝ, (∀ l, 0 < lam l) ∧ LinearIndependent ℚ lam :=
  exists_pos_linearIndependent_rat 3

/-- The `n = 0` case is degenerate: the empty family is vacuously independent, so the content
of the theorem begins at `n = 1`. Recorded so the degeneracy is visible rather than hidden. -/
example : LinearIndependent ℚ (fun _l : Fin 0 => (1 : ℝ)) := by
  simp

end MiscMath.Analysis.KolmogorovArnold
