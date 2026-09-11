/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.Generic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Iteration to an exact representation

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 4 of the development. Its declarations are proof:
machine-generated, kernel-checked and axiom-audited, and may be read by no one.

Layer 3 produced a tuple `ψ` of strictly increasing inner functions with a one-step
approximation for every `f`: an outer `g` with `‖g‖ ≤ c ‖f‖` and residual
`‖f - ∑_q g ∘ y_q‖ ≤ θ ‖f‖`, `θ < 1`. Iterating on the residual gives outer functions `g_j`
with `‖g_j‖ ≤ c θ^j ‖f‖`, whose sum converges in the Banach space of bounded continuous
functions on the line; the superposition operator is a bounded linear map, so it passes
through the sum, and the images telescope to `f`. Hence every continuous `f` on the cube
**is** a superposition `∑_q g ∘ y_q` — exactly, not approximately — for the same universal `ψ`.

## What this module proves

Fix `n` and constants `λ : Fin n → ℝ` linearly independent over `ℚ`. There is a tuple
`ψ = (ψ_0, …, ψ_{2n})` of continuous strictly increasing functions `[0,1] → ℝ` such that for
**every** continuous `f : [0,1]ⁿ → ℝ` there is a bounded continuous `g : ℝ → ℝ` with
`f(x) = ∑_{q=0}^{2n} g(∑_{p} λ_p ψ_q(x_p))` for all `x ∈ [0,1]ⁿ` (`exists_universal_tuple`).
The inner functions are chosen before `f` and serve every `f`; only `g` depends on `f`.

The iteration itself is stated separately (`exists_eq_superpose_of_step`): any tuple with a
one-step approximation property with constants `c ≥ 0`, `0 ≤ θ < 1` represents every `f`
exactly.

## Source

T. Hedberg, *The Kolmogorov superposition theorem*, Appendix II to H. S. Shapiro, *Topics in
Approximation Theory*, Lecture Notes in Math. 187, Springer, 1971, proof of Theorem 1, pp.
271–272: `f_0 = f`, `f_{j+1} = f_j - ∑_i g_j ∘ t_i` with `g_j` from Lemma 3, so
`‖f_j‖ ≤ (8/9)^j ‖f‖` and `‖g_j‖ ≤ (1/7)(8/9)^j ‖f‖`; "the series `∑ g_j` converges in norm to an
element `g ∈ C(ℝ)`, and we have `f = ∑ (f_j - f_{j+1}) = ∑_i g ∘ t_i`". Kahane, J. Approx.
Theory 13 (1975), p. 231, runs the same induction with `h_j = γ(f_j)`. Both are for the
`n = 2` notation or general `n` verbatim; nothing changes here.

## Sanity checks

`exists_universal_tuple` has one hypothesis, satisfied by Layer 0's `λ`, so the `example`
below instantiates it at every `n`. The `n = 0` case is recorded as well: the cube is a point,
the single inner sum is empty, and the theorem says that a constant is `g(0)` for some bounded
continuous `g`, which is true and content-free — the content starts at `n = 1`, and the theorem
is stated for all `n` so that no hypothesis needs to be checked for vacuity.

## Relation to Mathlib

Uses `Summable.of_norm_bounded` with the geometric series, `ContinuousLinearMap.map_tsum`,
`Summable.hasSum_iff_tendsto_nat` and the telescoping sum `Finset.sum_range_sub'`. Nothing
about superpositions is in Mathlib.
-/

open unitInterval BoundedContinuousFunction Filter Topology

namespace MiscMath.Analysis.KolmogorovArnold

variable {n : ℕ}

/-- **Iteration** (Hedberg, proof of Theorem 1). A tuple with a one-step approximation for every
`f`, with `‖g‖ ≤ c ‖f‖` and residual at most `θ ‖f‖` for a fixed `θ < 1`, represents every `f`
exactly: `f = ∑_q g ∘ y_q` for some bounded continuous `g`. -/
theorem exists_eq_superpose_of_step {lam : Fin n → ℝ} (ψ : InnerTuple n) {c θ : ℝ} (hc : 0 ≤ c)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ f : C(Fin n → I, ℝ), ∃ g : ℝ →ᵇ ℝ,
      ‖g‖ ≤ c * ‖f‖ ∧ ‖f - superpose lam ψ g‖ ≤ θ * ‖f‖)
    (f : C(Fin n → I, ℝ)) : ∃ g : ℝ →ᵇ ℝ, superpose lam ψ g = f := by
  choose G hG using h
  -- The residuals `F 0 = f`, `F (j+1) = F j - S (G (F j))`.
  let F : ℕ → C(Fin n → I, ℝ) := fun j =>
    Nat.rec (motive := fun _ => C(Fin n → I, ℝ)) f (fun _ Fj => Fj - superpose lam ψ (G Fj)) j
  have hF0 : F 0 = f := rfl
  have hFsucc : ∀ j, F (j + 1) = F j - superpose lam ψ (G (F j)) := fun _ => rfl
  have hFnorm : ∀ j, ‖F j‖ ≤ θ ^ j * ‖f‖ := by
    intro j
    induction j with
    | zero => simp [hF0]
    | succ j ih =>
      rw [hFsucc, pow_succ]
      calc ‖F j - superpose lam ψ (G (F j))‖ ≤ θ * ‖F j‖ := (hG (F j)).2
        _ ≤ θ * (θ ^ j * ‖f‖) := mul_le_mul_of_nonneg_left ih hθ0
        _ = θ ^ j * θ * ‖f‖ := by ring
  have hGnorm : ∀ j, ‖G (F j)‖ ≤ c * ‖f‖ * θ ^ j := by
    intro j
    calc ‖G (F j)‖ ≤ c * ‖F j‖ := (hG (F j)).1
      _ ≤ c * (θ ^ j * ‖f‖) := mul_le_mul_of_nonneg_left (hFnorm j) hc
      _ = c * ‖f‖ * θ ^ j := by ring
  -- The outer functions are summable, by comparison with a geometric series.
  have hsum : Summable fun j => G (F j) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ0 hθ1).mul_left (c * ‖f‖)) hGnorm
  refine ⟨∑' j, G (F j), ?_⟩
  rw [(superpose lam ψ).map_tsum hsum]
  -- The images telescope to `f`.
  have hterm : ∀ j, superpose lam ψ (G (F j)) = F j - F (j + 1) := fun j => by
    rw [hFsucc]
    abel
  have hsum' : Summable fun j => superpose lam ψ (G (F j)) := hsum.mapL _
  have hF0lim : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero_norm hFnorm ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const ‖f‖
    simpa using this
  have hhas : HasSum (fun j => superpose lam ψ (G (F j))) f := by
    rw [hsum'.hasSum_iff_tendsto_nat]
    simp_rw [hterm]
    have hpartial : (fun k => ∑ i ∈ Finset.range k, (F i - F (i + 1))) = fun k => f - F k := by
      funext k
      rw [Finset.sum_range_sub', hF0]
    rw [hpartial]
    simpa using tendsto_const_nhds.sub hF0lim
  exact hhas.tsum_eq

/-- **A universal tuple of inner functions, on the cube** (Kolmogorov–Arnold, Lorentz–Sprecher
form, with inner functions on `I` and a bounded outer function). For `λ` linearly independent
over `ℚ` there is a tuple `ψ` of continuous strictly increasing `ψ_q : I → ℝ` such that every
continuous `f` on the cube is `∑_q g (∑_p λ_p ψ_q (x_p))` for some bounded continuous
`g : ℝ → ℝ`. -/
theorem exists_universal_tuple {lam : Fin n → ℝ} (hlam : LinearIndependent ℚ lam) :
    ∃ ψ : InnerTuple n, (∀ q, StrictMono (ψ q : C(I, ℝ))) ∧
      ∀ f : C(Fin n → I, ℝ), ∃ g : ℝ →ᵇ ℝ, superpose lam ψ g = f := by
  obtain ⟨ψ, hψ, c, θ, hc, hθ0, hθ1, h⟩ := exists_generic_tuple hlam
  exact ⟨ψ, hψ, fun f => exists_eq_superpose_of_step ψ hc hθ0 hθ1 h f⟩

/-- The pointwise form of `exists_universal_tuple`: the representation as an identity of
functions on the cube. -/
theorem exists_universal_tuple_apply {lam : Fin n → ℝ} (hlam : LinearIndependent ℚ lam) :
    ∃ ψ : InnerTuple n, (∀ q, StrictMono (ψ q : C(I, ℝ))) ∧
      ∀ f : C(Fin n → I, ℝ), ∃ g : ℝ →ᵇ ℝ,
        ∀ x, f x = ∑ q, g (∑ p, lam p * (ψ q : C(I, ℝ)) (x p)) := by
  obtain ⟨ψ, hψ, h⟩ := exists_universal_tuple hlam
  refine ⟨ψ, hψ, fun f => ?_⟩
  obtain ⟨g, hg⟩ := h f
  refine ⟨g, fun x => ?_⟩
  have := congrArg (fun F : C(Fin n → I, ℝ) => F x) hg
  simp only [superpose_apply, innerSum_apply] at this
  exact this.symm

/-! ## Sanity checks -/

/-- The hypothesis is satisfiable at every `n`, by Layer 0. -/
example (n : ℕ) : ∃ (lam : Fin n → ℝ) (ψ : InnerTuple n), (∀ q, StrictMono (ψ q : C(I, ℝ))) ∧
    ∀ f : C(Fin n → I, ℝ), ∃ g : ℝ →ᵇ ℝ, superpose lam ψ g = f := by
  obtain ⟨lam, -, hlam⟩ := exists_pos_linearIndependent_rat n
  exact ⟨lam, exists_universal_tuple hlam⟩

/-- At `n = 0` the statement is true and content-free: the cube is a point, the inner sum is
empty, and any constant is `g 0` for `g` the constant function. Recorded so the degeneracy is
visible. -/
example (ψ : InnerTuple 0) (f : C(Fin 0 → I, ℝ)) :
    ∃ g : ℝ →ᵇ ℝ, ∀ x, f x = ∑ q, g (∑ p, (Fin.elim0 p : ℝ) * (ψ q : C(I, ℝ)) (x p)) := by
  refine ⟨BoundedContinuousFunction.const ℝ (f (Fin.elim0 ·)), fun x => ?_⟩
  have hx : x = (Fin.elim0 ·) := funext fun p => Fin.elim0 p
  simp [hx]

end MiscMath.Analysis.KolmogorovArnold
