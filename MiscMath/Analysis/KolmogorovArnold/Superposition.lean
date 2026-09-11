/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.InnerSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# The superposition operator and the approximation sets

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 1 of the development. Its declarations are proof:
machine-generated, kernel-checked and axiom-audited, and may be read by no one.

Given constants `λ_1, …, λ_n` and a tuple `ψ = (ψ_0, …, ψ_{2n})` of inner functions on
`I = [0, 1]`, the superposition of an outer function `g : ℝ → ℝ` is

  `x ↦ ∑_{q} g (∑_{p} λ_p ψ_q (x_p))`

on the cube `Iⁿ`. The representation theorem says that for a suitable universal `ψ` every
continuous `f` on the cube is such a superposition. The Baire-category proof (Hedberg 1971,
Kahane 1975) gets there by considering, for one fixed `f`, the set of tuples `ψ` that admit a
*one-step approximation* of `f` — an outer function `g` of norm at most `δ` with
`‖f - ∑_q g ∘ y_q‖ < θ` — and showing that this set is open and dense in the complete metric
space of tuples. This module defines the operator and that set, and proves the openness. The
density is Layer 2, and it is where all the work is.

## What this module proves

Fix `n`, constants `λ : Fin n → ℝ`, and a tuple `ψ` of `2n + 1` monotone continuous functions
`I → ℝ`. Write `y_q(x) = ∑_p λ_p ψ_q(x_p)` for the inner sums, continuous on the cube.

* `superpose λ ψ` is the linear operator `g ↦ ∑_q g ∘ y_q` from bounded continuous functions
  on `ℝ` to continuous functions on the cube; it has norm at most `2n + 1`.
* For a continuous `f` on the cube and reals `δ, θ`, the **approximation set**
  `approxSet λ δ θ f` consists of the tuples `ψ` for which some bounded continuous `g` with
  `‖g‖ ≤ δ` has `‖f - superpose λ ψ g‖ < θ`.
* **Theorem** (`isOpen_approxSet`): `approxSet λ δ θ f` is open in the sup metric on tuples.
  Equivalently, if an outer function `g` works for `ψ`, it works for every tuple close enough
  to `ψ`.

The inner sums and the superposition depend continuously on the tuple `ψ`
(`continuous_innerSum`, `continuous_superpose`), which is the whole content of the openness.

## Source

- T. Hedberg, *The Kolmogorov superposition theorem*, Appendix II to H. S. Shapiro, *Topics
  in Approximation Theory*, Lecture Notes in Math. 187, Springer, 1971, pp. 267–275. The set
  `U_f` of his Lemma 2 (p. 269), for `‖f‖ = 1`: the 5-tuples `(φ_1, …, φ_5)` for which some
  `g ∈ C(ℝ)` has `|g(t)| ≤ 1/7` and `|f(x, y) - ∑_i g(φ_i(x) + λ φ_i(y))| < 7/8`. His openness
  argument is the single sentence "if `g` works for a particular 5-tuple, it does so for all
  sufficiently neighboring 5-tuples". Here the constants are parameters `δ, θ`, the dimension
  is general, and the inner functions are the factored `λ_p ψ_q(x_p)` of his Theorem 1.
- J.-P. Kahane, *Sur le théorème de superposition de Kolmogorov*, J. Approx. Theory 13
  (1975) 229–234. The set `Ω(f)` on p. 231, for `f ≠ 0`: the tuples for which some `h ∈ C(I)`
  satisfies his (6), namely `‖h‖ ≤ ‖f‖` and `‖f - ∑_q h(∑_p λ_p φ_q(x_p))‖ < (1 - ε)‖f‖`;
  "visiblement `Ω(f)` est un ouvert". His bounds are relative to `‖f‖`, ours absolute, which
  is why Layer 2 assumes `‖f‖ ≤ 1`.

## Sanity checks

The `example`s below compute the definitions in the `n = 1` case with the identity inner
functions and `λ = 1` — the inner sums are `x ↦ x_0` and the superposition is `3 g(x_0)` —
and check the approximation sets at their edges: for `f = 0` every tuple is in
`approxSet λ δ θ 0` as soon as `0 ≤ δ` and `0 < θ` (take `g = 0`), and `approxSet λ δ θ f` is
empty when `θ ≤ 0`. The first says the definition is not vacuous; the second that the strict
inequality is really there.

## Relation to Mathlib

The operator is a `ContinuousLinearMap` between Mathlib's Banach spaces `ℝ →ᵇ ℝ`
(`BoundedContinuousFunction`) and `C(Fin n → I, ℝ)`; the openness rests on
`ContinuousMap.continuous_postcomp` and `ContinuousMap.continuous_precomp` from
`Topology/CompactOpen.lean`, which apply because the sup-metric topology on `C(K, ℝ)` for
compact `K` is the compact-open topology. Nothing about superpositions of this shape is in
Mathlib.
-/

open unitInterval BoundedContinuousFunction

namespace MiscMath.Analysis.KolmogorovArnold

variable {n : ℕ}

/-- The coordinate projection `x ↦ x p` as a continuous map on the cube. -/
def proj (p : Fin n) : C(Fin n → I, I) := ⟨fun x => x p, continuous_apply p⟩

@[simp] theorem proj_apply (p : Fin n) (x : Fin n → I) : proj p x = x p := rfl

/-- The `q`-th inner sum `y_q(x) = ∑_p λ_p ψ_q(x_p)`, as a continuous map on the cube. -/
def innerSum (lam : Fin n → ℝ) (ψ : InnerTuple n) (q : Fin (2 * n + 1)) : C(Fin n → I, ℝ) :=
  ∑ p, lam p • ((ψ q : C(I, ℝ)).comp (proj p))

@[simp] theorem innerSum_apply (lam : Fin n → ℝ) (ψ : InnerTuple n) (q : Fin (2 * n + 1))
    (x : Fin n → I) : innerSum lam ψ q x = ∑ p, lam p * (ψ q : C(I, ℝ)) (x p) := by
  simp [innerSum, ContinuousMap.sum_apply]

/-- The inner sums depend continuously on the tuple of inner functions. -/
theorem continuous_innerSum (lam : Fin n → ℝ) (q : Fin (2 * n + 1)) :
    Continuous fun ψ : InnerTuple n => innerSum lam ψ q := by
  unfold innerSum
  refine continuous_finsetSum _ fun p _ => Continuous.const_smul ?_ (lam p)
  exact (ContinuousMap.continuous_precomp (proj p)).comp
    (continuous_subtype_val.comp (continuous_apply q))

/-- The superposition `g ↦ ∑_q g ∘ y_q` as a linear map. -/
def superposeₗ (lam : Fin n → ℝ) (ψ : InnerTuple n) : (ℝ →ᵇ ℝ) →ₗ[ℝ] C(Fin n → I, ℝ) where
  toFun g := ∑ q, g.toContinuousMap.comp (innerSum lam ψ q)
  map_add' g₁ g₂ := by
    ext x
    simp [ContinuousMap.sum_apply, Finset.sum_add_distrib]
  map_smul' c g := by
    ext x
    simp [ContinuousMap.sum_apply, Finset.mul_sum]

theorem norm_superposeₗ_le (lam : Fin n → ℝ) (ψ : InnerTuple n) (g : ℝ →ᵇ ℝ) :
    ‖superposeₗ lam ψ g‖ ≤ (2 * n + 1) * ‖g‖ := by
  calc ‖superposeₗ lam ψ g‖
      = ‖∑ q, g.toContinuousMap.comp (innerSum lam ψ q)‖ := rfl
    _ ≤ ∑ q : Fin (2 * n + 1), ‖g.toContinuousMap.comp (innerSum lam ψ q)‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Fin (2 * n + 1), ‖g‖ :=
        Finset.sum_le_sum fun q _ =>
          (ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun x => g.norm_coe_le_norm _
    _ = (2 * n + 1) * ‖g‖ := by simp

/-- **The superposition operator** `g ↦ ∑_q g ∘ y_q`, a bounded linear map from bounded
continuous functions on the line to continuous functions on the cube. -/
noncomputable def superpose (lam : Fin n → ℝ) (ψ : InnerTuple n) :
    (ℝ →ᵇ ℝ) →L[ℝ] C(Fin n → I, ℝ) :=
  (superposeₗ lam ψ).mkContinuous (2 * n + 1) (norm_superposeₗ_le lam ψ)

theorem superpose_eq_sum (lam : Fin n → ℝ) (ψ : InnerTuple n) (g : ℝ →ᵇ ℝ) :
    superpose lam ψ g = ∑ q, g.toContinuousMap.comp (innerSum lam ψ q) := rfl

@[simp] theorem superpose_apply (lam : Fin n → ℝ) (ψ : InnerTuple n) (g : ℝ →ᵇ ℝ)
    (x : Fin n → I) : superpose lam ψ g x = ∑ q, g (innerSum lam ψ q x) := by
  simp [superpose_eq_sum, ContinuousMap.sum_apply]

theorem norm_superpose_le (lam : Fin n → ℝ) (ψ : InnerTuple n) (g : ℝ →ᵇ ℝ) :
    ‖superpose lam ψ g‖ ≤ (2 * n + 1) * ‖g‖ :=
  norm_superposeₗ_le lam ψ g

/-- For a fixed outer function, the superposition depends continuously on the tuple. -/
theorem continuous_superpose (lam : Fin n → ℝ) (g : ℝ →ᵇ ℝ) :
    Continuous fun ψ : InnerTuple n => superpose lam ψ g := by
  simp only [superpose_eq_sum]
  exact continuous_finsetSum _ fun q _ =>
    (ContinuousMap.continuous_postcomp _).comp (continuous_innerSum lam q)

/-- **The approximation set** `U_f` of Hedberg, `Ω(f)` of Kahane: the tuples `ψ` for which some
outer function of norm at most `δ` brings the superposition within `θ` of `f`. -/
def approxSet (lam : Fin n → ℝ) (δ θ : ℝ) (f : C(Fin n → I, ℝ)) : Set (InnerTuple n) :=
  {ψ | ∃ g : ℝ →ᵇ ℝ, ‖g‖ ≤ δ ∧ ‖f - superpose lam ψ g‖ < θ}

theorem mem_approxSet {lam : Fin n → ℝ} {δ θ : ℝ} {f : C(Fin n → I, ℝ)} {ψ : InnerTuple n} :
    ψ ∈ approxSet lam δ θ f ↔ ∃ g : ℝ →ᵇ ℝ, ‖g‖ ≤ δ ∧ ‖f - superpose lam ψ g‖ < θ :=
  Iff.rfl

/-- **The approximation set is open** (Hedberg, Lemma 2; Kahane, p. 231): an outer function
that works for `ψ` works for every tuple close enough to `ψ`. -/
theorem isOpen_approxSet (lam : Fin n → ℝ) (δ θ : ℝ) (f : C(Fin n → I, ℝ)) :
    IsOpen (approxSet lam δ θ f) := by
  have h : approxSet lam δ θ f =
      ⋃ g ∈ {g : ℝ →ᵇ ℝ | ‖g‖ ≤ δ}, (fun ψ => superpose lam ψ g) ⁻¹' Metric.ball f θ := by
    ext ψ
    simp only [approxSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Metric.mem_ball,
      dist_eq_norm, norm_sub_rev (superpose lam ψ _) f, exists_prop]
  rw [h]
  exact isOpen_biUnion fun g _ => Metric.isOpen_ball.preimage (continuous_superpose lam g)

/-! ## Sanity checks -/

section SanityChecks

/-- The `n = 1` tuple with every inner function the identity. -/
private def idTuple : InnerTuple 1 := fun _ => Inner.id

/-- With `λ = 1` and identity inner functions, every inner sum is `x ↦ x_0`. -/
example (q : Fin 3) (x : Fin 1 → I) : innerSum (fun _ => (1 : ℝ)) idTuple q x = x 0 := by
  simp [idTuple]

/-- ... and the superposition of `g` is `3 g(x_0)`. -/
example (g : ℝ →ᵇ ℝ) (x : Fin 1 → I) :
    superpose (fun _ => (1 : ℝ)) idTuple g x = 3 * g (x 0) := by
  simp [idTuple]

/-- The approximation set is not vacuous: for `f = 0`, with `0 ≤ δ` and `0 < θ`, every tuple
belongs to it (take `g = 0`). -/
example (lam : Fin n → ℝ) {δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : 0 < θ) (ψ : InnerTuple n) :
    ψ ∈ approxSet lam δ θ 0 :=
  ⟨0, by simpa using hδ, by simpa using hθ⟩

/-- The strict inequality is real: for `θ ≤ 0` the approximation set is empty. -/
example (lam : Fin n → ℝ) (δ : ℝ) {θ : ℝ} (hθ : θ ≤ 0) (f : C(Fin n → I, ℝ)) :
    approxSet lam δ θ f = ∅ := by
  ext ψ
  simp only [mem_approxSet, Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_lt]
  intro g _
  exact hθ.trans (norm_nonneg _)

end SanityChecks

end MiscMath.Analysis.KolmogorovArnold
