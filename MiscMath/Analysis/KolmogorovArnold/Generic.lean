/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.Density
import MiscMath.Analysis.KolmogorovArnold.StrictlyIncreasing
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The Baire step: a generic tuple approximates every function in one step

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 3 of the development. Its declarations are proof:
machine-generated, kernel-checked and axiom-audited, and may be read by no one.

Layer 1 made the approximation sets `U_f` open and Layer 2 made them dense, for every `f` in
the closed unit ball of `C(Iⁿ, ℝ)`. That ball is separable, so the intersection of the `U_h`
over a countable dense set of `h` is a dense `Gδ` in the complete metric space of tuples
(Baire); so is the set of tuples with strictly increasing components (Layer 1), and two dense
`Gδ`s meet. A tuple `ψ` in the intersection approximates *every* continuous `f` in one step,
with `‖g‖` and the error both proportional to `‖f‖`: this is Hedberg's Lemma 3, and it is the
input to the iteration of Layer 4.

## What this module proves

Fix `n` and constants `λ : Fin n → ℝ` linearly independent over `ℚ`. There is a tuple
`ψ = (ψ_0, …, ψ_{2n})` of continuous **strictly increasing** functions `[0,1] → ℝ`, and
constants `c ≥ 0` and `0 ≤ θ < 1`, such that for every continuous `f : [0,1]ⁿ → ℝ` there is a
bounded continuous `g : ℝ → ℝ` with `‖g‖ ≤ c ‖f‖` and
`sup_{x ∈ [0,1]ⁿ} |f(x) - ∑_q g(∑_p λ_p ψ_q(x_p))| ≤ θ ‖f‖` (`exists_generic_tuple`). The proof
gives `c = 1/(2n+3)` and `θ = (8n+11)/(8n+12)`; at `n = 2` these are Hedberg's `1/7` and a
`θ` between his `7/8` and `8/9`.

The tuple does not depend on `f` — that is the point — and it comes from a residual set, so
"quasi-every" tuple of monotone inner functions would do.

## Source

T. Hedberg, *The Kolmogorov superposition theorem*, Appendix II to H. S. Shapiro, *Topics in
Approximation Theory*, Lecture Notes in Math. 187, Springer, 1971, Lemma 3, p. 271: "there exist
`φ_1, …, φ_5 ∈ C(I)` such that, given `f ∈ C(I²)`, there exists `g ∈ C(ℝ)` satisfying
`|g(t)| ≤ (1/7)‖f‖` and `‖f - ∑_i g ∘ t_i‖ ≤ (8/9)‖f‖`", proved by intersecting the `U_{h_j}`
over a sequence `(h_j)` dense in the unit sphere of `C(I²)` and appealing to Baire's theorem.
The strict monotonicity of the components is Kahane's remark (J. Approx. Theory 13 (1975),
p. 231), imported from `StrictlyIncreasing.lean` through `Dense.inter_of_Gδ`; Hedberg's Remark 2
(p. 272) obtains non-decreasing components by running the same argument in the closed subspace
`H`, which is where `Inner` lives from the outset.

## Sanity checks

The theorem has one hypothesis, the rational independence of `λ`, and Layer 0 supplies a
witness (`exists_pos_linearIndependent_rat`), so the `example` below instantiates the theorem
at every `n`. A second `example` records the countable dense subset of the closed unit ball
that the proof intersects over, since separability of `C(Iⁿ, ℝ)` is what makes the Baire
family countable.

## Relation to Mathlib

Uses `BaireSpace` for the complete metric space of tuples (through `dense_biInter_of_isOpen`),
`Dense.inter_of_Gδ`, and `ContinuousMap.instSecondCountableTopology` for separability of
`C(Iⁿ, ℝ)`. Nothing about superpositions is in Mathlib.
-/

open unitInterval Set Topology BoundedContinuousFunction

namespace MiscMath.Analysis.KolmogorovArnold

variable {n : ℕ}

/-- The closed unit ball of `C(Iⁿ, ℝ)` has a countable subset dense in it. -/
theorem exists_countable_dense_unitBall :
    ∃ D : Set C(Fin n → I, ℝ), D.Countable ∧ (∀ h ∈ D, ‖h‖ ≤ 1) ∧
      ∀ f : C(Fin n → I, ℝ), ‖f‖ ≤ 1 → ∀ r > 0, ∃ h ∈ D, ‖f - h‖ < r := by
  obtain ⟨t, htc, htd⟩ :=
    TopologicalSpace.exists_countable_dense (Metric.closedBall (0 : C(Fin n → I, ℝ)) 1)
  refine ⟨Subtype.val '' t, htc.image _, ?_, ?_⟩
  · rintro h ⟨y, -, rfl⟩
    exact mem_closedBall_zero_iff.mp y.2
  · intro f hf r hr
    have hfmem : f ∈ Metric.closedBall (0 : C(Fin n → I, ℝ)) 1 := mem_closedBall_zero_iff.mpr hf
    obtain ⟨y, hy, hyt⟩ := Metric.dense_iff.mp htd ⟨f, hfmem⟩ r hr
    refine ⟨y, ⟨y, hyt, rfl⟩, ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, dist_comm, dist_eq_norm] at hy
    exact hy

/-- **A generic tuple approximates every `f` in one step** (Hedberg, Lemma 3). For `λ` linearly
independent over `ℚ` there are a tuple `ψ` of continuous strictly increasing inner functions
and constants `c ≥ 0`, `0 ≤ θ < 1`, such that every continuous `f` on the cube has an outer
`g` with `‖g‖ ≤ c ‖f‖` and `‖f - ∑_q g ∘ y_q‖ ≤ θ ‖f‖`. -/
theorem exists_generic_tuple {lam : Fin n → ℝ} (hlam : LinearIndependent ℚ lam) :
    ∃ ψ : InnerTuple n, (∀ q, StrictMono (ψ q : C(I, ℝ))) ∧
      ∃ c θ : ℝ, 0 ≤ c ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ f : C(Fin n → I, ℝ), ∃ g : ℝ →ᵇ ℝ,
        ‖g‖ ≤ c * ‖f‖ ∧ ‖f - superpose lam ψ g‖ ≤ θ * ‖f‖ := by
  obtain ⟨D, hDc, hD1, hDd⟩ := exists_countable_dense_unitBall (n := n)
  set δ : ℝ := 1 / (2 * n + 3) with hδ
  set θ₁ : ℝ := (4 * n + 5) / (4 * n + 6) with hθ₁def
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hθ₁ : (2 * n + 2) / (2 * n + 3) < θ₁ := by
    rw [hθ₁def, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hθ₁0 : 0 ≤ θ₁ := by positivity
  have hθ₁1 : θ₁ < 1 := by
    rw [hθ₁def, div_lt_one (by positivity)]
    linarith
  -- The Baire intersection over the countable dense set, meeting the strictness `Gδ`.
  have hVopen : ∀ h ∈ D, IsOpen (approxSet lam δ θ₁ h) := fun h _ => isOpen_approxSet _ _ _ _
  have hV : Dense (⋂ h ∈ D, approxSet lam δ θ₁ h) :=
    dense_biInter_of_isOpen hVopen hDc fun h hh => dense_approxSet hlam (hD1 h hh) hθ₁
  have hVGδ : IsGδ (⋂ h ∈ D, approxSet lam δ θ₁ h) := IsGδ.biInter_of_isOpen hDc hVopen
  obtain ⟨G, hGδ, hGd, hG⟩ := exists_isGδ_dense_strictMono_tuple n
  obtain ⟨ψ, hψV, hψG⟩ := (hV.inter_of_Gδ hVGδ hGδ hGd).nonempty
  refine ⟨ψ, hG ψ hψG, δ, (θ₁ + 1) / 2, by positivity, by positivity, by linarith, ?_⟩
  intro f
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0], by simp [hf0]⟩
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  -- Normalise, approximate the normalised function by an element of `D`, and scale back.
  set f₁ : C(Fin n → I, ℝ) := ‖f‖⁻¹ • f with hf₁
  have hf₁norm : ‖f₁‖ = 1 := by
    rw [hf₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hfpos.ne']
  obtain ⟨h, hhD, hfh⟩ := hDd f₁ hf₁norm.le ((1 - θ₁) / 2) (by linarith)
  have hψh : ψ ∈ approxSet lam δ θ₁ h := mem_iInter₂.mp hψV h hhD
  obtain ⟨g₁, hg₁, hg₁h⟩ := hψh
  refine ⟨‖f‖ • g₁, ?_, ?_⟩
  · rw [norm_smul, norm_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right hg₁ hfpos.le
  · have hlin : superpose lam ψ (‖f‖ • g₁) = ‖f‖ • superpose lam ψ g₁ :=
      (superpose lam ψ).map_smul _ _
    have hf : ‖f‖ • f₁ = f := by
      rw [hf₁, smul_smul, mul_inv_cancel₀ hfpos.ne', one_smul]
    have hkey : f - superpose lam ψ (‖f‖ • g₁) = ‖f‖ • (f₁ - superpose lam ψ g₁) := by
      rw [hlin, smul_sub, hf]
    have htri : ‖f₁ - superpose lam ψ g₁‖ ≤ (1 - θ₁) / 2 + θ₁ :=
      (norm_sub_le_norm_sub_add_norm_sub f₁ h _).trans (add_le_add hfh.le hg₁h.le)
    calc ‖f - superpose lam ψ (‖f‖ • g₁)‖ = ‖f‖ * ‖f₁ - superpose lam ψ g₁‖ := by
          rw [hkey, norm_smul, norm_norm]
      _ ≤ ‖f‖ * ((1 - θ₁) / 2 + θ₁) := mul_le_mul_of_nonneg_left htri hfpos.le
      _ = (θ₁ + 1) / 2 * ‖f‖ := by ring

/-! ## Sanity checks -/

/-- The hypothesis is satisfiable at every `n`, by Layer 0, so the theorem instantiates. -/
example (n : ℕ) : ∃ (lam : Fin n → ℝ) (ψ : InnerTuple n), (∀ q, StrictMono (ψ q : C(I, ℝ))) ∧
    ∃ c θ : ℝ, 0 ≤ c ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ f : C(Fin n → I, ℝ), ∃ g : ℝ →ᵇ ℝ,
      ‖g‖ ≤ c * ‖f‖ ∧ ‖f - superpose lam ψ g‖ ≤ θ * ‖f‖ := by
  obtain ⟨lam, -, hlam⟩ := exists_pos_linearIndependent_rat n
  exact ⟨lam, exists_generic_tuple hlam⟩

/-- Separability of `C(Iⁿ, ℝ)`, the fact that makes the Baire family countable. -/
example (n : ℕ) : TopologicalSpace.SeparableSpace C(Fin n → I, ℝ) := inferInstance

end MiscMath.Analysis.KolmogorovArnold
