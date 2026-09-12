/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold

/-!
# The Challenge statements agree with the library

`Palomar/KolmogorovArnold/Challenge.lean` restates the three theorems of
`MiscMath.Analysis.KolmogorovArnold` without their proofs, so that Palomar's Comparator can
check the shipped proofs against an independently readable statement surface. Two copies of
a statement can drift apart, and Comparator would only report it at submission time.

Each `example` below ascribes a type **copied by hand from `Challenge.lean`** to the
theorem the library ships, and it is worth being exact about the limit of that. This module
never reads `Challenge.lean`, so an edit made there and nowhere else is invisible here.
What it does catch is a library statement that has moved away from what the Challenge
advertises, and a Challenge edit propagated here but not into the library; a wrong edit
made identically here and in the Challenge would pass. Comparator compares the two actual
modules and is the check Palomar records — this is a local convenience that fails earlier
and more cheaply. Every `example` here must elaborate, and none may use `sorry`, since each
asserts a real theorem of the library.

This module is deliberately outside `MiscMath/`, so it reaches neither
`MiscMath/Audit.lean` nor the three checks in `scripts/`, all of which are scoped to that
directory. Build it with `lake build PalomarKolmogorovArnoldTypeCheck`.
-/

open Set

example : ∀ n : ℕ,
    ∃ (lam : Fin n → ℝ) (ψ : Fin (2 * n + 1) → ℝ → ℝ),
      (∀ p, 0 < lam p) ∧
      (∀ q, Continuous (ψ q)) ∧
      (∀ q, StrictMono (ψ q)) ∧
      ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ g : ℝ → ℝ, Continuous g ∧
          ∀ x ∈ Icc (0 : Fin n → ℝ) 1, f x = ∑ q, g (∑ p, lam p * ψ q (x p)) :=
  MiscMath.Analysis.kolmogorov_arnold_lorentz_sprecher

example : ∀ n : ℕ,
    ∃ φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ,
      (∀ q p, Continuous (φ q p)) ∧
      (∀ q p, Monotone (φ q p)) ∧
      ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ Φ : ℝ → ℝ, Continuous Φ ∧
          ∀ x ∈ Icc (0 : Fin n → ℝ) 1, f x = ∑ q, Φ (∑ p, φ q p (x p)) :=
  MiscMath.Analysis.kolmogorov_arnold_lorentz

example : ∀ n : ℕ,
    ∃ φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ,
      (∀ q p, Continuous (φ q p)) ∧
      ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Icc 0 1) →
        ∃ Φ : Fin (2 * n + 1) → ℝ → ℝ, (∀ q, Continuous (Φ q)) ∧
          ∀ x ∈ Icc (0 : Fin n → ℝ) 1, f x = ∑ q, Φ q (∑ p, φ q p (x p)) :=
  MiscMath.Analysis.kolmogorov_arnold
