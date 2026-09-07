/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Geometry.SphereCoveringExponent

/-!
# The Challenge statements agree with the library

`Palomar/Wyner/Challenge.lean` restates five theorems of
`MiscMath.Geometry.SphereCoveringExponent` without their proofs, so that Palomar's
Comparator can check the shipped proofs against an independently readable statement
surface. Two copies of a statement can drift apart, and Comparator would only report it
at submission time.

Each `example` below ascribes a type **copied by hand from `Challenge.lean`** to the
theorem the library ships, and it is worth being exact about the limit of that. This module
never reads `Challenge.lean`, so an edit made there and nowhere else is invisible here.
What it does catch is a library statement that has moved away from what the Challenge
advertises, and a Challenge edit propagated here but not into the library; a wrong edit
made identically here and in the Challenge would pass. Comparator compares the two actual
modules and is the check Palomar records — this is a local convenience that fails earlier
and more cheaply. Every `example` here must elaborate, and none may use `sorry`, since each
asserts a real theorem of the library.

This module is deliberately outside `MiscMath/`, so it reaches neither `MiscMath/Audit.lean`
nor the three checks in `scripts/`, all of which are scoped to that directory. Build it with
`lake build PalomarWynerTypeCheck`.
-/

noncomputable section

open Filter Topology Real InnerProductGeometry

example : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V},
    ‖x‖ = 1 → ‖y‖ = 1 → dist x y = 2 * Real.sin (angle x y / 2) :=
  @MiscMath.Geometry.dist_eq_two_mul_sin_angle_div_two

example : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V},
    ‖x‖ = 1 → ‖y‖ = 1 → ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ π →
      (angle x y ≤ θ ↔ dist x y ≤ 2 * Real.sin (θ / 2)) :=
  @MiscMath.Geometry.angle_le_iff_dist_le

example : ∀ {θ : ℝ}, 0 < θ → θ < π / 2 →
    Tendsto
      (fun n : ℕ =>
        Real.log ((Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
            (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toNat : ℝ) / (n : ℝ))
      atTop (𝓝 (-Real.log (Real.sin θ))) :=
  @MiscMath.Geometry.tendsto_log_coveringNumber_sphere_div_atTop

example : ∀ (n : ℕ) {θ : ℝ}, 0 < θ → θ ≤ π →
    Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
  @MiscMath.Geometry.coveringNumber_sphere_ne_top

example : ∀ {n : ℕ}, 1 ≤ n → ∀ {θ : ℝ}, 0 < θ → θ ≤ π →
    0 < (Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toNat :=
  @MiscMath.Geometry.coveringNumber_sphere_pos
