/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The inner-function space

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 1 of the development. Its declarations are proof:
machine-generated, kernel-checked and axiom-audited, and may be read by no one.

The Baire-category proof of the superposition theorem (Hedberg 1971, Kahane 1975) works in a
complete metric space of candidate inner functions and shows that the tuples which work are
residual. This module fixes that space:

* `monoMaps`, the monotone elements of `C(I, ℝ)`, a closed set;
* `Inner`, that set as a type — Hedberg's `H` (his Remark 2) and Kahane's `Φ` without his
  normalisation `φ(0) = 0`, `φ(1) = 1`, which is a proof device we do not need — complete
  because closed subsets of complete spaces are complete;
* `InnerTuple n`, the `2n + 1`-fold product with the sup metric, which is complete and
  therefore a Baire space.

Everything past the closedness proof is an instance Mathlib already supplies. Here `I` is
Mathlib's `unitInterval`, so an inner function is a function on `[0, 1]`; extending to `ℝ` is
the last layer's business.
-/

open unitInterval

namespace MiscMath.Analysis.KolmogorovArnold

/-- The monotone (non-decreasing) continuous real functions on `I`, as a set in `C(I, ℝ)`. -/
def monoMaps : Set C(I, ℝ) := {φ | Monotone φ}

/-- `monoMaps` is the intersection over `a ≤ b` of the closed conditions `φ a ≤ φ b`. -/
theorem monoMaps_eq_iInter :
    monoMaps = ⋂ (a : I) (b : I) (_ : a ≤ b), {φ : C(I, ℝ) | φ a ≤ φ b} := by
  ext φ
  simp only [monoMaps, Set.mem_ofPred_eq, Set.mem_iInter]
  exact ⟨fun h a b hab => h hab, fun h a b hab => h a b hab⟩

theorem isClosed_monoMaps : IsClosed monoMaps := by
  rw [monoMaps_eq_iInter]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
  exact isClosed_le (continuous_eval_const a) (continuous_eval_const b)

/-- The inner-function space `H`: monotone continuous functions `I → ℝ` with the sup metric. -/
abbrev Inner : Type := monoMaps

instance : CompleteSpace Inner := isClosed_monoMaps.isComplete.completeSpace_coe

/-- The space of `2n + 1`-tuples of inner functions, with the sup metric. -/
abbrev InnerTuple (n : ℕ) : Type := Fin (2 * n + 1) → Inner

namespace Inner

/-- An inner function is monotone. -/
theorem monotone (φ : Inner) : Monotone (φ : C(I, ℝ)) := φ.2

/-- An inner function is continuous. -/
theorem continuous (φ : Inner) : Continuous (φ : C(I, ℝ)) := (φ : C(I, ℝ)).continuous

/-- The identity `t ↦ t` as an inner function. -/
def id : Inner := ⟨⟨Subtype.val, continuous_subtype_val⟩, fun _ _ h => h⟩

@[simp] theorem coe_id_apply (t : I) : (id : C(I, ℝ)) t = t := rfl

instance : Nonempty Inner := ⟨id⟩

/-- Adding a non-negative multiple of the identity to an inner function. -/
def addSmulId (φ : Inner) (c : ℝ) (hc : 0 ≤ c) : Inner :=
  ⟨(φ : C(I, ℝ)) + c • (id : C(I, ℝ)), fun a b hab => by
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, coe_id_apply, smul_eq_mul]
    exact add_le_add (φ.monotone hab) (mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hab) hc)⟩

@[simp] theorem addSmulId_apply (φ : Inner) (c : ℝ) (hc : 0 ≤ c) (t : I) :
    (addSmulId φ c hc : C(I, ℝ)) t = (φ : C(I, ℝ)) t + c * t := by
  simp [addSmulId]

/-- The perturbation `φ + c • id` is within `|c|` of `φ`. -/
theorem dist_addSmulId_le (φ : Inner) (c : ℝ) (hc : 0 ≤ c) : dist (addSmulId φ c hc) φ ≤ c := by
  rw [Subtype.dist_eq, ContinuousMap.dist_le hc]
  intro t
  rw [addSmulId_apply, Real.dist_eq, add_sub_cancel_left, abs_of_nonneg (mul_nonneg hc t.2.1)]
  exact mul_le_of_le_one_right hc t.2.2

end Inner

/-- The tuple space is a Baire space, being complete and metrisable. Recorded as an `example`
because it is exactly what the Baire step of the proof needs and it comes for free. -/
example (n : ℕ) : BaireSpace (InnerTuple n) := inferInstance

end MiscMath.Analysis.KolmogorovArnold
