/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.InnerSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.ProjIcc

/-!
# Extending inner functions from `[0, 1]` to `ℝ`

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start. Its declarations are proof: machine-generated, kernel-checked and
axiom-audited, and may be read by no one.

The Baire-category argument produces inner functions on `I = [0, 1]`; the theorem is stated with
inner functions continuous and strictly increasing on all of `ℝ`. The extension used is

  `Inner.extend φ t = φ (clamp t) + (t - clamp t)`,

where `clamp` is Mathlib's `Set.projIcc 0 1`. It agrees with `φ` on `I` (`extend_of_mem`), is
continuous (`continuous_extend`), and is strictly increasing whenever `φ` is
(`extend_strictMono`): off `I` the second term increases strictly, and on `I` the first does.
-/

open Set unitInterval

namespace MiscMath.Analysis.KolmogorovArnold

namespace Inner

/-- The extension of an inner function from `I` to `ℝ`: `ψ(clamp t) + (t - clamp t)`. It agrees
with `ψ` on `I`, is continuous, and is strictly increasing whenever `ψ` is: off `I` the second
term increases strictly, and on `I` the first does. -/
noncomputable def extend (φ : Inner) (t : ℝ) : ℝ :=
  (φ : C(I, ℝ)) (projIcc 0 1 zero_le_one t) + (t - (projIcc 0 1 zero_le_one t : ℝ))

theorem extend_of_mem (φ : Inner) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    φ.extend t = (φ : C(I, ℝ)) ⟨t, ht⟩ := by
  unfold extend
  rw [projIcc_of_mem _ ht]
  simp

theorem continuous_extend (φ : Inner) : Continuous φ.extend := by
  unfold extend
  exact ((φ : C(I, ℝ)).continuous.comp continuous_projIcc).add
    (continuous_id.sub (continuous_subtype_val.comp continuous_projIcc))

theorem extend_strictMono (φ : Inner) (hφ : StrictMono (φ : C(I, ℝ))) : StrictMono φ.extend := by
  intro a b hab
  unfold extend
  have hmono : projIcc (0 : ℝ) 1 zero_le_one a ≤ projIcc 0 1 zero_le_one b :=
    monotone_projIcc _ hab.le
  have hlip : (projIcc (0 : ℝ) 1 zero_le_one b : ℝ) - projIcc 0 1 zero_le_one a ≤ b - a := by
    have := Set.abs_projIcc_sub_projIcc (zero_le_one : (0 : ℝ) ≤ 1) (c := b) (d := a)
    rwa [abs_of_nonneg (sub_nonneg.mpr (Subtype.coe_le_coe.mpr hmono)),
      abs_of_pos (sub_pos.mpr hab)] at this
  rcases hmono.lt_or_eq with hlt | heq
  · have := hφ hlt
    linarith
  · rw [heq]
    linarith

end Inner

end MiscMath.Analysis.KolmogorovArnold
