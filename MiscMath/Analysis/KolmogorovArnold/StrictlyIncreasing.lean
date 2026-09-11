/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.InnerSpace
import Mathlib.Topology.Baire.Lemmas

/-!
# Quasi-every monotone function is strictly increasing

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 1 of the development, the part that pays for the one clause of
the statement that goes beyond every stated theorem in the literature. Its declarations are
proof: machine-generated, kernel-checked and axiom-audited, and may be read by no one.

The Baire-category proof produces a tuple of inner functions in the complete metric space of
*monotone* continuous functions on `I = [0, 1]`, and the residual set it produces is stable
under intersection with any other dense `Gδ`. Kahane observed that the strictly increasing
functions contain one, so the tuple can be taken strictly increasing at no further cost. This
module proves that
observation, for one function and for tuples.

## What this module proves

In the space `Inner` of monotone continuous functions `I → ℝ` with the sup metric:

* for `a < b` in `I`, the set of `φ` with `φ(a) < φ(b)` is open and dense
  (`isOpen_sepSet`, `dense_sepSet`);
* there is a dense `Gδ` set `G` every member of which is strictly increasing
  (`exists_isGδ_dense_strictMono`);
* for every `n` there is a dense `Gδ` set of `2n + 1`-tuples every component of which is
  strictly increasing (`exists_isGδ_dense_strictMono_tuple`).

"Dense `Gδ`" is what "quasi-every" means in Kahane's usage: a countable intersection of dense
open sets, hence itself dense by the Baire category theorem since the space is complete.

## Source

J.-P. Kahane, *Sur le théorème de superposition de Kolmogorov*, J. Approx. Theory 13 (1975)
229–234, p. 231: "Quasi toute `φ` est strictement croissante, car visiblement, pour tout couple
de rationnels `(ρ, ρ')` tels que `0 ≤ ρ < ρ' ≤ 1`, l'ensemble des `φ` qui vérifient
`φ(ρ + 0) < φ(ρ' − 0)` est un ouvert dense dans `Φ`." His `Φ` is the space of increasing
continuous `φ : I → I` with `φ(0) = 0`, `φ(1) = 1`; here the normalisation is dropped and the
functions are real-valued, which changes nothing in the argument. The countable dense set of
points is taken abstractly rather than as the rationals, and the intersection is over pairs
from it.

Hedberg, *The Kolmogorov superposition theorem* (LNM 187, 1971), Remark 2, p. 272–273, runs the
Baire argument in the closed subspace `H` of non-decreasing functions but does not take the
further step to strictly increasing ones; the theorem's `StrictMono` rests on Kahane's remark
alone, and this module is where that remark is proved.

## Sanity checks

The `example`s below check the two edges of the separating sets: `sepSet a a` is empty (no
function separates a point from itself), and the identity is in `sepSet a b` for every `a < b`,
so the sets whose intersection is taken are non-empty for exactly the pairs that matter. The
main theorems are existence statements with no hypotheses, so there is no satisfiability
witness to give; the tuple version is instantiated at `n = 2`.

## Relation to Mathlib

Uses `IsGδ.biInter_of_isOpen`, `dense_biInter_of_isOpen` (Baire), `dense_pi`, `IsGδ.preimage`,
and `TopologicalSpace.exists_countable_dense` on `I`. Mathlib has nothing about generic
properties of monotone functions in `C(I, ℝ)`.
-/

open unitInterval Set Topology

namespace MiscMath.Analysis.KolmogorovArnold

/-- The inner functions that strictly separate `a` from `b`: `φ a < φ b`. -/
def sepSet (a b : I) : Set Inner := {φ | (φ : C(I, ℝ)) a < (φ : C(I, ℝ)) b}

theorem mem_sepSet {a b : I} {φ : Inner} : φ ∈ sepSet a b ↔ (φ : C(I, ℝ)) a < (φ : C(I, ℝ)) b :=
  Iff.rfl

theorem isOpen_sepSet (a b : I) : IsOpen (sepSet a b) :=
  isOpen_lt ((continuous_eval_const a).comp continuous_subtype_val)
    ((continuous_eval_const b).comp continuous_subtype_val)

/-- For `a < b`, the separating set is dense: `φ + (r/2) • id` is monotone, within `r` of `φ`,
and separates. -/
theorem dense_sepSet {a b : I} (hab : a < b) : Dense (sepSet a b) := by
  rw [Metric.dense_iff]
  intro φ r hr
  have hr2 : 0 ≤ r / 2 := by positivity
  refine ⟨Inner.addSmulId φ (r / 2) hr2, ?_, ?_⟩
  · rw [Metric.mem_ball]
    exact (Inner.dist_addSmulId_le φ (r / 2) hr2).trans_lt (by linarith)
  · rw [mem_sepSet, Inner.addSmulId_apply, Inner.addSmulId_apply]
    have h1 : (φ : C(I, ℝ)) a ≤ (φ : C(I, ℝ)) b := φ.monotone hab.le
    have h2 : r / 2 * (a : ℝ) < r / 2 * (b : ℝ) :=
      mul_lt_mul_of_pos_left (Subtype.coe_lt_coe.mpr hab) (by positivity)
    linarith

/-- The conditional separating set `{φ | a < b → φ a < φ b}`: the separating set when `a < b`
and everything otherwise. Phrased this way so that it is indexed by all pairs. -/
def sepSet' (a b : I) : Set Inner := {φ | a < b → (φ : C(I, ℝ)) a < (φ : C(I, ℝ)) b}

theorem isOpen_sepSet' (a b : I) : IsOpen (sepSet' a b) := by
  by_cases h : a < b
  · have : sepSet' a b = sepSet a b := by
      ext φ
      simp [sepSet', sepSet, h]
    rw [this]
    exact isOpen_sepSet a b
  · have : sepSet' a b = univ := by
      ext φ
      simp [sepSet', h]
    rw [this]
    exact isOpen_univ

theorem dense_sepSet' (a b : I) : Dense (sepSet' a b) := by
  by_cases h : a < b
  · have : sepSet' a b = sepSet a b := by
      ext φ
      simp [sepSet', sepSet, h]
    rw [this]
    exact dense_sepSet h
  · have : sepSet' a b = univ := by
      ext φ
      simp [sepSet', h]
    rw [this]
    exact dense_univ

/-- Kahane's `Gδ`: the functions separating every pair `a < b` drawn from a set `D`. -/
def strictGδ (D : Set I) : Set Inner := ⋂ ab ∈ D ×ˢ D, sepSet' ab.1 ab.2

theorem isGδ_strictGδ {D : Set I} (hD : D.Countable) : IsGδ (strictGδ D) :=
  IsGδ.biInter_of_isOpen (hD.prod hD) fun ab _ => isOpen_sepSet' ab.1 ab.2

theorem dense_strictGδ {D : Set I} (hD : D.Countable) : Dense (strictGδ D) :=
  dense_biInter_of_isOpen (fun ab _ => isOpen_sepSet' ab.1 ab.2) (hD.prod hD)
    fun ab _ => dense_sepSet' ab.1 ab.2

/-- Between any two points of `I` there is a point of a dense set. -/
theorem exists_mem_Ioo_of_dense {D : Set I} (hD : Dense D) {x y : I} (hxy : x < y) :
    ∃ a ∈ D, x < a ∧ a < y := by
  obtain ⟨a, haD, ha⟩ := hD.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hxy)
  exact ⟨a, haD, ha.1, ha.2⟩

/-- A function separating every pair from a dense set is strictly increasing. -/
theorem strictMono_of_mem_strictGδ {D : Set I} (hD : Dense D) {φ : Inner}
    (hφ : φ ∈ strictGδ D) : StrictMono (φ : C(I, ℝ)) := by
  intro x y hxy
  obtain ⟨a, haD, hxa, hay⟩ := exists_mem_Ioo_of_dense hD hxy
  obtain ⟨b, hbD, hab, hby⟩ := exists_mem_Ioo_of_dense hD hay
  have hsep : (φ : C(I, ℝ)) a < (φ : C(I, ℝ)) b :=
    (mem_iInter₂.mp hφ (a, b) (mk_mem_prod haD hbD)) hab
  calc (φ : C(I, ℝ)) x ≤ (φ : C(I, ℝ)) a := φ.monotone hxa.le
    _ < (φ : C(I, ℝ)) b := hsep
    _ ≤ (φ : C(I, ℝ)) y := φ.monotone hby.le

/-- **Quasi-every monotone continuous function on `I` is strictly increasing** (Kahane 1975,
p. 231): the strictly increasing functions contain a dense `Gδ` of `Inner`. -/
theorem exists_isGδ_dense_strictMono :
    ∃ G : Set Inner, IsGδ G ∧ Dense G ∧ ∀ φ ∈ G, StrictMono (φ : C(I, ℝ)) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense I
  exact ⟨strictGδ D, isGδ_strictGδ hDc, dense_strictGδ hDc,
    fun φ hφ => strictMono_of_mem_strictGδ hDd hφ⟩

/-- **Quasi-every tuple of inner functions is strictly increasing in every component**: for every
`n`, the tuples all of whose `2n + 1` components are strictly increasing contain a dense `Gδ` of
`InnerTuple n`. -/
theorem exists_isGδ_dense_strictMono_tuple (n : ℕ) :
    ∃ G : Set (InnerTuple n), IsGδ G ∧ Dense G ∧ ∀ ψ ∈ G, ∀ q, StrictMono (ψ q : C(I, ℝ)) := by
  obtain ⟨G, hGδ, hGd, hG⟩ := exists_isGδ_dense_strictMono
  refine ⟨univ.pi fun _ => G, ?_, dense_pi univ fun _ _ => hGd, fun ψ hψ q => hG _ (hψ q trivial)⟩
  have h : (univ.pi fun _ => G) = ⋂ q, (fun ψ : InnerTuple n => ψ q) ⁻¹' G := by
    ext ψ
    simp [mem_pi]
  rw [h]
  exact IsGδ.iInter fun q => hGδ.preimage (continuous_apply q)

/-! ## Sanity checks -/

/-- No function separates a point from itself. -/
example (a : I) : sepSet a a = ∅ := by
  ext φ
  simp [sepSet]

/-- The identity separates every pair `a < b`. -/
example {a b : I} (hab : a < b) : Inner.id ∈ sepSet a b := by
  rw [mem_sepSet, Inner.coe_id_apply, Inner.coe_id_apply]
  exact Subtype.coe_lt_coe.mpr hab

/-- The tuple version at `n = 2`: five strictly increasing inner functions, generically. -/
example : ∃ G : Set (InnerTuple 2), IsGδ G ∧ Dense G ∧
    ∀ ψ ∈ G, ∀ q : Fin 5, StrictMono (ψ q : C(I, ℝ)) :=
  exists_isGδ_dense_strictMono_tuple 2

end MiscMath.Analysis.KolmogorovArnold
