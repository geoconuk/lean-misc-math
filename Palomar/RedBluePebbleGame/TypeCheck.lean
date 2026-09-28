/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
module

import MiscMath.Computability.RedBluePebbleGame

/-!
# The Challenge statements agree with the library

`Palomar/RedBluePebbleGame/Challenge.lean` restates the thirteen theorems of
`MiscMath.Computability.RedBluePebbleGame` without their proofs, together with the twelve
definitions they are stated through, so that Palomar's Comparator can check the shipped proofs
against an independently readable statement surface. Two copies of a statement can drift apart,
and Comparator would only report it at submission time.

Each `example` below ascribes a type **copied by hand from `Challenge.lean`** to the theorem the
library ships, and it is worth being exact about the limit of that. This module never reads
`Challenge.lean`, so an edit made there and nowhere else is invisible here. What it does catch is
a library statement that has moved away from what the Challenge advertises, and a Challenge edit
propagated here but not into the library; a wrong edit made identically here and in the Challenge
would pass. Comparator compares the two actual modules and is the check Palomar records — this is
a local convenience that fails earlier and more cheaply. Every `example` here must elaborate, and
none may use `sorry`, since each asserts a real theorem of the library.

Nor can this module see the Challenge's copies of the definitions. The Challenge declares them
under the library's own names, so the two cannot be imported together, and every `example` here
is elaborated against the library's definitions in `Spec.lean`. What keeps the two copies the
same is that the Challenge's are copied from `Spec.lean` byte for byte, and that the two files
import the same Mathlib modules in the same order, so that each definition elaborates to the same
term in both. Comparator requires exactly that: every declaration a compared statement uses must
be the same declaration in the Challenge and the Solution. A type ascription could not check it,
since it holds up to definitional unfolding, and a copy that elaborated to a different but
definitionally equal term would pass here and fail Comparator.

This module is deliberately outside `MiscMath/`, so it reaches neither `MiscMath/Audit.lean` nor
the three checks in `scripts/`, all of which are scoped to that directory. Build it with
`lake build PalomarRedBluePebbleGameTypeCheck`.
-/

open Filter MiscMath.Computability.RedBluePebbleGame

example : ∀ {V : Type*} [DecidableEq V] [Finite V] {E : V → V → Prop} {I O : Finset V} {S q : ℕ},
    IsComputationDAG E I O → HasCompleteCalculation E I O S q →
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S :=
  @MiscMath.Computability.exists_partition_of_hasCompleteCalculation

example : ∀ {V : Type*} [DecidableEq V] [Finite V] {E : V → V → Prop} {I O : Finset V}
    {S q h₀ : ℕ}, IsComputationDAG E I O →
    (∀ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P → h₀ ≤ h) →
    HasCompleteCalculation E I O S q →
    S * h₀ ≤ q + S :=
  @MiscMath.Computability.io_lower_bound_of_parts

example : ∀ {V : Type*} [DecidableEq V] [Finite V] {E : V → V → Prop} {I O : Finset V} {S : ℕ},
    IsComputationDAG E I O → (∃ q, HasCompleteCalculation E I O S q) →
    (S : ℤ) * (minParts E I (2 * S) - 1) ≤ minIOTime E I O S :=
  @MiscMath.Computability.minIOTime_lower_bound

example : ∀ {k S h : ℕ}, 1 ≤ S → ∀ {P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k))},
    IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P →
    (2 : ℝ) ^ k * (k + 1) ≤ h * (S * Real.logb 2 (2 * S)) :=
  @MiscMath.Computability.fft_parts_lower_bound

example :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1) / (p.2 * Real.log p.2))
      =O[𝓟 {p | 1 ≤ p.1 ∧ 2 ≤ p.2}]
      fun p => (minDominatorParts (fftEdge p.1) (Finset.univ.filter (·.1 = 0)) p.2 : ℝ) :=
  MiscMath.Computability.fft_parts_lower_bound_isBigO

example : ∀ {k S : ℕ}, 1 ≤ k →
    ((∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) ↔ 3 ≤ S) :=
  @MiscMath.Computability.fft_complete_iff

example : ∀ {k S q : ℕ}, 1 ≤ k → 1 ≤ S →
    HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q →
    2 ^ (k + 1) ≤ q ∧ (2 : ℝ) ^ k * (k + 1) / (2 * Real.logb 2 (4 * S)) - S ≤ q :=
  @MiscMath.Computability.fft_io_bounds

example : ∀ {k S q : ℕ}, 1 ≤ k → 3 ≤ S →
    HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q →
    (2 : ℝ) ^ k * k ≤ 5 * q * Real.logb 2 S :=
  @MiscMath.Computability.fft_io_lower_bound

example :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1)) =O[𝓟 {p | 1 ≤ p.1 ∧ 3 ≤ p.2}]
      fun p => (minIOTime (fftEdge p.1) (Finset.univ.filter (·.1 = 0))
        (Finset.univ.filter (·.1 = Fin.last p.1)) p.2 : ℝ) * Real.log p.2 :=
  MiscMath.Computability.fft_io_lower_bound_isBigO

example : ∀ {m k n : ℕ}, 1 ≤ m → 1 ≤ k → 1 ≤ n →
    ∃ (V : Type) (_ : DecidableEq V) (_ : Finite V) (E : V → V → Prop) (I O : Finset V),
      IsMatMulEvaluation m k n E I O ∧ ∀ S, (∃ q, HasCompleteCalculation E I O S q) ↔ 3 ≤ S :=
  @MiscMath.Computability.exists_isMatMulEvaluation

example : ∀ {V : Type*} [DecidableEq V] [Finite V] {E : V → V → Prop} {I O : Finset V}
    {m k n S q : ℕ}, 1 ≤ k → 1 ≤ S → IsMatMulEvaluation m k n E I O →
    HasCompleteCalculation E I O S q →
    m * k + k * n + m * n ≤ q ∧ (m * k * n : ℝ) / Real.sqrt (2 * S) - S ≤ q :=
  @MiscMath.Computability.matMul_io_bounds

example : ∀ {V : Type*} [DecidableEq V] [Finite V] {E : V → V → Prop} {I O : Finset V}
    {m k n S q : ℕ}, IsMatMulEvaluation m k n E I O → HasCompleteCalculation E I O S q →
    (m * k * n : ℝ) ≤ 2 * q * Real.sqrt S :=
  @MiscMath.Computability.matMul_io_lower_bound

example : ∀ {ι : Type*} {m k n : ι → ℕ} {W : ι → Type*} [∀ i, DecidableEq (W i)]
    [∀ i, Finite (W i)] {E : ∀ i, W i → W i → Prop} {I O : ∀ i, Finset (W i)},
    (∀ i, IsMatMulEvaluation (m i) (k i) (n i) (E i) (I i) (O i)) →
    (fun x : ι × ℕ => (m x.1 * k x.1 * n x.1 : ℝ))
      =O[𝓟 {x | ∃ q, HasCompleteCalculation (E x.1) (I x.1) (O x.1) x.2 q}]
      fun x => (minIOTime (E x.1) (I x.1) (O x.1) x.2 : ℝ) * Real.sqrt x.2 :=
  @MiscMath.Computability.matMul_io_lower_bound_isBigO
