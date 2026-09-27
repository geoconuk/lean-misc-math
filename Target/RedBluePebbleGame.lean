/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Spec
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Prod

/-!
# The red-blue pebble game: the frozen target statements

The advertised statements of `MiscMath.Computability.RedBluePebbleGame`, stated before they
are proved and frozen once read. The `sorry`s are deliberate: this module is the target the
proofs are held to, not a result. It reads only the definitions of
`MiscMath.Computability.RedBluePebbleGame.Spec`. Once proved, the library's theorems are
ascribed to these types, so a statement cannot drift from what was read without a build
failing.

The module is deliberately outside `MiscMath/`, and its library is not in `defaultTargets`,
so it reaches neither `lake build`, `MiscMath/Audit.lean`, nor the three checks in `scripts/`,
all of which are scoped to that directory. Build it with `lake build RedBluePebbleGameTarget`.
-/

open Filter MiscMath.Computability.RedBluePebbleGame

namespace Target.RedBluePebbleGame

theorem fft_io_lower_bound {k S q : ℕ} (hk : 1 ≤ k) (hS : 3 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    (2 : ℝ) ^ k * k ≤ 5 * q * Real.logb 2 S := by
  sorry

theorem fft_io_bounds {k S q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    2 ^ (k + 1) ≤ q ∧ (2 : ℝ) ^ k * (k + 1) / (2 * Real.logb 2 (4 * S)) - S ≤ q := by
  sorry

theorem fft_complete_iff {k S : ℕ} (hk : 1 ≤ k) :
    (∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) ↔ 3 ≤ S := by
  sorry

theorem fft_io_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1)) =O[𝓟 {p | 1 ≤ p.1 ∧ 3 ≤ p.2}]
      fun p => (minIOTime (fftEdge p.1) (Finset.univ.filter (·.1 = 0))
        (Finset.univ.filter (·.1 = Fin.last p.1)) p.2 : ℝ) * Real.log p.2 := by
  sorry

theorem exists_partition_of_hasCompleteCalculation {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q : ℕ} (hG : IsComputationDAG E I O)
    (hq : HasCompleteCalculation E I O S q) :
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S := by
  sorry

theorem io_lower_bound_of_parts {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q h₀ : ℕ} (hG : IsComputationDAG E I O)
    (hparts : ∀ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P → h₀ ≤ h)
    (hq : HasCompleteCalculation E I O S q) :
    S * h₀ ≤ q + S := by
  sorry

theorem minIOTime_lower_bound {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S : ℕ} (hG : IsComputationDAG E I O)
    (hcalc : ∃ q, HasCompleteCalculation E I O S q) :
    (S : ℤ) * (minParts E I (2 * S) - 1) ≤ minIOTime E I O S := by
  sorry

theorem io_lower_bound_of_dominated_card {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q U : ℕ} (hG : IsComputationDAG E I O)
    (hU : ∀ D W : Finset V, D.card ≤ 2 * S → Dominates E I D W → W.card ≤ U)
    (hq : HasCompleteCalculation E I O S q) :
    S * Nat.card V ≤ (q + S) * U := by
  sorry

theorem fft_parts_lower_bound {k S h : ℕ} (hS : 1 ≤ S)
    {P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hP : IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P) :
    (2 : ℝ) ^ k * (k + 1) ≤ h * (S * Real.logb 2 (2 * S)) := by
  sorry

theorem fft_parts_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1) / (p.2 * Real.log p.2))
      =O[𝓟 {p | 1 ≤ p.1 ∧ 2 ≤ p.2}]
      fun p => (minDominatorParts (fftEdge p.1) (Finset.univ.filter (·.1 = 0)) p.2 : ℝ) := by
  sorry

end Target.RedBluePebbleGame
