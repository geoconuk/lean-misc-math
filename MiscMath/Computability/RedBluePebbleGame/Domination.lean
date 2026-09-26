/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Calculation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The red-blue pebble game: windows of a calculation, and what dominates them

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

This is Hong and Kung's key argument (the proof of their Theorem 3.1), in the form the FFT bound
needs and without its partitions. Cut a calculation into windows, each ending once it has made
`S` loads or stores. The vertices given a red pebble in a window are *dominated* — every path
to them from an input meets it — by the at most `2S` vertices that were red at the window's start
or were loaded in it. So if no set dominated by `2S` vertices has more than `U` elements, a
calculation charged `q` gives red pebbles to at most `(q + S) U / S` vertices
(`Trace.mul_card_newReds_le`).

Domination is read with paths of length `0` included: an input is dominated only by a set
containing it.
-/

namespace MiscMath.Computability.RedBluePebbleGame

open Finset Relation

variable {V : Type*} [DecidableEq V] {E : V → V → Prop} {I : Finset V}

omit [DecidableEq V] in
/-- `Dominated E I D v`: every path along `E` from an input to `v` meets `D`, paths of length `0`
included. A path avoiding `D` is a chain of edges none of whose endpoints lies in `D`. -/
def Dominated (E : V → V → Prop) (I D : Finset V) (v : V) : Prop :=
  ∀ x ∈ I, x ∉ D → ¬ ReflTransGen (fun a b => E a b ∧ a ∉ D ∧ b ∉ D) x v

omit [DecidableEq V] in
theorem dominated_of_mem {D : Finset V} {v : V} (hv : v ∈ D) : Dominated E I D v := by
  intro x _ hx h
  rcases h.cases_tail with rfl | ⟨u, -, -, -, hvD⟩
  · exact hx hv
  · exact hvD hv

omit [DecidableEq V] in
/-- A non-input all of whose predecessors are dominated is dominated. -/
theorem Dominated.of_preds {D : Finset V} {v : V} (hvI : v ∉ I)
    (hp : ∀ u, E u v → Dominated E I D u) : Dominated E I D v := by
  intro x hxI hxD h
  rcases h.cases_tail with rfl | ⟨u, hxu, huv, -, -⟩
  · exact hvI hxI
  · exact hp u huv x hxI hxD hxu

namespace Trace

variable {S : ℕ} (T : Trace E I S)

/-- The total charge of the first `j` moves. -/
def charges (j : ℕ) : ℕ := ∑ i ∈ range j, T.c i

theorem charges_succ (j : ℕ) : T.charges (j + 1) = T.charges j + T.c j :=
  Finset.sum_range_succ _ _

theorem charges_mono {j e : ℕ} (h : j ≤ e) : T.charges j ≤ T.charges e :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem charges_add_sum_Ico {j e : ℕ} (h : j ≤ e) :
    T.charges j + ∑ i ∈ Ico j e, T.c i = T.charges e :=
  Finset.sum_range_add_sum_Ico _ h

/-- The vertices given a red pebble by moves `j, …, e - 1`. -/
def newReds (j e : ℕ) : Finset V :=
  (Ico j e).biUnion fun i => (T.σ (i + 1)).1 \ (T.σ i).1

/-- The dominator of the window of moves `j, …, e - 1`: the red pebbles at its start, and the
vertices it loads. -/
def windowDom (j e : ℕ) : Finset V :=
  (T.σ j).1 ∪ ((Ico j e).filter fun i => T.c i = 1).biUnion fun i => (T.σ (i + 1)).1 \ (T.σ i).1

theorem card_windowDom_le {j e : ℕ} (hj : j ≤ T.t) (he : e ≤ T.t) :
    (T.windowDom j e).card ≤ S + ∑ i ∈ Ico j e, T.c i := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add (T.budget j hj) ?_)
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ i ∈ (Ico j e).filter (fun i => T.c i = 1), ((T.σ (i + 1)).1 \ (T.σ i).1).card
      ≤ ∑ i ∈ (Ico j e).filter (fun i => T.c i = 1), T.c i := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_filter, Finset.mem_Ico] at hi
        rw [hi.2]
        exact (T.step i (by omega)).card_sdiff_red_le_one
    _ ≤ ∑ i ∈ Ico j e, T.c i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Every red pebble present during a window is on a vertex its dominator dominates. -/
theorem dominated_of_mem_window {j e : ℕ} (he : e ≤ T.t) :
    ∀ m, j ≤ m → m ≤ e → ∀ v ∈ (T.σ m).1, Dominated E I (T.windowDom j e) v := by
  intro m hjm
  induction m, hjm using Nat.le_induction with
  | base => exact fun _ v hv => dominated_of_mem (Finset.mem_union_left _ hv)
  | succ m hjm ih =>
    intro hme v hv
    by_cases hvm : v ∈ (T.σ m).1
    · exact ih (by omega) v hvm
    · obtain ⟨-, (⟨hc, -⟩ | ⟨-, hvI, hp⟩)⟩ := (T.step m (by omega)).new_red hvm hv
      · refine dominated_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, ?_, ?_⟩))
        · exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hjm, by omega⟩, hc⟩
        · exact Finset.mem_sdiff.2 ⟨hv, hvm⟩
      · exact Dominated.of_preds hvI fun u hu => ih (by omega) u (hp u hu)

theorem dominated_of_mem_newReds {j e : ℕ} (he : e ≤ T.t) {v : V} (hv : v ∈ T.newReds j e) :
    Dominated E I (T.windowDom j e) v := by
  obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.1 hv
  rw [Finset.mem_Ico] at hi
  exact T.dominated_of_mem_window he (i + 1) (by omega) (by omega) v (Finset.mem_sdiff.1 hv).1

/-- **Hong and Kung's key argument, without partitions.** If no set dominated by at most `2S`
vertices has more than `U` elements, then the vertices given a red pebble from move `j` on number
at most `(q - charges j + S) U / S`, where `q` is the whole calculation's charge. -/
theorem mul_card_newReds_le (hS : 1 ≤ S) (U : ℝ) (hU0 : 0 ≤ U)
    (hU : ∀ D W : Finset V, D.card ≤ 2 * S → (∀ w ∈ W, Dominated E I D w) → (W.card : ℝ) ≤ U) :
    ∀ j ≤ T.t, (S : ℝ) * (T.newReds j T.t).card ≤
      ((T.charges T.t : ℝ) - T.charges j + S) * U := by
  intro j hj
  induction h : T.t - j using Nat.strong_induction_on generalizing j with
  | _ n ih =>
  rcases Nat.eq_or_lt_of_le hj with rfl | hjt
  · simp only [newReds, Finset.Ico_self, Finset.biUnion_empty, Finset.card_empty,
      Nat.cast_zero, mul_zero, sub_self, zero_add]
    positivity
  -- The window ends at the first move `e > j` at which `S` more has been charged, or at `t`.
  have hex : ∃ e, j < e ∧ (T.t ≤ e ∨ T.charges j + S ≤ T.charges e) :=
    ⟨T.t, hjt, Or.inl le_rfl⟩
  classical
  set e := Nat.find hex with he_def
  have hspec : j < e ∧ (T.t ≤ e ∨ T.charges j + S ≤ T.charges e) := Nat.find_spec hex
  have het : e ≤ T.t := Nat.find_min' hex ⟨hjt, Or.inl le_rfl⟩
  have hwin : T.charges e ≤ T.charges j + S := by
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hc := T.c_le_one e'
    rw [he', T.charges_succ]
    rcases Nat.eq_or_lt_of_le (show j ≤ e' by omega) with h' | h'
    · subst h'
      omega
    · have hnot := Nat.find_min hex (show e' < Nat.find hex by omega)
      simp only [not_and, not_or, not_le] at hnot
      have := (hnot h').2
      omega
  -- The window's own contribution.
  have hwinU : ((T.newReds j e).card : ℝ) ≤ U := by
    refine hU (T.windowDom j e) (T.newReds j e) ?_ fun w hw => T.dominated_of_mem_newReds het hw
    have h₁ := T.card_windowDom_le hj het
    have h₂ := T.charges_add_sum_Ico hspec.1.le
    omega
  have hsplit : T.newReds j T.t = T.newReds j e ∪ T.newReds e T.t := by
    simp only [newReds]
    rw [← Finset.union_biUnion, Finset.Ico_union_Ico_eq_Ico hspec.1.le het]
  have hcard : ((T.newReds j T.t).card : ℝ) ≤ (T.newReds j e).card + (T.newReds e T.t).card := by
    rw [hsplit]
    exact_mod_cast Finset.card_union_le _ _
  have hmono : (T.charges j : ℝ) ≤ T.charges T.t := by exact_mod_cast T.charges_mono hj
  have hS0 : (0 : ℝ) ≤ S := by positivity
  rcases hspec.2 with hte | hfull
  · -- The window runs to the end.
    have hte : e = T.t := le_antisymm het hte
    have hrest : T.newReds e T.t = ∅ := by
      rw [hte]
      simp [newReds]
    rw [hrest, Finset.card_empty, Nat.cast_zero, add_zero] at hcard
    calc (S : ℝ) * (T.newReds j T.t).card ≤ S * U := mul_le_mul_of_nonneg_left
          (hcard.trans hwinU) hS0
      _ ≤ ((T.charges T.t : ℝ) - T.charges j + S) * U := by
          apply mul_le_mul_of_nonneg_right _ hU0
          linarith
  · -- A full window, and the rest by induction.
    have ih' := ih (T.t - e) (by omega) e het rfl
    have hfull' : (T.charges j : ℝ) + S ≤ T.charges e := by exact_mod_cast hfull
    calc (S : ℝ) * (T.newReds j T.t).card
        ≤ S * ((T.newReds j e).card + (T.newReds e T.t).card) :=
          mul_le_mul_of_nonneg_left hcard hS0
      _ = S * (T.newReds j e).card + S * (T.newReds e T.t).card := mul_add _ _ _
      _ ≤ S * U + ((T.charges T.t : ℝ) - T.charges e + S) * U :=
          add_le_add (mul_le_mul_of_nonneg_left hwinU hS0) ih'
      _ ≤ ((T.charges T.t : ℝ) - T.charges j + S) * U := by
          linarith [mul_le_mul_of_nonneg_right hfull' hU0]

end Trace

end MiscMath.Computability.RedBluePebbleGame
