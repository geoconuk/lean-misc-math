/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
module

public import MiscMath.Computability.RedBluePebbleGame.Domination
public import Mathlib.Data.Fintype.Card

/-!
# The red-blue pebble game: the partition a calculation defines

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

This is the construction behind Hong and Kung's Theorem 3.1, corrected. A calculation charged `q`
with at most `S` red pebbles is cut into `q / S + 1` windows, move `i` lying in window
`charges i / S`, so that each window makes at most `S` loads and stores. Window `m` contributes
the part `part m`: the vertices given a red pebble in the window and not already in an earlier
part, from which a path through such vertices leads to one that is red when the window ends or is
stored during it. These parts form a `2S`-partition (`exists_isPartition`).

The argument follows the source's, with two repairs:

* **The case split in the cover argument is on red, not on any pebble.** A predecessor of a vertex
  computed in window `m` is either red when the window starts, and so already in a part, or is
  given a red pebble during the window. An input holding its initial blue pebble need not be in
  any earlier part, and the source's case split puts it on the wrong side.
* **The terminal condition asks for a store during the window**, not for a blue pebble still there
  when it ends. Either works; this one is simpler to use.

It also records the facts about the graph that the argument needs: under `IsComputationDAG` every
vertex reaches an output (`IsComputationDAG.exists_output`), and a calculation with no red pebbles
exists only on the empty graph (`IsComputationDAG.isEmpty_of_hasCompleteCalculation_zero`).
-/

@[expose] public section

namespace MiscMath.Computability.RedBluePebbleGame

open Finset Relation

variable {V : Type*} [DecidableEq V] {E : V → V → Prop} {I : Finset V}

/-! ## Domination, set by set -/

omit [DecidableEq V] in
theorem dominates_iff {D W : Finset V} : Dominates E I D W ↔ ∀ w ∈ W, Dominated E I D w :=
  ⟨fun h w hw x hx hxD => h x hx hxD w hw, fun h x hx hxD w hw => h w hw x hx hxD⟩

omit [DecidableEq V] in
theorem dominates_of_subset {D W : Finset V} (h : W ⊆ D) : Dominates E I D W :=
  dominates_iff.2 fun _ hw => dominated_of_mem (h hw)

/-! ## The graphs of the key lemma -/

omit [DecidableEq V] in
/-- In a finite graph with no cycle, every vertex reaches a vertex with no successor. -/
theorem exists_sink_of_acyclic [Finite V] (hE : ∀ v, ¬ TransGen E v v) (v : V) :
    ∃ w, ReflTransGen E v w ∧ ∀ w', ¬ E w w' := by
  have : IsTrans V (flip (TransGen E)) := ⟨fun _ _ _ hab hbc => TransGen.trans hbc hab⟩
  have : Std.Irrefl (flip (TransGen E)) := ⟨fun a h => hE a h⟩
  obtain ⟨w, hw, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl (flip (TransGen E))).has_min
    {w | ReflTransGen E v w} ⟨v, ReflTransGen.refl⟩
  exact ⟨w, hw, fun w' hww' => hmin w' (ReflTransGen.tail hw hww') (TransGen.single hww')⟩

omit [DecidableEq V] in
/-- Every vertex of a computation DAG reaches an output. -/
theorem IsComputationDAG.exists_output [Finite V] {O : Finset V} (hG : IsComputationDAG E I O)
    (v : V) : ∃ o ∈ O, ReflTransGen E v o := by
  obtain ⟨w, hw, hs⟩ := exists_sink_of_acyclic hG.acyclic v
  exact ⟨w, hG.sinks_subset_outputs w hs, hw⟩

omit [DecidableEq V] in
/-- A vertex with a predecessor is not an input. -/
theorem IsComputationDAG.not_mem_inputs {O : Finset V} (hG : IsComputationDAG E I O) {u v : V}
    (h : E u v) : v ∉ I := fun hv => (hG.inputs_eq_sources v).1 hv u h

/-! ## Calculations, move by move -/

namespace Trace

variable {S : ℕ} (T : Trace E I S)

/-- The last time before `τ` a vertex red at `τ` was given its red pebble: it has stayed red
since. -/
theorem exists_last_red {v : V} (h0 : v ∉ (T.σ 0).1) :
    ∀ τ, v ∈ (T.σ τ).1 → ∃ i < τ, v ∉ (T.σ i).1 ∧ ∀ j, i < j → j ≤ τ → v ∈ (T.σ j).1 := by
  intro τ
  induction τ with
  | zero => exact fun h => absurd h h0
  | succ τ ih =>
    intro h
    by_cases hτ : v ∈ (T.σ τ).1
    · obtain ⟨i, hi, hv, hred⟩ := ih hτ
      refine ⟨i, by omega, hv, fun j hij hj => ?_⟩
      rcases Nat.lt_or_ge j (τ + 1) with hj' | hj'
      · exact hred j hij (by omega)
      · rwa [show j = τ + 1 by omega]
    · exact ⟨τ, by omega, hτ, fun j hij hj => by rwa [show j = τ + 1 by omega]⟩

/-- The last time before `τ` a vertex blue at `τ` was given its blue pebble: it has stayed blue
since. -/
theorem exists_last_blue {v : V} (h0 : v ∉ (T.σ 0).2) :
    ∀ τ, v ∈ (T.σ τ).2 → ∃ i < τ, v ∉ (T.σ i).2 ∧ ∀ j, i < j → j ≤ τ → v ∈ (T.σ j).2 := by
  intro τ
  induction τ with
  | zero => exact fun h => absurd h h0
  | succ τ ih =>
    intro h
    by_cases hτ : v ∈ (T.σ τ).2
    · obtain ⟨i, hi, hv, hblue⟩ := ih hτ
      refine ⟨i, by omega, hv, fun j hij hj => ?_⟩
      rcases Nat.lt_or_ge j (τ + 1) with hj' | hj'
      · exact hblue j hij (by omega)
      · rwa [show j = τ + 1 by omega]
    · exact ⟨τ, by omega, hτ, fun j hij hj => by rwa [show j = τ + 1 by omega]⟩

/-- A vertex with no pebble at time `a` and a pebble at time `b` was computed in between: at some
move `i ∈ [a, b)` it was not red and all its predecessors were. -/
theorem exists_compute_between {v : V} {a : ℕ} (hR : v ∉ (T.σ a).1) (hB : v ∉ (T.σ a).2) :
    ∀ b, a ≤ b → b ≤ T.t → (v ∈ (T.σ b).1 ∨ v ∈ (T.σ b).2) →
      ∃ i, a ≤ i ∧ i < b ∧ v ∉ (T.σ i).1 ∧ ∀ u, E u v → u ∈ (T.σ i).1 := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => rintro - (h | h) <;> contradiction
  | succ b hab ih =>
    intro hbt h
    by_cases hprev : v ∈ (T.σ b).1 ∨ v ∈ (T.σ b).2
    · obtain ⟨i, hai, hib, rest⟩ := ih (by omega) hprev
      exact ⟨i, hai, by omega, rest⟩
    · simp only [not_or] at hprev
      obtain ⟨-, hp, -, -⟩ := (T.step b (by omega)).first_pebble hprev.1 hprev.2 h
      exact ⟨b, hab, by omega, hprev.1, hp⟩

/-- The vertices given a blue pebble by moves `j, …, e - 1`: those it stores. -/
def newBlues (j e : ℕ) : Finset V :=
  (Ico j e).biUnion fun i => (T.σ (i + 1)).2 \ (T.σ i).2

theorem card_newBlues_le {j e : ℕ} (he : e ≤ T.t) :
    (T.newBlues j e).card ≤ ∑ i ∈ Ico j e, T.c i := by
  refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.mem_Ico] at hi
  have hstep := T.step i (by omega)
  rcases Finset.eq_empty_or_nonempty ((T.σ (i + 1)).2 \ (T.σ i).2) with h | ⟨w, hw⟩
  · rw [h, Finset.card_empty]
    exact Nat.zero_le _
  · rw [Finset.mem_sdiff] at hw
    have hc := (hstep.new_blue hw.2 hw.1).2.1
    rw [hc, Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_sdiff] at ha hb
    exact hstep.eq_of_new_blue ha.2 ha.1 hb.2 hb.1

/-! ### Windows -/

/-- The window of move `i`: the number of complete blocks of `S` loads and stores before it. -/
def win (i : ℕ) : ℕ := T.charges i / S

theorem win_mono : Monotone T.win := fun _ _ h => Nat.div_le_div_right (T.charges_mono h)

/-- The time at which window `m` starts: the first time that is the end of the calculation or
lies in window `m` or a later one. -/
def cut (m : ℕ) : ℕ := Nat.find (⟨T.t, Or.inl rfl⟩ : ∃ τ, τ = T.t ∨ m ≤ T.win τ)

theorem cut_le (m : ℕ) : T.cut m ≤ T.t := Nat.find_min' _ (Or.inl rfl)

theorem cut_spec (m : ℕ) : T.cut m = T.t ∨ m ≤ T.win (T.cut m) :=
  Nat.find_spec (⟨T.t, Or.inl rfl⟩ : ∃ τ, τ = T.t ∨ m ≤ T.win τ)

/-- A move before the end lies before the start of window `m` exactly when its window is earlier. -/
theorem lt_cut_iff {i m : ℕ} (hi : i < T.t) : i < T.cut m ↔ T.win i < m := by
  constructor
  · intro h
    have := Nat.find_min (⟨T.t, Or.inl rfl⟩ : ∃ τ, τ = T.t ∨ m ≤ T.win τ) h
    simp only [not_or, not_le] at this
    exact this.2
  · intro h
    by_contra hle
    have hle' : T.cut m ≤ i := not_lt.1 hle
    rcases T.cut_spec m with h' | h'
    · omega
    · exact absurd (h'.trans (T.win_mono hle')) (by omega)

theorem cut_zero : T.cut 0 = 0 :=
  Nat.le_zero.1 (Nat.find_min' _ (Or.inr (Nat.zero_le _)))

theorem cut_mono : Monotone T.cut := fun _ _ h =>
  Nat.find_mono fun _ hτ => hτ.imp_right (le_trans h)

/-- Move `i` lies in the window `win i`, between its start and the next window's. -/
theorem cut_win_le {i : ℕ} (hi : i < T.t) : T.cut (T.win i) ≤ i :=
  not_lt.1 fun h => absurd ((T.lt_cut_iff hi).1 h) (lt_irrefl _)

theorem lt_cut_win_succ {i : ℕ} (hi : i < T.t) : i < T.cut (T.win i + 1) :=
  (T.lt_cut_iff hi).2 (Nat.lt_succ_self _)

/-- Every move lies in one of the first `charges t / S + 1` windows. -/
theorem cut_last : T.cut (T.charges T.t / S + 1) = T.t := by
  refine le_antisymm (T.cut_le _) (not_lt.1 fun h => ?_)
  have hwin : T.win (T.cut (T.charges T.t / S + 1)) ≤ T.charges T.t / S :=
    Nat.div_le_div_right (T.charges_mono (T.cut_le _))
  rcases T.cut_spec (T.charges T.t / S + 1) with h' | h'
  · omega
  · omega

/-- A window makes at most `S` loads and stores. -/
theorem sum_window_le (hS : 1 ≤ S) (m : ℕ) :
    ∑ i ∈ Ico (T.cut m) (T.cut (m + 1)), T.c i ≤ S := by
  have hmono : T.cut m ≤ T.cut (m + 1) := T.cut_mono (Nat.le_succ m)
  have hsum := T.charges_add_sum_Ico hmono
  rcases Nat.eq_or_lt_of_le hmono with heq | hlt
  · rw [heq, Finset.Ico_self, Finset.sum_empty]
    exact Nat.zero_le _
  -- The window is not empty, so it starts before the end, in window `m`.
  have hstart : m * S ≤ T.charges (T.cut m) := by
    rcases T.cut_spec m with h | h
    · exact absurd (h ▸ hlt) (not_lt.2 (T.cut_le _))
    · exact (Nat.le_div_iff_mul_le (by omega)).1 h
  -- Its last move lies in window `m`, so before it fewer than `(m + 1) S` were charged.
  obtain ⟨e, he⟩ : ∃ e, T.cut (m + 1) = e + 1 := ⟨T.cut (m + 1) - 1, by omega⟩
  have het : e < T.t := by have := T.cut_le (m + 1); omega
  have hwe : T.win e < m + 1 := (T.lt_cut_iff het).1 (by omega)
  have hce : T.charges e < (m + 1) * S := (Nat.div_lt_iff_lt_mul (by omega)).1 hwe
  have hend : T.charges (T.cut (m + 1)) ≤ (m + 1) * S := by
    rw [he, T.charges_succ]
    have := T.c_le_one e
    omega
  have : (m + 1) * S = m * S + S := Nat.succ_mul m S
  omega

/-! ### The parts -/

/-- The vertices a window `m` must account for when it ends: those red then, and those it
stored. -/
def terminal (m : ℕ) : Finset V :=
  (T.σ (T.cut (m + 1))).1 ∪ T.newBlues (T.cut m) (T.cut (m + 1))

/-- The candidates of window `m`, given the vertices `U` already placed in earlier parts: those
given a red pebble in the window and not in `U`. -/
def cand (U : Finset V) (m : ℕ) : Finset V :=
  T.newReds (T.cut m) (T.cut (m + 1)) \ U

open Classical in
/-- The part of window `m`, given the vertices `U` already placed: the candidates from which a path
through candidates leads to a terminal vertex. -/
noncomputable def partOf (U : Finset V) (m : ℕ) : Finset V :=
  (T.cand U m).filter fun v => ∃ w ∈ T.terminal m,
    ReflTransGen (fun a b => E a b ∧ a ∈ T.cand U m ∧ b ∈ T.cand U m) v w

/-- The vertices placed in the parts of windows `0, …, m - 1`. -/
noncomputable def assigned : ℕ → Finset V
  | 0 => ∅
  | m + 1 => assigned m ∪ T.partOf (assigned m) m

/-- The part of window `m`. -/
noncomputable def part (m : ℕ) : Finset V := T.partOf (T.assigned m) m

theorem assigned_succ (m : ℕ) : T.assigned (m + 1) = T.assigned m ∪ T.part m := rfl

theorem assigned_mono : Monotone T.assigned :=
  monotone_nat_of_le_succ fun m => by rw [assigned_succ]; exact Finset.subset_union_left

theorem mem_assigned_iff {v : V} {m : ℕ} : v ∈ T.assigned m ↔ ∃ m' < m, v ∈ T.part m' := by
  induction m with
  | zero => simp [assigned]
  | succ m ih =>
    rw [assigned_succ, Finset.mem_union, ih]
    constructor
    · rintro (⟨m', hm', h⟩ | h)
      · exact ⟨m', by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨m', hm', h⟩
      rcases Nat.lt_or_ge m' m with hlt | hge
      · exact Or.inl ⟨m', hlt, h⟩
      · exact Or.inr (by rwa [show m = m' by omega])

theorem part_subset_assigned {m m' : ℕ} (h : m < m') : T.part m ⊆ T.assigned m' :=
  fun _ hv => T.mem_assigned_iff.2 ⟨m, h, hv⟩

theorem mem_part_iff {v : V} {m : ℕ} : v ∈ T.part m ↔ v ∈ T.cand (T.assigned m) m ∧
    ∃ w ∈ T.terminal m, ReflTransGen
      (fun a b => E a b ∧ a ∈ T.cand (T.assigned m) m ∧ b ∈ T.cand (T.assigned m) m) v w := by
  classical
  unfold part partOf
  rw [Finset.mem_filter]

theorem mem_cand_of_mem_part {v : V} {m : ℕ} (hv : v ∈ T.part m) : v ∈ T.cand (T.assigned m) m :=
  (T.mem_part_iff.1 hv).1

theorem not_mem_assigned_of_mem_part {v : V} {m : ℕ} (hv : v ∈ T.part m) : v ∉ T.assigned m :=
  (Finset.mem_sdiff.1 (T.mem_cand_of_mem_part hv)).2

theorem mem_newReds_of_mem_part {v : V} {m : ℕ} (hv : v ∈ T.part m) :
    v ∈ T.newReds (T.cut m) (T.cut (m + 1)) :=
  (Finset.mem_sdiff.1 (T.mem_cand_of_mem_part hv)).1

theorem disjoint_part {m m' : ℕ} (h : m ≠ m') : Disjoint (T.part m) (T.part m') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt
  · exact T.not_mem_assigned_of_mem_part hv' (T.part_subset_assigned hlt hv)
  · exact T.not_mem_assigned_of_mem_part hv (T.part_subset_assigned hlt hv')

/-- A terminal candidate is in the part. -/
theorem mem_part_of_terminal {v : V} {m : ℕ} (hc : v ∈ T.cand (T.assigned m) m)
    (ht : v ∈ T.terminal m) : v ∈ T.part m :=
  T.mem_part_iff.2 ⟨hc, v, ht, ReflTransGen.refl⟩

/-- A candidate with a successor in the part is in the part. -/
theorem mem_part_of_edge {u v : V} {m : ℕ} (hu : u ∈ T.cand (T.assigned m) m) (huv : E u v)
    (hv : v ∈ T.part m) : u ∈ T.part m := by
  obtain ⟨hvc, w, hw, hpath⟩ := T.mem_part_iff.1 hv
  exact T.mem_part_iff.2 ⟨hu, w, hw, ReflTransGen.head ⟨huv, hu, hvc⟩ hpath⟩

/-- A vertex of the part with no successor in it is terminal. -/
theorem mem_terminal_of_mem_part {v : V} {m : ℕ} (hv : v ∈ T.part m)
    (hmin : ∀ w ∈ T.part m, ¬ E v w) : v ∈ T.terminal m := by
  obtain ⟨-, w, hw, hpath⟩ := T.mem_part_iff.1 hv
  rcases hpath.cases_head with rfl | ⟨v', ⟨hvv', -, hv'c⟩, hrest⟩
  · exact hw
  · exact absurd hvv' (hmin v' (T.mem_part_iff.2 ⟨hv'c, w, hw, hrest⟩))

/-! ### The key claims -/

variable {O : Finset V} (h0 : T.σ 0 = (∅, I))
include h0

theorem not_mem_red_zero (v : V) : v ∉ (T.σ 0).1 := by rw [h0]; exact Finset.notMem_empty v

/-- **A vertex red when a window ends is in its part or an earlier one.** -/
theorem mem_assigned_of_red {v : V} {m : ℕ} (hv : v ∈ (T.σ (T.cut (m + 1))).1) :
    v ∈ T.assigned (m + 1) := by
  obtain ⟨i, hi, hvi, hred⟩ := T.exists_last_red (T.not_mem_red_zero h0 v) _ hv
  have hit : i < T.t := lt_of_lt_of_le hi (T.cut_le _)
  have hwin : T.win i < m + 1 := (T.lt_cut_iff hit).1 hi
  -- `v` was given its red pebble in window `win i` and is red when that window ends.
  have hnew : v ∈ T.newReds (T.cut (T.win i)) (T.cut (T.win i + 1)) :=
    Finset.mem_biUnion.2 ⟨i, Finset.mem_Ico.2 ⟨T.cut_win_le hit, T.lt_cut_win_succ hit⟩,
      Finset.mem_sdiff.2 ⟨hred (i + 1) (by omega) (by omega), hvi⟩⟩
  have hterm : v ∈ T.terminal (T.win i) :=
    Finset.mem_union_left _ (hred _ (T.lt_cut_win_succ hit) (T.cut_mono (by omega)))
  have hsub : T.assigned (T.win i + 1) ⊆ T.assigned (m + 1) := T.assigned_mono (by omega)
  by_cases ha : v ∈ T.assigned (T.win i)
  · exact hsub (T.assigned_mono (Nat.le_succ _) ha)
  · exact hsub (by
      rw [assigned_succ]
      exact Finset.mem_union_right _
        (T.mem_part_of_terminal (Finset.mem_sdiff.2 ⟨hnew, ha⟩) hterm))

/-- **A vertex stored in a window is in its part or an earlier one.** -/
theorem mem_assigned_of_stored {v : V} {m : ℕ} (hv : v ∈ T.newBlues (T.cut m) (T.cut (m + 1))) :
    v ∈ T.assigned (m + 1) := by
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 hv
  rw [Finset.mem_Ico] at hi
  rw [Finset.mem_sdiff] at hvi
  have hit : i < T.t := lt_of_lt_of_le hi.2 (T.cut_le _)
  have hRi : v ∈ (T.σ i).1 := ((T.step i hit).new_blue hvi.2 hvi.1).2.2
  obtain ⟨i', hi', hvi', hred⟩ := T.exists_last_red (T.not_mem_red_zero h0 v) _ hRi
  have hi't : i' < T.t := by omega
  have hwi : T.win i = m := by
    have h1 := (T.lt_cut_iff hit).1 hi.2
    have h2 : ¬ i < T.cut m := not_lt.2 hi.1
    rw [T.lt_cut_iff hit] at h2
    omega
  have hle : T.win i' ≤ m := hwi ▸ T.win_mono hi'.le
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · -- Given its red pebble in the same window: it is terminal there.
    have hnew : v ∈ T.newReds (T.cut m) (T.cut (m + 1)) := by
      refine Finset.mem_biUnion.2 ⟨i', Finset.mem_Ico.2 ⟨?_, by omega⟩,
        Finset.mem_sdiff.2 ⟨hred (i' + 1) (by omega) (by omega), hvi'⟩⟩
      exact heq ▸ T.cut_win_le hi't
    have hterm : v ∈ T.terminal m := Finset.mem_union_right _ hv
    by_cases ha : v ∈ T.assigned m
    · exact T.assigned_mono (Nat.le_succ _) ha
    · rw [assigned_succ]
      exact Finset.mem_union_right _
        (T.mem_part_of_terminal (Finset.mem_sdiff.2 ⟨hnew, ha⟩) hterm)
  · -- Given its red pebble earlier: it is red when that earlier window ends.
    have hcut : T.cut (T.win i' + 1) ≤ i := by
      have := T.cut_mono (show T.win i' + 1 ≤ m by omega)
      omega
    have hred' : v ∈ (T.σ (T.cut (T.win i' + 1))).1 :=
      hred _ (T.lt_cut_win_succ hi't) hcut
    exact T.assigned_mono (by omega) (T.mem_assigned_of_red h0 hred')

/-- **A non-input in a part has no pebble when its window starts.** -/
theorem not_pebbled_of_mem_part {v : V} {m : ℕ} (hv : v ∈ T.part m) (hvI : v ∉ I) :
    v ∉ (T.σ (T.cut m)).1 ∧ v ∉ (T.σ (T.cut m)).2 := by
  have hna := T.not_mem_assigned_of_mem_part hv
  cases m with
  | zero =>
    rw [T.cut_zero, h0]
    exact ⟨Finset.notMem_empty v, hvI⟩
  | succ m =>
    refine ⟨fun hR => hna (T.mem_assigned_of_red h0 hR), fun hB => ?_⟩
    obtain ⟨i, hi, hvi, hblue⟩ := T.exists_last_blue (by rw [h0]; exact hvI) _ hB
    have hit : i < T.t := lt_of_lt_of_le hi (T.cut_le _)
    have hwin : T.win i < m + 1 := (T.lt_cut_iff hit).1 hi
    have hst : v ∈ T.newBlues (T.cut (T.win i)) (T.cut (T.win i + 1)) :=
      Finset.mem_biUnion.2 ⟨i, Finset.mem_Ico.2 ⟨T.cut_win_le hit, T.lt_cut_win_succ hit⟩,
        Finset.mem_sdiff.2 ⟨hblue (i + 1) (by omega) (by omega), hvi⟩⟩
    exact hna (T.assigned_mono (by omega) (T.mem_assigned_of_stored h0 hst))

/-- **A predecessor of a non-input in a part is in that part or an earlier one.** -/
theorem mem_assigned_of_pred {u v : V} {m : ℕ} (hv : v ∈ T.part m) (hvI : v ∉ I) (huv : E u v) :
    u ∈ T.assigned (m + 1) := by
  obtain ⟨hR, hB⟩ := T.not_pebbled_of_mem_part h0 hv hvI
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 (T.mem_newReds_of_mem_part hv)
  rw [Finset.mem_Ico] at hi
  rw [Finset.mem_sdiff] at hvi
  have hit : i < T.t := lt_of_lt_of_le hi.2 (T.cut_le _)
  -- `v` was computed at some move `i₀` of the window, with `u` red.
  obtain ⟨i₀, hi₀a, hi₀b, -, hpred⟩ :=
    T.exists_compute_between hR hB (i + 1) (by omega) (by omega) (Or.inl hvi.1)
  have hi₀t : i₀ < T.t := by omega
  have hwi₀ : T.win i₀ = m := by
    have h1 := (T.lt_cut_iff hi₀t).1 (show i₀ < T.cut (m + 1) by omega)
    have h2 : ¬ i₀ < T.cut m := not_lt.2 hi₀a
    rw [T.lt_cut_iff hi₀t] at h2
    omega
  have hu := hpred u huv
  obtain ⟨i₁, hi₁, hui₁, hred⟩ := T.exists_last_red (T.not_mem_red_zero h0 u) _ hu
  have hi₁t : i₁ < T.t := by omega
  have hle : T.win i₁ ≤ m := hwi₀ ▸ T.win_mono hi₁.le
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · -- `u` was given its red pebble in the same window.
    have hnew : u ∈ T.newReds (T.cut m) (T.cut (m + 1)) := by
      refine Finset.mem_biUnion.2 ⟨i₁, Finset.mem_Ico.2 ⟨heq ▸ T.cut_win_le hi₁t, by omega⟩,
        Finset.mem_sdiff.2 ⟨hred (i₁ + 1) (by omega) (by omega), hui₁⟩⟩
    by_cases ha : u ∈ T.assigned m
    · exact T.assigned_mono (Nat.le_succ _) ha
    · rw [assigned_succ]
      exact Finset.mem_union_right _
        (T.mem_part_of_edge (Finset.mem_sdiff.2 ⟨hnew, ha⟩) huv hv)
  · -- `u` was red when an earlier window ended.
    have hcut : T.cut (T.win i₁ + 1) ≤ i₀ := by
      have := T.cut_mono (show T.win i₁ + 1 ≤ m by omega)
      omega
    exact T.assigned_mono (by omega)
      (T.mem_assigned_of_red h0 (hred _ (T.lt_cut_win_succ hi₁t) hcut))

/-- **Every vertex is in one of the first `charges t / S + 1` parts.** -/
theorem mem_assigned_last [Finite V] (hG : IsComputationDAG E I O) (ht : T.σ T.t = (∅, O))
    (v : V) : v ∈ T.assigned (T.charges T.t / S + 1) := by
  obtain ⟨o, ho, hpath⟩ := hG.exists_output v
  induction hpath using ReflTransGen.head_induction_on with
  | refl =>
    -- An output ends blue, and is not an input, so it was stored.
    have hoI : o ∉ I := fun h => Finset.disjoint_left.1 hG.disjoint h ho
    have hB : o ∈ (T.σ T.t).2 := by rw [ht]; exact ho
    obtain ⟨i, hi, hoi, hblue⟩ := T.exists_last_blue (by rw [h0]; exact hoI) _ hB
    have hst : o ∈ T.newBlues (T.cut (T.win i)) (T.cut (T.win i + 1)) :=
      Finset.mem_biUnion.2 ⟨i, Finset.mem_Ico.2 ⟨T.cut_win_le hi, T.lt_cut_win_succ hi⟩,
        Finset.mem_sdiff.2 ⟨hblue (i + 1) (by omega) (by omega), hoi⟩⟩
    have hwin : T.win i ≤ T.charges T.t / S := Nat.div_le_div_right (T.charges_mono hi.le)
    exact T.assigned_mono (by omega) (T.mem_assigned_of_stored h0 hst)
  | head huv _ ih =>
    obtain ⟨m, hm, hv⟩ := T.mem_assigned_iff.1 ih
    exact T.assigned_mono (by omega)
      (T.mem_assigned_of_pred h0 hv (hG.not_mem_inputs huv) huv)

omit h0 in
/-- The dominator of a part: the red pebbles when its window starts, and the vertices it loads. -/
theorem card_windowDom_part_le (hS : 1 ≤ S) (m : ℕ) :
    (T.windowDom (T.cut m) (T.cut (m + 1))).card ≤ 2 * S := by
  have := T.card_windowDom_le (T.cut_le m) (T.cut_le (m + 1))
  have := T.sum_window_le hS m
  omega

omit h0 in
theorem card_terminal_le (hS : 1 ≤ S) (m : ℕ) : (T.terminal m).card ≤ 2 * S := by
  refine (Finset.card_union_le _ _).trans ?_
  have := T.budget _ (T.cut_le (m + 1))
  have := (T.card_newBlues_le (j := T.cut m) (T.cut_le (m + 1))).trans (T.sum_window_le hS m)
  omega

/-- **The parts form a `2S`-partition.** -/
theorem isPartition [Finite V] (hS : 1 ≤ S) (hG : IsComputationDAG E I O)
    (ht : T.σ T.t = (∅, O)) :
    IsPartition E I (2 * S) (fun i : Fin (T.charges T.t / S + 1) => T.part i) := by
  classical
  refine ⟨⟨fun v => ?_, fun i => ⟨T.windowDom (T.cut i) (T.cut (i + 1)),
    T.card_windowDom_part_le hS i, dominates_iff.2 fun w hw =>
      T.dominated_of_mem_newReds (T.cut_le _) (T.mem_newReds_of_mem_part hw)⟩,
    fun i j u hu v hv huv => ?_⟩, fun i => ?_⟩
  · -- Every vertex lies in exactly one part.
    obtain ⟨m, hm, hv⟩ := T.mem_assigned_iff.1 (T.mem_assigned_last h0 hG ht v)
    refine ⟨⟨m, hm⟩, hv, fun j hj => Fin.ext ?_⟩
    by_contra hne
    exact Finset.disjoint_left.1 (T.disjoint_part hne) hj hv
  · -- Edges run forward.
    obtain ⟨m, hm, hu'⟩ := T.mem_assigned_iff.1
      (T.mem_assigned_of_pred h0 hv (hG.not_mem_inputs huv) huv)
    have : (i : ℕ) = m := by
      by_contra hne
      exact Finset.disjoint_left.1 (T.disjoint_part hne) hu hu'
    rw [Fin.le_iff_val_le_val]
    omega
  · -- The minimum set is terminal.
    refine (Finset.card_le_card fun v hv => ?_).trans (T.card_terminal_le hS i)
    rw [Finset.mem_filter] at hv
    exact T.mem_terminal_of_mem_part hv.1 hv.2

end Trace

/-- Every move is made on some vertex. -/
theorem Step.nonempty {s s' : Finset V × Finset V} {c : ℕ} (h : Step E I s c s') : Nonempty V := by
  rcases step_iff.1 h with ⟨v, -⟩ | ⟨v, -⟩ | ⟨v, -⟩ | ⟨v, -⟩ | ⟨v, -⟩ <;> exact ⟨v⟩

/-- So on the empty type no move can be made, and a complete calculation costs nothing. -/
theorem HasCompleteCalculation.eq_zero_of_isEmpty [IsEmpty V] {O : Finset V} {S q : ℕ}
    (h : HasCompleteCalculation E I O S q) : q = 0 := by
  obtain ⟨t, σ, c, -, -, -, hs, hq⟩ := h
  cases t with
  | zero => simpa using hq.symm
  | succ t => exact (hs 0).nonempty.elim isEmptyElim

/-- With no red pebbles nothing can be loaded, computed or stored, so a complete calculation exists
only on the empty graph. -/
theorem IsComputationDAG.isEmpty_of_hasCompleteCalculation_zero [Finite V] {O : Finset V} {q : ℕ}
    (hG : IsComputationDAG E I O) (h : HasCompleteCalculation E I O 0 q) : IsEmpty V := by
  obtain ⟨T, h0, ht, -⟩ := h.exists_trace
  refine ⟨fun v => ?_⟩
  obtain ⟨o, ho, -⟩ := hG.exists_output v
  have hoI : o ∉ I := fun h => Finset.disjoint_left.1 hG.disjoint h ho
  obtain ⟨i, hi, hoi, hblue⟩ := T.exists_last_blue (v := o) (by rw [h0]; exact hoI) T.t
    (by rw [ht]; exact ho)
  have hR := ((T.step i hi).new_blue hoi (hblue (i + 1) (by omega) (by omega))).2.2
  have := T.budget i hi.le
  rw [Finset.card_eq_zero.1 (Nat.le_zero.1 this)] at hR
  exact Finset.notMem_empty o hR

/-- **Hong and Kung's Theorem 3.1, corrected.** A complete calculation of a computation DAG with at
most `S` red pebbles, charged `q`, comes with a `2S`-partition into `h` parts, `q ≤ S h ≤ q + S`. -/
theorem exists_isPartition [Finite V] {O : Finset V} {S q : ℕ} (hG : IsComputationDAG E I O)
    (hq : HasCompleteCalculation E I O S q) :
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S := by
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · -- No red pebbles: the graph is empty, and so is the partition.
    have := hG.isEmpty_of_hasCompleteCalculation_zero hq
    have hq0 := hq.eq_zero_of_isEmpty
    refine ⟨0, Fin.elim0, ⟨⟨fun v => isEmptyElim v, fun i => i.elim0, fun i => i.elim0⟩,
      fun i => i.elim0⟩, by omega, by omega⟩
  · obtain ⟨T, h0, ht, hsum⟩ := hq.exists_trace
    have hct : T.charges T.t = q := hsum
    refine ⟨q / S + 1, fun i => T.part i, hct ▸ T.isPartition h0 hS hG ht,
      (Nat.lt_mul_div_succ q hS).le, ?_⟩
    have := Nat.mul_div_le q S
    rw [Nat.mul_add, Nat.mul_one]
    omega

end MiscMath.Computability.RedBluePebbleGame
