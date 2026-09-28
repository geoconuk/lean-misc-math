/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
module

public import MiscMath.Computability.RedBluePebbleGame.Spec
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The red-blue pebble game: calculations as sequences indexed by `ℕ`

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

`HasCompleteCalculation` indexes configurations by `Fin (t + 1)` and charges by `Fin t`, which
is the right shape for reading and the wrong one for proving. This file supplies:

* `step_iff`, the five moves as a disjunction, and the facts about a single move that the proofs
  use: a move adds at most one red pebble and at most one blue pebble, never one of each, and
  the first pebble a non-input receives comes from a computation;
* `Trace`, a calculation with configurations and charges indexed by `ℕ`, and the passage to it
  from `HasCompleteCalculation`;
* `Run`, a calculation assembled move by move, which is how calculations are built, and the
  passage from it back to `HasCompleteCalculation`;
* the count behind the trivial I/O bound: every input loaded and every output stored at least
  once costs at least `|I| + |O|`.
-/

@[expose] public section

namespace MiscMath.Computability.RedBluePebbleGame

open Finset

variable {V : Type*} [DecidableEq V] {E : V → V → Prop} {I : Finset V}

/-! ## A single move -/

/-- The five moves of `Step`, as a disjunction over the configuration's components. -/
theorem step_iff {s s' : Finset V × Finset V} {c : ℕ} :
    Step E I s c s' ↔
      (∃ v, v ∈ s.2 ∧ v ∉ s.1 ∧ c = 1 ∧ s' = (insert v s.1, s.2)) ∨
      (∃ v, v ∈ s.1 ∧ v ∉ s.2 ∧ c = 1 ∧ s' = (s.1, insert v s.2)) ∨
      (∃ v, v ∉ I ∧ v ∉ s.1 ∧ (∀ u, E u v → u ∈ s.1) ∧ c = 0 ∧ s' = (insert v s.1, s.2)) ∨
      (∃ v, v ∈ s.1 ∧ c = 0 ∧ s' = (s.1.erase v, s.2)) ∨
      (∃ v, v ∈ s.2 ∧ c = 0 ∧ s' = (s.1, s.2.erase v)) := by
  constructor
  · rintro (⟨hB, hR⟩ | ⟨hR, hB⟩ | ⟨hI, hR, hp⟩ | ⟨hR⟩ | ⟨hB⟩)
    · exact Or.inl ⟨_, hB, hR, rfl, rfl⟩
    · exact Or.inr <| Or.inl ⟨_, hR, hB, rfl, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨_, hI, hR, hp, rfl, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨_, hR, rfl, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨_, hB, rfl, rfl⟩
  · obtain ⟨R, B⟩ := s
    rintro (⟨v, hB, hR, rfl, rfl⟩ | ⟨v, hR, hB, rfl, rfl⟩ | ⟨v, hI, hR, hp, rfl, rfl⟩ |
      ⟨v, hR, rfl, rfl⟩ | ⟨v, hB, rfl, rfl⟩)
    · exact Step.load hB hR
    · exact Step.store hR hB
    · exact Step.compute hI hR hp
    · exact Step.deleteRed hR
    · exact Step.deleteBlue hB

/-- Whether a move is legal can be decided on a finite graph, which lets concrete calculations be
checked by `decide`. -/
instance Step.decidable [Fintype V] [DecidableRel E] {s s' : Finset V × Finset V} {c : ℕ} :
    Decidable (Step E I s c s') :=
  decidable_of_iff _ step_iff.symm

namespace Step

variable {s s' : Finset V × Finset V} {c : ℕ}

theorem charge_le_one (h : Step E I s c s') : c ≤ 1 := by
  rcases step_iff.1 h with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ |
    ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> omega

/-- A red pebble that appears in a move comes from a load, charged 1, or from a computation,
charged 0; either way the move adds exactly that red pebble. -/
theorem new_red (h : Step E I s c s') {v : V} (h₁ : v ∉ s.1) (h₂ : v ∈ s'.1) :
    s' = (insert v s.1, s.2) ∧
      ((c = 1 ∧ v ∈ s.2) ∨ (c = 0 ∧ v ∉ I ∧ ∀ u, E u v → u ∈ s.1)) := by
  rcases step_iff.1 h with ⟨w, hB, -, rfl, rfl⟩ | ⟨w, -, -, rfl, rfl⟩ | ⟨w, hI, -, hp, rfl, rfl⟩ |
    ⟨w, -, rfl, rfl⟩ | ⟨w, -, rfl, rfl⟩
  · obtain rfl : v = w := by simpa [h₁] using h₂
    exact ⟨rfl, Or.inl ⟨rfl, hB⟩⟩
  · exact absurd h₂ h₁
  · obtain rfl : v = w := by simpa [h₁] using h₂
    exact ⟨rfl, Or.inr ⟨rfl, hI, hp⟩⟩
  · exact absurd (Finset.mem_of_mem_erase h₂) h₁
  · exact absurd h₂ h₁

/-- A blue pebble that appears in a move comes from a store, charged 1. -/
theorem new_blue (h : Step E I s c s') {v : V} (h₁ : v ∉ s.2) (h₂ : v ∈ s'.2) :
    s' = (s.1, insert v s.2) ∧ c = 1 ∧ v ∈ s.1 := by
  rcases step_iff.1 h with ⟨w, -, -, rfl, rfl⟩ | ⟨w, hR, -, rfl, rfl⟩ | ⟨w, -, -, -, rfl, rfl⟩ |
    ⟨w, -, rfl, rfl⟩ | ⟨w, -, rfl, rfl⟩
  · exact absurd h₂ h₁
  · obtain rfl : v = w := by simpa [h₁] using h₂
    exact ⟨rfl, rfl, hR⟩
  · exact absurd h₂ h₁
  · exact absurd h₂ h₁
  · exact absurd (Finset.mem_of_mem_erase h₂) h₁

/-- A move adds at most one red pebble. -/
theorem eq_of_new_red (h : Step E I s c s') {v w : V} (hv₁ : v ∉ s.1) (hv₂ : v ∈ s'.1)
    (hw₁ : w ∉ s.1) (hw₂ : w ∈ s'.1) : v = w := by
  obtain ⟨rfl, -⟩ := h.new_red hv₁ hv₂
  exact (by simpa [hw₁] using hw₂ : w = v).symm

/-- A move adds at most one blue pebble. -/
theorem eq_of_new_blue (h : Step E I s c s') {v w : V} (hv₁ : v ∉ s.2) (hv₂ : v ∈ s'.2)
    (hw₁ : w ∉ s.2) (hw₂ : w ∈ s'.2) : v = w := by
  obtain ⟨rfl, -⟩ := h.new_blue hv₁ hv₂
  exact (by simpa [hw₁] using hw₂ : w = v).symm

/-- No move adds both a red pebble and a blue one. -/
theorem not_new_red_and_blue (h : Step E I s c s') {v w : V} (hv₁ : v ∉ s.1) (hv₂ : v ∈ s'.1)
    (hw₁ : w ∉ s.2) (hw₂ : w ∈ s'.2) : False := by
  obtain ⟨rfl, -⟩ := h.new_red hv₁ hv₂
  exact hw₁ hw₂

/-- The red pebbles a move adds: at most one. -/
theorem card_sdiff_red_le_one (h : Step E I s c s') : (s'.1 \ s.1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_sdiff] at ha hb
  exact h.eq_of_new_red ha.2 ha.1 hb.2 hb.1

/-- The first pebble a vertex receives, red or blue, comes from computing it. -/
theorem first_pebble (h : Step E I s c s') {v : V} (h₁ : v ∉ s.1) (h₂ : v ∉ s.2)
    (h₃ : v ∈ s'.1 ∨ v ∈ s'.2) :
    v ∉ I ∧ (∀ u, E u v → u ∈ s.1) ∧ s'.1 = insert v s.1 ∧ c = 0 := by
  rcases h₃ with h₃ | h₃
  · obtain ⟨rfl, (⟨-, hB⟩ | ⟨rfl, hI, hp⟩)⟩ := h.new_red h₁ h₃
    · exact absurd hB h₂
    · exact ⟨hI, hp, rfl, rfl⟩
  · obtain ⟨rfl, -, hR⟩ := h.new_blue h₂ h₃
    exact absurd hR h₁

end Step

/-! ## Calculations indexed by `ℕ` -/

/-- A calculation within a red-pebble budget `S`, with configurations `σ j` (`j ≤ t`) and
charges `c i` (`i < t`) indexed by `ℕ`. Charges past the end are `0`, so that partial sums of
charges stop growing at `t`. -/
structure Trace (E : V → V → Prop) (I : Finset V) (S : ℕ) where
  /-- The number of moves. -/
  t : ℕ
  /-- The configurations; only `σ 0, …, σ t` matter. -/
  σ : ℕ → Finset V × Finset V
  /-- The charges; only `c 0, …, c (t - 1)` matter, and the rest are `0`. -/
  c : ℕ → ℕ
  budget : ∀ j ≤ t, (σ j).1.card ≤ S
  step : ∀ i < t, Step E I (σ i) (c i) (σ (i + 1))
  c_eq_zero : ∀ i, t ≤ i → c i = 0

/-- Every complete calculation, read as a `Trace`. -/
theorem HasCompleteCalculation.exists_trace {O : Finset V} {S q : ℕ}
    (h : HasCompleteCalculation E I O S q) :
    ∃ T : Trace E I S, T.σ 0 = (∅, I) ∧ T.σ T.t = (∅, O) ∧
      ∑ i ∈ range T.t, T.c i = q := by
  obtain ⟨t, σ, c, h0, ht, hb, hs, hq⟩ := h
  refine ⟨⟨t, fun j => σ ⟨min j t, by omega⟩, fun i => if hi : i < t then c ⟨i, hi⟩ else 0,
    fun j _ => hb _, fun i hi => ?_, fun i hi => by simp [show ¬ i < t by omega]⟩, ?_, ?_, ?_⟩
  · have e₁ : (⟨min i t, by omega⟩ : Fin (t + 1)) = (⟨i, hi⟩ : Fin t).castSucc :=
      Fin.ext (by simp; omega)
    have e₂ : (⟨min (i + 1) t, by omega⟩ : Fin (t + 1)) = (⟨i, hi⟩ : Fin t).succ :=
      Fin.ext (by simp; omega)
    simp only [dif_pos hi, e₁, e₂]
    exact hs _
  · simpa using h0
  · simp only [min_self]
    exact ht
  · rw [← hq, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by simp

namespace Trace

variable {S : ℕ} (T : Trace E I S)

theorem c_le_one (i : ℕ) : T.c i ≤ 1 := by
  rcases lt_or_ge i T.t with hi | hi
  · exact (T.step i hi).charge_le_one
  · simp [T.c_eq_zero i hi]

/-- If a vertex holds a red pebble at time `j` but not at time `0`, some move before `j` gave
it one. -/
theorem exists_new_red {v : V} (h0 : v ∉ (T.σ 0).1) :
    ∀ j, v ∈ (T.σ j).1 → ∃ i < j, v ∉ (T.σ i).1 ∧ v ∈ (T.σ (i + 1)).1 := by
  intro j
  induction j with
  | zero => exact fun h => absurd h h0
  | succ j ih =>
    intro h
    by_cases hj : v ∈ (T.σ j).1
    · obtain ⟨i, hi, rest⟩ := ih hj
      exact ⟨i, by omega, rest⟩
    · exact ⟨j, by omega, hj, h⟩

/-- If a vertex holds a blue pebble at time `j` but not at time `0`, some move before `j` gave
it one. -/
theorem exists_new_blue {v : V} (h0 : v ∉ (T.σ 0).2) :
    ∀ j, v ∈ (T.σ j).2 → ∃ i < j, v ∉ (T.σ i).2 ∧ v ∈ (T.σ (i + 1)).2 := by
  intro j
  induction j with
  | zero => exact fun h => absurd h h0
  | succ j ih =>
    intro h
    by_cases hj : v ∈ (T.σ j).2
    · obtain ⟨i, hi, rest⟩ := ih hj
      exact ⟨i, by omega, rest⟩
    · exact ⟨j, by omega, hj, h⟩

/-- A non-input that holds a pebble at time `j ≤ t`, in a calculation that starts from the
inputs alone, was computed by some move before `j`: at that move all its predecessors were red
and it was not. -/
theorem exists_compute {v : V} (hv : v ∉ I) (h0 : T.σ 0 = (∅, I)) :
    ∀ j ≤ T.t, (v ∈ (T.σ j).1 ∨ v ∈ (T.σ j).2) →
      ∃ i < j, v ∉ (T.σ i).1 ∧ (∀ u, E u v → u ∈ (T.σ i).1) ∧
        (T.σ (i + 1)).1 = insert v (T.σ i).1 := by
  intro j
  induction j with
  | zero =>
    intro _ h
    rw [h0] at h
    simp only [Finset.notMem_empty, false_or] at h
    exact absurd h hv
  | succ j ih =>
    intro hj h
    by_cases hprev : v ∈ (T.σ j).1 ∨ v ∈ (T.σ j).2
    · obtain ⟨i, hi, rest⟩ := ih (by omega) hprev
      exact ⟨i, by omega, rest⟩
    · simp only [not_or] at hprev
      obtain ⟨-, hp, hR, -⟩ := (T.step j (by omega)).first_pebble hprev.1 hprev.2 h
      exact ⟨j, by omega, hprev.1, hp, hR⟩

/-- **The trivial I/O bound.** If every input is red at some point and every output ends blue,
the inputs and outputs being disjoint, the calculation is charged at least `|I| + |O|`: each input
is loaded, each output stored, and no move does two of these. -/
theorem card_add_card_le {O : Finset V} (h0 : T.σ 0 = (∅, I)) (ht : (T.σ T.t).2 = O)
    (hIO : Disjoint I O) (hred : ∀ x ∈ I, ∃ j ≤ T.t, x ∈ (T.σ j).1) :
    I.card + O.card ≤ ∑ i ∈ range T.t, T.c i := by
  classical
  -- A move at which each input first turns red, and one at which each output first turns blue.
  have hI' : ∀ x ∈ I, ∃ i < T.t, x ∉ (T.σ i).1 ∧ x ∈ (T.σ (i + 1)).1 := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := hred x hx
    obtain ⟨i, hi, h⟩ := T.exists_new_red (by simp [h0]) j hxj
    exact ⟨i, by omega, h⟩
  have hO' : ∀ o ∈ O, ∃ i < T.t, o ∉ (T.σ i).2 ∧ o ∈ (T.σ (i + 1)).2 := by
    intro o ho
    have hoI : o ∉ I := fun h => Finset.disjoint_left.1 hIO h ho
    obtain ⟨i, hi, h⟩ := T.exists_new_blue (by simpa [h0] using hoI) T.t (by simpa [ht] using ho)
    exact ⟨i, hi, h⟩
  choose! gI hgI using hI'
  choose! gO hgO using hO'
  let g : V → ℕ := fun v => if v ∈ I then gI v else gO v
  have hmaps : Set.MapsTo g ↑(I ∪ O) ↑((range T.t).filter (fun i => T.c i = 1)) := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_union] at hv
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    by_cases hvI : v ∈ I
    · obtain ⟨hlt, h₁, h₂⟩ := hgI v hvI
      simp only [g, if_pos hvI]
      refine ⟨hlt, ?_⟩
      obtain ⟨-, (⟨hc, -⟩ | ⟨-, hvI', -⟩)⟩ := (T.step _ hlt).new_red h₁ h₂
      · exact hc
      · exact absurd hvI hvI'
    · have hvO : v ∈ O := hv.resolve_left hvI
      obtain ⟨hlt, h₁, h₂⟩ := hgO v hvO
      simp only [g, if_neg hvI]
      exact ⟨hlt, ((T.step _ hlt).new_blue h₁ h₂).2.1⟩
  have hinj : Set.InjOn g ↑(I ∪ O) := by
    intro v hv w hw hvw
    rw [Finset.mem_coe, Finset.mem_union] at hv hw
    by_cases hvI : v ∈ I <;> by_cases hwI : w ∈ I
    · obtain ⟨hlt, h₁, h₂⟩ := hgI v hvI
      obtain ⟨-, h₃, h₄⟩ := hgI w hwI
      simp only [g, if_pos hvI, if_pos hwI] at hvw
      rw [← hvw] at h₃ h₄
      exact (T.step _ hlt).eq_of_new_red h₁ h₂ h₃ h₄
    · obtain ⟨hlt, h₁, h₂⟩ := hgI v hvI
      obtain ⟨-, h₃, h₄⟩ := hgO w (hw.resolve_left hwI)
      simp only [g, if_pos hvI, if_neg hwI] at hvw
      rw [← hvw] at h₃ h₄
      exact ((T.step _ hlt).not_new_red_and_blue h₁ h₂ h₃ h₄).elim
    · obtain ⟨hlt, h₁, h₂⟩ := hgO v (hv.resolve_left hvI)
      obtain ⟨-, h₃, h₄⟩ := hgI w hwI
      simp only [g, if_neg hvI, if_pos hwI] at hvw
      rw [← hvw] at h₃ h₄
      exact ((T.step _ hlt).not_new_red_and_blue h₃ h₄ h₁ h₂).elim
    · obtain ⟨hlt, h₁, h₂⟩ := hgO v (hv.resolve_left hvI)
      obtain ⟨-, h₃, h₄⟩ := hgO w (hw.resolve_left hwI)
      simp only [g, if_neg hvI, if_neg hwI] at hvw
      rw [← hvw] at h₃ h₄
      exact (T.step _ hlt).eq_of_new_blue h₁ h₂ h₃ h₄
  calc I.card + O.card = (I ∪ O).card := (Finset.card_union_of_disjoint hIO).symm
    _ ≤ ((range T.t).filter (fun i => T.c i = 1)).card :=
        Finset.card_le_card_of_injOn g hmaps hinj
    _ = ∑ i ∈ range T.t, if T.c i = 1 then 1 else 0 := Finset.card_filter _ _
    _ ≤ ∑ i ∈ range T.t, T.c i := Finset.sum_le_sum fun i _ => by split_ifs with h <;> omega

end Trace

/-! ## Calculations built move by move -/

/-- `Run E I S s q s'`: a sequence of moves from `s` to `s'`, charged `q` in total, in which every
configuration after the first has at most `S` red pebbles. -/
inductive Run (E : V → V → Prop) (I : Finset V) (S : ℕ) :
    Finset V × Finset V → ℕ → Finset V × Finset V → Prop
  | refl (s : Finset V × Finset V) : Run E I S s 0 s
  | cons {s s' s'' : Finset V × Finset V} {c q : ℕ} :
      Step E I s c s' → s'.1.card ≤ S → Run E I S s' q s'' → Run E I S s (c + q) s''

namespace Run

variable {S : ℕ}

theorem trans {s s' s'' : Finset V × Finset V} {q q' : ℕ} (h : Run E I S s q s')
    (h' : Run E I S s' q' s'') : Run E I S s (q + q') s'' := by
  induction h with
  | refl => simpa using h'
  | cons hs hb _ ih => simpa [Nat.add_assoc] using Run.cons hs hb (ih h')

theorem cast {s s' t t' : Finset V × Finset V} {q q' : ℕ} (h : Run E I S s q s') (hs : s = t)
    (hq : q = q') (hs' : s' = t') : Run E I S t q' t' := by
  subst hs hq hs'
  exact h

/-- One move, as a run. -/
theorem single {s s' : Finset V × Finset V} {c : ℕ} (h : Step E I s c s') (hb : s'.1.card ≤ S) :
    Run E I S s c s' := by
  simpa using Run.cons h hb (Run.refl s')

/-- A run, read as the data of `HasCompleteCalculation`. -/
theorem exists_seq {s s' : Finset V × Finset V} {q : ℕ} (h : Run E I S s q s')
    (hs : s.1.card ≤ S) :
    ∃ (t : ℕ) (σ : Fin (t + 1) → Finset V × Finset V) (c : Fin t → ℕ),
      σ 0 = s ∧ σ (Fin.last t) = s' ∧ (∀ j, (σ j).1.card ≤ S) ∧
      (∀ i : Fin t, Step E I (σ i.castSucc) (c i) (σ i.succ)) ∧ ∑ i, c i = q := by
  induction h with
  | refl s =>
    exact ⟨0, fun _ => s, Fin.elim0, rfl, rfl, fun _ => hs, fun i => i.elim0, by simp⟩
  | @cons s₀ s₁ s₂ c₀ q₀ hstep hb _ ih =>
    obtain ⟨t, σ, c, h0, ht, hbud, hsteps, hq⟩ := ih hb
    refine ⟨t + 1, Fin.cons s₀ σ, Fin.cons c₀ c, rfl, ?_, ?_, ?_, ?_⟩
    · rw [← Fin.succ_last, Fin.cons_succ, ht]
    · intro j
      refine Fin.cases hs (fun j => ?_) j
      simpa using hbud j
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [h0] using hstep
      · rw [← Fin.succ_castSucc]
        simpa using hsteps i
    · rw [Fin.sum_cons, hq]

/-- A run from the inputs alone to the outputs alone is a complete calculation. -/
theorem hasCompleteCalculation {O : Finset V} {q : ℕ} (h : Run E I S (∅, I) q (∅, O)) :
    HasCompleteCalculation E I O S q := by
  obtain ⟨t, σ, c, h0, ht, hb, hs, hq⟩ := h.exists_seq (by simp)
  exact ⟨t, σ, c, h0, ht, hb, hs, hq⟩

end Run

end MiscMath.Computability.RedBluePebbleGame
