/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Calculation
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# The red-blue pebble game: when the FFT graph can be pebbled at all

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

With three red pebbles the `2^k`-point FFT graph can be computed level by level: load a vertex's
two predecessors, compute it, store it, clear the red pebbles (`Run.block`), and finally delete the
blue pebbles off the outputs (`fft_hasCompleteCalculation`). With fewer it cannot: the move that
computes an output has its two predecessors red and places a third pebble
(`three_le_of_fft_hasCompleteCalculation`). A computed pebble is placed, not slid from a
predecessor; with sliding, two would do.
-/

namespace MiscMath.Computability.RedBluePebbleGame

section General

variable {V : Type*} [DecidableEq V] {E : V → V → Prop} {I : Finset V} {S : ℕ}

/-- Deleting red pebbles, one at a time, at no charge. -/
theorem Run.deleteReds (B R : Finset V) : R.card ≤ S → Run E I S (R, B) 0 (∅, B) := by
  induction R using Finset.induction_on with
  | empty => intro _; exact Run.refl _
  | insert a R ha ih =>
    intro hR
    have h₁ : Step E I (insert a R, B) 0 (R, B) := by
      have := Step.deleteRed (E := E) (I := I) (B := B) (Finset.mem_insert_self a R)
      rwa [Finset.erase_insert ha] at this
    have h₂ : R.card ≤ S := (Finset.card_le_card (Finset.subset_insert a R)).trans hR
    exact (Run.cons h₁ h₂ (ih h₂)).cast rfl rfl rfl

/-- Deleting blue pebbles, one at a time, at no charge. -/
theorem Run.deleteBlues (B Y : Finset V) : Y ⊆ B → Run E I S (∅, B) 0 (∅, B \ Y) := by
  induction Y using Finset.induction_on with
  | empty => intro _; exact (Run.refl _).cast rfl rfl (by simp)
  | insert a Y ha ih =>
    intro hY
    have hYB : Y ⊆ B := (Finset.subset_insert a Y).trans hY
    have haB : a ∈ B \ Y := Finset.mem_sdiff.2 ⟨hY (Finset.mem_insert_self a Y), ha⟩
    have r := (ih hYB).trans (Run.single (Step.deleteBlue (R := ∅) haB) (by simp))
    exact r.cast rfl rfl (by rw [Finset.sdiff_insert])

/-- One block: from a configuration with no red pebbles, a vertex whose two (distinct)
predecessors both hold blue pebbles is computed and stored at a charge of `3`, leaving no red
pebble behind. -/
theorem Run.block {B : Finset V} {v p₁ p₂ : V} (hvI : v ∉ I) (hvB : v ∉ B)
    (hpred : ∀ u, E u v → u = p₁ ∨ u = p₂) (hp₁ : p₁ ∈ B) (hp₂ : p₂ ∈ B)
    (h₁₂ : p₁ ≠ p₂) (hv₁ : v ≠ p₁) (hv₂ : v ≠ p₂) (hS : 3 ≤ S) :
    Run E I S (∅, B) 3 (∅, insert v B) := by
  have c₁ : (insert p₁ (∅ : Finset V)).card ≤ 1 := by simp
  have c₂ : (insert p₂ (insert p₁ (∅ : Finset V))).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by omega)
  have c₃ : (insert v (insert p₂ (insert p₁ (∅ : Finset V)))).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (by omega)
  have r₁ : Run E I S (∅, B) 1 (insert p₁ ∅, B) :=
    Run.single (Step.load hp₁ (Finset.notMem_empty _)) (by simp only; omega)
  have r₂ : Run E I S (insert p₁ ∅, B) 1 (insert p₂ (insert p₁ ∅), B) :=
    Run.single (Step.load hp₂ (fun h => h₁₂ ((Finset.mem_insert.1 h).resolve_right
      (Finset.notMem_empty _)).symm)) (by simp only; omega)
  have r₃ : Run E I S (insert p₂ (insert p₁ ∅), B) 0
      (insert v (insert p₂ (insert p₁ ∅)), B) :=
    Run.single (Step.compute hvI (by simp [hv₁, hv₂])
      (fun u hu => by rcases hpred u hu with rfl | rfl <;> simp)) (by simp only; omega)
  have r₄ : Run E I S (insert v (insert p₂ (insert p₁ ∅)), B) 1
      (insert v (insert p₂ (insert p₁ ∅)), insert v B) :=
    Run.single (Step.store (Finset.mem_insert_self v _) hvB) (by simp only; omega)
  have r₅ : Run E I S (insert v (insert p₂ (insert p₁ ∅)), insert v B) 0 (∅, insert v B) :=
    Run.deleteReds _ _ (by omega)
  exact (r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅)))).cast rfl rfl rfl

end General

/-- In the FFT graph, a vertex off level `0` has exactly two predecessors, and they are
distinct. -/
theorem fftEdge_preds {k : ℕ} (v : Fin (k + 1) × Fin (2 ^ k)) (hv : (v.1 : ℕ) ≠ 0) :
    ∃ p₁ p₂, p₁ ≠ p₂ ∧ fftEdge k p₁ v ∧ fftEdge k p₂ v ∧
      ∀ u, fftEdge k u v → u = p₁ ∨ u = p₂ := by
  obtain ⟨⟨l, hl⟩, ⟨x, hx⟩⟩ := v
  simp only at hv
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hm : m < k := by omega
  have hpow : 2 ^ m < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hm
  have hxor : x ^^^ 2 ^ m < 2 ^ k := Nat.xor_lt_two_pow hx hpow
  refine ⟨(⟨m, by omega⟩, ⟨x, hx⟩), (⟨m, by omega⟩, ⟨x ^^^ 2 ^ m, hxor⟩), ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : x = x ^^^ 2 ^ m := by
      have := congrArg (fun p : Fin (k + 1) × Fin (2 ^ k) => (p.2 : ℕ)) h
      simpa using this
    have h'' : x ^^^ x = x ^^^ (x ^^^ 2 ^ m) := by rw [← h']
    rw [Nat.xor_self, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h''
    exact absurd h''.symm (by positivity)
  · exact ⟨rfl, Or.inl rfl⟩
  · refine ⟨rfl, Or.inr ?_⟩
    simp [Nat.xor_assoc]
  · rintro ⟨⟨l', hl'⟩, ⟨y, hy⟩⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have : l' = m := by omega
    subst this
    rcases h2 with h2 | h2
    · left
      ext <;> simp [h2]
    · right
      ext
      · simp
      · simp only
        rw [h2, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The level of a predecessor, in the FFT graph. -/
theorem fftEdge.level {k : ℕ} {u v : Fin (k + 1) × Fin (2 ^ k)} (h : fftEdge k u v) :
    (v.1 : ℕ) = (u.1 : ℕ) + 1 := h.1

/-- Every predecessor-closed set of non-inputs of the FFT graph can be computed and stored. -/
theorem fft_run_union {k S : ℕ} {I : Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hI : ∀ v, v ∈ I ↔ (v.1 : ℕ) = 0) (hS : 3 ≤ S) (X : Finset (Fin (k + 1) × Fin (2 ^ k))) :
    (∀ v ∈ X, (v.1 : ℕ) ≠ 0) →
      (∀ v ∈ X, ∀ u, fftEdge k u v → u ∈ I ∨ u ∈ X) →
        ∃ q, Run (fftEdge k) I S (∅, I) q (∅, I ∪ X) := by
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hX0 hXc
    rcases X.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, (Run.refl _).cast rfl rfl (by simp)⟩
    · obtain ⟨v, hvX, hvmax⟩ := X.exists_max_image (fun v => (v.1 : ℕ)) hne
      obtain ⟨q, hq⟩ := ih (X.erase v) (Finset.erase_ssubset hvX)
        (fun w hw => hX0 w (Finset.mem_of_mem_erase hw)) (by
          intro w hw u hu
          rcases hXc w (Finset.mem_of_mem_erase hw) u hu with h | h
          · exact Or.inl h
          · right
            refine Finset.mem_erase.2 ⟨?_, h⟩
            rintro rfl
            have h₁ := hvmax w (Finset.mem_of_mem_erase hw)
            have h₂ := hu.level
            omega)
      obtain ⟨p₁, p₂, h₁₂, hp₁, hp₂, hpred⟩ := fftEdge_preds v (hX0 v hvX)
      have hvI : v ∉ I := fun h => hX0 v hvX ((hI v).1 h)
      have hmem : ∀ p, fftEdge k p v → p ∈ I ∪ X.erase v := by
        intro p hp
        rcases hXc v hvX p hp with h | h
        · exact Finset.mem_union_left _ h
        · refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, h⟩)
          rintro rfl
          have := hp.level
          omega
      have hne' : ∀ p, fftEdge k p v → v ≠ p := by
        rintro p hp rfl
        have := hp.level
        omega
      refine ⟨q + 3, hq.trans ((Run.block hvI ?_ hpred (hmem _ hp₁) (hmem _ hp₂) h₁₂
        (hne' _ hp₁) (hne' _ hp₂) hS).cast rfl rfl ?_)⟩
      · simp [hvI]
      · rw [← Finset.union_insert, Finset.insert_erase hvX]

/-- The FFT graph has a complete calculation for every budget `S ≥ 3`, `k = 0` included. -/
theorem fft_hasCompleteCalculation {k S : ℕ} (hS : 3 ≤ S) :
    ∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q := by
  have hI : ∀ v : Fin (k + 1) × Fin (2 ^ k),
      v ∈ Finset.univ.filter (·.1 = 0) ↔ (v.1 : ℕ) = 0 := by
    intro v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.val_eq_zero_iff.symm
  obtain ⟨q, hq⟩ := fft_run_union hI hS (Finset.univ.filter (fun v => (v.1 : ℕ) ≠ 0))
    (fun v hv => (Finset.mem_filter.1 hv).2) (by
      intro v _ u _
      by_cases h : (u.1 : ℕ) = 0
      · exact Or.inl ((hI u).2 h)
      · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  refine ⟨q, Run.hasCompleteCalculation ?_⟩
  have hdel := Run.deleteBlues (E := fftEdge k) (I := Finset.univ.filter (·.1 = 0)) (S := S)
    (Finset.univ.filter (·.1 = 0) ∪ Finset.univ.filter (fun v => (v.1 : ℕ) ≠ 0))
    (Finset.univ.filter (fun v : Fin (k + 1) × Fin (2 ^ k) => v.1 ≠ Fin.last k))
    (by
      intro v _
      by_cases h : (v.1 : ℕ) = 0
      · exact Finset.mem_union_left _ ((hI v).2 h)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  refine (hq.trans hdel).cast rfl (by simp) ?_
  refine Prod.ext rfl ?_
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    not_not]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_cases h' : (v.1 : ℕ) = 0
    · exact Or.inl (Fin.val_eq_zero_iff.1 h')
    · exact Or.inr h'

/-- For `k ≥ 1`, every complete calculation of the FFT graph needs at least 3 red pebbles. -/
theorem three_le_of_fft_hasCompleteCalculation {k S q : ℕ} (hk : 1 ≤ k)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) : 3 ≤ S := by
  obtain ⟨T, h0, ht, -⟩ := h.exists_trace
  have h2k : 0 < 2 ^ k := by positivity
  have h2k' : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  set o : Fin (k + 1) × Fin (2 ^ k) := (Fin.last k, ⟨0, h2k⟩) with ho
  set p₁ : Fin (k + 1) × Fin (2 ^ k) := (⟨k - 1, by omega⟩, ⟨0, h2k⟩) with hp₁
  set p₂ : Fin (k + 1) × Fin (2 ^ k) := (⟨k - 1, by omega⟩, ⟨2 ^ (k - 1), h2k'⟩) with hp₂
  have hoI : o ∉ Finset.univ.filter (fun v : Fin (k + 1) × Fin (2 ^ k) => v.1 = 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ho, Fin.last_eq_zero_iff]
    omega
  have hoT : o ∈ (T.σ T.t).2 := by
    rw [ht]
    simp [ho]
  obtain ⟨i, hi, -, hpred, hins⟩ := T.exists_compute hoI h0 T.t le_rfl (Or.inr hoT)
  have e₁ : fftEdge k p₁ o := ⟨by simp only [ho, hp₁, Fin.val_last]; omega, Or.inl rfl⟩
  have e₂ : fftEdge k p₂ o :=
    ⟨by simp only [ho, hp₂, Fin.val_last]; omega, Or.inr (by simp [ho, hp₂])⟩
  have hsub : ({o, p₁, p₂} : Finset _) ⊆ (T.σ (i + 1)).1 := by
    rw [hins]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hpred _ e₁)
    · exact Finset.mem_insert_of_mem (hpred _ e₂)
  have hcard : ({o, p₁, p₂} : Finset _).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨o, p₁, p₂, ?_, ?_, ?_, rfl⟩
    · intro h
      have := congrArg (fun p : Fin (k + 1) × Fin (2 ^ k) => (p.1 : ℕ)) h
      simp only [ho, hp₁, Fin.val_last] at this
      omega
    · intro h
      have := congrArg (fun p : Fin (k + 1) × Fin (2 ^ k) => (p.1 : ℕ)) h
      simp only [ho, hp₂, Fin.val_last] at this
      omega
    · intro h
      have := congrArg (fun p : Fin (k + 1) × Fin (2 ^ k) => (p.2 : ℕ)) h
      simp only [hp₁, hp₂] at this
      exact absurd this.symm (by positivity)
  calc 3 = ({o, p₁, p₂} : Finset _).card := hcard.symm
    _ ≤ (T.σ (i + 1)).1.card := Finset.card_le_card hsub
    _ ≤ S := T.budget (i + 1) (by omega)

end MiscMath.Computability.RedBluePebbleGame
