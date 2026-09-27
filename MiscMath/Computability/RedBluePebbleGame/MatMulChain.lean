/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Feasibility
import MiscMath.Computability.RedBluePebbleGame.MatMul
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# The red-blue pebble game: the ordinary algorithm for matrix multiplication, as a graph

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

The graph of the ordinary algorithm for the product of an `m × k` matrix `A` by a `k × n` matrix
`B`, each entry of the product summed left to right (`MatMulChain.edge`). Its vertices are the
entries of `A` and `B`, the products `A i l * B l j`, and for each entry `(i, j)` of the product
the partial sums of its products at positions `0, …, r + 1`, for `r < k - 1`. The inputs are the
vertices with no predecessor and the outputs those with no successor.

For `m, k, n ≥ 1` it is an `IsMatMulEvaluation` (`MatMulChain.isMatMulEvaluation`), and it has a
complete calculation exactly when `S ≥ 3` (`MatMulChain.complete_iff`): the witness of
`exists_isMatMulEvaluation`. Three red pebbles suffice for any finite graph whose non-inputs each
have exactly two predecessors and which some rank orders (`hasCompleteCalculation_of_rank`, which
generalises the FFT graph's `fft_run_union`): load the two predecessors, compute, store, clear.
-/

namespace MiscMath.Computability.RedBluePebbleGame

section General

variable {V : Type*} [DecidableEq V] {E : V → V → Prop} {I : Finset V} {S : ℕ}

omit [DecidableEq V] in
/-- A rank that every edge raises rules out cycles. -/
theorem acyclic_of_rank (f : V → ℕ) (hf : ∀ u v, E u v → f u < f v) (v : V) :
    ¬ Relation.TransGen E v v := by
  have key : ∀ u w, Relation.TransGen E u w → f u < f w := by
    intro u w h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact ih.trans (hf _ _ h)
  exact fun h => (key v v h).false

/-- In a graph ordered by a rank, in which every non-input has exactly two predecessors, every
predecessor-closed set of non-inputs can be computed and stored with three red pebbles. -/
theorem run_union_of_rank (f : V → ℕ) (hf : ∀ u v, E u v → f u < f v) (hS : 3 ≤ S)
    (hpred : ∀ v ∉ I, ∃ p₁ p₂, p₁ ≠ p₂ ∧ E p₁ v ∧ E p₂ v ∧ ∀ u, E u v → u = p₁ ∨ u = p₂)
    (X : Finset V) : (∀ v ∈ X, v ∉ I) → (∀ v ∈ X, ∀ u, E u v → u ∈ I ∨ u ∈ X) →
      ∃ q, Run E I S (∅, I) q (∅, I ∪ X) := by
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hXI hXc
    rcases X.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, (Run.refl _).cast rfl rfl (by simp)⟩
    · obtain ⟨v, hvX, hvmax⟩ := X.exists_max_image f hne
      obtain ⟨q, hq⟩ := ih (X.erase v) (Finset.erase_ssubset hvX)
        (fun w hw => hXI w (Finset.mem_of_mem_erase hw)) (by
          intro w hw u hu
          rcases hXc w (Finset.mem_of_mem_erase hw) u hu with h | h
          · exact Or.inl h
          · right
            refine Finset.mem_erase.2 ⟨?_, h⟩
            rintro rfl
            have h₁ := hvmax w (Finset.mem_of_mem_erase hw)
            have h₂ := hf _ _ hu
            omega)
      have hvI := hXI v hvX
      obtain ⟨p₁, p₂, h₁₂, hp₁, hp₂, hpred'⟩ := hpred v hvI
      have hmem : ∀ p, E p v → p ∈ I ∪ X.erase v := by
        intro p hp
        rcases hXc v hvX p hp with h | h
        · exact Finset.mem_union_left _ h
        · refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, h⟩)
          rintro rfl
          exact absurd (hf _ _ hp) (lt_irrefl _)
      have hne' : ∀ p, E p v → v ≠ p := by
        rintro p hp rfl
        exact absurd (hf _ _ hp) (lt_irrefl _)
      refine ⟨q + 3, hq.trans ((Run.block hvI ?_ hpred' (hmem _ hp₁) (hmem _ hp₂) h₁₂
        (hne' _ hp₁) (hne' _ hp₂) hS).cast rfl rfl ?_)⟩
      · simp [hvI]
      · rw [← Finset.union_insert, Finset.insert_erase hvX]

/-- **Three red pebbles suffice** for a finite graph ordered by a rank, in which every non-input has
exactly two predecessors, whatever its outputs: compute and store every vertex, then delete the
blue pebbles off the vertices that are not outputs. -/
theorem hasCompleteCalculation_of_rank [Finite V] (f : V → ℕ) (hf : ∀ u v, E u v → f u < f v)
    (hS : 3 ≤ S)
    (hpred : ∀ v ∉ I, ∃ p₁ p₂, p₁ ≠ p₂ ∧ E p₁ v ∧ E p₂ v ∧ ∀ u, E u v → u = p₁ ∨ u = p₂)
    (O : Finset V) : ∃ q, HasCompleteCalculation E I O S q := by
  have := Fintype.ofFinite V
  obtain ⟨q, hq⟩ := run_union_of_rank f hf hS hpred (Finset.univ.filter (· ∉ I))
    (fun v hv => (Finset.mem_filter.1 hv).2) (fun v _ u _ => by
      by_cases h : u ∈ I
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  have hU : I ∪ Finset.univ.filter (· ∉ I) = Finset.univ := by
    ext v
    by_cases h : v ∈ I <;> simp [h]
  refine ⟨q, Run.hasCompleteCalculation ((hq.trans (Run.deleteBlues _ (Finset.univ \ O)
    (by rw [hU]; exact Finset.subset_univ _))).cast rfl (by simp) ?_)⟩
  rw [hU]
  ext v <;> simp

end General

namespace MatMulChain

/-- The vertices of the graph of the ordinary algorithm for the product of an `m × k` matrix `A` by
a `k × n` matrix `B`, each entry of the product summed left to right. -/
inductive Vertex (m k n : ℕ) : Type
  /-- The entry `A i l`. -/
  | a (i : Fin m) (l : Fin k)
  /-- The entry `B l j`. -/
  | b (l : Fin k) (j : Fin n)
  /-- The product `A i l * B l j`. -/
  | prod (i : Fin m) (l : Fin k) (j : Fin n)
  /-- The partial sum of the products `A i l * B l j` for `l ≤ r + 1`. -/
  | sum (i : Fin m) (r : Fin (k - 1)) (j : Fin n)
  deriving DecidableEq, Fintype

variable {m k n : ℕ}

/-- The edges: each product from its two factors, the first partial sum of an entry from its first
two products, and each later partial sum from the one before it and the next product. Indices are
compared as natural numbers. -/
def edge : Vertex m k n → Vertex m k n → Prop
  | .a i l, .prod i' l' _ => i' = i ∧ l' = l
  | .b l j, .prod _ l' j' => l' = l ∧ j' = j
  | .prod i l j, .sum i' r j' => i' = i ∧ j' = j ∧ ((l : ℕ) = r + 1 ∨ (l : ℕ) = 0 ∧ (r : ℕ) = 0)
  | .sum i r j, .sum i' r' j' => i' = i ∧ j' = j ∧ (r' : ℕ) = r + 1
  | _, _ => False

instance : DecidableRel (edge (m := m) (k := k) (n := n)) := fun u v => by
  cases u <;> cases v <;> unfold edge <;> infer_instance

/-- A rank raised by every edge. -/
def rank : Vertex m k n → ℕ
  | .a _ _ => 0
  | .b _ _ => 0
  | .prod _ _ _ => 1
  | .sum _ r _ => r + 2

theorem rank_lt {u v : Vertex m k n} (h : edge u v) : rank u < rank v := by
  cases u <;> cases v <;> simp only [edge, rank] at h ⊢ <;> omega

/-- The entry of the product that a product or a partial sum belongs to. -/
def entry : Vertex m k n → Option (Fin m × Fin n)
  | .prod i _ j => some (i, j)
  | .sum i _ j => some (i, j)
  | _ => none

theorem entry_eq {u v : Vertex m k n} {e : Fin m × Fin n} (h : edge u v)
    (hu : entry u = some e) : entry v = some e := by
  cases u <;> cases v <;> simp_all [edge, entry]

/-- Everything reached from a product belongs to its entry. -/
theorem entry_of_reach {i : Fin m} {l : Fin k} {j : Fin n} {w : Vertex m k n}
    (h : Relation.ReflTransGen edge (.prod i l j) w) : entry w = some (i, j) := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact entry_eq h ih

variable (m k n) in
/-- The inputs: the vertices with no predecessor. -/
def inputs : Finset (Vertex m k n) := Finset.univ.filter fun v => ∀ u, ¬ edge u v

variable (m k n) in
/-- The outputs: the vertices with no successor. -/
def outputs : Finset (Vertex m k n) := Finset.univ.filter fun v => ∀ w, ¬ edge v w

theorem a_mem_inputs (i : Fin m) (l : Fin k) : Vertex.a i l ∈ inputs m k n := by
  simp only [inputs, Finset.mem_filter, Finset.mem_univ, true_and]
  intro u
  cases u <;> simp [edge]

theorem b_mem_inputs (l : Fin k) (j : Fin n) : Vertex.b l j ∈ inputs m k n := by
  simp only [inputs, Finset.mem_filter, Finset.mem_univ, true_and]
  intro u
  cases u <;> simp [edge]

theorem isComputationDAG (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IsComputationDAG (edge (m := m) (k := k) (n := n)) (inputs m k n) (outputs m k n) where
  acyclic := acyclic_of_rank rank fun _ _ h => rank_lt h
  inputs_eq_sources v := by simp [inputs]
  sinks_subset_outputs v hv := Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩
  disjoint := by
    rw [inputs, outputs, Finset.disjoint_filter]
    intro v _ hsrc hsink
    cases v with
    | a i l => exact hsink (.prod i l ⟨0, hn⟩) (by simp [edge])
    | b l j => exact hsink (.prod ⟨0, hm⟩ l j) (by simp [edge])
    | prod i l j => exact hsrc (.a i l) (by simp [edge])
    | sum i r j => exact hsrc (.prod i ⟨r + 1, by omega⟩ j) (by simp [edge])

theorem isMatMulLabelling :
    IsMatMulLabelling (edge (m := m) (k := k) (n := n)) (inputs m k n)
      (fun y => .a y.1 y.2) (fun z => .b z.1 z.2) (fun x => .prod x.1 x.2.1 x.2.2) where
  injective_a y y' h := by
    simp only [Vertex.a.injEq] at h
    exact Prod.ext h.1 h.2
  injective_b z z' h := by
    simp only [Vertex.b.injEq] at h
    exact Prod.ext h.1 h.2
  injective_p x x' h := by
    simp only [Vertex.prod.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  disjoint_ab := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
    simp at hz
  a_mem y := a_mem_inputs _ _
  b_mem z := b_mem_inputs _ _
  edge_a i l j := by simp [edge]
  edge_b i l j := by simp [edge]
  independent i l j i' l' j' w h h' := by
    have e := entry_of_reach h
    rw [entry_of_reach h'] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    exact ⟨e.1.symm, e.2.symm⟩

theorem isMatMulEvaluation (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IsMatMulEvaluation m k n (edge (m := m) (k := k) (n := n)) (inputs m k n) (outputs m k n) :=
  ⟨isComputationDAG hm hn, _, _, _, isMatMulLabelling⟩

/-- Every vertex that is not an input has exactly two predecessors. -/
theorem preds (v : Vertex m k n) (hv : v ∉ inputs m k n) :
    ∃ p₁ p₂, p₁ ≠ p₂ ∧ edge p₁ v ∧ edge p₂ v ∧ ∀ u, edge u v → u = p₁ ∨ u = p₂ := by
  cases v with
  | a i l => exact absurd (a_mem_inputs i l) hv
  | b l j => exact absurd (b_mem_inputs l j) hv
  | prod i l j =>
    refine ⟨.a i l, .b l j, by simp, by simp [edge], by simp [edge], fun u hu => ?_⟩
    cases u with
    | a i' l' =>
      simp only [edge] at hu
      obtain ⟨rfl, rfl⟩ := hu
      exact Or.inl rfl
    | b l' j' =>
      simp only [edge] at hu
      obtain ⟨rfl, rfl⟩ := hu
      exact Or.inr rfl
    | prod _ _ _ => simp [edge] at hu
    | sum _ _ _ => simp [edge] at hu
  | sum i r j =>
    have hr := r.isLt
    by_cases h0 : (r : ℕ) = 0
    · refine ⟨.prod i ⟨0, by omega⟩ j, .prod i ⟨1, by omega⟩ j, by simp, by simp [edge, h0],
        by simp [edge, h0], fun u hu => ?_⟩
      cases u with
      | prod i' l' j' =>
        simp only [edge] at hu
        obtain ⟨rfl, rfl, hl⟩ := hu
        rcases hl with hl | ⟨hl, -⟩
        · exact Or.inr (by rw [show l' = ⟨1, by omega⟩ from Fin.ext (by simp; omega)])
        · exact Or.inl (by rw [show l' = ⟨0, by omega⟩ from Fin.ext (by simp; omega)])
      | sum i' r' j' =>
        simp only [edge] at hu
        omega
      | a _ _ => simp [edge] at hu
      | b _ _ => simp [edge] at hu
    · refine ⟨.sum i ⟨r - 1, by omega⟩ j, .prod i ⟨r + 1, by omega⟩ j, by simp,
        by simp [edge]; omega, by simp [edge],
        fun u hu => ?_⟩
      cases u with
      | prod i' l' j' =>
        simp only [edge] at hu
        obtain ⟨rfl, rfl, hl⟩ := hu
        exact Or.inr (by rw [show l' = ⟨r + 1, by omega⟩ from Fin.ext (by simp; omega)])
      | sum i' r' j' =>
        simp only [edge] at hu
        obtain ⟨rfl, rfl, hr'⟩ := hu
        exact Or.inl (by rw [show r' = ⟨r - 1, by omega⟩ from Fin.ext (by simp; omega)])
      | a _ _ => simp [edge] at hu
      | b _ _ => simp [edge] at hu

/-- **Feasibility.** For `m, k, n ≥ 1` the graph has a complete calculation exactly when `S ≥ 3`. -/
theorem complete_iff (hm : 1 ≤ m) (hk : 1 ≤ k) (hn : 1 ≤ n) (S : ℕ) :
    (∃ q, HasCompleteCalculation (edge (m := m) (k := k) (n := n)) (inputs m k n)
      (outputs m k n) S q) ↔ 3 ≤ S :=
  ⟨fun ⟨_, hq⟩ => isMatMulLabelling.three_le (isComputationDAG hm hn)
      (⟨0, hm⟩, ⟨0, hk⟩, ⟨0, hn⟩) hq,
    fun hS => hasCompleteCalculation_of_rank rank (fun _ _ h => rank_lt h) hS preds _⟩

end MatMulChain

end MiscMath.Computability.RedBluePebbleGame
