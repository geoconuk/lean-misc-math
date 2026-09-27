/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Parts
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# The red-blue pebble game: the I/O bounds for matrix multiplication

Support module of `MiscMath.Computability.RedBluePebbleGame`, where the results are stated and
where the reader should start. Nothing here is a result on its own.

This is Hong and Kung's §6 for the graphs of `IsMatMulEvaluation`, by way of their Theorem 3.1.
A complete calculation with `S` red pebbles gives a `2S`-partition into `h` parts, `S h ≤ q + S`
(`exists_isPartition`). Each part holds at most `S √(2S)` products (`card_prod_mem_le`, which takes
the place of the source's Lemma 6.1):

* a product in the part leads, inside the part, to a vertex with no successor there, which lies in
  the part's minimum set; products for different entries of the result lead to different such
  vertices (`independent`), so the part meets at most `2S` entries of the result;
* a product in the part is in its dominator, or both its factors are;
* so, slice by slice in the inner index `l`, the products of the part outside the dominator number
  at most `min(2S, α_l β_l) ≤ √(2S) (α_l + β_l) / 2`, where `α_l` and `β_l` count the entries of
  column `l` of `A` and of row `l` of `B` in the dominator.

Summing over the parts gives `m k n ≤ (q + S) √(2S)` (`mul_le_of_isMatMulLabelling`). Alongside
it: every input is loaded and every output stored, so `q ≥ m k + k n + m n`
(`add_le_of_isMatMulLabelling`), and a calculation needs three red pebbles as soon as there is a
product (`IsMatMulLabelling.three_le`).
-/

namespace MiscMath.Computability.RedBluePebbleGame

open Finset Relation

variable {V : Type*} [DecidableEq V] {E : V → V → Prop} {I O : Finset V}

/-! ## Facts about a complete calculation of a computation DAG -/

omit [DecidableEq V] in
/-- An input of a computation DAG has a successor: it reaches an output, and it is not one. -/
theorem IsComputationDAG.exists_succ_of_mem [Finite V] (hG : IsComputationDAG E I O) {x : V}
    (hx : x ∈ I) : ∃ w, E x w := by
  obtain ⟨o, ho, hpath⟩ := hG.exists_output x
  rcases hpath.cases_head with rfl | ⟨w, hxw, -⟩
  · exact absurd ho (Finset.disjoint_left.1 hG.disjoint hx)
  · exact ⟨w, hxw⟩

namespace Trace

variable {S : ℕ} (T : Trace E I S)

/-- In a complete calculation of a computation DAG, every vertex holds a pebble at some point: it
reaches an output, which ends blue, and a vertex is computed only once its predecessors are red. -/
theorem exists_pebbled [Finite V] (hG : IsComputationDAG E I O) (h0 : T.σ 0 = (∅, I))
    (ht : T.σ T.t = (∅, O)) (v : V) : ∃ j ≤ T.t, v ∈ (T.σ j).1 ∨ v ∈ (T.σ j).2 := by
  obtain ⟨o, ho, hpath⟩ := hG.exists_output v
  induction hpath using ReflTransGen.head_induction_on with
  | refl => exact ⟨T.t, le_rfl, Or.inr (by rw [ht]; exact ho)⟩
  | head huv _ ih =>
    obtain ⟨j, hj, hw⟩ := ih
    obtain ⟨i, hi, -, hp, -⟩ := T.exists_compute (hG.not_mem_inputs huv) h0 j hj hw
    exact ⟨i, by omega, Or.inl (hp _ huv)⟩

/-- In a complete calculation of a computation DAG, a vertex with a successor holds a red pebble at
some point: the successor is computed, and then it is red. -/
theorem exists_red_of_edge [Finite V] (hG : IsComputationDAG E I O) (h0 : T.σ 0 = (∅, I))
    (ht : T.σ T.t = (∅, O)) {u v : V} (huv : E u v) : ∃ i ≤ T.t, u ∈ (T.σ i).1 := by
  obtain ⟨j, hj, hv⟩ := T.exists_pebbled hG h0 ht v
  obtain ⟨i, hi, -, hp, -⟩ := T.exists_compute (hG.not_mem_inputs huv) h0 j hj hv
  exact ⟨i, by omega, hp u huv⟩

end Trace

/-! ## Facts about a matrix-multiplication labelling -/

namespace IsMatMulLabelling

variable {m k n : ℕ} {a : Fin m × Fin k → V} {b : Fin k × Fin n → V}
  {p : Fin m × Fin k × Fin n → V}

omit [DecidableEq V] in
/-- A product is not an input: it has a predecessor. -/
theorem prod_notMem (hG : IsComputationDAG E I O) (hL : IsMatMulLabelling E I a b p)
    (x : Fin m × Fin k × Fin n) : p x ∉ I :=
  hG.not_mem_inputs (hL.edge_a x.1 x.2.1 x.2.2)

omit [DecidableEq V] in
theorem prod_ne_a (hG : IsComputationDAG E I O) (hL : IsMatMulLabelling E I a b p)
    (x : Fin m × Fin k × Fin n) (y : Fin m × Fin k) : p x ≠ a y := fun h =>
  hL.prod_notMem hG x (h ▸ hL.a_mem y)

omit [DecidableEq V] in
theorem prod_ne_b (hG : IsComputationDAG E I O) (hL : IsMatMulLabelling E I a b p)
    (x : Fin m × Fin k × Fin n) (z : Fin k × Fin n) : p x ≠ b z := fun h =>
  hL.prod_notMem hG x (h ▸ hL.b_mem z)

omit [DecidableEq V] in
theorem a_ne_b (hL : IsMatMulLabelling E I a b p) (y : Fin m × Fin k) (z : Fin k × Fin n) :
    a y ≠ b z := fun h =>
  Set.disjoint_left.1 hL.disjoint_ab ⟨y, rfl⟩ ⟨z, h.symm⟩

/-- **Three red pebbles are needed.** When a product is first computed, it and its two factors are
all red. -/
theorem three_le [Finite V] {S q : ℕ} (hG : IsComputationDAG E I O)
    (hL : IsMatMulLabelling E I a b p) (x : Fin m × Fin k × Fin n)
    (hq : HasCompleteCalculation E I O S q) : 3 ≤ S := by
  obtain ⟨T, h0, ht, -⟩ := hq.exists_trace
  obtain ⟨i, l, j⟩ := x
  obtain ⟨τ, hτ, hpeb⟩ := T.exists_pebbled hG h0 ht (p (i, l, j))
  obtain ⟨s, hs, -, hpred, hins⟩ := T.exists_compute (hL.prod_notMem hG _) h0 τ hτ hpeb
  have ha : a (i, l) ∈ (T.σ s).1 := hpred _ (hL.edge_a i l j)
  have hb : b (l, j) ∈ (T.σ s).1 := hpred _ (hL.edge_b i l j)
  have hsub : ({p (i, l, j), a (i, l), b (l, j)} : Finset V) ⊆ (T.σ (s + 1)).1 := by
    rw [hins]
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ha
    · exact Finset.mem_insert_of_mem hb
  have hcard : ({p (i, l, j), a (i, l), b (l, j)} : Finset V).card = 3 :=
    Finset.card_eq_three.2 ⟨_, _, _, hL.prod_ne_a hG _ _, hL.prod_ne_b hG _ _, hL.a_ne_b _ _, rfl⟩
  calc 3 = _ := hcard.symm
    _ ≤ (T.σ (s + 1)).1.card := Finset.card_le_card hsub
    _ ≤ S := T.budget (s + 1) (by omega)

end IsMatMulLabelling

/-! ## The trivial bound -/

/-- **Every input is loaded and every output stored.** The entries of the two matrices are distinct
inputs, and for `k ≥ 1` the entries of the result lead to distinct outputs, so a complete
calculation is charged `q ≥ m k + k n + m n`. -/
theorem add_le_of_isMatMulLabelling [Finite V] {m k n S q : ℕ} {a : Fin m × Fin k → V}
    {b : Fin k × Fin n → V} {p : Fin m × Fin k × Fin n → V} (hG : IsComputationDAG E I O)
    (hL : IsMatMulLabelling E I a b p) (hk : 1 ≤ k) (hq : HasCompleteCalculation E I O S q) :
    m * k + k * n + m * n ≤ q := by
  classical
  obtain ⟨T, h0, ht, hsum⟩ := hq.exists_trace
  have hred : ∀ x ∈ I, ∃ j ≤ T.t, x ∈ (T.σ j).1 := fun x hx => by
    obtain ⟨w, hxw⟩ := hG.exists_succ_of_mem hx
    exact T.exists_red_of_edge hG h0 ht hxw
  have hIO := T.card_add_card_le h0 (by rw [ht]) hG.disjoint hred
  rw [hsum] at hIO
  -- The entries of `A` and `B` are `m k + k n` distinct inputs.
  have hI : m * k + k * n ≤ I.card := by
    have hdisj : Disjoint (univ.image a) (univ.image b) := by
      rw [disjoint_left]
      intro v hva hvb
      obtain ⟨y, -, rfl⟩ := mem_image.1 hva
      obtain ⟨z, -, hz⟩ := mem_image.1 hvb
      exact hL.a_ne_b y z hz.symm
    have hsub : univ.image a ∪ univ.image b ⊆ I := by
      refine union_subset (fun v hv => ?_) (fun v hv => ?_)
      · obtain ⟨y, -, rfl⟩ := mem_image.1 hv
        exact hL.a_mem y
      · obtain ⟨z, -, rfl⟩ := mem_image.1 hv
        exact hL.b_mem z
    calc m * k + k * n = (univ.image a).card + (univ.image b).card := by
          rw [card_image_of_injective _ hL.injective_a, card_image_of_injective _ hL.injective_b]
          simp
      _ = (univ.image a ∪ univ.image b).card := (card_union_of_disjoint hdisj).symm
      _ ≤ I.card := card_le_card hsub
  -- The products `p (i, 0, j)` lead to `m n` distinct outputs.
  have hO : m * n ≤ O.card := by
    calc m * n = (univ : Finset (Fin m × Fin n)).card := by simp
      _ ≤ O.card := card_le_card_of_forall_subsingleton
          (fun e o => ReflTransGen E (p (e.1, ⟨0, hk⟩, e.2)) o)
          (fun e _ => hG.exists_output _)
          (fun o _ e he e' he' =>
            have h := hL.independent _ _ _ _ _ _ o he.2 he'.2
            Prod.ext h.1 h.2)
  exact (Nat.add_le_add hI hO).trans hIO

/-! ## The products in one part -/

omit [DecidableEq V] in
/-- In a finite graph with no cycle, a vertex of a set `U` leads, along edges inside `U`, to a
vertex of `U` with no successor in `U`. -/
theorem exists_sink_in [Finite V] (hE : ∀ v, ¬ TransGen E v v) {U : Finset V} {v : V}
    (hv : v ∈ U) : ∃ w ∈ U, ReflTransGen E v w ∧ ∀ w' ∈ U, ¬ E w w' := by
  have hE' : ∀ v, ¬ TransGen (fun x y => E x y ∧ x ∈ U ∧ y ∈ U) v v :=
    fun v h => hE v (TransGen.mono (fun _ _ h => h.1) _ _ h)
  obtain ⟨w, hw, hs⟩ := exists_sink_of_acyclic hE' v
  have hwU : w ∈ U := by
    rcases hw.cases_tail with rfl | ⟨u, -, -, -, hwU⟩
    · exact hv
    · exact hwU
  exact ⟨w, hwU, ReflTransGen.mono (fun _ _ h => h.1) _ _ hw,
    fun w' hw' hww' => hs w' ⟨hww', hwU, hw'⟩⟩

/-- One slice of the count: at most `min(s, α β)` things, where `α β` bounds them one way and `s`
another, number at most `√s (α + β) / 2`. -/
theorem le_sqrt_mul_add_div_two {t α β s : ℝ} (ht : 0 ≤ t) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hs : 0 ≤ s) (h₁ : t ≤ s) (h₂ : t ≤ α * β) : t ≤ Real.sqrt s * (α + β) / 2 := by
  refine le_of_sq_le_sq ?_ (by positivity)
  have hts : t ^ 2 ≤ s * (α * β) := by
    rw [sq]
    exact mul_le_mul h₁ h₂ ht hs
  have hsq : (Real.sqrt s * (α + β) / 2) ^ 2 = s * (α + β) ^ 2 / 4 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hs]
    ring
  rw [hsq]
  nlinarith [mul_nonneg hs (sq_nonneg (α - β))]

/-- **The products in one part, the source's Lemma 6.1 in the form the proof needs.** A set `U`
dominated by at most `s ≥ 4` vertices, of which at most `s` have no successor in `U`, holds at most
`s √s / 2` products. -/
theorem card_prod_mem_le [Finite V] {m k n s : ℕ} {a : Fin m × Fin k → V} {b : Fin k × Fin n → V}
    {p : Fin m × Fin k × Fin n → V} (hG : IsComputationDAG E I O)
    (hL : IsMatMulLabelling E I a b p) (hs : 4 ≤ s) {U D M : Finset V} (hD : D.card ≤ s)
    (hDom : Dominates E I D U) (hM : ∀ v ∈ U, (∀ w ∈ U, ¬ E v w) → v ∈ M) (hMs : M.card ≤ s) :
    ((univ.filter fun x : Fin m × Fin k × Fin n => p x ∈ U).card : ℝ) ≤ s * Real.sqrt s / 2 := by
  classical
  -- The entries of the result with a product in `U`: at most `s`, one vertex of `M` each.
  set Y : Finset (Fin m × Fin n) := univ.filter fun e => ∃ l, p (e.1, l, e.2) ∈ U with hY
  have hYs : Y.card ≤ s := by
    refine le_trans (card_le_card_of_forall_subsingleton (t := M)
      (fun e w => ∃ l, ReflTransGen E (p (e.1, l, e.2)) w) (fun e he => ?_)
      (fun w _ e he e' he' => ?_)) hMs
    · obtain ⟨l, hl⟩ := (mem_filter.1 he).2
      obtain ⟨w, hwU, hpath, hsink⟩ := exists_sink_in hG.acyclic hl
      exact ⟨w, hM w hwU hsink, l, hpath⟩
    · obtain ⟨-, l, hl⟩ := he
      obtain ⟨-, l', hl'⟩ := he'
      have h := hL.independent _ _ _ _ _ _ w hl hl'
      exact Prod.ext h.1 h.2
  -- A product of `U` outside `D` has both its factors in `D`.
  have hfac : ∀ x : Fin m × Fin k × Fin n, p x ∈ U → p x ∉ D →
      a (x.1, x.2.1) ∈ D ∧ b (x.2.1, x.2.2) ∈ D := by
    rintro ⟨i, l, j⟩ hU hD'
    constructor
    · by_contra ha
      exact hDom _ (hL.a_mem _) ha _ hU (ReflTransGen.single ⟨hL.edge_a i l j, ha, hD'⟩)
    · by_contra hb
      exact hDom _ (hL.b_mem _) hb _ hU (ReflTransGen.single ⟨hL.edge_b i l j, hb, hD'⟩)
  set PU := univ.filter fun x : Fin m × Fin k × Fin n => p x ∈ U with hPU_def
  set PD := univ.filter fun x : Fin m × Fin k × Fin n => p x ∈ D with hPD_def
  set XA := univ.filter fun y : Fin m × Fin k => a y ∈ D with hXA_def
  set XB := univ.filter fun z : Fin k × Fin n => b z ∈ D with hXB_def
  set T := univ.filter fun x : Fin m × Fin k × Fin n =>
    (x.1, x.2.2) ∈ Y ∧ a (x.1, x.2.1) ∈ D ∧ b (x.2.1, x.2.2) ∈ D with hT_def
  -- The products of `U` are those in `D` and those counted by `T`.
  have hPU : PU.card ≤ PD.card + T.card := by
    refine (card_le_card fun x hx => ?_).trans (card_union_le PD T)
    have hxU : p x ∈ U := (mem_filter.1 hx).2
    by_cases hxD : p x ∈ D
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hxD⟩)
    · obtain ⟨ha, hb⟩ := hfac x hxU hxD
      exact mem_union_right _
        (mem_filter.2 ⟨mem_univ _, mem_filter.2 ⟨mem_univ _, x.2.1, hxU⟩, ha, hb⟩)
  -- The products, entries of `A` and entries of `B` in `D` are distinct vertices of `D`.
  have hDsum : PD.card + XA.card + XB.card ≤ D.card := by
    have h₁ : Disjoint (PD.image p) (XA.image a) := by
      rw [disjoint_left]
      intro v hv hv'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hv
      obtain ⟨y, -, hy⟩ := mem_image.1 hv'
      exact hL.prod_ne_a hG x y hy.symm
    have h₂ : Disjoint (PD.image p ∪ XA.image a) (XB.image b) := by
      rw [disjoint_left]
      intro v hv hv'
      obtain ⟨z, -, rfl⟩ := mem_image.1 hv'
      rcases mem_union.1 hv with hv | hv
      · obtain ⟨x, -, hx⟩ := mem_image.1 hv
        exact hL.prod_ne_b hG x z hx
      · obtain ⟨y, -, hy⟩ := mem_image.1 hv
        exact hL.a_ne_b y z hy
    have hsub : PD.image p ∪ XA.image a ∪ XB.image b ⊆ D := by
      refine union_subset (union_subset (fun v hv => ?_) (fun v hv => ?_)) (fun v hv => ?_)
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hv
        exact (mem_filter.1 hx).2
      · obtain ⟨y, hy, rfl⟩ := mem_image.1 hv
        exact (mem_filter.1 hy).2
      · obtain ⟨z, hz, rfl⟩ := mem_image.1 hv
        exact (mem_filter.1 hz).2
    calc PD.card + XA.card + XB.card
        = (PD.image p).card + (XA.image a).card + (XB.image b).card := by
          rw [card_image_of_injective _ hL.injective_p, card_image_of_injective _ hL.injective_a,
            card_image_of_injective _ hL.injective_b]
      _ = (PD.image p ∪ XA.image a ∪ XB.image b).card := by
          rw [card_union_of_disjoint h₂, card_union_of_disjoint h₁]
      _ ≤ D.card := card_le_card hsub
  -- Slice by the inner index `l`.
  set Tl : Fin k → Finset (Fin m × Fin k × Fin n) := fun l => T.filter fun x => x.2.1 = l
    with hTl_def
  set Al : Fin k → Finset (Fin m × Fin k) := fun l => XA.filter fun y => y.2 = l with hAl_def
  set Bl : Fin k → Finset (Fin k × Fin n) := fun l => XB.filter fun z => z.1 = l with hBl_def
  have hTY : ∀ l, (Tl l).card ≤ Y.card := by
    intro l
    refine card_le_card_of_injOn (fun x => (x.1, x.2.2)) (fun x hx => ?_) (fun x hx x' hx' h => ?_)
    · exact (mem_filter.1 (mem_filter.1 hx).1).2.1
    · have e₁ : x.2.1 = l := (mem_filter.1 hx).2
      have e₂ : x'.2.1 = l := (mem_filter.1 hx').2
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext (e₁.trans e₂.symm) h.2)
  have hTAB : ∀ l, (Tl l).card ≤ (Al l).card * (Bl l).card := by
    intro l
    rw [← card_product]
    refine card_le_card_of_injOn (fun x => ((x.1, x.2.1), (x.2.1, x.2.2))) (fun x hx => ?_)
      (fun x _ x' _ h => ?_)
    · have hT' := mem_filter.1 hx
      have hx' := (mem_filter.1 hT'.1).2
      refine mem_product.2 ⟨mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hx'.2.1⟩, hT'.2⟩,
        mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hx'.2.2⟩, hT'.2⟩⟩
    · simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2.2)
  have hTsum : T.card = ∑ l, (Tl l).card :=
    card_eq_sum_card_fiberwise (f := fun x : Fin m × Fin k × Fin n => x.2.1) (t := univ)
      fun _ _ => mem_coe.2 (mem_univ _)
  have hXAsum : XA.card = ∑ l, (Al l).card :=
    card_eq_sum_card_fiberwise (f := fun y : Fin m × Fin k => y.2) (t := univ)
      fun _ _ => mem_coe.2 (mem_univ _)
  have hXBsum : XB.card = ∑ l, (Bl l).card :=
    card_eq_sum_card_fiberwise (f := fun z : Fin k × Fin n => z.1) (t := univ)
      fun _ _ => mem_coe.2 (mem_univ _)
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hT : (T.card : ℝ) ≤ Real.sqrt s * (XA.card + XB.card) / 2 := by
    rw [hTsum, hXAsum, hXBsum]
    push_cast
    calc ∑ l, ((Tl l).card : ℝ)
        ≤ ∑ l, Real.sqrt s * (((Al l).card : ℝ) + (Bl l).card) / 2 :=
          sum_le_sum fun l _ => le_sqrt_mul_add_div_two (Nat.cast_nonneg _) (Nat.cast_nonneg _)
            (Nat.cast_nonneg _) hs0 (by exact_mod_cast (hTY l).trans hYs)
            (by exact_mod_cast hTAB l)
      _ = Real.sqrt s * (∑ l, ((Al l).card : ℝ) + ∑ l, ((Bl l).card : ℝ)) / 2 := by
          rw [← sum_add_distrib, mul_sum, sum_div]
  have hsqrt : 2 ≤ Real.sqrt s := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hs)
  have hPU' : (PU.card : ℝ) ≤ PD.card + T.card := by exact_mod_cast hPU
  have hDsum' : (PD.card : ℝ) + XA.card + XB.card ≤ s := by exact_mod_cast hDsum.trans hD
  have hd0 : (0 : ℝ) ≤ PD.card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left
      (show (XA.card : ℝ) + XB.card ≤ s - PD.card by linarith) (Real.sqrt_nonneg s),
    mul_nonneg hd0 (show 0 ≤ Real.sqrt s - 2 by linarith)]

/-! ## All the products -/

/-- **The domination bound, Hong and Kung's Corollary 6.2 in finitary form.** A complete calculation
with `S ≥ 2` red pebbles, charged `q`, has `m k n ≤ (q + S) √(2S)`. -/
theorem mul_le_of_isMatMulLabelling [Finite V] {m k n S q : ℕ} {a : Fin m × Fin k → V}
    {b : Fin k × Fin n → V} {p : Fin m × Fin k × Fin n → V} (hG : IsComputationDAG E I O)
    (hL : IsMatMulLabelling E I a b p) (hS : 2 ≤ S) (hq : HasCompleteCalculation E I O S q) :
    (m * k * n : ℝ) ≤ (q + S) * Real.sqrt (2 * S) := by
  classical
  obtain ⟨h, P, ⟨⟨hcov, hdom, -⟩, hmin⟩, -, hSh⟩ := exists_isPartition hG hq
  have hpart : ∀ i, ((univ.filter fun x : Fin m × Fin k × Fin n => p x ∈ P i).card : ℝ) ≤
      S * Real.sqrt (2 * S) := by
    intro i
    obtain ⟨D, hD, hDom⟩ := hdom i
    have := card_prod_mem_le hG hL (s := 2 * S) (by omega) hD hDom
      (fun v hv hs => mem_filter.2 ⟨hv, hs⟩) (hmin i)
    push_cast at this
    linarith
  have hsum : Fintype.card (Fin m × Fin k × Fin n) =
      ∑ i, (univ.filter fun x : Fin m × Fin k × Fin n => p x ∈ P i).card :=
    card_eq_sum_of_existsUnique fun x => by simpa using hcov (p x)
  have hcard : (m * k * n : ℝ) =
      ∑ i, ((univ.filter fun x : Fin m × Fin k × Fin n => p x ∈ P i).card : ℝ) := by
    have := congrArg (fun z : ℕ => (z : ℝ)) hsum
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    push_cast at this
    rw [← this]
    ring
  have hSh' : (S : ℝ) * h ≤ q + S := by exact_mod_cast hSh
  calc (m * k * n : ℝ) = _ := hcard
    _ ≤ ∑ _i : Fin h, S * Real.sqrt (2 * S) := sum_le_sum fun i _ => hpart i
    _ = S * h * Real.sqrt (2 * S) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ (q + S) * Real.sqrt (2 * S) := mul_le_mul_of_nonneg_right hSh' (Real.sqrt_nonneg _)

end MiscMath.Computability.RedBluePebbleGame
