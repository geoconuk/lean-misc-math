/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Analysis.KolmogorovArnold.Approximant
import MiscMath.Analysis.KolmogorovArnold.RationalIndependence
import MiscMath.Analysis.KolmogorovArnold.Superposition
import Mathlib.Topology.TietzeExtension

/-!
# Density of the approximation sets

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 2 of the development, the crux of the Baire-category proof. Its
declarations are proof: machine-generated, kernel-checked and axiom-audited, and may be read by
no one.

For a continuous `f` on the cube with `‖f‖ ≤ 1`, the set `approxSet lam δ θ f` of tuples of inner
functions admitting a one-step approximation of `f` — an outer `g` with `‖g‖ ≤ δ` and
`‖f - ∑_q g ∘ y_q‖ < θ` — is **dense** in the space of tuples, for `δ = 1/(2n+3)` and any
`θ > (2n+2)/(2n+3)`. Together with its openness (Layer 1) this is Hedberg's Lemma 2 in general
dimension, and it is the only place where the geometry of the cube enters the proof.

The proof, following Hedberg (pp. 269–271) with Kahane's general-`n` interval system:

1. Given a tuple `ψ₀` and `ε > 0`, choose `N` so that `(2n+1)/N` is below a modulus of continuity
   of `f` at `δ` and of the `ψ₀_q` at `ε/4`, then `M` large in terms of `N`. The approximant
   tuple `ψ` (`Approximant.lean`) is within `ε` of `ψ₀` and is constant, with a rational level,
   on every cell of its rank.
2. On a red cube `a` — a product of cells of one rank — every inner sum `y_q` of `ψ` is constant,
   equal to the cell-map value `cellMap a`, and the cell map is injective by the rational
   independence of the `λ_p` (`Levels.lean`; the only use of Layer 0).
3. Define `g` on the finitely many cell-map values as `δ · sign(f on the cube)` and extend to a
   bounded continuous function on `ℝ` of the same norm by Tietze.
4. Each point `x` of the cube lies in red cubes of at least `n + 1` of the `2n + 1` ranks
   (`Cells.lean`), and on those the summand `g(y_q(x))` is `δ` when `f(x) > δ`, `-δ` when
   `f(x) < -δ`, because a red cube has diameter below the modulus of `f`; the remaining at most
   `n` summands are bounded by `δ`. This gives `|f(x) - ∑_q g(y_q(x))| ≤ max(1 - δ, (2n+2)δ) =
   (2n+2)/(2n+3) < θ`.

## What this module proves

Fix `n` and constants `λ : Fin n → ℝ` linearly independent over `ℚ`. For every continuous
`f : [0,1]ⁿ → ℝ` with `‖f‖ ≤ 1` and every `θ > (2n+2)/(2n+3)`, the set of `(2n+1)`-tuples of
monotone continuous functions `ψ_q : [0,1] → ℝ` for which some bounded continuous `g : ℝ → ℝ`
with `‖g‖ ≤ 1/(2n+3)` satisfies `sup_{x ∈ [0,1]ⁿ} |f(x) - ∑_{q} g(∑_p λ_p ψ_q(x_p))| < θ` is
dense in the space of all such tuples, with respect to uniform convergence in every component
(`dense_approxSet`).

## Source

- T. Hedberg, *The Kolmogorov superposition theorem*, Appendix II to H. S. Shapiro, *Topics in
  Approximation Theory*, Lecture Notes in Math. 187, Springer, 1971, Lemma 2, pp. 269–271: for
  `n = 2`, `‖f‖ = 1`, `δ = 1/7`, `θ = 7/8`, with red intervals of rank `i` obtained by deleting
  `[s/N, (s+1)/N]` for `s ≡ i - 1 (mod 5)`, approximants constant with rational values on them
  (properties a)–c)), `g = ±1/7` on the red rectangles where `f` has a sign, and the count "at
  least three of the numbers `g(t_i(x,y))` are equal to `1/7`". The general-`n` constants here,
  `δ = 1/(2n+3)` and `θ > (2n+2)/(2n+3)`, reduce to his at `n = 2` (`6/7 < 7/8`). His Lemma 1′
  (rational independence of the `λ_i`) is Layer 0.
- J.-P. Kahane, *Sur le théorème de superposition de Kolmogorov*, J. Approx. Theory 13 (1975)
  229–234, pp. 231–232: the interval system `I_q(j) = [qδ + (2n+1)jδ, qδ + (2n+1)jδ + 2nδ]` for
  general `n`, the observation that every point of `Iⁿ` lies in a cube `P_q` for at least
  `n + 1` values of `q`, and the constraint `ε < 1/(2(n+1))`. Kahane sets `h = 2ε · (mean of f)`
  on a cube and works in the increasing space `Φ` from the outset; here `g` takes the values
  `±δ, 0` as in Hedberg, and the space is `Inner` (monotone, unnormalised).

## Sanity checks

The theorem has hypotheses, so it needs a satisfiability witness: the `example`s below exhibit
`λ` from Layer 0 (`exists_pos_linearIndependent_rat`), a function with `‖f‖ ≤ 1` (the zero
function, and the first coordinate at `n = 1`), and a `θ` above the threshold, so that the
hypotheses hold simultaneously; they also check the threshold at `n = 2` is Hedberg's `6/7`. The
conclusion is a density statement, so it is non-vacuous as soon as the tuple space is non-empty,
which it is (`Inner.id`).

## Relation to Mathlib

Uses Tietze's theorem in the form
`BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding`, `Metric.dense_iff`,
uniform continuity on compact spaces
(`CompactSpace.uniformContinuous_of_continuous`), and `Fintype.linearIndependent_iff` through
`Levels.lean`. Nothing about superpositions is in Mathlib.
-/

open unitInterval Finset BoundedContinuousFunction Topology

namespace MiscMath.Analysis.KolmogorovArnold

noncomputable section

variable {n : ℕ}

/-- Indices of the red cubes with cell indices at most `N`: a rank and, for each coordinate, a
cell index. -/
abbrev CubeIndex (n N : ℕ) : Type := Fin (2 * n + 1) × (Fin n → Fin (N + 1))

/-- The red cube with index `a`: the points of the cube each of whose rescaled coordinates
`N x_p` lies in the cell of rank `a.1` and index `a.2 p`. -/
def redCube (N : ℕ) (a : CubeIndex n N) : Set (Fin n → I) :=
  {y | ∀ p, (N : ℝ) * y p ∈ cell a.1 (a.2 p)}

theorem mem_redCube {N : ℕ} {a : CubeIndex n N} {y : Fin n → I} :
    y ∈ redCube N a ↔ ∀ p, (N : ℝ) * y p ∈ cell a.1 (a.2 p) :=
  Iff.rfl

/-- The cell map: the value of the inner sum of rank `a.1` of the approximant tuple on the red
cube `a`, namely `∑_p λ_p · level(a.1, a.2 p)`. -/
def cellMap (lam : Fin n → ℝ) (φ : InnerTuple n) (N M : ℕ) (a : CubeIndex n N) : ℝ :=
  ∑ p, lam p * levels φ N M a.1 (a.2 p)

theorem cellMap_injective' {lam : Fin n → ℝ} (hlam : LinearIndependent ℚ lam) (φ : InnerTuple n)
    (N : ℕ) {M : ℕ} (hM : 0 < M) : Function.Injective (cellMap lam φ N M) := by
  intro a b h
  unfold cellMap levels at h
  have := cellMap_injective hlam φ N hM
    (a₁ := (a.1, fun p => (a.2 p : ℕ))) (a₂ := (b.1, fun p => (b.2 p : ℕ))) h
  rw [Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  exact Prod.ext h1 (funext fun p => Fin.ext (congrFun h2 p))

open Classical in
/-- The sign of `f` on the red cube `a`: `1` if `f > 0` throughout, `-1` if `f < 0` throughout,
and `0` otherwise. -/
def cubeSign (f : C(Fin n → I, ℝ)) (N : ℕ) (a : CubeIndex n N) : ℝ :=
  if ∀ y ∈ redCube N a, 0 < f y then 1 else if ∀ y ∈ redCube N a, f y < 0 then -1 else 0

theorem abs_cubeSign_le (f : C(Fin n → I, ℝ)) (N : ℕ) (a : CubeIndex n N) :
    |cubeSign f N a| ≤ 1 := by
  unfold cubeSign
  split_ifs <;> norm_num

theorem cubeSign_eq_one {f : C(Fin n → I, ℝ)} {N : ℕ} {a : CubeIndex n N}
    (h : ∀ y ∈ redCube N a, 0 < f y) : cubeSign f N a = 1 := by
  unfold cubeSign
  split_ifs
  rfl

theorem cubeSign_eq_neg_one {f : C(Fin n → I, ℝ)} {N : ℕ} {a : CubeIndex n N}
    (h : ∀ y ∈ redCube N a, f y < 0) (hne : (redCube N a).Nonempty) : cubeSign f N a = -1 := by
  unfold cubeSign
  have h1 : ¬ ∀ y ∈ redCube N a, 0 < f y := by
    intro h'
    obtain ⟨y, hy⟩ := hne
    exact absurd (h y hy) (not_lt.mpr (h' y hy).le)
  split_ifs
  rfl

/-- The arithmetic of Hedberg's estimate, abstracted: with `(2n+3) δ = 1`, `|a| ≤ 1`,
`|s| ≤ (2n+1) δ`, and `s` on the side of `δ` when `a` is beyond `δ`, one has
`|a - s| ≤ 1 - δ`. -/
theorem abs_sub_le_of_estimate {δ a s : ℝ} (hδ : (2 * n + 3) * δ = 1) (hδpos : 0 < δ)
    (ha : |a| ≤ 1) (hs : |s| ≤ (2 * n + 1) * δ) (hpos : δ < a → δ ≤ s) (hneg : a < -δ → s ≤ -δ) :
    |a - s| ≤ 1 - δ := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnδ : 0 ≤ (n : ℝ) * δ := mul_nonneg hn hδpos.le
  rw [abs_le] at ha hs ⊢
  rcases lt_or_ge δ a with h1 | h1
  · have := hpos h1
    constructor <;> nlinarith
  · rcases lt_or_ge a (-δ) with h2 | h2
    · have := hneg h2
      constructor <;> nlinarith
    · constructor <;> nlinarith

/-- A sum of terms each `≥ -δ`, with the terms indexed by `S` equal to `δ`, is at least
`(2 #S - #ι) δ`. -/
theorem sum_ge_of_forall_ge {ι : Type*} [Fintype ι] {v : ι → ℝ} {δ : ℝ}
    (hv : ∀ i, -δ ≤ v i) (S : Finset ι) (hS : ∀ i ∈ S, v i = δ) :
    (2 * S.card - Fintype.card ι : ℝ) * δ ≤ ∑ i, v i := by
  classical
  rw [← sum_add_sum_compl S]
  have h1 : ∑ i ∈ S, v i = S.card * δ := by
    rw [sum_congr rfl hS, sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ Sᶜ, -δ ≤ ∑ i ∈ Sᶜ, v i := sum_le_sum fun i _ => hv i
  rw [sum_const, nsmul_eq_mul] at h2
  have h3 : (Sᶜ.card : ℝ) = Fintype.card ι - S.card := by
    rw [card_compl, Nat.cast_sub (card_le_univ S)]
  rw [h3] at h2
  rw [h1]
  linarith

/-- The mirror image: terms each `≤ δ`, those indexed by `S` equal to `-δ`. -/
theorem sum_le_of_forall_le {ι : Type*} [Fintype ι] {v : ι → ℝ} {δ : ℝ}
    (hv : ∀ i, v i ≤ δ) (S : Finset ι) (hS : ∀ i ∈ S, v i = -δ) :
    ∑ i, v i ≤ -((2 * S.card - Fintype.card ι : ℝ) * δ) := by
  have := sum_ge_of_forall_ge (v := fun i => -v i) (δ := δ) (fun i => by simp [hv i]) S
    fun i hi => by simp [hS i hi]
  rw [sum_neg_distrib] at this
  linarith

/-- **The approximation sets are dense** (Hedberg, Lemma 2; Kahane, pp. 231–232). For `λ`
linearly independent over `ℚ`, `‖f‖ ≤ 1` and `θ > (2n+2)/(2n+3)`, the tuples admitting a
one-step approximation of `f` with `‖g‖ ≤ 1/(2n+3)` and error below `θ` are dense in
`InnerTuple n`. -/
theorem dense_approxSet {lam : Fin n → ℝ} (hlam : LinearIndependent ℚ lam) {f : C(Fin n → I, ℝ)}
    (hf : ‖f‖ ≤ 1) {θ : ℝ} (hθ : (2 * n + 2) / (2 * n + 3) < θ) :
    Dense (approxSet lam (1 / (2 * n + 3)) θ f) := by
  classical
  rw [Metric.dense_iff]
  intro ψ₀ ε hε
  set δ : ℝ := 1 / (2 * n + 3) with hδdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hδpos : 0 < δ := by positivity
  have hδ : (2 * n + 3) * δ = 1 := by
    rw [hδdef]
    field_simp
  have hθpos : 0 < θ := lt_of_le_of_lt (by positivity) hθ
  have hθ' : 1 - δ < θ := by
    have h1δ : 1 - δ = (2 * n + 2) / (2 * n + 3) := by
      rw [hδdef]
      field_simp
      ring
    rw [h1δ]
    exact hθ
  -- Uniform continuity of `f` at `δ`.
  obtain ⟨ηf, hηf, hfuc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) δ hδpos
  -- Uniform continuity of the inner functions, jointly, at `ε / 4`.
  have hΦ : Continuous fun t : I => fun q : Fin (2 * n + 1) => (ψ₀ q : C(I, ℝ)) t :=
    continuous_pi fun q => (ψ₀ q : C(I, ℝ)).continuous
  obtain ⟨η, hη, hΦuc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hΦ) (ε / 4) (by positivity)
  have hη' : ∀ q (s t : I), |(s : ℝ) - t| < η →
      |(ψ₀ q : C(I, ℝ)) s - (ψ₀ q : C(I, ℝ)) t| < ε / 4 := by
    intro q s t hst
    have h := hΦuc (a := s) (b := t) (by rwa [Subtype.dist_eq, Real.dist_eq])
    rw [dist_pi_lt_iff (by positivity)] at h
    have h := h q
    rwa [Real.dist_eq] at h
  -- Choose `N` with `(2n+1) / N < min ηf η`, then `M` with `(2n+1) (N + 2) / M ≤ ε / 4`.
  have hmR : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hmin : 0 < min ηf η := lt_min hηf hη
  obtain ⟨N, hN⟩ := exists_nat_gt (((2 * n + 1 : ℕ) : ℝ) / min ηf η)
  have hNR : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNpos : 0 < N := by exact_mod_cast hNR
  have hmN : ((2 * n + 1 : ℕ) : ℝ) / N < min ηf η := by
    have := (div_lt_iff₀ hmin).mp hN
    rw [div_lt_iff₀ hNR]
    linarith
  have hNηf : ((2 * n + 1 : ℕ) : ℝ) / N < ηf := lt_of_lt_of_le hmN (min_le_left _ _)
  have hNη : ((2 * n + 1 : ℕ) : ℝ) / N < η := lt_of_lt_of_le hmN (min_le_right _ _)
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * ((2 * n + 1 : ℕ) : ℝ) * (N + 2) / ε)
  have hMR : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hMpos : 0 < M := by exact_mod_cast hMR
  have hMε : ((2 * n + 1 : ℕ) : ℝ) * (N + 2) / M ≤ ε / 4 := by
    rw [div_le_iff₀ hMR]
    have := (div_lt_iff₀ hε).mp hM
    linarith
  -- The approximant tuple.
  set ψ : InnerTuple n := fun q => approximant ψ₀ N hMpos q with hψ
  refine ⟨ψ, ?_, ?_⟩
  · rw [Metric.mem_ball]
    exact dist_approximant_lt ψ₀ hNpos hMpos hε hη' hNη hMε
  -- The outer function: `± δ` on the cell-map values, extended by Tietze.
  have hinj : Function.Injective (cellMap lam ψ₀ N M) := cellMap_injective' hlam ψ₀ N hMpos
  have hemb : IsClosedEmbedding (cellMap lam ψ₀ N M) :=
    continuous_of_discreteTopology.isClosedEmbedding hinj
  set f₀ : CubeIndex n N →ᵇ ℝ :=
    mkOfCompact ⟨fun a => δ * cubeSign f N a, continuous_of_discreteTopology⟩ with hf₀
  have hf₀norm : ‖f₀‖ ≤ δ := by
    rw [norm_le hδpos.le]
    intro a
    rw [hf₀, mkOfCompact_apply, ContinuousMap.coe_mk, Real.norm_eq_abs, abs_mul,
      abs_of_pos hδpos]
    exact mul_le_of_le_one_right hδpos.le (abs_cubeSign_le f N a)
  obtain ⟨g, hgnorm, hgext⟩ := exists_extension_norm_eq_of_isClosedEmbedding f₀ hemb
  have hgδ : ‖g‖ ≤ δ := by rw [hgnorm]; exact hf₀norm
  refine ⟨g, hgδ, ?_⟩
  have hg : ∀ a, g (cellMap lam ψ₀ N M a) = δ * cubeSign f N a := fun a => by
    have := congrFun hgext a
    simpa [hf₀] using this
  have hgbound : ∀ t, |g t| ≤ δ := fun t => by
    have := g.norm_coe_le_norm t
    rw [Real.norm_eq_abs] at this
    exact this.trans hgδ
  -- The estimate, pointwise on the cube.
  rw [ContinuousMap.norm_lt_iff _ hθpos]
  intro x
  rw [ContinuousMap.sub_apply, superpose_apply, Real.norm_eq_abs]
  refine lt_of_le_of_lt ?_ hθ'
  set u : Fin n → ℝ := fun p => (N : ℝ) * x p with hu
  have hu0 : ∀ p, 0 ≤ u p := fun p => mul_nonneg hNR.le (x p).2.1
  have huN : ∀ p, u p ≤ N := fun p => mul_le_of_le_one_right hNR.le (x p).2.2
  obtain ⟨S, hSred, hScard⟩ := exists_red_finset (m := 2 * n + 1) hu0
  -- On a red rank the summand is `δ · sign` for the red cube through `x`.
  have hred : ∀ q ∈ S, ∃ a : CubeIndex n N, x ∈ redCube N a ∧
      g (innerSum lam ψ q x) = δ * cubeSign f N a := by
    intro q hq
    obtain ⟨jv, hjv⟩ := hSred q hq
    have hjN : ∀ p, jv p < N + 1 := fun p =>
      Nat.lt_succ_of_le (le_of_cellLeft_le (hjv p).1 (huN p))
    refine ⟨(q, fun p => ⟨jv p, hjN p⟩), hjv, ?_⟩
    rw [← hg]
    congr 1
    rw [innerSum_apply]
    unfold cellMap
    refine sum_congr rfl fun p _ => ?_
    congr 1
    exact approximant_apply_of_mem_cell ψ₀ N hMpos q
      (Nat.le_succ_of_le (Nat.le_of_lt_succ (hjN p))) (hjv p)
  -- Points of a red cube through `x` are within `ηf` of `x`, so `f` moves by less than `δ`.
  have hcube : ∀ a : CubeIndex n N, x ∈ redCube N a → ∀ y ∈ redCube N a, |f x - f y| < δ := by
    intro a hx y hy
    have hdist : dist x y < ηf := by
      rw [dist_pi_lt_iff hηf]
      intro p
      rw [Subtype.dist_eq, Real.dist_eq]
      have h := abs_sub_le_of_mem_cell (hx p) (hy p)
      have hscale : |(x p : ℝ) - y p| = |(N : ℝ) * x p - N * y p| / N := by
        rw [← mul_sub, abs_mul, abs_of_pos hNR, mul_div_cancel_left₀ _ hNR.ne']
      rw [hscale]
      calc |(N : ℝ) * x p - N * y p| / N ≤ (((2 * n + 1 : ℕ) : ℝ) - 1) / N :=
            div_le_div_of_nonneg_right h hNR.le
        _ < ((2 * n + 1 : ℕ) : ℝ) / N := by
          apply div_lt_div_of_pos_right _ hNR
          linarith
        _ < ηf := hNηf
    have := hfuc hdist
    rwa [Real.dist_eq] at this
  have hfx : |f x| ≤ 1 := by
    have := f.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at this
    exact this.trans hf
  -- The summands.
  set v : Fin (2 * n + 1) → ℝ := fun q => g (innerSum lam ψ q x) with hv
  have hvbound : ∀ q, |v q| ≤ δ := fun q => hgbound _
  have hsabs : |∑ q, v q| ≤ (2 * n + 1) * δ := by
    calc |∑ q, v q| ≤ ∑ q, |v q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q : Fin (2 * n + 1), δ := sum_le_sum fun q _ => hvbound q
      _ = (2 * n + 1) * δ := by simp
  have hk : (n : ℝ) + 1 ≤ S.card := by exact_mod_cast (by omega : n + 1 ≤ S.card)
  have hpos : δ < f x → δ ≤ ∑ q, v q := by
    intro hfxδ
    have hS : ∀ q ∈ S, v q = δ := by
      intro q hq
      obtain ⟨a, hxa, hva⟩ := hred q hq
      change g (innerSum lam ψ q x) = δ
      rw [hva, cubeSign_eq_one, mul_one]
      intro y hy
      have := hcube a hxa y hy
      rw [abs_lt] at this
      linarith
    have := sum_ge_of_forall_ge (fun q => (abs_le.mp (hvbound q)).1) S hS
    rw [Fintype.card_fin] at this
    have h2 := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * S.card - ((2 * n + 1 : ℕ) : ℝ) by push_cast; linarith) hδpos.le
    linarith
  have hneg : f x < -δ → ∑ q, v q ≤ -δ := by
    intro hfxδ
    have hS : ∀ q ∈ S, v q = -δ := by
      intro q hq
      obtain ⟨a, hxa, hva⟩ := hred q hq
      change g (innerSum lam ψ q x) = -δ
      rw [hva, cubeSign_eq_neg_one _ ⟨x, hxa⟩, mul_neg_one]
      intro y hy
      have := hcube a hxa y hy
      rw [abs_lt] at this
      linarith
    have := sum_le_of_forall_le (fun q => (abs_le.mp (hvbound q)).2) S hS
    rw [Fintype.card_fin] at this
    have h2 := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * S.card - ((2 * n + 1 : ℕ) : ℝ) by push_cast; linarith) hδpos.le
    linarith
  exact abs_sub_le_of_estimate hδ hδpos hfx hsabs hpos hneg

/-! ## Sanity checks -/

/-- The hypotheses are simultaneously satisfiable: Layer 0 supplies the `λ`, the zero function
has norm at most `1`, and `θ = 1` is above the threshold `(2n+2)/(2n+3)`. -/
example (n : ℕ) : ∃ (lam : Fin n → ℝ) (f : C(Fin n → I, ℝ)) (θ : ℝ),
    LinearIndependent ℚ lam ∧ ‖f‖ ≤ 1 ∧ (2 * n + 2) / (2 * n + 3) < θ := by
  obtain ⟨lam, -, hlam⟩ := exists_pos_linearIndependent_rat n
  refine ⟨lam, 0, 1, hlam, by simp, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- A non-zero function with the hypothesis: the first coordinate at `n = 1`, which has
sup norm `1` on the cube. -/
example : ‖(⟨fun x : Fin 1 → I => (x 0 : ℝ), by fun_prop⟩ : C(Fin 1 → I, ℝ))‖ ≤ 1 := by
  rw [ContinuousMap.norm_le _ zero_le_one]
  intro x
  rw [ContinuousMap.coe_mk, Real.norm_eq_abs, abs_of_nonneg (x 0).2.1]
  exact (x 0).2.2

/-- At `n = 2` the threshold is Hedberg's `6/7`, and his `θ = 7/8` clears it. -/
example : ((2 * 2 + 2 : ℝ) / (2 * 2 + 3)) = 6 / 7 ∧ (6 : ℝ) / 7 < 7 / 8 := by norm_num

end

end MiscMath.Analysis.KolmogorovArnold
