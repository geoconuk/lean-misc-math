/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Wyner's spherical covering exponent

## Informal statement

Fix an angle `θ` with `0 < θ < π/2`, and for each `n` let `M(n, θ)` be the least number of
spherical caps of angular radius `θ`, centred at points of the unit sphere of `ℝⁿ`, whose
union is the whole sphere. Then

    lim_{n → ∞} (1/n) · log M(n, θ) = -log sin θ,

that is, `M(n, θ) = exp (n · (-log sin θ) · (1 + o(1)))`. The covering number grows
exponentially in the dimension, with exponent exactly `-log sin θ`.

The cap of angular radius `θ` about a point `c` of the unit sphere is the set of unit
vectors `u` with `angle u c ≤ θ`. For unit vectors `‖u - c‖ = 2 sin (angle u c / 2)`, so
that cap is precisely the closed ball of radius `2 sin (θ/2)` about `c`. The statement
below therefore uses Mathlib's `Metric.coveringNumber` at radius `2 sin (θ/2)` on
`Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin n)`, and defines no covering number of its
own. `Metric.coveringNumber` requires the centres to lie in the set being covered, which
is also what Wyner requires.

Two points of care in reading the Lean statement:

* `Metric.coveringNumber` takes values in `ℕ∞`, and the statement applies `ENat.toNat`,
  whose junk value at `⊤` is `0`. `coveringNumber_sphere_ne_top` and
  `coveringNumber_sphere_pos` bound that: the covering number is finite for every `n`, and
  positive for every `n ≥ 1`, so from `n = 1` onwards neither `ENat.toNat` nor `Real.log`
  is applied to a junk argument. `n = 0` is the exception and is genuinely degenerate: the
  sphere of `ℝ⁰` is empty, so the covering number is `0` at every radius and the summand
  collapses to `Real.log 0 / (0 : ℝ) = 0`, two junk conventions at once. A limit along
  `atTop` does not see it, but it is not excluded either.
* The radius is written `Real.toNNReal (2 * sin (θ/2))`. For `0 < θ < π/2` this is the
  honest value `2 sin (θ/2)` and not a truncation to `0`; the sanity checks pin it down at
  `θ = π/3`, where it is exactly `1`.

**Where this differs from the source.** Wyner defines a `θ`-covering with *open* caps,
`angle u c < θ` (p. 2112). Mathlib's `Metric.IsCover` is stated with closed balls, so what
is proved below concerns *closed* caps, `angle u c ≤ θ`. The exponent is unaffected — a
closed `θ`-cover is an open `θ'`-cover for every `θ' > θ`, and `-log sin` is continuous —
but the two covering numbers are not literally equal, and it is the closed one that is
formalised here.

## Source

A. D. Wyner, *Random packings and coverings of the unit n-sphere*, Bell System Technical
Journal **46** (1967), 2111-2118.

The result formalised here is the covering half of that paper: equations (2a) and (2b),
restated as a limit on p. 2116, `lim (1/n) log M_c(n, θ) = R_c(θ)` with
`R_c(θ) = -log sin θ` for `θ < π/2`. Both halves of Wyner's argument are reproduced — the
elementary volume bound (Lemma 2, p. 2115) for the lower bound on the covering number, and
the random-covering argument (Theorem 2 and its corollary, pp. 2115-2117) for the upper
bound. The packing results of the same paper are not formalised.

## Relation to Mathlib

Mathlib supplies the vocabulary but not the theorem. `Mathlib/Topology/MetricSpace/`
`CoveringNumbers.lean` defines `Metric.coveringNumber`, `Metric.externalCoveringNumber` and
`Metric.packingNumber` along with the elementary inequalities relating them, but contains no
asymptotics. Mathlib has no spherical cap measure and no metric-entropy estimate for any
family of sets, so nothing here is a duplicate.

The theorem below is stated entirely in Mathlib's vocabulary and introduces no definition at
the level of the statement. The auxiliary notions needed for the proof — the normalised
surface measure of a cap, and the radial cone over a cap — are `private` to this file and do
not appear in any exported statement. `MeasureTheory.Measure.toSphere` and
`EuclideanSpace.volume_ball` provide the measure-theoretic input, and
`Metric.packingNumber` together with `Metric.maximalSeparatedSet` provide the finite nets
used by the random-covering argument.

## Provenance

Result selected and specified by George A. Constantinides, who has read the Lean statement
below against the informal claim above on a best-effort basis. The statement and its
proof were generated by Claude; the proof is read by nobody. Both are kernel-verified
and axiom-audited. A best-effort read is not a review — satisfy yourself that the
statement says what you need before relying on it. See the repository README.

An earlier formalisation of this result, by George A. Constantinides and Codex as part of a
paper coauthored with Bardia Zadeh, is at
<https://github.com/bardia01/Direction-Preserving-Number-Representations/blob/main/PaperProofs/PaperProofs/Wyner.lean>.
This file is a refactoring of that development: restructured into a single self-contained
module, restated in terms of `Metric.coveringNumber` rather than a bespoke covering number,
and reproved against a current Mathlib.
-/

noncomputable section

open Set Filter Topology Real Metric MeasureTheory InnerProductGeometry
open RealInnerProductSpace
open scoped ENNReal NNReal Pointwise

namespace MiscMath.Geometry

/-! ### Chords and angles -/

section Chords

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The chord joining two unit vectors has length `2 sin (θ/2)`, where `θ` is the angle
between them. -/
theorem dist_eq_two_mul_sin_angle_div_two {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    dist x y = 2 * Real.sin (angle x y / 2) := by
  have hcos : Real.cos (angle x y) = ⟪x, y⟫ := by
    rw [InnerProductGeometry.cos_angle, hx, hy]; ring
  have key : ∀ u : ℝ, Real.cos (2 * u) = 1 - 2 * Real.sin u ^ 2 := by
    intro u
    rw [Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hhalf : Real.cos (angle x y) = 1 - 2 * Real.sin (angle x y / 2) ^ 2 := by
    have h := key (angle x y / 2)
    rwa [show 2 * (angle x y / 2) = angle x y by ring] at h
  have hsin_nonneg : 0 ≤ Real.sin (angle x y / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [InnerProductGeometry.angle_nonneg x y]
    · linarith [InnerProductGeometry.angle_le_pi x y, Real.pi_pos]
  have hsq : dist x y ^ 2 = (2 * Real.sin (angle x y / 2)) ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hx, hy, ← hcos, hhalf]
    ring
  nlinarith [hsq, dist_nonneg (x := x) (y := y), hsin_nonneg]

/-- For unit vectors, an angular cap of half-angle `θ ∈ [0, π]` is exactly a chordal
closed ball of radius `2 sin (θ/2)`. -/
theorem angle_le_iff_dist_le {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    angle x y ≤ θ ↔ dist x y ≤ 2 * Real.sin (θ / 2) := by
  rw [dist_eq_two_mul_sin_angle_div_two hx hy]
  constructor
  · intro h
    have : Real.sin (angle x y / 2) ≤ Real.sin (θ / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [InnerProductGeometry.angle_nonneg x y, Real.pi_pos])
        (by linarith) (by linarith)
    linarith
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have : Real.sin (θ / 2) < Real.sin (angle x y / 2) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos])
        (by linarith [InnerProductGeometry.angle_le_pi x y])
        (by linarith)
    linarith

end Chords

/-! ### Volumes of Euclidean unit balls -/

/-- The volume of the unit ball in `ℝ^n`, as a real number. -/
private def ballVol (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

private theorem ballVol_pos (n : ℕ) : 0 < ballVol n := by
  have h1 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    (measure_ball_pos _ _ one_pos).ne'
  have h2 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  exact ENNReal.toReal_pos h1 h2

private theorem ballVol_eq (n : ℕ) (hn : 0 < n) :
    ballVol n = Real.sqrt π ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hg : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := by
    apply Real.Gamma_pos_of_pos; positivity
  rw [ballVol, EuclideanSpace.volume_ball, Fintype.card_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]

private theorem ballVol_rec (n : ℕ) (hn : 0 < n) :
    ballVol (n + 2) = ballVol n * (2 * π / ((n : ℝ) + 2)) := by
  have hg : Real.Gamma ((n : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hne : ((n : ℝ) / 2 + 1) ≠ 0 := by positivity
  have hgamma :
      Real.Gamma (((n : ℝ) + 2) / 2 + 1)
        = ((n : ℝ) / 2 + 1) * Real.Gamma ((n : ℝ) / 2 + 1) := by
    rw [show ((n : ℝ) + 2) / 2 + 1 = ((n : ℝ) / 2 + 1) + 1 by ring,
      Real.Gamma_add_one hne]
  have hsq : Real.sqrt π ^ (n + 2) = Real.sqrt π ^ n * π := by
    rw [pow_add, Real.sq_sqrt Real.pi_nonneg]
  rw [ballVol_eq n hn, ballVol_eq (n + 2) (by omega)]
  push_cast
  rw [hgamma, hsq]
  field_simp

private theorem gamma_three_halves : Real.Gamma ((3 : ℝ) / 2) = Real.sqrt π / 2 := by
  rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

private theorem gamma_two : Real.Gamma (2 : ℝ) = 1 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one]
  ring

private theorem ballVol_one : ballVol 1 = 2 := by
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [ballVol_eq 1 one_pos]
  norm_num
  rw [gamma_three_halves]
  field_simp

private theorem ballVol_two : ballVol 2 = π := by
  rw [ballVol_eq 2 (by norm_num)]
  norm_num [gamma_two, Real.sq_sqrt Real.pi_nonneg]

private theorem ballVol_three : ballVol 3 = 4 * π / 3 := by
  have h := ballVol_rec 1 one_pos
  rw [ballVol_one] at h
  norm_num at h
  rw [h]
  ring

/-- Consecutive unit-ball volumes: `V_{n-1} / V_n` grows like `√(n/2π)`. These crude
bounds are all the asymptotic argument needs, since `(log n)/n → 0`. -/
private theorem ballVol_ratio_bounds (k : ℕ) :
    1 / 2 ≤ ballVol (k + 1) / ballVol (k + 2) ∧
      ballVol (k + 1) / ballVol (k + 2) ≤ (k : ℝ) + 2 := by
  induction k using Nat.twoStepInduction with
  | zero =>
      rw [ballVol_one, ballVol_two]
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ Real.pi_pos]; nlinarith [Real.pi_lt_four]
      · rw [div_le_iff₀ Real.pi_pos]; push_cast; nlinarith [Real.pi_gt_three]
  | one =>
      rw [ballVol_two, ballVol_three]
      have h3 : (0 : ℝ) < 4 * π / 3 := by positivity
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ h3]; nlinarith [Real.pi_gt_three]
      · rw [div_le_iff₀ h3]; push_cast; nlinarith [Real.pi_gt_three]
  | more k ih _ =>
      have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have hk4 : (0 : ℝ) < (k : ℝ) + 4 := by positivity
      have hpos1 := ballVol_pos (k + 1)
      have hpos2 := ballVol_pos (k + 2)
      have e1 : ballVol (k + 1 + 2) = ballVol (k + 1) * (2 * π / ((k : ℝ) + 3)) := by
        have h := ballVol_rec (k + 1) (by omega)
        push_cast at h
        rw [h]; ring_nf
      have e2 : ballVol (k + 2 + 2) = ballVol (k + 2) * (2 * π / ((k : ℝ) + 4)) := by
        have h := ballVol_rec (k + 2) (by omega)
        push_cast at h
        rw [h]; ring_nf
      have hkey : ballVol (k + 2 + 1) / ballVol (k + 2 + 2) =
          (ballVol (k + 1) / ballVol (k + 2)) * (((k : ℝ) + 4) / ((k : ℝ) + 3)) := by
        change ballVol (k + 1 + 2) / ballVol (k + 2 + 2) = _
        rw [e1, e2]
        field_simp
      rw [hkey]
      have hratio1 : (1 : ℝ) ≤ ((k : ℝ) + 4) / ((k : ℝ) + 3) := by
        rw [le_div_iff₀ hk3]; linarith
      have hq_nonneg : 0 ≤ ballVol (k + 1) / ballVol (k + 2) := by positivity
      refine ⟨?_, ?_⟩
      · nlinarith [ih.1, hratio1]
      · rw [mul_div_assoc', div_le_iff₀ hk3]
        push_cast
        nlinarith [ih.2, hq_nonneg]


/-! ### Spherical caps and their normalised surface measure -/

/-- A point on the unit sphere in `ℝ^n`. -/
private abbrev SpherePoint (n : ℕ) :=
  {u : EuclideanSpace ℝ (Fin n) // u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1}


/-- Surface measure on the unit sphere in `ℝ^n`, realized via `Measure.toSphere`. -/
private def sphereSurfaceMeasure (n : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

/-- Surface area of the unit sphere `S^m`, viewed as a real number. -/
private def sphereArea (m : ℕ) : ℝ :=
  (sphereSurfaceMeasure (m + 1)).real Set.univ

/-- The first standard basis vector in `ℝ^n`, totalized by returning `0` when `n = 0`. -/
private def e1Vec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  if hn : 0 < n then EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) else 0

/-- The spherical cap cut out by the angle bound `a` around `e₁`. -/
private def capSet (n : ℕ) (a : ℝ) : Set (SpherePoint n) :=
  {x | InnerProductGeometry.angle x.1 (e1Vec n) ≤ a}

/-- The normalized spherical cap measure. For `n = 0` we set it to `0`. -/
private def capMeasure (n : ℕ) (a : ℝ) : ℝ :=
  if 0 < n then
    (sphereSurfaceMeasure n).real (capSet n a) / sphereArea (n - 1)
  else
    0

@[simp]
private theorem sphereArea_def (m : ℕ) :
    sphereArea m = (sphereSurfaceMeasure (m + 1)).real Set.univ := rfl


@[simp]
private theorem e1Vec_eq_single {n : ℕ} (hn : 0 < n) :
    e1Vec n = EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) := by
  simp [e1Vec, hn]

@[simp]
private theorem norm_e1Vec {n : ℕ} (hn : 0 < n) : ‖e1Vec n‖ = 1 := by
  simp [e1Vec, hn]

private theorem inner_e1Vec {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (e1Vec n) = x ⟨0, hn⟩ := by
  simpa [e1Vec, hn] using
    (EuclideanSpace.inner_single_right (i := ⟨0, hn⟩) (a := (1 : ℝ)) (v := x))

private theorem sphereArea_eq_finrank_mul_volume_ball (m : ℕ) :
    sphereArea m =
      (m + 1) * (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real (Metric.ball 0 1) := by
  rw [sphereArea, sphereSurfaceMeasure, Measure.toSphere_real_apply_univ]
  simp

private theorem sphereArea_pos (m : ℕ) : 0 < sphereArea m := by
  have hne : sphereSurfaceMeasure (m + 1) ≠ 0 := by
    change ((volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).toSphere) ≠ 0
    exact Measure.toSphere_ne_zero
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))))
  let : NeZero (sphereSurfaceMeasure (m + 1)) := ⟨hne⟩
  let : IsFiniteMeasure (sphereSurfaceMeasure (m + 1)) := by
    dsimp [sphereSurfaceMeasure]
    infer_instance
  rw [sphereArea]
  exact measureReal_univ_pos (μ := sphereSurfaceMeasure (m + 1))


private theorem capMeasure_eq_div_surfaceMeasure {n : ℕ} (hn : 0 < n) (a : ℝ) :
    capMeasure n a = (sphereSurfaceMeasure n).real (capSet n a) / sphereArea (n - 1) := by
  simp [capMeasure, hn]

private theorem mem_capSet_iff_cos_le_coord0 {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) (x : SpherePoint n) :
    x ∈ capSet n a ↔ Real.cos a ≤ (x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩ := by
  have hapi' : a ≤ Real.pi := by linarith [hapi]
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hx' := x.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx'
  have he1norm : ‖e1Vec n‖ = 1 := norm_e1Vec hn
  constructor
  · intro hx
    have hcos :
        Real.cos a
          ≤ Real.cos (InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (InnerProductGeometry.angle_nonneg _ _) hapi' hx
    calc
      Real.cos a
          ≤ Real.cos (InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n)) := hcos
      _ = (x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩ := by
        rw [InnerProductGeometry.cos_angle, hxnorm, he1norm, inner_e1Vec hn]
        norm_num
  · intro hx
    have h_arccos :
        Real.arccos ((x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩) ≤ Real.arccos (Real.cos a) :=
      Real.arccos_le_arccos hx
    have hacos : Real.arccos (Real.cos a) = a :=
      Real.arccos_cos ha0 hapi'
    have hangle :
        InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n) =
          Real.arccos ((x : EuclideanSpace ℝ (Fin n)) ⟨0, hn⟩) := by
      simp [InnerProductGeometry.angle, hxnorm, he1norm, inner_e1Vec hn]
    change InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin n)) (e1Vec n) ≤ a
    rw [hangle]
    exact le_trans h_arccos hacos.le

private theorem measurableSet_capSet {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    MeasurableSet (capSet n a) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hcap :
      capSet n a = {x : SpherePoint n | Real.cos a ≤ (x : EuclideanSpace ℝ (Fin n)) i0} := by
    ext x
    simpa [i0] using mem_capSet_iff_cos_le_coord0 hn ha0 hapi x
  rw [hcap]
  have hcont :
      Continuous fun x : SpherePoint n => (x : EuclideanSpace ℝ (Fin n)) i0 := by
    fun_prop
  exact (isClosed_le continuous_const hcont).measurableSet


/-- Split `ℝ^(n+1)` into its first coordinate and the remaining `n` coordinates. -/
private def splitFirstCoord (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ℝ × EuclideanSpace ℝ (Fin n) :=
  (x 0, show EuclideanSpace ℝ (Fin n) from WithLp.toLp 2 (fun i : Fin n => x i.succ))

/-- Reassemble a vector in `ℝ^(n+1)` from its first coordinate and tail. -/
private def joinFirstCoord (n : ℕ) (u : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  show EuclideanSpace ℝ (Fin (n + 1)) from
    WithLp.toLp 2 (Fin.cons u.1 fun i : Fin n => u.2 i)





@[simp]
private theorem joinFirstCoord_splitFirstCoord (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    joinFirstCoord n (splitFirstCoord n x) = x := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [joinFirstCoord, splitFirstCoord]
  · intro j
    simp [joinFirstCoord, splitFirstCoord]

@[simp]
private theorem splitFirstCoord_joinFirstCoord (n : ℕ) (u : ℝ × EuclideanSpace ℝ (Fin n)) :
    splitFirstCoord n (joinFirstCoord n u) = u := by
  refine Prod.ext ?_ ?_
  · simp [splitFirstCoord, joinFirstCoord]
  · ext i
    simp [splitFirstCoord, joinFirstCoord]

/-- The coordinate splitting equivalence `ℝ^(n+1) ≃ ℝ × ℝ^n`. -/
private def splitFirstCoordEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ ℝ × EuclideanSpace ℝ (Fin n) where
  toFun := splitFirstCoord n
  invFun := joinFirstCoord n
  left_inv := joinFirstCoord_splitFirstCoord n
  right_inv := splitFirstCoord_joinFirstCoord n



/-- The first-coordinate splitting map as a measurable equivalence. -/
private def splitFirstCoordMeasurableEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin n) :=
  ((MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))))

@[simp]
private theorem splitFirstCoordMeasurableEquiv_apply (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    splitFirstCoordMeasurableEquiv n x = splitFirstCoord n x := by
  change (x.ofLp 0, WithLp.toLp 2 (Fin.tail x.ofLp)) = splitFirstCoord n x
  refine Prod.ext ?_ ?_
  · rfl
  · ext i
    simp [splitFirstCoord, Fin.tail]

private theorem measurePreserving_splitFirstCoord (n : ℕ) :
    MeasurePreserving (splitFirstCoord n)
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) := by
  have h₁ : MeasurePreserving
      (⇑((MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm))
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
      (volume : Measure (Fin (n + 1) → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin (n + 1))
  have h₂ : MeasurePreserving
      (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0))
      (volume : Measure (Fin (n + 1) → ℝ))
      (volume : Measure (ℝ × (Fin n → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have h₃ : MeasurePreserving
      (⇑((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))))
      (volume : Measure (ℝ × (Fin n → ℝ)))
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) :=
    (MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
      (PiLp.volume_preserving_toLp (Fin n))
  have hcomp : MeasurePreserving (⇑(splitFirstCoordMeasurableEquiv n))
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) := h₁.trans (h₂.trans h₃)
  exact (funext (splitFirstCoordMeasurableEquiv_apply n)) ▸ hcomp

private theorem norm_sq_eq_splitFirstCoord (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = (splitFirstCoord n x).1 ^ 2 + ‖(splitFirstCoord n x).2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [EuclideanSpace.norm_sq_eq, splitFirstCoord]

private theorem mem_capSet_iff_cos_le_splitFirstCoord_zero (n : ℕ)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) (x : SpherePoint (n + 1)) :
    x ∈ capSet (n + 1) a ↔
      Real.cos a ≤ (splitFirstCoord n (x : EuclideanSpace ℝ (Fin (n + 1)))).1 := by
  simpa [splitFirstCoord] using
    (mem_capSet_iff_cos_le_coord0 (hn := Nat.succ_pos _) ha0 hapi x)

/-- The open radial cone over a spherical cap. -/
private def capCone (n : ℕ) (a : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Set.Ioo (0 : ℝ) 1 • ((↑) '' capSet n a)

private theorem mem_capCone_succ_iff (n : ℕ)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    x ∈ capCone (n + 1) a ↔
      0 < ‖x‖ ∧
      ‖x‖ < 1 ∧
      Real.cos a * ‖x‖ ≤ (splitFirstCoord n x).1 := by
  constructor
  · rintro ⟨r, hr, z, hz, rfl⟩
    rcases hz with ⟨u, hu, rfl⟩
    have hucoord :
        Real.cos a ≤
          (splitFirstCoord n
            (((u : SpherePoint (n + 1)) : EuclideanSpace ℝ (Fin (n + 1))))).1 := by
      exact (mem_capSet_iff_cos_le_splitFirstCoord_zero n ha0 hapi u).1 hu
    have hunorm :
        ‖(((u : SpherePoint (n + 1)) : EuclideanSpace ℝ (Fin (n + 1))))‖ = 1 := by
      have hu' := u.2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu'
    constructor
    · simpa [norm_smul, hunorm, abs_of_pos hr.1] using hr.1
    constructor
    · simpa [norm_smul, hunorm, abs_of_pos hr.1] using hr.2
    · simpa [splitFirstCoord, norm_smul, hunorm, abs_of_pos hr.1,
        mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hucoord hr.1.le
  · rintro ⟨hxnorm_pos, hxnorm_lt, hcoord⟩
    have hxnorm_ne : ‖x‖ ≠ 0 := hxnorm_pos.ne'
    let u : SpherePoint (n + 1) :=
      ⟨‖x‖⁻¹ • x, by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hxnorm_pos), inv_mul_cancel₀ hxnorm_ne]⟩
    have hu_mem : u ∈ capSet (n + 1) a := by
      refine (mem_capSet_iff_cos_le_splitFirstCoord_zero n ha0 hapi u).2 ?_
      have hdiv : Real.cos a ≤ (splitFirstCoord n x).1 / ‖x‖ :=
        (le_div_iff₀ hxnorm_pos).2 hcoord
      simpa [u, splitFirstCoord, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    refine ⟨‖x‖, ⟨hxnorm_pos, hxnorm_lt⟩,
      (((u : SpherePoint (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)))),
      ⟨u, hu_mem, rfl⟩, ?_⟩
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    simp [smul_smul, hxnorm_ne]

/-- The cap cone expressed in split first-coordinate / tail coordinates. -/
private def capConeProd (n : ℕ) (a : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
  {p | joinFirstCoord n p ∈ capCone (n + 1) a}

private theorem norm_joinFirstCoord (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    ‖joinFirstCoord n p‖ = Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_splitFirstCoord]
  simp

private theorem mem_capConeProd_iff (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    p ∈ capConeProd n a ↔
      0 < p.1 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 ∧ ‖p.2‖ ≤ p.1 * Real.tan a := by
  rcases p with ⟨u, y⟩
  have hcos_pos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, hapi⟩
  have hsin_nonneg : 0 ≤ Real.sin a := by
    have hpi : a ≤ Real.pi := by linarith
    exact Real.sin_nonneg_of_nonneg_of_le_pi ha0 hpi
  constructor
  · intro hp
    have hmem :=
      (mem_capCone_succ_iff n ha0 hapi.le (joinFirstCoord n (u, y))).1 hp
    rcases hmem with ⟨hnorm_pos, hnorm_lt, hcoord⟩
    have hu_pos : 0 < u := by
      have hleft_pos : 0 < Real.cos a * ‖joinFirstCoord n (u, y)‖ :=
        mul_pos hcos_pos hnorm_pos
      exact lt_of_lt_of_le hleft_pos (by simpa using hcoord)
    have hball : u ^ 2 + ‖y‖ ^ 2 < 1 := by
      rw [norm_joinFirstCoord] at hnorm_lt
      have hball' : u ^ 2 + ‖y‖ ^ 2 < 1 ^ 2 := (Real.sqrt_lt' one_pos).1 hnorm_lt
      simpa using hball'
    have hcoord' : Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2) ≤ u := by
      simpa [norm_joinFirstCoord] using hcoord
    have hsqrt_le : Real.sqrt (u ^ 2 + ‖y‖ ^ 2) ≤ u / Real.cos a := by
      have hcoord'' : Real.sqrt (u ^ 2 + ‖y‖ ^ 2) * Real.cos a ≤ u := by
        simpa [mul_comm] using hcoord'
      exact (le_div_iff₀ hcos_pos).2 hcoord''
    have hsquare : u ^ 2 + ‖y‖ ^ 2 ≤ (u / Real.cos a) ^ 2 := by
      exact (Real.sqrt_le_iff).1 hsqrt_le |>.2
    have hsquare_mul :
        (Real.cos a) ^ 2 * (u ^ 2 + ‖y‖ ^ 2) ≤ u ^ 2 := by
      have h :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg (Real.cos a))
      have hcancel : (Real.cos a) ^ 2 * (u / Real.cos a) ^ 2 = u ^ 2 := by
        field_simp [hcos_pos.ne']
      simpa [hcancel] using h
    have hpoly : (Real.cos a) ^ 2 * ‖y‖ ^ 2 ≤ u ^ 2 * (Real.sin a) ^ 2 := by
      nlinarith [hsquare_mul, Real.sin_sq_add_cos_sq a]
    have hcosy_sq : (Real.cos a * ‖y‖) ^ 2 ≤ (u * Real.sin a) ^ 2 := by
      nlinarith [hpoly]
    have hcosy : Real.cos a * ‖y‖ ≤ u * Real.sin a := by
      have hleft_nonneg : 0 ≤ Real.cos a * ‖y‖ :=
        mul_nonneg hcos_pos.le (norm_nonneg _)
      have hright_nonneg : 0 ≤ u * Real.sin a :=
        mul_nonneg hu_pos.le hsin_nonneg
      have habs := (sq_le_sq.1 hcosy_sq)
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs
    have htan : ‖y‖ ≤ u * Real.tan a := by
      have hcosy' : ‖y‖ * Real.cos a ≤ u * Real.sin a := by
        simpa [mul_comm] using hcosy
      have hdiv : ‖y‖ ≤ (u * Real.sin a) / Real.cos a :=
        (le_div_iff₀ hcos_pos).2 hcosy'
      simpa [Real.tan_eq_sin_div_cos, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    exact ⟨hu_pos, hball, htan⟩
  · rintro ⟨hu_pos, hball, htan⟩
    have hnorm_pos : 0 < ‖joinFirstCoord n (u, y)‖ := by
      rw [norm_joinFirstCoord]
      have : 0 < u ^ 2 + ‖y‖ ^ 2 := by positivity
      exact Real.sqrt_pos.2 this
    have hnorm_lt : ‖joinFirstCoord n (u, y)‖ < 1 := by
      rw [norm_joinFirstCoord]
      have hball' : u ^ 2 + ‖y‖ ^ 2 < 1 ^ 2 := by simpa using hball
      exact (Real.sqrt_lt' one_pos).2 hball'
    have hcosy : Real.cos a * ‖y‖ ≤ u * Real.sin a := by
      rw [Real.tan_eq_sin_div_cos] at htan
      have h :=
        mul_le_mul_of_nonneg_left htan hcos_pos.le
      have hcancel : Real.cos a * (u * (Real.sin a / Real.cos a)) = u * Real.sin a := by
        field_simp [hcos_pos.ne']
      simpa [mul_assoc, hcancel] using h
    have hcosy_sq : (Real.cos a * ‖y‖) ^ 2 ≤ (u * Real.sin a) ^ 2 := by
      have hleft_nonneg : 0 ≤ Real.cos a * ‖y‖ :=
        mul_nonneg hcos_pos.le (norm_nonneg _)
      have hright_nonneg : 0 ≤ u * Real.sin a :=
        mul_nonneg hu_pos.le hsin_nonneg
      exact (sq_le_sq.2 <| by
        simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using hcosy)
    have hsquare :
        (Real.cos a) ^ 2 * (u ^ 2 + ‖y‖ ^ 2) ≤ u ^ 2 := by
      nlinarith [hcosy_sq, Real.sin_sq_add_cos_sq a]
    have hsq :
        (Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2)) ^ 2 ≤ u ^ 2 := by
      have hnonneg : 0 ≤ u ^ 2 + ‖y‖ ^ 2 := by positivity
      calc
        (Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2)) ^ 2
            = (Real.cos a) ^ 2 * (Real.sqrt (u ^ 2 + ‖y‖ ^ 2)) ^ 2 := by
              ring
        _ = (Real.cos a) ^ 2 * (u ^ 2 + ‖y‖ ^ 2) := by
              rw [Real.sq_sqrt hnonneg]
        _ ≤ u ^ 2 := hsquare
    have hcoord_sqrt : Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2) ≤ u := by
      have hleft_nonneg : 0 ≤ Real.cos a * Real.sqrt (u ^ 2 + ‖y‖ ^ 2) :=
        mul_nonneg hcos_pos.le (Real.sqrt_nonneg _)
      have hright_nonneg : 0 ≤ u := hu_pos.le
      have habs := (sq_le_sq.1 hsq)
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs
    have hcoord : Real.cos a * ‖joinFirstCoord n (u, y)‖ ≤ u := by
      simpa [norm_joinFirstCoord] using hcoord_sqrt
    simpa [capConeProd] using
      (mem_capCone_succ_iff n ha0 hapi.le (joinFirstCoord n (u, y))).2
        ⟨hnorm_pos, hnorm_lt, hcoord⟩

private theorem preimage_mk_capConeProd (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (u : ℝ) :
    Prod.mk u ⁻¹' capConeProd n a =
      if 0 < u then
        {y : EuclideanSpace ℝ (Fin n) | u ^ 2 + ‖y‖ ^ 2 < 1 ∧ ‖y‖ ≤ u * Real.tan a}
      else
        ∅ := by
  by_cases hu : 0 < u
  · ext y
    simp [mem_capConeProd_iff, ha0, hapi, hu]
  · ext y
    simp [mem_capConeProd_iff, ha0, hapi, hu]

private theorem u_sq_add_u_mul_tan_sq_lt_one_of_lt_cos
    {a u : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (hu : 0 ≤ u) (hu_lt : u < Real.cos a) :
    u ^ 2 + (u * Real.tan a) ^ 2 < 1 := by
  have hcos_pos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, hapi⟩
  have hu_sq_lt : u ^ 2 < (Real.cos a) ^ 2 := by
    nlinarith [hu, hu_lt, hcos_pos]
  have hmul_lt :
      u ^ 2 * (1 + Real.tan a ^ 2) < (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) := by
    have hpos : 0 < 1 + Real.tan a ^ 2 := by positivity
    exact mul_lt_mul_of_pos_right hu_sq_lt hpos
  have htrig : (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) = 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.one_add_tan_sq_mul_cos_sq_eq_one hcos_pos.ne')
  calc
    u ^ 2 + (u * Real.tan a) ^ 2 = u ^ 2 * (1 + Real.tan a ^ 2) := by ring
    _ < (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) := hmul_lt
    _ = 1 := htrig

private theorem sqrt_one_sub_u_sq_le_u_mul_tan_of_cos_le
    {a u : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2)
    (hu : 0 < u) (hcos_le : Real.cos a ≤ u) :
    Real.sqrt (1 - u ^ 2) ≤ u * Real.tan a := by
  have hcos_pos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, hapi⟩
  have htan_nonneg : 0 ≤ Real.tan a :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha0 hapi.le
  have hright_nonneg : 0 ≤ u * Real.tan a := mul_nonneg hu.le htan_nonneg
  have hcos_sq_le : (Real.cos a) ^ 2 ≤ u ^ 2 := by
    nlinarith [hcos_le, hcos_pos]
  have hmul_le :
      (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) ≤ u ^ 2 * (1 + Real.tan a ^ 2) := by
    have hnonneg : 0 ≤ 1 + Real.tan a ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hcos_sq_le hnonneg
  have htrig : (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) = 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.one_add_tan_sq_mul_cos_sq_eq_one hcos_pos.ne')
  have hone_le : 1 ≤ u ^ 2 * (1 + Real.tan a ^ 2) := by
    calc
      1 = (Real.cos a) ^ 2 * (1 + Real.tan a ^ 2) := htrig.symm
      _ ≤ u ^ 2 * (1 + Real.tan a ^ 2) := hmul_le
  have hsq_le : 1 - u ^ 2 ≤ (u * Real.tan a) ^ 2 := by
    have hsum : 1 ≤ u ^ 2 + (u * Real.tan a) ^ 2 := by
      calc
        1 ≤ u ^ 2 * (1 + Real.tan a ^ 2) := hone_le
        _ = u ^ 2 + (u * Real.tan a) ^ 2 := by ring
    nlinarith
  exact (Real.sqrt_le_iff).2 ⟨hright_nonneg, hsq_le⟩

private theorem preimage_mk_capConeProd_eq_closedBall_of_lt_cos (n : ℕ) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (hu : 0 < u) (hu_lt : u < Real.cos a) :
    Prod.mk u ⁻¹' capConeProd n a =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (u * Real.tan a) := by
  ext y
  rw [preimage_mk_capConeProd n ha0 hapi u, if_pos hu, Metric.mem_closedBall, dist_eq_norm,
    sub_zero]
  constructor
  · intro hy
    exact hy.2
  · intro hy
    constructor
    · have hy_sq : ‖y‖ ^ 2 ≤ (u * Real.tan a) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hy 2
      have hbound : u ^ 2 + (u * Real.tan a) ^ 2 < 1 :=
        u_sq_add_u_mul_tan_sq_lt_one_of_lt_cos ha0 hapi hu.le hu_lt
      nlinarith
    · exact hy

private theorem preimage_mk_capConeProd_eq_ball_of_cos_le (n : ℕ) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) (hu : 0 < u) (hcos_le : Real.cos a ≤ u) :
    Prod.mk u ⁻¹' capConeProd n a =
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (1 - u ^ 2)) := by
  ext y
  rw [preimage_mk_capConeProd n ha0 hapi u, if_pos hu, Metric.mem_ball, dist_eq_norm, sub_zero]
  constructor
  · intro hy
    have hsub_nonneg : 0 ≤ 1 - u ^ 2 := by
      nlinarith [hy.1, sq_nonneg ‖y‖]
    have hy_sq : ‖y‖ ^ 2 < 1 - u ^ 2 := by
      nlinarith [hy.1]
    exact (Real.lt_sqrt (norm_nonneg _)).2 hy_sq
  · intro hy
    have hsqrt_pos : 0 < Real.sqrt (1 - u ^ 2) := by
      exact lt_of_le_of_lt (norm_nonneg _) hy
    have hsub_nonneg : 0 ≤ 1 - u ^ 2 := by
      exact le_of_lt (Real.sqrt_pos.1 hsqrt_pos)
    have hy_sq : ‖y‖ ^ 2 < 1 - u ^ 2 := by
      exact (Real.lt_sqrt (norm_nonneg _)).1 hy
    have hball : u ^ 2 + ‖y‖ ^ 2 < 1 := by
      nlinarith
    have hradius_le : Real.sqrt (1 - u ^ 2) ≤ u * Real.tan a :=
      sqrt_one_sub_u_sq_le_u_mul_tan_of_cos_le ha0 hapi hu hcos_le
    have htan : ‖y‖ ≤ u * Real.tan a := le_trans hy.le hradius_le
    exact ⟨hball, htan⟩

private theorem volume_fiber_eq_piecewise_ball (n : ℕ) (hn : 0 < n) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (Prod.mk u ⁻¹' capConeProd n a) =
      if 0 < u then
        if u < Real.cos a then
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (u * Real.tan a))
        else
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (Real.sqrt (1 - u ^ 2)))
      else 0 := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  by_cases hu : 0 < u
  · by_cases hu_lt : u < Real.cos a
    · rw [if_pos hu, if_pos hu_lt]
      rw [preimage_mk_capConeProd_eq_closedBall_of_lt_cos n ha0 hapi hu hu_lt]
      rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_ball]
    · rw [if_pos hu, if_neg hu_lt]
      rw [preimage_mk_capConeProd_eq_ball_of_cos_le n ha0 hapi hu (le_of_not_gt hu_lt)]
  · rw [if_neg hu]
    rw [preimage_mk_capConeProd n ha0 hapi u, if_neg hu, measure_empty]

private theorem measurableSet_capConeProd (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    MeasurableSet (capConeProd n a) := by
  have hset :
      capConeProd n a =
        {p : ℝ × EuclideanSpace ℝ (Fin n) |
          0 < p.1 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 ∧ ‖p.2‖ ≤ p.1 * Real.tan a} := by
    ext p
    simpa using (mem_capConeProd_iff n ha0 hapi p)
  rw [hset]
  have hcont_sqnorm :
      Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.1 ^ 2 + ‖p.2‖ ^ 2 := by
    fun_prop
  have hcont_tan :
      Continuous fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.1 * Real.tan a := by
    fun_prop
  exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter <|
    (isOpen_lt hcont_sqnorm continuous_const).measurableSet.inter <|
      (isClosed_le (continuous_norm.comp continuous_snd) hcont_tan).measurableSet

private theorem volume_capCone_eq_volume_capConeProd (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) (capConeProd n a) := by
  rw [← (measurePreserving_splitFirstCoord n).map_eq]
  rw [Measure.map_apply (measurePreserving_splitFirstCoord n).measurable
    (measurableSet_capConeProd n ha0 hapi)]
  congr 1
  ext x
  simp [capConeProd]

private theorem volume_capCone_eq_lintegral_fiber (n : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      ∫⁻ u, (volume : Measure (EuclideanSpace ℝ (Fin n))) (Prod.mk u ⁻¹' capConeProd n a)
        ∂(volume : Measure ℝ) := by
  rw [volume_capCone_eq_volume_capConeProd n ha0 hapi]
  rw [Measure.volume_eq_prod ℝ (EuclideanSpace ℝ (Fin n))]
  rw [Measure.prod_apply (measurableSet_capConeProd n ha0 hapi)]

private theorem volume_capCone_eq_lintegral_fiber_piecewise_ball (n : ℕ) (hn : 0 < n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      ∫⁻ u, if 0 < u then
          if u < Real.cos a then
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (u * Real.tan a))
          else
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 (Real.sqrt (1 - u ^ 2)))
        else 0
        ∂(volume : Measure ℝ) := by
  rw [volume_capCone_eq_lintegral_fiber n ha0 hapi]
  refine lintegral_congr_ae ?_
  filter_upwards with u
  rw [volume_fiber_eq_piecewise_ball n hn ha0 hapi]

private theorem volume_fiber_eq_piecewise_pow (n : ℕ) (hn : 0 < n) {a u : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (Prod.mk u ⁻¹' capConeProd n a) =
      if 0 < u then
        if u < Real.cos a then
          ENNReal.ofReal ((u * Real.tan a) ^ n) *
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
        else
          ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n) *
            (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
      else 0 := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [volume_fiber_eq_piecewise_ball n hn ha0 hapi]
  by_cases hu : 0 < u
  · by_cases hu_lt : u < Real.cos a
    · rw [if_pos hu, if_pos hu_lt]
      have htan_nonneg : 0 ≤ u * Real.tan a := by
        have htan_nonneg : 0 ≤ Real.tan a :=
          Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha0 hapi.le
        exact mul_nonneg hu.le htan_nonneg
      rw [Measure.addHaar_ball (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (x := (0 : EuclideanSpace ℝ (Fin n))) (hr := htan_nonneg)]
      simp [hu, hu_lt]
    · rw [if_pos hu, if_neg hu_lt]
      rw [Measure.addHaar_ball (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (x := (0 : EuclideanSpace ℝ (Fin n))) (hr := Real.sqrt_nonneg _)]
      simp [hu, hu_lt]
  · simp [hu]

private theorem volume_capCone_eq_lintegral_fiber_piecewise_pow (n : ℕ) (hn : 0 < n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      ∫⁻ u, if 0 < u then
          if u < Real.cos a then
            ENNReal.ofReal ((u * Real.tan a) ^ n) *
              (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
          else
            ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n) *
              (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
        else 0
        ∂(volume : Measure ℝ) := by
  rw [volume_capCone_eq_lintegral_fiber_piecewise_ball n hn ha0 hapi]
  refine lintegral_congr_ae ?_
  filter_upwards with u
  exact
    (volume_fiber_eq_piecewise_ball n hn (a := a) (u := u) ha0 hapi).symm.trans
      (volume_fiber_eq_piecewise_pow n hn (a := a) (u := u) ha0 hapi)

/-- The one-dimensional piecewise power integrand arising from the first-coordinate fiber
decomposition of the cap cone. -/
private def capConeFiberPowIntegrand (n : ℕ) (a u : ℝ) : ℝ≥0∞ :=
  if 0 < u then
    if u < Real.cos a then
      ENNReal.ofReal ((u * Real.tan a) ^ n)
    else
      ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n)
  else
    0


private theorem volume_capCone_eq_lintegral_capConeFiberPow_mul_unitBall
    (n : ℕ) (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) (capCone (n + 1) a) =
      (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)) *
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1) := by
  let C : ℝ≥0∞ := (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
  have hC : C ≠ ∞ := by
    exact measure_ball_lt_top.ne
  rw [volume_capCone_eq_lintegral_fiber_piecewise_pow n hn ha0 hapi]
  have hrewrite :
      (∫⁻ u, if 0 < u then
          if u < Real.cos a then
            ENNReal.ofReal ((u * Real.tan a) ^ n) * C
          else
            ENNReal.ofReal ((Real.sqrt (1 - u ^ 2)) ^ n) * C
        else 0
        ∂(volume : Measure ℝ)) =
      ∫⁻ u, capConeFiberPowIntegrand n a u * C ∂(volume : Measure ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards with u
    by_cases hu : 0 < u <;> simp [capConeFiberPowIntegrand, hu, C]
  rw [hrewrite, lintegral_mul_const' C (capConeFiberPowIntegrand n a) hC]

private theorem volumeReal_capCone_eq_lintegral_capConeFiberPow_mul_unitBall
    (n : ℕ) (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).real (capCone (n + 1) a) =
      (∫⁻ u, capConeFiberPowIntegrand n a u ∂(volume : Measure ℝ)).toReal *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) := by
  rw [measureReal_def, volume_capCone_eq_lintegral_capConeFiberPow_mul_unitBall n hn ha0 hapi,
    ENNReal.toReal_mul, measureReal_def]

private theorem capCone_subset_ball (n : ℕ) (a : ℝ) :
    capCone n a ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rintro x ⟨r, hr, y, ⟨u, _, rfl⟩, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul]
  have hu_norm : ‖((u : SpherePoint n) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hu_sphere := u.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu_sphere
  simp [abs_of_pos hr.1, hu_norm, hr.2]

private theorem sphereSurfaceMeasure_capSet_eq_mul_volume_capCone
    {n : ℕ} (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    (sphereSurfaceMeasure n).real (capSet n a) =
      n * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (capCone n a) := by
  have hs : MeasurableSet (capSet n a) := measurableSet_capSet hn ha0 hapi
  have hcone_fin :
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (capCone n a) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono (capCone_subset_ball n a)) measure_ball_lt_top
  have hcone :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) (capSet n a) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) *
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (capCone n a) := by
    simpa [capCone] using
      (Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hs)
  simpa [sphereSurfaceMeasure, measureReal_def, finrank_euclideanSpace_fin,
    hcone_fin] using congrArg ENNReal.toReal hcone

private theorem capMeasure_eq_volume_capCone_div_volume_ball
    (n : ℕ) (hn : 0 < n) {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    capMeasure n a =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real (capCone n a) /
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have hcast : (((n - 1 : ℕ) : ℝ) + 1) = n := by
    exact_mod_cast hsub
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [capMeasure_eq_div_surfaceMeasure hn]
  rw [sphereSurfaceMeasure_capSet_eq_mul_volume_capCone hn ha0 hapi]
  rw [sphereArea_eq_finrank_mul_volume_ball]
  rw [hsub, hcast]
  simpa using
    (mul_div_mul_left
      (a := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (capCone n a))
      (b := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1))
      (c := (n : ℝ)) hn')

private theorem capMeasure_eq_lintegral_capConeFiberPow
    (n : ℕ) (hn : 2 ≤ n) (a : ℝ) (ha0 : 0 ≤ a) (hapi : a < Real.pi / 2) :
    capMeasure n a =
      (∫⁻ u, capConeFiberPowIntegrand (n - 1) a u ∂(volume : Measure ℝ)).toReal *
        (volume : Measure (EuclideanSpace ℝ (Fin (n - 1)))).real (Metric.ball 0 1) /
          (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) := by
  cases n with
  | zero =>
      cases hn
  | succ m =>
      have hm_pos : 0 < m := by
        apply Nat.succ_lt_succ_iff.mp
        have : 1 < m + 1 := lt_of_lt_of_le (by decide : 1 < 2) hn
        simpa using this
      rw [capMeasure_eq_volume_capCone_div_volume_ball (m + 1) (Nat.succ_pos _) ha0 hapi.le]
      rw [volumeReal_capCone_eq_lintegral_capConeFiberPow_mul_unitBall m hm_pos ha0 hapi]
      rfl





/-! ### Cap measure bounds -/

section CapBounds

variable {a : ℝ}

private theorem cos_pos_of_lt_pi_div_two (ha0 : 0 < a) (hapi : a < π / 2) : 0 < Real.cos a :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hapi⟩

private theorem sin_nonneg_of_lt_pi_div_two (ha0 : 0 < a) (hapi : a < π / 2) :
    0 ≤ Real.sin a :=
  Real.sin_nonneg_of_nonneg_of_le_pi ha0.le (by linarith [Real.pi_pos])

/-- The first-coordinate fibre integrand is bounded by `sin a ^ m` on `(0,1)` and vanishes
off it. -/
private theorem lintegral_capConeFiberPow_le (m : ℕ) (hm : 0 < m)
    (ha0 : 0 < a) (hapi : a < π / 2) :
    ∫⁻ u, capConeFiberPowIntegrand m a u ∂(volume : Measure ℝ)
      ≤ ENNReal.ofReal (Real.sin a ^ m) := by
  have hcos_pos := cos_pos_of_lt_pi_div_two ha0 hapi
  have hsin_nonneg := sin_nonneg_of_lt_pi_div_two ha0 hapi
  have htan_nonneg : 0 ≤ Real.tan a :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha0.le hapi.le
  have hsin_eq : Real.sin a = Real.sqrt (1 - Real.cos a ^ 2) :=
    Real.sin_eq_sqrt_one_sub_cos_sq ha0.le (by linarith [Real.pi_pos])
  have hbound : ∀ u : ℝ, capConeFiberPowIntegrand m a u
      ≤ (Set.Ioo (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (Real.sin a ^ m)) u := by
    intro u
    unfold capConeFiberPowIntegrand
    split_ifs with h1 h2
    · have hu1 : u < 1 := lt_of_lt_of_le h2 (Real.cos_le_one a)
      rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨h1, hu1⟩)]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ m)
      rw [Real.tan_eq_sin_div_cos, mul_div_assoc', div_le_iff₀ hcos_pos]
      nlinarith [hsin_nonneg, h2.le, hcos_pos]
    · by_cases hu1 : u < 1
      · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨h1, hu1⟩)]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ m)
        rw [hsin_eq]
        exact Real.sqrt_le_sqrt (by nlinarith [not_lt.mp h2])
      · have hzero : Real.sqrt (1 - u ^ 2) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (by nlinarith [not_lt.mp hu1])
        rw [hzero, zero_pow hm.ne']
        simp
    · simp
  calc ∫⁻ u, capConeFiberPowIntegrand m a u ∂(volume : Measure ℝ)
      ≤ ∫⁻ u, (Set.Ioo (0 : ℝ) 1).indicator
            (fun _ => ENNReal.ofReal (Real.sin a ^ m)) u ∂(volume : Measure ℝ) :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (Real.sin a ^ m) := by
        rw [lintegral_indicator measurableSet_Ioo, lintegral_const,
          Measure.restrict_apply_univ, Real.volume_Ioo]
        simp

/-- Restricting the fibre integral to the linear branch gives the matching lower bound. -/
private theorem lintegral_capConeFiberPow_ge (m : ℕ)
    (ha0 : 0 < a) (hapi : a < π / 2) :
    ENNReal.ofReal (Real.sin a ^ m * Real.cos a / (m + 1))
      ≤ ∫⁻ u, capConeFiberPowIntegrand m a u ∂(volume : Measure ℝ) := by
  have hcos_pos := cos_pos_of_lt_pi_div_two ha0 hapi
  have hsin_nonneg := sin_nonneg_of_lt_pi_div_two ha0 hapi
  have htan_nonneg : 0 ≤ Real.tan a :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha0.le hapi.le
  have hGle : ∀ u : ℝ,
      (Set.Ioo (0 : ℝ) (Real.cos a)).indicator
          (fun v => ENNReal.ofReal ((v * Real.tan a) ^ m)) u
        ≤ capConeFiberPowIntegrand m a u := by
    intro u
    by_cases hu : u ∈ Set.Ioo (0 : ℝ) (Real.cos a)
    · rw [Set.indicator_of_mem hu]
      unfold capConeFiberPowIntegrand
      rw [if_pos hu.1, if_pos hu.2]
    · rw [Set.indicator_of_notMem hu]
      exact zero_le
  have hint : ∫⁻ u, (Set.Ioo (0 : ℝ) (Real.cos a)).indicator
          (fun v => ENNReal.ofReal ((v * Real.tan a) ^ m)) u ∂(volume : Measure ℝ)
      = ENNReal.ofReal (Real.sin a ^ m * Real.cos a / (m + 1)) := by
    rw [lintegral_indicator measurableSet_Ioo]
    have hcont : Continuous fun v : ℝ => (v * Real.tan a) ^ m := by fun_prop
    have hintegrable : IntegrableOn (fun v : ℝ => (v * Real.tan a) ^ m)
        (Set.Ioo 0 (Real.cos a)) volume :=
      (hcont.integrableOn_Icc (a := 0) (b := Real.cos a)).mono_set Set.Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioo 0 (Real.cos a))]
        fun v => (v * Real.tan a) ^ m := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      have hv0 : 0 ≤ v * Real.tan a := mul_nonneg hv.1.le htan_nonneg
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnn]
    congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hcos_pos.le]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_mul_const, integral_pow,
      Real.tan_eq_sin_div_cos, div_pow, zero_pow (Nat.succ_ne_zero m), pow_succ]
    field_simp
    ring
  calc ENNReal.ofReal (Real.sin a ^ m * Real.cos a / (m + 1))
      = ∫⁻ u, (Set.Ioo (0 : ℝ) (Real.cos a)).indicator
          (fun v => ENNReal.ofReal ((v * Real.tan a) ^ m)) u ∂(volume : Measure ℝ) := hint.symm
    _ ≤ ∫⁻ u, capConeFiberPowIntegrand m a u ∂(volume : Measure ℝ) := lintegral_mono hGle

private theorem ballVol_eq_measureReal (n : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) = ballVol n := rfl

private theorem capMeasure_eq_toReal_mul_ratio {k : ℕ}
    (ha0 : 0 < a) (hapi : a < π / 2) :
    capMeasure (k + 2) a
      = (∫⁻ u, capConeFiberPowIntegrand (k + 1) a u ∂(volume : Measure ℝ)).toReal
          * (ballVol (k + 1) / ballVol (k + 2)) := by
  rw [capMeasure_eq_lintegral_capConeFiberPow (k + 2) (by omega) a ha0.le hapi]
  simp only [ballVol_eq_measureReal]
  rw [show k + 2 - 1 = k + 1 from rfl, mul_div_assoc]

/-- Cap measure is at most `n * sin a ^ (n-1)`. The exponential factor is what matters;
the polynomial factor is crude and does not affect the exponent. -/
private theorem capMeasure_le {n : ℕ} (hn : 2 ≤ n) (ha0 : 0 < a) (hapi : a < π / 2) :
    capMeasure n a ≤ (n : ℝ) * Real.sin a ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hsin_nonneg := sin_nonneg_of_lt_pi_div_two ha0 hapi
  have hI_le := lintegral_capConeFiberPow_le (k + 1) (by omega) ha0 hapi
  have hItoReal :
      (∫⁻ u, capConeFiberPowIntegrand (k + 1) a u ∂(volume : Measure ℝ)).toReal
        ≤ Real.sin a ^ (k + 1) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hI_le
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hratio := (ballVol_ratio_bounds k).2
  have hv1 := ballVol_pos (k + 1)
  have hv2 := ballVol_pos (k + 2)
  rw [capMeasure_eq_toReal_mul_ratio ha0 hapi]
  calc (∫⁻ u, capConeFiberPowIntegrand (k + 1) a u ∂(volume : Measure ℝ)).toReal
          * (ballVol (k + 1) / ballVol (k + 2))
      ≤ Real.sin a ^ (k + 1) * ((k : ℝ) + 2) :=
        mul_le_mul hItoReal hratio (by positivity) (by positivity)
    _ = ((k + 2 : ℕ) : ℝ) * Real.sin a ^ (k + 2 - 1) := by
        rw [show k + 2 - 1 = k + 1 from rfl]; push_cast; ring

/-- Cap measure is at least `sin a ^ (n-1) * cos a / (2n)`. -/
private theorem capMeasure_ge {n : ℕ} (hn : 2 ≤ n) (ha0 : 0 < a) (hapi : a < π / 2) :
    Real.sin a ^ (n - 1) * Real.cos a / (2 * (n : ℝ)) ≤ capMeasure n a := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hsin_nonneg := sin_nonneg_of_lt_pi_div_two ha0 hapi
  have hcos_pos := cos_pos_of_lt_pi_div_two ha0 hapi
  have hI_ge := lintegral_capConeFiberPow_ge (k + 1) ha0 hapi
  have hI_le := lintegral_capConeFiberPow_le (k + 1) (by omega) ha0 hapi
  have hIne : (∫⁻ u, capConeFiberPowIntegrand (k + 1) a u ∂(volume : Measure ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI_le
  have hItoReal : Real.sin a ^ (k + 1) * Real.cos a / ((k : ℝ) + 2)
      ≤ (∫⁻ u, capConeFiberPowIntegrand (k + 1) a u ∂(volume : Measure ℝ)).toReal := by
    have h := ENNReal.toReal_mono hIne hI_ge
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    calc Real.sin a ^ (k + 1) * Real.cos a / ((k : ℝ) + 2)
        = Real.sin a ^ (k + 1) * Real.cos a / (((k + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf
      _ ≤ _ := h
  have hratio := (ballVol_ratio_bounds k).1
  have hv1 := ballVol_pos (k + 1)
  have hv2 := ballVol_pos (k + 2)
  rw [capMeasure_eq_toReal_mul_ratio ha0 hapi]
  calc Real.sin a ^ (k + 2 - 1) * Real.cos a / (2 * ((k + 2 : ℕ) : ℝ))
      = (Real.sin a ^ (k + 1) * Real.cos a / ((k : ℝ) + 2)) * (1 / 2) := by
        rw [show k + 2 - 1 = k + 1 from rfl]
        have hk : ((k : ℝ) + 2) ≠ 0 := by positivity
        push_cast
        field_simp
    _ ≤ (∫⁻ u, capConeFiberPowIntegrand (k + 1) a u ∂(volume : Measure ℝ)).toReal
          * (ballVol (k + 1) / ballVol (k + 2)) :=
        mul_le_mul hItoReal hratio (by norm_num) (by positivity)

end CapBounds

/-! ### Caps around arbitrary centres, and the sphere probability measure -/

/-- The spherical cap of angular radius `a` around the sphere point `v`. -/
private def capAround {n : ℕ} (v : SpherePoint n) (a : ℝ) : Set (SpherePoint n) :=
  {x | InnerProductGeometry.angle x.1 v.1 ≤ a}

@[simp]
private theorem mem_capAround {n : ℕ} {v x : SpherePoint n} {a : ℝ} :
    x ∈ capAround v a ↔ InnerProductGeometry.angle x.1 v.1 ≤ a :=
  Iff.rfl

@[simp]
private theorem norm_spherePoint {n : ℕ} (x : SpherePoint n) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have hx := x.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx

/-- The reflection sending `e₁` to the sphere point `v`. -/
private def capCenterReflection {n : ℕ} (v : SpherePoint n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Submodule.reflection (ℝ ∙ (e1Vec n - v.1))ᗮ

private theorem capCenterReflection_map_e1Vec {n : ℕ} (hn : 0 < n) (v : SpherePoint n) :
    capCenterReflection v (e1Vec n) = v.1 := by
  have hvnorm : ‖v.1‖ = 1 := norm_spherePoint v
  have heq : ‖e1Vec n‖ = ‖v.1‖ := by
    rw [norm_e1Vec hn, hvnorm]
  simpa [capCenterReflection] using
    (Submodule.reflection_sub (v := e1Vec n) (w := v.1) heq)

private theorem capCenterReflection_symm_apply_v {n : ℕ} (hn : 0 < n) (v : SpherePoint n) :
    (capCenterReflection v).symm v.1 = e1Vec n := by
  have hmap := capCenterReflection_map_e1Vec hn v
  simpa using (congrArg (capCenterReflection v).symm hmap).symm

private theorem image_capSet_eq_capAround {n : ℕ} (hn : 0 < n) (v : SpherePoint n) (a : ℝ) :
    capCenterReflection v '' ((↑) '' capSet n a) = ((↑) '' capAround v a) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨capCenterReflection v z.1, ?_⟩, ?_, rfl⟩
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact ((capCenterReflection v).norm_map z.1).trans (norm_spherePoint z)
    · have hangle :
          InnerProductGeometry.angle ((capCenterReflection v) z.1)
            ((capCenterReflection v) (e1Vec n)) ≤ a := by
        calc
          InnerProductGeometry.angle ((capCenterReflection v) z.1)
              ((capCenterReflection v) (e1Vec n))
            = InnerProductGeometry.angle z.1 (e1Vec n) := by
                simpa using
                  ((capCenterReflection v).toLinearIsometry.angle_map z.1 (e1Vec n))
          _ ≤ a := hz
      simpa [capCenterReflection_map_e1Vec hn v] using hangle
  · rintro ⟨x', hx', rfl⟩
    refine ⟨(capCenterReflection v).symm x'.1, ?_, by simp⟩
    refine ⟨⟨(capCenterReflection v).symm x'.1, ?_⟩, ?_, rfl⟩
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact ((capCenterReflection v).symm.norm_map x'.1).trans (norm_spherePoint x')
    · have hangle :
          InnerProductGeometry.angle ((capCenterReflection v).symm x'.1)
            ((capCenterReflection v).symm v.1) ≤ a := by
        calc
          InnerProductGeometry.angle ((capCenterReflection v).symm x'.1)
              ((capCenterReflection v).symm v.1)
            = InnerProductGeometry.angle x'.1 v.1 := by
                simpa using
                  ((capCenterReflection v).symm.toLinearIsometry.angle_map x'.1 v.1)
          _ ≤ a := hx'
      simpa [capSet, Set.mem_ofPred_eq, capCenterReflection_symm_apply_v hn v] using hangle

private theorem preimage_capAroundCone_eq_capCone
    {n : ℕ} (hn : 0 < n) (v : SpherePoint n) (a : ℝ) :
    capCenterReflection v ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' capAround v a)) =
      Set.Ioo (0 : ℝ) 1 • ((↑) '' capSet n a) := by
  ext x
  constructor
  · intro hx
    rw [← image_capSet_eq_capAround hn v a] at hx
    rcases hx with ⟨r, hr, y, hy, hxy⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨r, hr, z, hz, ?_⟩
    apply (capCenterReflection v).injective
    simpa using hxy
  · rintro ⟨r, hr, y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨r, hr, capCenterReflection v z.1, ?_, ?_⟩
    · refine ⟨⟨capCenterReflection v z.1, ?_⟩, ?_, rfl⟩
      · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        exact ((capCenterReflection v).norm_map z.1).trans (norm_spherePoint z)
      · have hangle :
            InnerProductGeometry.angle ((capCenterReflection v) z.1)
              ((capCenterReflection v) (e1Vec n)) ≤ a := by
          calc
            InnerProductGeometry.angle ((capCenterReflection v) z.1)
                ((capCenterReflection v) (e1Vec n))
              = InnerProductGeometry.angle z.1 (e1Vec n) := by
                  simpa using
                    ((capCenterReflection v).toLinearIsometry.angle_map z.1 (e1Vec n))
            _ ≤ a := hz
        simpa [capCenterReflection_map_e1Vec hn v] using hangle
    · exact ((capCenterReflection v).map_smul r z.1).symm

private theorem measurableSet_capAround {n : ℕ} (v : SpherePoint n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    MeasurableSet (capAround v a) := by
  have hcont :
      Continuous fun x : SpherePoint n =>
        inner ℝ (x : EuclideanSpace ℝ (Fin n)) v.1 := by
    fun_prop
  have hcap :
      capAround v a
        = {x : SpherePoint n | Real.cos a ≤ inner ℝ (x : EuclideanSpace ℝ (Fin n)) v.1} := by
    ext x
    have hxnorm : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_spherePoint x
    have hvnorm : ‖v.1‖ = 1 := norm_spherePoint v
    constructor
    · intro hx
      have hapi' : a ≤ Real.pi := by linarith [Real.pi_pos]
      have hcos :
          Real.cos a ≤ Real.cos (InnerProductGeometry.angle x.1 v.1) :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          (InnerProductGeometry.angle_nonneg _ _) hapi' hx
      calc
        Real.cos a ≤ Real.cos (InnerProductGeometry.angle x.1 v.1) := hcos
        _ = inner ℝ x.1 v.1 := by
          rw [InnerProductGeometry.cos_angle, hxnorm, hvnorm]
          norm_num
    · intro hx
      have h_arccos :
          Real.arccos (inner ℝ x.1 v.1) ≤ Real.arccos (Real.cos a) :=
        Real.arccos_le_arccos hx
      have hacos : Real.arccos (Real.cos a) = a := by
        have hapi' : a ≤ Real.pi := by linarith [Real.pi_pos]
        exact Real.arccos_cos ha0 hapi'
      have hangle :
          InnerProductGeometry.angle x.1 v.1 = Real.arccos (inner ℝ x.1 v.1) := by
        simp [InnerProductGeometry.angle, hxnorm, hvnorm]
      change InnerProductGeometry.angle x.1 v.1 ≤ a
      rw [hangle]
      exact le_trans h_arccos hacos.le
  rw [hcap]
  exact (isClosed_le continuous_const hcont).measurableSet

private theorem sphereSurfaceMeasure_capAround_eq_capSet
    {n : ℕ} (hn : 0 < n) (v : SpherePoint n)
    {a : ℝ} (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    (sphereSurfaceMeasure n).real (capAround v a) =
      (sphereSurfaceMeasure n).real (capSet n a) := by
  let coneAround : Set (EuclideanSpace ℝ (Fin n)) := Set.Ioo (0 : ℝ) 1 • ((↑) '' capAround v a)
  let coneCap : Set (EuclideanSpace ℝ (Fin n)) := Set.Ioo (0 : ℝ) 1 • ((↑) '' capSet n a)
  have hsAround : MeasurableSet (capAround v a) := measurableSet_capAround v ha0 hapi
  have hAround :
      (sphereSurfaceMeasure n).real (capAround v a) =
        n * (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneAround := by
    simpa [sphereSurfaceMeasure, coneAround, measureReal_def, finrank_euclideanSpace_fin] using
      congrArg ENNReal.toReal
        (Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsAround)
  have hCap :
      (sphereSurfaceMeasure n).real (capSet n a) =
        n * (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneCap := by
    simpa [coneCap, capCone] using
      sphereSurfaceMeasure_capSet_eq_mul_volume_capCone (n := n) hn ha0 hapi
  have hpre :
      capCenterReflection v ⁻¹' coneAround = coneCap := by
    simpa [coneAround, coneCap] using preimage_capAroundCone_eq_capCone hn v a
  have hpres :
      MeasurePreserving (capCenterReflection v).toMeasurableEquiv
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa using
      ((capCenterReflection v).measurePreserving :
        MeasurePreserving (capCenterReflection v)
          (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hvol :
      (volume : Measure (EuclideanSpace ℝ (Fin n))) coneAround =
        (volume : Measure (EuclideanSpace ℝ (Fin n))) coneCap := by
    have hmp :
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (((capCenterReflection v).toMeasurableEquiv) ⁻¹' coneAround) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))) coneAround := by
      simpa using hpres.measure_preimage_equiv coneAround
    have hpre' :
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (((capCenterReflection v).toMeasurableEquiv) ⁻¹' coneAround) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))) coneCap := by
      simpa using
        congrArg (fun s : Set (EuclideanSpace ℝ (Fin n)) =>
          (volume : Measure (EuclideanSpace ℝ (Fin n))) s) hpre
    exact hmp.symm.trans hpre'
  have hvolReal :
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneAround =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real coneCap :=
    congrArg ENNReal.toReal hvol
  rw [hAround, hCap, hvolReal]

private theorem sphereSurfaceMeasure_ne_zero {n : ℕ} (hn : 0 < n) :
    sphereSurfaceMeasure n ≠ 0 := by
  let : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    infer_instance
  change ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) ≠ 0
  exact Measure.toSphere_ne_zero (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))

/-- The normalized surface measure on `S^(n-1)`. -/
private noncomputable def sphereProbabilityMeasure (n : ℕ) (hn : 0 < n) :
    ProbabilityMeasure (SpherePoint n) := by
  letI : NeZero (sphereSurfaceMeasure n) := ⟨sphereSurfaceMeasure_ne_zero hn⟩
  letI : IsFiniteMeasure (sphereSurfaceMeasure n) := by
    dsimp [sphereSurfaceMeasure]
    infer_instance
  exact ⟨((sphereSurfaceMeasure n) Set.univ)⁻¹ • sphereSurfaceMeasure n,
    show IsProbabilityMeasure (((sphereSurfaceMeasure n) Set.univ)⁻¹ • sphereSurfaceMeasure n) from
      inferInstance⟩

private theorem sphereProbabilityMeasure_real_apply
    {n : ℕ} (hn : 0 < n) (s : Set (SpherePoint n)) :
    ((sphereProbabilityMeasure n hn : Measure (SpherePoint n)).real s) =
      (sphereSurfaceMeasure n).real s / sphereArea (n - 1) := by
  let : NeZero (sphereSurfaceMeasure n) := ⟨sphereSurfaceMeasure_ne_zero hn⟩
  let : IsFiniteMeasure (sphereSurfaceMeasure n) := by
    dsimp [sphereSurfaceMeasure]
    infer_instance
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have hrealuniv :
      (sphereSurfaceMeasure n).real Set.univ = sphereArea (n - 1) := by
    rw [sphereArea_def, hsub]
  have huniv :
      (sphereSurfaceMeasure n) Set.univ = ENNReal.ofReal (sphereArea (n - 1)) := by
    rw [← ofReal_measureReal (μ := sphereSurfaceMeasure n) (s := Set.univ)
      (h := (measure_lt_top (sphereSurfaceMeasure n) Set.univ).ne)]
    rw [hrealuniv]
  unfold sphereProbabilityMeasure
  simp [measureReal_ennreal_smul_apply, huniv, div_eq_mul_inv, mul_comm]

private theorem sphereProbabilityMeasure_real_capAround_eq_capMeasure
    {n : ℕ} (hn : 2 ≤ n) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    ((sphereProbabilityMeasure n (show 0 < n by omega) :
        Measure (SpherePoint n)).real (capAround v a)) =
      capMeasure n a := by
  have hn0 : 0 < n := by omega
  calc
    ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real (capAround v a))
      = (sphereSurfaceMeasure n).real (capAround v a) / sphereArea (n - 1) :=
          sphereProbabilityMeasure_real_apply hn0 (capAround v a)
    _ = (sphereSurfaceMeasure n).real (capSet n a) / sphereArea (n - 1) := by
          rw [sphereSurfaceMeasure_capAround_eq_capSet hn0 v ha0 hapi]
    _ = capMeasure n a := by
          symm
          exact capMeasure_eq_div_surfaceMeasure hn0 a

/-! ### Finite angular nets -/

@[simp]
private theorem norm_spherePoint' {n : ℕ} (x : SpherePoint n) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have hx := x.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx

/-- If the angular distance between two sphere points is larger than `ε`, then their ambient
Euclidean distance is larger than `ε / 2`, provided `ε ≤ 1`. -/
private theorem half_eps_lt_dist_of_angle_gt
    {n : ℕ} {u v : SpherePoint n} {ε : ℝ}
    (hε0 : 0 < ε) (_hε1 : ε ≤ 1)
    (hangle : ε < InnerProductGeometry.angle u.1 v.1) :
    ε / 2 < dist u v := by
  let θ := InnerProductGeometry.angle u.1 v.1
  have hε1 : ε ≤ 1 := _hε1
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg _ _
  have hθ_le_pi : θ ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
  have hε_half_mem : ε / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have : 0 ≤ ε / 2 := by positivity
      linarith
    · have hε_pi : ε / 2 ≤ Real.pi / 2 := by
        linarith [hε1, Real.pi_gt_three]
      exact hε_pi
  have hθ_half_mem : θ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith
    · linarith
  have hsin_lt :
      Real.sin (ε / 2) < Real.sin (θ / 2) := by
    exact Real.strictMonoOn_sin hε_half_mem hθ_half_mem (by linarith)
  have hquarter_le_sin :
      ε / 4 ≤ Real.sin (ε / 2) := by
    have hhalf_nonneg : 0 ≤ ε / 2 := by positivity
    have hhalf_le_pi2 : ε / 2 ≤ Real.pi / 2 := by
      linarith [hε1, Real.pi_gt_three]
    have hmul : (2 / Real.pi) * (ε / 2) ≤ Real.sin (ε / 2) :=
      Real.mul_le_sin hhalf_nonneg hhalf_le_pi2
    have hmul'' : ε / 4 ≤ (2 / Real.pi) * (ε / 2) := by
      have hcoeff : (1 / 4 : ℝ) ≤ 1 / Real.pi := by
        simpa using one_div_le_one_div_of_le Real.pi_pos Real.pi_le_four
      have hmul' : ε * (1 / 4 : ℝ) ≤ ε * (1 / Real.pi) := by
        exact mul_le_mul_of_nonneg_left hcoeff hε0.le
      calc
        ε / 4 = ε * (1 / 4 : ℝ) := by ring
        _ ≤ ε * (1 / Real.pi) := hmul'
        _ = (2 / Real.pi) * (ε / 2) := by ring
    exact hmul''.trans hmul
  have hquarter_lt : ε / 4 < Real.sin (θ / 2) :=
    by simpa [div_eq_mul_inv, mul_assoc] using lt_of_le_of_lt hquarter_le_sin hsin_lt
  have hnorm_sq :
      dist u v * dist u v = 4 * Real.sin (θ / 2) * Real.sin (θ / 2) := by
    have hu : ‖u.1‖ = 1 := norm_spherePoint' u
    have hv : ‖v.1‖ = 1 := norm_spherePoint' v
    change ‖u.1 - v.1‖ * ‖u.1 - v.1‖ = 4 * Real.sin (θ / 2) * Real.sin (θ / 2)
    calc
      ‖u.1 - v.1‖ * ‖u.1 - v.1‖
          = ‖u.1‖ * ‖u.1‖ + ‖v.1‖ * ‖v.1‖
              - 2 * ‖u.1‖ * ‖v.1‖ * Real.cos θ := by
                simpa [θ] using
                  norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
                    u.1 v.1
      _ = 2 - 2 * Real.cos θ := by rw [hu, hv]; ring
      _ = 4 * Real.sin (θ / 2) * Real.sin (θ / 2) := by
            rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
            have hhalf : 2 * (θ / 2) / 2 = θ / 2 := by ring
            rw [hhalf]
            nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hdist_nonneg : 0 ≤ dist u v := dist_nonneg
  have hsin_nonneg : 0 ≤ Real.sin (θ / 2) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith
  nlinarith

/-- A Euclidean distance bound of `ε / 2` implies an angular distance bound of `ε`
for sphere points, provided `ε ≤ 1`. -/
private theorem angle_le_of_dist_le_half_eps
    {n : ℕ} {u v : SpherePoint n} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hdist : dist u v ≤ ε / 2) :
    InnerProductGeometry.angle u.1 v.1 ≤ ε := by
  by_contra hgt
  have : ε / 2 < dist u v :=
    half_eps_lt_dist_of_angle_gt hε0 hε1 (lt_of_not_ge hgt)
  linarith

/-- A separated finite subset of the unit sphere has size at most `(5 / ε)^n`. -/
private theorem spherePoint_finset_card_le_of_separated
    {n : ℕ} (s : Finset (SpherePoint n)) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ε / 2 < dist u v) :
    (s.card : ℝ) ≤ (5 / ε) ^ n := by
  let E := EuclideanSpace ℝ (Fin n)
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε / 4
  let ρ : ℝ := 1 + ε / 4
  have hδ_pos : 0 < δ := by positivity
  have hρ_pos : 0 < ρ := by positivity
  set A : Set E := ⋃ c ∈ s, Metric.ball (c.1 : E) δ with hA
  have hdisj :
      Set.Pairwise (s : Set (SpherePoint n))
        (fun c d => Disjoint (Metric.ball (c.1 : E) δ) (Metric.ball (d.1 : E) δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    have hdist : ε / 2 < dist c d := hsep c hc d hd hcd
    have hdelta : δ + δ = ε / 2 := by
      simp [δ]
      ring
    change δ + δ ≤ dist c.1 d.1
    simpa [hdelta, Subtype.dist_eq, dist_eq_norm] using hdist.le
  have hA_subset : A ⊆ Metric.ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    have hxnorm : dist x.1 0 ≤ 1 := by
      rw [dist_eq_norm, sub_zero]
      exact (norm_spherePoint' x).le
    calc
      δ + dist x.1 0 ≤ δ + 1 := by
        linarith
      _ ≤ ρ := by
        dsimp [δ, ρ]
        linarith
  have hmeasure :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball 0 1) ≤
        ENNReal.ofReal (ρ ^ n) * μ (Metric.ball 0 1) := by
    have hsum :
        ∑ x ∈ s, μ (Metric.ball (x.1 : E) δ) =
          (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1) := by
      calc
        ∑ x ∈ s, μ (Metric.ball (x.1 : E) δ)
            = ∑ x ∈ s, ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                simpa [E] using (μ.addHaar_ball_of_pos (x.1 : E) hδ_pos)
        _ = (s.card : ℝ≥0∞) * (ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball (0 : E) 1) := by
              rw [mul_assoc]
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) * μ (Metric.ball 0 1)
          = μ A := by
              rw [hA, measure_biUnion_finset hdisj fun _ _ => measurableSet_ball]
              exact hsum.symm
      _ ≤ μ (Metric.ball (0 : E) ρ) := measure_mono hA_subset
      _ = ENNReal.ofReal (ρ ^ n) * μ (Metric.ball 0 1) := by
            simpa [E] using (μ.addHaar_ball_of_pos (0 : E) hρ_pos)
  have hmeasure' : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ n) ≤ ENNReal.ofReal (ρ ^ n) := by
    exact
      (ENNReal.mul_le_mul_iff_left
        (measure_ball_pos (μ := μ) (0 : E) zero_lt_one).ne'
        measure_ball_lt_top.ne).1 hmeasure
  have hmeasure_real : (s.card : ℝ) * δ ^ n ≤ ρ ^ n := by
    have hδpow_nonneg : 0 ≤ δ ^ n := by positivity
    have hmeasure_real' :
        ENNReal.ofReal ((s.card : ℝ) * δ ^ n) ≤ ENNReal.ofReal (ρ ^ n) := by
      simpa [ENNReal.ofReal_mul, hδpow_nonneg, mul_comm, mul_left_comm, mul_assoc] using hmeasure'
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hρ_pos.le n)).1 hmeasure_real'
  have hratio :
      (s.card : ℝ) ≤ (ρ / δ) ^ n := by
    have hδpow_pos : 0 < δ ^ n := pow_pos hδ_pos n
    have hratio' : (s.card : ℝ) ≤ ρ ^ n / δ ^ n := by
      exact (le_div_iff₀ hδpow_pos).2
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmeasure_real)
    simpa [div_pow] using hratio'
  have hratio_le : ρ / δ ≤ 5 / ε := by
    have hcalc : ρ / δ = (4 + ε) / ε := by
      field_simp [ρ, δ, hε0.ne']
      ring
    rw [hcalc]
    have hnum : 4 + ε ≤ 5 := by linarith
    exact div_le_div_of_nonneg_right hnum hε0.le
  have hratio_nonneg : 0 ≤ ρ / δ := by positivity
  exact hratio.trans (pow_le_pow_left₀ hratio_nonneg hratio_le n)

/-- Existence of finite angular `ε`-nets on the unit sphere with cardinality bounded by
`(5 / ε)^n`. -/
private theorem exists_finset_card_le_and_angle_cover
    (n : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset (SpherePoint n),
      (∀ u : SpherePoint n, ∃ v ∈ N, InnerProductGeometry.angle u.1 v.1 ≤ ε) ∧
      (N.card : ℝ) ≤ (5 / ε) ^ n := by
  let r : ℝ≥0 := ⟨ε / 4, by positivity⟩
  have hr_ne : r ≠ 0 := by
    have hr_pos : (0 : ℝ≥0) < r := by
      change (0 : ℝ) < ε / 4
      positivity
    exact ne_of_gt hr_pos
  obtain ⟨C, -, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (ε := r)
      (s := (Set.univ : Set (SpherePoint n))) hr_ne isCompact_univ
  have hExt_ne_top :
      Metric.externalCoveringNumber r (Set.univ : Set (SpherePoint n)) ≠ ⊤ := by
    refine ne_of_lt <| lt_of_le_of_lt hCcover.externalCoveringNumber_le_encard ?_
    exact hCfin.encard_lt_top
  have hPack_ne_top :
      Metric.packingNumber (2 * r) (Set.univ : Set (SpherePoint n)) ≠ ⊤ := by
    refine ne_of_lt <| lt_of_le_of_lt
      (Metric.packingNumber_two_mul_le_externalCoveringNumber r (Set.univ : Set (SpherePoint n))) ?_
    exact hExt_ne_top.lt_top
  let S := Metric.maximalSeparatedSet (2 * r) (Set.univ : Set (SpherePoint n))
  have hSfin : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [Metric.encard_maximalSeparatedSet (A := (Set.univ : Set (SpherePoint n))) hPack_ne_top]
    exact hPack_ne_top.lt_top
  let N : Finset (SpherePoint n) := hSfin.toFinset
  refine ⟨N, ?_, ?_⟩
  · intro u
    obtain ⟨v, hvS, hvdist⟩ :=
      Metric.isCover_maximalSeparatedSet (ε := 2 * r) (A := (Set.univ : Set (SpherePoint n)))
        hPack_ne_top (by simp : u ∈ (Set.univ : Set (SpherePoint n)))
    refine ⟨v, hSfin.mem_toFinset.mpr hvS, ?_⟩
    have hvdist' : dist u v ≤ (2 * r : ℝ) := by
      rw [dist_edist]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using hvdist)
    have hvdist'' : dist u v ≤ ε / 2 := by
      have htwo : (2 * r : ℝ) = ε / 2 := by
        change 2 * (ε / 4) = ε / 2
        ring
      simpa [htwo] using hvdist'
    exact angle_le_of_dist_le_half_eps hε0 hε1 hvdist''
  · have hsep :
        ∀ u ∈ N, ∀ v ∈ N, u ≠ v → ε / 2 < dist u v := by
      intro u hu v hv huv
      have huS : u ∈ S := hSfin.mem_toFinset.mp hu
      have hvS : v ∈ S := hSfin.mem_toFinset.mp hv
      have hsep' :=
        Metric.isSeparated_maximalSeparatedSet
          (ε := 2 * r) (A := (Set.univ : Set (SpherePoint n))) huS hvS huv
      have : ENNReal.ofReal (ε / 2) < edist u v := by
        have hcoe : ((2 * r : ℝ≥0) : ℝ) = ε / 2 := by
          change 2 * (ε / 4) = ε / 2
          ring
        have htwo : ENNReal.ofReal (ε / 2) = (2 * r : ℝ≥0∞) := by
          rw [← hcoe, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]
          norm_num
        simpa [htwo] using hsep'
      have this' : ENNReal.ofReal (ε / 2) < ENNReal.ofReal (dist u v) := by
        simpa [edist_dist] using this
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 this'
    simpa [N] using spherePoint_finset_card_le_of_separated N hε0 hε1 hsep



/-! ### Finite angular covers -/

/-- A finite set of centers whose spherical caps of angular radius `theta` cover
the whole unit sphere in `ℝ^n`. -/
private def SphericalCapCover (n : ℕ) (theta : ℝ) (C : Finset (SpherePoint n)) : Prop :=
  ∀ u : SpherePoint n, ∃ c ∈ C, InnerProductGeometry.angle u.1 c.1 ≤ theta


/-- A finite cap cover has total cap measure at least one. -/
private theorem one_le_card_mul_capMeasure_of_sphericalCapCover
    {n : ℕ} (hn : 2 ≤ n) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi2 : theta ≤ Real.pi / 2)
    {C : Finset (SpherePoint n)} (hC : SphericalCapCover n theta C) :
    1 ≤ (C.card : ℝ) * capMeasure n theta := by
  have hn0 : 0 < n := by omega
  let μ : ProbabilityMeasure (SpherePoint n) := sphereProbabilityMeasure n hn0
  have hsubset :
      (Set.univ : Set (SpherePoint n)) ⊆ ⋃ c ∈ C, capAround c theta := by
    intro u _
    rcases hC u with ⟨c, hc, huc⟩
    exact mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨hc, huc⟩⟩
  calc
    1 = ((μ : Measure (SpherePoint n)).real Set.univ) := by
          simp [Measure.real_def, μ]
    _ ≤ ((μ : Measure (SpherePoint n)).real (⋃ c ∈ C, capAround c theta)) := by
          exact MeasureTheory.measureReal_mono hsubset
            (measure_ne_top (μ := (μ : Measure (SpherePoint n))) _)
    _ ≤ ∑ c ∈ C, ((μ : Measure (SpherePoint n)).real (capAround c theta)) := by
          simpa using
            MeasureTheory.measureReal_biUnion_finset_le
              (μ := (μ : Measure (SpherePoint n))) C (fun c => capAround c theta)
    _ = ∑ c ∈ C, capMeasure n theta := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          exact sphereProbabilityMeasure_real_capAround_eq_capMeasure hn c htheta0 htheta_pi2
    _ = (C.card : ℝ) * capMeasure n theta := by
          simp [Finset.sum_const, nsmul_eq_mul]


/-! ### The random covering argument -/



private theorem capMeasure_le_one
    (n : ℕ) (hn : 2 ≤ n) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    capMeasure n a ≤ 1 := by
  have hn0 : 0 < n := by omega
  calc
    capMeasure n a
      = ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real (capAround v a)) := by
          symm
          exact sphereProbabilityMeasure_real_capAround_eq_capMeasure hn v ha0 hapi
    _ ≤ ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real Set.univ) := by
          exact MeasureTheory.measureReal_mono (by simp)
    _ = 1 := by simp [Measure.real_def]

private theorem badEvent_real_eq_pow
    {n M : ℕ} (hn : 2 ≤ n) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    let μ := sphereProbabilityMeasure n (show 0 < n by omega)
    let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) :=
      ProbabilityMeasure.pi (fun _ : Fin M => μ)
    let bad : Set (Fin M → SpherePoint n) := Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
    ((Ωμ : Measure (Fin M → SpherePoint n)).real bad) = (1 - capMeasure n a) ^ M := by
  have hn0 : 0 < n := by omega
  let μ := sphereProbabilityMeasure n hn0
  let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) := ProbabilityMeasure.pi (fun _ : Fin M => μ)
  let bad : Set (Fin M → SpherePoint n) := Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
  have hfactor :
      ((μ : Measure (SpherePoint n)).real ((capAround v a)ᶜ)) = 1 - capMeasure n a := by
    rw [MeasureTheory.probReal_compl_eq_one_sub
      (μ := (μ : Measure (SpherePoint n))) (measurableSet_capAround v ha0 hapi)]
    rw [sphereProbabilityMeasure_real_capAround_eq_capMeasure hn v ha0 hapi]
  have hpi :
      Ωμ bad = ∏ i : Fin M, μ ((capAround v a)ᶜ) := by
    exact (ProbabilityMeasure.pi_pi (μ := fun _ : Fin M => μ)
      (s := fun _ : Fin M => (capAround v a)ᶜ))
  calc
    ((Ωμ : Measure (Fin M → SpherePoint n)).real bad)
      = (Ωμ bad : ℝ) := by simp
    _ = ((∏ i : Fin M, μ ((capAround v a)ᶜ)) : ℝ) := by
          simpa using congrArg (fun t : ℝ≥0 => (t : ℝ)) hpi
    _ = ∏ i : Fin M, (μ ((capAround v a)ᶜ) : ℝ) := by
          simp
    _ = ∏ i : Fin M, ((μ : Measure (SpherePoint n)).real ((capAround v a)ᶜ)) := by
          simp
    _ = (1 - capMeasure n a) ^ M := by
          have hfactor' :
              ((μ : Measure (SpherePoint n)).real ((capAround v a)ᶜ))
                = 1 - capMeasure n a := hfactor
          simpa [Finset.prod_const] using congrArg (fun x : ℝ => x ^ M) hfactor'

private theorem badEvent_real_le_exp_neg
    {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M) (v : SpherePoint n) {a : ℝ}
    (ha0 : 0 ≤ a) (hapi : a ≤ Real.pi / 2) :
    let μ := sphereProbabilityMeasure n (show 0 < n by omega)
    let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) :=
      ProbabilityMeasure.pi (fun _ : Fin M => μ)
    let bad : Set (Fin M → SpherePoint n) := Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
    ((Ωμ : Measure (Fin M → SpherePoint n)).real bad) ≤
      Real.exp (-(M : ℝ) * capMeasure n a) := by
  have hp_nonneg : 0 ≤ capMeasure n a := by
    have hn0 : 0 < n := by omega
    calc
      0 ≤ ((sphereProbabilityMeasure n hn0 : Measure (SpherePoint n)).real (capAround v a)) := by
            positivity
      _ = capMeasure n a := by
            exact sphereProbabilityMeasure_real_capAround_eq_capMeasure hn v ha0 hapi
  have hp_le_one : capMeasure n a ≤ 1 := capMeasure_le_one n hn v ha0 hapi
  have hpow :
      (1 - capMeasure n a) ^ M ≤ Real.exp (-(M : ℝ) * capMeasure n a) := by
    have ht : capMeasure n a * M ≤ M := by
      have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
      nlinarith
    have hM0 : (M : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hM
    calc
      (1 - capMeasure n a) ^ M
        = (1 - (capMeasure n a * M) / M) ^ M := by
            congr 1
            field_simp [hM0]
      _ ≤ Real.exp (-(capMeasure n a * M)) :=
            Real.one_sub_div_pow_le_exp_neg (n := M) (t := capMeasure n a * M) ht
      _ = Real.exp (-(M : ℝ) * capMeasure n a) := by ring_nf
  simpa using (badEvent_real_eq_pow (n := n) (M := M) hn v ha0 hapi).trans_le hpow

private theorem eventually_pow_mul_exp_neg_pow_lt_one
    {A c γ : ℝ} (hA : 1 < A) (hc : 0 < c) (hγ : 1 < γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → A ^ n * Real.exp (-c * γ ^ n) < 1 := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hdiv_tendsto :
      Tendsto (fun n : ℕ => (n : ℝ) / γ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 hγ)
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (n : ℝ) / γ ^ n < c / Real.log A := by
    exact hdiv_tendsto.eventually (gt_mem_nhds (show 0 < c / Real.log A by positivity))
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hratio : (n : ℝ) / γ ^ n < c / Real.log A := hN n hn
  have hγpow_pos : 0 < γ ^ n := pow_pos (lt_trans zero_lt_one hγ) n
  have hn_lt : (n : ℝ) < (c / Real.log A) * γ ^ n := by
    exact (div_lt_iff₀ hγpow_pos).1 hratio
  have hnlog_lt :
      (n : ℝ) * Real.log A < c * γ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hn_lt hlogA
    have hright :
        ((c / Real.log A) * γ ^ n) * Real.log A = c * γ ^ n := by
      field_simp [hlogA.ne']
    rwa [hright] at hmul
  have hexponent_lt : (n : ℝ) * Real.log A - c * γ ^ n < 0 := by
    linarith
  have hAexp : A ^ n = Real.exp ((n : ℝ) * Real.log A) := by
    calc
      A ^ n = (Real.exp (Real.log A)) ^ n := by rw [Real.exp_log (lt_trans zero_lt_one hA)]
      _ = Real.exp ((n : ℝ) * Real.log A) := by rw [← Real.exp_nat_mul]
  calc
    A ^ n * Real.exp (-c * γ ^ n)
      = Real.exp ((n : ℝ) * Real.log A) * Real.exp (-c * γ ^ n) := by rw [hAexp]
    _ = Real.exp ((n : ℝ) * Real.log A + -(c * γ ^ n)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = Real.exp ((n : ℝ) * Real.log A - c * γ ^ n) := by rw [sub_eq_add_neg]
    _ < 1 := by exact Real.exp_lt_one_iff.mpr hexponent_lt

/-- For `q > 1`, `n ≤ q ^ n` eventually. Used to absorb the polynomial factor in the
cap-measure lower bound into an arbitrarily small loss in the exponential rate. -/
private theorem eventually_nat_le_pow {q : ℝ} (hq : 1 < q) :
    ∃ N : ℕ, ∀ n, N ≤ n → (n : ℝ) ≤ q ^ n := by
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) / q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 hq)
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) / q ^ n < 1 :=
    hdiv.eventually (gt_mem_nhds one_pos)
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hqpow : 0 < q ^ n := pow_pos (by linarith) n
  exact le_of_lt ((div_lt_one hqpow).1 (hN n hn))

/-- Random-covering upper bound (Wyner's Theorem 2 and its corollary): if
`1 < lam * sin theta`, then for all large `n` some set of at most `⌊lam ^ n⌋` points of
the sphere covers it with caps of angular radius `theta`. -/
private theorem eventual_sphericalCapCover_card_le_floor_of_mul_sin_gt_one
    {lam theta : ℝ}
    (hlam1 : 1 < lam)
    (htheta0 : 0 < theta)
    (htheta_pi2 : theta < Real.pi / 2)
    (hmul : 1 < lam * Real.sin theta) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n, N ≤ n →
      ∃ C : Finset (SpherePoint n),
        C.card ≤ ⌊lam ^ n⌋₊ ∧ SphericalCapCover n theta C := by
  let f : ℝ → ℝ := fun t => lam * Real.sin (theta - t)
  have hfcont : Continuous f := by
    fun_prop
  have hnhds : {t : ℝ | 1 < f t} ∈ 𝓝 (0 : ℝ) := by
    apply (isOpen_lt continuous_const hfcont).mem_nhds
    simpa [f] using hmul
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr_pos, hr_sub⟩
  let η : ℝ := min (r / 2) (theta / 2)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_lt_theta : η < theta := by
    have : η ≤ theta / 2 := by
      dsimp [η]
      exact min_le_right _ _
    linarith
  have hη_mem : η ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hη_pos.le]
    dsimp [η]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hmargin : 1 < lam * Real.sin (theta - η) := by
    exact hr_sub hη_mem
  let ε : ℝ := η / 2
  let a : ℝ := theta - ε
  let γ : ℝ := lam * Real.sin (a - ε)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt_theta : ε < theta := by
    dsimp [ε]
    linarith
  have hε_le_one : ε ≤ 1 := by
    have : ε < 1 := by
      dsimp [ε]
      linarith [hη_lt_theta, htheta_pi2, Real.pi_lt_four]
    linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_pi2 : a < Real.pi / 2 := by
    dsimp [a]
    linarith
  have hε_lt_a : ε < a := by
    dsimp [a, ε]
    linarith
  have hgamma : 1 < γ := by
    have hrewrite : a - ε = theta - η := by
      dsimp [a, ε]
      ring
    simpa [γ, hrewrite] using hmargin
  have hA : 1 < 5 / ε := by
    have hfive : ε < 5 := by linarith
    exact (one_lt_div hε_pos).2 hfive
  have hsin_a_pos : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi ha_pos (by linarith [Real.pi_pos])
  have hcos_a_pos : 0 < Real.cos a :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha_pi2⟩
  -- `K` replaces the constant `ε / (2π)` of the cap-measure lower bound
  set K : ℝ := Real.cos a / (4 * Real.sin a) with hKdef
  have hK_pos : 0 < K := by
    rw [hKdef]; positivity
  -- the ambient rate `γ₀ = lam * sin a` strictly exceeds the working rate `γ`
  have hgamma0 : γ < lam * Real.sin a := by
    have hmono : Real.sin (a - ε) < Real.sin a :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos]) (by linarith) (by linarith)
    have : lam * Real.sin (a - ε) < lam * Real.sin a :=
      mul_lt_mul_of_pos_left hmono (by linarith)
    simpa [γ] using this
  have hgamma_pos : 0 < γ := by linarith
  obtain ⟨Nratio, hNratio⟩ :=
    eventually_nat_le_pow (q := (lam * Real.sin a) / γ)
      ((one_lt_div hgamma_pos).2 hgamma0)
  have hd : 0 < K := hK_pos
  obtain ⟨Nexp, hNexp⟩ :=
    eventually_pow_mul_exp_neg_pow_lt_one hA hd hgamma
  have hpow_lam : Tendsto (fun n : ℕ => lam ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlam1
  have hlarge :
      ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ lam ^ n := hpow_lam.eventually_ge_atTop 2
  rcases Filter.eventually_atTop.1 hlarge with ⟨Nfloor, hNfloor⟩
  refine ⟨max (max (max Nexp Nfloor) Nratio) 2, by omega, ?_⟩
  intro n hn
  have hn_exp : Nexp ≤ n := by omega
  have hn_floor : Nfloor ≤ n := by omega
  have hn_ratio : Nratio ≤ n := by omega
  have hn_two : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  let Nnet : Finset (SpherePoint n) :=
    Classical.choose (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)
  have hNnet_cover :
      ∀ u : SpherePoint n, ∃ v ∈ Nnet, InnerProductGeometry.angle u.1 v.1 ≤ ε := by
    exact (Classical.choose_spec (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)).1
  have hNnet_card : (Nnet.card : ℝ) ≤ (5 / ε) ^ n := by
    exact (Classical.choose_spec (exists_finset_card_le_and_angle_cover n hε_pos hε_le_one)).2
  let M : ℕ := ⌊lam ^ n⌋₊
  have hpow_ge_two : (2 : ℝ) ≤ lam ^ n := hNfloor n hn_floor
  have hM_half : lam ^ n / 2 ≤ (M : ℝ) := by
    have hfloor : lam ^ n - 1 < (M : ℝ) := by
      exact Nat.sub_one_lt_floor (a := lam ^ n)
    nlinarith
  have hM_pos : 0 < M := by
    have : (0 : ℝ) < (M : ℝ) := by
      nlinarith [hM_half, hpow_ge_two]
    exact_mod_cast this
  let μn : ProbabilityMeasure (SpherePoint n) := sphereProbabilityMeasure n hn0
  let Ωμ : ProbabilityMeasure (Fin M → SpherePoint n) := ProbabilityMeasure.pi (fun _ : Fin M => μn)
  let bad : SpherePoint n → Set (Fin M → SpherePoint n) :=
    fun v => Set.pi Set.univ (fun _ : Fin M => (capAround v a)ᶜ)
  let badUnion : Set (Fin M → SpherePoint n) := ⋃ v ∈ Nnet, bad v
  have hcap_lb :
      Real.sin a ^ (n - 1) * Real.cos a / (2 * (n : ℝ)) ≤ capMeasure n a :=
    capMeasure_ge hn_two ha_pos ha_pi2
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hgpow : (0 : ℝ) < γ ^ n := pow_pos hgamma_pos n
  have hkey : (n : ℝ) * γ ^ n ≤ (lam * Real.sin a) ^ n := by
    have h := hNratio n hn_ratio
    rw [div_pow, le_div_iff₀ hgpow] at h
    linarith
  have hsinpow : Real.sin a ^ (n - 1) * Real.sin a = Real.sin a ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hMcap :
      K * γ ^ n ≤ (M : ℝ) * capMeasure n a := by
    have hstep1 : K * γ ^ n
        ≤ (lam ^ n / 2) * (Real.sin a ^ (n - 1) * Real.cos a / (2 * (n : ℝ))) := by
      have hL : K * γ ^ n = (Real.cos a * γ ^ n) / (4 * Real.sin a) := by
        rw [hKdef]; ring
      have hR : (lam ^ n / 2) * (Real.sin a ^ (n - 1) * Real.cos a / (2 * (n : ℝ)))
          = (Real.cos a * (lam * Real.sin a) ^ n) / (4 * (n : ℝ) * Real.sin a) := by
        rw [mul_pow, ← hsinpow]
        field_simp
        ring
      rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hkey
        (show (0 : ℝ) ≤ 4 * Real.cos a * Real.sin a by positivity)]
    calc K * γ ^ n
        ≤ (lam ^ n / 2) * (Real.sin a ^ (n - 1) * Real.cos a / (2 * (n : ℝ))) := hstep1
      _ ≤ (M : ℝ) * (Real.sin a ^ (n - 1) * Real.cos a / (2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hM_half (by positivity)
      _ ≤ (M : ℝ) * capMeasure n a :=
          mul_le_mul_of_nonneg_left hcap_lb (by positivity)
  have hbad_each :
      ∀ v : SpherePoint n,
        ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) ≤
          Real.exp (-K * γ ^ n) := by
    intro v
    have hbad0 :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) ≤
          Real.exp (-(M : ℝ) * capMeasure n a) := by
      simpa [Ωμ, bad] using
        badEvent_real_le_exp_neg (n := n) (M := M) hn_two hM_pos v ha_pos.le ha_pi2.le
    refine le_trans hbad0 ?_
    have hexp_arg :
        -(M : ℝ) * capMeasure n a ≤ -K * γ ^ n := by
      linarith
    exact Real.exp_le_exp.mpr hexp_arg
  have hunion :
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) ≤
        (Nnet.card : ℝ) * Real.exp (-K * γ ^ n) := by
    calc
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion)
        ≤ ∑ v ∈ Nnet, ((Ωμ : Measure (Fin M → SpherePoint n)).real (bad v)) := by
            simpa [badUnion] using
              MeasureTheory.measureReal_biUnion_finset_le
                (μ := (Ωμ : Measure (Fin M → SpherePoint n))) Nnet bad
      _ ≤ ∑ v ∈ Nnet, Real.exp (-K * γ ^ n) := by
            exact Finset.sum_le_sum (fun v hv => hbad_each v)
      _ = (Nnet.card : ℝ) * Real.exp (-K * γ ^ n) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hbad_lt_one :
      ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) < 1 := by
    have hmul_le :
        (Nnet.card : ℝ) * Real.exp (-K * γ ^ n) ≤
          (5 / ε) ^ n * Real.exp (-K * γ ^ n) := by
      exact mul_le_mul_of_nonneg_right hNnet_card (by positivity)
    exact lt_of_le_of_lt (le_trans hunion hmul_le) (by simpa [γ] using hNexp n hn_exp)
  have hnotall : ¬ ∀ ω : Fin M → SpherePoint n, ω ∈ badUnion := by
    intro hall
    have hEq : badUnion = Set.univ := Set.eq_univ_iff_forall.mpr hall
    have hreal_univ :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real Set.univ) = 1 := by
      simp [Measure.real_def]
    have hbad_eq_one :
        ((Ωμ : Measure (Fin M → SpherePoint n)).real badUnion) = 1 := by
      rw [hEq]
      exact hreal_univ
    linarith
  rcases not_forall.mp hnotall with ⟨ω, hω⟩
  let C : Finset (SpherePoint n) := Finset.univ.image ω
  have hCcard : C.card ≤ M := by
    simpa [C] using (Finset.card_image_le (s := Finset.univ) (f := ω))
  have hnet_hit :
      ∀ v ∈ Nnet, ∃ i : Fin M, ω i ∈ capAround v a := by
    intro v hv
    have hnotbad : ω ∉ bad v := by
      intro hbad
      exact hω <| by
        exact mem_iUnion.2 ⟨v, mem_iUnion.2 ⟨hv, hbad⟩⟩
    have hnotforall : ¬ ∀ i : Fin M, ω i ∈ (capAround v a)ᶜ := by
      simpa [bad, Set.mem_pi, Set.mem_univ] using hnotbad
    push Not at hnotforall
    simpa using hnotforall
  have hcover : SphericalCapCover n theta C := by
    intro u
    rcases hNnet_cover u with ⟨v, hv, huv⟩
    rcases hnet_hit v hv with ⟨i, hi⟩
    have hci : ω i ∈ C := by
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    have hvu : InnerProductGeometry.angle v.1 (ω i).1 ≤ a := by
      simpa [InnerProductGeometry.angle_comm] using hi
    have huc : InnerProductGeometry.angle u.1 (ω i).1 ≤ theta := by
      calc
        InnerProductGeometry.angle u.1 (ω i).1
          ≤ InnerProductGeometry.angle u.1 v.1 + InnerProductGeometry.angle v.1 (ω i).1 := by
              exact InnerProductGeometry.angle_le_angle_add_angle u.1 v.1 (ω i).1
        _ ≤ ε + a := by gcongr
        _ = theta := by
              dsimp [a]
              ring
    exact ⟨ω i, hci, huc⟩
  exact ⟨C, hCcard, hcover⟩


/-! ### The covering number in Mathlib's vocabulary -/

section Bridge

variable {n : ℕ} {θ : ℝ}

/-- The chordal radius corresponding to angular radius `θ`, as an `ℝ≥0`. -/
private theorem coe_capRadius (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    ((Real.toNNReal (2 * Real.sin (θ / 2)) : ℝ≥0) : ℝ) = 2 * Real.sin (θ / 2) := by
  refine Real.coe_toNNReal _ ?_
  have : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

/-- Mathlib's `IsCover` on the unit sphere, at chordal radius `2 sin (θ/2)`, is exactly
the condition that every point lies within angle `θ` of a centre. -/
private theorem isCover_iff_angle (h0 : 0 ≤ θ) (hpi : θ ≤ π) (C : Set (SpherePoint n)) :
    Metric.IsCover (Real.toNNReal (2 * Real.sin (θ / 2))) (Set.univ : Set (SpherePoint n)) C
      ↔ ∀ u : SpherePoint n, ∃ c ∈ C, InnerProductGeometry.angle u.1 c.1 ≤ θ := by
  have hrad_nonneg : (0 : ℝ) ≤ 2 * Real.sin (θ / 2) := by
    have : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    linarith
  have hedist : ∀ u c : SpherePoint n,
      edist u c ≤ (Real.toNNReal (2 * Real.sin (θ / 2)) : ℝ≥0∞)
        ↔ InnerProductGeometry.angle u.1 c.1 ≤ θ := by
    intro u c
    rw [edist_dist, ENNReal.coe_nnreal_eq, coe_capRadius h0 hpi,
      ENNReal.ofReal_le_ofReal_iff hrad_nonneg]
    rw [show dist u c = dist u.1 c.1 from rfl]
    exact (angle_le_iff_dist_le (norm_spherePoint' u) (norm_spherePoint' c) h0 hpi).symm
  constructor
  · intro hC u
    obtain ⟨c, hc, hdist⟩ := hC (Set.mem_univ u)
    exact ⟨c, hc, (hedist u c).1 hdist⟩
  · intro hC u _
    obtain ⟨c, hc, hangle⟩ := hC u
    exact ⟨c, hc, (hedist u c).2 hangle⟩

/-- A finite angular cover bounds the covering number. -/
private theorem coveringNumber_le_of_angle_cover (h0 : 0 ≤ θ) (hpi : θ ≤ π)
    {C : Finset (SpherePoint n)}
    (hC : ∀ u : SpherePoint n, ∃ c ∈ C, InnerProductGeometry.angle u.1 c.1 ≤ θ) :
    Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Set.univ : Set (SpherePoint n)) ≤ (C.card : ℕ∞) := by
  have hcov : Metric.IsCover (Real.toNNReal (2 * Real.sin (θ / 2)))
      (Set.univ : Set (SpherePoint n)) (C : Set (SpherePoint n)) := by
    refine (isCover_iff_angle h0 hpi _).2 ?_
    intro u
    obtain ⟨c, hc, hangle⟩ := hC u
    exact ⟨c, by simpa using hc, hangle⟩
  refine le_trans (hcov.coveringNumber_le_encard (Set.subset_univ _)) ?_
  rw [Set.encard_coe_eq_coe_finsetCard]

/-- The covering number of the sphere at positive angular radius is finite. -/
private theorem coveringNumber_ne_top (hθ0 : 0 < θ) (hθpi : θ ≤ π) :
    Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Set.univ : Set (SpherePoint n)) ≠ ⊤ := by
  obtain ⟨N, hNcover, -⟩ :=
    exists_finset_card_le_and_angle_cover n (ε := min θ 1)
      (lt_min hθ0 one_pos) (min_le_right _ _)
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top N.card) ?_
  refine coveringNumber_le_of_angle_cover hθ0.le hθpi ?_
  intro u
  obtain ⟨v, hv, huv⟩ := hNcover u
  exact ⟨v, hv, huv.trans (min_le_left _ _)⟩

/-- The covering number of the sphere in dimension at least one is positive. -/
private theorem coveringNumber_pos (hn : 1 ≤ n) (hθ0 : 0 < θ) (hθpi : θ ≤ π) :
    0 < (Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Set.univ : Set (SpherePoint n))).toNat := by
  have hne := coveringNumber_ne_top (n := n) (θ := θ) hθ0 hθpi
  have hnonempty : (Set.univ : Set (SpherePoint n)).Nonempty := by
    refine ⟨⟨e1Vec n, ?_⟩, Set.mem_univ _⟩
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_e1Vec (by omega)
  have hpos : 0 < Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
      (Set.univ : Set (SpherePoint n)) := Metric.coveringNumber_pos_iff.2 hnonempty
  exact ENat.toNat_pos hpos.ne' hne

/-- The elementary volume bound: a cover of the sphere by caps of angular radius `θ`
needs at least `1 / capMeasure n θ` of them. This is Wyner's Lemma 2. -/
private theorem one_le_coveringNumber_mul_capMeasure (hn : 2 ≤ n) (hθ0 : 0 < θ)
    (hθpi2 : θ ≤ π / 2) :
    1 ≤ ((Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
      (Set.univ : Set (SpherePoint n))).toNat : ℝ) * capMeasure n θ := by
  have hθpi : θ ≤ π := by linarith [Real.pi_pos]
  have hne := coveringNumber_ne_top (n := n) (θ := θ) hθ0 hθpi
  obtain ⟨C, hCsub, hCfin, hCcover, hCcard⟩ :=
    Metric.exists_set_encard_eq_coveringNumber (A := (Set.univ : Set (SpherePoint n))) hne
  have hangle : ∀ u : SpherePoint n, ∃ c ∈ hCfin.toFinset,
      InnerProductGeometry.angle u.1 c.1 ≤ θ := by
    intro u
    obtain ⟨c, hc, hangle⟩ := (isCover_iff_angle hθ0.le hθpi C).1 hCcover u
    exact ⟨c, hCfin.mem_toFinset.2 hc, hangle⟩
  have hcard : (hCfin.toFinset.card : ℕ∞)
      = Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
          (Set.univ : Set (SpherePoint n)) := by
    rw [← hCcard, ← Set.encard_coe_eq_coe_finsetCard]
    congr 1
    exact hCfin.coe_toFinset
  have hcardNat : hCfin.toFinset.card
      = (Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
          (Set.univ : Set (SpherePoint n))).toNat := by
    rw [← hcard]
    simp
  have := one_le_card_mul_capMeasure_of_sphericalCapCover (n := n) hn hθ0.le hθpi2
    (C := hCfin.toFinset) hangle
  rwa [hcardNat] at this

end Bridge


/-! ### The asymptotic covering exponent -/

section Asymptotics

variable {θ : ℝ}

/-- Abbreviation used in this section: the covering number of the unit sphere in `ℝ^n`
by closed chordal balls of radius `2 sin (θ/2)`, i.e. by caps of angular radius `θ`. -/
private def capCoveringNumber (n : ℕ) (θ : ℝ) : ℕ :=
  (Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
    (Set.univ : Set (SpherePoint n))).toNat

private theorem log_nat_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  refine (hreal.comp tendsto_natCast_atTop_atTop).congr ?_
  intro n
  simp

private theorem one_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
  refine (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr ?_
  intro n
  simp [one_div]

/-- The lower bound on `log N / n` supplied by the volume argument tends to the
covering exponent. -/
private theorem lowerBound_tendsto (θ : ℝ) :
    Tendsto
      (fun n : ℕ => -(Real.log n / (n : ℝ)) - (1 - 1 / (n : ℝ)) * Real.log (Real.sin θ))
      atTop (𝓝 (-Real.log (Real.sin θ))) := by
  have h1 := log_nat_div_nat_tendsto_zero
  have h2 := one_div_nat_tendsto_zero
  have := (h1.neg).sub (((tendsto_const_nhds (x := (1 : ℝ))).sub h2).mul
    (tendsto_const_nhds (x := Real.log (Real.sin θ))))
  simpa using this

/-- Volume lower bound on the covering number, in logarithmic form. -/
private theorem lowerBound_le_log_capCoveringNumber (hθ0 : 0 < θ) (hθ : θ < π / 2)
    {n : ℕ} (hn : 2 ≤ n) :
    -(Real.log n / (n : ℝ)) - (1 - 1 / (n : ℝ)) * Real.log (Real.sin θ)
      ≤ Real.log (capCoveringNumber n θ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hNpos : 0 < capCoveringNumber n θ :=
    coveringNumber_pos (by omega) hθ0 (by linarith [Real.pi_pos])
  have hNposR : (0 : ℝ) < (capCoveringNumber n θ : ℝ) := by exact_mod_cast hNpos
  have hvol : 1 ≤ ((capCoveringNumber n θ : ℕ) : ℝ) * capMeasure n θ :=
    one_le_coveringNumber_mul_capMeasure hn hθ0 (by linarith)
  have hcap : capMeasure n θ ≤ (n : ℝ) * Real.sin θ ^ (n - 1) :=
    capMeasure_le hn hθ0 hθ
  have hpow_pos : (0 : ℝ) < Real.sin θ ^ (n - 1) := pow_pos hsin_pos _
  have hprod : 1 ≤ (capCoveringNumber n θ : ℝ) * ((n : ℝ) * Real.sin θ ^ (n - 1)) :=
    hvol.trans (mul_le_mul_of_nonneg_left hcap hNposR.le)
  -- take logarithms
  have hlog : 0 ≤ Real.log ((capCoveringNumber n θ : ℝ) * ((n : ℝ) * Real.sin θ ^ (n - 1))) :=
    Real.log_nonneg hprod
  have hexpand :
      Real.log ((capCoveringNumber n θ : ℝ) * ((n : ℝ) * Real.sin θ ^ (n - 1)))
        = Real.log (capCoveringNumber n θ) + Real.log n
            + ((n : ℝ) - 1) * Real.log (Real.sin θ) := by
    rw [Real.log_mul hNposR.ne' (by positivity), Real.log_mul hnR.ne' hpow_pos.ne',
      Real.log_pow]
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [this]
    ring
  rw [hexpand] at hlog
  have hgoal : -(Real.log n / (n : ℝ)) - (1 - 1 / (n : ℝ)) * Real.log (Real.sin θ)
      = (-(Real.log n) - ((n : ℝ) - 1) * Real.log (Real.sin θ)) / (n : ℝ) := by
    field_simp
  rw [hgoal, div_le_div_iff_of_pos_right hnR]
  linarith [hlog]

/-- Random-covering upper bound on the covering number, in logarithmic form. -/
private theorem eventually_log_capCoveringNumber_le (hθ0 : 0 < θ) (hθ : θ < π / 2)
    {p : ℝ} (hp : -Real.log (Real.sin θ) < p) :
    ∀ᶠ n : ℕ in atTop, Real.log (capCoveringNumber n θ) / (n : ℝ) ≤ p := by
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hp_pos : 0 < p := by
    have hlog_neg : Real.log (Real.sin θ) < 0 := by
      refine Real.log_neg hsin_pos ?_
      have : Real.sin θ < Real.sin (π / 2) :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl hθ
      simpa using this
    linarith
  have hmul : 1 < Real.exp p * Real.sin θ := by
    have harg : 0 < p + Real.log (Real.sin θ) := by linarith
    calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ < Real.exp (p + Real.log (Real.sin θ)) := Real.exp_strictMono harg
      _ = Real.exp p * Real.sin θ := by rw [Real.exp_add, Real.exp_log hsin_pos]
  obtain ⟨N, hN2, hN⟩ :=
    eventual_sphericalCapCover_card_le_floor_of_mul_sin_gt_one
      (lam := Real.exp p) (theta := θ)
      (by simpa using Real.one_lt_exp_iff.2 hp_pos) hθ0 hθ hmul
  refine Filter.eventually_atTop.2 ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  obtain ⟨C, hCcard, hCcover⟩ := hN n hnN
  have hNle : capCoveringNumber n θ ≤ C.card := by
    have := coveringNumber_le_of_angle_cover (θ := θ) hθ0.le
      (by linarith [Real.pi_pos]) (C := C) hCcover
    unfold capCoveringNumber
    exact_mod_cast ENat.toNat_le_toNat this (by simp)
  have hNpos : 0 < capCoveringNumber n θ :=
    coveringNumber_pos (by omega) hθ0 (by linarith [Real.pi_pos])
  have hNposR : (0 : ℝ) < (capCoveringNumber n θ : ℝ) := by exact_mod_cast hNpos
  have hfloor : ((⌊Real.exp p ^ n⌋₊ : ℕ) : ℝ) ≤ Real.exp p ^ n :=
    Nat.floor_le (pow_nonneg (Real.exp_pos p).le n)
  have hle : (capCoveringNumber n θ : ℝ) ≤ Real.exp p ^ n := by
    refine le_trans ?_ hfloor
    exact_mod_cast le_trans hNle hCcard
  have hlog := Real.log_le_log hNposR hle
  rw [← Real.exp_nat_mul, Real.log_exp] at hlog
  rw [div_le_iff₀ hnR]
  linarith [hlog]

end Asymptotics


/-! ### Wyner's theorem -/

section Main

/-- The covering number of the sphere, computed inside the sphere as a metric space in
its own right, agrees with the covering number of the sphere as a subset of `ℝ^n`. -/
private theorem coveringNumber_sphere_eq (n : ℕ) (ε : ℝ≥0) :
    Metric.coveringNumber ε (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      = Metric.coveringNumber ε (Set.univ : Set (SpherePoint n)) := by
  have h := (isometry_subtype_coe
      (s := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).coveringNumber_image
      (ε := ε) (A := (Set.univ : Set (SpherePoint n)))
  rwa [Set.image_univ, Subtype.range_coe] at h

/-- **Wyner's covering theorem.** For a fixed angular radius `θ ∈ (0, π/2)`, the minimum
number of spherical caps of angular radius `θ`, *centred at points of the unit sphere of
`ℝⁿ`*, whose union is that whole sphere grows like `exp (n · (-log sin θ))`: its logarithm,
divided by `n`, converges to `-log sin θ`.

A cap of angular radius `θ` about a centre `c` on the sphere is exactly the closed ball of
chordal radius `2 sin (θ/2)` about `c` (`angle_le_iff_dist_le`), so the covering number is
Mathlib's `Metric.coveringNumber` at that radius.

Two features of the statement that are easy to misread, both discussed at more length in
the module docstring:

* `Metric.coveringNumber` is the *internal* covering number — the centres are required to
  lie on the sphere, which is what Wyner requires. This is load-bearing, not incidental:
  the result is false for `Metric.externalCoveringNumber`, since at `θ = π/3` the chordal
  radius is `1` and the single ball of radius `1` about the origin already contains the
  whole sphere.
* The caps here are closed, `angle u c ≤ θ`, whereas Wyner's are open, `angle u c < θ`.
  The exponent is the same either way, but the two covering numbers are not literally
  equal, and it is the closed one that is formalised. -/
theorem tendsto_log_coveringNumber_sphere_div_atTop
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < π / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
            (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toNat : ℝ) / (n : ℝ))
      atTop (𝓝 (-Real.log (Real.sin θ))) := by
  have hcongr : ∀ n : ℕ,
      Real.log ((Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toNat : ℝ) / (n : ℝ)
        = Real.log (capCoveringNumber n θ) / (n : ℝ) := by
    intro n
    rw [coveringNumber_sphere_eq n]
    rfl
  refine (Filter.Tendsto.congr (fun n => (hcongr n).symm) ?_)
  -- the squeeze between the volume lower bound and the random-covering upper bound
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hlow_event :
      ∀ᶠ n : ℕ in atTop,
        -Real.log (Real.sin θ) - ε / 2
          ≤ -(Real.log n / (n : ℝ)) - (1 - 1 / (n : ℝ)) * Real.log (Real.sin θ) :=
    (lowerBound_tendsto θ).eventually
      (Ici_mem_nhds (by linarith : -Real.log (Real.sin θ) - ε / 2 < -Real.log (Real.sin θ)))
  have hlow_bound :
      ∀ᶠ n : ℕ in atTop,
        -(Real.log n / (n : ℝ)) - (1 - 1 / (n : ℝ)) * Real.log (Real.sin θ)
          ≤ Real.log (capCoveringNumber n θ) / (n : ℝ) :=
    Filter.eventually_atTop.2 ⟨2, fun n hn => lowerBound_le_log_capCoveringNumber hθ0 hθ hn⟩
  have hup_event :=
    eventually_log_capCoveringNumber_le hθ0 hθ
      (p := -Real.log (Real.sin θ) + ε / 2) (by linarith)
  have hfinal : ∀ᶠ n : ℕ in atTop,
      dist (Real.log (capCoveringNumber n θ) / (n : ℝ)) (-Real.log (Real.sin θ)) < ε := by
    filter_upwards [hlow_event, hlow_bound, hup_event] with n h1 h2 h3
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  exact Filter.eventually_atTop.1 hfinal

/-- The covering number appearing above is finite, so the `ENat.toNat` in its statement
is not a junk value. -/
theorem coveringNumber_sphere_ne_top (n : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ ≤ π) :
    Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := by
  rw [coveringNumber_sphere_eq n]
  exact coveringNumber_ne_top hθ0 hθpi

/-- ... and it is nonzero in every dimension `n ≥ 1`, so its logarithm is not a junk value
either. The hypothesis `1 ≤ n` cannot be dropped: the sphere of `ℝ⁰` is empty, so its
covering number is `0` at every radius. -/
theorem coveringNumber_sphere_pos {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ0 : 0 < θ)
    (hθpi : θ ≤ π) :
    0 < (Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toNat := by
  rw [coveringNumber_sphere_eq n]
  exact coveringNumber_pos hn hθ0 hθpi

end Main

/-! ## Sanity checks

Guards against the ways a correct proof can still accompany a useless statement. These are
`example`s: elaborated by the build, so one that stops holding breaks it, and exporting no
names. They are *not* reached by the axiom audit, which walks the named declarations a
module contributes to the environment, and an `example` contributes none. What covers them
instead is the textual escape-hatch scan in `scripts/check-conventions.sh`, which reads the
file rather than the environment.
-/

section Sanity

-- REQUIRED. The hypotheses `0 < θ` and `θ < π/2` are simultaneously satisfiable, so the
-- theorem is not vacuous. There are no universally quantified hypotheses to satisfy.
example : ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 :=
  ⟨π / 4, by positivity, by linarith [Real.pi_pos]⟩

-- REQUIRED. The radius appearing in the statement is the intended chordal radius and not a
-- `Real.toNNReal` truncation to zero: caps of angular radius `π/3` are exactly the closed
-- balls of radius `1`. This is the step where the statement would most easily drift from
-- its intent, since it is the only place the angle is translated into a metric radius.
example : ((Real.toNNReal (2 * Real.sin ((π / 3) / 2)) : ℝ≥0) : ℝ) = 1 := by
  rw [show (π / 3) / 2 = π / 6 by ring, Real.sin_pi_div_six]
  norm_num

-- ... and that radius really does mean what the informal statement says it means. The
-- example above only checks the arithmetic `2 sin (π/6) = 1`; this one closes the loop, at
-- the same angular radius `π/3`, between "within angle `θ` of `c`" and "in the closed ball
-- of radius `2 sin (θ/2)` about `c`", which is what `Metric.coveringNumber` counts.
-- `angle_le_iff_dist_le` is the only bridge between the two notions in this file.
example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u c : V}
    (hu : ‖u‖ = 1) (hc : ‖c‖ = 1) :
    InnerProductGeometry.angle u c ≤ π / 3 ↔ dist u c ≤ 1 := by
  rw [angle_le_iff_dist_le hu hc (by positivity) (by linarith [Real.pi_pos]),
    show (π / 3) / 2 = π / 6 by ring, Real.sin_pi_div_six]
  norm_num

-- REQUIRED. The hypotheses of the two exported chord lemmas are simultaneously satisfiable
-- — they are vacuous when `V` is the zero space, where there are no unit vectors — and are
-- satisfied by a concrete pair rather than only in the abstract: the first two standard
-- basis vectors of `ℝ²` are unit vectors at angle `π/2`, with `0 ≤ π/2 ≤ π`. The final
-- conjunct pins the chord formula itself at that pair, `dist = √2 = 2 sin (π/4)`.
example :
    ∃ (x y : EuclideanSpace ℝ (Fin 2)) (θ : ℝ),
      ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ 0 ≤ θ ∧ θ ≤ π ∧
        InnerProductGeometry.angle x y = θ ∧ dist x y = 2 * Real.sin (θ / 2) := by
  have hx : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ = 1 := by simp
  have hy : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ = 1 := by simp
  have hangle : InnerProductGeometry.angle (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = π / 2 := by
    rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two,
      EuclideanSpace.inner_single_left]
    simp
  exact ⟨_, _, π / 2, hx, hy, by positivity, by linarith [Real.pi_pos], hangle,
    by rw [dist_eq_two_mul_sin_angle_div_two hx hy, hangle]⟩

-- The limit value is a recognisable number: at `θ = π/6` the exponent is `log 2`, i.e.
-- covering the sphere by caps of angular radius 30 degrees costs one bit per dimension.
example : -Real.log (Real.sin (π / 6)) = Real.log 2 := by
  rw [Real.sin_pi_div_six, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]

-- The exponent is strictly positive throughout the stated range, so the theorem really does
-- assert exponential growth rather than accidentally asserting a subexponential rate.
example {θ : ℝ} (h0 : 0 < θ) (h : θ < π / 2) : 0 < -Real.log (Real.sin θ) := by
  have hpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hlt : Real.sin θ < 1 := by
    have : Real.sin θ < Real.sin (π / 2) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl h
    simpa using this
  have := Real.log_neg hpos hlt
  linarith

-- The exponent genuinely depends on `θ`, so the statement is not a constant in disguise:
-- a larger cap needs fewer of them.
example : -Real.log (Real.sin (π / 3)) < -Real.log (Real.sin (π / 6)) := by
  have h3 : Real.sqrt 3 / 2 > (1 : ℝ) / 2 := by
    have : (1 : ℝ) < Real.sqrt 3 := by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith [Real.sqrt_nonneg 3]
    linarith
  rw [Real.sin_pi_div_six, Real.sin_pi_div_three]
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 2) h3
  linarith

-- The object being measured is non-degenerate at a concrete dimension and angle: the
-- covering number is finite (so `ENat.toNat` is not its junk value `0`) and nonzero (so
-- `Real.log` is not applied to `0`).
example :
    Metric.coveringNumber (Real.toNNReal (2 * Real.sin ((π / 4) / 2)))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) ≠ ⊤ :=
  coveringNumber_sphere_ne_top 5 (by positivity) (by linarith [Real.pi_pos])

example :
    0 < (Metric.coveringNumber (Real.toNNReal (2 * Real.sin ((π / 4) / 2)))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)).toNat :=
  coveringNumber_sphere_pos (by norm_num) (by positivity) (by linarith [Real.pi_pos])

end Sanity

end MiscMath.Geometry
