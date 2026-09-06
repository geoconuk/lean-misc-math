/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Wyner's spherical covering exponent — advertised statement

This is the statement surface of the submission: the declarations a mathematical reader is
asked to audit. The proofs are in `MiscMath.Geometry.SphereCoveringExponent`, which is the
Solution module of the accompanying Comparator configuration and is the file the library
actually ships. The `sorry`s below are the deliberate holes Comparator fills.

## Informal statement

Fix an angle `θ` with `0 < θ < π/2`, and for each `n` let `M(n, θ)` be the least number of
spherical caps of angular radius `θ`, centred at points of the unit sphere of `ℝⁿ`, whose
union is the whole sphere. Then

    lim_{n → ∞} (1/n) · log M(n, θ) = -log sin θ,

that is, `M(n, θ) = exp (n · (-log sin θ) · (1 + o(1)))`. The covering number grows
exponentially in the dimension, with exponent exactly `-log sin θ`.

The cap of angular radius `θ` about a point `c` of the unit sphere is the set of unit
vectors `u` with `angle u c ≤ θ`. For unit vectors `‖u - c‖ = 2 sin (angle u c / 2)`, so
that cap is precisely the closed ball of radius `2 sin (θ/2)` about `c`. The headline
statement therefore uses Mathlib's `Metric.coveringNumber` at radius `2 sin (θ/2)` on
`Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin n)`, and defines no covering number of its
own. `Metric.coveringNumber` requires the centres to lie in the set being covered, which
is also what Wyner requires.

`dist_eq_two_mul_sin_angle_div_two` and `angle_le_iff_dist_le` below are the bridge that
licenses that translation, and they are compared alongside the headline precisely so that
a reader need not take the identification of caps with chordal balls on trust.

## How to read the headline statement

Three things about `tendsto_log_coveringNumber_sphere_div_atTop` are easy to misread.

* **Junk values.** `Metric.coveringNumber` takes values in `ℕ∞`, and the statement applies
  `ENat.toNat`, whose junk value at `⊤` is `0`. `coveringNumber_sphere_ne_top` and
  `coveringNumber_sphere_pos` bound that: the covering number is finite for every `n`, and
  positive for every `n ≥ 1`, so from `n = 1` onwards neither `ENat.toNat` nor `Real.log`
  is applied to a junk argument. They are compared as part of this submission for that
  reason. `n = 0` is the exception and is genuinely degenerate: the sphere of `ℝ⁰` is
  empty, so the covering number is `0` at every radius and the summand collapses to
  `Real.log 0 / (0 : ℝ) = 0`, two junk conventions at once. A limit along `atTop` does not
  see it, but it is not excluded either.
* **Internal, not external, covering number.** The centres are required to lie on the
  sphere. This is load-bearing, not incidental: the result is false for
  `Metric.externalCoveringNumber`, since at `θ = π/3` the chordal radius is `1` and the
  single ball of radius `1` about the origin already contains the whole sphere.
* **The radius is not a truncation.** It is written `Real.toNNReal (2 * sin (θ/2))`. For
  `0 < θ < π/2` this is the honest value `2 sin (θ/2)` and not a truncation to `0`; at
  `θ = π/3` it is exactly `1`.

## Source

A. D. Wyner, *Random packings and coverings of the unit n-sphere*, Bell System Technical
Journal **46** (1967), 2111-2118.

The result stated here is the covering half of that paper: equations (2a) and (2b),
restated as a limit on p. 2116, `lim (1/n) log M_c(n, θ) = R_c(θ)` with
`R_c(θ) = -log sin θ` for `θ < π/2`. Both halves of Wyner's argument are reproduced in the
Solution — the elementary volume bound (Lemma 2, p. 2115) for the lower bound on the
covering number, and the random-covering argument (Theorem 2 and its corollary,
pp. 2115-2117) for the upper bound. The packing results of the same paper are not
formalised.

**Where this differs from the source.** Wyner defines a `θ`-covering with *open* caps,
`angle u c < θ` (p. 2112). Mathlib's `Metric.IsCover` is stated with closed balls, so what
is proved here concerns *closed* caps, `angle u c ≤ θ`. The exponent is unaffected — a
closed `θ`-cover is an open `θ'`-cover for every `θ' > θ`, and `-log sin` is continuous —
but the two covering numbers are not literally equal, and it is the closed one that is
formalised.

## Relation to Mathlib

Mathlib supplies the vocabulary but not the theorem. `Mathlib/Topology/MetricSpace/`
`CoveringNumbers.lean` defines `Metric.coveringNumber`, `Metric.externalCoveringNumber` and
`Metric.packingNumber` along with the elementary inequalities relating them, but contains no
asymptotics. Mathlib has no spherical cap measure and no metric-entropy estimate for any
family of sets, so nothing here is a duplicate.

Every statement below is in Mathlib's vocabulary and introduces no definition. The
auxiliary notions needed for the proof — the normalised surface measure of a cap, and the
radial cone over a cap — are `private` to the Solution module and appear in no compared
statement.
-/

noncomputable section

open Filter Topology Real InnerProductGeometry

namespace MiscMath.Geometry

/-! ## The bridge between angular caps and chordal balls -/

/-- The chord joining two unit vectors has length `2 sin (θ/2)`, where `θ` is the angle
between them. -/
theorem dist_eq_two_mul_sin_angle_div_two {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    dist x y = 2 * Real.sin (angle x y / 2) := by
  sorry

/-- For unit vectors, an angular cap of half-angle `θ ∈ [0, π]` is exactly a chordal
closed ball of radius `2 sin (θ/2)`.

This is what makes the headline statement a statement about spherical caps: the set of
unit vectors within angle `θ` of a centre `c` and the closed ball of radius
`2 sin (θ/2)` about `c` are the same set, so counting one is counting the other. -/
theorem angle_le_iff_dist_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    angle x y ≤ θ ↔ dist x y ≤ 2 * Real.sin (θ / 2) := by
  sorry

/-! ## Wyner's covering theorem -/

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
  sorry

/-! ## The two guards against junk values

`Metric.coveringNumber` lands in `ℕ∞` and the headline statement applies `ENat.toNat` to
it, then `Real.log`. Both have junk values — `ENat.toNat ⊤ = 0` and `Real.log 0 = 0` — and
a statement that only ever spoke about those would be true and worthless. These two
theorems rule that out for every dimension the limit can see. -/

/-- The covering number appearing in `tendsto_log_coveringNumber_sphere_div_atTop` is
finite, so the `ENat.toNat` in its statement is not a junk value. -/
theorem coveringNumber_sphere_ne_top (n : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ ≤ π) :
    Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := by
  sorry

/-- ... and it is nonzero in every dimension `n ≥ 1`, so its logarithm is not a junk value
either. The hypothesis `1 ≤ n` cannot be dropped: the sphere of `ℝ⁰` is empty, so its
covering number is `0` at every radius. -/
theorem coveringNumber_sphere_pos {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ0 : 0 < θ)
    (hθpi : θ ≤ π) :
    0 < (Metric.coveringNumber (Real.toNNReal (2 * Real.sin (θ / 2)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toNat := by
  sorry

end MiscMath.Geometry
