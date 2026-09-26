/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Bounds
import MiscMath.Computability.RedBluePebbleGame.Feasibility
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Fin.VecNotation

/-!
# Hong and Kung's I/O lower bound for the FFT, in the red-blue pebble game

## Informal statement

The **red-blue pebble game** models a computation run with `S` words of fast memory and
unlimited slow memory. It is played on a directed graph whose vertices are values and whose
edges run from each value to the ones computed from it. A red pebble on a vertex is its value
held in fast memory, a blue pebble its value held in slow memory. There are five moves:

* **load:** put a red pebble on a vertex that holds a blue one;
* **store:** put a blue pebble on a vertex that holds a red one;
* **compute:** put a red pebble on a vertex that is not an input, once all its predecessors
  hold red pebbles;
* **delete** a red pebble, or a blue one.

A load or a store costs one I/O operation; the other moves are free. A *complete calculation*
starts with blue pebbles on exactly the inputs and ends with blue pebbles on exactly the outputs
and no red pebble, never holding more than `S` red pebbles at once. The *minimum I/O time* `Q` is
the least cost of a complete calculation.

The **`n`-point FFT graph**, `n = 2^k` with `k ≥ 1`, has levels `0, …, k` of `n` vertices each.
Each vertex `(l, i)` below the top has edges to `(l + 1, i)` and `(l + 1, i xor 2^l)`. The inputs
are level `0` and the outputs level `k`. For it:

1. **Feasibility** (`fft_complete_iff`). A complete calculation exists exactly when `S ≥ 3`.
2. **The two bounds the argument gives** (`fft_io_bounds`). With `S ≥ 1`, every complete
   calculation costs `q ≥ 2n`, and `q ≥ n (log₂ n + 1) / (2 log₂ (4S)) − S`.
3. **Corollary 4.1, with its constant** (`fft_io_lower_bound`). With `S ≥ 3`, every complete
   calculation satisfies `n log₂ n ≤ 5 q log₂ S`.
4. **Corollary 4.1 as the paper states it** (`fft_io_lower_bound_isBigO`): `Q · log S = Ω(n log n)`,
   with one constant for every `n ≥ 2` and every `S ≥ 3`.

## How to read these statements

The four definitions they are stated through are in `RedBluePebbleGame/Spec.lean`, and they are
part of the read. They are `Step` (the five moves, each labelled with its charge),
`HasCompleteCalculation`, `fftEdge` and `minIOTime` (the paper's `Q`, as an infimum over `ℕ`).
The inputs and outputs are written inline, as `Finset.univ.filter (·.1 = 0)` and
`Finset.univ.filter (·.1 = Fin.last k)`. Seven things are worth knowing.

* **The charges are part of the witness.** A transition that is both a load and a computation
  may be charged either way. In the source the player chooses which rule to apply, and the I/O
  time counts applications of the I/O rules; so the bounds hold for the cheapest charging.
* **Levels and lanes are compared as natural numbers.** No edge leaves the top level; `Fin`
  arithmetic would have wrapped round to level `0`.
* **The hypotheses on `S` restrict nothing.** A complete calculation forces `S ≥ 3`
  (`fft_complete_iff`), so `3 ≤ S` in `fft_io_lower_bound` and `1 ≤ S` in `fft_io_bounds` are
  implied by the calculation hypothesis. They are there so that each logarithm is visibly away
  from its junk values.
* **The second bound of `fft_io_bounds` can say nothing.** Its left side is `≤ 0` exactly when
  `S ≥ n/2`, the additive `−S` having swamped it. There the first bound, `q ≥ 2n`, carries the
  claim, and `fft_io_lower_bound` combines the two.
* **`minIOTime` is `sInf`, which is `0` where no calculation exists** (`S ≤ 2`). The asymptotic
  statement is made only for `S ≥ 3`, and it could not survive that value: on its own it implies
  that a calculation exists at every point it covers, and that none costs nothing.
* **Mathlib has no `Ω`.** So `Q · log S = Ω(n log n)` is written `n log n = O(Q · log S)`,
  with `n = 2^k` and natural logarithms (the base only moves the constant).
* **The asymptotic statement is uniform.** Its filter is the principal filter of
  `{(k, S) : k ≥ 1, S ≥ 3}`, so it says: there is one constant `C` with `n ln n ≤ C · Q · ln S` for
  every `k ≥ 1` and every `S ≥ 3` (`C = 5` works).
  - The paper names no filter. It calls `S` "a constant" yet keeps `log S` in the bound, which
    only carries information if the hidden constant is independent of `S`.
  - This reading is the strongest. The readings `n → ∞` at fixed `S`, and `n, S → ∞` together,
    follow in one line each (`IsBigO.comp_tendsto`, `IsBigO.mono`).

## Source

Hong Jia-Wei and H. T. Kung, *I/O Complexity: The Red-Blue Pebble Game*, Proceedings of the 13th
Annual ACM Symposium on Theory of Computing (STOC '81), pp. 326–333,
doi:10.1145/800076.802486; a scan is on H. T. Kung's page,
<https://www.eecs.harvard.edu/~htk/publication/1981-stoc-hong-kung.pdf>. Where things are:

* the game and the definition of `Q`: §2, p. 327;
* Lemma 3.1, Theorem 4.1 and its proof, and Corollary 4.1 ("`Q · log S = Ω(n log n)`"): §4, p. 329.

Later restatements of the model, for comparison:

* J. Elango, F. Rastello, L.-N. Pouchet, J. Ramanujam and P. Sadayappan (2014), arXiv:1404.4767:
  the inputs are exactly the sources, and inputs cannot be computed, as here;
* P. A. Papp and R. Wattenhofer (2020), arXiv:2005.08609: sources can be computed for free.

## Relation to Mathlib

Mathlib has no pebble games and no I/O complexity, and its `Digraph` is a bare adjacency
relation with no path API. The game is therefore stated through four new definitions, in
`RedBluePebbleGame/Spec.lean`, which are part of the read.

Everything else is Mathlib's:

* the graph is an edge relation `V → V → Prop`, the form of `Digraph.Adj`;
* configurations are pairs of `Finset`s;
* the minimum is `sInf` on `ℕ`;
* the asymptotic statement is `Asymptotics.IsBigO`;
* paths, in the proofs, are `Relation.ReflTransGen`.

No earlier formalisation of the game or of these bounds was found, in Lean, Coq, Isabelle or
Prove2Me's Formalpedia (searched 2026-09-25).

## Where this differs from the source

* **Corrected: an input cannot be computed.** The paper's rule R3 places a red pebble on any
  vertex whose predecessors are all red. For a source that holds vacuously, so read literally the
  inputs can be computed for free. That makes the paper's Theorem 3.1 false: summing 8 inputs
  with `S = 3` costs one I/O, yet the theorem demands more. Here `compute` requires `v ∉ I`, as in
  Elango et al.
  - The sanity checks show the condition carries weight: without designated inputs, the 2-point
    FFT costs 2 rather than 4.
* **Corrected in the proof: Theorem 4.1's per-set bound.** The paper bounds a set dominated by `d`
  vertices by `2d log d`, which is `0` at `d = 1` although a vertex dominates itself, and its
  induction uses that case. The proof here uses `d log₂ (2d)`, which is exact at `d = 1, 2, 4`.
  Theorem 4.1 itself, a bound on the parts of an `S`-dominator partition, is not stated here.
* **A different route.** The paper reaches Corollary 4.1 through `S`-partitions (Theorem 3.1 and
  Lemma 3.1), and Theorem 3.1 as printed is false. The proof here cuts the calculation into windows
  of `S` loads and stores directly, and needs no partition theorem.
* **Strengthened: explicit constants.** Corollary 4.1's `Ω` gets the constant `1/5`
  (`fft_io_lower_bound`), and the `Ω` form is stated uniformly in `n` and `S`.
* **Added: `q ≥ 2n`.** Every input is loaded and every output stored. The paper does not state
  this, and for large `S` its step from Lemma 3.1 to Corollary 4.1 silently needs it.
* **Convention: no move is a no-op.** A load onto a vertex already red is not a move, and nor are
  the like. This loses nothing: deleting a no-op from a calculation leaves one no dearer.
* **Convention: the end is exact.** A calculation ends with blue pebbles on exactly the outputs and
  no red pebble. The paper asks only for blue pebbles on the outputs. Deletions are free, so the
  minimum cost is the same.
* **Convention: a computed pebble is placed, not slid.** Computing a vertex leaves its predecessors'
  red pebbles where they are. With sliding, two red pebbles would do for the FFT graph.
* **Omitted: everything else in the paper.** That includes Theorem 2.1 (the matching upper bound,
  which the paper states without proof), Theorems 3.1 and 4.1 as stated, and §§5–8, matrix
  multiplication among them.

## Provenance

Result selected and specified by George A. Constantinides, who has read its advertised
statements against the informal claim above on a best-effort basis. They are `fft_io_lower_bound`,
`fft_io_bounds`, `fft_complete_iff` and `fft_io_lower_bound_isBigO`, and the four definitions
they are stated through: `Step`, `HasCompleteCalculation`, `fftEdge` and `minIOTime` in
`RedBluePebbleGame/Spec.lean`. The statements and their proofs were generated by Claude, and are
kernel-verified and axiom-audited; the proofs are read by nobody. Every other lemma and definition
here is proof, and may be read by no one. A best-effort read is not a review — satisfy yourself
that the statement says what you need before relying on it. See the repository README.

The statements were written, read back and read before any proof existed, and frozen as
`Target/RedBluePebbleGame.lean` (commit `783e5a3`). `Target/RedBluePebbleGame/TypeCheck.lean`
ascribes each frozen type to the theorem proved here, so the two cannot drift apart.

Before that read, the advertised statements were read back blind. An agent was given them, and
the definitions they are stated through, and nothing else — no informal statement, no source, no
docstring — and rendered them into English; the rendering was compared against the informal
statement above. This was done twice:

* **The first rendering** surfaced that a transition that is both a load and a computation may be
  charged either way. The docstrings now say so.
* **The second** followed the subtractive form of `fft_io_bounds` and the addition of the
  asymptotic statement. It surfaced that the second bound says nothing once `S ≥ n/2`, and that
  the asymptotic statement itself implies a calculation exists wherever it applies. Both are now
  said above.

The renderings are kept verbatim in `docs/readbacks/Computability/RedBluePebbleGame.md`, with the
model that wrote them and the date.
-/

open Filter

namespace MiscMath.Computability

open RedBluePebbleGame

/-- **Hong and Kung's Corollary 4.1, with its constant.** Every complete calculation of the
`2^k`-point FFT graph with `S ≥ 3` red pebbles, charged `q`, has `2^k · k ≤ 5 q log₂ S`. -/
theorem fft_io_lower_bound {k S q : ℕ} (hk : 1 ≤ k) (hS : 3 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    (2 : ℝ) ^ k * k ≤ 5 * q * Real.logb 2 S := by
  have h1 : (2 : ℝ) ^ (k + 1) ≤ q := by exact_mod_cast fft_two_pow_succ_le hk h
  have h2 := fft_mul_card_le hk (by omega) h
  have hS' : (3 : ℝ) ≤ S := by exact_mod_cast hS
  have hL4 : Real.logb 2 (4 * S) = 2 + Real.logb 2 S := by
    rw [Real.logb_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  set L := Real.logb 2 S with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) (by linarith)
  have hL43 : 4 ≤ 3 * L := by
    have e₁ : Real.logb 2 ((S : ℝ) ^ 3) = 3 * L := by rw [Real.logb_pow, hL]; push_cast; ring
    have e₂ : Real.logb 2 (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    have hmono : Real.logb 2 16 ≤ Real.logb 2 ((S : ℝ) ^ 3) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hS' 3])
    linarith
  have h2' : (S : ℝ) * ((k + 1) * 2 ^ k) ≤ S * ((q + S) * (2 * (2 + L))) := by
    rw [hL4] at h2
    calc _ ≤ _ := h2
      _ = _ := by ring
  have h3 : ((k : ℝ) + 1) * 2 ^ k ≤ (q + S) * (2 * (2 + L)) :=
    le_of_mul_le_mul_left h2' (by positivity)
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  rcases le_or_gt (2 ^ k) (S ^ 10) with hA | hB
  · -- Memory is large: `k ≤ 10 log₂ S`, and the trivial bound suffices.
    have hkL : (k : ℝ) ≤ 10 * L := by
      have : Real.logb 2 ((2 : ℝ) ^ k) ≤ Real.logb 2 ((S : ℝ) ^ 10) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast hA)
      rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    have hq2 : (2 : ℝ) * 2 ^ k ≤ q := by rw [pow_succ] at h1; linarith
    nlinarith [mul_le_mul_of_nonneg_right hq2 hL0, mul_le_mul_of_nonneg_left hkL h2k]
  · -- Memory is small: `5 S log₂ S < 2^k`, and the domination bound suffices.
    have hLS : L ≤ S := by
      have h' : (S : ℝ) < 2 ^ S := by exact_mod_cast Nat.lt_two_pow_self
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h'.le
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    have h5 : 5 * (S : ℝ) ^ 2 ≤ (S : ℝ) ^ 10 := by
      have h8 : (5 : ℝ) ≤ (S : ℝ) ^ 8 :=
        calc (5 : ℝ) ≤ 3 ^ 8 := by norm_num
          _ ≤ (S : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hS' 8
      have : (S : ℝ) ^ 10 = (S : ℝ) ^ 8 * (S : ℝ) ^ 2 := by ring
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ S by positivity) 2]
    have hB' : (S : ℝ) ^ 10 < 2 ^ k := by exact_mod_cast hB
    have hLS5 : 5 * L * S ≤ 2 ^ k := by
      nlinarith [mul_le_mul_of_nonneg_right hLS (show (0 : ℝ) ≤ S by positivity)]
    have hqS : (0 : ℝ) ≤ q + S := by positivity
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 * L - 4 by linarith) hqS]

/-- **The two bounds the argument gives.** Every complete calculation of the `2^k`-point FFT graph,
charged `q`, loads each input and stores each output, so `q ≥ 2^(k+1)`; and
`q ≥ 2^k (k + 1) / (2 log₂ (4S)) − S`, which says nothing once `S ≥ 2^(k-1)`. -/
theorem fft_io_bounds {k S q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    2 ^ (k + 1) ≤ q ∧ (2 : ℝ) ^ k * (k + 1) / (2 * Real.logb 2 (4 * S)) - S ≤ q := by
  refine ⟨fft_two_pow_succ_le hk h, ?_⟩
  have h2 := fft_mul_card_le hk hS h
  have hS' : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hL : 0 < Real.logb 2 (4 * S) := Real.logb_pos (by norm_num) (by linarith)
  have h2' : (S : ℝ) * ((k + 1) * 2 ^ k) ≤ S * ((q + S) * (2 * Real.logb 2 (4 * S))) := by
    calc _ ≤ _ := h2
      _ = _ := by ring
  have h3 := le_of_mul_le_mul_left h2' (by positivity)
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  linarith

/-- **Feasibility.** The `2^k`-point FFT graph, `k ≥ 1`, has a complete calculation exactly when
at least three red pebbles are available. -/
theorem fft_complete_iff {k S : ℕ} (hk : 1 ≤ k) :
    (∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) ↔ 3 ≤ S :=
  ⟨fun ⟨_, h⟩ => three_le_of_fft_hasCompleteCalculation hk h, fft_hasCompleteCalculation⟩

/-- **Hong and Kung's Corollary 4.1 as stated: `Q · log S = Ω(n log n)`.** With `n = 2^k` and `Q`
the minimum I/O time, `n ln n = O(Q · ln S)` along the principal filter of
`{(k, S) : k ≥ 1, S ≥ 3}`: one constant serves every such `k` and `S`. -/
theorem fft_io_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1)) =O[𝓟 {p | 1 ≤ p.1 ∧ 3 ≤ p.2}]
      fun p => (minIOTime (fftEdge p.1) (Finset.univ.filter (·.1 = 0))
        (Finset.univ.filter (·.1 = Fin.last p.1)) p.2 : ℝ) * Real.log p.2 := by
  rw [Asymptotics.isBigO_principal]
  refine ⟨5, ?_⟩
  rintro ⟨k, S⟩ ⟨hk, hS⟩
  dsimp only at hk hS ⊢
  have hmem : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S
      (minIOTime (fftEdge k) (Finset.univ.filter (·.1 = 0))
        (Finset.univ.filter (·.1 = Fin.last k)) S) :=
    Nat.sInf_mem (s := {q | HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q}) ((fft_complete_iff hk).2 hS)
  have hb := fft_io_lower_bound hk hS hmem
  set Q := minIOTime (fftEdge k) (Finset.univ.filter (·.1 = 0))
    (Finset.univ.filter (·.1 = Fin.last k)) S
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (by omega : 1 < S))
  rw [Real.logb, mul_div_assoc', le_div_iff₀ hlog2] at hb
  rw [Real.log_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg k) hlog2.le)),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg Q) hlogS.le)]
  linarith

/-! ## Sanity checks

Guards against the ways a correct proof can still accompany a useless statement. These are
`example`s: elaborated by the build, so one that stops holding breaks it, and exporting no names.
They are *not* reached by the axiom audit, which walks the named declarations a module contributes
to the environment, and an `example` contributes none. What covers them instead is the textual
escape-hatch scan in `scripts/check-conventions.sh`, which reads the file rather than the
environment. The `private` declarations of this file are audited under their mangled names.

What each one pins:

* **Non-vacuity.** `twoPoint_calc` is a complete calculation of the 2-point FFT with three red
  pebbles and four loads and stores. It is checked move by move by `decide`, independently of
  every proof above, and every hypothesis of the four theorems holds there.
* **The first bound is attained.** At that point `minIOTime` is exactly `4`: at most `4` by the
  calculation, at least `4` by `fft_io_bounds`. So `q ≥ 2^(k+1)` is sharp at `k = 1`, and
  `minIOTime` takes a genuine value there, not its value on the empty set.
* **`k ≥ 1` cannot be dropped.** At `k = 0` the one vertex is both input and output, and the
  calculation with no moves costs nothing, with no red pebbles.
* **The input condition in `Step` carries weight.** Declare no inputs and the level-0 vertices are
  computed from nothing, so the 2-point FFT costs only its two stores. With the inputs declared,
  `fft_io_bounds` demands four.
* **The butterfly is the intended graph.** No edge leaves the top level and none enters level `0`,
  so nothing wraps round. At `k = 3` every vertex off level `0` has exactly two predecessors, and
  the lanes paired at a given level differ in that level's bit.
-/

section Sanity

/-- The 2-point FFT with three red pebbles: load both inputs, compute and store each output, clear
up. Four loads and stores. -/
private theorem twoPoint_calc : HasCompleteCalculation (fftEdge 1) (Finset.univ.filter (·.1 = 0))
    (Finset.univ.filter (·.1 = Fin.last 1)) 3 4 :=
  ⟨12, ![(∅, {(0, 0), (0, 1)}),
    ({(0, 0)}, {(0, 0), (0, 1)}),
    ({(0, 0), (0, 1)}, {(0, 0), (0, 1)}),
    ({(0, 0), (0, 1), (1, 0)}, {(0, 0), (0, 1)}),
    ({(0, 0), (0, 1), (1, 0)}, {(0, 0), (0, 1), (1, 0)}),
    ({(0, 0), (0, 1)}, {(0, 0), (0, 1), (1, 0)}),
    ({(0, 0), (0, 1), (1, 1)}, {(0, 0), (0, 1), (1, 0)}),
    ({(0, 0), (0, 1), (1, 1)}, {(0, 0), (0, 1), (1, 0), (1, 1)}),
    ({(0, 0), (0, 1)}, {(0, 0), (0, 1), (1, 0), (1, 1)}),
    ({(0, 1)}, {(0, 0), (0, 1), (1, 0), (1, 1)}),
    (∅, {(0, 0), (0, 1), (1, 0), (1, 1)}),
    (∅, {(0, 1), (1, 0), (1, 1)}),
    (∅, {(1, 0), (1, 1)})], ![1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], by decide⟩

-- Non-vacuity: the hypotheses of all four theorems hold at `k = 1`, `S = 3`, `q = 4`.
example : 1 ≤ 1 ∧ 3 ≤ 3 ∧ HasCompleteCalculation (fftEdge 1) (Finset.univ.filter (·.1 = 0))
    (Finset.univ.filter (·.1 = Fin.last 1)) 3 4 :=
  ⟨le_rfl, le_rfl, twoPoint_calc⟩

-- The bound `q ≥ 2^(k+1)` is attained at `k = 1`, and `minIOTime` there is a genuine minimum.
example : minIOTime (fftEdge 1) (Finset.univ.filter (·.1 = 0))
    (Finset.univ.filter (·.1 = Fin.last 1)) 3 = 4 := by
  refine le_antisymm (Nat.sInf_le twoPoint_calc) ?_
  have hmem : HasCompleteCalculation (fftEdge 1) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last 1)) 3
      (minIOTime (fftEdge 1) (Finset.univ.filter (·.1 = 0))
        (Finset.univ.filter (·.1 = Fin.last 1)) 3) :=
    Nat.sInf_mem (s := {q | HasCompleteCalculation (fftEdge 1) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last 1)) 3 q}) ⟨4, twoPoint_calc⟩
  exact (fft_io_bounds le_rfl (by norm_num) hmem).1

-- `1 ≤ k` cannot be dropped: at `k = 0` nothing need be done, at no cost and with no red pebble,
-- whereas `2^(0+1) = 2`.
example : HasCompleteCalculation (fftEdge 0) (Finset.univ.filter (·.1 = 0))
    (Finset.univ.filter (·.1 = Fin.last 0)) 0 0 :=
  ⟨0, fun _ => (∅, Finset.univ.filter (·.1 = 0)), Fin.elim0, by decide⟩

-- The input condition in `Step` carries weight: with no inputs declared, level 0 is computed from
-- nothing and the 2-point FFT costs only its two stores, where `fft_io_bounds` demands four.
example : HasCompleteCalculation (fftEdge 1) ∅ (Finset.univ.filter (·.1 = Fin.last 1)) 3 2 :=
  ⟨10, ![(∅, ∅),
    ({(0, 0)}, ∅),
    ({(0, 0), (0, 1)}, ∅),
    ({(0, 0), (0, 1), (1, 0)}, ∅),
    ({(0, 0), (0, 1), (1, 0)}, {(1, 0)}),
    ({(0, 0), (0, 1)}, {(1, 0)}),
    ({(0, 0), (0, 1), (1, 1)}, {(1, 0)}),
    ({(0, 0), (0, 1), (1, 1)}, {(1, 0), (1, 1)}),
    ({(0, 0), (0, 1)}, {(1, 0), (1, 1)}),
    ({(0, 1)}, {(1, 0), (1, 1)}),
    (∅, {(1, 0), (1, 1)})], ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0], by decide⟩

-- The butterfly as intended: no edge leaves the top level, and none enters level 0.
example (k : ℕ) (u v : Fin (k + 1) × Fin (2 ^ k)) (hu : u.1 = Fin.last k) : ¬ fftEdge k u v := by
  have := v.1.isLt
  simp only [fftEdge, hu, Fin.val_last]
  omega

example (k : ℕ) (u v : Fin (k + 1) × Fin (2 ^ k)) (hv : v.1 = 0) : ¬ fftEdge k u v := by
  simp only [fftEdge, hv, Fin.val_zero]
  omega

-- At `k = 3`: every vertex off level 0 has exactly two predecessors, and from level 1 to level 2
-- the edges pair each lane with the lane differing in bit 1.
example : ∀ v : Fin 4 × Fin 8, v.1 ≠ 0 → (Finset.univ.filter (fftEdge 3 · v)).card = 2 := by
  decide

example : ∀ i j : Fin 8, fftEdge 3 (1, i) (2, j) ↔ (j = i ∨ (i : ℕ) ^^^ 2 = j) := by
  decide

end Sanity

end MiscMath.Computability
