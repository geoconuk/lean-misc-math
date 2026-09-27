/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import MiscMath.Computability.RedBluePebbleGame.Bounds
import MiscMath.Computability.RedBluePebbleGame.Feasibility
import MiscMath.Computability.RedBluePebbleGame.Parts
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Fin.VecNotation

/-!
# Hong and Kung's red-blue pebble game: the key lemma, and the I/O complexity of the FFT

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

**The key lemma.** A *computation DAG* is a finite directed graph with no cycle, whose inputs are
exactly its vertices with no predecessor, whose outputs include every vertex with no successor,
and in which no vertex is both an input and an output.

* A set `D` *dominates* a set `W` if every path from an input to a vertex of `W`, paths of length
  `0` included, passes through `D`.
* An *`S`-dominator partition* splits the vertices into sets `V₁, …, V_h`, some possibly empty.
  Each set is dominated by at most `S` vertices, and every edge between two of the sets runs from
  the earlier to the later.
* An *`S`-partition* is an `S`-dominator partition in which each set also has at most `S`
  vertices with no successor in the same set.
* `P(S)` and `P_D(S)` are the least numbers of sets of an `S`-partition and of an `S`-dominator
  partition.

For every computation DAG:

1. **Theorem 3.1, corrected** (`exists_partition_of_hasCompleteCalculation`). Every complete
   calculation with at most `S` red pebbles, costing `q`, comes with a `2S`-partition into `h` sets,
   `S h ≥ q ≥ S (h − 1)`.
2. **Lemma 3.1** (`io_lower_bound_of_parts`). If every `2S`-partition has at least `h₀` sets, every
   complete calculation with at most `S` red pebbles costs `q ≥ S (h₀ − 1)`.
3. **Lemma 3.1 as the paper states it** (`minIOTime_lower_bound`). Wherever a complete calculation
   exists, `Q ≥ S (P(2S) − 1)`.

**The FFT.** The **`n`-point FFT graph**, `n = 2^k`, has levels `0, …, k` of `n` vertices each.
Each vertex `(l, i)` below the top has edges to `(l + 1, i)` and `(l + 1, i xor 2^l)`. The inputs
are level `0` and the outputs level `k`. For it:

4. **Theorem 4.1, with its constant** (`fft_parts_lower_bound`). For `S ≥ 1`, every `S`-dominator
   partition has `h` sets with `n (log₂ n + 1) ≤ h S log₂ (2S)`.
5. **Theorem 4.1 as the paper states it** (`fft_parts_lower_bound_isBigO`):
   `P_D(S) = Ω(n log n / (S log S))`, with one constant for every `n ≥ 2` and every `S ≥ 2`.
6. **Feasibility** (`fft_complete_iff`). For `k ≥ 1`, a complete calculation exists exactly when
   `S ≥ 3`.
7. **The two bounds the direct argument gives** (`fft_io_bounds`). For `k ≥ 1` and `S ≥ 1`, every
   complete calculation costs `q ≥ 2n`, and `q ≥ n (log₂ n + 1) / (2 log₂ (4S)) − S`.
8. **Corollary 4.1, with its constant** (`fft_io_lower_bound`). For `k ≥ 1` and `S ≥ 3`, every
   complete calculation satisfies `n log₂ n ≤ 5 q log₂ S`.
9. **Corollary 4.1 as the paper states it** (`fft_io_lower_bound_isBigO`): `Q · log S = Ω(n log n)`,
   with one constant for every `n ≥ 2` and every `S ≥ 3`.

## How to read these statements

The ten definitions they are stated through are in `RedBluePebbleGame/Spec.lean`, and they are
part of the read:

* the game: `Step` (the five moves, each labelled with its charge), `HasCompleteCalculation`,
  `fftEdge` and `minIOTime` (the paper's `Q`, as an infimum over `ℕ`);
* the key lemma: `IsComputationDAG`, `Dominates`, `IsDominatorPartition`, `IsPartition`, and
  `minParts` and `minDominatorParts` (the paper's `P(S)` and `P_D(S)`, as infima over `ℕ`).

The FFT's inputs and outputs are written inline, as `Finset.univ.filter (·.1 = 0)` and
`Finset.univ.filter (·.1 = Fin.last k)`.

**The game and the FFT.**

* **The charges are part of the witness.** A transition that is both a load and a computation
  may be charged either way. In the source the player chooses which rule to apply, and the I/O
  time counts applications of the I/O rules; so the bounds hold for the cheapest charging.
* **Levels and lanes are compared as natural numbers.** No edge leaves the top level; `Fin`
  arithmetic would have wrapped round to level `0`.
* **The hypotheses on `S` restrict nothing.**
  - A complete calculation of the FFT forces `S ≥ 3` (`fft_complete_iff`). So `3 ≤ S` in
    `fft_io_lower_bound` and `1 ≤ S` in `fft_io_bounds` are implied by the calculation hypothesis.
  - No `0`-dominator partition exists, since a set holding an input must have it in its dominator.
    So `1 ≤ S` in `fft_parts_lower_bound` excludes nothing either.
  - They are there so that each logarithm is visibly away from its junk values.
* **The second bound of `fft_io_bounds` can say nothing.** Its left side is `≤ 0` exactly when
  `S ≥ n/2`, the additive `−S` having swamped it. There the first bound, `q ≥ 2n`, carries the
  claim, and `fft_io_lower_bound` combines the two.
* **`minIOTime` is `sInf`, which is `0` where no calculation exists** (`S ≤ 2`). The asymptotic
  statement is made only for `S ≥ 3`, and it could not survive that value: on its own it implies
  that a calculation exists at every point it covers, and that none costs nothing.
* **Mathlib has no `Ω`.** So "`g = Ω(f)`" is written "`f = O(g)`", with `n = 2^k` and natural
  logarithms (the base only moves the constant). `Q · log S = Ω(n log n)` becomes
  `n log n = O(Q · log S)`, and `P_D(S) = Ω(n log n / (S log S))` becomes
  `n log n / (S log S) = O(P_D(S))`.
* **The asymptotic statements are uniform.** Their filters are principal, on
  `{(k, S) : k ≥ 1, S ≥ 3}` and `{(k, S) : k ≥ 1, S ≥ 2}`. So each says there is one constant `C`
  for every such `k` and `S` at once: `n ln n ≤ C · Q · ln S` (`C = 5` works), and
  `n ln n / (S ln S) ≤ C · P_D(S)` (`C = 2` works).
  - The paper names no filter. It calls `S` "a constant" yet keeps `log S` in its bounds, which
    only carries information if the hidden constant is independent of `S`.
  - This reading is the strongest. The readings `n → ∞` at fixed `S`, and `n, S → ∞` together,
    follow in one line each (`IsBigO.comp_tendsto`, `IsBigO.mono`).

**The key lemma.**

* **`IsComputationDAG` is the paper's §2 assumptions on the graph, corrected.** The paper lets the
  inputs be any set containing the sources; here they are exactly the sources. The sanity checks
  show that each of its four conditions carries weight. Together they rule out isolated vertices.
* **Paths of length `0` count in `Dominates`,** so an input in `W` must lie in `D`. That is what the
  condition `x ∉ D` in its definition is for: a path of length `0` uses no edge, so the condition
  on edges cannot see it.
* **Partitions are indexed families, and empty sets are allowed and counted.**
  - So in Theorem 3.1, `q ≤ S h` can always be met by adding empty sets. `S h ≤ q + S` is the
    conjunct that bounds `h`.
  - Together the two conjuncts fix `h` to `⌈q/S⌉`, or to `q/S` or `q/S + 1` when `S` divides `q`.
  - The paper's own construction produces empty sets, so its statement has the same slack.
* **The paper's condition P4, "no cyclic dependence" among the sets, is an ordering here:** an edge
  from `V_i` to `V_j` forces `i ≤ j`.
  - A family has no cyclic dependence exactly when some re-indexing of it satisfies this.
  - Every statement here depends on a partition only through whether one exists, or through its
    number of sets, so nothing changes.
  - The paper's own proof establishes the ordered form (p. 328).
  - `IsDominatorPartition` is a property of the indexed family, not of the collection of sets.
* **`IsPartition` counts the minimum set with a classical decision procedure,** for "no successor
  in the same set". Which procedure is used cannot change the count.
* **`2S`, not `S`.** Theorem 3.1 turns `S` red pebbles into a `2S`-partition, and Lemma 3.1 reads
  `P(2S)`, as in the paper.
  - A window of the calculation making `S` loads and stores has as dominator the vertices red when
    it starts and those it loads, at most `S` of each.
  - Its minimum set lies within the vertices red when it ends and those it stores.
  - Theorem 4.1 is stated at a general `S`, as in the paper, and Corollary 4.1 uses it at `2S`.
* **The general statements carry no `1 ≤ S`.** Under `IsComputationDAG`, a complete calculation of
  a nonempty graph needs `S ≥ 2`.
  - A vertex with no successor is an output, hence not an input, hence has a predecessor.
  - Computing it needs both red at once.
  - So `S ≤ 1` leaves only the empty graph, where the statements hold trivially.
* **`minParts` and `minDominatorParts` are `sInf`, which is `0` where no partition exists.**
  - `minIOTime_lower_bound` is made only where a calculation exists. There Theorem 3.1 supplies a
    `2S`-partition, so `P(2S)` is a genuine minimum.
  - `P_D(S)` is a genuine minimum for every `S ≥ 1`: the single vertices, level by level, form an
    `S`-dominator partition.

## Source

Hong Jia-Wei and H. T. Kung, *I/O Complexity: The Red-Blue Pebble Game*, Proceedings of the 13th
Annual ACM Symposium on Theory of Computing (STOC '81), pp. 326–333,
doi:10.1145/800076.802486; a scan is on H. T. Kung's page,
<https://www.eecs.harvard.edu/~htk/publication/1981-stoc-hong-kung.pdf>. Where things are:

* the game, its standing assumptions on the graph, and the definition of `Q`: §2, p. 327;
* `S`-partitions (P1–P4), Theorem 3.1 and its proof: §3, p. 328;
* `P(S)`, Lemma 3.1, `S`-dominator partitions, `P_D(S)`, Theorem 4.1 and its proof, and
  Corollary 4.1 ("`Q · log S = Ω(n log n)`"): §§3–4, p. 329.

Later restatements of the model, for comparison:

* J. Elango, F. Rastello, L.-N. Pouchet, J. Ramanujam and P. Sadayappan (2014), arXiv:1404.4767:
  the inputs are exactly the sources, and inputs cannot be computed, as here;
* P. A. Papp and R. Wattenhofer (2020), arXiv:2005.08609: sources can be computed for free.

## Relation to Mathlib

Mathlib has no pebble games and no I/O complexity, and its `Digraph` is a bare adjacency
relation with no path API. The game and the key lemma are therefore stated through ten new
definitions, in `RedBluePebbleGame/Spec.lean`, which are part of the read.

Everything else is Mathlib's:

* the graph is an edge relation `V → V → Prop`, the form of `Digraph.Adj`;
* configurations and the sets of a partition are `Finset`s;
* paths are `Relation.ReflTransGen`, and cycles `Relation.TransGen`;
* the minima are `sInf` on `ℕ`;
* the asymptotic statements are `Asymptotics.IsBigO`.

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
* **Corrected: the inputs are exactly the sources.** The paper lets the inputs be any set
  containing the sources (§2), and uses that in §7. That too makes its Theorem 3.1 false.
  - A chain of 9 designated inputs feeding one output has a calculation costing 2 with `S = 2`.
    That allows at most 2 sets, yet every `4`-partition needs 3 (sanity checks).
* **Corrected in the proof: Theorem 3.1's cover argument.**
  - The paper splits on whether a predecessor holds any pebble when a subcalculation starts.
    Here the split is on whether it holds a red one.
  - An input still holding its initial blue pebble need not lie in an earlier set, and the
    paper's split puts it on the wrong side.
* **Corrected: Theorem 4.1's per-set bound.**
  - The paper bounds a set dominated by `d` vertices by `2d log d`. That is `0` at `d = 1`,
    although a vertex dominates itself, and its induction uses that case.
  - Here the bound is `d log₂ (2d)`, which is exact at `d = 1, 2, 4`.
  - So `fft_parts_lower_bound` carries `S log₂ (2S)`. Theorem 4.1's `Ω` form is unaffected.
* **Convention: partitions are indexed families, and may have empty sets.** The paper's own
  construction needs them for `S h ≥ q`.
* **Convention: P4 is an ordering of the sets.** See above; nothing changes.
* **Two routes to Corollary 4.1.**
  - The paper's route goes through Theorem 3.1, Lemma 3.1 and Theorem 4.1, all stated and proved
    here.
  - The proof of Corollary 4.1 here does not use them. It cuts the calculation into windows of
    `S` loads and stores directly.
  - With the corrected Theorem 4.1 applied at `2S`, the paper's route gives the second bound of
    `fft_io_bounds`.
* **Strengthened: explicit constants.**
  - Corollary 4.1's `Ω` gets the constant `1/5` (`fft_io_lower_bound`).
  - Theorem 4.1 gets `n (log₂ n + 1) ≤ h S log₂ (2S)`.
  - Both `Ω` forms are stated uniformly in `n` and `S`.
* **Added: `q ≥ 2n`.** Every input is loaded and every output stored. The paper does not state
  this, and for large `S` its step from Lemma 3.1 to Corollary 4.1 silently needs it.
* **Convention: no move is a no-op.** A load onto a vertex already red is not a move, and nor are
  the like. This loses nothing: deleting a no-op from a calculation leaves one no dearer.
* **Convention: the end is exact.** A calculation ends with blue pebbles on exactly the outputs and
  no red pebble. The paper asks only for blue pebbles on the outputs. Deletions are free, so the
  minimum cost is the same.
* **Convention: a computed pebble is placed, not slid.** Computing a vertex leaves its predecessors'
  red pebbles where they are. With sliding, two red pebbles would do for the FFT graph.
* **Omitted: everything else in the paper.** That includes:
  - Theorem 2.1, the matching upper bound, which the paper states without proof;
  - §§5–8, including matrix multiplication (§6, whose own use of the method bounds each set
    through its minimum set as well as its dominator).

## Provenance

Result selected and specified by George A. Constantinides, who has read its advertised
statements on a best-effort basis, before any proof of them existed.

They are nine theorems:

* `exists_partition_of_hasCompleteCalculation`, `io_lower_bound_of_parts` and
  `minIOTime_lower_bound`;
* `fft_parts_lower_bound` and `fft_parts_lower_bound_isBigO`;
* `fft_io_lower_bound`, `fft_io_bounds`, `fft_complete_iff` and `fft_io_lower_bound_isBigO`.

They are stated through ten definitions in `RedBluePebbleGame/Spec.lean`: `Step`,
`HasCompleteCalculation`, `fftEdge`, `minIOTime`, `IsComputationDAG`, `Dominates`,
`IsDominatorPartition`, `IsPartition`, `minParts` and `minDominatorParts`.

The statements and their proofs were generated by Claude, and are kernel-verified and
axiom-audited; the proofs are read by nobody. Every other lemma and definition here is proof, and
may be read by no one. A best-effort read is not a review — satisfy yourself that the statement
says what you need before relying on it. See the repository README.

The statements were written, read back and read before any proof existed. They were frozen in two
phases as `Target/RedBluePebbleGame.lean`:

* the FFT statements in commit `783e5a3`;
* the key lemma and Theorem 4.1 in commits `7c3c34d` and `d971e3f`.

`Target/RedBluePebbleGame/TypeCheck.lean` ascribes each frozen type to the theorem proved here, so
the two cannot drift apart.

Before George's read, the advertised statements were read back blind. An agent was given them,
and the definitions they are stated through, and nothing else — no informal statement, no source,
no docstring. It rendered them into English, and the rendering was compared with the intended
statements. Each phase had two rounds:

* **Phase 1, round 1** surfaced that a transition that is both a load and a computation may be
  charged either way. The docstrings now say so.
* **Phase 1, round 2** followed the subtractive form of `fft_io_bounds` and the addition of the
  asymptotic statement. It surfaced two points, both now said above:
  - the second bound says nothing once `S ≥ n/2`;
  - the asymptotic statement itself implies a calculation exists wherever it applies.
* **Phase 2, round 1** surfaced that under the graph hypotheses `S ≤ 1` leaves only the empty
  graph. It also confirmed that empty sets make `q ≤ S h` free.
* **Phase 2, round 2** followed the gathering of the four graph hypotheses into
  `IsComputationDAG`. It surfaced that the conclusion of Theorem 3.1 fixes `h` almost exactly.

The points from Phase 2 are said above too. The renderings are kept verbatim in
`docs/readbacks/Computability/RedBluePebbleGame.md`, with the model that wrote them and the date.
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

/-- **Hong and Kung's Theorem 3.1, corrected.** Every complete calculation of a computation DAG
with at most `S` red pebbles, charged `q`, comes with a `2S`-partition of the graph into `h` parts,
`q ≤ S h ≤ q + S`. -/
theorem exists_partition_of_hasCompleteCalculation {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q : ℕ} (hG : IsComputationDAG E I O)
    (hq : HasCompleteCalculation E I O S q) :
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S :=
  exists_isPartition hG hq

/-- **Hong and Kung's Lemma 3.1.** If every `2S`-partition of a computation DAG has at least `h₀`
parts, every complete calculation with at most `S` red pebbles is charged `q ≥ S (h₀ - 1)`. -/
theorem io_lower_bound_of_parts {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q h₀ : ℕ} (hG : IsComputationDAG E I O)
    (hparts : ∀ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P → h₀ ≤ h)
    (hq : HasCompleteCalculation E I O S q) :
    S * h₀ ≤ q + S := by
  obtain ⟨h, P, hP, -, hle⟩ := exists_partition_of_hasCompleteCalculation hG hq
  exact (Nat.mul_le_mul_left S (hparts h P hP)).trans hle

/-- **Hong and Kung's Lemma 3.1 as stated: `Q ≥ S (P(2S) - 1)`.** For a computation DAG with a
complete calculation using at most `S` red pebbles, with `Q` the minimum I/O time and `P(2S)` the
least number of parts of a `2S`-partition. -/
theorem minIOTime_lower_bound {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S : ℕ} (hG : IsComputationDAG E I O)
    (hcalc : ∃ q, HasCompleteCalculation E I O S q) :
    (S : ℤ) * (minParts E I (2 * S) - 1) ≤ minIOTime E I O S := by
  have hQ : HasCompleteCalculation E I O S (minIOTime E I O S) :=
    Nat.sInf_mem (s := {q | HasCompleteCalculation E I O S q}) hcalc
  have h := io_lower_bound_of_parts hG
    (fun h P hP => (Nat.sInf_le ⟨P, hP⟩ : minParts E I (2 * S) ≤ h)) hQ
  have h' : ((S * minParts E I (2 * S) : ℕ) : ℤ) ≤ ((minIOTime E I O S + S : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

-- `1 ≤ S` is part of the frozen statement: it keeps `log₂ (2S)` visibly away from its junk value
-- at `0`. The proof does not use it, since at `S = 0` no part can hold an input.
set_option linter.unusedVariables false in
/-- **Hong and Kung's Theorem 4.1, with its constant.** Every `S`-dominator partition of the
`2^k`-point FFT graph, `S ≥ 1`, has `h` parts with `(k + 1) 2^k ≤ h S log₂ (2S)`. -/
theorem fft_parts_lower_bound {k S h : ℕ} (hS : 1 ≤ S)
    {P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hP : IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P) :
    (2 : ℝ) ^ k * (k + 1) ≤ h * (S * Real.logb 2 (2 * S)) := by
  have := fft_card_le_mul_bfly hP
  rw [bfly] at this
  linarith

/-- **Hong and Kung's Theorem 4.1 as stated: `P_D(S) = Ω(n log n / (S log S))`.** With `n = 2^k`
and `P_D(S)` the least number of parts of an `S`-dominator partition of the `n`-point FFT graph,
`n ln n / (S ln S) = O(P_D(S))` along the principal filter of `{(k, S) : k ≥ 1, S ≥ 2}`: one
constant serves every such `k` and `S`. -/
theorem fft_parts_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1) / (p.2 * Real.log p.2))
      =O[𝓟 {p | 1 ≤ p.1 ∧ 2 ≤ p.2}]
      fun p => (minDominatorParts (fftEdge p.1) (Finset.univ.filter (·.1 = 0)) p.2 : ℝ) := by
  rw [Asymptotics.isBigO_principal]
  refine ⟨2, ?_⟩
  rintro ⟨k, S⟩ ⟨hk, hS⟩
  dsimp only at hk hS ⊢
  obtain ⟨P, hP⟩ : ∃ P : Fin (minDominatorParts (fftEdge k) (Finset.univ.filter (·.1 = 0)) S) →
      Finset (Fin (k + 1) × Fin (2 ^ k)),
      IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P :=
    Nat.sInf_mem (s := {h | ∃ P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k)),
      IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P})
      ⟨_, fft_exists_isDominatorPartition k (by omega)⟩
  have hb : (2 : ℝ) ^ k * (k + 1) ≤
      (minDominatorParts (fftEdge k) (Finset.univ.filter (·.1 = 0)) S : ℝ) *
        (S * Real.logb 2 (2 * S)) := fft_parts_lower_bound (by omega) hP
  set M := minDominatorParts (fftEdge k) (Finset.univ.filter (·.1 = 0)) S
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS' : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hSpos : (0 : ℝ) < S := by linarith
  have hlogS : Real.log 2 ≤ Real.log S := Real.log_le_log (by norm_num) hS'
  have hlogSpos : 0 < Real.log S := hlog2.trans_le hlogS
  -- Clear `log₂ (2S) = (ln 2 + ln S) / ln 2` from the finitary bound.
  have hb' : (2 : ℝ) ^ k * (k + 1) * Real.log 2 ≤ M * S * (Real.log 2 + Real.log S) := by
    rw [Real.logb, Real.log_mul (by norm_num) hSpos.ne',
      show (M : ℝ) * (S * ((Real.log 2 + Real.log S) / Real.log 2)) =
        M * S * (Real.log 2 + Real.log S) / Real.log 2 by ring, le_div_iff₀ hlog2] at hb
    exact hb
  -- Then `ln 2 ≤ ln S` gives the constant `2`.
  have h1 : (M : ℝ) * S * Real.log 2 ≤ M * S * Real.log S :=
    mul_le_mul_of_nonneg_left hlogS (by positivity)
  have h2 : (0 : ℝ) ≤ 2 ^ k * Real.log 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.log_pow,
    abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg k)
      hlog2.le)) (mul_nonneg hSpos.le hlogSpos.le)), abs_of_nonneg (Nat.cast_nonneg M),
    div_le_iff₀ (mul_pos hSpos hlogSpos)]
  nlinarith [hb', h1, h2]

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

For the key lemma and Theorem 4.1:

* **Non-vacuity.** The FFT graph is a computation DAG for every `k ≥ 1` (`fft_isComputationDAG`).
  At the 2-point FFT with `S = 3` and `q = 4`, every hypothesis of the key lemma holds.
* **What Theorem 3.1 promises is there.** At that point it promises a `6`-partition into `h = 2`
  sets. The whole graph and an empty set are one.
* **The minima are genuine.** At the 2-point FFT, `P(6) = 1`. Also `P_D(1) = 4`, one set per
  vertex, so the bound of `fft_parts_lower_bound` is attained at `S = 1`.
* **Each graph hypothesis carries weight.** For each field of `IsComputationDAG`, a small graph
  satisfies the other three and has a complete calculation, but the conclusion of Theorem 3.1
  fails.
  - The first graph is a chain of designated inputs: the paper's own setting, and why its printed
    Theorem 3.1 is false.
  - The printed theorem's other defect, inputs computed under the literal rule R3, needs a
    different `Step`. It was checked by brute force, not here.
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

/-! ### The key lemma and Theorem 4.1 -/

-- Non-vacuity of the key lemma: its hypotheses hold together at the 2-point FFT, `S = 3`, `q = 4`.
example : IsComputationDAG (fftEdge 1) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last 1)) ∧
    HasCompleteCalculation (fftEdge 1) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last 1)) 3 4 :=
  ⟨fft_isComputationDAG le_rfl, twoPoint_calc⟩

/-- The whole 2-point FFT graph as one part is a 6-partition: the inputs dominate it, and it has
four vertices in all. -/
private theorem twoPoint_onePart : IsPartition (fftEdge 1) (Finset.univ.filter (·.1 = 0)) (2 * 3)
    (![Finset.univ] : Fin 1 → Finset (Fin 2 × Fin 2)) := by
  classical
  refine ⟨⟨fun v => ⟨0, by simp, fun j _ => Subsingleton.elim _ _⟩, fun i =>
    ⟨Finset.univ.filter (·.1 = 0), by decide, fun x hx hxD => absurd hx hxD⟩,
    fun i j _ _ _ _ _ => by simp [Subsingleton.elim i j]⟩, fun i => ?_⟩
  calc _ ≤ (Finset.univ : Finset (Fin 2 × Fin 2)).card := Finset.card_le_univ _
    _ ≤ 2 * 3 := by decide

-- What Theorem 3.1 promises there, `4 ≤ 3h ≤ 7`, so `h = 2`: the whole graph and an empty part.
example : ∃ P : Fin 2 → Finset (Fin 2 × Fin 2),
    IsPartition (fftEdge 1) (Finset.univ.filter (·.1 = 0)) (2 * 3) P ∧
      4 ≤ 3 * 2 ∧ 3 * 2 ≤ 4 + 3 := by
  classical
  obtain ⟨⟨hcov, hdom, -⟩, hmin⟩ := twoPoint_onePart
  refine ⟨![Finset.univ, ∅], ⟨⟨fun v => ⟨0, by simp, fun j hj => ?_⟩, fun i => ?_,
    fun i j u hu v hv _ => ?_⟩, fun i => ?_⟩, by norm_num, by norm_num⟩
  · fin_cases j
    · rfl
    · simp at hj
  · fin_cases i
    · exact hdom 0
    · exact ⟨∅, by simp, fun _ _ _ w hw => by simp at hw⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i
    · exact hmin 0
    · simp

-- `P(6) = 1` at the 2-point FFT: the least number of parts is genuine there, not `sInf ∅`.
example : minParts (fftEdge 1) (Finset.univ.filter (·.1 = 0)) (2 * 3) = 1 := by
  refine le_antisymm (Nat.sInf_le ⟨_, twoPoint_onePart⟩) (Nat.one_le_iff_ne_zero.2 fun h0 => ?_)
  rcases Nat.sInf_eq_zero.1 h0 with ⟨P, hP⟩ | hempty
  · obtain ⟨i, -⟩ := hP.1.1 ((0 : Fin 2), (0 : Fin 2))
    exact i.elim0
  · exact Set.eq_empty_iff_forall_notMem.1 hempty 1 ⟨_, twoPoint_onePart⟩

-- Theorem 4.1's bound is attained at `S = 1`: the 2-point FFT needs `P_D(1) = 4` parts, one per
-- vertex, and `fft_parts_lower_bound` demands `2 · 2 ≤ h · 1 · log₂ 2`.
example : minDominatorParts (fftEdge 1) (Finset.univ.filter (·.1 = 0)) 1 = 4 := by
  obtain ⟨P, hP⟩ := fft_exists_isDominatorPartition 1 le_rfl
  have hle : minDominatorParts (fftEdge 1) (Finset.univ.filter (·.1 = 0)) 1 ≤ (1 + 1) * 2 ^ 1 :=
    Nat.sInf_le ⟨P, hP⟩
  refine le_antisymm (hle.trans (by norm_num)) ?_
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin (minDominatorParts (fftEdge 1) (Finset.univ.filter (·.1 = 0)) 1) →
      Finset (Fin 2 × Fin 2), IsDominatorPartition (fftEdge 1) (Finset.univ.filter (·.1 = 0)) 1 Q :=
    Nat.sInf_mem (s := {h | ∃ Q : Fin h → Finset (Fin 2 × Fin 2),
      IsDominatorPartition (fftEdge 1) (Finset.univ.filter (·.1 = 0)) 1 Q}) ⟨_, P, hP⟩
  have h := fft_parts_lower_bound le_rfl hQ
  norm_num [Real.logb_self_eq_one] at h
  exact_mod_cast h

/-! ### Each graph hypothesis of the key lemma carries weight

Drop any one of the four fields of `IsComputationDAG`, keep the other three, and a small graph has a
complete calculation for which the conclusion of Theorem 3.1 fails. All four fail the same way: a
part's dominator must contain the part's inputs (`mem_of_dominates_input`), so an `S`-dominator
partition with `h` parts has at most `h S` inputs (`card_inputs_le`), and here there are more
inputs than `2 (q + S)` (`not_conclusion`). The first is the paper's own setting, where the inputs
may be any set containing the sources: it is why the printed Theorem 3.1 is false. -/

private theorem mem_of_dominates_input {V : Type*} {E : V → V → Prop} {I D W : Finset V} {x : V}
    (hD : Dominates E I D W) (hxI : x ∈ I) (hxW : x ∈ W) : x ∈ D := by
  by_contra hxD
  exact hD x hxI hxD x hxW Relation.ReflTransGen.refl

private theorem card_inputs_le {V : Type*} {E : V → V → Prop} {I : Finset V} {S h : ℕ}
    {P : Fin h → Finset V} (hP : IsDominatorPartition E I S P) : I.card ≤ h * S := by
  classical
  obtain ⟨hcov, hdom, -⟩ := hP
  choose D hDcard hD using hdom
  have hsub : I ⊆ Finset.univ.biUnion fun i => D i := by
    intro x hx
    obtain ⟨i, hi, -⟩ := hcov x
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, mem_of_dominates_input (hD i) hx hi⟩
  calc I.card ≤ (Finset.univ.biUnion fun i => D i).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (D i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin h, S := Finset.sum_le_sum fun i _ => hDcard i
    _ = h * S := by simp

private theorem not_conclusion {V : Type*} {E : V → V → Prop} {I : Finset V} {S q : ℕ}
    (hS : 1 ≤ S) (hI : 2 * (q + S) < I.card) :
    ¬ ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S := by
  rintro ⟨h, P, hP, -, hh⟩
  have h1 := card_inputs_le hP.1
  have h2 : S * I.card ≤ S * (2 * (q + S)) := by
    calc S * I.card ≤ S * (h * (2 * S)) := Nat.mul_le_mul_left _ h1
      _ = 2 * S * (S * h) := by ring
      _ ≤ 2 * S * (q + S) := Nat.mul_le_mul_left _ hh
      _ = S * (2 * (q + S)) := by ring
  have := Nat.le_of_mul_le_mul_left h2 (by omega)
  omega

private theorem acyclic_of_potential {V : Type*} {E : V → V → Prop} (f : V → ℕ)
    (hf : ∀ u v, E u v → f u < f v) : ∀ v, ¬ Relation.TransGen E v v := by
  have key : ∀ u v, Relation.TransGen E u v → f u < f v := by
    intro u v h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact ih.trans (hf _ _ h)
  exact fun v h => (key v v h).false

/-- A chain `0 → 1 → ⋯ → 9`. -/
private def chainE (u v : Fin 10) : Prop := (v : ℕ) = u + 1
private instance : DecidableRel chainE := fun u v => by unfold chainE; infer_instance

-- Drop `inputs_eq_sources`: nine designated inputs `0, …, 8` in a chain, feeding the output `9`.
-- With `S = 2` the calculation loads `8` alone, computes and stores `9`: `q = 2`.
example : (∀ v, ¬ Relation.TransGen chainE v v) ∧
    (∀ v, (∀ w, ¬ chainE v w) → v ∈ ({9} : Finset (Fin 10))) ∧
    Disjoint (Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9)) {9} ∧
    ¬ (∀ v, v ∈ Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9) ↔ ∀ u, ¬ chainE u v) ∧
    HasCompleteCalculation chainE (Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9)) {9} 2 2 ∧
    ¬ ∃ (h : ℕ) (P : Fin h → Finset (Fin 10)),
      IsPartition chainE (Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9)) (2 * 2) P ∧
        2 ≤ 2 * h ∧ 2 * h ≤ 2 + 2 := by
  refine ⟨acyclic_of_potential (fun v => v) fun u v h => by unfold chainE at h; omega,
    by decide, by decide, by decide, ?_, not_conclusion (by norm_num) (by decide)⟩
  exact ⟨14, ![(∅, Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9)),
    ({8}, Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9)),
    ({8, 9}, Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9)),
    ({8, 9}, insert 9 (Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9))),
    ({8}, insert 9 (Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9))),
    (∅, insert 9 (Finset.univ.filter (fun v : Fin 10 => (v : ℕ) < 9))),
    (∅, {1, 2, 3, 4, 5, 6, 7, 8, 9}),
    (∅, {2, 3, 4, 5, 6, 7, 8, 9}),
    (∅, {3, 4, 5, 6, 7, 8, 9}),
    (∅, {4, 5, 6, 7, 8, 9}),
    (∅, {5, 6, 7, 8, 9}),
    (∅, {6, 7, 8, 9}),
    (∅, {7, 8, 9}),
    (∅, {8, 9}),
    (∅, {9})], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], by decide⟩

/-- Three vertices `0, 1, 2` feeding a fourth, `3`. -/
private def sinkE (u v : Fin 4) : Prop := v = 3 ∧ u ≠ 3
private instance : DecidableRel sinkE := fun u v => by unfold sinkE; infer_instance

-- Drop `sinks_subset_outputs`: the sink `3` is not an output, and nothing need be computed. With
-- `S = 1` the calculation only deletes blue pebbles: `q = 0`.
example : (∀ v, ¬ Relation.TransGen sinkE v v) ∧
    (∀ v, v ∈ ({0, 1, 2} : Finset (Fin 4)) ↔ ∀ u, ¬ sinkE u v) ∧
    Disjoint ({0, 1, 2} : Finset (Fin 4)) ∅ ∧
    ¬ (∀ v, (∀ w, ¬ sinkE v w) → v ∈ (∅ : Finset (Fin 4))) ∧
    HasCompleteCalculation sinkE {0, 1, 2} ∅ 1 0 ∧
    ¬ ∃ (h : ℕ) (P : Fin h → Finset (Fin 4)),
      IsPartition sinkE {0, 1, 2} (2 * 1) P ∧ 0 ≤ 1 * h ∧ 1 * h ≤ 0 + 1 := by
  refine ⟨acyclic_of_potential (fun v => if v = 3 then 1 else 0) fun u v h => by
      unfold sinkE at h; simp [h.1, h.2], by decide, by decide, by decide, ?_,
    not_conclusion le_rfl (by decide)⟩
  exact ⟨3, ![(∅, {0, 1, 2}), (∅, {1, 2}), (∅, {2}), (∅, ∅)], ![0, 0, 0], by decide⟩

/-- No edges at all. -/
private def noE (_ _ : Fin 3) : Prop := False
private instance : DecidableRel noE := fun _ _ => isFalse id

-- Drop `disjoint`: three isolated vertices, each an input and an output. With `S = 1` the
-- calculation makes no move: `q = 0`.
example : (∀ v, ¬ Relation.TransGen noE v v) ∧
    (∀ v, v ∈ (Finset.univ : Finset (Fin 3)) ↔ ∀ u, ¬ noE u v) ∧
    (∀ v, (∀ w, ¬ noE v w) → v ∈ (Finset.univ : Finset (Fin 3))) ∧
    ¬ Disjoint (Finset.univ : Finset (Fin 3)) Finset.univ ∧
    HasCompleteCalculation noE Finset.univ Finset.univ 1 0 ∧
    ¬ ∃ (h : ℕ) (P : Fin h → Finset (Fin 3)),
      IsPartition noE Finset.univ (2 * 1) P ∧ 0 ≤ 1 * h ∧ 1 * h ≤ 0 + 1 :=
  ⟨acyclic_of_potential (fun _ => 0) fun u v h => h.elim, by decide, by decide, by decide,
    ⟨0, fun _ => (∅, Finset.univ), Fin.elim0, by decide⟩, not_conclusion le_rfl (by decide)⟩

/-- Three vertices `0, 1, 2` feeding a two-cycle `3 ⇄ 4`. -/
private def cycE (u v : Fin 5) : Prop :=
  ((u : ℕ) < 3 ∧ v = 3) ∨ (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3)
private instance : DecidableRel cycE := fun u v => by unfold cycE; infer_instance

-- Drop `acyclic`: with no sink, no output is needed. With `S = 1` the calculation only deletes
-- blue pebbles: `q = 0`.
example : (∀ v, v ∈ ({0, 1, 2} : Finset (Fin 5)) ↔ ∀ u, ¬ cycE u v) ∧
    (∀ v, (∀ w, ¬ cycE v w) → v ∈ (∅ : Finset (Fin 5))) ∧
    Disjoint ({0, 1, 2} : Finset (Fin 5)) ∅ ∧
    ¬ (∀ v, ¬ Relation.TransGen cycE v v) ∧
    HasCompleteCalculation cycE {0, 1, 2} ∅ 1 0 ∧
    ¬ ∃ (h : ℕ) (P : Fin h → Finset (Fin 5)),
      IsPartition cycE {0, 1, 2} (2 * 1) P ∧ 0 ≤ 1 * h ∧ 1 * h ≤ 0 + 1 := by
  refine ⟨by decide, by decide, by decide, fun h => h 3 (Relation.TransGen.head (b := 4)
      (by decide) (Relation.TransGen.single (by decide))), ?_, not_conclusion le_rfl (by decide)⟩
  exact ⟨3, ![(∅, {0, 1, 2}), (∅, {1, 2}), (∅, {2}), (∅, ∅)], ![0, 0, 0], by decide⟩

end Sanity

end MiscMath.Computability
