/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
module

public import MiscMath.Computability.RedBluePebbleGame.Bounds
public import MiscMath.Computability.RedBluePebbleGame.Feasibility
public import MiscMath.Computability.RedBluePebbleGame.MatMulChain
public import MiscMath.Computability.RedBluePebbleGame.Parts
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Data.Fin.VecNotation

/-!
# Hong and Kung's red-blue pebble game: the key lemma, the FFT and matrix multiplication

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

**The FFT.** The **`n`-point FFT graph**, `n = 2^k`, has a vertex `(l, i)` for each level
`l = 0, …, k` and each lane `i = 0, …, n − 1`. Each vertex below the top level has edges to
`(l + 1, i)` and `(l + 1, i xor 2^l)`. The inputs are level `0` and the outputs level `k`. For it:

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

**Matrix multiplication.** The *ordinary algorithm* for the product of an `m × k` matrix `A` by a
`k × n` matrix `B` forms the `m k n` products `A i l · B l j`, and adds up the `k` products of each
entry `(i, j)` of the result. A computation DAG *evaluates* it (`IsMatMulEvaluation`) if some of
its vertices can be labelled so that:

* the entries of `A` and of `B` are `m k + k n` distinct inputs;
* each product `A i l · B l j` is a vertex of its own, with an edge from each of its two factors;
* no vertex can be reached from the products of two different entries of the result.

How the products are then combined, and in what order, are left free, as is anything else the
graph computes, subject to the third condition. For such graphs:

10. **Feasibility, and non-vacuity** (`exists_isMatMulEvaluation`). For all `m, k, n ≥ 1`, some
    such graph has a complete calculation exactly when `S ≥ 3`.
11. **The two bounds the argument gives** (`matMul_io_bounds`). For `k ≥ 1` and `S ≥ 1`,
    every complete calculation costs `q ≥ m k + k n + m n`, and `q ≥ m k n / √(2S) − S`.
12. **Corollary 6.2, with its constant** (`matMul_io_lower_bound`). Every complete calculation
    with at most `S` red pebbles, costing `q`, has `m k n ≤ 2 q √S`.
13. **Corollary 6.2 as the paper states it** (`matMul_io_lower_bound_isBigO`): `Q · √S = Ω(m k n)`.
    Over any collection of such graphs, one constant serves every graph of the collection and every
    `S` at which that graph has a complete calculation.

## How to read these statements

The twelve definitions they are stated through are in `RedBluePebbleGame/Spec.lean`, and they are
part of the read:

* the game: `Step` (the five moves, each labelled with its charge), `HasCompleteCalculation`,
  `fftEdge` and `minIOTime` (the paper's `Q`, as an infimum over `ℕ`);
* the key lemma: `IsComputationDAG`, `Dominates`, `IsDominatorPartition`, `IsPartition`, and
  `minParts` and `minDominatorParts` (the paper's `P(S)` and `P_D(S)`, as infima over `ℕ`);
* matrix multiplication: `IsMatMulLabelling` (which vertices are the entries and the products) and
  `IsMatMulEvaluation` (a computation DAG with such a labelling).

The FFT's inputs and outputs are written inline, as `Finset.univ.filter (·.1 = 0)` and
`Finset.univ.filter (·.1 = Fin.last k)`.

**The game and the FFT.**

* **The charges are part of the witness.** Two different moves can have the same effect. Take a
  vertex that is not an input and holds a blue pebble but no red one, whose predecessors all hold
  red pebbles. Putting a red pebble on it is then a load, charged `1`, and equally a computation,
  charged `0`: the configurations before and after are the same either way. A complete
  calculation records the charge of each move, so such a move may be charged `0`, and the bounds
  hold for the cheapest charging. In the source, too, the player chooses which rule to apply, and
  only loads and stores are counted.
* **Levels and lanes are compared as natural numbers.** They are elements of `Fin (k + 1)` and
  `Fin (2^k)`, whose own arithmetic wraps round. Compared as natural numbers, no edge leaves the
  top level; with `Fin` arithmetic, level `k + 1` would have been level `0`.
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
  `n log n / (S log S) = O(P_D(S))`. For matrix multiplication, `Q · √S = Ω(m k n)` becomes
  `m k n = O(Q · √S)`.
* **The FFT's asymptotic statements are uniform.** Their filters are principal, on
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
  - For `S ≥ 1` the two conjuncts together fix `h` to `⌈q/S⌉`, or to `q/S` or `q/S + 1` when `S`
    divides `q`.
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
  - Theorem 4.1 is stated at a general `S`, as in the paper, and the paper's Corollary 4.1 uses it
    at `2S`.
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

**Matrix multiplication.**

* **The class is what the proof uses, and it is wider than the paper's.** The paper proves
  Corollary 6.2 for *independent evaluations* (its E1 and E2). There the products are formed first,
  and each entry of the result is then summed from its own products by a tree of additions and
  subtractions; the trees of different entries share no vertex. `IsMatMulLabelling` asks only for
  what the proof needs.
  - For `m, k, n ≥ 1`, every independent evaluation is in the class, whatever the shapes of its
    trees and the order of its additions: everything reached from a product lies in the tree of its
    entry.
  - So is a chain of fused multiply-adds `s ← s + a · b`, each `s` standing for its product: a
    product may have predecessors besides its two factors.
  - An entry of `A` or `B` may have other successors, there may be inputs besides the entries, and
    the graph may compute other things too, within the limit below. `O` is constrained only by
    `IsComputationDAG`.
* **What the class leaves out.** The class is about the shape of the graph, which vertices feed
  which, and not about the operations at its vertices.
  - It leaves out any vertex reached from the products of two different entries of the result,
    such as a partial sum used by both: `independent` forbids it. Work before the products may
    still be shared: a vertex computed from `B 0 0` and `B 0 1` may feed the products of two
    entries.
  - It leaves out Strassen's `2 × 2` algorithm: a brute-force search over its graph finds no
    labelling at all.
* **The class is weak at degenerate sizes.** If `k = 0`, or `m = n = 0`, every computation DAG is
  in it. If `m = 0 < k, n`, the labelling asks only for `k n` distinct inputs, and `n = 0` is
  symmetric. In all these cases `m k n = 0`, so the bounds on `m k n` say nothing; the first bound
  of `matMul_io_bounds` still says `q ≥ k n` when `m = 0 < k, n`.
  - So `k ≥ 1` in `matMul_io_bounds` carries weight. Its first bound counts the `m n` outputs that
    the products reach, and with `k = 0` there are no products. The sanity checks show the bound
    failing at `k = 0`.
* **The hypotheses on `S` restrict nothing.**
  - A complete calculation of a graph in the class with `m k n ≥ 1` forces `S ≥ 3`: when a product
    is first computed, it and its two factors are red. So `matMul_io_lower_bound` needs no
    hypothesis on `S`.
  - In `matMul_io_bounds`, `S ≥ 1` keeps `√(2S)` visibly away from `0`. At `S = 0` a calculation
    exists only on the empty graph, where both bounds hold.
* **The second bound of `matMul_io_bounds` can say nothing.** Its left side is `≤ 0` exactly when
  `m k n ≤ S √(2S)`. There the first bound carries the claim, and `matMul_io_lower_bound` combines
  the two.
* **`exists_isMatMulEvaluation` is about one graph of each size.** It says that some graph of the
  class has a complete calculation exactly when `S ≥ 3`, not that every graph does. Every graph of
  the class with `m k n ≥ 1` needs `S ≥ 3`, and some need more. The graph its proof exhibits is the
  ordinary algorithm itself, each entry of the result summed left to right.
* **The asymptotic statement is about a collection of graphs.** One graph has one size, so the
  statement takes a collection, indexed by any type `ι`, in which graph `i` evaluates the product of
  an `m i × k i` matrix by a `k i × n i` matrix. It says there is one constant `C` with
  `m i · k i · n i ≤ C · Q_i(S) · √S` at every point `(i, S)` of its filter (`C = 2` works).
  - The constant is chosen after the collection. That loses nothing: a collection may hold every
    graph of the class, and then one constant covers the class.
  - The filter is principal, on the pairs `(i, S)` at which graph `i` has a complete calculation
    with `S` red pebbles. There `Q_i(S)` is a genuine minimum. The set is upward closed in `S`, and
    on it the right-hand side vanishes only for an empty graph.
  - Unlike the FFT's, the filter could not be `S ≥ 3`. A chain of fused multiply-adds with `k ≥ 2`
    needs four red pebbles. At `S = 3` it has no calculation, `Q` would take `minIOTime`'s value
    `0`, and the statement would be false.
  - The paper names no filter. This reading, uniform in the sizes and in `S`, is the strongest.

## Source

Hong Jia-Wei and H. T. Kung, *I/O Complexity: The Red-Blue Pebble Game*, Proceedings of the 13th
Annual ACM Symposium on Theory of Computing (STOC '81), pp. 326–333,
doi:10.1145/800076.802486; a scan is on H. T. Kung's page,
<https://www.eecs.harvard.edu/~htk/publication/1981-stoc-hong-kung.pdf>. Where things are:

* the game, its standing assumptions on the graph, and the definition of `Q`: §2, p. 327;
* `S`-partitions (P1–P4), Theorem 3.1 and its proof: §3, p. 328;
* `P(S)`, Lemma 3.1, `S`-dominator partitions, `P_D(S)`, Theorem 4.1 and its proof, and
  Corollary 4.1 ("`Q · log S = Ω(n log n)`"): §§3–4, p. 329;
* independent evaluations (E1, E2) and Theorem 6.1: §6, p. 330, with the proof of Theorem 6.1
  running on to p. 331;
* Lemma 6.1 and its proof, and Corollary 6.2 ("`Q · √S = Ω(mkn)`"): §6, p. 331.

Later restatements of the model, for comparison:

* V. Elango, F. Rastello, L.-N. Pouchet, J. Ramanujam and P. Sadayappan, *On characterizing the
  data movement complexity of computational DAGs for parallel execution* (2014), arXiv:1404.4767:
  the inputs are exactly the sources, and inputs cannot be computed, as here;
* P. A. Papp and R. Wattenhofer, *On the hardness of red-blue pebble games* (2020),
  arXiv:2005.08609: sources can be computed for free.

## Relation to Mathlib

Mathlib has no pebble games and no I/O complexity, and its `Digraph` is a bare adjacency
relation with no path API. The game, the key lemma and the matrix-multiplication graphs are
therefore stated through twelve new definitions, in `RedBluePebbleGame/Spec.lean`, which are part
of the read.

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
  left to right with `S = 3` costs one I/O, yet every `6`-partition of that graph has at least two
  sets, so the theorem demands at least three. Here `compute` requires `v ∉ I`, as in Elango et al.
  - The sanity checks show the condition carries weight: without designated inputs, the 2-point
    FFT costs 2 rather than 4.
* **Corrected: the inputs are exactly the sources.** The paper lets the inputs be any set
  containing the sources (§2), and uses that in §7. That too makes its Theorem 3.1 false.
  - A chain of 17 designated inputs feeding one output has a calculation costing 2 with `S = 2`,
    so the theorem allows at most 2 sets. Yet every `4`-partition has at least 3 (sanity checks).
  - That holds even if paths of length `0` are not counted in dominators. A dominator must then
    contain an end of every edge into its set, and the 17 edges need 9 such vertices, more than two
    dominators of 4 can hold.
* **Corrected in the proof: Theorem 3.1's cover argument.** The proof places each predecessor `u`
  of a vertex first made red in subcalculation `C_i`.
  - Its Case 1, `u` holding a pebble of either colour when `C_i` starts, puts `u` in an earlier
    set, on the grounds that every pebble follows a red one.
  - An input still holding its initial blue pebble has had no red one, so it lies in no earlier
    set.
  - Here the split is on a red pebble. Such an input then falls under the paper's Case 2, and the
    conclusion stands.
* **Corrected: Theorem 4.1's per-set bound.**
  - The paper bounds a set dominated by `d` vertices by `2d log d`. That is `0` at `d = 1`,
    although a vertex dominates itself, and its induction uses that case.
  - Here the bound is `d log₂ (2d)`, which is exact at `d = 1, 2, 4`.
  - So `fft_parts_lower_bound` carries `S log₂ (2S)`. Theorem 4.1's `Ω` form is unaffected.
* **Generalised: Corollary 6.2 is proved for a wider class of graphs.** The paper derives it from
  its Theorem 6.1, about independent evaluations. Here the class is cut down to what the proof
  uses; see above.
* **Convention: partitions are indexed families, and may have empty sets.** The paper's own
  construction needs them for `S h ≥ q`.
* **Convention: P4 is an ordering of the sets.** See above; nothing changes.
* **Convention: no move is a no-op.** A load onto a vertex already red is not a move, and nor are
  the like. This loses nothing: deleting a no-op from a calculation leaves one no dearer.
* **Convention: a computed pebble is placed, not slid.** Computing a vertex leaves its predecessors'
  red pebbles where they are. With sliding, two red pebbles would do for the FFT graph.
* **Two routes to Corollary 4.1.**
  - The paper's route goes through Theorem 3.1, Lemma 3.1 and Theorem 4.1, all stated and proved
    here.
  - The proof of Corollary 4.1 here does not use them. It cuts the calculation into windows of
    `S` loads and stores directly.
  - With the corrected Theorem 4.1 applied at `2S`, the paper's route gives the second bound of
    `fft_io_bounds`.
* **A different route to Lemma 6.1.** Both routes bound the products in one set of the partition.
  - The paper splits the rows of `A` at `√S` entries in the set's dominator.
  - Here the products with both factors in the dominator are counted slice by slice in the inner
    index `l`. Slice `l` has at most `min(2S, α_l β_l) ≤ √(2S) (α_l + β_l) / 2` of them, where
    `α_l` and `β_l` count the entries of column `l` of `A` and of row `l` of `B` in the dominator.
    The `2S` bounds the entries of the result the set meets, one vertex of its minimum set each.
  - That gives at most `S √(2S)` products per set.
* **Strengthened: explicit constants.**
  - Corollary 4.1's `Ω` gets the constant `1/5` (`fft_io_lower_bound`).
  - Theorem 4.1 gets `n (log₂ n + 1) ≤ h S log₂ (2S)`.
  - The FFT's two `Ω` forms are stated uniformly in `n` and `S`.
  - Corollary 6.2's `Ω` gets the constant `1/2` (`matMul_io_lower_bound`), and is stated uniformly
    in the sizes and `S`, over any collection of graphs of the class.
* **Added: `q ≥ 2n`, and `q ≥ m k + k n + m n`.** Every input is loaded and every output stored.
  The paper states neither, and for large `S` its step from Lemma 3.1 to Corollary 4.1 silently
  needs the first. Its route to Corollary 6.2 needs the second in the same way.
* **Omitted: everything else in the paper.** That includes:
  - Theorem 2.1, the matching upper bound, which the paper states without proof;
  - §§5, 7 and 8;
  - from §6: Theorem 6.1 for other expressions, with its `S`-combination number `H(S)`;
    Lemma 6.1 as stated; and Corollary 6.1, on matrix–vector products.

## Provenance

Result selected and specified by George A. Constantinides, who has read its advertised
statements on a best-effort basis, before any proof of them existed.

They are thirteen theorems:

* `exists_partition_of_hasCompleteCalculation`, `io_lower_bound_of_parts` and
  `minIOTime_lower_bound`;
* `fft_parts_lower_bound` and `fft_parts_lower_bound_isBigO`;
* `fft_complete_iff`, `fft_io_bounds`, `fft_io_lower_bound` and `fft_io_lower_bound_isBigO`;
* `exists_isMatMulEvaluation`, `matMul_io_bounds`, `matMul_io_lower_bound` and
  `matMul_io_lower_bound_isBigO`.

They are stated through twelve definitions in `RedBluePebbleGame/Spec.lean`: `Step`,
`HasCompleteCalculation`, `fftEdge`, `minIOTime`, `IsComputationDAG`, `Dominates`,
`IsDominatorPartition`, `IsPartition`, `minParts`, `minDominatorParts`, `IsMatMulLabelling` and
`IsMatMulEvaluation`.

The statements and their proofs were generated by Claude, and are kernel-verified and
axiom-audited; no human has read the proofs. Every other lemma and definition here is proof, and
may be read by no one. One machine read is on record, and its scope is stated exactly so that it
is not taken for more. On 2026-09-27 an independent review of commit `0c9bac9` by an OpenAI Codex
agent wrote down its own reading of the twelve definitions and thirteen statements before reading
this docstring or the paper, then compared it with both (pp. 327–331). It re-ran the build, a
fresh axiom audit, the import and convention guards, the frozen targets and their type check, and
an equivalent of the audit self-test. It reproduced, by computations of its own, the two
counterexamples to the printed Theorem 3.1, the exclusion of Strassen's algorithm and four of the
examples showing that a hypothesis cannot be dropped. It read `Spec.lean` whole and selected
declarations in six of the other ten modules under `RedBluePebbleGame/`, among them the repair of
the paper's cover argument in `Partition.lean`, but not every proof. It reported no false
advertised statement, no contradictory hypotheses and no unguarded junk value, and four errors in
the prose, corrected since. It ran no second kernel, and its build reused cached artifacts. It is
not a review, and a best-effort read is not one either — satisfy yourself that the statement says
what you need before relying on it. See the repository README.

The statements were written, read back and read before any proof existed. They were frozen in
three phases as `Target/RedBluePebbleGame.lean`:

* the FFT statements in commit `783e5a3`;
* the key lemma and Theorem 4.1 in commits `7c3c34d` and `d971e3f`;
* matrix multiplication in commit `0049cbf`.

`Target/RedBluePebbleGame/TypeCheck.lean` ascribes each frozen type to the theorem proved here, so
the two cannot differ while it builds; it is built by CI and by
`lake build RedBluePebbleGameTypeCheck`, not by `lake build`. Both read the definitions in
`Spec.lean`, which were frozen with the statements and have not changed since.

Before George's read, the advertised statements were read back blind. An agent was given them,
and the definitions they are stated through, and nothing else — no informal statement, no source,
no docstring. It rendered them into English, and the rendering was compared with the intended
statements. Each phase had two rounds:

* **Phase 1, round 1** surfaced that a move that could be either a load or a computation may be
  charged either way. The docstrings now say so.
* **Phase 1, round 2** followed the subtractive form of `fft_io_bounds` and the addition of the
  asymptotic statement. It surfaced two points, both now said above:
  - the second bound says nothing once `S ≥ n/2`;
  - the asymptotic statement itself implies a calculation exists wherever it applies.
* **Phase 2, round 1** surfaced that under the graph hypotheses `S ≤ 1` leaves only the empty
  graph. It also confirmed that empty sets make `q ≤ S h` free.
* **Phase 2, round 2** followed the gathering of the four graph hypotheses into
  `IsComputationDAG`. It surfaced that the conclusion of Theorem 3.1 fixes `h` almost exactly.
* **Phase 3, round 1** surfaced four points about the matrix-multiplication statements:
  - the asymptotic statement does not degenerate on its filter;
  - the filter is upward closed in `S`;
  - the class is weak at degenerate sizes, where the bounds on `m k n` say nothing;
  - the constant may depend on the whole collection, which may hold the whole class.
* **Phase 3, round 2** followed the folding of `IsComputationDAG` into `IsMatMulEvaluation`, and
  the restatement of `exists_isMatMulEvaluation` as an equivalence. It surfaced nothing new.

The points from Phases 2 and 3 are said above too. The renderings are kept verbatim in
`docs/readbacks/Computability/RedBluePebbleGame.md`, with the model that wrote them and the date.
-/

@[expose] public section

open Filter

namespace MiscMath.Computability

open RedBluePebbleGame

/-- **Hong and Kung's Theorem 3.1, corrected.** Every complete calculation of a computation DAG
with at most `S` red pebbles, charged `q`, comes with a `2S`-partition of the graph into `h` parts,
`q ≤ S h ≤ q + S`. -/
theorem exists_partition_of_hasCompleteCalculation {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q : ℕ} (hG : IsComputationDAG E I O)
    (hq : HasCompleteCalculation E I O S q) :
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S :=
  exists_isPartition hG hq

/-- **Hong and Kung's Lemma 3.1.** If every `2S`-partition of a computation DAG has at least `h₀`
parts, every complete calculation with at most `S` red pebbles is charged `q ≥ S (h₀ − 1)`. -/
theorem io_lower_bound_of_parts {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q h₀ : ℕ} (hG : IsComputationDAG E I O)
    (hparts : ∀ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P → h₀ ≤ h)
    (hq : HasCompleteCalculation E I O S q) :
    S * h₀ ≤ q + S := by
  obtain ⟨h, P, hP, -, hle⟩ := exists_partition_of_hasCompleteCalculation hG hq
  exact (Nat.mul_le_mul_left S (hparts h P hP)).trans hle

/-- **Hong and Kung's Lemma 3.1 as stated: `Q ≥ S (P(2S) − 1)`.** For a computation DAG with a
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

/-- **Feasibility.** The `2^k`-point FFT graph, `k ≥ 1`, has a complete calculation exactly when
at least three red pebbles are available. -/
theorem fft_complete_iff {k S : ℕ} (hk : 1 ≤ k) :
    (∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) ↔ 3 ≤ S :=
  ⟨fun ⟨_, h⟩ => three_le_of_fft_hasCompleteCalculation hk h, fft_hasCompleteCalculation⟩

/-- **The two bounds the argument gives.** For `k ≥ 1` and `S ≥ 1`, every complete calculation of
the `2^k`-point FFT graph, charged `q`, loads each input and stores each output, so
`q ≥ 2^(k+1)`; and `q ≥ 2^k (k + 1) / (2 log₂ (4S)) − S`, which says nothing once `S ≥ 2^(k-1)`. -/
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

/-- **Hong and Kung's Corollary 4.1, with its constant.** For `k ≥ 1`, every complete calculation of
the `2^k`-point FFT graph with `S ≥ 3` red pebbles, charged `q`, has `2^k · k ≤ 5 q log₂ S`. -/
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

/-- **Non-vacuity, and feasibility.** For all `m, k, n ≥ 1` some graph evaluates the ordinary
product of an `m × k` matrix by a `k × n` matrix (`IsMatMulEvaluation`) and has a complete
calculation exactly when at least three red pebbles are available. The graph the proof exhibits
is the ordinary algorithm itself, each entry of the product summed left to right. -/
theorem exists_isMatMulEvaluation {m k n : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∃ (V : Type) (_ : DecidableEq V) (_ : Finite V) (E : V → V → Prop) (I O : Finset V),
      IsMatMulEvaluation m k n E I O ∧ ∀ S, (∃ q, HasCompleteCalculation E I O S q) ↔ 3 ≤ S :=
  ⟨MatMulChain.Vertex m k n, inferInstance, inferInstance, MatMulChain.edge,
    MatMulChain.inputs m k n, MatMulChain.outputs m k n, MatMulChain.isMatMulEvaluation hm hn,
    MatMulChain.complete_iff hm hk hn⟩

/-- **The two bounds the argument gives.** For `k ≥ 1`, every complete calculation of a graph that
evaluates the ordinary product of an `m × k` matrix by a `k × n` matrix, charged `q`, loads each
entry of the two matrices and stores an output for each entry of the product, so
`q ≥ m k + k n + m n`; and for `S ≥ 1` red pebbles, `q ≥ m k n / √(2S) − S`. -/
theorem matMul_io_bounds {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {m k n S q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (hM : IsMatMulEvaluation m k n E I O) (hq : HasCompleteCalculation E I O S q) :
    m * k + k * n + m * n ≤ q ∧ (m * k * n : ℝ) / Real.sqrt (2 * S) - S ≤ q := by
  obtain ⟨hG, a, b, p, hL⟩ := hM
  refine ⟨add_le_of_isMatMulLabelling hG hL hk hq, ?_⟩
  have hS' : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hpos : 0 < Real.sqrt (2 * S) := Real.sqrt_pos.2 (by linarith)
  rw [sub_le_iff_le_add, div_le_iff₀ hpos]
  rcases Nat.eq_zero_or_pos (m * k * n) with h0 | hmkn
  · have h0' : (m * k * n : ℝ) = 0 := by exact_mod_cast h0
    rw [h0']
    positivity
  · have hm : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hmkn
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hmkn
    have h3 : 3 ≤ S := hL.three_le hG (⟨0, hm⟩, ⟨0, hk⟩, ⟨0, hn⟩) hq
    exact mul_le_of_isMatMulLabelling hG hL (by omega) hq

/-- **Hong and Kung's Corollary 6.2, with its constant.** Every complete calculation of a graph that
evaluates the ordinary product of an `m × k` matrix by a `k × n` matrix (`IsMatMulEvaluation`),
with at most `S` red pebbles and charged `q`, has `m k n ≤ 2 q √S`. -/
theorem matMul_io_lower_bound {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {m k n S q : ℕ} (hM : IsMatMulEvaluation m k n E I O)
    (hq : HasCompleteCalculation E I O S q) :
    (m * k * n : ℝ) ≤ 2 * q * Real.sqrt S := by
  obtain ⟨hG, a, b, p, hL⟩ := hM
  rcases Nat.eq_zero_or_pos (m * k * n) with h0 | hpos
  · have h0' : (m * k * n : ℝ) = 0 := by exact_mod_cast h0
    rw [h0']
    positivity
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hpos
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at hpos
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hpos
  have h3 : 3 ≤ S := hL.three_le hG (⟨0, hm⟩, ⟨0, hk⟩, ⟨0, hn⟩) hq
  have h1 := add_le_of_isMatMulLabelling hG hL hk hq
  have h2 := mul_le_of_isMatMulLabelling hG hL (by omega) hq
  have hS : (3 : ℝ) ≤ S := by exact_mod_cast h3
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hsS : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  rcases le_or_gt (3 * S) q with hbig | hsmall
  · -- Many loads and stores: `q + S ≤ 4q/3`, and `(4/3) √2 ≤ 2`.
    have hbig' : (3 : ℝ) * S ≤ q := by exact_mod_cast hbig
    have hr2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hkey : ((q : ℝ) + S) * Real.sqrt 2 ≤ 2 * q := by
      nlinarith [mul_le_mul_of_nonneg_left hr2 (by positivity : (0 : ℝ) ≤ q + S)]
    rw [Real.sqrt_mul (by norm_num)] at h2
    calc (m * k * n : ℝ) ≤ (q + S) * (Real.sqrt 2 * Real.sqrt S) := h2
      _ = ((q + S) * Real.sqrt 2) * Real.sqrt S := by ring
      _ ≤ (2 * q) * Real.sqrt S := mul_le_mul_of_nonneg_right hkey hsS
  · -- Few: each of `m k`, `k n` and `m n` is at most `q < 3S`, so `(m k n)² ≤ q³ < 4 q² S`.
    have hsmall' : (q : ℝ) < 3 * S := by exact_mod_cast hsmall
    have hx : ((m * k : ℕ) : ℝ) ≤ q := by exact_mod_cast (show m * k ≤ q by omega)
    have hy : ((k * n : ℕ) : ℝ) ≤ q := by exact_mod_cast (show k * n ≤ q by omega)
    have hz : ((m * n : ℕ) : ℝ) ≤ q := by exact_mod_cast (show m * n ≤ q by omega)
    have hxy : ((m * k : ℕ) : ℝ) * ((k * n : ℕ) : ℝ) ≤ q * q :=
      mul_le_mul hx hy (Nat.cast_nonneg _) hq0
    have hxyz : ((m * k : ℕ) : ℝ) * ((k * n : ℕ) : ℝ) * ((m * n : ℕ) : ℝ) ≤ q * q * q :=
      mul_le_mul hxy hz (Nat.cast_nonneg _) (mul_nonneg hq0 hq0)
    have hq3 : (q : ℝ) * q * q ≤ 3 * S * (q * q) := by
      nlinarith [mul_nonneg hq0 hq0]
    refine le_of_sq_le_sq ?_ (by positivity)
    have hsq : (2 * (q : ℝ) * Real.sqrt S) ^ 2 = 4 * (q * q) * S := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [hsq]
    push_cast at hxyz
    nlinarith [mul_nonneg (mul_nonneg hq0 hq0) (Nat.cast_nonneg S : (0 : ℝ) ≤ S)]

/-- **Hong and Kung's Corollary 6.2 as stated: `Q · √S = Ω(m k n)`.** For any collection of graphs,
the `i`-th evaluating the ordinary product of an `m i × k i` matrix by a `k i × n i` matrix, and
with `Q` the minimum I/O time, `m k n = O(Q · √S)` along the principal filter of the pairs `(i, S)`
at which graph `i` has a complete calculation with `S` red pebbles: one constant serves every graph
of the collection and every such `S`. -/
theorem matMul_io_lower_bound_isBigO {ι : Type*} {m k n : ι → ℕ} {W : ι → Type*}
    [∀ i, DecidableEq (W i)] [∀ i, Finite (W i)] {E : ∀ i, W i → W i → Prop}
    {I O : ∀ i, Finset (W i)} (hM : ∀ i, IsMatMulEvaluation (m i) (k i) (n i) (E i) (I i) (O i)) :
    (fun x : ι × ℕ => (m x.1 * k x.1 * n x.1 : ℝ))
      =O[𝓟 {x | ∃ q, HasCompleteCalculation (E x.1) (I x.1) (O x.1) x.2 q}]
      fun x => (minIOTime (E x.1) (I x.1) (O x.1) x.2 : ℝ) * Real.sqrt x.2 := by
  rw [Asymptotics.isBigO_principal]
  refine ⟨2, ?_⟩
  rintro ⟨i, S⟩ hx
  have hmem : HasCompleteCalculation (E i) (I i) (O i) S (minIOTime (E i) (I i) (O i) S) :=
    Nat.sInf_mem (s := {q | HasCompleteCalculation (E i) (I i) (O i) S q}) hx
  have hb := matMul_io_lower_bound (hM i) hmem
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
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
* **`k ≥ 1` cannot be dropped from `fft_io_bounds` or `fft_complete_iff`.** At `k = 0` the one
  vertex is both input and output, and the calculation with no moves costs nothing, with no red
  pebbles.
* **The input condition in `Step` carries weight.** Declare no inputs and the level-0 vertices are
  computed from nothing, so the 2-point FFT costs only its two stores. With the inputs declared,
  `fft_io_bounds` demands four.
* **The butterfly is the intended graph.** No edge leaves the top level and none enters level `0`,
  so nothing wraps round. At `k = 3` every vertex off level `0` has exactly two predecessors, and
  from level `1` to level `2` the paired lanes differ in bit `1`.

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

For matrix multiplication:

* **Non-vacuity.** `exists_isMatMulEvaluation` is itself the check for the other three
  statements. At every size `m, k, n ≥ 1` their hypotheses hold together with any `S ≥ 3`, and a
  family of its witnesses meets the hypothesis of the asymptotic statement with every `S ≥ 3` in
  its filter.
  - Here, besides, the `1 × 1 × 2` product is in the class, and `mm112_calc` is a complete
    calculation of it with three red pebbles and five loads and stores, checked move by move by
    `decide`. It has two entries, so `independent` says something there.
* **The first bound is attained.** At that point `minIOTime` is exactly `5 = 1 · 1 + 1 · 2 + 1 · 2`:
  at most `5` by the calculation, at least `5` by `matMul_io_bounds`.
* **`k ≥ 1` cannot be dropped from `matMul_io_bounds`.** With `k = 0` the labelling says nothing,
  so the graph with one edge evaluates the `2 × 0 × 2` product. It costs `2`, where the first bound
  would demand `4`.
* **`independent` carries weight.** Add the two products of the `1 × 1 × 2` product into a sixth
  vertex, and every other field of `IsMatMulLabelling` still holds. Four red pebbles then give a
  calculation costing `4`, below the first bound's `5`.
* **Other fields carry weight too, at larger sizes.** This was checked by brute force, not here.
  - Drop one of `independent`, `injective_a`, `a_mem` and `edge_a`, and keep everything else.
    Then some graph has a calculation, checked move by move, that breaks both
    `matMul_io_lower_bound` and the second bound of `matMul_io_bounds`. The matrices are square, of
    sizes 30 to 100.
  - By symmetry the same holds for the fields of `B`.
  - No such example is known for `injective_p` or `disjoint_ab`.
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

/-- A chain `0 → 1 → ⋯ → 17`. -/
private def chainE (u v : Fin 18) : Prop := (v : ℕ) = u + 1
private instance : DecidableRel chainE := fun u v => by unfold chainE; infer_instance

-- Drop `inputs_eq_sources`: seventeen designated inputs `0, …, 16` in a chain, feeding the output
-- `17`. With `S = 2` the calculation loads `16` alone, computes and stores `17`: `q = 2`. Seventeen
-- rather than fewer, so that the chain also refutes the paper's Theorem 3.1 if its dominators
-- ignore paths of length `0` (see "Where this differs").
example : (∀ v, ¬ Relation.TransGen chainE v v) ∧
    (∀ v, (∀ w, ¬ chainE v w) → v ∈ ({17} : Finset (Fin 18))) ∧
    Disjoint (Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17)) {17} ∧
    ¬ (∀ v, v ∈ Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17) ↔ ∀ u, ¬ chainE u v) ∧
    HasCompleteCalculation chainE (Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17)) {17} 2 2 ∧
    ¬ ∃ (h : ℕ) (P : Fin h → Finset (Fin 18)),
      IsPartition chainE (Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17)) (2 * 2) P ∧
        2 ≤ 2 * h ∧ 2 * h ≤ 2 + 2 := by
  refine ⟨acyclic_of_potential (fun v => v) fun u v h => by unfold chainE at h; omega,
    by decide, by decide, by decide, ?_, not_conclusion (by norm_num) (by decide)⟩
  exact ⟨22, ![(∅, Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17)),
    ({16}, Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17)),
    ({16, 17}, Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17)),
    ({16, 17}, insert 17 (Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17))),
    ({17}, insert 17 (Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17))),
    (∅, insert 17 (Finset.univ.filter (fun v : Fin 18 => (v : ℕ) < 17))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 1 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 2 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 3 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 4 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 5 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 6 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 7 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 8 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 9 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 10 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 11 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 12 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 13 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 14 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 15 ≤ (v : ℕ))),
    (∅, Finset.univ.filter (fun v : Fin 18 => 16 ≤ (v : ℕ))),
    (∅, {17})],
    ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], by decide⟩

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

/-! ### Matrix multiplication -/

/-- The graph of the `1 × 1 × 2` product: `0 = A 0 0`, `1 = B 0 0`, `2 = B 0 1`,
`3 = A 0 0 * B 0 0` and `4 = A 0 0 * B 0 1`. With `k = 1` there are no additions: each product is an
entry of the result. -/
private def mm112E (u v : Fin 5) : Prop :=
  (u = 0 ∧ v = 3) ∨ (u = 1 ∧ v = 3) ∨ (u = 0 ∧ v = 4) ∨ (u = 2 ∧ v = 4)
private instance : DecidableRel mm112E := fun u v => by unfold mm112E; infer_instance

/-- From a vertex with no successor, a path reaches only the vertex itself. -/
private theorem reach_eq_of_sink {V : Type*} {E : V → V → Prop} {x w : V} (hx : ∀ y, ¬ E x y)
    (h : Relation.ReflTransGen E x w) : w = x := by
  induction h with
  | refl => rfl
  | tail _ h ih => subst ih; exact absurd h (hx _)

/-- The `1 × 1 × 2` product is in the class, with `A 0 0 ↦ 0`, `B 0 j ↦ 1 + j` and
`A 0 0 * B 0 j ↦ 3 + j`. Its two entries make `independent` say something. -/
private theorem mm112_eval : IsMatMulEvaluation 1 1 2 mm112E {0, 1, 2} {3, 4} := by
  refine ⟨⟨acyclic_of_potential (fun v => v) fun u v h => by unfold mm112E at h; omega,
    by decide, by decide, by decide⟩, fun _ => 0, fun x => if x.2 = 0 then 1 else 2,
    fun x => if x.2.2 = 0 then 3 else 4,
    ⟨by decide, by decide, by decide, ?_, by decide, by decide, by decide, by decide, ?_⟩⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact (by decide : ∀ x : Fin 1 × Fin 1, ∀ y : Fin 1 × Fin 2,
      (if y.2 = 0 then (1 : Fin 5) else 2) ≠ 0) x y hy
  · intro i l j i' l' j' w h h'
    have hs : ∀ x : Fin 1 × Fin 1 × Fin 2, ∀ y, ¬ mm112E (if x.2.2 = 0 then 3 else 4) y := by
      decide
    have e := (reach_eq_of_sink (hs _) h).symm.trans (reach_eq_of_sink (hs _) h')
    exact (by decide : ∀ x y : Fin 1 × Fin 1 × Fin 2, (if x.2.2 = 0 then (3 : Fin 5) else 4) =
      (if y.2.2 = 0 then 3 else 4) → x.1 = y.1 ∧ x.2.2 = y.2.2) (i, l, j) (i', l', j') e

/-- The `1 × 1 × 2` product with three red pebbles: load `A 0 0` and `B 0 0`, compute and store the
first product, drop it and `B 0 0`, load `B 0 1`, compute and store the second, then clear up.
Five loads and stores. -/
private theorem mm112_calc : HasCompleteCalculation mm112E {0, 1, 2} {3, 4} 3 5 :=
  ⟨15, ![(∅, {0, 1, 2}), ({0}, {0, 1, 2}), ({0, 1}, {0, 1, 2}), ({0, 1, 3}, {0, 1, 2}),
      ({0, 1, 3}, {0, 1, 2, 3}), ({0, 1}, {0, 1, 2, 3}), ({0}, {0, 1, 2, 3}),
      ({0, 2}, {0, 1, 2, 3}), ({0, 2, 4}, {0, 1, 2, 3}), ({0, 2, 4}, {0, 1, 2, 3, 4}),
      ({2, 4}, {0, 1, 2, 3, 4}), ({4}, {0, 1, 2, 3, 4}), (∅, {0, 1, 2, 3, 4}),
      (∅, {1, 2, 3, 4}), (∅, {2, 3, 4}), (∅, {3, 4})],
    ![1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], by decide⟩

-- Non-vacuity at a size with two entries: the hypotheses of `matMul_io_lower_bound` and of
-- `matMul_io_bounds` hold together at `1 × 1 × 2`, `S = 3`, `q = 5`.
example : 1 ≤ 1 ∧ 1 ≤ 3 ∧ IsMatMulEvaluation 1 1 2 mm112E {0, 1, 2} {3, 4} ∧
    HasCompleteCalculation mm112E {0, 1, 2} {3, 4} 3 5 :=
  ⟨le_rfl, by norm_num, mm112_eval, mm112_calc⟩

-- The first bound of `matMul_io_bounds`, `q ≥ 1 · 1 + 1 · 2 + 1 · 2 = 5`, is attained there, and
-- `minIOTime` is a genuine minimum.
example : minIOTime mm112E {0, 1, 2} {3, 4} 3 = 5 := by
  refine le_antisymm (Nat.sInf_le mm112_calc) ?_
  have hmem : HasCompleteCalculation mm112E {0, 1, 2} {3, 4} 3
      (minIOTime mm112E {0, 1, 2} {3, 4} 3) :=
    Nat.sInf_mem (s := {q | HasCompleteCalculation mm112E {0, 1, 2} {3, 4} 3 q}) ⟨5, mm112_calc⟩
  exact (matMul_io_bounds le_rfl (by norm_num) mm112_eval hmem).1

/-- One edge, `0 → 1`. -/
private def edgeE (u v : Fin 2) : Prop := u = 0 ∧ v = 1
private instance : DecidableRel edgeE := fun u v => by unfold edgeE; infer_instance

-- `1 ≤ k` cannot be dropped from `matMul_io_bounds`: with `k = 0` the labelling says nothing, so
-- the one-edge graph evaluates the `2 × 0 × 2` product. Load, compute, store: `q = 2`, where the
-- first bound would demand `2 · 0 + 0 · 2 + 2 · 2 = 4`.
example : IsMatMulEvaluation 2 0 2 edgeE {0} {1} ∧ HasCompleteCalculation edgeE {0} {1} 2 2 ∧
    ¬ 2 * 0 + 0 * 2 + 2 * 2 ≤ 2 :=
  ⟨⟨⟨acyclic_of_potential (fun v => v) fun u v h => by unfold edgeE at h; omega,
      by decide, by decide, by decide⟩,
    fun x => x.2.elim0, fun x => x.1.elim0, fun x => x.2.1.elim0,
    ⟨fun x => x.2.elim0, fun x => x.1.elim0, fun x => x.2.1.elim0,
      Set.disjoint_left.2 fun _ ⟨x, _⟩ => x.2.elim0, fun x => x.2.elim0, fun x => x.1.elim0,
      fun _ l => l.elim0, fun _ l => l.elim0, fun _ l => l.elim0⟩⟩,
    ⟨6, ![(∅, {0}), ({0}, {0}), ({0, 1}, {0}), ({0, 1}, {0, 1}), ({1}, {0, 1}), (∅, {0, 1}),
      (∅, {1})], ![1, 0, 1, 0, 0, 0], by decide⟩, by norm_num⟩

/-- The `1 × 1 × 2` product with its two products added into a sixth vertex `5`, the only output. -/
private def mm112SumE (u v : Fin 6) : Prop :=
  (u = 0 ∧ v = 3) ∨ (u = 1 ∧ v = 3) ∨ (u = 0 ∧ v = 4) ∨ (u = 2 ∧ v = 4) ∨ (u = 3 ∧ v = 5) ∨
    (u = 4 ∧ v = 5)
private instance : DecidableRel mm112SumE := fun u v => by unfold mm112SumE; infer_instance

/-- The labelling of `mm112E`, on six vertices. -/
private def sumA (_ : Fin 1 × Fin 1) : Fin 6 := 0
private def sumB (x : Fin 1 × Fin 2) : Fin 6 := if x.2 = 0 then 1 else 2
private def sumP (x : Fin 1 × Fin 1 × Fin 2) : Fin 6 := if x.2.2 = 0 then 3 else 4

-- `independent` carries weight. With the two products added into one vertex, the graph is a
-- computation DAG and every other field of `IsMatMulLabelling` holds, but `independent` fails. Then
-- four red pebbles give a calculation with three loads and one store, `q = 4`, where the first
-- bound of `matMul_io_bounds` demands `5`.
example : IsComputationDAG mm112SumE {0, 1, 2} {5} ∧
    Function.Injective sumA ∧ Function.Injective sumB ∧ Function.Injective sumP ∧
    Disjoint (Set.range sumA) (Set.range sumB) ∧ (∀ x, sumA x ∈ ({0, 1, 2} : Finset (Fin 6))) ∧
    (∀ x, sumB x ∈ ({0, 1, 2} : Finset (Fin 6))) ∧
    (∀ i l j, mm112SumE (sumA (i, l)) (sumP (i, l, j))) ∧
    (∀ i l j, mm112SumE (sumB (l, j)) (sumP (i, l, j))) ∧
    ¬ (∀ i l j i' l' j' w, Relation.ReflTransGen mm112SumE (sumP (i, l, j)) w →
      Relation.ReflTransGen mm112SumE (sumP (i', l', j')) w → i = i' ∧ j = j') ∧
    HasCompleteCalculation mm112SumE {0, 1, 2} {5} 4 4 ∧ ¬ 1 * 1 + 1 * 2 + 1 * 2 ≤ 4 := by
  refine ⟨⟨acyclic_of_potential (fun v => v) fun u v h => by unfold mm112SumE at h; omega,
      by decide, by decide, by decide⟩, by decide, by decide, by decide, ?_, by decide, by decide,
    by decide, by decide, fun h => ?_, ?_, by norm_num⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact (by decide : ∀ x : Fin 1 × Fin 1, ∀ y : Fin 1 × Fin 2, sumB y ≠ sumA x) x y hy
  · exact absurd (h 0 0 0 0 0 1 5 (.single (by decide)) (.single (by decide))).2 (by decide)
  · exact ⟨16, ![(∅, {0, 1, 2}), ({0}, {0, 1, 2}), ({0, 1}, {0, 1, 2}), ({0, 1, 3}, {0, 1, 2}),
      ({0, 3}, {0, 1, 2}), ({0, 2, 3}, {0, 1, 2}), ({0, 2, 3, 4}, {0, 1, 2}),
      ({2, 3, 4}, {0, 1, 2}), ({3, 4}, {0, 1, 2}), ({3, 4, 5}, {0, 1, 2}),
      ({3, 4, 5}, {0, 1, 2, 5}), ({4, 5}, {0, 1, 2, 5}), ({5}, {0, 1, 2, 5}),
      (∅, {0, 1, 2, 5}), (∅, {1, 2, 5}), (∅, {2, 5}), (∅, {5})],
      ![1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], by decide⟩

end Sanity

end MiscMath.Computability
