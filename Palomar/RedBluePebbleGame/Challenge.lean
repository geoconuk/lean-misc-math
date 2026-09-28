/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fintype.Prod

/-!
# Hong and Kung's red-blue pebble game — advertised statements

This is the statement surface of the submission: the declarations a mathematical reader is asked
to audit. The proofs are in `MiscMath.Computability.RedBluePebbleGame`, which is the Solution module
of the accompanying Comparator configuration and is the file the library actually ships; its proofs
rest on the support modules beneath it. The `sorry`s below are the deliberate holes Comparator
fills.

Mathlib has no pebble games, so the statements are made about twelve definitions of the
formalisation's own. A Challenge may import nothing but Mathlib (with Lean core, Tau Ceti and
CSLib), so the definitions are restated in this file: verbatim from
`MiscMath/Computability/RedBluePebbleGame/Spec.lean`, docstrings included, and in the namespace the
library declares them in. They are not holes, and the Comparator configuration's
`definition_names` is empty. Comparator checks that every declaration a compared statement uses is
the same declaration in the Challenge and in the Solution, so the definitions read here are the
ones the library's theorems are about.

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

The twelve definitions they are stated through are restated below, and they are part of the read:

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
  inputs be any set containing the sources; here they are exactly the sources. The Solution
  module's sanity checks show that each of its four conditions carries weight. Together they rule
  out isolated vertices.
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
    the products reach, and with `k = 0` there are no products. The Solution module's sanity
    checks show the bound failing at `k = 0`.
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
therefore stated through twelve new definitions, which are part of the read. This file restates
them, so that it imports nothing but Mathlib.

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
  - The Solution module's sanity checks show the condition carries weight: without designated
    inputs, the 2-point FFT costs 2 rather than 4.
* **Corrected: the inputs are exactly the sources.** The paper lets the inputs be any set
  containing the sources (§2), and uses that in §7. That too makes its Theorem 3.1 false.
  - A chain of 17 designated inputs feeding one output has a calculation costing 2 with `S = 2`,
    so the theorem allows at most 2 sets. Yet every `4`-partition has at least 3 (the
    Solution module's sanity checks).
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
* **Corrected in the proof: Theorem 4.1's induction.**
  - The paper claims, for `S ≥ 2`, that a set with a dominator of at most `S` vertices has at
    most `2S log S` vertices, and that holds. But its induction applies the bound to the parts
    of a dominator, which may have a single vertex, and at `1` it is `0`, although a vertex
    dominates itself.
  - Here the bound is `d log₂ (2d)`, for a dominator of `d` vertices. It holds at `d = 1` too,
    which closes the induction; it is at most `2d log₂ d` for `d ≥ 2`; and it is exact at
    `d = 1, 2, 4`.
  - So `fft_parts_lower_bound` carries `S log₂ (2S)`, for every `S ≥ 1`. Theorem 4.1 as the paper
    states it, for `S ≥ 2`, is unaffected.
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
  - With `fft_parts_lower_bound` applied at `2S`, the paper's route gives the second bound of
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

Selected and specified by George A. Constantinides, who read the thirteen statements and the
twelve definitions on a best-effort basis before any proof of them existed. They are restated here
unchanged. The definitions, the statements and the proofs were generated by Claude (Anthropic), and
the proofs are kernel-verified and axiom-audited; no human has read them. `formalization.yaml` and
the Solution module's `## Provenance` give the full account, including a blind read-back of the
statements and one machine read, with exactly what it covered.
-/

@[expose] public section

namespace MiscMath.Computability.RedBluePebbleGame

variable {V : Type*} [DecidableEq V]

/-- One move of the red-blue pebble game on the directed graph with edge relation `E` (an edge
`E u v` runs from `u` to `v`, so the predecessors of `v` are the `u` with `E u v`) and
designated inputs `I`. A configuration is a pair `(R, B)`: the vertices holding a red pebble
(fast memory) and those holding a blue pebble (slow memory). `Step E I (R, B) c (R', B')` says
that one move leads from `(R, B)` to `(R', B')` and is charged `c` I/O operations.

There are exactly five moves, and none of them is a no-op. Loading and storing copy a value
without removing the pebble of the other colour, so a vertex may hold both. The red-pebble
budget is not part of a move: `HasCompleteCalculation` imposes it on every configuration of a
run.

A move is not always recoverable from the two configurations. Loading a vertex that could also
be computed leads to the same configuration as computing it; the charge says which move was
made. -/
inductive Step (E : V → V → Prop) (I : Finset V) :
    Finset V × Finset V → ℕ → Finset V × Finset V → Prop
  /-- **Load**, charged 1: put a red pebble on a vertex that has a blue one and no red one. -/
  | load {R B : Finset V} {v : V} (hB : v ∈ B) (hR : v ∉ R) :
      Step E I (R, B) 1 (insert v R, B)
  /-- **Store**, charged 1: put a blue pebble on a vertex that has a red one and no blue one. -/
  | store {R B : Finset V} {v : V} (hR : v ∈ R) (hB : v ∉ B) :
      Step E I (R, B) 1 (R, insert v B)
  /-- **Compute**, charged 0: put a red pebble on a vertex that is not an input and has no red
  pebble, once every predecessor of it has a red pebble. -/
  | compute {R B : Finset V} {v : V} (hI : v ∉ I) (hR : v ∉ R) (hpred : ∀ u, E u v → u ∈ R) :
      Step E I (R, B) 0 (insert v R, B)
  /-- **Delete a red pebble**, charged 0. -/
  | deleteRed {R B : Finset V} {v : V} (hR : v ∈ R) :
      Step E I (R, B) 0 (R.erase v, B)
  /-- **Delete a blue pebble**, charged 0. -/
  | deleteBlue {R B : Finset V} {v : V} (hB : v ∈ B) :
      Step E I (R, B) 0 (R, B.erase v)

/-- `HasCompleteCalculation E I O S q`: the red-blue pebble game on edge relation `E` can be
played from a blue pebble on every input in `I` and nothing else, to a blue pebble on every
output in `O` and nothing else, never holding more than `S` red pebbles at once, at a total
I/O charge of exactly `q`.

Spelled out: there are a number of moves `t`, configurations `σ 0, …, σ t` and charges
`c 0, …, c (t - 1)` such that `σ 0 = (∅, I)`, `σ t = (∅, O)`, every configuration — the first
and last included — has at most `S` red pebbles, each `σ i` leads to `σ (i + 1)` by a `Step`
charged `c i`, and the charges sum to `q`.

The charges are part of the witness, not a function of the configurations: where a step could
be either a load or a computation, `c i` records which it was. So one sequence of
configurations may be charged in more than one way, and a statement about every `q` for which
a calculation exists covers the cheapest charging.

It carries no acyclicity, source or sink conditions: those are properties of the graph a
theorem is about, and a theorem that needs them states them. -/
def HasCompleteCalculation (E : V → V → Prop) (I O : Finset V) (S q : ℕ) : Prop :=
  ∃ (t : ℕ) (σ : Fin (t + 1) → Finset V × Finset V) (c : Fin t → ℕ),
    σ 0 = (∅, I) ∧
    σ (Fin.last t) = (∅, O) ∧
    (∀ j, (σ j).1.card ≤ S) ∧
    (∀ i : Fin t, Step E I (σ i.castSucc) (c i) (σ i.succ)) ∧
    ∑ i, c i = q

/-- The edge relation of the `2^k`-point FFT graph (the butterfly). Its vertices are the pairs
`(l, i)` of a level `l ≤ k` and a lane `i < 2^k`. There is an edge from `(l, i)` to `(l + 1, i)`
and to `(l + 1, i xor 2^l)`, and no other. Levels and lanes are compared as natural numbers,
so no edge leaves level `k`: `Fin` addition would wrap it round to level `0`. The inputs are
level `0` and the outputs level `k`. -/
def fftEdge (k : ℕ) (u v : Fin (k + 1) × Fin (2 ^ k)) : Prop :=
  (v.1 : ℕ) = (u.1 : ℕ) + 1 ∧
    ((v.2 : ℕ) = (u.2 : ℕ) ∨ (v.2 : ℕ) = (u.2 : ℕ) ^^^ 2 ^ (u.1 : ℕ))

/-- The **minimum I/O time** `Q` of the source: the least total I/O charge of a complete
calculation on the graph `E` with at most `S` red pebbles, that is, the least number of loads
and stores any complete calculation needs.

Where no complete calculation exists the set is empty, and `sInf ∅ = 0` in `ℕ`. That value
means nothing, so a statement about `minIOTime` should only be made where a complete
calculation exists. -/
noncomputable def minIOTime (E : V → V → Prop) (I O : Finset V) (S : ℕ) : ℕ :=
  sInf {q | HasCompleteCalculation E I O S q}

omit [DecidableEq V] in
/-- `IsComputationDAG E I O`: the graph with edge relation `E`, inputs `I` and outputs `O`
satisfies the source's standing assumptions on the graph (§2), with the inputs restricted to the
sources. That restriction is a correction: the source lets the inputs be any set containing the
sources, and its Theorem 3.1 is false for some such sets. -/
structure IsComputationDAG (E : V → V → Prop) (I O : Finset V) : Prop where
  /-- No vertex reaches itself by a path of length at least `1`. -/
  acyclic : ∀ v, ¬ Relation.TransGen E v v
  /-- The inputs are exactly the vertices with no predecessor. -/
  inputs_eq_sources : ∀ v, v ∈ I ↔ ∀ u, ¬ E u v
  /-- Every vertex with no successor is an output. Other vertices may be outputs too. -/
  sinks_subset_outputs : ∀ v, (∀ w, ¬ E v w) → v ∈ O
  /-- No vertex is both an input and an output. -/
  disjoint : Disjoint I O

omit [DecidableEq V] in
/-- `Dominates E I D W`: in the graph with edge relation `E` and inputs `I`, the set `D`
*dominates* the set `W` — every path along `E` from an input to a vertex of `W` contains a vertex
of `D`. Paths of length `0` count, so an input in `W` must itself be in `D`.

Spelled out: for every input `x` outside `D` and every `w ∈ W`, there is no path from `x` to `w`
along edges both of whose endpoints lie outside `D`. That is, once the vertices of `D` are
deleted, no vertex of `W` can be reached from an input. -/
def Dominates (E : V → V → Prop) (I D W : Finset V) : Prop :=
  ∀ x ∈ I, x ∉ D → ∀ w ∈ W, ¬ Relation.ReflTransGen (fun a b => E a b ∧ a ∉ D ∧ b ∉ D) x w

omit [DecidableEq V] in
/-- `IsDominatorPartition E I S P`: the sets `P 0, …, P (h - 1)` form an `S`-*dominator
partition* of the graph with edge relation `E` and inputs `I`. That is:

* every vertex lies in exactly one of the sets;
* each set is dominated (`Dominates`) by some set of at most `S` vertices;
* an edge from a vertex of `P i` to a vertex of `P j` forces `i ≤ j`: edges between the sets run
  only from a set to a later one, though they may run inside a set.

Some of the sets may be empty, and each empty set counts towards `h`. -/
def IsDominatorPartition {h : ℕ} (E : V → V → Prop) (I : Finset V) (S : ℕ)
    (P : Fin h → Finset V) : Prop :=
  (∀ v, ∃! i, v ∈ P i) ∧
    (∀ i, ∃ D : Finset V, D.card ≤ S ∧ Dominates E I D (P i)) ∧
    ∀ i j, ∀ u ∈ P i, ∀ v ∈ P j, E u v → i ≤ j

omit [DecidableEq V] in
open Classical in
/-- `IsPartition E I S P`: the sets `P 0, …, P (h - 1)` form an `S`-*partition* of the graph with
edge relation `E` and inputs `I`. That is, they form an `S`-dominator partition
(`IsDominatorPartition`), and moreover each set has at most `S` vertices with no successor in the
same set. Those vertices make up the set's *minimum set*.

Counting them needs the property "no successor in the set" to be decidable, and it is decided
classically. Which decision procedure is used cannot change the count. -/
def IsPartition {h : ℕ} (E : V → V → Prop) (I : Finset V) (S : ℕ) (P : Fin h → Finset V) :
    Prop :=
  IsDominatorPartition E I S P ∧ ∀ i, ((P i).filter fun v => ∀ w ∈ P i, ¬ E v w).card ≤ S

omit [DecidableEq V] in
/-- The least number of sets in an `S`-partition (`IsPartition`) of the graph with edge relation
`E` and inputs `I`: the source's `P(S)`.

Where the graph has no `S`-partition the set is empty, and `sInf ∅ = 0` in `ℕ`. That value means
nothing, so a statement about `minParts` should only be made where an `S`-partition exists. -/
noncomputable def minParts (E : V → V → Prop) (I : Finset V) (S : ℕ) : ℕ :=
  sInf {h | ∃ P : Fin h → Finset V, IsPartition E I S P}

omit [DecidableEq V] in
/-- The least number of sets in an `S`-dominator partition (`IsDominatorPartition`) of the graph
with edge relation `E` and inputs `I`: the source's `P_D(S)`.

Where the graph has no `S`-dominator partition the set is empty, and `sInf ∅ = 0` in `ℕ`. That
value means nothing, so a statement about `minDominatorParts` should only be made where an
`S`-dominator partition exists. -/
noncomputable def minDominatorParts (E : V → V → Prop) (I : Finset V) (S : ℕ) : ℕ :=
  sInf {h | ∃ P : Fin h → Finset V, IsDominatorPartition E I S P}

omit [DecidableEq V] in
/-- `IsMatMulLabelling E I a b p`: in the graph with edge relation `E` and inputs `I`, the
vertices `a (i, l)`, `b (l, j)` and `p (i, l, j)` are the entries `A i l` of an `m × k` matrix `A`,
the entries `B l j` of a `k × n` matrix `B`, and the `m k n` products `A i l * B l j` of the
ordinary algorithm for `A * B`. That is: the entries are distinct inputs; each product is a vertex
of its own, with an edge from each of its two factors; and no vertex depends on products for two
different entries of `A * B`.

Nothing else is asked. How the products for an entry are combined, and what else the graph
computes, are free. -/
structure IsMatMulLabelling {m k n : ℕ} (E : V → V → Prop) (I : Finset V)
    (a : Fin m × Fin k → V) (b : Fin k × Fin n → V) (p : Fin m × Fin k × Fin n → V) : Prop where
  /-- The entries of `A` are distinct vertices. -/
  injective_a : Function.Injective a
  /-- The entries of `B` are distinct vertices. -/
  injective_b : Function.Injective b
  /-- The products are distinct vertices. -/
  injective_p : Function.Injective p
  /-- No entry of `A` is an entry of `B`. -/
  disjoint_ab : Disjoint (Set.range a) (Set.range b)
  /-- Every entry of `A` is an input. -/
  a_mem : ∀ x, a x ∈ I
  /-- Every entry of `B` is an input. -/
  b_mem : ∀ x, b x ∈ I
  /-- The product `p (i, l, j)` has an edge from its factor `a (i, l)`. -/
  edge_a : ∀ i l j, E (a (i, l)) (p (i, l, j))
  /-- The product `p (i, l, j)` has an edge from its factor `b (l, j)`. -/
  edge_b : ∀ i l j, E (b (l, j)) (p (i, l, j))
  /-- A vertex that can be reached, by a path of length `0` or more, from a product for the entry
  `(i, j)` of `A * B` cannot be reached from any product for another entry. -/
  independent : ∀ i l j i' l' j' w, Relation.ReflTransGen E (p (i, l, j)) w →
    Relation.ReflTransGen E (p (i', l', j')) w → i = i' ∧ j = j'

omit [DecidableEq V] in
/-- `IsMatMulEvaluation m k n E I O`: the graph with edge relation `E`, inputs `I` and outputs `O`
satisfies the source's standing assumptions (`IsComputationDAG`), computes the products of the
ordinary algorithm for multiplying an `m × k` matrix by a `k × n` matrix, and keeps what it
computes from them for different entries of the result apart: some labelling of its vertices is
an `IsMatMulLabelling`. -/
def IsMatMulEvaluation (m k n : ℕ) (E : V → V → Prop) (I O : Finset V) : Prop :=
  IsComputationDAG E I O ∧
    ∃ (a : Fin m × Fin k → V) (b : Fin k × Fin n → V) (p : Fin m × Fin k × Fin n → V),
      IsMatMulLabelling E I a b p

end MiscMath.Computability.RedBluePebbleGame

open Filter

namespace MiscMath.Computability

open RedBluePebbleGame

/-- **Hong and Kung's Theorem 3.1, corrected.** Every complete calculation of a computation DAG
with at most `S` red pebbles, charged `q`, comes with a `2S`-partition of the graph into `h` parts,
`q ≤ S h ≤ q + S`. -/
theorem exists_partition_of_hasCompleteCalculation {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q : ℕ} (hG : IsComputationDAG E I O)
    (hq : HasCompleteCalculation E I O S q) :
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S := by
  sorry

/-- **Hong and Kung's Lemma 3.1.** If every `2S`-partition of a computation DAG has at least `h₀`
parts, every complete calculation with at most `S` red pebbles is charged `q ≥ S (h₀ − 1)`. -/
theorem io_lower_bound_of_parts {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q h₀ : ℕ} (hG : IsComputationDAG E I O)
    (hparts : ∀ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P → h₀ ≤ h)
    (hq : HasCompleteCalculation E I O S q) :
    S * h₀ ≤ q + S := by
  sorry

/-- **Hong and Kung's Lemma 3.1 as stated: `Q ≥ S (P(2S) − 1)`.** For a computation DAG with a
complete calculation using at most `S` red pebbles, with `Q` the minimum I/O time and `P(2S)` the
least number of parts of a `2S`-partition. -/
theorem minIOTime_lower_bound {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S : ℕ} (hG : IsComputationDAG E I O)
    (hcalc : ∃ q, HasCompleteCalculation E I O S q) :
    (S : ℤ) * (minParts E I (2 * S) - 1) ≤ minIOTime E I O S := by
  sorry

/-- **Hong and Kung's Theorem 4.1, with its constant.** Every `S`-dominator partition of the
`2^k`-point FFT graph, `S ≥ 1`, has `h` parts with `(k + 1) 2^k ≤ h S log₂ (2S)`. -/
theorem fft_parts_lower_bound {k S h : ℕ} (hS : 1 ≤ S)
    {P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hP : IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P) :
    (2 : ℝ) ^ k * (k + 1) ≤ h * (S * Real.logb 2 (2 * S)) := by
  sorry

/-- **Hong and Kung's Theorem 4.1 as stated: `P_D(S) = Ω(n log n / (S log S))`.** With `n = 2^k`
and `P_D(S)` the least number of parts of an `S`-dominator partition of the `n`-point FFT graph,
`n ln n / (S ln S) = O(P_D(S))` along the principal filter of `{(k, S) : k ≥ 1, S ≥ 2}`: one
constant serves every such `k` and `S`. -/
theorem fft_parts_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1) / (p.2 * Real.log p.2))
      =O[𝓟 {p | 1 ≤ p.1 ∧ 2 ≤ p.2}]
      fun p => (minDominatorParts (fftEdge p.1) (Finset.univ.filter (·.1 = 0)) p.2 : ℝ) := by
  sorry

/-- **Feasibility.** The `2^k`-point FFT graph, `k ≥ 1`, has a complete calculation exactly when
at least three red pebbles are available. -/
theorem fft_complete_iff {k S : ℕ} (hk : 1 ≤ k) :
    (∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) ↔ 3 ≤ S := by
  sorry

/-- **The two bounds the argument gives.** For `k ≥ 1` and `S ≥ 1`, every complete calculation of
the `2^k`-point FFT graph, charged `q`, loads each input and stores each output, so
`q ≥ 2^(k+1)`; and `q ≥ 2^k (k + 1) / (2 log₂ (4S)) − S`, which says nothing once `S ≥ 2^(k-1)`. -/
theorem fft_io_bounds {k S q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    2 ^ (k + 1) ≤ q ∧ (2 : ℝ) ^ k * (k + 1) / (2 * Real.logb 2 (4 * S)) - S ≤ q := by
  sorry

/-- **Hong and Kung's Corollary 4.1, with its constant.** For `k ≥ 1`, every complete calculation of
the `2^k`-point FFT graph with `S ≥ 3` red pebbles, charged `q`, has `2^k · k ≤ 5 q log₂ S`. -/
theorem fft_io_lower_bound {k S q : ℕ} (hk : 1 ≤ k) (hS : 3 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    (2 : ℝ) ^ k * k ≤ 5 * q * Real.logb 2 S := by
  sorry

/-- **Hong and Kung's Corollary 4.1 as stated: `Q · log S = Ω(n log n)`.** With `n = 2^k` and `Q`
the minimum I/O time, `n ln n = O(Q · ln S)` along the principal filter of
`{(k, S) : k ≥ 1, S ≥ 3}`: one constant serves every such `k` and `S`. -/
theorem fft_io_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1)) =O[𝓟 {p | 1 ≤ p.1 ∧ 3 ≤ p.2}]
      fun p => (minIOTime (fftEdge p.1) (Finset.univ.filter (·.1 = 0))
        (Finset.univ.filter (·.1 = Fin.last p.1)) p.2 : ℝ) * Real.log p.2 := by
  sorry

/-- **Non-vacuity, and feasibility.** For all `m, k, n ≥ 1` some graph evaluates the ordinary
product of an `m × k` matrix by a `k × n` matrix (`IsMatMulEvaluation`) and has a complete
calculation exactly when at least three red pebbles are available. The graph the proof exhibits
is the ordinary algorithm itself, each entry of the product summed left to right. -/
theorem exists_isMatMulEvaluation {m k n : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∃ (V : Type) (_ : DecidableEq V) (_ : Finite V) (E : V → V → Prop) (I O : Finset V),
      IsMatMulEvaluation m k n E I O ∧ ∀ S, (∃ q, HasCompleteCalculation E I O S q) ↔ 3 ≤ S := by
  sorry

/-- **The two bounds the argument gives.** For `k ≥ 1`, every complete calculation of a graph that
evaluates the ordinary product of an `m × k` matrix by a `k × n` matrix, charged `q`, loads each
entry of the two matrices and stores an output for each entry of the product, so
`q ≥ m k + k n + m n`; and for `S ≥ 1` red pebbles, `q ≥ m k n / √(2S) − S`. -/
theorem matMul_io_bounds {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {m k n S q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (hM : IsMatMulEvaluation m k n E I O) (hq : HasCompleteCalculation E I O S q) :
    m * k + k * n + m * n ≤ q ∧ (m * k * n : ℝ) / Real.sqrt (2 * S) - S ≤ q := by
  sorry

/-- **Hong and Kung's Corollary 6.2, with its constant.** Every complete calculation of a graph that
evaluates the ordinary product of an `m × k` matrix by a `k × n` matrix (`IsMatMulEvaluation`),
with at most `S` red pebbles and charged `q`, has `m k n ≤ 2 q √S`. -/
theorem matMul_io_lower_bound {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {m k n S q : ℕ} (hM : IsMatMulEvaluation m k n E I O)
    (hq : HasCompleteCalculation E I O S q) :
    (m * k * n : ℝ) ≤ 2 * q * Real.sqrt S := by
  sorry

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
  sorry

end MiscMath.Computability
