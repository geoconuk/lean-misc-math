/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice.Nat

/-!
# The red-blue pebble game: the definitions its statements are read through

Support module of `MiscMath.Computability.RedBluePebbleGame`, which is where the results are
stated and where the reader should start. This file holds exactly the definitions the
advertised statements there are stated through, and nothing else. The game:

* `Step` — one legal move of the game, labelled by its I/O charge;
* `HasCompleteCalculation` — a complete calculation within a red-pebble budget, with a given
  total I/O charge;
* `fftEdge` — the edge relation of the `2^k`-point FFT graph (the butterfly);
* `minIOTime` — the least total I/O charge of a complete calculation, the source's `Q`.

The source's key lemma, and its partitions:

* `IsComputationDAG` — the graphs the key lemma is about: acyclic, with the inputs exactly the
  sources, every sink an output, and no input an output;
* `Dominates` — every path from an input to a set of vertices passes through another;
* `IsDominatorPartition` — an `S`-dominator partition, the source's P1, P2 and P4;
* `IsPartition` — an `S`-partition, which adds the source's P3;
* `minParts` and `minDominatorParts` — the least number of sets in either, the source's `P(S)`
  and `P_D(S)`.

Matrix multiplication (the source's §6):

* `IsMatMulLabelling` — which vertices are the entries of two matrices and which the products of
  the ordinary algorithm for their product, in a graph that keeps the work for different entries
  of the result apart;
* `IsMatMulEvaluation` — a computation DAG (`IsComputationDAG`) some labelling of whose vertices
  is one: the graphs the matrix-multiplication bounds are about.

Nothing is proved here. The proof machinery lives in the other modules of this directory,
which import this one; this one imports none of them.
-/

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
