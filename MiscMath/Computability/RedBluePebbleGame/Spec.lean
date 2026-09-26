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
stated and where the reader should start. This file holds exactly the four definitions the
advertised statements there are stated through, and nothing else:

* `Step` — one legal move of the game, labelled by its I/O charge;
* `HasCompleteCalculation` — a complete calculation within a red-pebble budget, with a given
  total I/O charge;
* `fftEdge` — the edge relation of the `2^k`-point FFT graph (the butterfly);
* `minIOTime` — the least total I/O charge of a complete calculation, the source's `Q`.

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

end MiscMath.Computability.RedBluePebbleGame
