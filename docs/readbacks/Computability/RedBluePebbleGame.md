# Read-back: `Computability/RedBluePebbleGame`

The blind read-backs of the red-blue pebble game's advertised statements, produced as
[`docs/READBACK.md`](../../READBACK.md) describes. The statements came in two phases, each read
back before it was read and frozen:

- **Phase 2, the key lemma (Hong and Kung's §3 and Theorem 4.1).** Two rounds:
  - **Round 2 is current for Phase 2.** It renders the six Phase 2 statements, and every
    definition they are stated through, as they now stand.
  - **Round 1 is kept** for what it surfaced. Its renderings of the four general statements
    describe versions that took the graph hypotheses separately; those versions no longer exist.
- **Phase 1, the FFT statements (Corollary 4.1).** Two rounds:
  - **Round 2 is current for Phase 1.** It renders the four Phase 1 statements, and the four
    definitions they are stated through, as they now stand.
  - **Round 1 is kept** because it surfaced the charging point recorded under it. Its rendering
    of `fft_io_bounds` describes a version of that statement that no longer exists.

## Phase 2, round 2 (current for Phase 2), 2026-09-27

### What changed since round 1

- **`IsComputationDAG` is new.** It is a `Prop` structure with four fields: `acyclic`,
  `inputs_eq_sources`, `sinks_subset_outputs` and `disjoint`. They bundle the four graph
  hypotheses the general statements took separately in round 1, word for word. George asked for
  this on 2026-09-27, after reading round 1's core items, and approved the name and the form.
- **The four general statements** take `(hG : IsComputationDAG E I O)` in place of `hE`, `hI`,
  `hO` and `hIO`: `exists_partition_of_hasCompleteCalculation`, `io_lower_bound_of_parts`,
  `minIOTime_lower_bound` and `io_lower_bound_of_dominated_card`. Their conclusions and other
  hypotheses are unchanged.
- **Everything else is unchanged:** the five definitions of round 1, and the two FFT statements.
  They were sent again, so that this round renders the whole current Phase 2 surface.

### What was sent

- **Taken from:** an uncommitted draft on branch `hong-kung`, based on `30b9d4a`, on 2026-09-27.
  The SHA-256 of each stripped module exactly as sent is
  - `b35d3000fa7a033ddec4bc1744a55d276de3302f163a7bfc80eaf7d5d4f223fa` for Module 1;
  - `fad9e1ff18f51f3491388d822b4d6747c0f560b9f9e9f01dca49c8c55eee1e42` for Module 2.
- **Declarations:** the same six as in round 1.
- **Definitions they are stated through:** `IsComputationDAG`, which is new, and the nine of
  round 1. These ten, with the constructors of `Step` and `IsComputationDAG`, are the only project
  constants the six statement types reach, transitively. This was checked by walking the
  elaborated statements.
- **The prompt** was composed as in round 1: the same opening line, the brief, and the two
  stripped modules below.

### Who wrote it

`claude-opus-5-5` (Claude Opus 5.5), as a fresh subagent with no prior context, on 2026-09-27.
Its one tool call was the hand-back that delivered the rendering. It read no file, ran no
command and did not browse; the count was checked in its transcript. Its model ID, on the final
line of its reply, is left out below. As in round 1, it unfolded the definitions inline rather
than giving them blocks of their own. Its headings are demoted one level to fit this file, and
the rendering is otherwise verbatim.

### What the comparison found

The rendering agrees with the intended statements clause by clause:

- **`IsComputationDAG`** is rendered as exactly the four conditions round 1 rendered as separate
  hypotheses:
  - no walk of length at least 1 from a vertex back to itself;
  - the inputs are exactly the vertices with no incoming edge;
  - every vertex with no outgoing edge is an output, and other vertices may be outputs too;
  - no vertex is both an input and an output.
- **The general statements otherwise read as in round 1.** In particular:
  - `minIOTime_lower_bound` subtracts in ℤ, with no truncation;
  - `hparts` in `io_lower_bound_of_parts` is not vacuous for `S ≥ 1`.
- **The two FFT statements read as in round 1.** The bound on the dominator is `S`, and the
  constant in the asymptotic statement is uniform over the principal filter.

It surfaced two points that the intended account had left implicit. Both are correct, and both
were checked by hand:

1. **Theorem 3.1's conclusion determines `h` almost exactly.**
   - For `S ≥ 1`, `q ≤ S·h ≤ q + S` forces `h = ⌈q/S⌉` when `S` does not divide `q`.
   - It allows `h = q/S` or `h = q/S + 1` when `S` divides `q`.
   - This fits round 1's point: padding with empty parts reaches `q ≤ S·h`, and `S·h ≤ q + S`
     caps it.
2. **The bridge says nothing on a graph with at most `2S` inputs.**
   - There `D = I` dominates every set, since there is no input outside `D`.
   - So the bridge's hypothesis forces `U ≥ |V|`, and its conclusion is immediate.
   - Its content is for graphs with more than `2S` inputs, as in the FFT. This belongs in the
     roof docstring.

It did not repeat round 1's point that `S ≤ 1` forces the graph to be empty. It gives the case
`S = 0` alone, which is consistent. It also notes that in the asymptotic statement the base of the
logarithms is immaterial, since only their ratio appears. That is right.

No error was found in the rendering.

### The rendering, verbatim

#### exists_partition_of_hasCompleteCalculation

**Binders.** All of these are universally quantified, in this order. Nothing is chosen before them.
- $V$: an arbitrary type, in any universe. Its elements are called vertices. $V$ carries two instance assumptions:
  - a decidable-equality instance, which only makes finite-set operations computable and does not affect meaning;
  - finiteness: $V$ has finitely many elements, possibly none.
- $E$: an arbitrary binary relation on $V$. $E(u,v)$ is read "there is an edge from $u$ to $v$".
- $I$, $O$: finite subsets of $V$.
- $S$, $q$: natural numbers.

**Hypotheses.**
1. $(E,I,O)$ is a computation DAG, which means all four of the following:
   - (i) No vertex $v$ has a directed $E$-walk of length $\ge 1$ from $v$ back to $v$. In particular $E(v,v)$ never holds.
   - (ii) For every vertex $v$: $v\in I$ if and only if there is no $u$ with $E(u,v)$. So $I$ is exactly the set of vertices with no incoming edge.
   - (iii) Every vertex $v$ with no $w$ such that $E(v,w)$ lies in $O$. $O$ may contain further vertices.
   - (iv) $I\cap O=\emptyset$.
2. There is a complete calculation with red bound $S$ and cost exactly $q$. This means there exist:
   - a length $t\in\mathbb N$ ($t=0$ allowed),
   - pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$ (the "red" and "blue" sets),
   - numbers $c_0,\dots,c_{t-1}\in\mathbb N$,

   such that:
   - $(R_0,B_0)=(\emptyset,I)$ and $(R_t,B_t)=(\emptyset,O)$. The final blue set is exactly $O$, not a superset of it.
   - $|R_j|\le S$ for every $j=0,\dots,t$. The blue sets are not bounded.
   - For each $i<t$, the passage from $(R_i,B_i)$ to $(R_{i+1},B_{i+1})$ is a move of cost $c_i$.
   - $c_0+\dots+c_{t-1}=q$.

   The moves from $(R,B)$ are exactly these five; nothing else is a move:
   - **load**, cost 1: pick $v\in B$ with $v\notin R$ and go to $(R\cup\{v\},B)$.
   - **store**, cost 1: pick $v\in R$ with $v\notin B$ and go to $(R,B\cup\{v\})$.
   - **compute**, cost 0: pick $v$ with $v\notin I$, $v\notin R$, and every $u\in V$ with $E(u,v)$ lying in $R$, and go to $(R\cup\{v\},B)$. Nothing is required about whether $v\in B$.
   - **remove red**, cost 0: pick $v\in R$ and go to $(R\setminus\{v\},B)$.
   - **remove blue**, cost 0: pick $v\in B$ and go to $(R,B\setminus\{v\})$.

   So each $c_i$ is 0 or 1, and $q$ counts the steps given cost 1. A transition that fits both the load and the compute description may be given either cost. $q$ is the cost of some such calculation, not necessarily the least one.

**Conclusion.** There exist a natural number $h$ and finite sets $P_0,\dots,P_{h-1}\subseteq V$, indexed by $\{0,\dots,h-1\}$ in its usual order. They are chosen after everything above and may depend on all of it. They satisfy:
- (a) Every vertex of $V$ lies in exactly one $P_i$. So the $P_i$ are pairwise disjoint and cover $V$. Empty $P_i$ are allowed and are counted in $h$.
- (b) For every $i$ there is a finite $D_i\subseteq V$, which may depend on $i$, with $|D_i|\le 2S$ and with $D_i$ dominating $P_i$. Here "$D$ dominates $W$" means: for every $x\in I$ with $x\notin D$ and every $w\in W$, there is no sequence $x=a_0,a_1,\dots,a_m=w$ with $m\ge 0$, with $E(a_r,a_{r+1})$ for all $r<m$, and with no $a_r$ in $D$.
  - Equivalently, every $E$-walk of length $\ge 0$ from a vertex of $I$ to a vertex of $W$ contains a vertex of $D$.
  - The case $m=0$ requires $I\cap W\subseteq D$.
  - $D$ is otherwise unrestricted; it may meet $W$ or $I$.
- (c) Whenever $u\in P_i$, $v\in P_j$ and $E(u,v)$, then $i\le j$.
- (d) For every $i$, at most $2S$ vertices $v\in P_i$ have no $w\in P_i$ with $E(v,w)$.
- (e) $q\le S\cdot h$ and $S\cdot h\le q+S$, in natural-number arithmetic. No subtraction occurs.

*Edge cases.*
- **$V$ empty.** Then $I=O=\emptyset$. No move is possible, so $t=0$ and $q=0$. $h=0$ with the empty family meets the conclusion.
- **Isolated vertices.** The hypotheses exclude any vertex with no incoming and no outgoing edge: by (ii) and (iii) it would lie in both $I$ and $O$, contradicting (iv).
- **$S=0$.** Every red set must be empty, so only "remove blue" moves can occur. A calculation then needs $O\subseteq I$, which with (iv) gives $O=\emptyset$. By (iii) there is then no vertex without an outgoing edge, which is impossible in a finite nonempty graph satisfying (i). So at $S=0$ the hypotheses hold only for empty $V$, and the inequalities in (e) then say only $q=0$.
- **$S\ge 1$.** (e) forces $h=\lceil q/S\rceil$ when $S\nmid q$, and $h\in\{q/S,\;q/S+1\}$ when $S\mid q$. Because empty parts are counted, $h$ counts indices, not nonempty parts. $h=0$ is possible only if $V$ is empty.
- **Satisfiability.** The hypotheses can hold together non-trivially. Example: $V=\{a,b\}$ with the single edge $a\to b$, $I=\{a\}$, $O=\{b\}$, $S=2$, $q=2$, using the moves: load $a$, compute $b$, store $b$, remove red $a$, remove red $b$, remove blue $a$.

---

#### io_lower_bound_of_parts

**Binders.** All of these are universally quantified, in this order. Nothing is chosen before them.
- $V$: an arbitrary type, in any universe; its elements are vertices. It carries a decidable-equality instance (no effect on meaning) and is assumed finite, possibly empty.
- $E$: an arbitrary binary relation on $V$. $E(u,v)$ is read "there is an edge from $u$ to $v$".
- $I$, $O$: finite subsets of $V$.
- $S$, $q$, $h_0$: natural numbers.

**Hypotheses.**
1. $(E,I,O)$ is a computation DAG, which means all four of the following:
   - (i) No vertex $v$ has a directed $E$-walk of length $\ge 1$ from $v$ back to $v$. In particular $E(v,v)$ never holds.
   - (ii) For every vertex $v$: $v\in I$ if and only if there is no $u$ with $E(u,v)$. So $I$ is exactly the set of vertices with no incoming edge.
   - (iii) Every vertex $v$ with no $w$ such that $E(v,w)$ lies in $O$. $O$ may contain further vertices.
   - (iv) $I\cap O=\emptyset$.
2. For every natural number $h$ and every family $P_0,\dots,P_{h-1}$ of finite subsets of $V$ (indexed by $\{0,\dots,h-1\}$ in its usual order), if the family satisfies all of (a)–(d) below, then $h_0\le h$:
   - (a) Every vertex of $V$ lies in exactly one $P_i$. Empty $P_i$ are allowed and counted in $h$.
   - (b) For every $i$ there is a finite $D_i\subseteq V$, which may depend on $i$, with $|D_i|\le 2S$ and with $D_i$ dominating $P_i$. Here "$D$ dominates $W$" means: for every $x\in I$ with $x\notin D$ and every $w\in W$, there is no sequence $x=a_0,\dots,a_m=w$ with $m\ge 0$, with $E(a_r,a_{r+1})$ for all $r<m$, and with no $a_r$ in $D$.
     - Equivalently, every $E$-walk of length $\ge 0$ from $I$ to $W$ meets $D$.
     - The case $m=0$ requires $I\cap W\subseteq D$.
   - (c) If $u\in P_i$, $v\in P_j$ and $E(u,v)$, then $i\le j$.
   - (d) For every $i$, at most $2S$ vertices $v\in P_i$ have no $w\in P_i$ with $E(v,w)$.
3. There is a complete calculation with red bound $S$ and cost exactly $q$. This means there exist:
   - a length $t\in\mathbb N$ ($t=0$ allowed),
   - pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$,
   - numbers $c_0,\dots,c_{t-1}\in\mathbb N$,

   such that:
   - $(R_0,B_0)=(\emptyset,I)$ and $(R_t,B_t)=(\emptyset,O)$. The final blue set is exactly $O$.
   - $|R_j|\le S$ for all $j=0,\dots,t$. The blue sets are unbounded.
   - Each passage $(R_i,B_i)\to(R_{i+1},B_{i+1})$ is a move of cost $c_i$.
   - $\sum_i c_i=q$.

   The moves from $(R,B)$ are exactly these five:
   - **load**, cost 1: some $v\in B$ with $v\notin R$ goes to $(R\cup\{v\},B)$.
   - **store**, cost 1: some $v\in R$ with $v\notin B$ goes to $(R,B\cup\{v\})$.
   - **compute**, cost 0: some $v\notin I$ with $v\notin R$ and all $u$ with $E(u,v)$ in $R$ goes to $(R\cup\{v\},B)$. There is no condition on whether $v\in B$.
   - **remove red**, cost 0: some $v\in R$ goes to $(R\setminus\{v\},B)$.
   - **remove blue**, cost 0: some $v\in B$ goes to $(R,B\setminus\{v\})$.

   A transition that is both a valid load and a valid compute may be given either cost. $q$ is the cost of some calculation, not necessarily the least.

**Conclusion.** $S\cdot h_0\le q+S$, in natural-number arithmetic. No subtraction occurs.

*Edge cases.*
- **Trivial cases.** The conclusion is automatic when $S=0$ or $h_0=0$, and $h_0=0$ always satisfies hypothesis 2.
- **Vacuity of hypothesis 2.** Hypothesis 2 would hold for every $h_0$ if no family satisfied (a)–(d). For $S\ge 1$ that does not happen. The singletons $\{v\}$, listed in an order in which every edge goes forward (one exists by (i) and finiteness), satisfy (a)–(d) with $D=\{v\}$. So for $S\ge 1$, hypothesis 2 implies $h_0\le|V|$.
- **Restatement.** For $S\ge 1$ the conclusion is equivalent to $q\ge S(h_0-1)$ with integer subtraction.
- **Isolated vertices.** The hypotheses exclude them: such a vertex would lie in both $I$ and $O$.
- **$S=0$.** The hypotheses force $V=\emptyset$. Only blue removals are possible, so $O\subseteq I$, so $O=\emptyset$, which contradicts (i) and (iii) for a nonempty finite $V$.

---

#### minIOTime_lower_bound

**Binders.** All of these are universally quantified, in this order.
- $V$: an arbitrary type, in any universe; its elements are vertices. It carries a decidable-equality instance (no effect on meaning) and is assumed finite, possibly empty.
- $E$: an arbitrary binary relation on $V$. $E(u,v)$ means "edge from $u$ to $v$".
- $I$, $O$: finite subsets of $V$.
- $S$: a natural number.

**Hypotheses.**
1. $(E,I,O)$ is a computation DAG, which means all four of the following:
   - (i) There is no directed $E$-walk of length $\ge 1$ from any vertex back to itself.
   - (ii) $v\in I$ if and only if there is no $u$ with $E(u,v)$. So $I$ is exactly the set of vertices with no incoming edge.
   - (iii) Every vertex with no outgoing edge lies in $O$. $O$ may contain further vertices.
   - (iv) $I\cap O=\emptyset$.
2. For some natural number $q$ there is a complete calculation with red bound $S$ and cost exactly $q$. This means there exist:
   - $t\in\mathbb N$ ($t=0$ allowed),
   - pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$,
   - $c_0,\dots,c_{t-1}\in\mathbb N$,

   such that:
   - $(R_0,B_0)=(\emptyset,I)$ and $(R_t,B_t)=(\emptyset,O)$, with the final blue set exactly $O$.
   - $|R_j|\le S$ for all $j$. The blue sets are unbounded.
   - Each passage $(R_i,B_i)\to(R_{i+1},B_{i+1})$ is a move of cost $c_i$.
   - $\sum_i c_i=q$.

   The moves from $(R,B)$ are exactly these five:
   - **load**, cost 1: some $v\in B$ with $v\notin R$ goes to $(R\cup\{v\},B)$.
   - **store**, cost 1: some $v\in R$ with $v\notin B$ goes to $(R,B\cup\{v\})$.
   - **compute**, cost 0: some $v\notin I$ with $v\notin R$ and every $u$ with $E(u,v)$ in $R$ goes to $(R\cup\{v\},B)$. There is no condition on $v\in B$.
   - **remove red**, cost 0: some $v\in R$ goes to $(R\setminus\{v\},B)$.
   - **remove blue**, cost 0: some $v\in B$ goes to $(R,B\setminus\{v\})$.

   A transition that is both a valid load and a valid compute may be given either cost.

**Conclusion.** In the integers, $S\cdot(m-1)\le T$. $S$, $m$ and $T$ are natural numbers cast to $\mathbb Z$, and $m-1$ is integer subtraction, not truncated: $m=0$ gives $-1$. The two quantities are:
- $T$: the infimum in $\mathbb N$ of the set of $q$ for which a complete calculation (as in hypothesis 2) with red bound $S$ and cost exactly $q$ exists. By Mathlib's convention this is the least element of the set if the set is nonempty, and $0$ if it is empty. Hypothesis 2 makes it nonempty, so $T$ is the least cost of a complete calculation.
- $m$: the infimum in $\mathbb N$ of the set of $h$ for which there is a family $P_0,\dots,P_{h-1}$ of finite subsets of $V$ satisfying all of (a)–(d) below. It is the least such $h$, or $0$ if there is none.
  - (a) Every vertex lies in exactly one $P_i$. Empty $P_i$ are allowed and counted.
  - (b) For every $i$ there is a finite $D_i\subseteq V$ with $|D_i|\le 2S$ such that every $E$-walk of length $\ge 0$ from a vertex of $I$ to a vertex of $P_i$ contains a vertex of $D_i$. Literally: for every $x\in I$ with $x\notin D_i$ and every $w\in P_i$, there is no $E$-walk from $x$ to $w$ all of whose vertices lie outside $D_i$. In particular $I\cap P_i\subseteq D_i$.
  - (c) $u\in P_i$, $v\in P_j$ and $E(u,v)$ imply $i\le j$.
  - (d) For every $i$, at most $2S$ vertices $v\in P_i$ have no $w\in P_i$ with $E(v,w)$.

*Edge cases.*
- **$S=0$.** The left side is 0, so the statement is trivially true.
- **$m=0$.** This happens when $V=\emptyset$ (then $h=0$ is admissible), or if no admissible family exists. The left side is then $-S$ and the statement holds trivially.
- **$S\ge 1$ and $V\ne\emptyset$.** The singletons, listed in an order in which every edge goes forward, are admissible, and $h=0$ is not. So $m\ge 1$ is a genuine least element, and the statement reads $T\ge S(m-1)$.
- **Role of hypothesis 2.** Without it, $T$ could be the junk value 0. Hypothesis 2 excludes this.
- **Degenerate graphs.** The hypotheses exclude isolated vertices. At $S=0$ they force $V=\emptyset$.

---

#### io_lower_bound_of_dominated_card

**Binders.** All of these are universally quantified, in this order.
- $V$: an arbitrary type, in any universe; its elements are vertices. It carries a decidable-equality instance (no effect on meaning) and is assumed finite, possibly empty.
- $E$: an arbitrary binary relation on $V$. $E(u,v)$ means "edge from $u$ to $v$".
- $I$, $O$: finite subsets of $V$.
- $S$, $q$, $U$: natural numbers.

**Hypotheses.**
1. $(E,I,O)$ is a computation DAG, which means all four of the following:
   - (i) There is no directed $E$-walk of length $\ge 1$ from any vertex back to itself.
   - (ii) $v\in I$ if and only if there is no $u$ with $E(u,v)$.
   - (iii) Every vertex with no outgoing edge lies in $O$.
   - (iv) $I\cap O=\emptyset$.
2. For all finite $D,W\subseteq V$: if $|D|\le 2S$ and $D$ dominates $W$, then $|W|\le U$. Here "$D$ dominates $W$" means: for every $x\in I$ with $x\notin D$ and every $w\in W$, there is no sequence $x=a_0,\dots,a_m=w$ with $m\ge 0$, with $E(a_r,a_{r+1})$ for all $r<m$, and with no $a_r$ in $D$.
   - Equivalently, every $E$-walk of length $\ge 0$ from $I$ to $W$ meets $D$.
   - In particular $I\cap W\subseteq D$.
3. There is a complete calculation with red bound $S$ and cost exactly $q$. This means there exist:
   - $t\in\mathbb N$ ($t=0$ allowed),
   - pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$,
   - $c_0,\dots,c_{t-1}\in\mathbb N$,

   such that:
   - $(R_0,B_0)=(\emptyset,I)$ and $(R_t,B_t)=(\emptyset,O)$, with the final blue set exactly $O$.
   - $|R_j|\le S$ for all $j$. The blue sets are unbounded.
   - Each passage $(R_i,B_i)\to(R_{i+1},B_{i+1})$ is a move of cost $c_i$.
   - $\sum_i c_i=q$.

   The moves from $(R,B)$ are exactly these five:
   - **load**, cost 1: some $v\in B$ with $v\notin R$ goes to $(R\cup\{v\},B)$.
   - **store**, cost 1: some $v\in R$ with $v\notin B$ goes to $(R,B\cup\{v\})$.
   - **compute**, cost 0: some $v\notin I$ with $v\notin R$ and every $u$ with $E(u,v)$ in $R$ goes to $(R\cup\{v\},B)$.
   - **remove red**, cost 0: some $v\in R$ goes to $(R\setminus\{v\},B)$.
   - **remove blue**, cost 0: some $v\in B$ goes to $(R,B\setminus\{v\})$.

   A transition that is both a valid load and a valid compute may be given either cost. $q$ is the cost of some calculation, not necessarily the least.

**Conclusion.** $S\cdot|V|\le (q+S)\cdot U$ in natural-number arithmetic, where $|V|$ is the number of elements of $V$ (its true cardinality, since $V$ is finite).

*Edge cases.*
- **Trivial cases.** The statement is trivially true when $S=0$ or $V=\emptyset$.
- **What hypothesis 2 forces on $U$.** Taking $D=W$ shows hypothesis 2 forces $U\ge\min(2S,|V|)$.
- **Choices of $U$ that make the conclusion immediate.**
  - $U=|V|$ always satisfies hypothesis 2, and then the conclusion is immediate.
  - If $|I|\le 2S$, then $D=I$ dominates every $W$, since no $x\in I$ lies outside $D$. So hypothesis 2 forces $U\ge|V|$, and the conclusion is again immediate.
- **Degenerate graphs.** The hypotheses exclude isolated vertices. At $S=0$ they force $V=\emptyset$.

---

#### fft_parts_lower_bound

**Setting.** For $k\in\mathbb N$, let $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$. Its elements are pairs (level $\ell$, index $x$); $|V_k|=(k+1)2^k$.

The graph $G_k$ has an edge from $(\ell,x)$ to $(\ell',x')$ if and only if $\ell'=\ell+1$ (as natural numbers, with no wrap-around) and either $x'=x$ or $x'=x\oplus 2^{\ell}$. Here $\oplus$ is bitwise exclusive-or on natural numbers, so $x\oplus 2^{\ell}$ is $x$ with binary digit $\ell$ flipped. Consequently:
- Edges run only from level $\ell\le k-1$ to level $\ell+1$.
- Each vertex at level $\ell<k$ has exactly the two out-neighbours $(\ell+1,x)$ and $(\ell+1,x\oplus 2^\ell)$.
- Each vertex at level $\ge 1$ has exactly two in-neighbours.
- Level 0 has no incoming edges, and level $k$ has no outgoing edges.

$I_k=\{(0,x):0\le x<2^k\}$ is the set of level-0 vertices.

**Binders.** All universally quantified, in this order:
- natural numbers $k$, $S$, $h$;
- then the hypothesis $1\le S$;
- then a family $P_0,\dots,P_{h-1}$ of subsets of $V_k$, indexed by $\{0,\dots,h-1\}$ in its usual order;
- then the hypothesis below.

**Hypotheses.**
1. $S\ge 1$.
2. The family satisfies (a)–(c), with dominance taken in $G_k$ relative to $I_k$:
   - (a) Every vertex of $V_k$ lies in exactly one $P_i$. Empty $P_i$ are allowed and counted in $h$.
   - (b) For every $i$ there is $D_i\subseteq V_k$, which may depend on $i$, with $|D_i|\le S$ and such that: for every $x\in I_k$ with $x\notin D_i$ and every $w\in P_i$, there is no directed walk $x=a_0\to a_1\to\dots\to a_m=w$ in $G_k$ with $m\ge 0$ whose vertices all lie outside $D_i$.
     - Equivalently, every walk from a level-0 vertex to a vertex of $P_i$ meets $D_i$.
     - In particular, level-0 vertices of $P_i$ lie in $D_i$.
   - (c) Whenever $u\in P_i$, $v\in P_j$ and $G_k$ has an edge from $u$ to $v$, then $i\le j$.

   There is no condition bounding the number of vertices of $P_i$ without a successor in $P_i$.

**Conclusion.** In the reals, $2^k\,(k+1)\le h\cdot S\cdot\log_2(2S)$, where $k$, $h$, $S$ are cast to $\mathbb R$ and $\log_2 y=\ln y/\ln 2$. The left side equals $|V_k|$.

*Edge cases.*
- **No junk values.** For $S\ge 1$, $\log_2(2S)=1+\log_2 S\ge 1$. $S=0$ is excluded by hypothesis 1; there the right side would be $0$, since the logarithm of $0$ is $0$ by convention.
- **$k=0$.** $V_0=\{(0,0)\}$, there are no edges, and that vertex is in $I_0$. (a) forces $h\ge 1$, and the statement reads $1\le h\,S\log_2(2S)$.
- **$S=1$.** The right side is $h$, so the statement says $h\ge (k+1)2^k=|V_k|$.
- **Scope.** The bound applies to every admissible family, not only minimal ones. Empty parts are counted in $h$.
- **Satisfiability.** Hypothesis 2 is satisfiable for every $k$ and every $S\ge 1$: take the singletons ordered by level, each dominated by itself.
- **Same $S$.** $S$ is both the dominator-size bound and the $S$ on the right side.

---

#### fft_parts_lower_bound_isBigO

**Setting.** $V_k$, $G_k$ and $I_k$ are as follows:
- $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$.
- $G_k$ has an edge $(\ell,x)\to(\ell',x')$ if and only if $\ell'=\ell+1$ and ($x'=x$ or $x'=x\oplus 2^\ell$), with $\oplus$ bitwise exclusive-or. So edges run from each level to the next, and each vertex below level $k$ has two out-neighbours.
- $I_k$ is the set of level-0 vertices.

**Binders.** There are no hypotheses and no outer variables. The statement concerns two real-valued functions of a pair $p=(k,S)\in\mathbb N\times\mathbb N$:
- $f(k,S)=\dfrac{2^k\cdot\ln(2^k)}{S\cdot\ln S}$, parsed as $(2^k\ln 2^k)/(S\ln S)$.
  - $\ln$ is the natural logarithm and $S$ is cast to $\mathbb R$.
  - Since $\ln(2^k)=k\ln 2$, $f(k,S)=2^k k\ln 2/(S\ln S)$.
  - Only the ratio $\ln(2^k)/\ln S$ involves logarithms, so the base is immaterial.
- $g(k,S)=m(k,S)$ cast to $\mathbb R$. Here $m(k,S)$ is the infimum in $\mathbb N$ of the set of $h$ for which there is a family $P_0,\dots,P_{h-1}$ of subsets of $V_k$ satisfying (a)–(c). It is the least such $h$, or $0$ if the set is empty.
  - (a) Every vertex of $V_k$ lies in exactly one $P_i$. Empty parts are allowed and counted.
  - (b) For every $i$ there is $D_i\subseteq V_k$ with $|D_i|\le S$ such that every directed walk of length $\ge 0$ in $G_k$ from a level-0 vertex to a vertex of $P_i$ contains a vertex of $D_i$. Literally: no walk from some $x\in I_k\setminus D_i$ to a vertex of $P_i$ avoids $D_i$.
  - (c) An edge from $P_i$ to $P_j$ implies $i\le j$.

  The dominator bound here is $S$ itself, the same $S$ as in $f$.

**Conclusion.** $f=O(g)$ along the principal filter of $A=\{(k,S)\in\mathbb N\times\mathbb N : k\ge 1,\ S\ge 2\}$. By Mathlib's definitions of big-O and of the principal filter, this means: there exists a real number $C$ such that for every $(k,S)$ with $k\ge 1$ and $S\ge 2$,
$$|f(k,S)|\le C\cdot|g(k,S)|.$$
- $C$ is chosen once, before $(k,S)$, and is not specified.
- The bound holds at every point of $A$ simultaneously. It is not a limit statement and is not restricted to large $k$ or $S$.
- $f$ is the function bounded; the minimal number of parts $g$ is the bounding function.

*Edge cases.*
- **On $A$, no junk values.** $S\ge 2$ gives $S\ln S>0$, so there is no division by zero, and $k\ge 1$ gives $f>0$. Both sides are nonnegative on $A$, so the absolute values can be dropped: $f(k,S)\le C\,m(k,S)$.
- **Points outside $A$.** Pairs with $k=0$ or $S\le 1$ are excluded. There $f$ would be $0$: at $S\in\{0,1\}$ the denominator is $0$ and division by zero gives $0$, and at $k=0$, $\ln 1=0$.
- **Junk value of $m$.** $m(k,S)$ would be $0$ at any point where no admissible family exists, and the inequality there would read $|f|\le 0$. For $S\ge 1$ this does not happen: the singletons ordered by level are admissible. Since $V_k\neq\emptyset$ forces $h\ge 1$, $m(k,S)$ is a genuine least element with $m(k,S)\ge 1$ on $A$.

### The Lean sent

Module 1:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice.Nat

namespace MiscMath.Computability.RedBluePebbleGame

variable {V : Type*} [DecidableEq V]

inductive Step (E : V → V → Prop) (I : Finset V) :
    Finset V × Finset V → ℕ → Finset V × Finset V → Prop
  | load {R B : Finset V} {v : V} (hB : v ∈ B) (hR : v ∉ R) :
      Step E I (R, B) 1 (insert v R, B)
  | store {R B : Finset V} {v : V} (hR : v ∈ R) (hB : v ∉ B) :
      Step E I (R, B) 1 (R, insert v B)
  | compute {R B : Finset V} {v : V} (hI : v ∉ I) (hR : v ∉ R) (hpred : ∀ u, E u v → u ∈ R) :
      Step E I (R, B) 0 (insert v R, B)
  | deleteRed {R B : Finset V} {v : V} (hR : v ∈ R) :
      Step E I (R, B) 0 (R.erase v, B)
  | deleteBlue {R B : Finset V} {v : V} (hB : v ∈ B) :
      Step E I (R, B) 0 (R, B.erase v)

def HasCompleteCalculation (E : V → V → Prop) (I O : Finset V) (S q : ℕ) : Prop :=
  ∃ (t : ℕ) (σ : Fin (t + 1) → Finset V × Finset V) (c : Fin t → ℕ),
    σ 0 = (∅, I) ∧
    σ (Fin.last t) = (∅, O) ∧
    (∀ j, (σ j).1.card ≤ S) ∧
    (∀ i : Fin t, Step E I (σ i.castSucc) (c i) (σ i.succ)) ∧
    ∑ i, c i = q

def fftEdge (k : ℕ) (u v : Fin (k + 1) × Fin (2 ^ k)) : Prop :=
  (v.1 : ℕ) = (u.1 : ℕ) + 1 ∧
    ((v.2 : ℕ) = (u.2 : ℕ) ∨ (v.2 : ℕ) = (u.2 : ℕ) ^^^ 2 ^ (u.1 : ℕ))

noncomputable def minIOTime (E : V → V → Prop) (I O : Finset V) (S : ℕ) : ℕ :=
  sInf {q | HasCompleteCalculation E I O S q}

omit [DecidableEq V] in
structure IsComputationDAG (E : V → V → Prop) (I O : Finset V) : Prop where
  acyclic : ∀ v, ¬ Relation.TransGen E v v
  inputs_eq_sources : ∀ v, v ∈ I ↔ ∀ u, ¬ E u v
  sinks_subset_outputs : ∀ v, (∀ w, ¬ E v w) → v ∈ O
  disjoint : Disjoint I O

omit [DecidableEq V] in
def Dominates (E : V → V → Prop) (I D W : Finset V) : Prop :=
  ∀ x ∈ I, x ∉ D → ∀ w ∈ W, ¬ Relation.ReflTransGen (fun a b => E a b ∧ a ∉ D ∧ b ∉ D) x w

omit [DecidableEq V] in
def IsDominatorPartition {h : ℕ} (E : V → V → Prop) (I : Finset V) (S : ℕ)
    (P : Fin h → Finset V) : Prop :=
  (∀ v, ∃! i, v ∈ P i) ∧
    (∀ i, ∃ D : Finset V, D.card ≤ S ∧ Dominates E I D (P i)) ∧
    ∀ i j, ∀ u ∈ P i, ∀ v ∈ P j, E u v → i ≤ j

omit [DecidableEq V] in
open Classical in
def IsPartition {h : ℕ} (E : V → V → Prop) (I : Finset V) (S : ℕ) (P : Fin h → Finset V) :
    Prop :=
  IsDominatorPartition E I S P ∧ ∀ i, ((P i).filter fun v => ∀ w ∈ P i, ¬ E v w).card ≤ S

omit [DecidableEq V] in
noncomputable def minParts (E : V → V → Prop) (I : Finset V) (S : ℕ) : ℕ :=
  sInf {h | ∃ P : Fin h → Finset V, IsPartition E I S P}

omit [DecidableEq V] in
noncomputable def minDominatorParts (E : V → V → Prop) (I : Finset V) (S : ℕ) : ℕ :=
  sInf {h | ∃ P : Fin h → Finset V, IsDominatorPartition E I S P}

end MiscMath.Computability.RedBluePebbleGame
```

Module 2:

```lean
import MiscMath.Computability.RedBluePebbleGame.Spec
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Prod

open Filter MiscMath.Computability.RedBluePebbleGame

namespace Target.RedBluePebbleGame

theorem exists_partition_of_hasCompleteCalculation {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q : ℕ} (hG : IsComputationDAG E I O)
    (hq : HasCompleteCalculation E I O S q) :
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S

theorem io_lower_bound_of_parts {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q h₀ : ℕ} (hG : IsComputationDAG E I O)
    (hparts : ∀ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P → h₀ ≤ h)
    (hq : HasCompleteCalculation E I O S q) :
    S * h₀ ≤ q + S

theorem minIOTime_lower_bound {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S : ℕ} (hG : IsComputationDAG E I O)
    (hcalc : ∃ q, HasCompleteCalculation E I O S q) :
    (S : ℤ) * (minParts E I (2 * S) - 1) ≤ minIOTime E I O S

theorem io_lower_bound_of_dominated_card {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q U : ℕ} (hG : IsComputationDAG E I O)
    (hU : ∀ D W : Finset V, D.card ≤ 2 * S → Dominates E I D W → W.card ≤ U)
    (hq : HasCompleteCalculation E I O S q) :
    S * Nat.card V ≤ (q + S) * U

theorem fft_parts_lower_bound {k S h : ℕ} (hS : 1 ≤ S)
    {P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hP : IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P) :
    (2 : ℝ) ^ k * (k + 1) ≤ h * (S * Real.logb 2 (2 * S))

theorem fft_parts_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1) / (p.2 * Real.log p.2))
      =O[𝓟 {p | 1 ≤ p.1 ∧ 2 ≤ p.2}]
      fun p => (minDominatorParts (fftEdge p.1) (Finset.univ.filter (·.1 = 0)) p.2 : ℝ)

end Target.RedBluePebbleGame
```

## Phase 2, round 1, 2026-09-27 (superseded for the four general statements)

Phase 2 adds Hong and Kung's §3 partitions, their Theorem 3.1 (corrected) and Lemma 3.1, and
their Theorem 4.1. The round renders the six new statements. The five new definitions they are
stated through, and the four Phase 1 definitions, were sent with them.

### What was sent

- **Taken from:** an uncommitted draft on branch `hong-kung`, based on `30b9d4a`, on 2026-09-27.
  Nothing containing an advertised statement is committed before its read, so the text is
  identified by content. The SHA-256 of each stripped module exactly as sent is
  - `6deb76fd709ce886868e299fa2ce90799306604c36eb3f669c478250529d9613` for Module 1;
  - `b441f429ec000e7699248361aeeb35aab8dbdbbc03a03344b4bb4b946e5c1b33` for Module 2.
- **Declarations:** `Target.RedBluePebbleGame.exists_partition_of_hasCompleteCalculation`,
  `.io_lower_bound_of_parts`, `.minIOTime_lower_bound`, `.io_lower_bound_of_dominated_card`,
  `.fft_parts_lower_bound` and `.fft_parts_lower_bound_isBigO`.
- **Definitions they are stated through:** `MiscMath.Computability.RedBluePebbleGame.Dominates`,
  `.IsDominatorPartition`, `.IsPartition`, `.minParts` and `.minDominatorParts`, which are new,
  and `.Step`, `.HasCompleteCalculation`, `.fftEdge` and `.minIOTime` from Phase 1. These nine
  are the only project constants the six statement types reach, transitively. This was checked
  by walking the elaborated statements.
- **Module 1** is the whole of `Spec.lean`, stripped. **Module 2** is the target module's
  preamble and the six new statements, stripped. The four Phase 1 statements are unchanged since
  Phase 1's round 2 rendered them, and were left out.
- **The prompt** was composed as in Phase 1:
  - the same operational opening line;
  - Part 2 of `READBACK.md`, verbatim;
  - the two stripped modules below, labelled "Module 1" and "Module 2".

### Who wrote it

`claude-opus-5-5` (Claude Opus 5.5), as a fresh subagent with no prior context, on 2026-09-27.
Its one tool call was the hand-back that delivered the rendering. It read no file, ran no
command and did not browse; the count of its tool calls was checked in its transcript. It
reported its model ID on the final line of its reply, and that line is left out below.

It rendered the six statements as six blocks. It did not give the definitions blocks of their
own: it unfolded each one inline, in every block that reads it. Every definition the statements
are stated through is covered that way. The rendering is otherwise verbatim; its headings are
demoted one level to fit this file.

### What the comparison found

The intended meaning of every new item was written into the plan before the rendering came back,
and the rendering was compared with it clause by clause. They agree on all six statements and on
all five new definitions:

- **`Dominates`:** every walk from an input to the dominated set meets the dominator, walks of
  length zero included, so the dominated set's inputs lie in the dominator. The dominator need
  not lie inside the dominated set.
- **`IsDominatorPartition`:** every vertex lies in exactly one part, empty parts allowed; each
  part has a dominator within the bound; an edge from a part to another forces the second's index
  to be at least the first's.
- **`IsPartition`:** additionally, at most the bound's number of vertices of a part have no
  out-neighbour in that part. The classical decision procedure does not appear in the rendering,
  as intended: it cannot change the count.
- **`minParts`, `minDominatorParts`:** the least number of parts, and `0` where there is none.
  The rendering flags `0` as a default.
- **Theorem 3.1, corrected (`exists_partition_of_hasCompleteCalculation`):**
  - the four graph hypotheses, with the sink condition one-directional;
  - the 2S bound in the dominator and minimum-set conditions;
  - `q ≤ S·h ≤ q + S` in ℕ, with no subtraction.
- **Lemma 3.1:**
  - finitary (`io_lower_bound_of_parts`): `S·h₀ ≤ q + S`;
  - as printed (`minIOTime_lower_bound`): `S·(P(2S) − 1) ≤ Q` with the subtraction in ℤ, not
    truncated.
- **The bridge (`io_lower_bound_of_dominated_card`):** `S·|V| ≤ (q + S)·U`, with `D` and `W`
  quantified independently.
- **Theorem 4.1, finitary (`fft_parts_lower_bound`):** the dominator bound is `S`, not `2S`, and
  there is no minimum-set condition.
- **Theorem 4.1 as printed (`fft_parts_lower_bound_isBigO`):** one constant, chosen before `k`
  and `S`, for every `k ≥ 1` and `S ≥ 2`. `P_D(S)` takes a genuine value on that whole range.

The rendering surfaced one point that the intended account had missed. It is correct, and it was
checked by hand and by brute force:

1. **For `S ≤ 1` the hypotheses of the four general statements force the graph to be empty.**
   - A nonempty finite acyclic graph has a vertex `s` with no out-neighbour.
   - `s` is an output, hence not an input, hence has an in-neighbour `u ≠ s`.
   - The first pebble `s` receives can only come from computing it, which needs `u` red as well.
     So a calculation of a nonempty graph needs `S ≥ 2`.
   - The intended account had argued only the case `S = 0`.
   - Brute force: none of the 814 nonempty graphs on at most 5 vertices (inputs the sources,
     outputs the sinks) has a calculation with `S ≤ 1`.
   - Like `1 ≤ S` in Phase 1, this restricts nothing, since the calculation hypothesis implies
     it. It belongs in the roof docstring.

It confirmed the point the intended account had recorded: empty parts can always be appended, so
`q ≤ S·h` can always be met, and `S·h ≤ q + S` is what bounds `h`. The paper's own construction
produces empty parts too, so its statement has the same slack. The roof docstring should say so.

It also noted three facts the intended account had left implicit; all are correct:

- For `S ≥ 1`, 2S-partitions of a finite acyclic graph exist: the singletons, in a topological
  order. So `hparts` is never vacuous there, and `P(2S)` is a genuine minimum wherever a
  calculation exists.
- In the bridge, taking `D = W` shows that `U ≥ min(2S, |V|)` is forced.
- At `S = 1`, Theorem 4.1's finitary form says `h ≥ |V|`. This matches the exact values
  `P_D(1) = 4` and `12` computed for the 2- and 4-point FFT.

No error was found in the rendering. Its edge-case claims were checked:

- **Its satisfiability example:** the edge `a → b` with `S = 2` and `q = 2`. The steps are load
  `a`, compute `b`, store `b`, then three deletions; two red pebbles at most.
- `t = 0` forces `I = O = ∅`.
- The singleton families satisfy every condition claimed.
- On the asymptotic statement's range both sides are positive, so the absolute values change
  nothing there.

### The rendering, verbatim

#### `exists_partition_of_hasCompleteCalculation`

**Binders** (all universally quantified, in this order)

- $V$: a type, in any universe. It carries an instance deciding equality on $V$, which has no mathematical content, and an instance asserting that $V$ is finite. $V$ may be empty.
- $E$: a binary relation on $V$, read as a directed graph on the vertex set $V$. Write $u \to v$ for $E(u,v)$. A *walk from $x$ to $w$* is a sequence of vertices $x = a_0, a_1, \dots, a_n = w$ with $n \ge 0$ and $a_m \to a_{m+1}$ for every $m < n$. When $n = 0$ it is the single vertex $x = w$.
- $I$, $O$: finite subsets of $V$.
- $S$, $q$: natural numbers.

**Hypotheses**

- (hE) No vertex has a walk of length $n \ge 1$ to itself, i.e. the transitive closure of $E$ is irreflexive. The graph has no directed cycle, and in particular $v \to v$ holds for no $v$.
- (hI) For every $v \in V$: $v \in I$ if and only if there is no $u \in V$ with $u \to v$. So $I$ is exactly the set of vertices with no incoming edge.
- (hO) For every $v \in V$: if there is no $w \in V$ with $v \to w$, then $v \in O$. This goes in one direction only. $O$ contains every vertex with no outgoing edge and may contain other vertices too.
- (hIO) $I$ and $O$ are disjoint.
- (hq) There exist:
  - a natural number $t$ ($t = 0$ is allowed),
  - pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$,
  - natural numbers $c_0,\dots,c_{t-1}$,

  such that:
  1. $(R_0,B_0) = (\emptyset, I)$.
  2. $(R_t,B_t) = (\emptyset, O)$. The final $B$ must equal $O$ exactly, not merely contain it.
  3. $|R_j| \le S$ for every $j = 0,\dots,t$. There is no bound on the $B_j$, which may contain any vertices.
  4. For each $i = 0,\dots,t-1$ there is a vertex $v$ such that the passage from $(R_i,B_i)$ to $(R_{i+1},B_{i+1})$ with cost $c_i$ is one of the following five:
     - *load*: $v \in B_i$ and $v \notin R_i$. The next pair is $(R_i \cup \{v\}, B_i)$ and $c_i = 1$.
     - *store*: $v \in R_i$ and $v \notin B_i$. The next pair is $(R_i, B_i \cup \{v\})$ and $c_i = 1$.
     - *compute*: $v \notin I$, $v \notin R_i$, and every $u$ with $u \to v$ lies in $R_i$. The next pair is $(R_i \cup \{v\}, B_i)$ and $c_i = 0$.
     - *delete from $R$*: $v \in R_i$. The next pair is $(R_i \setminus \{v\}, B_i)$ and $c_i = 0$.
     - *delete from $B$*: $v \in B_i$. The next pair is $(R_i, B_i \setminus \{v\})$ and $c_i = 0$.
  5. $c_0 + \dots + c_{t-1} = q$, where the empty sum is $0$.

**Conclusion.** There exist a natural number $h$ and finite subsets $P_0,\dots,P_{h-1}$ of $V$ satisfying (a) to (d) below. They are chosen after everything above and may depend on all of it.

- (a) Every $v \in V$ lies in exactly one $P_i$. So the $P_i$ are pairwise disjoint and cover $V$. Empty $P_i$ are allowed.
- (b) For each $i$ there is a finite set $D_i \subseteq V$, chosen after the family, with $|D_i| \le 2S$, such that the following holds: for every $x \in I$ with $x \notin D_i$ and every $w \in P_i$, there is no walk from $x$ to $w$ all of whose vertices lie outside $D_i$.
  - Equivalently, every walk from a vertex of $I$ to a vertex of $P_i$ contains a vertex of $D_i$. Walks of length zero are included, so $I \cap P_i \subseteq D_i$.
  - $D_i$ is otherwise unrestricted. It need not lie inside $P_i$.
- (c) For all indices $i, j$ and all $u \in P_i$, $v \in P_j$: if $u \to v$ then $i \le j$.
- (d) For each $i$, at most $2S$ vertices $v \in P_i$ have no $w \in P_i$ with $v \to w$.

In addition, $q \le S\cdot h$ and $S\cdot h \le q + S$. This is natural-number arithmetic and no subtraction occurs.

*Edge cases.*
- **What (hI), (hO) and (hIO) say together.** $I$ is exactly the set of vertices with no incoming edge. $O$ is any set that contains every vertex with no outgoing edge and no vertex with no incoming edge. No vertex may have neither incoming nor outgoing edges.
- **Empty $V$.** $V = \emptyset$ is allowed. Then $I = O = \emptyset$, no step exists, $t = 0$ and $q = 0$. The conclusion then only asks for some $h$ with $S h \le S$, for example $h = 0$ with the empty family.
- **$t = 0$.** This forces $I = O$, hence $I = O = \emptyset$ by (hIO), and $q = 0$.
- **$S \le 1$.** The hypotheses force $V = \emptyset$. Suppose $V \ne \emptyset$:
  - Finiteness and (hE) give a vertex $s$ with no outgoing edge.
  - $s \in O$ by (hO), so $s \notin I$ by (hIO).
  - By (hI) and (hE), $s$ has an in-neighbour $u \ne s$.
  - $s \notin R_0 \cup B_0$ but $s \in B_t$. A load of $s$ needs $s$ already in $B$, and a store needs it already in $R$. So the first step that puts $s$ into $R \cup B$ is a compute of $s$.
  - After that step $\{u,s\} \subseteq R_{i+1}$, so $S \ge 2$.

  Hence for nonempty $V$ the statement has content only when $S \ge 2$.
- **What $q$ counts.** Each $c_i$ is $0$ or $1$, according to the kind of move used to justify step $i$. So $q$ is the number of steps justified as a load or a store.
- **One step can have two costs.** The transition $(R,B) \to (R \cup \{v\}, B)$ is both a load (cost 1) and a compute (cost 0) when $v \in B \setminus R$, $v \notin I$ and all in-neighbours of $v$ lie in $R$. So one sequence of pairs can witness (hq) for several values of $q$, and the theorem applies to each of them.
- **Padding with empty parts.** Appending empty parts to a family satisfying (a) to (d) gives another such family, taking $D_i = \emptyset$ for the new parts. So for $S \ge 1$ the requirement $q \le S h$ can always be met by padding, and it is $S h \le q + S$ that bounds $h$ from above.
- **Other points.** When $V \ne \emptyset$, (a) forces $h \ge 1$. The bound in (b) and (d) is $2S$, while the bound on the $R_j$ is $S$.
- **Satisfiability.** The hypotheses can all hold with $V \ne \emptyset$. Take $V = \{a,b\}$ with the single edge $a \to b$, $I = \{a\}$, $O = \{b\}$, $S = 2$ and $q = 2$. The steps are: load $a$; compute $b$; store $b$; delete $a$ from $R$; delete $b$ from $R$; delete $a$ from $B$.

---

#### `io_lower_bound_of_parts`

**Binders** (all universally quantified, in this order)

- $V$: a type, in any universe, with an instance deciding equality (no mathematical content) and an instance asserting that $V$ is finite. $V$ may be empty.
- $E$: a binary relation on $V$, read as a directed graph; write $u \to v$ for $E(u,v)$. A *walk from $x$ to $w$* is a sequence $x = a_0,\dots,a_n = w$ with $n \ge 0$ and $a_m \to a_{m+1}$ for every $m < n$. When $n = 0$ it is the single vertex $x = w$.
- $I$, $O$: finite subsets of $V$.
- $S$, $q$, $h_0$: natural numbers.

**Hypotheses**

- (hE) No vertex has a walk of length $n \ge 1$ to itself. There is no directed cycle, and in particular no $v \to v$.
- (hI) For every $v$: $v \in I$ if and only if no $u$ has $u \to v$. So $I$ is exactly the set of vertices with no incoming edge.
- (hO) For every $v$: if no $w$ has $v \to w$, then $v \in O$. This goes in one direction only, so $O$ may contain further vertices.
- (hIO) $I \cap O = \emptyset$.
- (hparts) Take any natural number $h$ and any finite subsets $P_0,\dots,P_{h-1}$ of $V$ that together satisfy (a) to (d) below. Then $h_0 \le h$. In other words, $h_0$ is at most the number of parts of every such family.
  - (a) Every $v \in V$ lies in exactly one $P_i$. Empty $P_i$ are allowed.
  - (b) For each $i$ there is a finite $D_i \subseteq V$ with $|D_i| \le 2S$ such that: for every $x \in I \setminus D_i$ and every $w \in P_i$, no walk from $x$ to $w$ has all its vertices outside $D_i$. Equivalently, every walk from $I$ to $P_i$, length zero included, meets $D_i$, so $I \cap P_i \subseteq D_i$. $D_i$ need not lie inside $P_i$.
  - (c) For all $i, j$ and all $u \in P_i$, $v \in P_j$: if $u \to v$ then $i \le j$.
  - (d) For each $i$, at most $2S$ vertices $v \in P_i$ have no $w \in P_i$ with $v \to w$.
- (hq) There exist a natural number $t$ ($t = 0$ allowed), pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$, and natural numbers $c_0,\dots,c_{t-1}$, such that:
  1. $(R_0,B_0) = (\emptyset, I)$.
  2. $(R_t,B_t) = (\emptyset, O)$ exactly.
  3. $|R_j| \le S$ for all $j = 0,\dots,t$. The $B_j$ are unbounded.
  4. For each $i < t$ there is a vertex $v$ for which the passage from $(R_i,B_i)$ to $(R_{i+1},B_{i+1})$ with cost $c_i$ is one of:
     - load: $v \in B_i \setminus R_i$; add $v$ to $R$; cost $1$.
     - store: $v \in R_i \setminus B_i$; add $v$ to $B$; cost $1$.
     - compute: $v \notin I$, $v \notin R_i$, and all $u$ with $u \to v$ are in $R_i$; add $v$ to $R$; cost $0$.
     - delete from $R$: $v \in R_i$; remove $v$ from $R$; cost $0$.
     - delete from $B$: $v \in B_i$; remove $v$ from $B$; cost $0$.

     In every case the component not mentioned is unchanged.
  5. $c_0 + \dots + c_{t-1} = q$, where the empty sum is $0$.

**Conclusion.** $S\cdot h_0 \le q + S$ in the natural numbers. Equivalently, $S\,(h_0 - 1) \le q$ with the subtraction done in the integers.

*Edge cases.*
- **Trivial instances.** $h_0 = 0$ makes (hparts) and the conclusion trivial. $S = 0$ makes the conclusion $0 \le q$.
- **When no family exists.** (hparts) ranges over all families, including ones with empty parts. If no family satisfies (a) to (d) with bound $2S$, then (hparts) holds for every $h_0$.
- **When families do exist.** For $S \ge 1$ and finite $V$ satisfying (hE), such families exist: take the singletons $\{v\}$ listed in a topological order of the graph, with $D_i = P_i$. (hparts) then says exactly that $h_0$ is at most the least admissible number of parts.
- **What (hI), (hO) and (hIO) say together.** $I$ is exactly the set of vertices with no incoming edge. $O$ contains every vertex with no outgoing edge and no vertex with no incoming edge. No vertex may have neither incoming nor outgoing edges.
- **Empty $V$ and $t = 0$.** $V = \emptyset$ is allowed; then $t = 0$ and $q = 0$. $t = 0$ forces $I = O = \emptyset$.
- **$S \le 1$.** The hypotheses force $V = \emptyset$. Suppose $V \ne \emptyset$:
  - There is a vertex $s$ with no outgoing edge.
  - $s$ lies in $O$, not in $I$, and has an in-neighbour $u \ne s$.
  - $s$ first enters $R \cup B$ only through a compute, after which $\{u,s\} \subseteq R$. So $S \ge 2$.
- **One step can have two costs.** A transition that adds $v$ to $R$ is both a load (cost 1) and a compute (cost 0) when $v \in B \setminus R$, $v \notin I$ and all in-neighbours of $v$ are in $R$. So $q$ is not determined by the sequence of pairs alone. $q$ is the number of steps justified as a load or a store.
- **Satisfiability.** Take $V = \{a,b\}$ with the single edge $a \to b$, $I = \{a\}$, $O = \{b\}$, $S = 2$ and $q = 2$. The steps are: load $a$, compute $b$, store $b$, delete $a$ and $b$ from $R$, delete $a$ from $B$. With $h_0 = 1$, (hparts) holds, because $V \ne \emptyset$ forces $h \ge 1$. The conclusion then reads $2 \le 4$.

---

#### `minIOTime_lower_bound`

**Binders** (all universally quantified, in this order)

- $V$: a type, in any universe, with an instance deciding equality (no mathematical content) and an instance asserting that $V$ is finite. $V$ may be empty.
- $E$: a binary relation on $V$, read as a directed graph; write $u \to v$. Walks are defined as above: $x = a_0 \to \dots \to a_n = w$ with $n \ge 0$, and $n = 0$ means $x = w$.
- $I$, $O$: finite subsets of $V$.
- $S$: a natural number.

**Hypotheses**

- (hE) There is no walk of length $\ge 1$ from any vertex to itself. So there is no directed cycle and no $v \to v$.
- (hI) $v \in I$ if and only if $v$ has no incoming edge, for every $v$.
- (hO) Every vertex with no outgoing edge lies in $O$. This goes in one direction only.
- (hIO) $I \cap O = \emptyset$.
- (hcalc) There is a natural number $q$ for which the following exist: a natural number $t$ ($t = 0$ allowed), pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$, and natural numbers $c_0,\dots,c_{t-1}$, such that:
  - $(R_0,B_0) = (\emptyset,I)$.
  - $(R_t,B_t) = (\emptyset,O)$ exactly.
  - $|R_j| \le S$ for all $j$. The $B_j$ are unbounded.
  - Each passage from $(R_i,B_i)$ to $(R_{i+1},B_{i+1})$ with cost $c_i$ is, for some vertex $v$, one of:
    - load: $v \in B_i \setminus R_i$; $R$ gains $v$; cost $1$.
    - store: $v \in R_i \setminus B_i$; $B$ gains $v$; cost $1$.
    - compute: $v \notin I$, $v \notin R_i$, and all in-neighbours of $v$ are in $R_i$; $R$ gains $v$; cost $0$.
    - delete from $R$: $v \in R_i$; cost $0$.
    - delete from $B$: $v \in B_i$; cost $0$.

    The component not mentioned is unchanged.
  - $\sum_i c_i = q$, where the empty sum is $0$.

**Conclusion.** As an inequality between integers,
$$S\cdot(m_P - 1) \le m_{IO}.$$

- **$m_P$** is the infimum, in $\mathbb{N}$, of the set of natural numbers $h$ for which some finite subsets $P_0,\dots,P_{h-1}$ of $V$ satisfy all of:
  - (a) Every $v \in V$ lies in exactly one $P_i$. Empty parts are allowed.
  - (b) For each $i$ there is a finite $D_i \subseteq V$ with $|D_i| \le 2S$ such that: for every $x \in I \setminus D_i$ and every $w \in P_i$, no walk from $x$ to $w$ has all its vertices outside $D_i$. Equivalently, every walk from $I$ to $P_i$, length zero included, meets $D_i$.
  - (c) If $u \in P_i$, $v \in P_j$ and $u \to v$, then $i \le j$.
  - (d) For each $i$, at most $2S$ vertices of $P_i$ have no out-neighbour in $P_i$.

  By Mathlib's convention for infima of sets of natural numbers, $m_P$ is the least such $h$ if one exists, and $0$ if none exists.
- **$m_{IO}$** is the infimum, in $\mathbb{N}$, of the set of natural numbers $q$ for which a calculation as in (hcalc) with total cost $q$ exists. By (hcalc) this set is nonempty, so $m_{IO}$ is its least element.
- **Casting.** $S$, $m_P$ and $m_{IO}$ are converted to integers before the arithmetic. So $m_P - 1$ is ordinary integer subtraction, equal to $-1$ when $m_P = 0$. It is not truncated.

*Edge cases.*
- **$m_P = 0$.** The left side is then $-S$ and the inequality holds automatically. $m_P = 0$ happens when $V = \emptyset$ (the empty family, $h = 0$, qualifies) or when no family qualifies.
- **When $m_P$ is a genuine minimum.** For $S \ge 1$ and nonempty $V$ satisfying (hE), families do qualify: take singletons in a topological order with $D_i = P_i$. And $h = 0$ does not qualify. So $m_P \ge 1$ is a genuine minimum.
- **$S = 0$.** The left side is $0$.
- **$S \le 1$.** The hypotheses force $V = \emptyset$. A vertex $s$ with no outgoing edge would lie in $O \setminus I$ and have an in-neighbour $u \ne s$. It could first enter $R \cup B$ only by a compute, putting both $u$ and $s$ in $R$, so $S \ge 2$. With $V = \emptyset$, $m_P = 0$ and $m_{IO} = 0$, and the inequality reads $-S \le 0$.
- **How $m_{IO}$ counts cost.** $m_{IO}$ minimises over all calculations and all admissible cost labellings. A transition that is both a load and a compute can be counted at cost $0$. That happens when $v \in B \setminus R$, $v \notin I$ and all in-neighbours of $v$ are in $R$.
- **What (hI), (hO) and (hIO) say together.** $I$ is exactly the set of vertices with no incoming edge. $O$ contains all vertices with no outgoing edge and none with no incoming edge. No vertex may have neither incoming nor outgoing edges.
- **Two bounds.** The partition bound is $2S$, while the calculation bound is $S$.
- **Satisfiability.** Take $V = \{a,b\}$ with the single edge $a \to b$, $I = \{a\}$, $O = \{b\}$ and $S = 2$. (hcalc) holds via: load $a$, compute $b$, store $b$, delete $a$ and $b$ from $R$, delete $a$ from $B$.

---

#### `io_lower_bound_of_dominated_card`

**Binders** (all universally quantified, in this order)

- $V$: a type, in any universe, with an instance deciding equality (no mathematical content) and an instance asserting that $V$ is finite. $V$ may be empty.
- $E$: a binary relation on $V$, read as a directed graph; write $u \to v$. A walk from $x$ to $w$ is $x = a_0 \to a_1 \to \dots \to a_n = w$ with $n \ge 0$, and $n = 0$ means $x = w$.
- $I$, $O$: finite subsets of $V$.
- $S$, $q$, $U$: natural numbers.

**Hypotheses**

- (hE) There is no walk of length $\ge 1$ from any vertex to itself. So there is no directed cycle and no $v \to v$.
- (hI) For every $v$: $v \in I$ if and only if $v$ has no incoming edge.
- (hO) Every vertex with no outgoing edge lies in $O$. This goes in one direction only.
- (hIO) $I \cap O = \emptyset$.
- (hU) Take any finite subsets $D$ and $W$ of $V$, quantified independently. Suppose $|D| \le 2S$, and suppose that for every $x \in I \setminus D$ and every $w \in W$ there is no walk from $x$ to $w$ all of whose vertices lie outside $D$. Then $|W| \le U$. The walk condition is equivalent to: every walk from a vertex of $I$ to a vertex of $W$, length zero included, contains a vertex of $D$.
- (hq) There exist a natural number $t$ ($t = 0$ allowed), pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$, and natural numbers $c_0,\dots,c_{t-1}$, such that:
  - $(R_0,B_0) = (\emptyset,I)$.
  - $(R_t,B_t) = (\emptyset,O)$ exactly.
  - $|R_j| \le S$ for all $j = 0,\dots,t$. The $B_j$ are unbounded.
  - Each passage from $(R_i,B_i)$ to $(R_{i+1},B_{i+1})$ with cost $c_i$ is, for some vertex $v$, one of:
    - load: $v \in B_i \setminus R_i$; $R$ gains $v$; cost $1$.
    - store: $v \in R_i \setminus B_i$; $B$ gains $v$; cost $1$.
    - compute: $v \notin I$, $v \notin R_i$, and every $u$ with $u \to v$ is in $R_i$; $R$ gains $v$; cost $0$.
    - delete from $R$: $v \in R_i$; $R$ loses $v$; cost $0$.
    - delete from $B$: $v \in B_i$; $B$ loses $v$; cost $0$.

    The component not mentioned is unchanged.
  - $c_0 + \dots + c_{t-1} = q$, where the empty sum is $0$.

**Conclusion.** $S\cdot|V| \le (q + S)\cdot U$ in the natural numbers. Here $|V|$ is Mathlib's natural-number cardinality of $V$. It is the number of elements for a finite type, as here, and would be $0$ for an infinite one.

*Edge cases.*
- **Large $U$.** Every $U \ge |V|$ satisfies (hU), since no subset of $V$ has more than $|V|$ elements. For such $U$ the conclusion holds automatically.
- **What (hU) forces.** Taking $D = W$ in (hU) shows that $U \ge |W|$ for every $W$ with $|W| \le 2S$, i.e. $U \ge \min(2S, |V|)$.
- **Freedom in $D$ and $W$.** $D$ need not be related to $W$. $W = \emptyset$ imposes nothing.
- **$S = 0$.** The conclusion is $0 \le qU$.
- **Empty $V$ and $S \le 1$.** $V = \emptyset$ is allowed; then $q = 0$ and both sides are $0$. For $S \le 1$ the hypotheses force $V = \emptyset$. A vertex $s$ with no outgoing edge would lie in $O \setminus I$ and have an in-neighbour $u \ne s$. It could first enter $R \cup B$ only through a compute, putting $u$ and $s$ in $R$ together, so $S \ge 2$.
- **One step can have two costs.** A transition that adds $v$ to $R$ is both a load (cost 1) and a compute (cost 0) when $v \in B \setminus R$, $v \notin I$ and all in-neighbours of $v$ are in $R$. So $q$, the number of steps justified as a load or a store, is not determined by the pairs alone.
- **What (hI), (hO) and (hIO) say together.** $I$ is exactly the set of vertices with no incoming edge. $O$ contains every vertex with no outgoing edge and no vertex with no incoming edge. No vertex may have neither incoming nor outgoing edges.
- **Satisfiability.** Take $V = \{a,b\}$ with the single edge $a \to b$, $I = \{a\}$, $O = \{b\}$, $S = 2$, $q = 2$ and $U = 2$. The conclusion then reads $4 \le 8$.

---

#### `fft_parts_lower_bound`

**Binders** (all universally quantified, in this order)

- $k$, $S$, $h$: natural numbers.
- (hS): a hypothesis, stated below.
- $P$: a family $P_0,\dots,P_{h-1}$, indexed by $\{0,\dots,h-1\}$, of subsets of the finite set $G_k$ defined next.
- (hP): a hypothesis, stated below.

**Definitions used**

- **Vertex set.** $G_k$ is the set of pairs $(\ell, x)$ with $\ell \in \{0,1,\dots,k\}$ and $x \in \{0,1,\dots,2^k-1\}$. It has $(k+1)2^k$ elements.
- **Edge relation.** $(\ell,x) \to_k (\ell',x')$ holds if and only if both of these hold:
  - $\ell' = \ell + 1$ as natural numbers. So there is no wrap-around from level $k$.
  - Either $x' = x$ or $x' = x \oplus 2^{\ell}$. Here $\oplus$ is bitwise exclusive-or of natural numbers, so $x \oplus 2^\ell$ is $x$ with its binary digit of place value $2^\ell$ flipped. The exponent $\ell$ is the level of the tail vertex.
- **Consequences of the edge relation.**
  - Every vertex at a level $\ell < k$ has exactly two out-neighbours, $(\ell+1,x)$ and $(\ell+1,x\oplus 2^\ell)$. Level-$k$ vertices have none.
  - Every vertex at level $\ge 1$ has exactly two in-neighbours. Level-$0$ vertices have none.
  - There are no directed cycles.
- **Input set.** $I_k = \{(0,x) : 0 \le x < 2^k\}$, the $2^k$ level-0 vertices.
- **Walks.** A walk from $x$ to $w$ is $x = a_0 \to_k a_1 \to_k \dots \to_k a_n = w$ with $n \ge 0$. When $n = 0$ it means $x = w$.

**Hypotheses**

- (hS) $S \ge 1$.
- (hP) The family satisfies all of:
  - (a) Every vertex of $G_k$ lies in exactly one $P_i$. Empty $P_i$ are allowed.
  - (b) For each $i$ there is a set $D_i \subseteq G_k$ with $|D_i| \le S$ such that: for every $x \in I_k \setminus D_i$ and every $w \in P_i$, there is no walk from $x$ to $w$ all of whose vertices lie outside $D_i$.
    - Equivalently, every walk from a level-0 vertex to a vertex of $P_i$, length zero included, contains a vertex of $D_i$. In particular, the level-0 vertices of $P_i$ must lie in $D_i$.
    - $D_i$ need not lie inside $P_i$.
  - (c) For all $i, j$ and all $u \in P_i$, $v \in P_j$: if $u \to_k v$ then $i \le j$.

  Nothing limits how many vertices of a part lack an out-neighbour inside that part.

**Conclusion.** In the real numbers,
$$2^k\,(k+1) \le h\cdot\bigl(S\cdot\log_2(2S)\bigr).$$
- $k$, $h$ and $S$ are the given natural numbers viewed as reals.
- $\log_2$ is Mathlib's base-2 logarithm, $\log_2 y = \ln y/\ln 2$. Mathlib's $\ln$ gives $\ln|y|$ for $y \ne 0$ and $0$ at $0$.
- Here $2S \ge 2$, so this is the ordinary base-2 logarithm and $\log_2(2S) = 1 + \log_2 S \ge 1$.
- The left side equals the number of vertices $|G_k|$.

*Edge cases.*
- **$k = 0$.** $G_0 = \{(0,0)\} = I_0$ and there are no edges. The conclusion reads $1 \le h\,S\log_2(2S)$.
- **Size of $h$.** $G_k$ is never empty, so (a) forces $h \ge 1$. Because empty parts are allowed, any admissible $h$ can be enlarged by padding.
- **$S = 1$.** $\log_2 2 = 1$, so the conclusion reads $2^k(k+1) \le h$.
- **No junk values.** (hS) keeps the logarithm's argument at least $2$, so no junk value arises.
- **Satisfiability.** (hP) can hold for every $k$ and every $S \ge 1$. Take singleton parts listed by nondecreasing level, with $D_i = P_i$ and $h = (k+1)2^k$.
- **$S$ unbounded.** $S$ has no upper bound.
- **Bound in (b).** The bound in (b) is $S$ itself, not $2S$.

---

#### `fft_parts_lower_bound_isBigO`

**Binders.** The statement has no binders or hypotheses of its own. The two functions compared are functions of a pair $p = (k, S)$ of natural numbers.

**Statement.** There is a real number $c$, chosen once and before $k$ and $S$, such that for every pair of natural numbers $(k,S)$ with $k \ge 1$ and $S \ge 2$:
$$\left|\frac{2^k\cdot\ln(2^k)}{S\cdot\ln S}\right| \le c\cdot|M(k,S)|.$$

- $\ln$ is the natural logarithm, so $\ln(2^k) = k\ln 2$. $S$ is viewed as a real number.
- $M(k,S)$ is a natural number, viewed as a real. It is the infimum, in $\mathbb{N}$, of the set of natural numbers $h$ for which there are subsets $P_0,\dots,P_{h-1}$ of $G_k$ satisfying (a) to (c) below. By Mathlib's convention this is the least such $h$ if one exists, and $0$ if none exists.
  - **Vertex set.** $G_k$ is the set of pairs $(\ell,x)$ with $0 \le \ell \le k$ and $0 \le x < 2^k$.
  - **Edges.** $(\ell,x) \to_k (\ell',x')$ if and only if $\ell' = \ell+1$ (in $\mathbb{N}$, no wrap-around) and either $x' = x$ or $x' = x \oplus 2^\ell$, with $\oplus$ bitwise exclusive-or.
  - **Inputs.** $I_k$ is the set of level-0 vertices $\{(0,x)\}$.
  - **Walks** are defined as in the previous block, length zero included.
  - (a) Every vertex of $G_k$ lies in exactly one $P_i$. Empty parts are allowed.
  - (b) For each $i$ there is $D_i \subseteq G_k$ with $|D_i| \le S$ such that: for every $x \in I_k \setminus D_i$ and every $w \in P_i$, no walk from $x$ to $w$ has all its vertices outside $D_i$. Equivalently, every walk from a level-0 vertex to $P_i$ meets $D_i$.
  - (c) If $u \in P_i$, $v \in P_j$ and $u \to_k v$, then $i \le j$.

**Formal form.** Formally this is Mathlib's big-O relation: the first function is big-O of the second along the principal filter of $A = \{(k,S) : 1 \le k \text{ and } 2 \le S\}$.
- Mathlib's big-O means: there exists a real $c$ such that, eventually along the filter, $|f| \le c\,|g|$.
- "Eventually along the principal filter of $A$" means "at every point of $A$".
- So this is one inequality holding uniformly over all of $A$ with a single constant. It is not a statement about large $k$ or large $S$ only.

*Edge cases.*
- **Excluded points.** Points with $k = 0$ or $S \le 1$ are excluded. At those points the left formula would involve $\ln 1 = 0$ or $\ln 0 = 0$ (Mathlib's convention) and division by zero, which Mathlib defines as $0$.
- **Positivity on $A$.** On $A$, $S\ln S \ge 2\ln 2 > 0$ and $\ln(2^k) = k\ln 2 > 0$. So the left side is strictly positive there, and the inequality forces $c > 0$ and $M(k,S) \ge 1$. Both sides are nonnegative on $A$, so the absolute values change nothing there.
- **$M$ on $A$.** The default value $0$ of $M$ never occurs on $A$.
  - $h = 0$ does not qualify, because $G_k \ne \emptyset$.
  - For $S \ge 1$, singleton parts listed by nondecreasing level, with $D_i = P_i$, do qualify.
  - So $M(k,S)$ is a genuine minimum there.
- **Which bound $M$ uses.** $M$ uses the bound $S$ in (b), not $2S$, and only conditions (a) to (c). Nothing limits how many vertices of a part lack an out-neighbour inside the part.
- **Range of $k$ and $S$.** $k$ ranges over all integers $\ge 1$ and $S$ over all integers $\ge 2$, independently. $S$ may exceed $|G_k|$.

### The Lean sent

Module 1:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice.Nat

namespace MiscMath.Computability.RedBluePebbleGame

variable {V : Type*} [DecidableEq V]

inductive Step (E : V → V → Prop) (I : Finset V) :
    Finset V × Finset V → ℕ → Finset V × Finset V → Prop
  | load {R B : Finset V} {v : V} (hB : v ∈ B) (hR : v ∉ R) :
      Step E I (R, B) 1 (insert v R, B)
  | store {R B : Finset V} {v : V} (hR : v ∈ R) (hB : v ∉ B) :
      Step E I (R, B) 1 (R, insert v B)
  | compute {R B : Finset V} {v : V} (hI : v ∉ I) (hR : v ∉ R) (hpred : ∀ u, E u v → u ∈ R) :
      Step E I (R, B) 0 (insert v R, B)
  | deleteRed {R B : Finset V} {v : V} (hR : v ∈ R) :
      Step E I (R, B) 0 (R.erase v, B)
  | deleteBlue {R B : Finset V} {v : V} (hB : v ∈ B) :
      Step E I (R, B) 0 (R, B.erase v)

def HasCompleteCalculation (E : V → V → Prop) (I O : Finset V) (S q : ℕ) : Prop :=
  ∃ (t : ℕ) (σ : Fin (t + 1) → Finset V × Finset V) (c : Fin t → ℕ),
    σ 0 = (∅, I) ∧
    σ (Fin.last t) = (∅, O) ∧
    (∀ j, (σ j).1.card ≤ S) ∧
    (∀ i : Fin t, Step E I (σ i.castSucc) (c i) (σ i.succ)) ∧
    ∑ i, c i = q

def fftEdge (k : ℕ) (u v : Fin (k + 1) × Fin (2 ^ k)) : Prop :=
  (v.1 : ℕ) = (u.1 : ℕ) + 1 ∧
    ((v.2 : ℕ) = (u.2 : ℕ) ∨ (v.2 : ℕ) = (u.2 : ℕ) ^^^ 2 ^ (u.1 : ℕ))

noncomputable def minIOTime (E : V → V → Prop) (I O : Finset V) (S : ℕ) : ℕ :=
  sInf {q | HasCompleteCalculation E I O S q}

omit [DecidableEq V] in
def Dominates (E : V → V → Prop) (I D W : Finset V) : Prop :=
  ∀ x ∈ I, x ∉ D → ∀ w ∈ W, ¬ Relation.ReflTransGen (fun a b => E a b ∧ a ∉ D ∧ b ∉ D) x w

omit [DecidableEq V] in
def IsDominatorPartition {h : ℕ} (E : V → V → Prop) (I : Finset V) (S : ℕ)
    (P : Fin h → Finset V) : Prop :=
  (∀ v, ∃! i, v ∈ P i) ∧
    (∀ i, ∃ D : Finset V, D.card ≤ S ∧ Dominates E I D (P i)) ∧
    ∀ i j, ∀ u ∈ P i, ∀ v ∈ P j, E u v → i ≤ j

omit [DecidableEq V] in
open Classical in
def IsPartition {h : ℕ} (E : V → V → Prop) (I : Finset V) (S : ℕ) (P : Fin h → Finset V) :
    Prop :=
  IsDominatorPartition E I S P ∧ ∀ i, ((P i).filter fun v => ∀ w ∈ P i, ¬ E v w).card ≤ S

omit [DecidableEq V] in
noncomputable def minParts (E : V → V → Prop) (I : Finset V) (S : ℕ) : ℕ :=
  sInf {h | ∃ P : Fin h → Finset V, IsPartition E I S P}

omit [DecidableEq V] in
noncomputable def minDominatorParts (E : V → V → Prop) (I : Finset V) (S : ℕ) : ℕ :=
  sInf {h | ∃ P : Fin h → Finset V, IsDominatorPartition E I S P}

end MiscMath.Computability.RedBluePebbleGame
```

Module 2:

```lean
import MiscMath.Computability.RedBluePebbleGame.Spec
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Prod

open Filter MiscMath.Computability.RedBluePebbleGame

namespace Target.RedBluePebbleGame

theorem exists_partition_of_hasCompleteCalculation {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q : ℕ}
    (hE : ∀ v, ¬ Relation.TransGen E v v) (hI : ∀ v, v ∈ I ↔ ∀ u, ¬ E u v)
    (hO : ∀ v, (∀ w, ¬ E v w) → v ∈ O) (hIO : Disjoint I O)
    (hq : HasCompleteCalculation E I O S q) :
    ∃ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P ∧ q ≤ S * h ∧ S * h ≤ q + S

theorem io_lower_bound_of_parts {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q h₀ : ℕ}
    (hE : ∀ v, ¬ Relation.TransGen E v v) (hI : ∀ v, v ∈ I ↔ ∀ u, ¬ E u v)
    (hO : ∀ v, (∀ w, ¬ E v w) → v ∈ O) (hIO : Disjoint I O)
    (hparts : ∀ (h : ℕ) (P : Fin h → Finset V), IsPartition E I (2 * S) P → h₀ ≤ h)
    (hq : HasCompleteCalculation E I O S q) :
    S * h₀ ≤ q + S

theorem minIOTime_lower_bound {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S : ℕ}
    (hE : ∀ v, ¬ Relation.TransGen E v v) (hI : ∀ v, v ∈ I ↔ ∀ u, ¬ E u v)
    (hO : ∀ v, (∀ w, ¬ E v w) → v ∈ O) (hIO : Disjoint I O)
    (hcalc : ∃ q, HasCompleteCalculation E I O S q) :
    (S : ℤ) * (minParts E I (2 * S) - 1) ≤ minIOTime E I O S

theorem io_lower_bound_of_dominated_card {V : Type*} [DecidableEq V] [Finite V]
    {E : V → V → Prop} {I O : Finset V} {S q U : ℕ}
    (hE : ∀ v, ¬ Relation.TransGen E v v) (hI : ∀ v, v ∈ I ↔ ∀ u, ¬ E u v)
    (hO : ∀ v, (∀ w, ¬ E v w) → v ∈ O) (hIO : Disjoint I O)
    (hU : ∀ D W : Finset V, D.card ≤ 2 * S → Dominates E I D W → W.card ≤ U)
    (hq : HasCompleteCalculation E I O S q) :
    S * Nat.card V ≤ (q + S) * U

theorem fft_parts_lower_bound {k S h : ℕ} (hS : 1 ≤ S)
    {P : Fin h → Finset (Fin (k + 1) × Fin (2 ^ k))}
    (hP : IsDominatorPartition (fftEdge k) (Finset.univ.filter (·.1 = 0)) S P) :
    (2 : ℝ) ^ k * (k + 1) ≤ h * (S * Real.logb 2 (2 * S))

theorem fft_parts_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1) / (p.2 * Real.log p.2))
      =O[𝓟 {p | 1 ≤ p.1 ∧ 2 ≤ p.2}]
      fun p => (minDominatorParts (fftEdge p.1) (Finset.univ.filter (·.1 = 0)) p.2 : ℝ)

end Target.RedBluePebbleGame
```

## Phase 1, round 2 (current for Phase 1), 2026-09-26

### What changed since round 1

- **`fft_io_bounds`:** the second conjunct is restated in subtractive form, at George's
  request on 2026-09-26. Given `1 ≤ S`, it is equivalent to the product form it replaces;
  this was checked in Lean.
- **`minIOTime` is new.** It is the source's minimum I/O time `Q`: the least total charge of a
  complete calculation.
- **`fft_io_lower_bound_isBigO` is new.** It is Corollary 4.1 in the paper's asymptotic form,
  also at George's request on 2026-09-26.
- **Everything else is unchanged.** It was sent again so that this round renders the whole
  current surface.

### What was sent

- **Taken from:** an uncommitted draft on branch `hong-kung`, based on `088256c`, on
  2026-09-26. The SHA-256 of each stripped module exactly as sent is
  - `188c854454b48fe4d3d97725ffe4fefc52aa5c333c79bdecaf6c508500e0f7b3` for Module 1;
  - `c1310837b4bb9562996ec76221c72003a4cdc4cffdffb3e0a635b7b8dc7fc8e7` for Module 2.
- **Declarations:** `Target.RedBluePebbleGame.fft_io_lower_bound`, `.fft_io_bounds`,
  `.fft_complete_iff` and `.fft_io_lower_bound_isBigO`.
- **Definitions they are stated through:** `MiscMath.Computability.RedBluePebbleGame.Step`,
  `.HasCompleteCalculation`, `.fftEdge` and `.minIOTime`. These are the only project constants
  the four statement types reach, transitively. This was checked by walking the elaborated
  statements.
- **The prompt** was composed as in round 1:
  - the same operational opening line;
  - Part 2 of `READBACK.md`, verbatim;
  - the two stripped modules below, labelled "Module 1" and "Module 2".

### Who wrote it

`claude-opus-5-5` (Claude Opus 5.5), as a fresh subagent with no prior context, on 2026-09-26.
Its one tool call was the hand-back that delivered the rendering. It read no file, ran no
command and did not browse. It reported its model ID on the final line of its reply, and that
line is left out below.

### What the comparison found

The rendering agrees with the intended statements, clause by clause. On the new and changed
items:

- **`minIOTime`** is rendered as the least cost of a complete calculation, with the value 0
  where none exists, from `sInf ∅ = 0`. That value is flagged as meaningless, as the docstring
  says.
- **`fft_io_bounds`, conjunct (b),** is rendered as the subtractive inequality in ℝ, with real
  subtraction, not truncated.
- **`fft_io_lower_bound_isBigO`** is rendered as: one constant `C`, chosen before `k` and `S`,
  with `k·2^k·ln 2 ≤ C·Q(k,S)·ln S` for every `k ≥ 1` and every `S ≥ 3`. It notes that the
  principal filter makes this uniform, not eventual. That is the intended reading.

The rendering surfaced two points that the intended account had left implicit. Both are
correct; they were checked by hand.

1. **Conjunct (b) of `fft_io_bounds` can say nothing.** The rendering shows that its left side
   is `≤ 0` once `S ≥ 2^(k−2)(k+1)`, so (b) adds nothing for `k ≤ 2` wherever a calculation
   exists.
   - The exact threshold is lower: the left side is `≤ 0` exactly when `S ≥ 2^(k−1)`, half the
     number of points.
   - This is the limitation the subtractive form was chosen to make visible. Conjunct (a) and
     `fft_io_lower_bound` carry those cases.
   - It belongs in the roof docstring.
2. **The asymptotic statement cannot be vacuous through `minIOTime`'s value 0.** On its own,
   it entails that at every `(k, S)` with `k ≥ 1` and `S ≥ 3` some calculation exists, and
   none has cost 0. Were there none, `Q` would be `sInf ∅ = 0`, and the inequality would fail
   there.

The rendering also notes that `fft_io_lower_bound_isBigO` uses natural logarithms while the
finitary statements use base 2. That is intended: in a big-O statement the base changes only
the constant.

No error was found in the rendering. Its new edge-case claims were checked:

- whenever `O ⊆ I`, a calculation of cost 0 exists for every `S`;
- a vertex with a self-loop can never be computed;
- the butterfly has no self-loops and has `(k+1)·2^k` vertices.

### The rendering, verbatim

#### `MiscMath.Computability.RedBluePebbleGame.Step`

**Binders.**
- $V$ is a type, in any universe, with decidable equality. The decidable equality is needed to form $R\cup\{v\}$ and $R\setminus\{v\}$ as finite sets.
- $E$ is a binary relation on $V$. Nothing is assumed about it: it need not be finite, acyclic or irreflexive. Below, $u$ is called an *$E$-predecessor* of $v$ when $E(u,v)$.
- $I$ is a finite subset of $V$.

**Definition.** $\mathrm{Step}_{E,I}$ relates three things: a state $(R,B)$, which is an ordered pair of finite subsets of $V$; a natural number $c$; and a second state $(R',B')$. It is generated inductively by five rules, and none of them has a Step premise. So $\mathrm{Step}_{E,I}((R,B),c,(R',B'))$ holds exactly when, for some $v\in V$, one of the following holds:
1. (load) $v\in B$, $v\notin R$, $c=1$ and $(R',B')=(R\cup\{v\},B)$;
2. (store) $v\in R$, $v\notin B$, $c=1$ and $(R',B')=(R,B\cup\{v\})$;
3. (compute) $v\notin I$, $v\notin R$, every $u\in V$ with $E(u,v)$ lies in $R$, $c=0$ and $(R',B')=(R\cup\{v\},B)$;
4. (delete red) $v\in R$, $c=0$ and $(R',B')=(R\setminus\{v\},B)$;
5. (delete blue) $v\in B$, $c=0$ and $(R',B')=(R,B\setminus\{v\})$.

*Edge cases.*
- Only $c\in\{0,1\}$ occurs.
- The cost belongs to the rule, not to the transition. Suppose $v\in B\setminus R$, $v\notin I$ and every $E$-predecessor of $v$ is in $R$. Then the move to $(R\cup\{v\},B)$ is both a load and a compute, and Step holds for it with $c=1$ and also with $c=0$.
- A vertex $v\notin I$ with no $E$-predecessors can be computed at cost 0 from any state with $v\notin R$, including $R=\emptyset$.
- A vertex of $I$ can never be computed. It can only be loaded.
- A vertex with $E(v,v)$ can never be computed, and neither can a vertex with infinitely many $E$-predecessors, since $R$ is finite.
- Compute does not look at $B$, so $v$ may already be in $B$.
- Both deletions apply to any vertex, including vertices of $I$.
- Step itself puts no bound on $|R|$ or $|B|$.

#### `MiscMath.Computability.RedBluePebbleGame.HasCompleteCalculation`

**Binders.**
- $V$ with decidable equality, and a binary relation $E$ on $V$, as for Step.
- Finite sets $I,O\subseteq V$.
- Natural numbers $S$ and $q$.

**Definition.** The predicate holds if and only if there exist:
- a natural number $t$;
- states $(R_0,B_0),\dots,(R_t,B_t)$, each a pair of finite subsets of $V$;
- natural numbers $c_0,\dots,c_{t-1}$.

All of these may depend on $E,I,O,S,q$. They must satisfy:
- $(R_0,B_0)=(\emptyset,I)$.
- $(R_t,B_t)=(\emptyset,O)$. The final red set is empty, and the final blue set is exactly $O$, not merely a superset of it.
- $|R_j|\le S$ for every $j\in\{0,\dots,t\}$. There is no bound on $|B_j|$.
- For each $i\in\{0,\dots,t-1\}$, $\mathrm{Step}_{E,I}((R_i,B_i),c_i,(R_{i+1},B_{i+1}))$ holds. That is, the next state is obtained, for some vertex $v$, by one of these moves:
  - a load: $v\in B_i\setminus R_i$; $v$ is added to the red set; $c_i=1$;
  - a store: $v\in R_i\setminus B_i$; $v$ is added to the blue set; $c_i=1$;
  - a compute: $v\notin I$, $v\notin R_i$ and every $E$-predecessor of $v$ is in $R_i$; $v$ is added to the red set; $c_i=0$;
  - a red deletion: $v\in R_i$ is removed from the red set; $c_i=0$;
  - a blue deletion: $v\in B_i$ is removed from the blue set; $c_i=0$.
- $c_0+\dots+c_{t-1}=q$ exactly.

So $q$ is exactly the number of moves counted as loads or stores in some such sequence. A move that is both a load and a compute may be counted either way.

*Edge cases.*
- $t=0$ is allowed. The conditions then force $I=O$ and $q=0$ (the empty sum is $0$). This works for every $E$ and every $S$, including $S=0$.
- More generally, whenever $O\subseteq I$ the predicate holds with $q=0$ for every $S$: delete the blue pebbles on $I\setminus O$ one at a time.
- When $S=0$, no load, compute or store is ever possible. So the predicate holds if and only if $O\subseteq I$ and $q=0$.
- $I$ and $O$ may be empty.
- The number of moves is unbounded, and a vertex may be loaded or computed any number of times.
- $q$ is an exact cost, not an upper bound.

#### `MiscMath.Computability.RedBluePebbleGame.fftEdge`

**Binders.**
- $k\in\mathbb N$.
- Vertices $u=(\ell,x)$ and $v=(\ell',x')$ with $\ell,\ell'\in\{0,\dots,k\}$ and $x,x'\in\{0,\dots,2^k-1\}$. These are elements of $\mathrm{Fin}(k+1)\times\mathrm{Fin}(2^k)$, compared through their values as natural numbers.

**Definition.** $\mathrm{fftEdge}_k(u,v)$ holds if and only if $\ell'=\ell+1$ and either $x'=x$ or $x'=x\oplus 2^{\ell}$.
- $\oplus$ is bitwise exclusive or on $\mathbb N$, so $x\oplus 2^{\ell}$ is $x$ with binary digit $\ell$ flipped.
- The exponent is $\ell$, the level of the first argument $u$.
- The level condition is evaluated in $\mathbb N$, so there is no wrap-around from level $k$ to level $0$.

Consequences:
- Edges run only from level $\ell$ to level $\ell+1$.
- For $\ell<k$, the vertex $(\ell,x)$ has exactly two out-neighbours, $(\ell+1,x)$ and $(\ell+1,x\oplus 2^{\ell})$. They are distinct and both in range.
- For $\ell\ge1$, the vertex $(\ell,x)$ has exactly two in-neighbours, $(\ell-1,x)$ and $(\ell-1,x\oplus 2^{\ell-1})$.
- Level-0 vertices have no in-neighbours, and level-$k$ vertices have no out-neighbours.
- There are no self-loops.
- The vertex set has $(k+1)2^k$ elements.

*Edge cases.* For $k=0$ there is a single vertex $(0,0)$ and no edges. That vertex is both the level-0 vertex and the level-$k$ vertex.

#### `MiscMath.Computability.RedBluePebbleGame.minIOTime`

**Binders.**
- $V$ with decidable equality.
- A binary relation $E$ on $V$.
- Finite sets $I,O\subseteq V$.
- $S\in\mathbb N$.

**Definition.** minIOTime is the infimum, in $\mathbb N$, of the set of $q\in\mathbb N$ for which HasCompleteCalculation$(E,I,O,S,q)$ holds. When such $q$ exist, this is the least $q$ for which there is a sequence of states that:
- starts at $(\emptyset,I)$;
- ends at $(\emptyset,O)$, with the final blue set exactly $O$;
- has at most $S$ red elements in every state;
- has consecutive states related by the five moves (load and store cost 1; compute, red deletion and blue deletion cost 0);
- has costs summing to exactly $q$.

*Edge cases.*
- This uses Mathlib's convention that the infimum of the empty set of natural numbers is $0$.
- So if no complete calculation exists at all, minIOTime is $0$. That is the same value it takes when a zero-cost calculation exists, for example whenever $O\subseteq I$.
- When the set is nonempty, the infimum is attained.

#### `Target.RedBluePebbleGame.fft_io_lower_bound`

**Binders.** Natural numbers $k$, $S$ and $q$, all universally quantified.

**Setting** (unfolding fftEdge, Step and HasCompleteCalculation).
- $G_k$ is the directed graph on $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$. An element $(\ell,x)$ has level $\ell$ and row $x$.
- There is an edge $(\ell,x)\to(\ell',x')$ if and only if $\ell'=\ell+1$ and either $x'=x$ or $x'=x\oplus 2^{\ell}$, where $\oplus$ is bitwise exclusive or on $\mathbb N$.
- So each $(\ell,x)$ with $\ell\ge1$ has exactly two in-neighbours, $(\ell-1,x)$ and $(\ell-1,x\oplus 2^{\ell-1})$. Level-0 vertices have none.
- $I_k$ is the set of the $2^k$ vertices at level 0. $O_k$ is the set of the $2^k$ vertices at level $k$.

An *$S$-calculation of cost $q$* consists of:
- $t\in\mathbb N$;
- pairs $(R_0,B_0),\dots,(R_t,B_t)$ of subsets of $V_k$;
- $c_0,\dots,c_{t-1}\in\mathbb N$.

They must satisfy:
- $(R_0,B_0)=(\emptyset,I_k)$;
- $(R_t,B_t)=(\emptyset,O_k)$, so the final blue set is exactly $O_k$;
- $|R_j|\le S$ for all $0\le j\le t$;
- $c_0+\dots+c_{t-1}=q$ exactly;
- each $(R_{i+1},B_{i+1})$ is obtained from $(R_i,B_i)$, for some vertex $v$, by one of these moves:
  - load: $v\in B_i\setminus R_i$; $v$ is added to the red set; $c_i=1$;
  - store: $v\in R_i\setminus B_i$; $v$ is added to the blue set; $c_i=1$;
  - compute: $v\notin I_k$, $v\notin R_i$, and every in-neighbour of $v$ is in $R_i$; $v$ is added to the red set; $c_i=0$;
  - red deletion: $v\in R_i$ is removed from the red set; $c_i=0$;
  - blue deletion: $v\in B_i$ is removed from the blue set; $c_i=0$.

A move that is both a load and a compute may carry either cost.

**Hypotheses.**
- $k\ge1$.
- $S\ge3$.
- An $S$-calculation of cost $q$ in $G_k$ exists. Its $t$, states and costs are chosen after $k$, $S$ and $q$.

**Conclusion.** $2^k\cdot k\le 5\cdot q\cdot\log_2 S$ in $\mathbb R$.
- $k$, $q$ and $S$ are embedded in $\mathbb R$, and $\log_2 S=\ln S/\ln 2$.
- Equivalently, $q\ge k\,2^k/(5\log_2 S)$.
- $q$ is any cost for which a calculation exists, so the bound applies to every calculation, not only to a cheapest one.

*Edge cases.*
- $S\ge3$ gives $\log_2 S\ge\log_2 3>0$. So the logarithm takes no junk value, and the conclusion is a genuine lower bound on $q$.
- The constant 5 is explicit. The inequality is claimed for every $k\ge1$ and $S\ge3$, not asymptotically.
- $k=0$ and $S\le2$ are excluded by hypothesis.
- For $k\ge1$, $I_k$ and $O_k$ are disjoint.
- For given $k\ge1$ and $S\ge3$, the hypotheses can be satisfied exactly when some $S$-calculation exists. `fft_complete_iff` asserts that one exists for all such $k$ and $S$.
- For a $q$ that is not the cost of any calculation, the theorem says nothing.

#### `Target.RedBluePebbleGame.fft_io_bounds`

**Binders.** Natural numbers $k$, $S$ and $q$, all universally quantified.

**Setting** (unfolding fftEdge, Step and HasCompleteCalculation).
- $G_k$ is the directed graph on $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$. An element $(\ell,x)$ has level $\ell$ and row $x$.
- There is an edge $(\ell,x)\to(\ell',x')$ if and only if $\ell'=\ell+1$ and either $x'=x$ or $x'=x\oplus 2^{\ell}$, where $\oplus$ is bitwise exclusive or on $\mathbb N$.
- So each $(\ell,x)$ with $\ell\ge1$ has exactly two in-neighbours, $(\ell-1,x)$ and $(\ell-1,x\oplus 2^{\ell-1})$. Level-0 vertices have none.
- $I_k$ is the set of the $2^k$ level-0 vertices. $O_k$ is the set of the $2^k$ level-$k$ vertices.

An *$S$-calculation of cost $q$* consists of:
- $t\in\mathbb N$;
- pairs $(R_0,B_0),\dots,(R_t,B_t)$ of subsets of $V_k$;
- $c_0,\dots,c_{t-1}\in\mathbb N$.

They must satisfy:
- $(R_0,B_0)=(\emptyset,I_k)$;
- $(R_t,B_t)=(\emptyset,O_k)$, so the final blue set is exactly $O_k$;
- $|R_j|\le S$ for all $0\le j\le t$;
- $c_0+\dots+c_{t-1}=q$ exactly;
- each step, for some vertex $v$, is one of these moves:
  - load: $v\in B_i\setminus R_i$; $v$ is added to the red set; $c_i=1$;
  - store: $v\in R_i\setminus B_i$; $v$ is added to the blue set; $c_i=1$;
  - compute: $v\notin I_k$, $v\notin R_i$, and every in-neighbour of $v$ is in $R_i$; $v$ is added to the red set; $c_i=0$;
  - red deletion: $v\in R_i$ is removed from the red set; $c_i=0$;
  - blue deletion: $v\in B_i$ is removed from the blue set; $c_i=0$.

A move that is both a load and a compute may carry either cost.

**Hypotheses.**
- $k\ge1$.
- $S\ge1$.
- An $S$-calculation of cost $q$ in $G_k$ exists. Its $t$, states and costs are chosen after $k$, $S$ and $q$.

**Conclusion.** Both of the following hold:
- (a) $2^{k+1}\le q$, in $\mathbb N$.
- (b) $\dfrac{2^k(k+1)}{2\log_2(4S)}-S\le q$, in $\mathbb R$, with $k$, $S$ and $q$ embedded in $\mathbb R$. Since $\log_2(4S)=2+\log_2 S$, the denominator equals $4+2\log_2 S$.

*Edge cases.*
- The hypothesis allows $S=1$ and $S=2$. But `fft_complete_iff` asserts that no calculation exists for $S<3$, so for those $S$ this theorem is vacuously true. It has content only for $S\ge3$.
- In (b) the subtraction is real subtraction, not truncated.
- The left-hand side of (b) is $\le0$ whenever $S\ge 2^{k-2}(k+1)$, because $2\log_2(4S)\ge4$. There, (b) says only that $q$ is at least a non-positive number.
- That threshold covers every $S\ge1$ when $k=1$, and every $S\ge3$ when $k=2$. So for $k\le2$, (b) adds nothing wherever the hypothesis can hold.
- For $S\ge1$ the denominator is at least 4, so there is no division by zero.
- (a) involves no subtraction or division.

#### `Target.RedBluePebbleGame.fft_complete_iff`

**Binders.** Natural numbers $k$ and $S$, universally quantified.

**Setting** (unfolding fftEdge, Step and HasCompleteCalculation).
- $G_k$ is the directed graph on $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$, with elements written $(\ell,x)$.
- There is an edge $(\ell,x)\to(\ell',x')$ if and only if $\ell'=\ell+1$ and either $x'=x$ or $x'=x\oplus 2^{\ell}$, where $\oplus$ is bitwise exclusive or on $\mathbb N$.
- So each $(\ell,x)$ with $\ell\ge1$ has exactly two in-neighbours, $(\ell-1,x)$ and $(\ell-1,x\oplus 2^{\ell-1})$. Level-0 vertices have none.
- $I_k$ is the set of the $2^k$ level-0 vertices. $O_k$ is the set of the $2^k$ level-$k$ vertices.

An *$S$-calculation of cost $q$* consists of:
- $t\in\mathbb N$;
- pairs $(R_0,B_0),\dots,(R_t,B_t)$ of subsets of $V_k$;
- $c_0,\dots,c_{t-1}\in\mathbb N$.

They must satisfy:
- $(R_0,B_0)=(\emptyset,I_k)$;
- $(R_t,B_t)=(\emptyset,O_k)$, so the final blue set is exactly $O_k$;
- $|R_j|\le S$ for all $j$;
- $\sum c_i=q$ exactly;
- each step, for some vertex $v$, is one of these moves:
  - load: $v\in B_i\setminus R_i$; $v$ is added to the red set; cost 1;
  - store: $v\in R_i\setminus B_i$; $v$ is added to the blue set; cost 1;
  - compute: $v\notin I_k$, $v\notin R_i$, and every in-neighbour of $v$ is in $R_i$; $v$ is added to the red set; cost 0;
  - red deletion: $v\in R_i$ is removed; cost 0;
  - blue deletion: $v\in B_i$ is removed; cost 0.

A move that is both a load and a compute may carry either cost.

**Hypothesis.** $k\ge1$.

**Conclusion.** An $S$-calculation in $G_k$ exists, for some cost $q\in\mathbb N$, if and only if $S\ge3$. In detail:
- every $S$-calculation, of any cost, forces $S\ge3$;
- for every $S\ge3$, including $S=3$, there is an $S$-calculation of some unspecified cost.

*Edge cases.*
- $S$ ranges over all of $\mathbb N$. $S=0$, $1$ and $2$ all fall on the side where no calculation exists.
- The "if" direction asserts existence only. It gives no bound on the cost $q$ or on the number of moves.
- $k=0$ is excluded by the hypothesis. For $k=0$, $I_0=O_0$ is the single vertex $(0,0)$, so a calculation with no moves and cost 0 exists for every $S$, including $S=0$. The left-hand side of the equivalence then holds for every $S$.

#### `Target.RedBluePebbleGame.fft_io_lower_bound_isBigO`

**Binders.** None at top level. The statement compares two real-valued functions of $p=(k,S)\in\mathbb N\times\mathbb N$.

**Setting** (unfolding fftEdge, Step, HasCompleteCalculation and minIOTime).
- $G_k$ is the directed graph on $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$, with elements written $(\ell,x)$.
- There is an edge $(\ell,x)\to(\ell',x')$ if and only if $\ell'=\ell+1$ and either $x'=x$ or $x'=x\oplus 2^{\ell}$, where $\oplus$ is bitwise exclusive or on $\mathbb N$.
- So each $(\ell,x)$ with $\ell\ge1$ has exactly two in-neighbours, $(\ell-1,x)$ and $(\ell-1,x\oplus 2^{\ell-1})$. Level-0 vertices have none.
- $I_k$ is the set of the $2^k$ level-0 vertices. $O_k$ is the set of the $2^k$ level-$k$ vertices.

An *$S$-calculation of cost $q$* consists of:
- $t\in\mathbb N$;
- pairs $(R_0,B_0),\dots,(R_t,B_t)$ of subsets of $V_k$;
- $c_0,\dots,c_{t-1}\in\mathbb N$.

They must satisfy:
- $(R_0,B_0)=(\emptyset,I_k)$;
- $(R_t,B_t)=(\emptyset,O_k)$, so the final blue set is exactly $O_k$;
- $|R_j|\le S$ for all $j$;
- $\sum c_i=q$ exactly;
- each step, for some vertex $v$, is one of these moves:
  - load: $v\in B_i\setminus R_i$; $v$ is added to the red set; cost 1;
  - store: $v\in R_i\setminus B_i$; $v$ is added to the blue set; cost 1;
  - compute: $v\notin I_k$, $v\notin R_i$, and every in-neighbour of $v$ is in $R_i$; $v$ is added to the red set; cost 0;
  - red deletion: $v\in R_i$ is removed; cost 0;
  - blue deletion: $v\in B_i$ is removed; cost 0.

A move that is both a load and a compute may carry either cost.

$M(k,S)$ is minIOTime for $G_k$, $I_k$, $O_k$ and red bound $S$. It is the least $q$ for which an $S$-calculation of cost $q$ in $G_k$ exists. If none exists, it is $0$, by Mathlib's convention for the infimum of the empty subset of $\mathbb N$.

**Conclusion.** Let $f(k,S)=2^k\ln(2^k)$ and $g(k,S)=M(k,S)\cdot\ln S$.
- $\ln$ is the natural logarithm.
- $M(k,S)$ and $S$ are embedded in $\mathbb R$.

The theorem states $f=O(g)$ along the principal filter of $D=\{(k,S)\in\mathbb N\times\mathbb N : k\ge1,\ S\ge3\}$. By Mathlib's definition of big-O, this means: there is a real constant $C$, chosen once and before $k$ and $S$, such that for every $k\ge1$ and every $S\ge3$,
$$\bigl|2^k\ln(2^k)\bigr|\le C\,\bigl|M(k,S)\ln S\bigr|.$$
On $D$ both sides are non-negative, and $\ln(2^k)=k\ln 2$. So the statement is: $k\,2^k\ln 2\le C\,M(k,S)\ln S$ for all $k\ge1$ and $S\ge3$. This is a lower bound on $M$ with an unspecified constant.

*Edge cases.*
- The filter is principal. So the inequality must hold at every point of $D$ with a single $C$, not merely eventually or in a limit as $k\to\infty$ or $S\to\infty$.
- Points with $k=0$ or $S\le2$ are unconstrained.
- The logarithms here are natural. `fft_io_lower_bound` and `fft_io_bounds` use base 2.
- The left side is strictly positive on $D$. So the statement forces $C>0$ and $M(k,S)\ge1$ at every point of $D$.
- In particular, minIOTime's default value 0 cannot occur on $D$. The statement therefore entails that at every point of $D$ some calculation exists and none has cost 0.
- $f$ does not depend on $S$.

### The Lean sent

Module 1:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice.Nat

namespace MiscMath.Computability.RedBluePebbleGame

variable {V : Type*} [DecidableEq V]

inductive Step (E : V → V → Prop) (I : Finset V) :
    Finset V × Finset V → ℕ → Finset V × Finset V → Prop
  | load {R B : Finset V} {v : V} (hB : v ∈ B) (hR : v ∉ R) :
      Step E I (R, B) 1 (insert v R, B)
  | store {R B : Finset V} {v : V} (hR : v ∈ R) (hB : v ∉ B) :
      Step E I (R, B) 1 (R, insert v B)
  | compute {R B : Finset V} {v : V} (hI : v ∉ I) (hR : v ∉ R) (hpred : ∀ u, E u v → u ∈ R) :
      Step E I (R, B) 0 (insert v R, B)
  | deleteRed {R B : Finset V} {v : V} (hR : v ∈ R) :
      Step E I (R, B) 0 (R.erase v, B)
  | deleteBlue {R B : Finset V} {v : V} (hB : v ∈ B) :
      Step E I (R, B) 0 (R, B.erase v)

def HasCompleteCalculation (E : V → V → Prop) (I O : Finset V) (S q : ℕ) : Prop :=
  ∃ (t : ℕ) (σ : Fin (t + 1) → Finset V × Finset V) (c : Fin t → ℕ),
    σ 0 = (∅, I) ∧
    σ (Fin.last t) = (∅, O) ∧
    (∀ j, (σ j).1.card ≤ S) ∧
    (∀ i : Fin t, Step E I (σ i.castSucc) (c i) (σ i.succ)) ∧
    ∑ i, c i = q

def fftEdge (k : ℕ) (u v : Fin (k + 1) × Fin (2 ^ k)) : Prop :=
  (v.1 : ℕ) = (u.1 : ℕ) + 1 ∧
    ((v.2 : ℕ) = (u.2 : ℕ) ∨ (v.2 : ℕ) = (u.2 : ℕ) ^^^ 2 ^ (u.1 : ℕ))

noncomputable def minIOTime (E : V → V → Prop) (I O : Finset V) (S : ℕ) : ℕ :=
  sInf {q | HasCompleteCalculation E I O S q}

end MiscMath.Computability.RedBluePebbleGame
```

Module 2:

```lean
import MiscMath.Computability.RedBluePebbleGame.Spec
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Prod

open Filter MiscMath.Computability.RedBluePebbleGame

namespace Target.RedBluePebbleGame

theorem fft_io_lower_bound {k S q : ℕ} (hk : 1 ≤ k) (hS : 3 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    (2 : ℝ) ^ k * k ≤ 5 * q * Real.logb 2 S

theorem fft_io_bounds {k S q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    2 ^ (k + 1) ≤ q ∧ (2 : ℝ) ^ k * (k + 1) / (2 * Real.logb 2 (4 * S)) - S ≤ q

theorem fft_complete_iff {k S : ℕ} (hk : 1 ≤ k) :
    (∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) ↔ 3 ≤ S

theorem fft_io_lower_bound_isBigO :
    (fun p : ℕ × ℕ => (2 : ℝ) ^ p.1 * Real.log ((2 : ℝ) ^ p.1)) =O[𝓟 {p | 1 ≤ p.1 ∧ 3 ≤ p.2}]
      fun p => (minIOTime (fftEdge p.1) (Finset.univ.filter (·.1 = 0))
        (Finset.univ.filter (·.1 = Fin.last p.1)) p.2 : ℝ) * Real.log p.2

end Target.RedBluePebbleGame
```

## Phase 1, round 1, 2026-09-25 (superseded for `fft_io_bounds`)

Round 1 rendered the six items as they stood on 2026-09-25. Since then `fft_io_bounds` has
changed, so its rendering below describes a statement that no longer exists. The other five
items are unchanged, and round 2 renders them again.

### What was sent

- **Taken from:** an uncommitted draft on branch `hong-kung`, based on `088256c`, on
  2026-09-25. The draft was not committed because nothing containing an advertised statement is
  committed before its read. So the text is identified by content: the SHA-256 of each stripped
  module exactly as sent is
  - `3ccac61d6211b6c4fc339cf9f2eb4f8a127f7e490350098b28ed7061bcc94f8d` for Module 1;
  - `4f9c69f0fa8e582fbc3c8f6d533486ebef4ba09c92a5ea4f82ece9f34bb73b60` for Module 2.
- **Declarations:** `Target.RedBluePebbleGame.fft_io_lower_bound`,
  `Target.RedBluePebbleGame.fft_io_bounds` and `Target.RedBluePebbleGame.fft_complete_iff`, the
  frozen targets the library's theorems are held to.
- **Definitions they are stated through:** `MiscMath.Computability.RedBluePebbleGame.Step`,
  `.HasCompleteCalculation` and `.fftEdge`. These are the only project constants the three
  statement types reach, transitively; the constructors of `Step` and one auxiliary proof term
  of `HasCompleteCalculation` come with them. This was checked by walking the elaborated
  statements, not by searching the text.
- **The prompt** held only these items:
  - the brief, Part 2 of `READBACK.md`, verbatim;
  - the two modules below, with every comment and docstring stripped and the theorems' proofs
    removed, under the neutral labels "Module 1" and "Module 2".

  It opened with one operational line, which says nothing about the intended meaning. The
  subagent runs inside this repository, where the plan and the source are on disk, and the
  line was there to keep it from reading them:

  > Work from the text of this message alone. Do not use any tools: do not read, list or
  > search any files, run any commands, or browse. Reply with the rendering only; then, on one
  > separate final line, give the exact model ID you are running as, as stated in your system
  > prompt.

  The subagent made no tool calls.

### Who wrote it

`claude-opus-5-5` (Claude Opus 5.5), as a fresh subagent with no prior context, on 2026-09-25.
It reported its model ID on the final line of its reply, and that line is left out below.

### What the comparison found

The rendering was compared, clause by clause, with the intended statements: the plan's three
definitions and three advertised statements. It agrees on all of them:

- the five moves, with their preconditions and charges;
- the exact start and end configurations;
- the red-pebble budget on every configuration, the first and last included;
- the butterfly's levels and lanes compared as natural numbers, with no wrap-around;
- the inputs at level 0 and the outputs at level `k`;
- the three conclusions, with their quantifier order and the ordinary embedding of ℕ in ℝ.

The rendering surfaced one point that the intended account had left implicit. The charges are
part of the witness. A step that is legal both as a load and as a computation may be charged 1
or 0, so one sequence of configurations can witness several values of `q`. The lower bounds
therefore cover the cheapest charging. This is the intended semantics, as in the source: there
the player chooses which rule to apply, and the I/O count is the number of load and store
applications. The point is now stated in the docstrings of `Step` and `HasCompleteCalculation`.
No Lean changed, and the stripped text is byte-identical to what was sent.

It also noted, correctly, that the hypothesis `1 ≤ S` of `fft_io_bounds` excludes nothing,
given `fft_complete_iff`. Neither does `3 ≤ S` in `fft_io_lower_bound`: both are implied by the
calculation hypothesis. They are kept on purpose, so that each logarithm is visibly away from
its junk values.

No error was found in the rendering. Its edge-case claims were checked by hand:

- the zero-move case forces `I = O` and `q = 0`;
- with `S = 0`, a calculation exists iff `O ⊆ I` and `q = 0`;
- each vertex above level 0 has exactly two in-neighbours;
- the `k = 0` graph has one vertex and a free calculation for every `S`.

### The rendering, verbatim

#### MiscMath.Computability.RedBluePebbleGame.Step (inductive definition)

**Parameters, in order.**
- $V$ is an arbitrary type whose elements are the vertices. It is inferred from context, not supplied. It comes with a decision procedure for equality of vertices. That procedure is used only to form the finite sets $R\cup\{v\}$ and $R\setminus\{v\}$, and these sets are the same whichever procedure is supplied.
- $E$ is an arbitrary binary relation on $V$. Read $E(u,v)$ as "$u$ is an in-neighbour of $v$". Nothing is assumed about $E$: it need not be acyclic, in-neighbourhoods need not be finite, and it need not be decidable.
- $I$ is a finite subset of $V$.

**Meaning.** A *configuration* is an ordered pair $(R,B)$ of finite subsets of $V$. The constructor names call the first set red and the second blue. Let $s$ and $s'$ be configurations and $c$ a natural number, and write $s=(R,B)$. The relation $\mathrm{Step}_{E,I}(s,c,s')$ holds exactly when some vertex $v\in V$ satisfies one of the following five clauses. It holds in no other case.
1. *load*: $v\in B$, $v\notin R$, $c=1$ and $s'=(R\cup\{v\},\,B)$.
2. *store*: $v\in R$, $v\notin B$, $c=1$ and $s'=(R,\,B\cup\{v\})$.
3. *compute*: $v\notin I$, $v\notin R$, every $u\in V$ with $E(u,v)$ belongs to $R$, $c=0$ and $s'=(R\cup\{v\},\,B)$.
4. *deleteRed*: $v\in R$, $c=0$ and $s'=(R\setminus\{v\},\,B)$.
5. *deleteBlue*: $v\in B$, $c=0$ and $s'=(R,\,B\setminus\{v\})$.

*Edge cases.*
- The cost $c$ is only ever $0$ or $1$.
- Every clause changes the configuration, so there is no idle step.
- $R$ and $B$ may share vertices, and nothing here bounds their sizes.
- $I$ is a fixed parameter, not the current second set. A vertex of $I$ can never be computed. It can therefore enter $R$ only by load, which needs it to be in $B$ at that moment.
- Compute puts no condition on whether $v\in B$.
- A vertex outside $I$ with no in-neighbours can be computed whenever it is not in $R$, because the in-neighbour condition is then empty.
- A vertex with infinitely many in-neighbours can never be computed, because $R$ is finite.
- Load and compute produce the same transition $(R,B)\to(R\cup\{v\},B)$. Suppose $v\in B$, $v\notin R$, $v\notin I$ and all in-neighbours of $v$ lie in $R$. Then both clauses apply, and the relation holds for that one transition with $c=1$ and also with $c=0$.

#### MiscMath.Computability.RedBluePebbleGame.HasCompleteCalculation (definition)

**Parameters, in order.**
- $V$ with a decision procedure for equality, inferred as above.
- A binary relation $E$ on $V$; $E(u,v)$ means $u$ is an in-neighbour of $v$.
- Finite subsets $I$ and $O$ of $V$.
- Natural numbers $S$ and $q$.

**Meaning.** The proposition holds iff there exist, chosen in this order:
- a natural number $t$;
- pairs $(R_0,B_0),\dots,(R_t,B_t)$ of finite subsets of $V$;
- natural numbers $c_0,\dots,c_{t-1}$;

such that all of the following hold:
1. $(R_0,B_0)=(\varnothing,\,I)$.
2. $(R_t,B_t)=(\varnothing,\,O)$. At the end the first set is empty and the second set is exactly $O$.
3. $|R_j|\le S$ for every $j\in\{0,1,\dots,t\}$, including the first and last pairs.
4. For every $i\in\{0,\dots,t-1\}$, write $(R,B)=(R_i,B_i)$. Some vertex $v$ satisfies one of these:
   - *load*: $v\in B$, $v\notin R$, $c_i=1$, $(R_{i+1},B_{i+1})=(R\cup\{v\},B)$;
   - *store*: $v\in R$, $v\notin B$, $c_i=1$, $(R_{i+1},B_{i+1})=(R,B\cup\{v\})$;
   - *compute*: $v\notin I$, $v\notin R$, every in-neighbour of $v$ is in $R$, $c_i=0$, $(R_{i+1},B_{i+1})=(R\cup\{v\},B)$;
   - *deleteRed*: $v\in R$, $c_i=0$, $(R_{i+1},B_{i+1})=(R\setminus\{v\},B)$;
   - *deleteBlue*: $v\in B$, $c_i=0$, $(R_{i+1},B_{i+1})=(R,B\setminus\{v\})$.
5. $c_0+c_1+\dots+c_{t-1}=q$.

The single set $I$ plays two roles: it is the initial second set, and it is the set of vertices that may never be computed.

*Edge cases.*
- $t=0$ is allowed. The conditions then reduce to $I=O$ and $q=0$, since an empty sum is $0$. This holds for every $E$ and every $S$, including $S=0$.
- For $S=0$ in general, the first set must stay empty throughout. Only deleteBlue moves are then possible, and the proposition holds iff $O\subseteq I$ and $q=0$.
- $S$ is only an upper bound, so the proposition for $S$ implies it for every larger $S$.
- Nothing bounds $t$ or $|B_j|$, and nothing relates $O$ to $I$ or to $E$.
- $q$ must equal the recorded total exactly. The recorded costs, however, are not determined by the configurations: a step that is legal both as load and as compute may be recorded with cost $1$ or with cost $0$. So $q$ is the sum of three counts:
  - the store steps;
  - the steps that add a vertex to the first set and are legal as load but not as compute;
  - however many of the steps legal as both are recorded at cost $1$.

  One sequence of configurations can therefore witness several values of $q$.

#### MiscMath.Computability.RedBluePebbleGame.fftEdge (definition)

**Parameters, in order.** $k\in\mathbb N$, then two vertices $u=(\ell,x)$ and $v=(\ell',x')$. Each vertex is a pair whose first coordinate (the level) lies in $\{0,\dots,k\}$ and whose second coordinate (the index) lies in $\{0,\dots,2^k-1\}$.

**Meaning.** $\mathrm{fftEdge}_k(u,v)$ holds iff
$$\ell'=\ell+1\quad\text{and}\quad\bigl(x'=x\ \text{ or }\ x'=x\oplus 2^{\ell}\bigr).$$
- Coordinates are read as natural numbers and all arithmetic is in $\mathbb N$, so nothing wraps around modulo $k+1$ or $2^k$.
- $\oplus$ is bitwise exclusive-or. So $x\oplus2^\ell$ is $x$ with its binary digit of weight $2^\ell$ flipped: it equals $x+2^\ell$ if that digit is $0$, and $x-2^\ell$ if it is $1$.
- The exponent is the level $\ell$ of the source vertex $u$.

What this gives:
- Edges run only from level $\ell$ to level $\ell+1$, for $0\le\ell\le k-1$.
- A vertex $(\ell,x)$ with $\ell<k$ has exactly two out-neighbours, $(\ell+1,x)$ and $(\ell+1,x\oplus2^\ell)$. They are distinct, and both are in range because $x<2^k$ and $\ell<k$.
- A vertex $(\ell',x')$ with $\ell'\ge1$ has exactly two in-neighbours, $(\ell'-1,x')$ and $(\ell'-1,x'\oplus2^{\ell'-1})$.
- Level-$0$ vertices have no in-neighbours, and level-$k$ vertices have no out-neighbours.

*Edge cases.* $k=0$ gives a single vertex $(0,0)$ and no edges.

#### Target.RedBluePebbleGame.fft_io_lower_bound

**Binders, in order.** For all natural numbers $k$, $S$, $q$ (universally quantified; they are inferred rather than supplied when the theorem is applied), followed by three hypotheses. Everything else is fixed by $k$:
- **Vertices.** $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$, written $(\ell,x)$ with level $\ell$ and index $x$, using the standard equality test.
- **Edges.** $(\ell,x)\to(\ell',x')$ iff $\ell'=\ell+1$ and ($x'=x$ or $x'=x\oplus2^\ell$). Arithmetic is in $\mathbb N$ with no wrap-around, and $\oplus$ is bitwise exclusive-or, so $x\oplus2^\ell$ is $x$ with its binary digit of weight $2^\ell$ flipped. Level-$0$ vertices have no in-neighbours. Each $(\ell',x')$ with $\ell'\ge1$ has exactly two in-neighbours, $(\ell'-1,x')$ and $(\ell'-1,x'\oplus2^{\ell'-1})$.
- **$I_k$** is the set of all $2^k$ vertices of level $0$. **$O_k$** is the set of all $2^k$ vertices of level $k$.
- **$\mathcal C_k(S,q)$** is the statement that there exist $t\in\mathbb N$, then pairs $(R_0,B_0),\dots,(R_t,B_t)$ of subsets of $V_k$, and numbers $c_0,\dots,c_{t-1}\in\mathbb N$, such that:
  - (a) $(R_0,B_0)=(\varnothing,I_k)$;
  - (b) $(R_t,B_t)=(\varnothing,O_k)$, with the final second set exactly $O_k$;
  - (c) $|R_j|\le S$ for all $j=0,\dots,t$;
  - (d) for each $i<t$, writing $(R,B)=(R_i,B_i)$, some vertex $v$ satisfies one of:
    - *load*: $v\in B$, $v\notin R$, $c_i=1$, next pair $(R\cup\{v\},B)$;
    - *store*: $v\in R$, $v\notin B$, $c_i=1$, next pair $(R,B\cup\{v\})$;
    - *compute*: $v\notin I_k$ (that is, $v$ has level $\ge1$), $v\notin R$, both in-neighbours of $v$ are in $R$, $c_i=0$, next pair $(R\cup\{v\},B)$;
    - *deleteRed*: $v\in R$, $c_i=0$, next pair $(R\setminus\{v\},B)$;
    - *deleteBlue*: $v\in B$, $c_i=0$, next pair $(R,B\setminus\{v\})$;
  - (e) $c_0+\dots+c_{t-1}=q$.

  Nothing bounds $t$ or $|B_j|$. A step legal both as load and as compute ($v\in B$, $v\notin R$, level $\ge1$, both in-neighbours in $R$) may be recorded with $c_i=1$ or with $c_i=0$.

**Hypotheses.**
1. $k\ge1$.
2. $S\ge3$.
3. $\mathcal C_k(S,q)$. Because this is a hypothesis, the theorem applies to every $t$, every sequence of pairs and every cost list satisfying (a)–(e).

**Conclusion.** In the real numbers, with $k$, $q$ and $S$ embedded as reals,
$$2^k\cdot k\;\le\;5\,q\,\log_2 S,\qquad \log_2 S=\ln S/\ln 2 .$$

*Edge cases.*
- Nothing is asserted for $k=0$ or for $S\le2$.
- For $k\ge1$, $I_k$ and $O_k$ are disjoint and each has $2^k$ elements, so a calculation with zero moves is impossible.
- For $S\ge3$, $\log_2S\ge\log_2 3>1.58$. So the logarithm takes no junk value, there is no division by zero and no subtraction, and the casts are the ordinary embedding of $\mathbb N$ into $\mathbb R$.
- The bound is asserted for every $q$ that admits a calculation, not only the least such $q$. Since steps legal as both load and compute may be recorded at cost $0$, the bound applies in particular to the count in which all such steps are free.
- The left side is at least $2$, so the conclusion rules out $q=0$.
- For a $q$ that admits no calculation, the statement says nothing.
- fft_complete_iff asserts that for every $k\ge1$ and $S\ge3$ some $q$ admits a calculation. If so, the hypotheses can all be satisfied at every admitted $(k,S)$.

#### Target.RedBluePebbleGame.fft_io_bounds

**Binders, in order.** For all natural numbers $k$, $S$, $q$ (universally quantified; they are inferred rather than supplied when the theorem is applied), followed by three hypotheses. Everything else is fixed by $k$:
- **Vertices.** $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$, written $(\ell,x)$ with level $\ell$ and index $x$, using the standard equality test.
- **Edges.** $(\ell,x)\to(\ell',x')$ iff $\ell'=\ell+1$ and ($x'=x$ or $x'=x\oplus2^\ell$). Arithmetic is in $\mathbb N$ with no wrap-around, and $\oplus$ is bitwise exclusive-or, so $x\oplus2^\ell$ is $x$ with its binary digit of weight $2^\ell$ flipped. Level-$0$ vertices have no in-neighbours. Each $(\ell',x')$ with $\ell'\ge1$ has exactly two in-neighbours, $(\ell'-1,x')$ and $(\ell'-1,x'\oplus2^{\ell'-1})$.
- **$I_k$** is the set of all $2^k$ vertices of level $0$. **$O_k$** is the set of all $2^k$ vertices of level $k$.
- **$\mathcal C_k(S,q)$** is the statement that there exist $t\in\mathbb N$, then pairs $(R_0,B_0),\dots,(R_t,B_t)$ of subsets of $V_k$, and numbers $c_0,\dots,c_{t-1}\in\mathbb N$, such that:
  - (a) $(R_0,B_0)=(\varnothing,I_k)$;
  - (b) $(R_t,B_t)=(\varnothing,O_k)$, with the final second set exactly $O_k$;
  - (c) $|R_j|\le S$ for all $j=0,\dots,t$;
  - (d) for each $i<t$, writing $(R,B)=(R_i,B_i)$, some vertex $v$ satisfies one of:
    - *load*: $v\in B$, $v\notin R$, $c_i=1$, next pair $(R\cup\{v\},B)$;
    - *store*: $v\in R$, $v\notin B$, $c_i=1$, next pair $(R,B\cup\{v\})$;
    - *compute*: $v\notin I_k$ (that is, $v$ has level $\ge1$), $v\notin R$, both in-neighbours of $v$ are in $R$, $c_i=0$, next pair $(R\cup\{v\},B)$;
    - *deleteRed*: $v\in R$, $c_i=0$, next pair $(R\setminus\{v\},B)$;
    - *deleteBlue*: $v\in B$, $c_i=0$, next pair $(R,B\setminus\{v\})$;
  - (e) $c_0+\dots+c_{t-1}=q$.

  Nothing bounds $t$ or $|B_j|$. A step legal both as load and as compute ($v\in B$, $v\notin R$, level $\ge1$, both in-neighbours in $R$) may be recorded with $c_i=1$ or with $c_i=0$.

**Hypotheses.**
1. $k\ge1$.
2. $S\ge1$.
3. $\mathcal C_k(S,q)$. Because this is a hypothesis, the theorem applies to every calculation satisfying (a)–(e).

**Conclusion.** Both of the following hold, for the same $q$:
- (i) $2^{k+1}\le q$, as natural numbers;
- (ii) in the real numbers, with $k$, $q$ and $S$ embedded,
$$2^k\,(k+1)\;\le\;2\,(q+S)\,\log_2(4S),\qquad \log_2(4S)=\ln(4S)/\ln 2 .$$

*Edge cases.*
- Nothing is asserted for $k=0$ or for $S=0$.
- The hypothesis admits $S=1$ and $S=2$. However, fft_complete_iff asserts that for $S\le2$ no calculation exists at any cost. For those two values hypothesis 3 then cannot be met, and the theorem says nothing.
- The theorem therefore has content only for $S\ge3$, where fft_complete_iff asserts that hypothesis 3 holds for some $q$.
- $4S\ge4$, so $\log_2(4S)\ge2$; it also equals $2+\log_2 S$. There are no junk values, no division by zero and no subtraction, and the casts are the ordinary embedding.
- Conjunct (i) does not involve $S$.
- Both conjuncts are asserted for every achievable $q$, including the least one, in which steps legal as both load and compute are recorded at cost $0$.
- $I_k$ and $O_k$ are disjoint and non-empty, so a calculation with zero moves is impossible.

#### Target.RedBluePebbleGame.fft_complete_iff

**Binders, in order.** For all natural numbers $k$ and $S$ (universally quantified; they are inferred rather than supplied when the theorem is applied), followed by one hypothesis. Everything else is fixed by $k$:
- **Vertices.** $V_k=\{0,\dots,k\}\times\{0,\dots,2^k-1\}$, written $(\ell,x)$ with level $\ell$ and index $x$, using the standard equality test.
- **Edges.** $(\ell,x)\to(\ell',x')$ iff $\ell'=\ell+1$ and ($x'=x$ or $x'=x\oplus2^\ell$). Arithmetic is in $\mathbb N$ with no wrap-around, and $\oplus$ is bitwise exclusive-or, so $x\oplus2^\ell$ is $x$ with its binary digit of weight $2^\ell$ flipped. Level-$0$ vertices have no in-neighbours. Each $(\ell',x')$ with $\ell'\ge1$ has exactly two in-neighbours, $(\ell'-1,x')$ and $(\ell'-1,x'\oplus2^{\ell'-1})$.
- **$I_k$** is the set of all $2^k$ vertices of level $0$. **$O_k$** is the set of all $2^k$ vertices of level $k$.
- **$\mathcal C_k(S,q)$** is the statement that there exist $t\in\mathbb N$, then pairs $(R_0,B_0),\dots,(R_t,B_t)$ of subsets of $V_k$, and numbers $c_0,\dots,c_{t-1}\in\mathbb N$, such that:
  - (a) $(R_0,B_0)=(\varnothing,I_k)$;
  - (b) $(R_t,B_t)=(\varnothing,O_k)$, with the final second set exactly $O_k$;
  - (c) $|R_j|\le S$ for all $j=0,\dots,t$;
  - (d) for each $i<t$, writing $(R,B)=(R_i,B_i)$, some vertex $v$ satisfies one of:
    - *load*: $v\in B$, $v\notin R$, $c_i=1$, next pair $(R\cup\{v\},B)$;
    - *store*: $v\in R$, $v\notin B$, $c_i=1$, next pair $(R,B\cup\{v\})$;
    - *compute*: $v\notin I_k$ (that is, $v$ has level $\ge1$), $v\notin R$, both in-neighbours of $v$ are in $R$, $c_i=0$, next pair $(R\cup\{v\},B)$;
    - *deleteRed*: $v\in R$, $c_i=0$, next pair $(R\setminus\{v\},B)$;
    - *deleteBlue*: $v\in B$, $c_i=0$, next pair $(R,B\setminus\{v\})$;
  - (e) $c_0+\dots+c_{t-1}=q$.

  Nothing bounds $t$ or $|B_j|$. A step legal both as load and as compute may be recorded with $c_i=1$ or with $c_i=0$.

**Hypothesis.** $k\ge1$.

**Conclusion.**
$$\bigl(\exists\,q\in\mathbb N:\ \mathcal C_k(S,q)\bigr)\iff S\ge3 .$$
$q$ is chosen after $k$ and $S$ and may depend on them. The calculation data (the number of moves $t$, the pairs and the costs) are chosen after $q$.

*Edge cases.*
- Every $S\in\mathbb N$ is covered, including $S=0$.
- Left to right: a calculation of any cost in which every first set has at most $S$ elements forces $S\ge3$. So for $S\in\{0,1,2\}$ no calculation exists at any cost.
- Right to left: for $S\ge3$ some calculation exists at some cost. Nothing is said about how large $q$ or $t$ is.
- "At most $S$" is an upper bound, so the left side is monotone in $S$. The theorem places the threshold at $3$ for every $k\ge1$.
- $k=0$ is excluded. At $k=0$, $V_0$ is the single vertex $(0,0)$ and $I_0=O_0=\{(0,0)\}$. The zero-move sequence is then a calculation with $q=0$ for every $S$, including $S=0$.

### The Lean sent

Module 1:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace MiscMath.Computability.RedBluePebbleGame

variable {V : Type*} [DecidableEq V]

inductive Step (E : V → V → Prop) (I : Finset V) :
    Finset V × Finset V → ℕ → Finset V × Finset V → Prop
  | load {R B : Finset V} {v : V} (hB : v ∈ B) (hR : v ∉ R) :
      Step E I (R, B) 1 (insert v R, B)
  | store {R B : Finset V} {v : V} (hR : v ∈ R) (hB : v ∉ B) :
      Step E I (R, B) 1 (R, insert v B)
  | compute {R B : Finset V} {v : V} (hI : v ∉ I) (hR : v ∉ R) (hpred : ∀ u, E u v → u ∈ R) :
      Step E I (R, B) 0 (insert v R, B)
  | deleteRed {R B : Finset V} {v : V} (hR : v ∈ R) :
      Step E I (R, B) 0 (R.erase v, B)
  | deleteBlue {R B : Finset V} {v : V} (hB : v ∈ B) :
      Step E I (R, B) 0 (R, B.erase v)

def HasCompleteCalculation (E : V → V → Prop) (I O : Finset V) (S q : ℕ) : Prop :=
  ∃ (t : ℕ) (σ : Fin (t + 1) → Finset V × Finset V) (c : Fin t → ℕ),
    σ 0 = (∅, I) ∧
    σ (Fin.last t) = (∅, O) ∧
    (∀ j, (σ j).1.card ≤ S) ∧
    (∀ i : Fin t, Step E I (σ i.castSucc) (c i) (σ i.succ)) ∧
    ∑ i, c i = q

def fftEdge (k : ℕ) (u v : Fin (k + 1) × Fin (2 ^ k)) : Prop :=
  (v.1 : ℕ) = (u.1 : ℕ) + 1 ∧
    ((v.2 : ℕ) = (u.2 : ℕ) ∨ (v.2 : ℕ) = (u.2 : ℕ) ^^^ 2 ^ (u.1 : ℕ))

end MiscMath.Computability.RedBluePebbleGame
```

Module 2:

```lean
import MiscMath.Computability.RedBluePebbleGame.Spec
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Prod

open MiscMath.Computability.RedBluePebbleGame

namespace Target.RedBluePebbleGame

theorem fft_io_lower_bound {k S q : ℕ} (hk : 1 ≤ k) (hS : 3 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    (2 : ℝ) ^ k * k ≤ 5 * q * Real.logb 2 S

theorem fft_io_bounds {k S q : ℕ} (hk : 1 ≤ k) (hS : 1 ≤ S)
    (h : HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) :
    2 ^ (k + 1) ≤ q ∧ (2 : ℝ) ^ k * (k + 1) ≤ 2 * (q + S) * Real.logb 2 (4 * S)

theorem fft_complete_iff {k S : ℕ} (hk : 1 ≤ k) :
    (∃ q, HasCompleteCalculation (fftEdge k) (Finset.univ.filter (·.1 = 0))
      (Finset.univ.filter (·.1 = Fin.last k)) S q) ↔ 3 ≤ S

end Target.RedBluePebbleGame
```
