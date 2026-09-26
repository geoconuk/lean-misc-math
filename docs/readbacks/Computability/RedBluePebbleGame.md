# Read-back: `Computability/RedBluePebbleGame`, Phase 1 (the FFT statements)

The blind read-backs of the red-blue pebble game's first advertised statements, produced as
[`docs/READBACK.md`](../../READBACK.md) describes. There have been two rounds:

- **Round 2 is current.** It renders every advertised statement, and every definition they are
  stated through, as they now stand.
- **Round 1 is kept** because it surfaced the charging point recorded under it. Its rendering
  of `fft_io_bounds` describes a version of that statement that no longer exists.

## Round 2 (current), 2026-09-26

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

## Round 1, 2026-09-25 (superseded for `fft_io_bounds`)

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
