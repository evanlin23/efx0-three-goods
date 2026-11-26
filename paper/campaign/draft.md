# EFX₀ with Few Relevant Goods per Agent: Refereed Results of a Campaign on Four Goods

*Draft, 2026-11-26. Workstream `paper/campaign`. This is a write-up of results from the repository; it changes no
ledger status.*

> **Scope.** TARGET₄ is **open**: we do not know whether every additive instance in which every agent values at most
> four goods has a complete EFX₀ allocation. Nothing in this draft proves or refutes it. The draft collects what a
> one-day parallel campaign on TARGET₄ established: theorems with written proofs that an independent referee
> checked, counterexamples, and conjectures with their evidence. Each statement carries one of the labels of §0.

## Abstract

An allocation of indivisible goods is EFX₀ if no agent envies another agent's bundle after removing any single good
from it, including a good the envious agent values at zero. For additive valuations, EFX₀ is known to exist when every
agent values at most three goods; the case of four goods (TARGET₄) is open, and the case of arbitrarily many goods is
the open EFX problem for additive valuations. We collect the results of a campaign on four goods. We prove the
following. (i) For two agents, from either serial-dictatorship order, the picks are kept with one absorbing agent, or
one improving chain repairs them; the allocation is computed in $O(m \log m)$ at every number of relevant goods. Bare
existence for two agents is due to Plaut and Roughgarden; the shape is new. (ii) A charity bound that does not depend
on the number of agents: if every agent values at most $k$ goods and every good has at most $d$ valuers, some partial
EFX₀ allocation with strong charity leaves at most $\min\{(k-2)d-1,\ R(d)\}$ goods out, where $R(d) < ed$ is the rainbow
cycle number. Also: exact EFX₀ with $O(\sqrt{kn})$ charity; complete EFX₀ for instances whose agent–good graph has two
or more components with agents; and welfare maxima can strand two goods at $k = 3$ and $k = 4$. (iii) EFX₀ exists for
monotone valuations when the agent hypergraph is linear and some agent lies on no Berge 3-cycle, which extends the
girth-4 theorem of Lianeas, Sgouritsa and Sotiriou. (iv) Serial-dictatorship facts that the central conjecture rests
on, with Lean proofs: serial-dictatorship outcomes are exactly the Pareto-optimal matchings (strict values), some order
picks a maximum matching, and at such picks no agent reachable from an unmatched agent by an alternating path values an
unpicked good. (v) At $k = 3$, in the core case of Draft and Exchange, one improving chain suffices from every order
whose draft is compatible with the peeling priority. (vi) A complete proof that a reconstruction of the 4-limited
algorithm of Viswanathan and Mehta, with one necessary correction, gives ordinary EFX (not EFX₀). On the negative side
we give counterexamples: "one chain from every order" fails on strict $k = 4$ cores; one chain fails at $k = 5$ even
from maximum-matching starts; one round of disjoint chains fails at $k = 5$; and value-monotone methods can get stuck
already at $k = 3$. We end with the conjectures that survive, among them OC₁^max (one chain from every
maximum-matching order), with the evidence for each.

## Contents

0. How to read this draft
1. Introduction
2. Model and definitions
3. Two agents
4. Bounded charity
5. Linear hypergraphs
6. Serial dictatorship and maximum matchings
7. Refutations
8. The k-ladder (mostly evidence)
9. Three relevant goods: one chain from R1-compatible orders
10. Ordinary EFX for 4-limited instances: a reconstruction of Viswanathan–Mehta
11. Open problems and conjectures
12. References

Appendix A. Verification record. Appendix B. Other refereed results. Appendix C. Reproducing the instance checks.

## 0. How to read this draft

**Labels.** Every numbered statement has one of these labels.
- **[R]** Proved. A written proof is given here or in the file named, and the campaign's independent referee
  (branch `claude/k4-referee`, `k4/referee/`) found it CORRECT. The referee's checks are written from the raw
  definitions and share no code with the authors' sessions.
- **[R′]** Proved. The referee found it CORRECT WITH FIXES, and the fix is applied in this text. The fix is stated.
- **[L]** Also machine-checked in Lean 4 (core Lean only, standard axioms only).
- **[V]** A counterexample checked by at least two independent programs from the raw definitions, but **not** in the
  referee's table. The programs are named.
- **[E]** Evidence only: computation on finite data. Random testing can miss rare failures, so [E] never means proved.
- **[C]** Conjecture.

**Sources.** Each result names its source: the file, the section, and the branch where that file lives. The
repository is `evanlin23/efx0-three-goods`. The referee read the sources at the commits named in Appendix A, and
Appendix A also records whether the cited section changed afterwards. "Session" means one of the campaign's parallel
working sessions, and "coordinator" the session that integrated them (branch `claude/kind-lamport-y8fdme`, log
`k4/attack_log.md`).

**What the computations are.** Unless a statement says otherwise, computations here are the sessions' and the
referee's, and they are logged in the repository. Appendix C adds one check by this write-up's session
(`paper/campaign/check_instances.py`). It re-verifies every instance printed in this draft from the printed data, so
transcription errors would show up.

## 1. Introduction

### 1.1 The problem

Agents $N = [n]$ share indivisible goods $M$, $|M| = m$, with additive valuations $v_i(S) = \sum_{g \in S} v_i(g)$,
$v_i(g) \ge 0$. An allocation $X = (X_1, \dots, X_n)$ is **EFX₀** if
$$v_i(X_i) \ \ge\ v_i(X_j \setminus \{g\}) \qquad \text{for all } i \ne j \text{ and every } g \in X_j .$$
The removed good may be worthless to $i$. This is the notion of Plaut and Roughgarden [PR] and of the graph and
multigraph papers [CFKS, AAMMS, LSS]. In *ordinary* EFX the removed good must satisfy $v_i(g) > 0$. The two differ
exactly on goods of value zero: an agent must not envy a bundle that holds a good it values at zero, even though
removing that good leaves the bundle's value unchanged.

The **relevant set** of agent $i$ is $R_i = \{g : v_i(g) > 0\}$, and an instance is **$k$-limited** if $|R_i| \le k$
for every agent. We write

> **TARGET$_k$.** Every $k$-limited additive instance has a complete EFX₀ allocation.

What is known (§1.3 has the details):
- TARGET$_2$ holds: serial dictatorship works.
- TARGET$_3$ is proved in this repository, with a machine-checked proof (ledger row T; [Lin-k3], [Lin-k3s]).
- **TARGET$_4$ is open.**
- TARGET$_k$ for every $k$ is EFX₀ existence for all additive instances, since every instance is $m$-limited.

By a perturbation argument (PROMPT.md, L1), EFX₀ existence for all additive instances is equivalent to EFX existence
for all strictly positive additive instances. That problem is open for $n \ge 4$ agents. So a counterexample to
TARGET$_k$ for any $k$ would refute the additive EFX conjecture.

### 1.2 The campaign

On 2026-11-26 about fifteen sessions attacked TARGET₄ in parallel from different angles. A coordinator integrated
their results, and an independent referee checked every written proof they produced. This draft collects the
statements that survived that process.

The campaign's organizing object was serial dictatorship (SD). Fix an order of the agents; each agent in turn takes
its favourite remaining relevant good. These *picks* form a Pareto-optimal matching. The question is how far the picks
are from a complete EFX₀ allocation. The answers found are these.
- From some orders, nothing needs to change: the unpicked goods can be handed out.
- In general the picks have to be repaired, by an **improving chain**: a sequence of agents, each passing its base to
  the next, in which every agent strictly gains.
- The sharpest surviving conjecture, **OC₁^max** (§11.1), says: from every order whose picks form a maximum matching,
  the picks need at most one improving move, after which one agent absorbs the leftover goods. It implies TARGET₄.
  That implication is machine-checked (§6.4).

The results below are of four kinds.
1. *Theorems that hold for every $k$*: the two-agent shape (§3), the charity bounds (§4), the linear-hypergraph theorem
   (§5) and the matching lemmas (§6).
2. *Counterexamples* (§7). They show which forms of "one chain suffices" are false. They also locate the role of
   $k \le 4$: after one repair, a frozen agent has at most $k - 3$ unpicked goods left, which is at most one at
   $k = 4$ (Lemma 7.4).
3. *Evidence* for the surviving conjectures, collected in the $k$-ladder table (§8).
4. *Two side results*: one chain suffices at $k = 3$ from orders compatible with the peeling priority (§9), and a
   complete proof of a reconstruction of Viswanathan and Mehta's ordinary-EFX algorithm (§10).

### 1.3 Related work, and what was already in the repository

Only works that some session read are cited as such; anything else is marked [unverified] (§12 gives read levels).
- *Two agents.* Plaut and Roughgarden prove EFX₀ existence for two agents with arbitrary monotone valuations, by
  cut-and-choose with the leximin++ solution ([PR], Theorem 4.3; their Definition 2.3 removes any good, so their EFX
  is EFX₀). Our §3 adds the SD shape, not existence.
- *Three agents.* Chaudhury, Garg and Mehlhorn prove EFX₀ existence for three additive agents [CGM].
- *Few goods.* Mahara proves EFX₀ existence whenever $m \le n + 3$, for monotone valuations ([Mah], Theorem 3).
- *Graphs and multigraphs.* EFX₀ exists when every good is valued by at most two agents: on graphs [CFKS] and on
  multigraphs [AAMMS].
- *Hypergraphs.* Lianeas, Sgouritsa and Sotiriou prove EFX₀ existence for monotone valuations on hypergraphs of girth
  at least 4 [LSS]. §5 extends their theorem.
- *Charity.* Chaudhury, Kavitha, Mehlhorn and Sgouritsa give a partial EFX₀ allocation with strong charity, leaving
  fewer goods out than there are sources of the envy graph [CKMS]. Chaudhury, Garg, Mehlhorn, Mehta and Misra relate
  the charity of $(1-\varepsilon)$-EFX to the rainbow cycle number [CGMMM], and Sivashankar proves $R(d) < ed$ [Siv].
- *Four relevant goods.* Viswanathan and Mehta announce ordinary EFX for 4-limited instances, in a three-page extended
  abstract whose key step is stated without proof [VM]. Their notion is ordinary EFX, and goods valued by nobody go to
  an arbitrary agent, so the claim does not settle TARGET₄ (`proofs/citations.md`, item 2). §10 proves a
  reconstruction.
- *Counterexamples for other valuation classes.* EFX can fail for monotone (even submodular) valuations [AMMSW, MS].
  The additive case is open.
- *House allocation.* SD outcomes are the Pareto-optimal matchings [AS98, ACMM], and a maximum Pareto-optimal matching
  exists and is found in polynomial time [ACMM]. §6 reproves the facts we need, with machine-checked proofs.

The repository already contained the following before the campaign (ledger rows named).
- *TARGET$_3$* (row T). It is proved by construction LB⁺ (`proofs/lb_last_step.md`) and by Draft and Exchange (DE)
  [Lin-k3s], both checked in Lean.
- *Reductions to cores at $k = 4$* (rows K4.CORE, K4.TIE). They are proved and checked in Lean; §2.4 states them.
- *Certified cases of TARGET₄* (rows K4.R5, K4.R5c, K4.R5d, K4.R5p, K4.R6a, K4.MC6, K4.MC7). Every connected strict
  $k = 4$ core with $n \le 5$ and a 4-good agent, or with $n = 6$ and exactly one 4-good agent, has an EFX₀
  allocation, and so does every instance whose core components have cyclomatic number at most 4. These are
  computer-certified results from earlier work; this campaign does not add to them.

## 2. Model and definitions

### 2.1 Instances, relevance and EFX₀

An instance has agents $N = [n]$, goods $M$ and additive valuations $v_i \ge 0$. Write $R_i = \{g : v_i(g) > 0\}$
for the relevant set of $i$, and $V(g) = \{i : v_i(g) > 0\}$ for the *valuers* of $g$. The instance is $k$-limited
if $|R_i| \le k$ for all $i$. The *incidence graph* is bipartite, on agents and goods, with an edge $i - g$ when
$g \in R_i$. Its hypergraph form has the agents as vertices and each good $g$ as the edge $V(g)$.

A *partial allocation* $X$ has disjoint bundles; the unallocated goods form the *pool* $P$. Agent $i$ *envies* a set
$B$ if $v_i(B) > v_i(X_i)$. It *strongly envies* $B$ (equivalently, $B$ *threatens* $i$) if
$v_i(B \setminus \{g\}) > v_i(X_i)$ for some $g \in B$. $X$ is EFX₀ if no agent strongly envies another agent's bundle.
Four facts are used throughout.
- A singleton is never strongly envied.
- Toward a bundle $B \subseteq R_i$, EFX₀ for $i$ reads $v_i(X_i) \ge v_i(B) - \min_{g \in B} v_i(g)$.
- Toward a bundle with a good outside $R_i$, EFX₀ for $i$ reads $v_i(X_i) \ge v_i(B)$, that is, no envy.
- The pool has *strong charity* if $v_i(P) \le v_i(X_i)$ for every $i$, and *weak charity* if
  $v_i(g) \le v_i(X_i)$ for every $i$ and $g \in P$.

The *envy graph* $G_X$ has an edge $i \to j$ when $i$ envies $X_j$; its *sources* are the vertices of in-degree 0.
Rotating bundles along a cycle of $G_X$ keeps EFX₀ (PROMPT.md, L3).

Two standard reductions (PROMPT.md, L2 and L3) are used.
- *Peeling.* A *top-heavy* agent ($v_i(a) \ge v_i(R_i \setminus a)$ for its favourite remaining good $a$) can be given
  $\{a\}$ and removed (rule R1). An agent whose private goods are worth at least its other goods can be given its
  private goods and removed (rule R2).
- *Junk.* Goods valued by nobody go to a source of the envy graph after envy cycles are rotated away.

### 2.2 Cores at $k = 4$

A **$k = 4$ core** (ledger K4.CORE; Lean `EFX.IsCore4`) is an instance with at least two agents such that, writing
$P_i$ for the private goods of $i$ (relevant to $i$ only) and $S_i = R_i \setminus P_i$:
- (C1) $3 \le |R_i| \le 4$;
- (C2) $2 v_i(g) < v_i(R_i)$ for every $g$ (strictly balanced: no good is worth half of $R_i$);
- (C3) $|P_i| + 2 \le |R_i|$;
- (C4) $|P_i| = 2 \Rightarrow v_i(P_i) < v_i(S_i)$;
- (C5) every good is relevant to some agent.

It is **strict** if disjoint nonempty subsets of each $R_i$ have different values. It is **connected** if its
incidence graph is connected. Two reductions are proved and machine-checked in the repository.
- *Core reduction* (K4.CORE; Lean `EFX.core_reduction4_conn`). If every connected $k = 4$ core with at most $N$
  agents has an EFX₀ allocation, so does every 4-limited instance with at most $N$ agents.
- *Tie reduction* (K4.TIE; Lean `EFX.tie_reduction`, `EFX.target4_of_strict_cores`). It suffices to treat strict
  profiles.

So TARGET₄ reduces to strict connected $k = 4$ cores. A minimal counterexample also has no agent with two private
goods (K4.MC2, certified). We call such cores the **MC2 class**.

### 2.3 Serial dictatorship

Values are strict within each agent unless stated, and ties are broken by good index. For an order $\pi$ of the
agents, *serial dictatorship* SD($\pi$) lets each agent in turn take its favourite remaining good of $R_i$, or
nothing if none is left. The good $y_i$ agent $i$ takes is its **pick**; an agent that takes nothing is **pickless**.
The unpicked goods form the **junk** $J$. The outcome has two properties (`k4/sdc.md` §2):
- (I1) every good that $i$ prefers to $y_i$ was picked earlier by another agent;
- (I2) every junk good $g \in R_i$ is worth less to $i$ than $y_i$.

Agent $i$ **wants** a good held by another agent if it values that good above its own holding. At SD picks an agent
wants only picks of earlier agents, so the want relation is acyclic. A pick holder whose pick someone wants is
**frozen**. A frozen agent that values some junk good is **dangerous**. A **danger set** of $i$ is a set
$T \subseteq R_i$ of goods outside $X_i$ with $v_i(T) > v_i(X_i)$. A bundle threatens $i$ if and only if it strictly
contains a danger set of $i$, or it lies inside $R_i$ and $v_i(X_j) - \min_{X_j} v_i > v_i(X_i)$ (`k4/sdc.md` §2,
Lemma 2). By (I2), at SD picks a danger set of $i$ made of junk has at least two goods.

A *matching* gives each agent at most one good it values, and each good to at most one agent; SD picks are matchings.
$\nu$ is the maximum size of a matching in the incidence graph. A start is a **maximum-matching start** if its picks
match $\nu$ agents, and a **perfect start** if every agent that has a relevant good holds a pick.

### 2.4 Bases, moves and completions

A *state* gives each agent a *base* $B_i \subseteq R_i$; the other goods form the junk $J$. The SD picks are the state
$B_i = \{y_i\}$. Three kinds of *improving moves* are used (`k4/sdc.md` §29, §31; Lean `IsAddition`, `IsChain`,
`IsRing` in `lean/EFX/OC1Max.lean`).
- **Improving chain** $x_0, x_1, \dots, x_t$ ($t \ge 1$, distinct agents). It comes with pairwise disjoint sets
  $H_0 \subseteq J \cup B_{x_t}$ and $H_i \subseteq J$ ($i \ge 1$), each inside its receiver's relevant set, such that
  $$v_{x_0}(H_0) > v_{x_0}(B_{x_0}), \qquad v_{x_i}(B_{x_{i-1}} \cup H_i) > v_{x_i}(B_{x_i}) \quad (1 \le i \le t),$$
  and every passed base $B_{x_0}, \dots, B_{x_{t-1}}$ is nonempty. Applying it, $x_0$ takes $H_0$, each $x_i$ takes
  $B_{x_{i-1}} \cup H_i$, the rest of $B_{x_t}$ becomes junk, and every other agent keeps its base. Every agent on the
  chain strictly gains.
- **Addition** (the case $t = 0$). One agent adds a nonempty set of junk goods it values to its base.
- **Ring** $w_0, \dots, w_s$ ($s \ge 1$). Each $w_i$ takes its predecessor's nonempty base (cyclically) plus a set of
  junk goods it values, all sets disjoint, and each strictly gains.

A *completion* of a state is a complete allocation $X$ with $B_i \subseteq X_i$ for every $i$. It is **free** if the
junk may go anywhere. It is a **one-absorber completion** if at most one agent (the *absorber*) receives two or more
goods outside its base. The state *extends* if it has an EFX₀ completion.

*Rounds.* A **round** is a set of vertex-disjoint improving chains applied at once, each head taking goods only from
the junk and from its own chain's end (`k4/ksens.md` §6).

### 2.5 The statements tested

All of the following are about $k$-limited instances. They differ in which starts they quantify over, how many moves
they allow, and which completion they require.

| name | statement | source |
|---|---|---|
| SD-C | some order's picks extend (free completion, no move) | `k4/sdc.md` §2 |
| MD | every matching is *value-dominated* by a complete EFX₀ allocation $X$ ($v_i(X_i) \ge v_i(\mu_i)$ for all $i$) | `k4/sdc.md` §28 |
| OC | from **every** order: the picks extend, or extend after one improving chain | `k4/sdc.md` §29 |
| OC₁ | the same with one-absorber completions | `k4/sdc.md` §29 |
| OC₁($t \ge 0$) | OC₁ with additions allowed as the move | `kgen/n3.md` §1 |
| OC₁^max | on strict connected $k = 4$ cores, from every **maximum-matching** order: the picks have a one-absorber completion, or one move (addition, chain or ring) gives a state that has one | `k4/sdc.md` §31 |
| RD, RD₁ | from every order, one round, then a completion (free, resp. one-absorber) | `k4/ksens.md` §6 |
| RD² | the same with two rounds applied one after the other | `k4/ksens.md` §6 |

Each of OC, OC₁, OC₁^max and RD implies MD for the orders it covers, because every agent on a chain gains. Each
implies a complete EFX₀ allocation as soon as it holds for one order, hence TARGET$_k$ (for OC₁^max, through Lemma
6.2 and the reductions of §2.2).

## 3. Two agents

Source: `kgen/n3.md` §9 (branch `claude/kgen-n3`). Refereed against commit `418f876`; §9's mathematics is unchanged at
the head `78f59e9`, which only adds the literature paragraph.

**Setting.** Two agents $a$ and $b$, with $a$ picking first, and arbitrary additive values $v_a, v_b \ge 0$ (ties and
zeros allowed, any number of relevant goods). The pick $y_a$ is $a$'s favourite positively valued good, and $y_b$ is
$b$'s favourite positively valued good in $M \setminus \{y_a\}$, with ties to the smaller index; either may not
exist. The junk is $J = M \setminus \{y_a, y_b\}$. For an agent $c$ and a nonempty set $Z$, $\min_c(Z)$ is $c$'s
smallest value in $Z$, zeros included, so EFX₀ for $c$ toward $Z$ reads $v_c(\text{own}) \ge v_c(Z) - \min_c(Z)$.

In this section a move may be an addition (OC₁($t \ge 0$), §2.5).

### 3.1 Three facts

**Fact 3.1 (LPT cut) [R].** Let LPT$_c$ place the goods in order of decreasing $v_c$ (ties by index), each into the
bundle of smaller current $v_c$-value (the first bundle on a tie). The result $(P, Q)$ is EFX₀ for $c$ in both
directions: $v_c(Q) \ge v_c(P) - \min_c(P)$ and $v_c(P) \ge v_c(Q) - \min_c(Q)$. If the first good in the order has
positive value, the first two goods go to different bundles.

*Proof.* Let $h$ be the last good placed into a nonempty bundle $Z$. The order is decreasing, so $v_c(h) = \min_c(Z)$.
When $h$ was placed, $Z \setminus h$ was worth no more than the other bundle, which only grew afterwards. Hence
$v_c(Z) - \min_c(Z) \le v_c(\text{other})$. Goods of value 0 come last and satisfy the same inequality. For the last
sentence: the first good goes to $P$ (tie), and then $Q$ is the strictly smaller bundle. ∎

**Lemma 3.2 (moving worthless goods) [R].** Let $(X_c, X_d)$ be EFX₀ with $v_c(X_c) \ge v_c(X_d)$, and let $W$ be a set
of goods of $X_c$ that $c$ values at 0. Then $(X_c \setminus W, X_d \cup W)$ is EFX₀, and
$v_c(X_c \setminus W) \ge v_c(X_d \cup W)$.

*Proof.* The value of $c$ is unchanged, and $v_c((X_d \cup W) \setminus g) \le v_c(X_d) \le v_c(X_c)$. For $d$ and
any $g \in X_c \setminus W$: $v_d((X_c \setminus W) \setminus g) \le v_d(X_c \setminus g) \le v_d(X_d) \le v_d(X_d \cup W)$. ∎

**Lemma 3.3 (Tops Lemma; any $n$) [R].** Suppose each agent $i$ has a good $t_i$ that it values at least as much as
every good, with the $t_i$ distinct. Let $S$ be an EFX₀ allocation of $M \setminus \{t_1, \dots, t_n\}$. Then
$X_i = S_i \cup \{t_i\}$ is EFX₀.

*Proof.* Fix $i \ne j$. Removing $t_j$ from $X_j$ leaves $S_j$. If $S_j \neq \emptyset$, then
$v_i(S_j) = (v_i(S_j) - \min_i S_j) + \min_i S_j \le v_i(S_i) + v_i(t_i)$, since $S$ is EFX₀ and $t_i$ is a top of
$i$. Removing $g \in S_j$ leaves $v_i(S_j \setminus g) + v_i(t_j) \le v_i(S_i) + v_i(t_i)$. ∎

The proof uses only that $v_i(t_i)$ is at least $v_i(t_j)$ for every $j$ and at least one good of each $S_j$.

### 3.2 The theorem

**Theorem 3.4 (two-agent OC₁; Theorem 2 of `kgen/n3.md`) [R].** For two agents with arbitrary nonnegative additive
values, from either order, the picks have an EFX₀ completion of one of these shapes:
- **(A1)** both agents keep their picks, and every good of $X_a$ other than $y_a$ is a junk good that $a$ values.
  This is an addition at $a$ (when $X_a \ne \{y_a\}$), with $b$ the only agent holding goods outside its base.
- **(B)** $y_a \in X_b$, and $X_a \subseteq J \cup \{y_b\}$ consists of goods $a$ values, with
  $v_a(X_a) > v_a(y_a)$ and $v_b(y_a) > v_b(y_b)$. This is the improving chain $a \to b$: $a$'s base becomes
  $H_0 = X_a$, and $b$'s base becomes $\{y_a\} \cup (X_b \cap J \cap R_b)$. Only $b$ holds goods outside its base.
- **(D)** a degenerate case: some agent values nothing, or $b$ values only $y_a$ (step 0 of the proof).

In every shape at most one agent holds goods outside its base. The allocation is computed in $O(m \log m)$ time.

*Proof.* Fix the order $(a, b)$; the other order is the same with the names exchanged.

*Step 0 (degenerate cases).*
- If $a$ values nothing, take $X = (\emptyset, M)$. If $b$ values nothing, take $X = (M, \emptyset)$.
- If $b$ values only $y_a$, then $y_b$ does not exist.
  - If $v_a(y_a) \ge v_a(M \setminus y_a)$, take $X = (\{y_a\}, M \setminus y_a)$. Agent $a$ is EFX₀ by the
    inequality, and nobody strongly envies the singleton $\{y_a\}$. Agent $a$ keeps its pick and $b$ absorbs.
  - Otherwise take $X = (M \setminus y_a, \{y_a\})$. This is the chain $a \to b$: $b$ gains $v_b(y_a) > 0$, and
    $a$'s new base, the goods of $M \setminus y_a$ it values, is worth more than $y_a$. $b$ values $a$'s bundle at 0,
    and $b$'s bundle is a singleton, so $X$ is EFX₀.

From now on $y_a$ and $y_b$ exist, and $v_a(y_a), v_b(y_b) > 0$.

*Step 1: $v_b(y_a) > v_b(y_b)$.* Then $y_a$ is $b$'s unique top good and $y_b$ the next good in $b$'s order (the
same tie rule as SD). Let $b$ cut $M$ by LPT$_b$; by Fact 3.1, $y_a \in P$ and $y_b \in Q$. Agent $a$ takes $P$ if
$v_a(P) \ge v_a(Q)$ and $Q$ otherwise, and then $a$'s goods of value 0 to $a$ move to $b$ (Lemma 3.2). The result is
EFX₀: for $b$ by Fact 3.1, for $a$ because it chose its better part, and both are kept by Lemma 3.2.
- If $a$ took $P$: $y_a \in X_a$ (it has positive value for $a$), $y_b \in X_b$, and
  $X_a \setminus y_a \subseteq P \setminus y_a \subseteq J$ consists of goods $a$ values. This is shape (A1).
- If $a$ took $Q$: $v_a(X_a) = v_a(Q) > v_a(P) \ge v_a(y_a)$, $X_a \subseteq Q \subseteq J \cup \{y_b\}$ consists
  of goods $a$ values, $y_a \in P \subseteq X_b$, and $v_b(y_a) > v_b(y_b)$. This is shape (B). (If $a$ values $y_b$
  at 0, $y_b$ has moved to $b$; it is then outside $b$'s new base, and $b$ is still the only agent with goods outside
  its base.)

*Step 2: $v_b(y_a) \le v_b(y_b)$.* Then $y_b$ is $b$'s top over all of $M$, and $y_a$ is $a$'s top. Let $b$ cut $J$
by LPT$_b$ into $(P, Q)$, let $a$ take its better part $S_a$ ($P$ on a tie), let $b$ take $S_b$, and move $a$'s goods
of value 0 from $S_a$ to $S_b$ (Lemma 3.2). This is an EFX₀ allocation of $J$. By the Tops Lemma with $t_a = y_a$ and
$t_b = y_b$, $X = (S_a \cup \{y_a\}, S_b \cup \{y_b\})$ is EFX₀. Both agents keep their picks, and
$X_a \setminus y_a = S_a \subseteq J$ consists of goods $a$ values: shape (A1).

*Complexity.* One sort and linear passes. ∎

**Corollary 3.5 (Claim T of `kgen/n3.md`) [R].** Two agents whose top goods are distinct have an EFX₀ allocation in
which each keeps its top good, and the first agent holds no good it values at 0. *(Step 2 of the proof.)*

**Remarks.**
- *What is new.* EFX₀ existence for two agents is Plaut–Roughgarden, Theorem 4.3 [PR], for monotone valuations.
  Their cut-and-choose does not keep prescribed goods, and the referee found no published source for the SD shape or
  for Corollary 3.5 (`k4/referee/lit_n2.md`; searched no further than [PR]). The new content is the shape, the Tops
  Lemma, and the $O(m \log m)$ construction.
- *Additions are needed* (unrefereed, [E]). With chains of length $t \ge 1$ only, OC₁ fails already for two agents
  (`kgen/n3.md` §3.2: 2 of 8,000 random starts, at $k \ge 7$). On the curated $k = 4$ sets no start needs an addition
  (`kgen/n3.md` §3.3).
- *Not refereed, recorded for orientation.* Lemma P of `kgen/n3.md` §2 peels a top-heavy pick in OC₁ form, and with
  Theorem 3.4 gives OC₁ at $n = 3$ for every order with a top-heavy pick (Corollary 3 of §11 there). Proposition H of
  §10 there shows that OC₁ at $n = 3$ for every $k$, even with distinct tops, would imply EFX₀ for three additive
  agents. So general-$k$ statements at $n = 3$ are as hard as [CGM]. The reduction raises $k$ by 3, so fixed small
  $k$ is not covered.

**Referee report.** `k4/referee/kgen_n3.md` (branch `claude/k4-referee`): CORRECT, with the instruction to cite
[PR] Theorem 4.3 for existence. Its independent check (`k4/referee/theorem2_ref.py`) tests the construction against
the raw EFX₀ definition and an independent OC₁($t \ge 0$) witness test. That covers 496,162 starts: exhaustive over
small value grids, plus 20,000 random instances with $m \le 14$, with 0 failures. A mutation test shows Lemma 3.2 is
needed exactly where it is used: without it, the one-absorber shape breaks on 973 of 40,000 starts.

## 4. Bounded charity

Source: `kgen/charity.md` §2, §3, §6, §8 and `attempts/kgen-charity-welfare-maxima.md` (branch `claude/kgen-charity`).
Refereed against `78deef1` (CH-A, CH-B), `8862555` (CH-F, DU) and `1e986c6`/`0c85d91` (CH-KD); these sections are
unchanged at the head `0c85d91`.

The question is the relevant-goods analogue of bounded charity. Is there an $f(k)$, independent of $n$, such that
every $k$-limited instance has a partial EFX₀ allocation with strong charity leaving at most $f(k)$ goods out?
TARGET₄ is $f(4) = 0$. The answer obtained here is a bound in terms of $k$ and the number $d$ of valuers per good.

### 4.1 The rules and the source digraph

Let $X$ be a partial allocation with pool $P$, envy graph $G_X$, sources $S$, $\sigma = |S|$. For each agent $s$, let
$C(s)$ be the set of agents reachable from $s$ in $G_X$, including $s$.
- A **champion option** of a set $B$ that some agent envies is a pair $(Z, t)$ with $Z \subseteq B$, $t$ envying $Z$,
  and nobody envying $Z \setminus \{h\}$ for any $h \in Z$ ([CKMS], Definition 3).
- The **source digraph** $D$ has vertex set $S$. For every $s \in S$, $g \in P$ with $X_s \cup \{g\}$ envied, every
  option $(Z, t)$ of $X_s \cup \{g\}$ and every source $s'$ with $t \in C(s')$, it has an edge $s \to_g s'$ of colour
  $g$.
- A cycle of $D$ is **rainbow** if its vertices are distinct and its colours are distinct.

The rules are CKMS's Algorithm 2, with U2 taken along a shortest rainbow cycle.
- (R) If $G_X$ has a cycle, rotate bundles along it.
- (U0) If some $g \in P$ can be added to a bundle keeping EFX₀, add it.
- (U1) If some agent envies $P$, let $(Z, i)$ be an option of $P$. Give $Z$ to $i$, and return $X_i \cup (P \setminus Z)$
  to the pool.
- (U2) If $D$ has a rainbow cycle, take a shortest one, $s_0 \to_{g_0} s_1 \to \dots \to s_{\ell-1} \to_{g_{\ell-1}} s_0$,
  with options $(Z_i, t_{i+1})$ of $X_{s_i} \cup \{g_i\}$, $t_{i+1} \in C(s_{i+1})$, and envy paths $\pi_{i+1}$ from
  $s_{i+1}$ to $t_{i+1}$. Each agent on $\pi_{i+1}$ other than $t_{i+1}$ takes the bundle of its successor on the
  path, $t_{i+1}$ takes $Z_i$, and $(X_{s_i} \cup \{g_i\}) \setminus Z_i$ returns to the pool.

A **stopping state** is an EFX₀ state with no envy cycle to which none of U0, U1, U2 applies.

### 4.2 The theorem

**Theorem 4.1 (CH-KD; `kgen/charity.md` §8) [R].** Suppose every agent values at most $k$ goods and every good is
valued by at most $d \ge 1$ agents. Then some EFX₀ state with strong charity has a pool $P$ with:
1. $P = \emptyset$ if $k \le 2$;
2. $|P| \le (k - 2) \min_{g \in P} |V(g)| - 1 \le (k - 2)d - 1$ if $k \ge 3$;
3. $|P|! \le d^{|P| - 1}$; hence $|P| \le R(d) < e \cdot d$, where $R(d)$ is the rainbow cycle number.

All three hold at every stopping state, and the bound does not depend on $n$. For $k = 4$ it gives $|P| \le 2, 4, 6, 9$
for $d = 2, 3, 4, 5$, and $2d - 1$ from $d = 5$ on.

*Proof.*

*Step 1 (U2 is well defined).* In a shortest rainbow cycle the agents $t_1, \dots, t_\ell$ are distinct, and the
paths $\pi_1, \dots, \pi_\ell$ are pairwise vertex-disjoint. Suppose $\pi_a$ and $\pi_b$ ($a \ne b$) share a vertex.
Then $t_b$ is reachable from $s_a$, so the option $(Z_{b-1}, t_b)$ of $X_{s_{b-1}} \cup \{g_{b-1}\}$ gives an edge
$s_{b-1} \to_{g_{b-1}} s_a$. Then $s_a \to s_{a+1} \to \dots \to s_{b-1} \to s_a$ is a rainbow cycle with
$(b - a) \bmod \ell \in [1, \ell - 1]$ edges, which is shorter. Equal $t$'s share a vertex. A source has in-degree 0,
so it lies only on its own path.

*Step 2 (a stopping state exists).* Each rule keeps EFX₀:
- (R): [CKMS] Lemma 2;
- (U0): by its condition;
- (U1): [CKMS] Lemma 5, since nobody envies $Z \setminus h$ and $i$'s value rises;
- (U2): [CKMS] Lemma 7, whose proof assumes vertex-disjoint envy paths, which Step 1 supplies.

Rules (R), (U1) and (U2) strictly raise $\sum_i v_i(X_i)$ ([CKMS] Lemmas 2, 5, 7), and (U0) keeps it and shrinks the
pool. So the pair (welfare, $-|P|$) rises lexicographically, and every sequence of rules from the empty allocation
stops. At a stopping state $G_X$ is acyclic, so $\sigma \ge 1$. Since U1 fails, the pool has strong charity, hence
weak charity. Assume $P \ne \emptyset$ from here on.

*Step 3 (champions are local valuers).* Let $s \in S$ and $g \in P$. Then $X_s \cup \{g\}$ is envied, and every
option $(Z, t)$ of it satisfies:
- $g \in Z \subseteq R_t$, and $\emptyset \neq Z \setminus \{g\} \subseteq X_s$;
- $t \ne s$ and $t \notin C(s)$;
- $t$ values a good of $X_t$.

Indeed, U0 fails for $(s, g)$, so some agent strongly envies $X_s \cup \{g\}$, hence envies it. If $g \notin Z$, then
$Z \subseteq X_s$ and $t$ envies $X_s$, impossible for a source. A good of $Z$ worth 0 to $t$ could be dropped with
$t$ still envying, against minimality. $Z = \{g\}$ is not envied, by weak charity. If $t \in C(s)$, the one-edge cycle
$s \to_g s$ is rainbow and U2 would apply; this also gives $t \ne s$. Finally $v_t(X_t) \ge v_t(g) > 0$.

*Step 4 (parts 1 and 2).* Fix $g \in P$ and pick for each $s \in S$ one option $(Z_s, t_s)$ of $X_s \cup \{g\}$. By
Step 3, $t_s \in V(g)$, $t_s \ne s$, and $t_s$ values a good of $X_s$. Then $R_t$ contains $g$, a good of $X_t$, and
one good of each $X_s$ with $t_s = t$; these bundles are disjoint, disjoint from $P$, and different from $X_t$. So
$t = t_s$ for at most $|R_t| - 2 \le k - 2$ sources, and $\sigma \le (k - 2)|V(g)|$. If $k \le 2$ this contradicts
$\sigma \ge 1$, so $P = \emptyset$ (part 1).

Next, $|P| \le \sigma - 1$. Otherwise walk in $D$ from any source, each time along an edge of a colour not used yet.
Every vertex has an out-edge of every colour, by Step 3 and since every agent lies in $C(s')$ for some source $s'$.
After at most $\sigma \le |P|$ steps a vertex repeats, and the closed segment is a rainbow cycle. With the previous
bound this gives part 2.

*Step 5 (part 3: the rainbow cycle reduction with $\varepsilon = 0$).* Fix for every agent $a$ a source $\sigma(a)$
with $a \in C(\sigma(a))$, and for every $s \in S$, $g \in P$ one option, with champion $c(s, g)$. Let
$Q_g = \{c(s, g) : s \in S\}$. Build the $|P|$-partite digraph $\Gamma$ with parts $V_g = \{g\} \times \sigma(Q_g)$ and,
for $g \ne h$, an edge $(g, s_1) \to (h, s_2)$ if and only if $\sigma(c(s_2, g)) = s_1$.
- Every vertex $(h, s_2)$ has the in-neighbour $(g, \sigma(c(s_2, g))) \in V_g$ in every other part $V_g$.
- $\Gamma$ has no rainbow cycle (a cycle meeting each part at most once). A cycle
  $(g_1, s_1) \to \dots \to (g_\ell, s_\ell) \to (g_1, s_1)$ with distinct $g$'s means $c(s_{i+1}, g_i) \in C(s_i)$,
  that is, edges $s_{i+1} \to_{g_i} s_i$ of $D$. That is a closed walk of $D$ with distinct colours. Between two visits
  of one vertex it contains a rainbow cycle of $D$, and U2 would apply.
- $|V_g| \le |Q_g| \le |V(g)| \le d$, since champions of $g$ value $g$ (Step 3).

Sivashankar's packing inequality ([Siv], Theorem 3) says: a digraph with nonempty parts $V_1, \dots, V_p$, the
in-neighbour condition and no rainbow cycle satisfies $(p-1)! \sum_i |V_i| \le \prod_i |V_i|$. Since
$\prod / \sum$ is increasing in each part size, $|V_i| \le d$ gives $p! \le d^{p-1}$, hence $p < ed$. ∎

**Theorem 4.2 (CH-A and CH-B; `kgen/charity.md` §3) [R].** At every stopping state of a $k$-limited instance:
- **(CH-A)** $|P|(|P| - 1) \le e(k - 2) n$, so $|P| \le \tfrac12 + \sqrt{e(k-2)n + \tfrac14} = O(\sqrt{kn})$;
- **(CH-B)** if every good has at most $d$ valuers, $|P| \le R(d) < ed$, whatever $n$ and $k$.

*Proof.* CH-B is part 3 of Theorem 4.1. For CH-A, take $\Gamma$ of Step 5, with $p = |P|$ and $n_g = |V_g|$. A champion
$t \in Q_g$ values $g$, a good of its own bundle and a good of a source's bundle (Step 3). So it values at most $k - 2$
pool goods and lies in at most $k - 2$ sets $Q_g$, and $\sum_g n_g \le \sum_g |Q_g| \le (k - 2)n$. By AM–GM,
$\prod n_g \le (\sum n_g / p)^p$, so the packing inequality gives $(p-1)!\, p^p \le (\sum n_g)^{p-1}$. With
$(p-1)! \ge ((p-1)/e)^{p-1}$ this gives $\sum n_g \ge \frac{p-1}{e} p^{p/(p-1)} \ge p(p-1)/e$. ∎

**Corollary 4.3 (CH-KD′) [R].** At every stopping state and for every $d \ge 1$,
$|P| \le R(d) + |H_d|$, where $H_d$ is the set of pool goods with more than $d$ valuers. *Proof.* The parts $V_g$
with $g \in P \setminus H_d$ induce a sub-digraph of $\Gamma$. It keeps the in-neighbour condition between its parts and
has no rainbow cycle; apply the packing inequality to it. ∎

So beyond $R(d)$, charity is paid only for unallocated goods with many valuers.

**Remarks.**
- *Why $\varepsilon = 0$ works.* The rainbow-cycle reduction of [CGMMM] needs $\varepsilon > 0$, because a good is
  "valuable" when it exceeds an $\varepsilon$-fraction of a bundle, and without sparsity every good may be valuable to
  every agent. With genuine zeros, Step 3 shows that only valuers of $g$ champion $g$. The perturbation that makes all
  values positive (PROMPT.md, L1) would destroy exactly this.
- *Novelty.* As far as the sessions' literature survey found, neither CH-A nor an $n$-independent bound like CH-B
  appears in the literature; the best general charity for exact EFX is $n - 2$
  (`research_notes/EFX literature from the agent side/agent_count_side.md` §4, not re-read for this draft) [unverified].
- *Values of $R(d)$.* $R(3) = 3$ and $R(4) = 4$ are reported by [Siv] from computations of Kirchweger and Szeider
  [unverified]. If they hold, the $k = 4$ bounds improve to 3 and 4 for $d = 3, 4$. Nothing above depends on them.
- *The method cannot give $f(k)$* (unrefereed: Propositions CH-D and CH-E of `kgen/charity.md` §4–§5). There are
  stopping states, and even Pareto maxima among partial EFX₀ allocations, that leave $\Theta(\sqrt n)$ goods out at
  every $k \ge 3$. So any proof of an $n$-independent $f(k)$ must leave the stopping states of these rules.

**Referee report.** `k4/referee/charity.md` (CH-A, CH-B and the lemmas behind them: CORRECT) and `k4/referee/chkd.md`
(CH-KD and CH-KD′: CORRECT). The referee read [CKMS] §2 and [Siv] §1, §3, and re-derived Sivashankar's injection
proof. Their one wording point: cite [CKMS] Lemma 7 together with Step 1, because Lemma 7's proof uses
path-disjointness that CKMS's precondition does not state. This text does so. The referee's checks are:
- a SAT search confirming the packing inequality on 62 size vectors;
- the four rules run on 6,000 random instances and on the stalled families, with every claimed property asserted
  after each of 36,035 rule applications, 0 failures.

### 4.3 Disconnected instances

**Proposition 4.4 (DU; `kgen/charity.md` §3) [R].** If the incidence graph has at least two connected components that
contain agents, the instance has a complete EFX₀ allocation. (Additive valuations; also monotone ones, with $R_i$
the support of $v_i$.)

*Proof.* Let $I_1, \dots, I_c$ ($c \ge 2$) be the components with agents, and $J_0$ the goods valued by nobody. In each
$I_r$ take a stopping state $X^r$ (Theorem 4.1, Step 2): EFX₀ inside $I_r$, with strong charity
$v_a(P_r) \le v_a(X^r_a)$ and an acyclic envy graph, hence a source $s_r$. Give $P_r$ to $s_{r+1}$ (indices mod $c$)
and $J_0$ to $s_1$. Received goods are worthless to their receiver, so no agent's own value changes. Let $a \in I_r$
look at the bundle $B$ of an agent $b$.
- If $b \in I_r$: $B = X^r_b \cup E$ with $E$ worthless to $a$, and $E \ne \emptyset$ only if $b$ is a source of
  $I_r$. Removing $h \in E$ leaves $v_a(X^r_b) \le v_a(X^r_a)$, since $b$ is unenvied. Removing $h \in X^r_b$ leaves
  $v_a(X^r_b \setminus h) \le v_a(X^r_a)$, by EFX₀ in $I_r$.
- If $b \notin I_r$: $a$ values at most the goods of $P_r$ in $B$, and $v_a(P_r) \le v_a(X^r_a)$ by strong charity. ∎

So a counterexample to TARGET$_k$, and any instance that needs charity, is connected.

**Referee report.** `k4/referee/charity.md` §5 and `k4/referee/chf.md`: CORRECT, re-derived. The session checked the
construction on 2,000 random unions (`union_dump.log`).

### 4.4 Welfare maxima strand goods

For an instance $I$, let $w^*(I)$ be the largest total value $\sum_i v_i(X_i)$ over partial EFX₀ allocations, and
$p^*(I)$ the fewest unallocated goods among those of total $w^*(I)$. Consider the statement:

> **W($k, f$).** Every $k$-limited additive instance has $p^*(I) \le f$.

A welfare maximum with $p^*(I)$ goods out is a stopping state of §4.1, so W($k, f$) would give $f(k) \le f$.

**Proposition 4.5 (CH-F; `kgen/charity.md` §6) [R].** W(4, 1) and W(3, 1) are false. Here is the $k = 4$ instance
($n = 9$, $m = 14$, goods $0, \dots, 13$).

| agent | values (good: value) | holds in $X$ |
|---|---|---|
| $c(g_0, j_0)$ | 0: 20, 6: 21, 8: 40 | {8} |
| $c(g_1, j_0)$ | 0: 12, 7: 16, 9: 27 | {9} |
| $c(g_0, j_1)$ | 2: 20, 6: 21, 10: 40 | {10} |
| $c(g_1, j_1)$ | 2: 12, 7: 13, 11: 24 | {11} |
| $c(g_0, j_2)$ | 4: 20, 6: 21, 12: 40 | {12} |
| $c(g_1, j_2)$ | 4: 9, 7: 10, 13: 18 | {13} |
| $s_0$ | 0: 2, 1: 1, 12: 7, 13: 4 | {0, 1} |
| $s_1$ | 2: 2, 3: 1, 8: 5, 9: 4 | {2, 3} |
| $s_2$ | 4: 2, 5: 1, 10: 8, 11: 4 | {4, 5} |

The state $X$ leaves goods 6 and 7 out and has total value 198. It is EFX₀ with strong charity. It is the unique
welfare maximum over partial EFX₀ allocations: every EFX₀ allocation leaving at most one good out has total at most
197, and 197 is attained. The $k = 3$ instance ($n = 12$, $m = 17$: the same design with relay agents, total 484
against at most 483) is in `kgen/charity/w_counterexample.py` (`V3`, `X3`) on branch `claude/kgen-charity`.

*Design.* This is the hypergraph of S′(3, 4) (`kgen/charity.md` §5).
- Source $s_j$ holds $\{x_j, x'_j\} = \{2j, 2j+1\}$.
- Champion $c(g, j)$ holds its own good and values $x_j$ and the pool good $g$.
- Source $s_j$ also values the goods held by the champions $c(\cdot, j-1)$ (indices mod 3).

The values were found by an exact search over real values (`w_synth_family.py`, z3).

*Verification.* This is a finite claim, so the "proof" is an exact computation. Three methods agree:
- the session's SAT welfare maximizer;
- the session's separately written mixed-integer program (HiGHS);
- the referee's exact search, with no SAT and no MILP (`k4/referee/chf_ref.py`).

The referee's search has two steps. It first reduces to EFX₀ *orientations*: dropping goods held by non-valuers keeps
EFX₀ and the welfare. It then enumerates every orientation of welfare at least 198, with two sound prunes, and every
placement of the set-aside goods with at most one good out. Appendix C re-checks the printed state.

So welfare maxima strand two goods even at $k = 3$, where complete EFX₀ allocations always exist (TARGET$_3$). W($k$)
with $f \ge 2$ is open (§11.5).

**Referee report.** `k4/referee/chf.md`: CORRECT for both instances; single implementation on the referee's side,
independent of the session's two.

## 5. Linear hypergraphs

Source: `k4/girth.md` §1–§4 (branch `claude/k4-girth`). Refereed against `5b79844`, with the later additions
(generalized Lemma SLACK, Proposition HT) against `90c116f`; the proved statements are unchanged at the head `a494e3b`.

### 5.1 The model of Lianeas, Sgouritsa and Sotiriou

LSS [LSS] work with normalized monotone valuations $v_i : 2^M \to \mathbb{R}_{\ge 0}$ on a hypergraph. The agents are
vertices, and each good $g$ is an edge $e_g$: an agent $i \notin e_g$ has $v_i(S \cup \{g\}) = v_i(S)$ for every $S$.
For additive valuations, $e_g = V(g)$. EFX in [LSS] removes any good, so it is EFX₀.
- A *Berge cycle* of length $\ell$ is $(x_1, e_1, x_2, e_2, \dots, x_\ell, e_\ell, x_1)$ with distinct vertices,
  distinct edges, and $x_t, x_{t+1} \in e_t$.
- The *girth* is the length of a shortest Berge cycle.
- The hypergraph is **linear** if two agents share at most one good, that is, if it has no Berge 2-cycle.

LSS prove that girth at least 4 implies EFX₀ existence, in polynomial time ([LSS], Theorem 1).

**Their algorithm** ([LSS] §3; digest in `k4/girth.md` §1.2). Choose a special vertex $0$, label its neighbours
$1, \dots, n_0$ and the other agents $n_0 + 1, \dots, n - 1$; higher labels have priority. A partial allocation $X$
is an *orientation* if every allocated good goes to one of its endpoints. Write $U(X)$ for the unallocated goods and
$U_i(X)$ for those relevant to $i$. The target properties are:
- (1) $X$ is a partial EFX₀ orientation;
- (2) vertex 0 is not envied, and a neighbour $i$ of 0 is envied only if it holds the good it shares with 0;
- (3) $v_i(X_i) \ge v_i(e)$ for every $i$ and every $e \in U_i(X)$;
- (4) $v_i(X_i) \ge v_i(U_i(X))$ for every envied $i$.

The three algorithms are these.
- *Algorithm 1 (FixProp3).* While some $j$ and $e \in U(X)$ have $v_j(e) > v_j(X_j)$, let $j$ be the highest-labelled
  such vertex. It drops its bundle and takes its best unallocated relevant good.
- *Algorithm 2.* Run FixProp3. Then, while some envied $i$ has $v_i(U_i(X)) > v_i(X_i)$, let $i$ take $U_i(X)$ and run
  FixProp3 again.
- *Algorithm 3.* While some unallocated good contains a non-envied vertex $j$, give it to $j$. Then give everything
  left to vertex 0.

LSS's Lemmas 3.1–3.5 show that Algorithm 2 ends with (1)–(4) and that Algorithm 3 returns a complete EFX₀ allocation.

### 5.2 Linear hypergraphs with an agent on no 3-cycle

**Theorem 5.1 (T1; `k4/girth.md` §4) [R].** Let the hypergraph be linear, and let some agent lie on no Berge 3-cycle.
Then an EFX₀ allocation exists, for monotone valuations in the model of §5.1. In particular this holds for additive
valuations, with goods valued by nobody and several private goods per agent allowed.

*Proof.* Run LSS's algorithm with that agent as vertex 0. Linearity is LSS's Observation 2.1 ("two vertices share at
most one edge"). In §3 of [LSS], Observation 2.2, the only consequence of girth at least 4 beyond linearity, is invoked
exactly once, in the proof of Lemma 3.4. Every other step uses Observation 2.1 or nothing: Lemma 3.2 (Algorithm 2's
loop), the case $|X_i| > 1$ of Lemma 3.4, Lemma 3.5, and Lemma 3.3 (labels only). The digest that locates these uses
is `k4/girth.md` §1.2, and the referee confirmed it against the text.

The use of Observation 2.2 is the following case. Let $i$ be a neighbour of 0, let $f_i$ be the good that $i$ shares
with 0, and let $X_i = \{e\}$ with $e \neq f_i$. Lemma 3.4 needs that a neighbour $j$ of 0 with $j \notin f_i$ does
not value $e$. LSS derive this from girth at least 4. It suffices that 0 lies on no Berge 3-cycle. Suppose $j \in e$.
Then $(0, f_i, i, e, j, f_j, 0)$ is a Berge 3-cycle through 0:
- the vertices $0, i, j$ are distinct;
- $f_i \neq f_j$, since $j \notin f_i$;
- $e \neq f_i$ by assumption;
- $e \neq f_j$, since otherwise 0 and $i$ would share both $e$ and $f_i$, against linearity.

Every other step of [LSS] §3 applies unchanged. ∎

**Points the referee checked that [LSS] leaves implicit** (`k4/referee/girth.md` §1). Both hold here.
- In Lemma 3.4, vertex 0 itself does not envy $i$, because 0 and $i$ share only $f_i$, so $0 \notin e$.
- [LSS] works with a *set* of edges. Our instances have parallel edges of size 0 (goods valued by nobody) and size 1
  (several private goods of one agent). Such edges lie on no Berge cycle, and each lemma survives them: private
  edges of $i$ are irrelevant to everyone else, and Algorithm 3 gives size-0 edges to 0, where nobody values them.

**Corollary 5.2 [R].** A linear counterexample to TARGET₄, if one exists, has every agent on a Berge 3-cycle and a good
with at least three valuers. *(The first by Theorem 5.1. The second because instances in which every good has at most
two valuers are multigraph instances, covered by [AAMMS] (ledger T3).)*

**Proposition 5.3 (HT; `k4/girth.md` §4) [R].** For $t \ge 2$, every monotone valuation profile on the hypergraph of
the core $H_t$ has an EFX₀ allocation, computed by LSS's algorithm with $\ell$ as vertex 0. This includes every
additive profile, not only the strict ones of the source file.

$H_t$ (`k4/c4.md` §7) has $4t + 1$ agents $\ell$, $x_{j,i}$, $y_j$ ($1 \le j \le t$, $1 \le i \le 3$), and $10t + 3$
goods. The valuers of each good are:

| good | valuers |
|---|---|
| $g_1$ | $\ell$, $x_{1,1}, x_{1,2}, x_{1,3}$ |
| $g_j$ ($2 \le j \le t$) | $x_{j,1}, x_{j,2}, x_{j,3}$, $y_{j-1}$ |
| $z$ | $\ell$, $y_t$ |
| $a_{j,i}$ | $x_{j,i}$, $y_j$ |
| $b_{j,i}$, $c_{j,i}$ | $x_{j,i}$ |
| $u$, $u'$ | $\ell$ |

*Proof.* The pairs of agents that share a good are $(\ell, x_{1,i})$ (only $g_1$), $(\ell, y_t)$ (only $z$),
$(x_{j,i}, x_{j,i'})$ (only $g_j$), $(x_{j,i}, y_j)$ (only $a_{j,i}$) and $(y_{j-1}, x_{j,i})$ (only $g_j$). So
$H_t$ is linear. A Berge 3-cycle through $\ell$ uses two different goods of $\ell$ that another agent values, so $g_1$
and $z$. It has the form $(\ell, g_1, x_{1,i}, e, y_t, z, \ell)$ with $e$ a good shared by $x_{1,i}$ and $y_t$. Agent
$y_t$ values only $a_{t,1}, a_{t,2}, a_{t,3}$ and $z$, so for $t \ge 2$ no such $e$ exists. Apply Theorem 5.1. ∎

The families $H_t$ are those on which the earlier construction LB₄ʳ needs unboundedly many rotations (`k4/c4.md` §7).
`k4/girth.md` §4 states the same for the doubled family $HH_t$ (`k4/lemmam_bt.md` §3) and the gadget chains. The
referee did not rebuild $HH_t$, so those parts are proved by the session but not refereed. Theorem 5.1 covers few
small cores: 5 of the 1,002 four-agent and 77 of the 31,584 five-agent core hypergraphs (`k4/girth.md` §4, [E]).
Small cores are dominated by 2-cycles.

**Referee report.** `k4/referee/girth.md`: CORRECT. The referee read [LSS] §2–§3 in full from the PDF and
implemented Algorithms 1–3 from the text, with every choice randomized. The check covers 1.06 million runs on random
linear hypergraphs, additive and monotone, with 0 failures. The mutation that puts vertex 0 *on* a 3-cycle fails 9,834
times, always in the step the proof replaces (log `results/k4_referee/girth_ref.log`). Proposition HT was checked
for $t \le 6$ (`k4/referee/ht_ref.py`).

### 5.3 Three completion lemmas

These lemmas hold beyond linear hypergraphs, and Conjecture DYN (§11.4) is built on them. Write $U$ for the
unallocated goods, $U_i = U \cap R_i$, and $E$ and $N$ for the envied and the non-envied agents.

**Lemma 5.4 (SINK) [R].** For any monotone valuations, let $X$ be a partial EFX₀ allocation and $s$ an agent with
$v_i(X_i) \ge v_i(X_s \cup U)$ for every $i \ne s$. Giving $U$ to $s$ gives a complete EFX₀ allocation.

*Proof.* Nobody envies $X_s \cup U$, so nobody strongly envies it. The value of $s$ only rises, and the other bundles
are unchanged. ∎

**Lemma 5.5 (PARK; linear, monotone) [R].** Let $X$ be a partial EFX₀ orientation with (3) for all agents and (4) for
the envied ones. For an envied $i$, let its *safe set* be $S_i = \{u \in N : v_i(X_u \cup U_i) \le v_i(X_i)\}$.
Suppose that every unallocated good whose valuers are all envied has a common safe vertex
$u_e \in \bigcap_{i \in V(e)} S_i$, and that $N \neq \emptyset$ if some good is valued by nobody. Give each good of the
first kind to $u_e$, every other valued unallocated good to one of its non-envied valuers, and the goods valued by
nobody to a non-envied agent. The result is a complete EFX₀ allocation.

*Proof.* Envied agents keep their bundles and nobody's value drops, so no new strong envy arises toward them. Let
$u \in N$ and $k \ne u$; the new bundle is $Y_u \subseteq X_u \cup U$.
- If $k$ is envied and $u \in S_k$, then $Y_u \cap R_k \subseteq X_u \cup U_k$ and
  $v_k(Y_u) \le v_k(X_u \cup U_k) \le v_k(X_k)$.
- Otherwise no good of the first kind valued by $k$ went to $u$. Every good of $Y_u$ that $k$ values contains both $u$
  and $k$, so by linearity there is at most one, $f$. If $f \in X_u$, then $v_k(f) \le v_k(X_u) \le v_k(X_k)$, since
  $u$ is non-envied. If $f \in U$, then $v_k(f) \le v_k(X_k)$ by (3).

So nobody envies $Y_u$, and the goods valued by nobody can be added. ∎

(The hypothesis $N \ne \emptyset$ for goods valued by nobody is the referee's addition. In a partial EFX₀ orientation
every agent can be envied, as in an envy 3-cycle on a triangle; rotating envy cycles first also provides it.)

**Lemma 5.6 (SLACK; any hypergraph, monotone) [R].** Let $X$ be a partial EFX₀ allocation with (3) for all agents, let
$u$ be a non-envied agent with $X_u = \{f\}$ or $X_u = \emptyset$, and let $e$ be any unallocated good. Then replacing
$X_u$ by $X_u \cup \{e\}$ keeps a partial EFX₀ allocation.

*Proof.* Let $k \ne u$.
- If $k$ values both $f$ and $e$, removing either leaves one good worth at most $v_k(X_k)$: $f$ because $u$ is
  non-envied, $e$ by (3).
- If $k$ values only $f$, then $v_k(\{f, e\}) = v_k(f) \le v_k(X_k)$.
- If $k$ values only $e$, then $v_k(\{f, e\}) = v_k(e) \le v_k(X_k)$ by (3).

If $X_u = \emptyset$, the new bundle is a singleton. The value of $u$ does not drop. ∎

So a non-envied agent holding one good can absorb any one leftover good, even where it is not safe for the good's
valuers. The slack of a two-good bundle replaces envy-freeness.

**Referee report.** `k4/referee/girth.md` §2 and §5 (the generalized SLACK): CORRECT. The checks cover every partial
orientation of small random linear instances. They test 128,383 SINK cases, 343,429 PARK completions, 97,621 SLACK
cases and 16,549 combinations against the raw definition, with 0 failures. (In passing, the referee found that a
remark "Fact F2 also holds for monotone valuations" in `k4/girth.md` is false. Nothing above uses it.)

## 6. Serial dictatorship and maximum matchings

Sources: `k4/sdc.md` §28 and §31 (coordinator branch `claude/kind-lamport-y8fdme`) and `k4/oc1_hall.md` §19 (branch
`claude/k4-oc1-hall`). Refereed against `d48084e` and `e2b4701`. Lean: `lean/EFX/OC1Max.lean` on branch
`formal/k4-oc1max` (head `838fb0e`).

These three lemmas make the central conjecture OC₁^max imply TARGET₄, and they rule out the mechanism of every known
counterexample to "one chain from every order" (§7.2). All three are close to known facts about house allocation
[AS98, ACMM]; the proofs here are short and self-contained, and machine-checked.

**Lemma 6.1 (SDPO; `k4/sdc.md` §28) [R, L].** With strict values (agents may stay unmatched), the SD outcomes over all
orders are exactly the Pareto-optimal matchings.

*Proof.* ($\subseteq$) Let a matching $\mu'$ Pareto-dominate $Y = \mathrm{SD}(\pi)$, and let $i$ be the first agent of
$\pi$ with $\mu'_i \ne Y_i$. The agents before $i$ hold the same goods in both matchings, so $\mu'_i$, if it exists, was
available when $i$ picked. If $Y_i$ is none, then $\mu'_i$ exists, which contradicts the fact that $i$ took nothing
while a good it values was available. Otherwise $i$ took its favourite available good, so $v_i(\mu'_i) < v_i(Y_i)$ by
strictness ($\mu'_i =$ none gives value 0). Either way domination fails, so $\mu' = Y$.

($\supseteq$) Let $\mu$ be Pareto-optimal. Three facts follow.
- Every agent's favourite good is held, since otherwise the agent could take it.
- The pointers from each matched agent not holding its favourite to the holder of that favourite cannot form a cycle,
  since trading along it improves everyone on it. So some matched agent holds its favourite.
- An unmatched agent's goods are all held.

Put an agent $a$ that holds its favourite first, and remove $a$ and $\mu_a$. Then $\mu$ stays Pareto-optimal on the
rest, because a domination there would extend. By induction, with "favourite" meaning "favourite remaining good", and
with the unmatched agents last, SD reproduces $\mu$. ∎

With ties both inclusions fail. For example, agent 1 values goods $a$ and $b$ equally and breaks the tie toward $a$,
and agent 2 values only $a$. Then order $(1, 2)$ gives $(a, -)$, which $(b, a)$ dominates. The referee found SD $\ne$
PO on 1,105 of 2,000 tied instances. OC₁^max is stated for strict cores, so this is consistent. The fact is classical
for complete lists [AS98, Lemma 1] and for incomplete lists [ACMM, §6 Lemma 1] (read by the TTC session's literature
readers; `k4/ttc.md` §1).

**Lemma 6.2 (MAXSD; `k4/sdc.md` §31) [R, L].** In every instance with strict values, some SD order's picks form a
maximum matching of the incidence graph.

*Proof.* Let $M$ be a maximum matching that is Pareto-optimal among maximum matchings (one exists, by finiteness). A
Pareto improvement $M'$ of $M$ keeps every matched agent matched, since that agent's value stays positive. So
$|M'| \ge |M|$, $M'$ is maximum, and $M' = M$. Hence $M$ is Pareto-optimal among all matchings, and an SD outcome by
Lemma 6.1. ∎

The lemma also holds with ties when SD breaks ties by index: perturbing values by the tie-breaking order changes
neither the SD outcomes nor the incidence graph (referee's remark). The existence of a maximum Pareto-optimal matching
is [ACMM], Theorem 1.

**Lemma 6.3 (MAX; `k4/oc1_hall.md` §19; also Lemma T5 of `k4/ttc.md` §13) [R, L].** Let the picks $Y$ form a maximum
matching, and let $S$ be the set of agents reachable from a pickless agent by an alternating path
$u, g_1, j_1, g_2, j_2, \dots$, where $u$ has no pick, $g_l \in R_{j_{l-1}}$ (with $j_0 = u$) is a pick, and $j_l$ is
its holder. Then:
1. no agent of $S$ values a junk good;
2. so no dangerous frozen agent lies in $S$. Every agent on a want-chain above a dangerous agent holds a pick, and
   every such chain ends at an unfrozen pick holder.

*Proof.* (1) If $j \in S$ valued a junk good $g'$, the alternating path from $u$ to $j$ followed by the edge $j - g'$
would be augmenting, since $u$ and $g'$ are both unmatched. That contradicts maximality. (2) Wanting a pick means
valuing it, so want-arrows from a pickless agent form alternating paths, and every agent reached lies in $S$.
Want-chains are finite (wanting points to earlier picks), so each ends at an agent whose pick nobody wants. That agent
holds a pick, since a pickless agent would put the chain into $S$. ∎

The TTC session proved the same statement independently as Lemma T5 (`k4/referee/ttc_t5.md`: the same lemma with the
same proof).

### 6.4 What the lemmas give

**Corollary 6.4 (OC₁^max implies TARGET₄) [R, L].** If OC₁^max (§2.5) holds, every 4-limited additive instance has a
complete EFX₀ allocation.

*Proof.* By §2.2, it suffices to treat strict connected $k = 4$ cores. By Lemma 6.2 one of their orders picks a
maximum matching, and OC₁^max gives an EFX₀ completion for it. ∎

The Lean statement is `EFX.OC1Max.target4_of_conjOC1max`, with `EFX.OC1Max.ConjOC1max` a hypothesis (a `Prop`), not
an axiom. It runs through Lemma 6.2 and the machine-checked reductions K4.CORE and K4.TIE.
`EFX.OC1Max.target4_of_conjOC1maxWith` does the same for any move relation. The Lean model has values in
$\mathbb{N}$. The lemmas are `EFX.OC1Max.sdpo` (Lemma 6.1), `EFX.OC1Max.exists_order_maximum` (Lemma 6.2) and
`EFX.OC1Max.max_no_augment`, `EFX.OC1Max.picks_no_junk` (Lemma 6.3). `lean/EFX/OC1MaxExamples.lean` shows the
definitions are not vacuous on the MC2 core of §7.2: the failing order there does not pick a maximum matching, and the
order $3, 4, 0, 1, 2$ picks one with a one-absorber completion. The Lean proof of Lemma 6.2 takes a maximum matching
of largest total value; a Pareto improvement of it would be a maximum matching of larger total value.

**Why Lemma 6.3 matters.** Every known counterexample to OC and OC₁ "for every order" (§7.2) has the same shape.
Pickless agents value only picked goods. They freeze the pick holders, which then cannot take junk, and the pickless
agents are left as the only junk receivers. At a maximum-matching start this pickless pigeonhole cannot form:
pickless agents freeze only agents that value no junk.

**Referee report.** `k4/referee/maxsd.md`: SDPO CORRECT (strictness essential), MAXSD CORRECT (also with tie-breaking),
MAX CORRECT. The referee brute-forced all matchings and all orders on 4,500 strict instances ($n \le 6$) and 2,000
tied ones, and found 0 failures except the expected SD $\ne$ PO under ties. The Lean build result is in Appendix A.
