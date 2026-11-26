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

## 7. Refutations

Every instance below is printed in full. Goods are numbered from 0. "Agent $i$: $g$ ($x$)" means $v_i(g) = x$, and all
other values are 0. Appendix C re-checks each printed claim marked † from the printed data alone.

### 7.1 Value-monotone methods get stuck, at $k = 4$ and at $k = 3$

> **P1.** Every partial EFX₀ allocation that is Pareto-maximal among partial EFX₀ allocations (comparing value
> vectors), and allocates the most goods among those with its value vector, is complete.

If P1 held, no procedure that keeps a partial EFX₀ allocation and never lowers an agent's value could get stuck. That
covers adding goods, envy-cycle rotations, and path moves in which every agent on the path gains.

**Proposition 7.1 (P1 fails at $k = 4$; `k4/sdc.md` §1, ledger K4.SDC.P1) [V] †.** The instance GM4-E, a strict
connected $k = 4$ core with $n = 4$, $m = 7$:

| agent | goods (value) |
|---|---|
| 0 | 0 (3), 2 (10), 4 (6), 6 (2) |
| 1 | 1 (3), 3 (4), 5 (8), 6 (2) |
| 2 | 2 (4), 3 (2), 6 (3) |
| 3 | 4 (2), 5 (4), 6 (3) |

Take $X = (\{0, 4\}, \{1, 3\}, \{2\}, \{5\})$, which leaves good 6 out, with values $(9, 7, 4, 4)$.
- *$X$ is partial EFX₀.* Agents 0 and 1 envy only singletons. Agent 2 sees $\{1, 3\}$, of which it values good 3 at
  $2 \le 4$. Agent 3 sees $\{0, 4\}$, of which it values good 4 at $2 \le 4$.
- *Good 6 fits nowhere.* In $\{0, 4, 6\}$, agent 3 sees $\{4, 6\}$ after removing 0, worth $5 > 4$. In $\{1, 3, 6\}$,
  agent 2 sees $\{3, 6\}$, worth $5 > 4$. In $\{2, 6\}$, agent 0 sees $\{2\}$, worth $10 > 9$. In $\{5, 6\}$, agent 1
  sees $\{5\}$, worth $8 > 7$.
- *Nothing is better.* Exhaustively over all $5^7$ partial allocations, no partial EFX₀ allocation gives every agent at
  least its value in $X$ while either being better for some agent or allocating good 6. Each of the 15 complete EFX₀
  allocations leaves some agent below its value in $X$.

*Verification.* Two programs by the coordinator: `k4/sdc/refute_p1.py`, an independent replay from the definitions,
and `k4/sdc/p1_brute.py` with `p1_replay.py`. A SAT climb (`p1_screen.py`) also finds stuck Pareto maxima on the GM4
family. The referee did not check this item.

**Proposition 7.2 (P1 fails at $k = 3$; Proposition CH-E with $\sigma = 2$, `kgen/charity.md` §5) [V] †.** The
instance S′(2, 3) has $n = 4$, $m = 7$, and every agent values exactly three goods:

| agent | goods (value) | holds in $X$ |
|---|---|---|
| $c_0$ | 5 (10), 0 (6), 4 (6) | {5} |
| $c_1$ | 6 (10), 2 (6), 4 (6) | {6} |
| $s_0$ | 6 (5), 0 (2), 1 (2) | {0, 1} |
| $s_1$ | 5 (5), 2 (2), 3 (2) | {2, 3} |

The state $X$ leaves good 4 out. No partial EFX₀ allocation dominates it, and each of the 58 complete EFX₀
allocations leaves some agent worse off.

*Verification.* `kgen/charity/refute_pm.py` (the session; no SAT, exhaustive over $5^7$) and the coordinator's
`k4/sdc/p1_k3_verify.py` (brute force; attack log, 21:35). The written proof (Proposition CH-E: a Pareto maximum for
every $\sigma \ge 2$ and $k \ge 3$, leaving $\sigma - 1 = \Omega(\sqrt n)$ goods out) is not refereed.

**Consequence.** A correct procedure for TARGET₄ must avoid such states or take steps that lower some agent's value.
Since this happens already at $k = 3$, where complete EFX₀ allocations exist, it does not separate $k = 4$ from
$k = 3$. The $k = 3$ constructions LB⁺ and Draft and Exchange are not value-monotone in this sense: their
intermediate states are pre-allocations or trades, not partial EFX₀ allocations.

### 7.2 "One chain from every order" fails on strict $k = 4$ cores

**Proposition 7.3 (OC₁ and OC fail for some orders; `k4/sdc.md` §31) [V].** With moves = additions, chains and rings
(§2.4):
- **(a) OC₁ fails on a strict connected $k = 4$ core** (B<; $n = 6$, $m = 10$) †:

  | agent | goods (value) |
  |---|---|
  | 0 | 0 (6), 2 (14), 3 (16), 1 (12) |
  | 1 | 6 (4), 4 (18), 5 (12), 9 (28) |
  | 2 | 1 (28), 2 (4), 3 (16), 9 (21) |
  | 3 | 1 (16), 6 (14), 7 (12), 8 (6) |
  | 4 | 3 (28), 6 (8), 9 (24) |
  | 5 | 1 (20), 3 (30), 6 (8), 9 (4) |

  The order $0, 1, \dots, 5$ gives the picks $(3, 9, 1, 6, -, -)$, and the junk is $\{0, 2, 4, 5, 7, 8\}$. The picks
  have no one-absorber EFX₀ completion, and neither has any of the 57 states one move reaches. OC₁ fails for 24 of
  the 720 orders; all 24 give these picks. B> (agent 2's value for good 9 lowered to 19) behaves the same.
- **(b) OC fails, even with the free completion, on a strict connected core in the MC2 class** ($n = 5$, $m = 9$) †:

  | agent | goods (value) |
  |---|---|
  | 0 | 0 (10), 3 (6), 6 (5), 8 (7) |
  | 1 | 1 (10), 4 (6), 7 (5), 6 (7) |
  | 2 | 2 (10), 5 (6), 8 (5), 7 (7) |
  | 3 | 0 (4), 1 (3), 2 (2) |
  | 4 | 0 (2), 1 (4), 2 (3) |

  The order $0, \dots, 4$ gives the picks $(0, 1, 2, -, -)$. There is no EFX₀ completion at all, neither at the picks
  nor after any of the 232 moves. It fails for 12 of the 120 orders.

*Why (b) fails at the picks* (a hand proof; the claim after one move is computational). Agents 3 and 4 hold nothing
and value only the picks 0, 1, 2. So agents 0, 1, 2 are frozen and must hold their picks alone: a pick in a bundle
with another good is threatened by a wanter whose own bundle is worth 0 to it. All six junk goods therefore go to
agents 3 and 4. Each agent $i \le 2$ has a *danger triangle*: any two of its three junk goods outweigh its pick.
- agent 0: $\{3, 6, 8\}$, with $6 + 5 = 11$, $6 + 7 = 13$, $5 + 7 = 12$, all $> 10$;
- agent 1: $\{4, 7, 6\}$;
- agent 2: $\{5, 8, 7\}$.

A bundle of three or more goods may hold at most one good of each triangle. The shared goods 6, 7, 8 pairwise share a
triangle. Splitting six goods between two bundles puts two of them together. If their bundle has three or more goods,
it is threatened. If it is exactly that pair, the other bundle has four goods and contains two goods of a triangle
($\{3, 8\}$, $\{4, 6\}$ or $\{5, 7\}$ for the three pairs). ∎

**Mechanism, and what survives.** In both instances the failing picks match $\nu - 2$ agents, while $\nu = n$. The
pickless agents value only picks, freeze the pick holders, and are left as the only junk receivers, which cannot hold
the danger sets. Lemma 6.3 shows that this cannot happen at a maximum-matching start. On (b), all 50
maximum-matching orders complete at the picks.

Neither instance refutes MD, SD-C or TARGET₄. For B<, the allocation
$(\{3\}, \{9\}, \{1\}, \{6\}, \{2, 4, 7\}, \{0, 5, 8\})$ is EFX₀; it gives both pickless agents three junk goods †.

*Verification.* Found by the TTC session (`claude/k4-ttc`; `attempts/k4-ttc-oc-every-order.md`). Checked by the Hall
session (`k4/oc1_hall.md` §16, §18, `verify_ttc_cex.py`, with SAT and a brute force). Replayed by the coordinator with
code written from the core definition and the move rule, using raw EFX₀, brute-force completions and no SAT:
`k4/sdc/oc1_core_cex_verify.py` and `k4/sdc/oc_mc2_cex_verify.py`, logs in `results/k4_sdc/`. Ledger K4.SDC.OC and
K4.SDC.OC1 are REFUTED with these artifacts. The referee did not check this item.

**Remark (OC₁ at $k = 3$ outside cores; `k4/k3_oc1.md` §9) [V] †.** The same pigeonhole appears at $k = 3$ when agents
have two private goods. Every agent below values its goods $a > b > c$ at $10 > 8 > 7$.

| agent | goods $a, b, c$ |
|---|---|
| 0 | 0, 1, 2 |
| 1 | 0, 1, 2 |
| 2 | 0, 3, 4 |
| 3 | 1, 5, 6 |
| 4 | 2, 7, 8 |

The order $(2, 3, 4, 0, 1)$ gives agents 2, 3, 4 their tops and agents 0, 1 nothing. The six junk goods are the
private pairs of agents 2, 3, 4. No one-absorber completion exists at the picks, nor after any of the 51 chains that
never pass an empty base. Two programs of the $k = 3$ session agree: `k4/k3oc1/oc1_general.py` and the independent
replay `attempts/k4_k3oc1_oc1_cex.py`. Appendix C finds the same, and also that no addition or ring repairs.

The instance is not a core (rule R2 peels agents 2, 3, 4), and two weaker forms hold.
- One chain that passes through an agent holding nothing repairs it: in $3 \to 1 \to 4 \to 0$, agent 3 takes
  $\{5, 6\}$, agent 4 takes $\{7, 8\}$, and agents 1 and 0 receive goods 1 and 2.
- Under the free completion the picks already extend, with two absorbers:
  $(\{3, 5, 7\}, \{4, 6, 8\}, \{0\}, \{1\}, \{2\})$.

So OC₁ "for every instance", as literally stated, is false at $k = 3$. What the conjectures of §11 need is the core
form.

### 7.3 One chain fails at $k = 5$, even from maximum-matching starts

**Proposition 7.4 (PW5; `k4/ksens.md` §1) [R] †.** The following instance has $n = 5$, $m = 9$, and is 5-limited.
Here $p_j = j - 1$ for $j = 1, 2, 3$, $q_1 = 3$, $q_2 = 4$, and the pool is $D = \{5, 6, 7, 8\}$.

| agent | goods (value) |
|---|---|
| $x_1 = 0$ | $p_1 = 0$ (10); 5 (9), 6 (8), 7 (7), 8 (6) |
| $x_2 = 1$ | $p_2 = 1$ (10); 5 (9), 6 (8), 7 (7), 8 (6) |
| $x_3 = 2$ | $p_3 = 2$ (10); 5 (9), 6 (8), 7 (7), 8 (6) |
| $w_1 = 3$ | 0 (6), 1 (4), 2 (2), $q_1 = 3$ (1) |
| $w_2 = 4$ | 0 (6), 1 (4), 2 (2), $q_2 = 4$ (1) |

From the order $\pi = (x_1, x_2, x_3, w_1, w_2)$, neither the picks nor any state reached by one improving chain or
one addition has a complete EFX₀ completion, even a free one. Since every agent picks, this is a maximum-matching
start. Hence OC and OC₁ fail at $k = 5$, and so at every $k \ge 5$; so do OC^max and OC₁^max.

*Proof.* The picks are $p_1, p_2, p_3, q_1, q_2$, and the junk is $D$. Every $x_j$ is frozen, since both wanters want
every $p_j$. Every pair of $D$ is worth at least $6 + 7 = 13 > 10$ to every $x_j$, and every single good of $D$ less
than 10. Let $X$ be a complete EFX₀ allocation that contains the bases of a state reached by at most one chain or
addition.
1. *Who can gain.*
   - An $x$ values only its own $p$ and $D$, and no other agent's base contains its $p$. So on a chain an $x$ gains
     only if its new base holds at least two goods of $D$; in an addition it keeps $p_x$ and adds goods of $D$.
   - A wanter gains only by receiving some $p_j$, since it values nothing else above its $q$, and no junk at all.
   - Every agent's base is nonempty.
2. *A frozen $x$ holds its pick alone.* If an off-chain wanter $w$ holds no $p$, then $v_w(X_w) = 1 < v_w(p_j)$ for
   every $j$. So every $x_j$ that still holds $p_j$ has $X_{x_j} = \{p_j\}$, and then no bundle of three or more goods
   may contain two goods of $D$.
3. *Let $S$ be the set of $x$'s on the chain.* On a chain each $x$ in $S$ takes two goods of $D$, so $|S| \le 2$.
   - $|S| = 0$: no wanter can gain, so there is no chain, and an addition is by an $x$ (the case $|S| = 1$, $t = 0$
     below) or by nobody. At the picks, the $x$'s hold their picks alone (step 2), and the four goods of $D$ go to the
     two wanters' bundles. Some bundle then has at least three goods, two of them in $D$. ✗
   - $|S| = 2$: the third $x$ holds no good of $D$ and has value 10. The member of $S$ that is not $x_0$ holds a
     nonempty received base plus its pair, so at least three goods, two of them in $D$. ✗
   - $|S| = 1$, $S = \{x_a\}$, addition: $x_a$ keeps $p_a$ and adds goods of $D$. Both wanters hold no $p$, so they want
     $p_a$ and are threatened by $X_{x_a}$ minus a good of $D$. ✗
   - $|S| = 1$, chain: exactly one wanter $w$ receives $p_a$. The other wanter $w'$ cannot gain, so it is off the
     chain and holds no $p$, and by step 2 the other two $x$'s hold their picks alone. If $x_a \ne x_0$, then $x_a$
     holds a received base plus two goods of $D$. ✗ If $x_a = x_0$, its bundle is exactly two goods of $D$ by step 2.
     $w$ holds $p_a$, which $w'$ wants, so $X_w = \{p_a\}$, and the other two goods of $D$ can only go to $w'$, whose
     bundle then has at least three goods with two of $D$. ✗ ∎

Every case also holds with the free completion, so the proof covers OC as well as OC₁.

*Additions as replacements, and rings.* The written proof treats a one-agent move as an addition. The referee's
exhaustive enumeration also covers one-agent replacements $H_0 \subseteq J \cup B_{x_0}$: none of the 78 such states
extends. The coordinator's check `k4/sdc/pw5_max_check.py` also includes rings: none of the 555 states one move
reaches has a free completion [V].

**Referee report.** `k4/referee/ksens.md`: CORRECT. The referee enumerated all $5^9$ allocations (186 are EFX₀) and
every chain and one-agent move from all 19 distinct starts. The only failing start is $\pi$'s. The 12 orders that put
the three $x$'s before the two wanters produce it.

**Where $k \le 4$ enters.** One repair of a frozen agent spends two of its junk goods. A frozen agent with $k$
relevant goods has at most $k - 1$ junk goods, so at most $k - 3$ are left. At $k = 4$ that is one good, which is
never a danger set (I2). At $k = 5$ two goods are left, still a danger set for the agents sharing the pool, and one
chain cannot repair a second agent. The general statement is this.

**Lemma 7.5 (PL, pool leftover; `k4/ksens.md`) [R].** Let $Y = \mathrm{SD}(\pi)$ with junk $J$. Let $x$ be an agent
with pick $y_x$ and $|R_x| \le k$, and let $H \subseteq J \cap R_x$ with $v_x(H) > v_x(y_x)$ (a junk danger set of
$x$, used as its improving set). Then:
- (a) $|H| \ge 2$, and $x$ values at most $k - 3$ goods of $J \setminus H$;
- (b) if $|R_x| \le 4$, $x$ values at most one good of $J \setminus H$, worth at most $v_x(y_x) < v_x(H)$, so once
  $x$'s base contains $H$, no subset of $J \setminus H$ is a danger set of $x$;
- (c) if $z$ is any agent with a pick, $|R_z| \le 4$, that values at least two goods of $H$, then $z$ values at most
  one good of $J \setminus H$, worth at most $v_z(y_z)$; so while $z$ holds $y_z$, no subset of $J \setminus H$ is a
  danger set of $z$;
- (d) for every $k \ge 5$ the bound $k - 3 \ge 2$ of (a) is attained, and PW5 shows it is fatal for one chain.

*Proof.* Every $g \in J \cap R_x$ was available when $x$ picked, so $v_x(g) \le v_x(y_x)$ (I2). A single junk good is
therefore not worth more than $y_x$, so $|H| \ge 2$. Since $y_x \notin J$, $|J \cap R_x| \le |R_x| - 1 \le k - 1$, which
leaves at most $k - 3$ goods outside $H$. This proves (a). (b) is (a) with $k = 4$, together with (I2). For (c),
$|J \cap R_z| \le 3$ and two of these goods lie in $H$; the remaining one is worth at most $v_z(y_z)$ by (I2). (d) is
Proposition 7.4. ∎

PL covers only the old junk $J \setminus H$. Released picks, agents that share only one good with $H$, and danger
sets that use another agent's pick are not covered; these are the parts a $k = 4$ proof still has to handle
(`k4/ksens.md`, "What PL does not cover").

**Lemma 7.6 (PWk(a), the PW family at $k \le 4$; `k4/ksens.md` §7) [R′].** In the family PW($f, W, r$), $f$ frozen
agents $x_j$ value their pick $p_j$ at $P = 20$ and each good of a shared pool $D$, $|D| = r \le 10$, at less than $P$
(19, 18, …), and every pair of $D$ above $P$. $W$ wanters $w_i$ each value every $p_j$ above their own $q_i$, with the
same ranking $p_1 > \dots > p_f$. The order is $x_1, \dots, x_f, w_1, \dots, w_W$. If $r \le 3$, the start needs at
most one chain and has a one-absorber completion after it, for every $f$ and $W$. In particular PW never breaks OC₁
at $k \le 4$.

*Proof.* For $W = 0$ no agent is frozen, and the picks complete with one owner by Theorem DT⁺ of `k4/sdc.md` §6
(every agent then has at most four goods). For $W \ge 1$ and $r \le 1$, the pool good goes to $w_1$. Let $W \ge 1$ and
$r \in \{2, 3\}$. Use the chain $x_1 \to w_1$: $x_1$ takes two pool goods $d_1, d_2$, and $w_1$ takes $p_1$ and
releases $q_1$. Complete as follows: $x_1$ keeps $\{d_1, d_2\}$, $w_1$ keeps $\{p_1\}$, every other agent keeps its
pick, and the leftovers $q_1$ and (if $r = 3$) $d_3$ go as follows.

| case | $q_1$ to | $d_3$ to | absorber |
|---|---|---|---|
| $W \ge 2$ | $w_2$ | $w_2$ | $w_2$, bundle $\{q_2, q_1, d_3\}$ |
| $W = 1$, $f \ge 2$ | $x_2$, bundle $\{p_2, q_1\}$ | $w_1$, bundle $\{p_1, d_3\}$ | none |
| $W = 1$, $f = 1$ | $x_1$ | $x_1$ | $x_1$ (two agents only) |

The EFX₀ check is a short case analysis in `k4/ksens.md` §7. Two of its points:
- Each $x_j$ ($j \ge 2$) has value $P$ and sees at most one pool good outside $x_1$'s pair.
- $w_1$, holding its top pick $p_1$, sees in $\{p_2, q_1\}$ after removing a good only $p_2$ or $q_1$, each below
  $p_1$. ∎

*The fix.* The referee showed that the first version of this proof used, for $W = 1$, $f \ge 2$, $r = 3$, the
completion "absorber $x_2$ with $\{p_2, d_3, q_1\}$". That needs $v_{w_1}(p_2) + v_{w_1}(q_1) \le v_{w_1}(p_1)$, which
the family's description does not guarantee: it fails, for example, with wanter values $(12, 8, 5)$. The completion in
the table is the referee's fix; it needs no absorber. The session applied it, and it is the text above. Referee
report: `k4/referee/ksens.md` §5 (also Lemma PL: CORRECT). Checks: 60 clean configurations and 3,000 random value
assignments of the family's shape, all EFX₀.

### 7.4 One round of disjoint chains fails at $k = 5$

**Proposition 7.7 (RD5; `k4/ksens.md` §6) [V] †.** The following instance has $n = 4$, $m = 7$, strict values, and
only agent 0 has five goods.

| agent | goods (value) |
|---|---|
| 0 | 1 (57), 3 (44), 5 (33), 0 (26), 4 (24) |
| 1 | 1 (12), 2 (11), 3 (6) |
| 2 | 1 (9), 2 (8), 3 (6), 4 (1) |
| 3 | 2 (53), 5 (47), 0 (36), 6 (4) |

The order $(0, 3, 1, 2)$ gives agents 0, 3, 1, 2 the picks 1, 2, 3, 4, and the junk is $\{0, 5, 6\}$. Every agent
picks, so this is a maximum-matching start. None of the 50 states one round reaches (30 of them by one chain) has a
completion, free or with one absorber. Two sequential chains repair it.

*Mechanism.* Agents 0 and 3 are frozen, and they share the junk pair $\{0, 5\}$, a danger set for both
($26 + 33 > 57$, $36 + 47 > 53$). Agent 3 gains only by taking $\{0, 5\}$, so agent 0 must repair itself without it.
Its other improving sets need two other agents' picks (goods 3 and 4), and a chain or a round gives an agent at most
one other agent's pick. Five goods are needed: the pick, the shared pair, and two foreign picks. Dropping any one of
agent 0's goods restores one round.

*Verification.* Two programs of the $k$-sensitivity session: `k4/ksens/ocsat.py` (SAT, with rounds) and
`k4/ksens/brute.py` (every round enumerated from the definition, every allocation against the raw EFX₀ definition).
A third implementation, `ocseq.py` with rounds, agrees with both on 1,364 start–completion pairs
(`xcheck_rounds.log`). Log `results/k4_ksens/refute_rd_k5.log`. Not refereed.

Together, Propositions 7.4 and 7.7 show that the one-move and one-round forms are $k \le 4$ statements. Every
statement of §11.1 must use $k \le 4$ somewhere.

## 8. The $k$-ladder (mostly evidence)

Source: `k4/ksens.md` §4, §7, §8 (branch `claude/k4-ksens`), with the $k = 3$ entries from `k4/k3_oc1.md` (branch
`claude/k4-k3-oc1`). **This section is mostly evidence.** Only the cells marked [R] or [V] are established; "holds"
means "no failure on the data", never "proved".

How much repair do SD picks need, as a function of $k$? A *start* is the SD picks of an order. Each row asks for a
complete EFX₀ completion after the stated repair, from every start of the stated kind.

| statement | $k \le 2$ | $k = 3$ | $k = 4$ | first failure | smallest counterexample known |
|---|---|---|---|---|---|
| no repair: the picks extend | proved (K3.SD2, Lean) | **fails** [V] | fails | $k = 3$ | $n = 2$, $m = 4$ (below) |
| one chain (OC₁, OC) | (no chain needed) | proved for R1-compatible orders in DE's core case [R] (§9); holds on all cores tested [E]; fails outside cores [V] (§7.2) | holds [E] | **$k = 5$** | RD5, $n = 4$, $m = 7$ [V]; PW5, $n = 5$, $m = 9$ [R] |
| one chain from maximum-matching starts (OC₁^max) | | | holds [E] | **$k = 5$** | PW5 [R]; RD5 [V] |
| one chain from R1-priority starts, or from the need-2 neediest-first start | | | holds [E] | $k = 6$ | PWR1-6, NF2-6, $n = 6$, $m = 11$ [V] |
| one chain from LB₄ʳ's Phase 1 (need-2, R1) | | | holds [E] | none found | |
| $c$ chains in sequence | $c = 0$ | $c = 1$ [E] | $c = 1$ [E] | $k = 2c + 3$ ($c \le 3$) | PW($c+2$, $c+1$, $2c+2$); $c = 1$ [R], $c = 2, 3$ one SAT encoding [E] |
| one round of disjoint chains (RD, RD₁) | | | holds [E] | **$k = 5$** | RD5 [V] |
| two rounds (RD²), also from maximum-matching starts | | | holds [E] | none found | (§11.6) |
| SD-C (some order, no repair) | proved | holds [E] | holds [E] | none found ($k \le 8$) | |
| MD (every start value-dominated) | proved for strict values (K3.SD2 with Lemma 6.1) | open (TARGET₃ is the empty matching only) | holds [E] | none found ($k \le 8$) | |

Notes on the cells.
- *The picks extend at $k \le 2$.* Serial dictatorship, with the last agent taking all leftovers, is EFX₀ when every
  agent values at most two goods (ledger K3.SD2, Lean `EFX.Inst.sdRun_efx0`).
- *The $k = 3$ failure of "no repair"* (`results/k4_ksens/k3_zero.log`; SAT and brute force) †. Agent 0 values goods
  0, 1, 2 at 12, 13, 3, and agent 1 values goods 1, 2, 3 at 19, 2, 5. From the order (0, 1) the picks are 1 and 3, and
  the junk is $\{0, 2\}$. Agent 1 wants good 1, so agent 0 must hold it alone. Then both junk goods go to agent 1,
  and agent 0 sees $\{0, 2\}$, worth $15 > 13$. One chain repairs it.
- *$c$ chains.* In PW($f, W, r$) each chain repairs only its head, spends two pool goods and uses up one wanter.
  After $c$ chains, $r - 2c$ pool goods remain and only $W - c$ wanters can take one each. So $c$ chains fail when
  $r - 2c > W - c \ge 1$, which with $r = k - 1$ needs $k \ge 2c + 3$. The least number of chains in the family is
  $\lfloor (k-1)/2 \rfloor$, computed for $k = 5, \dots, 9$ by one SAT encoding (`ocseq.py`), and confirmed by a
  breadth-first search for $k = 5, 6$ [E]. The general count is a heuristic, not a proof.
- *Orders.* The orders where one chain first fails depend on the order class: every order fails at $k = 5$, and
  R1-priority and need-2 neediest-first orders fail at $k = 6$ (each case checked by two SAT encodings and a SAT-free
  enumeration, `refute_oc1_r1.log`). LB₄ʳ's Phase 1 order and "some order" (SD-C) have no counterexample at any $k$
  tested.
- *What fails at $k = 5$ beyond these rows.* The conclusions of Theorem DT, Lemma GDT and Theorem DT₁ (`k4/sdc.md` §6,
  §30), which hold at $k = 4$, fail at $k = 5$ [V]. The instance DT5 has $n = 2$, $m = 6$: agent 0 values goods 0
  (100) and 2, 3, 4, 5 (91, 92, 93, 94), and agent 1 values goods 1 (100) and 2, 3, 4, 5 (94, 93, 92, 91). The tops
  are distinct, and yet the picks have no one-absorber completion †. The instance DT1-5 has $n = 3$, $m = 8$
  (`k4/ksens.md` §3).

**The $k$-dependence in one count** (Lemma 7.5). A frozen agent's junk danger sets live in its at most $k - 1$ junk
goods, and a repair spends two of them.
- $k \le 2$: no danger set, no chain.
- $k = 3$: a danger pair, one chain, nothing left.
- $k = 4$: one good left, never a danger set; one chain suffices on all data.
- $k = 5$: two goods left, a danger set for the agents sharing the pool (PW5); or the repair needs two foreign picks
  (RD5).

The $k \le 4$ inputs a proof of OC₁^max can use are these:
- Lemma 7.5 (b), (c);
- Lemma 7.6;
- the one-agent counts in Theorem DT's (F4) and in DT₁'s step 3 (`k4/sdc.md` §6, §30);
- RD5's five-good requirement.

**Unrestricted $k$** (`k4/ksens.md` §8, [E]). Lift PW5 to full valuations, with every agent valuing every good
(strict, positive, $k = m = 9$): one chain still fails, and one round repairs. So PW's mechanism does not need zero
values. The same lift of RD5 needs only one round. With every good valued, no start within $n \le 5$, $m \le 9$
needed two rounds (climbs and random profiles). Zero values make the problem harder for rounds, not easier.

## 9. Three relevant goods: one chain from R1-compatible orders

Source: `k4/k3_oc1.md` §1–§3 (branch `claude/k4-k3-oc1`). Refereed against `949718a`; §2–§3 are unchanged at the head
`48bcf05`. The proofs build on construction LB⁺ (`proofs/lb_last_step.md`, machine-checked as `EFX.target`) and on
Draft and Exchange (DE; `paper/k3-simple`, [Lin-k3s]).

TARGET₃ is known. The question here is whether its constructions have the OC₁ shape: one-absorber completions of SD
picks, after at most one improving chain. A positive answer at $k = 3$ is the base case for OC₁^max at $k = 4$.

### 9.1 Setting

**DE's core case.** Every agent values exactly three goods, $a_i > b_i > c_i$, strictly balanced ($a_i < b_i + c_i$).
Goods valued by nobody (*dead goods*) are allowed. Every comparison of subset sums of one agent's goods is then fixed
by its ranking ($0 < c < b < a < b + c < a + c < a + b < a + b + c$; PROMPT.md, L5), so EFX₀ depends only on the
rankings. This is narrower than "every 3-limited instance": agents with fewer than three goods and top-heavy agents
are outside it. The peeling rules reduce TARGET₃ to cores, which lie in this case.

**DE states.** Each agent holds nothing, one of its goods, or its pair $\{b, c\}$.
- $U$ is the set of pair holders, and $J$ the junk.
- A state is **valid** if every good some agent wants is held alone. (An agent wants a good it ranks above its
  holding; pair holders want nothing.)
- The **terminals** $T$ are the agents outside $U$ whose holding nobody wants (DE's free agents). The other agents
  outside $U$ are **frozen**.
- An *owner* $o$ is a terminal or a pair holder.
- The **exposed** agents $E_o$ are the agents $x \notin U$, $x \ne o$, that hold exactly $a_x$ and have
  $b_x, c_x \in J \cup \mathrm{base}(o)$. For them, $\pi_x = \{b_x, c_x\} \cap J$.
- $h(\cdot)$ is the least size of a set of junk goods meeting every $\pi_x$ of the agents in question.

The *draft* of an order is its SD outcome. It is a valid DE state with no pair holders.

### 9.2 Lemmas

**Lemma 9.1 (simple completion; `k4/k3_oc1.md` §2, Lemma 1) [R].** A valid DE state has a one-absorber completion if
one of the following holds:
- (a) $|J| \le |T|$: every junk good goes to a different terminal, and there is no owner;
- (b) some owner $o$ has no $x \in E_o$ with $\{b_x, c_x\} \subseteq \mathrm{base}(o)$, and
  $h(E_o) \le |T| - [o \in T]$: a hitting set goes to the other terminals, one good each, and $o$ takes the rest;
- (c) some terminal $o$ holds nothing and $|J| \le |T| + 1$: $o$ ends with at most two goods.

*Proof.* Each completion here gives the terminals other than the owner at most one junk good each, and the frozen
agents and the other pair holders nothing. That is LB⁺'s completion with caps at most LB⁺'s. Theorem 1′ of
`proofs/lb_last_step.md` covers every completion of this kind, since lowering caps only removes completions; so it
applies to (a) and (b). Its proof also shows that in a valid state a bundle of at most two goods threatens nobody,
and in (c) every bundle has at most two goods. ∎

**Lemma 9.2 (the excess ω; Lemma 2) [R].** In a DE state, $\omega := |J| - |T| = (m - 2n) + e + \nu$. Here $e$ is the
number of agents holding nothing and $\nu$ the number of wanted goods. A DE trade raises neither $e$ nor $\nu$, so it
never raises $\omega$.

*Proof.* Count goods and agents: $m = 2|U| + (n - |U| - e) + |J|$, and $n = |U| + \nu + |T|$, since in a valid state
every wanted good is the single good of exactly one frozen agent. Subtract. A trade gives goods only to agents that
had one or none, so $e$ does not grow. The proof of DE's Lemma stay ([Lin-k3s]) shows that a good wanted after a trade
was wanted before, by the same agent. ∎

**Lemma 9.3 (self-service; Lemma 3, corrected) [R′].** Let $o$ be an owner such that no $x \in E_o$ has
$\{b_x, c_x\} \subseteq \mathrm{base}(o)$. This holds automatically when $o$ is a terminal. Write $F$ for the frozen
agents. Then condition (b) of Lemma 9.1 holds for $o$ whenever $h(E_o \cap F) \le |T \setminus E_o| - [o \in T]$. In
particular, every *satisfied* state, in which every agent holds its top or its pair, passes Lemma 9.1.

*Proof.* An exposed terminal $x$ takes a good of $\pi_x$ into its own slot; $\pi_x \ne \emptyset$ once the pair
condition holds. So the hitting set can be one good per exposed terminal, plus a hitting set of the frozen exposed
agents placed in the other terminals. The count is
$|E_o \cap T| + h(E_o \cap F) \le |T| - [o \in T]$. In a satisfied state every agent outside $U$ is a terminal, so a
terminal owner works. If $T = \emptyset$, every pair-holder owner has $E_o = \emptyset$. ∎

*The fix.* The source states Lemma 3 without the pair condition: "if every exposed agent of an owner $o$ is a
terminal, (b) holds for $o$". The referee showed this is false when $o$ is a pair holder
(`k4/referee/k3_oc1.md` §3). Smallest instance: two agents with the ranking $a \succ b \succ c$ and a dead good $d$;
$x$ holds $\{a\}$ and $o$ holds $\{b, c\}$. Then $E_o = \{x\}$, $x$ is a terminal, and $\{b_x, c_x\} = \mathrm{base}(o)$,
so (b) fails for $o$. Indeed $X_o = \{b, c, d\}$ gives $v_x(X_o \setminus d) = b + c > a$. The state still completes,
by (a). The corrected hypothesis never failed on 128,377 test cases. The referee checked that no later claim depends on
the defect: where Lemma 3 is used, the owners are terminals, or pair holders whose pair no exposed agent shares.

### 9.3 The theorems

The *need order* of a draft puts every agent after the holders of the goods it ranks above its pick. Every linear
extension of it gives the same draft. The draft is **R1-compatible** if some linear extension respects R1 priority:
whenever an unprocessed agent has lost a good, the next agent is such an agent. Then the draft is the Phase 1 output of
an LB⁺ run (`proofs/lb_last_step.md` §1, insertion choices included). Every R1-priority order is R1-compatible.

**Theorem 9.4 (R1C; `k4/k3_oc1.md` §3) [R].** In DE's core case, let the draft of $\pi$ be R1-compatible. After LB's
upgrades (a $b$-holder takes its junk $c$), the draft has a one-absorber completion, or it has one after a single DE
trade. That trade is LB⁺'s rotation from $k^*$ to $r$: a DE chain if $\{b_{k^*}, c_{k^*}\} \subseteq J$, and a ring with
one pair arrow $r \to k^*$ otherwise. Each upgraded agent's good $c$ counts as its one junk good, so this is OC₁ for
$\pi$.

*Proof.* Run LB⁺ (`proofs/lb_last_step.md`, Theorems A, B, C) with every cap equal to one, terminals with no pick
included.
- *Lemma 1 there* holds for any caps not above LB's.
- *Theorem A's count* (the owner $r$, the last-processed agent that is not upgraded) uses only two facts: each
  terminal $\tau(x)$ assigned to an exposed agent has cap at least 1, and $S - \mathrm{cap}(r)$ is the number of slots
  outside $r$.
- *Theorem B's count* (g) (the rotation in LB⁺'s bad case) uses only $\mathrm{cap}' \ge 1$ for the same terminals.

With unit caps the output gives every agent but the owner at most one junk good, so it is a one-absorber completion.
LB⁺'s rotation moves every agent of a need chain from $k^*$ to $r$ up one step, and gives $k^*$ its pair from
$J \cup \{Y_r\}$. ∎

The referee checked that LB⁺'s rotation is an OC₁ chain applied to the picks.
- No upgraded agent lies on the need chain (LB⁺'s (A4)).
- $H_0 = \{b_{k^*}, c_{k^*}\} \subseteq J \cup \{Y_r\}$, as a chain's head set must be.
- Every agent on the chain strictly gains: $b + c > a$, and each agent receives a good it ranks above its own.

**Theorem 9.5 (B\*; LB⁺'s rotation for every order; `k4/k3_oc1.md` §3) [R].** In DE's core case, take any order and
its draft after LB's maximal upgrades. Let $t$ be a terminal with $h(E_t) = |T|$ (deficit one for owner $t$), and let
$k \in E_t$ satisfy:
- (i) $k$ is frozen;
- (ii) there is a need chain $k = x_0, x_1, \dots, x_s = t$ ($s \ge 1$);
- (iii) no other agent of $E_t$ has the pair $\{b_k, c_k\}$;
- (iv) the sets $\{b_x, c_x\} \setminus \{b_k, c_k\}$, for $x \in E_t \setminus \{k\}$, have a hitting set of at most
  $|T| - 1$ goods.

Rotate along the chain: each $x_i$ ($i \ge 1$) takes $Y_{x_{i-1}}$, $k$ takes $b_k$ and $c_k$, and $t$'s pick, if any,
is released. The result has a one-absorber completion, with no owner if $|J'| \le |T'|$ and with owner $k$ otherwise.

*Proof.* `proofs/lb_last_step.md` §5 with $r$ replaced by $t$. Blocks are never used, so the statement holds for every
order. The steps are written out in `k4/k3_oc1.md` §3 and re-derived in `k4/referee/k3_oc1.md` §5. ∎

**Scope and coverage.** Theorem 9.4 is about DE's core case, not every 3-limited instance (§7.2, Remark). On the
session's logs it covers 4,608 of 18,569 hard drafts. Theorem 9.5 covers 8,075 of 14,138 exact-hard drafts with
$n \le 6$. The rest are open: drafts whose least deficit is 2, or where exposed agents share junk goods
(`k4/k3_oc1.md` §6). The candidate statement for every order (Theorem candidate OT, one DE trade of least $\omega$) holds
on 273,724,272 starts, exhaustively over every core with $3 \le n \le 5$ [E].

**Referee report.** `k4/referee/k3_oc1.md`. The verdicts are:
- Lemmas 9.1 and 9.2: CORRECT;
- Lemma 9.3: CORRECT WITH FIXES (applied above);
- Theorem 9.4: CORRECT, with the scope statement above;
- Theorem 9.5: CORRECT.

The referee ran LB⁺ with unit caps on every R1-compatible order of exhaustive $n = 3$ data and random data up to
$n = 6$ (about 735,000 runs). Every completion was EFX₀ with one absorber, and an independent brute force over OC₁
agreed.

## 10. Ordinary EFX for 4-limited instances: a reconstruction of Viswanathan–Mehta

Source: `k4/vm.md` §1, §2, §8 (branch `claude/k4-vm`). Refereed against `7a78df6`; these sections are unchanged at the
head `0595a29`.

**What this is.** Viswanathan and Mehta [VM] announce, in a three-page extended abstract, that *ordinary* EFX
allocations exist when every agent values at most four goods. The abstract describes the algorithm in about 25 lines
and asserts its key step ("we are able to prove that … there will be a source") without proof; it points to no full
version. This section proves a reconstruction of that algorithm. It is a reconstruction of a published claim, not an
independent result:
- one reading choice (G1) departs from the literal text, and the literal text is wrong without it;
- whether this is the authors' intended algorithm cannot be checked from the source.

**It says nothing about EFX₀ or TARGET₄.** In ordinary EFX only goods the envier values positively may be removed, and
the algorithm gives goods valued by nobody to an arbitrary agent. The algorithm is not EFX₀ (`k4/vm.md` §5).

### 10.1 The algorithm VM (main reading)

Fix for each agent $i$ a ranking $r_i(1) > r_i(2) > \dots$ of $R_i$ ($|R_i| \le 4$) by value, with ties by good index.
The $k$-th value graph $G_k(S, T)$ has an edge $(i, r_i(k))$ whenever $r_i(k) \in T$. Each agent has at most one edge,
so a maximum matching of $G_k$ gives each claimed good to one of its claimants; which one is a free choice.
1. **Phase I.** $A = \{i : v_i(r_i(1)) > v_i(r_i(2)) + v_i(r_i(3))\}$ (missing goods count 0). Each good that is the
   top of some agent of $A$ goes to one of them. Only the **matched** agents of $A$ (the set $W$) leave the remaining
   agents $N^r$. This is correction (G1); the abstract says "remove $A$ from $N^r$".
2. **Phase II.** For $k = 1, 2, 3, 4$, each remaining good that is $r_i(k)$ for some $i \in N^r$ goes to one such $i$,
   and the matched agents leave $N^r$. $N_k$ is the set of agents matched at step $k$.
3. **Phase III**, in this order: (a) each $N_3$ agent may get its 4th choice; (b) each $N_2$ agent may get its 3rd
   choice, and those that do form $N_2^r$; (c) each remaining $N_2$ agent may get its 4th choice. Each step is a
   maximum matching of the same kind.
4. **EFX-graph step.** While some unassigned good $j$ is valued by someone, give $j$ to a source of the EFX graph
   $G_{\mathrm{efx}}(j, S, X)$, with node set $S = W \cup N_1 \cup N_2^r$.
   - The nodes are the agents of $S$ that value $j$.
   - The graph has an edge $i \to i'$ iff $v_i(X_i) < v_i((X_{i'} \cup \{j\}) \setminus \{j'\})$ for some
     $j' \in X_{i'} \cup \{j\}$ with $v_i(j') > 0$.
5. **Junk.** Goods valued by nobody go to any agent.

The Phase-I winners $W$ count as $N_1$ for the node set (reading G2), and "$k$-th ranked" means rank in all of $R_i$
(reading G3). `k4/vm.md` §3 lists all twelve gaps of the abstract and tests every reading.

### 10.2 The theorem

Write $\mathrm{st}(i) = 0$ for $i \in W$, $\mathrm{st}(i) = k$ for $i \in N_k$, and $\mathrm{st}(i) = \infty$ for the
agents left in $N^r$. For $i \in W \cup N_1$ let $a_i = r_i(1)$ and $L_i = R_i \setminus \{a_i\}$.

**Theorem 10.1 (VM; `k4/vm.md` §8) [R].** If every agent values at most four goods, every run of VM (any resolution of
its choice points) ends with a complete ordinary-EFX allocation. At every EFX-graph step the graph is acyclic, every
directed path in it has at most two edges, and so it has a source.

*Proof.*

**Fact 0.** Agent $i$ EFX-envies a bundle $B$ (ordinary EFX) iff $|B \cap R_i| \ge 2$ and
$v_i(B \cap R_i) - \min_{h \in B \cap R_i} v_i(h) > v_i(X_i)$. Indeed, removing a good $h$ with $v_i(h) > 0$ leaves
$v_i(B \cap R_i) - v_i(h)$, and if $B \cap R_i$ is a single good its removal leaves 0.

**Lemma S (saturation).** After step $k$ of Phase II, every agent $i$ still in $N^r$ has $r_i(1), \dots, r_i(k)$
assigned. In particular:
- every good valued by an agent of $N_4 \cup N^r$ is assigned after Phase II;
- for $i \in N_k$, the goods $r_i(j)$ with $j < k$ are held by agents with $\mathrm{st} \le j$.

Indeed, at step $j$ an agent $i \in N^r$ has an edge to $r_i(j)$ if that good is unassigned, and every good with an
edge is matched. Holders never change.

**Lemma S′.** After Phase III (a) every $N_3$ agent's $r(4)$ is assigned. After (b) every $N_2$ agent's $r(3)$ is
assigned. After (c) every agent of $N_2 \setminus N_2^r$ has its $r(4)$ assigned. The proof is the same.

*Step 1 (Phase II).* All bundles are singletons, so the allocation is EFX by Fact 0.

*Step 2 (Phase III keeps EFX).* In each of (a), (b), (c), a bundle $\{y_s\}$ with $y_s = r_s(\mathrm{st}(s))$ becomes
$\{y_s, g\}$, with $g = r_s(3)$ or $r_s(4)$ previously unassigned. By Fact 0, an agent $i \ne s$ EFX-envies
$\{y_s, g\}$ only if it values both goods and $\max(v_i(y_s), v_i(g)) > v_i(X_i)$. That never happens:
- $i \in W \cup N_1$: $v_i(X_i) \ge v_i(a_i)$, which is at least every single good.
- $i \in N_4 \cup N^r$: all of $R_i$ was assigned after Phase II (Lemma S), and $g$ was not.
- $i \in N_3$: $r_i(1), r_i(2)$ are held by agents with $\mathrm{st} \le 2$. In (a), $y_s$ is held by $s$ with
  $\mathrm{st}(s) = 3$, so $y_s \notin \{r_i(1), r_i(2)\}$, and $y_s \neq r_i(3)$, which $i$ holds. So a valued $y_s$
  is $r_i(4)$, and so is a valued $g$; they cannot both be. In (b) and (c), $r_i(4)$ is already assigned (Lemma S′),
  so $i$ does not value $g$.
- $i \in N_2$: $y_s \ne r_i(1)$ (held by an agent with $\mathrm{st} \le 1$, while $\mathrm{st}(s) \ge 2$),
  $y_s \neq r_i(2)$, and $g \notin \{r_i(1), r_i(2)\}$. So
  $\max(v_i(y_s), v_i(g)) \le v_i(r_i(3)) \le v_i(r_i(2)) \le v_i(X_i)$.

Every other bundle is unchanged, and the receivers' values only rise. The case $i \in N_3$ uses that Phase III serves
$N_3$ before $N_2$, which is the abstract's order. With $N_2$ served first, the referee found EFX failures (mutation
`n2first`).

*Step 3 (only $S$ values unassigned goods).* After Phase III every agent valuing an unassigned good is in $S$:
- for $N_4 \cup N^r$, by Lemma S;
- for $N_3$: $r(1), r(2)$ are assigned, $r(3)$ is held, and $r(4)$ is assigned (Lemma S′);
- for $N_2 \setminus N_2^r$: $r(1)$ is assigned, $r(2)$ is held, and $r(3), r(4)$ are assigned (Lemma S′);
- unmatched agents of $A$ entered Phase II (G1), so they lie in one of these groups.

The claim persists as the set of unassigned goods shrinks.

*Step 4 (bundles in $S$).* Before the EFX-graph steps, an agent of $W \cup N_1$ holds $\{a_i\}$ and an agent of
$N_2^r$ holds $\{r_i(2), r_i(3)\}$. A good placed by an EFX-graph step goes to a node, which values it. So
$X_i \subseteq R_i$ for every $i \in S$ throughout.

*Step 5 (out-edges).* Fix $j$, and let $B = X_{i'} \cup \{j\}$ for a node $i' \ne i$.
- (i) *$W$ has no out-edges.* For $i \in W$, $a_i \in X_i$, so $B \cap R_i \subseteq L_i$, and for $T \subseteq L_i$,
  $v_i(T) - \min_T v_i \le v_i(r_i(2)) + v_i(r_i(3)) < v_i(a_i) \le v_i(X_i)$, since $i \in A$.
- (ii) *Out-edges from $N_1$.* If $i \in N_1$ has an edge $i \to i'$, then $T = B \cap R_i \subseteq L_i$. If
  $|T| \le 2$, $v_i(T) - \min_T v_i$ is at most one good's value, hence at most $v_i(a_i)$. So $T = L_i$ has three
  goods, $|R_i| = 4$, $X_i = \{a_i\}$, and since $j \in T$, two goods of $L_i$ lie in $X_{i'}$, so $|X_{i'}| \ge 2$.
- (iii) *An $N_1$ agent with at least two goods has no out-edge*, by (ii).
- (iv) *Out-edges from $N_2^r$ go to $W$.* For $i \in N_2^r$, $T = B \cap R_i \subseteq \{r_i(1), r_i(4)\}$.
  EFX-envy needs $T = \{r_i(1), r_i(4)\}$ and $v_i(r_i(1)) > v_i(X_i) \ge v_i(r_i(2)) + v_i(r_i(3))$, so $i \in A$.
  Being in $N_2$, $i$ lost $r_i(1)$ in Phase I to an agent of $W$, which keeps it. Since $r_i(1) \ne j$ (it is
  assigned), $r_i(1) \in X_{i'}$, and $i'$ is that agent of $W$.

So a directed path from $W$ stops at once. A path from $N_1$ goes to an agent holding at least two goods, which lies
in $N_1$ (stop), in $W$ (stop) or in $N_2^r$, and from $N_2^r$ it goes to $W$ and stops. Every path has at most two
edges, and there is no cycle. The node set is nonempty, because $j$ is valued by an agent of $S$ (Step 3). So a source
exists.

*Step 6 (adding $j$ to a source keeps EFX).* Every valuer of $j$ is a node (Step 3), and none EFX-envies
$X_s \cup \{j\}$, since the source $s$ has no in-edge. For a non-valuer $i$, $(X_s \cup \{j\}) \cap R_i = X_s \cap R_i$,
so by Fact 0 nothing changes for $i$. The other bundles are unchanged, and $s$ gains.

*Step 7 (junk).* A good valued by nobody changes no $X_j \cap R_i$, so by Fact 0 giving it to anyone keeps EFX. ∎

**Remarks.**
- *G1 is necessary.* Literally, the unmatched $A$-agents get nothing and are in no $N_k$. Example: $n = 2$, $m = 2$,
  $v_0 = (13, 8)$, $v_1 = (7, 2)$. Both agents are in $A$; one wins good 0 and the other leaves with nothing, and
  every literal run ends non-EFX. With G1, every run ends EFX (the referee reproduced both).
- *The bound of two edges is attained* (`k4/referee/vm.md` §3, a hand-built instance).
- *Where EFX₀ breaks.* Fact 0 has no EFX₀ analogue. Steps 2 and 6 dismiss non-valuers because "they do not value
  $g$". Under EFX₀ these are exactly the agents that envy $\{y_s\}$ or $X_s$ and see a good worthless to them added.
  The algorithm's repair toward EFX₀ is Conjecture VM1 (§11.3).

**Referee report.** `k4/referee/vm.md`: CORRECT, for ordinary EFX and for the reconstruction of §10.1. The referee
extracted the abstract's text from the PDF and confirmed that the quotations in `k4/vm.md` §1 are verbatim. Its own
implementation enumerated every resolution of every choice point: about 8.3 million runs, exhaustive over small value
sets for $n = 2$ ($m \le 6$) and $n = 3$ ($m \le 4$), plus random and contested-top instances, with values 0 and ties
allowed. Every run
ended in a complete ordinary-EFX allocation, with every step's invariants asserted. The referee's two requirements are
kept here: the scope (ordinary EFX only; a reconstruction), and the remark that Phase III must serve $N_3$ before
$N_2$.

## 11. Open problems and conjectures

Everything in this section is open. Evidence is finite data, and random data can miss rare structures. Several
conjectures of this campaign survived millions of random starts and then fell to one designed instance (§7.2).

### 11.0 TARGET₄

**TARGET₄ is open.** What is known comes from earlier certified work (ledger rows K4.R5–K4.R6a, K4.MC0–K4.MC7) with the
reductions of §2.2. A minimal counterexample is a strict connected $k = 4$ core in the MC2 class, and it has:
- at least six agents, at least one of them with four goods (at least two if $n = 6$);
- cyclomatic number at least 5.

By L1 (PROMPT.md), a counterexample would also refute EFX existence for strictly positive additive valuations.

### 11.1 OC₁^max, and the reduction to perfect starts

> **Conjecture 11.1 (OC₁^max; `k4/sdc.md` §31, ledger K4.SDC.OC1MAX) [C].** In every strict connected $k = 4$ core,
> for every SD order whose picks form a maximum matching: the picks have a one-absorber EFX₀ completion, or one
> improving move (an addition, a chain or a ring) gives a state that has one.

By Corollary 6.4 (machine-checked), Conjecture 11.1 implies TARGET₄.

*Evidence* [E] (`k4/sdc.md` §31, ledger K4.SDC.OC1MAX):
- every start of the earlier OC₁ data, since those runs tried every order with $n \le 5$: 120,050 starts;
- all 31,584 core hypergraphs with $n = 5$, three random strict profiles each, every order: 0 failures among
  11,002,996 maximum-matching orders, of which 176,670 need one move;
- the known counterexamples to the every-order forms: 0 failures among 33,082 maximum-matching orders. On the 39
  distinct core counterexamples every maximum-matching order completes at the picks;
- the Hall session's 2,071 one-absorber-hard maximum-matching starts ($n \le 5$), where the refined form OC₁-ED\*^max
  holds on all;
- adversarial climbs on strict cores up to $n = 8$, by the coordinator, the TTC session and the $k$-sensitivity session:
  no failure.

*Limits.* Conjecture 11.1 is false at $k = 5$ (Proposition 7.4), so a proof must use $k \le 4$, presumably through
Lemma 7.5. Every failing every-order start known has the pickless pigeonhole that Lemma 6.3 excludes.

**Lemma 11.2 (RED, reduction to perfect starts; `k4/sdc.md` §31) — written proof, not refereed.** The Hall session
checked it (`k4/oc1_hall.md` §21). Let $Y$ be maximum-matching picks of any instance with strict values. Let $U \ne
\emptyset$ be the pickless agents, $S$ the agents reachable from $U$ by $Y$-alternating paths, $T$ the remaining agents,
and $J$ the junk.
- (i) No agent of $U \cup S$ values a junk good (Lemma 6.3).
- (ii) Every good valued by an agent of $U \cup S$ is the pick of an agent of $S$.
- (iii) Let $I'$ be the instance with agents $T \cup U$ and goods $\{Y_t : t \in T\} \cup J$, values restricted. The
  agents of $U$ become *null agents*, valuing nothing. Then every one-absorber EFX₀ completion of $I'$, at its picks
  or after a move of $I'$, extends to one of $I$: the agents of $S$ keep their single picks, and the agents of $U$
  get what they get in $I'$.

*Proof sketch* (from the source). For (ii): a good valued by $u \in U$ is picked, else $u$ could be matched to it; it is
the pick of some $b$, and $b \in S$. A good valued by $s \in S$ is not junk by (i), so it is a pick $Y_b$, and again
$b \in S$. For (iii), every EFX₀ constraint involving $S \cup U$ holds in the extension:
- agents of $S \cup U$ value only picks of $S$, which are held alone, and removing a singleton's good leaves nothing;
- agents of $S \cup U$ value no junk, so they never envy the bundles of $U$ agents;
- agents of $T$ compare $S$ holders' singletons only, which never violates EFX₀.

Every move of $I'$ is a move of $I$, and the absorber counts are the same. ∎

So OC₁ at maximum-matching starts, for every instance with at most four relevant goods per agent, follows from OC₁ at
**perfect starts** (every agent with a relevant good holds a pick), with null agents allowed and counted as ordinary
agents in the absorber count. With Lemma 6.2 this would give TARGET₄ without the core reduction. $I'$ need not be a core,
so this route needs the perfect-start form for all 4-limited instances.

*What a proof could use* (each refereed, Appendix B, unless marked otherwise):
- the Hall session's exact condition for one-absorber completability at fixed bases (Lemma 2\*, Corollary 2.1 of
  `k4/oc1_hall.md`);
- the one-frozen-agent case (Theorem F1₁ there);
- Lemma 7.5;
- for one dangerous agent, the proved reduction of the Hall session's Finding D1 to two named obstacles, HEAD and
  CROWD (`k4/oc1_hall.md` §21; Lemmas D1-chain, D1-red), which is not refereed.

### 11.2 MD and SD-C

> **Conjecture 11.3 (MD; `k4/sdc.md` §28) [C].** In every 4-limited instance, every matching is value-dominated by a
> complete EFX₀ allocation.

> **Conjecture 11.4 (SD-C; `k4/sdc.md` §2) [C].** In every 4-limited instance, some SD order's picks extend to a
> complete EFX₀ allocation.

MD contains TARGET₄ (take the empty matching). By Lemma 6.1 it is equivalent, for strict values, to value domination
of every order's picks. Neither conjecture has a counterexample at any $k \le 8$ tested (§8). For every $k$, both
contain EFX₀ existence for all additive instances.

### 11.3 VM1: one move from a Viswanathan–Mehta matching

> **Conjecture 11.5 (VM1; `k4/vm.md` §7.3) [C].** For every 4-limited instance there are:
> - a V-M matching $Y$ (Phases I–II of §10.1, some resolution of ties);
> - at most one move: a pool upgrade, or a two-agent exchange in which $i$, holding a single good, takes any good $z$
>   of $j$ plus pool goods, both agents gaining and EFX₀ kept;
> - an order of the remaining goods;
>
> such that placing each good on some agent whose bundle stays EFX₀-unenvied, rotating envy cycles before each
> placement, ends in a complete EFX₀ allocation.

VM1 implies TARGET₄. Every state of such a run satisfies five invariants, (I1)–(I5) of `k4/vm.md` §7.3:
- (I1) partial EFX₀;
- (I2) domination of the start;
- (I3) a good someone prefers to its own bundle is held alone;
- (I4) bundles of two or more goods are envied only by agents that value all their goods;
- (I5) a potential rises at every move.

The referee checked these invariants (Lemmas SND and TERM; `k4/referee/vm.md` §6).
- *Evidence* [E]: the screen set 168/168 (157 with no move), the named instances 95/95, random cores with $n = 3$–5
  (2,700/2,700), and general instances 3,000/3,000.
- *Robustness at $k = 5$* [E]: VM1 holds at $k = 5$ on PW5, RD5 and both $n = 4$ instances of the two-agent session, and
  on 2,000 random 5-limited instances. So it is a general-$k$ candidate.
- *Limits.* With *narrow* exchanges (the taker must value $z$), VM1 is refuted at $n = 3$, $m = 7$
  (`attempts/k4-vm-vm1.md`, independent replay). The unproved step is placeability, and P1's state GM4-E (§7.1)
  shows that (I1), (I3), (I4) alone do not imply it.

### 11.4 DYN: LSS's algorithm with dynamic parking

> **Conjecture 11.6 (DYN; `k4/girth.md` §5) [C].** For every 4-limited instance there are a vertex 0 and a labeling
> such that LSS's Algorithm 2, with the G1 repair, ends in a state that *dynamic parking* completes.
>
> - The G1 repair: an envied agent takes the most valuable subset of its leftovers that beats its bundle and keeps
>   EFX₀, and is skipped if there is none.
> - Dynamic parking: hand out the leftover goods one at a time, each to an agent that is non-envied at that moment,
>   keeping EFX₀.

DYN implies TARGET₄. Lemmas 5.4–5.6 are its proved ingredients. Dynamic parking makes no agent worse off, so DYN is a
value-monotone route that must avoid the stuck states of §7.1. It does so on all data, including every labeling of
GM4-E.
- *Evidence* [E]: every screen and suite instance with 2-cycles, 2,164,809 random strict $n = 4$ core profiles,
  1,239,515 random $n = 5$ profiles, and 1,905,183 random instances with 2-cycles: all complete.
- *Robustness* [E]: it also survives PW5, RD5, B<, B> and the 39 core counterexamples, so it is not tied to $k = 4$.
- *Variants refuted*: DYN without the G1 repair (`attempts/k4-girth-dyn-plain.md`), and a single sink instead of dynamic
  parking (at $n = 2$).

The linear case of DYN (Conjecture LR-dyn, `k4/girth.md` §4) would give EFX₀ for every linear additive instance at
every $k$.

### 11.5 W: welfare maxima

> **Question 11.7 (W($k$); `kgen/charity.md` §6) [C].** Is there an $f$, independent of $n$, with W($k, f$)? That is:
> does every $k$-limited instance have a welfare maximum over partial EFX₀ allocations leaving at most $f$ goods out?

W($k, f$) implies a charity bound $f(k) \le f$ (§4.4). W(3, 0) and W(4, 0) fail (GM4-G, `w_brute.log`), and W(3, 1)
and W(4, 1) fail by Proposition 4.5. So $f \ge 2$ is needed at both $k = 3$ and $k = 4$. The S′($\sigma, k$) family is
the natural test. If it carries welfare-maximal stranded states for every $\sigma$, W($k$) fails for every $f$. The
$\sigma = 4$, $k = 4$ search (three goods stranded, $n = 20$) was running when this draft was written.

At $k = 4$ the only $n$-independent charity bounds proved are those of §4, for instances whose goods have few valuers.
The open case is connected instances whose unallocated goods all have many valuers (Corollary 4.3).

### 11.6 RD²: two rounds of disjoint chains

> **Conjecture 11.8 (RD²; `k4/ksens.md` §6–§7) [C].** For every $k$ and every additive instance, from every SD order
> (or from every maximum-matching order), two rounds of vertex-disjoint improving chains, applied one after the
> other, reach bases with a one-absorber completion.

One round is false at $k = 5$ (Proposition 7.7). There the first round releases the foreign picks and the second
collects them, and for this mechanism two rounds suffice however many picks are needed.
- *Evidence* [E]: climbs at $n \le 6$, $k = 5, 6, 8$ found no start needing three rounds. Within $n \le 5$, $m \le 9$,
  with every good valued, no start needs even two (§8).
- *Strength*: RD² for every $k$ contains EFX₀ existence for all additive instances.
- *A design to try next*: RD5's mechanism one level deeper, which needs $n \ge 6$.

### 11.7 Smaller questions

- *OC₁ at $k = 3$ for every order* (candidate theorem OT, `k4/k3_oc1.md` §4). The open drafts are those covered by
  neither Theorem 9.4 nor Theorem 9.5: least deficit 2, or exposed agents sharing junk goods.
- *Conjecture L, the ladder* (`k4/ksens.md` §4): from every order, $\lfloor (k-1)/2 \rfloor$ improving chains suffice.
  At $k = 4$ it is OC, which is false for some orders (§7.2), so the conjecture needs a restriction of the orders
  (for instance, maximum-matching orders).
- *Bounded charity CH($k$) at $k = 4$*: is there an $f(4)$ independent of $n$ and $d$? Theorem 4.1 gives
  $\min\{2d - 1, R(d)\}$.

## 12. References

Read levels are those recorded by the sessions that read each work: `proofs/citations.md`, the referee's reports,
`k4/ttc.md` §1, `kgen/charity.md` §8 and the campaign's literature report `reports/EFX literature from the agent
side.md`. A work no session read is marked [unverified].

- **[AAMMS]** H. Afshinmehr, A. Ashuri, M. Mahmoudkhan, K. Mehlhorn, A. Shahrezaei. *EFX Allocations Exist on
  Multi-Graphs.* arXiv:2606.18665v1, 2026. Read in full (`proofs/citations.md` item 4; digest
  `proofs/multigraph_digest.md`).
- **[ACMM]** D. J. Abraham, K. Cechlárová, D. F. Manlove, K. Mehlhorn. *Pareto optimality in house allocation
  problems.* ISAAC 2004, LNCS 3341, 3–15. Full text (author version) read by the TTC session's literature readers,
  whose notes were checked for consistency but not re-read against the PDF (`k4/ttc.md` §1). Used: Prop. 2, §6 Lemma 1,
  Theorem 1.
- **[AMMSW]** H. Akrami, N. Mayorov, K. Mehlhorn, S. Srinivas, C. Weidenbach. *A Counterexample to EFX, n ≥ 3 Agents,
  m ≥ n + 5 Items, Submodular Valuations, via SAT-Solving.* arXiv:2604.18216v3, 2026. Read in part: abstract, §1,
  §2, §9 (`proofs/citations.md`). The literature report cites a later version (v4, with more authors) for the
  monotone three-agent, eight-good counterexample; this draft relies on neither.
- **[AS98]** A. Abdulkadiroğlu, T. Sönmez. *Random serial dictatorship and the core from random endowments in house
  allocation problems.* Econometrica 66 (1998), 689–701. Full text, with the appendix proofs at statement level, read
  by the TTC session's literature readers. Used: Lemma 1.
- **[CFKS]** G. Christodoulou, A. Fiat, E. Koutsoupias, A. Sgouritsa. *Fair allocation in graphs.* EC 2023;
  *Envy-Freeness up to Any Good Allocations on Graphs*, Math. Oper. Res., 2026. Author PDF read in full
  (`proofs/citations.md` item 3). The EC text was not read.
- **[CGM]** B. R. Chaudhury, J. Garg, K. Mehlhorn. *EFX Exists for Three Agents.* arXiv:2002.05119v3; EC 2020;
  J. ACM 71(1), 2024. Read in part: abstract, model, Lemma 1, Theorem 20 (`proofs/citations.md`). The JACM text was
  not read.
- **[CGMMM]** B. R. Chaudhury, J. Garg, K. Mehlhorn, R. Mehta, P. Misra. *Improving EFX Guarantees through Rainbow
  Cycle Number.* arXiv:2103.01628; EC 2021. Read: §1 and §4 (`kgen/charity.md` §8).
- **[CKMS]** B. R. Chaudhury, T. Kavitha, K. Mehlhorn, A. Sgouritsa. *A Little Charity Guarantees Almost
  Envy-Freeness.* arXiv:1907.04596v3; SODA 2020; SIAM J. Comput. 50(4), 2021. Read: §2 (Algorithms 1–3, Lemmas 2,
  4–7, Theorem 8), by the charity session and by the referee.
- **[KS]** M. Kirchweger, S. Szeider. Computations of small rainbow cycle numbers ($R(3) = 3$, $R(4) = 4$).
  [unverified]: known only through [Siv], p. 2.
- **[Lin-k3]** E. Lin. *EFX₀ Allocations with at Most Three Relevant Goods: Existence and a Verified Polynomial-Time
  Algorithm.* Repository `paper/k3/` (main and long versions).
- **[Lin-k3s]** E. Lin. *EFX₀ Allocations with at Most Three Relevant Goods: A Short Proof* (Draft and Exchange).
  Repository `paper/k3-simple/`.
- **[LSS]** T. Lianeas, A. Sgouritsa, M. M. Sotiriou. *EFX Allocation In (Multi)Hypergraphs.* arXiv:2608.03171v1;
  AAAI 2026. §2–§3 read in full by the girth session and by the referee (PDF, sha256 `a720a6e4…cb53`); §4 skimmed.
- **[Mah]** R. Mahara. *Extension of Additive Valuations to General Valuations on the Existence of EFX.*
  arXiv:2107.09901v2; ESA 2021; Math. Oper. Res. 49(2), 2024. Read: Theorem 3 and §2 (`proofs/citations.md` item 1).
- **[MS]** S. Mackenzie, M. Suzuki. *Counterexamples to EFX for Submodular and Subadditive Valuations.*
  arXiv:2605.06451v1, 2026. Read: abstract, §1, the definition in §2.
- **[PR]** B. Plaut, T. Roughgarden. *Almost Envy-Freeness with General Valuations.* arXiv:1707.04769v3; SODA 2018.
  Read by the referee from the PDF: §1.3, §2, §4.2 (Theorems 4.1–4.3 with proofs), Appendix A, the start of
  Appendix B (`k4/referee/lit_n2.md`). The journal version (SIAM J. Discrete Math. 34(2), 2020) was not read
  [unverified].
- **[Siv]** V. Sivashankar. *A Linear Bound on the Rainbow Cycle Number and Approximate EFX.* arXiv:2607.27455v1, 2026.
  Read: §1–§3 and §5 (Theorem 3 with its proof), by the charity session and by the referee.
- **[VM]** M. Viswanathan, R. Mehta. *On the existence of EFX under picky or non-differentiative agents.* Proc.
  AAMAS 2024, pp. 2534–2536 (extended abstract). Read in full, by the VM session and by the referee (PDF, sha256
  `d0f6a352…7cd7`).

Repository-internal sources cited above: `proofs/lb_last_step.md` (construction LB⁺); `k4/SCOUT.md` (core reduction);
`k4/MINCEX.md` (minimal counterexamples); `LEDGER.md` (the rows named).

## Appendix A. Verification record

**Referee.** Branch `claude/k4-referee`, head `c873b80`, `k4/referee/README.md` (PR #108). The checks are under
`k4/referee/*.py`, with logs under `results/k4_referee/`.

**Sources.** The "head" column is the branch head when this draft was written. "Unchanged" means the cited sections
were compared between the refereed commit and the head by this write-up's session: proofs identical, at most remarks
or citations added.

| result here | source (branch) | refereed at | head | cited sections since | report | verdict |
|---|---|---|---|---|---|---|
| Fact 3.1, Lemmas 3.2–3.3, Theorem 3.4, Cor. 3.5 | `kgen/n3.md` §9 (`claude/kgen-n3`) | `418f876` | `78f59e9` | unchanged (literature paragraph added) | `kgen_n3.md`, `lit_n2.md` | CORRECT |
| Theorem 4.1, Cor. 4.3 | `kgen/charity.md` §8 (`claude/kgen-charity`) | `1e986c6`, `0c85d91` | `0c85d91` | unchanged | `chkd.md` | CORRECT |
| Theorem 4.2 | `kgen/charity.md` §2–§3 | `78deef1` | `0c85d91` | unchanged (Prop. DU added) | `charity.md` | CORRECT |
| Prop. 4.4 (DU) | `kgen/charity.md` §3 | `8862555` | `0c85d91` | unchanged | `charity.md` §5, `chf.md` | CORRECT |
| Prop. 4.5 (CH-F) | `kgen/charity.md` §6, `attempts/kgen-charity-welfare-maxima.md` | `8862555` | `0c85d91` | unchanged | `chf.md` | CORRECT |
| Theorem 5.1, Cor. 5.2, Lemmas 5.4–5.6 | `k4/girth.md` §3–§4 (`claude/k4-girth`) | `5b79844`, `90c116f` | `a494e3b` | unchanged (a remark on the valuation class added) | `girth.md` | CORRECT (PARK: state $N \ne \emptyset$) |
| Prop. 5.3 ($H_t$) | `k4/girth.md` §4 | `90c116f` | `a494e3b` | unchanged | `girth.md` §5 | CORRECT ($HH_t$ not rebuilt) |
| Lemmas 6.1, 6.2 | `k4/sdc.md` §28, §31 (`claude/kind-lamport-y8fdme`) | `d48084e` | `123b396` | unchanged (Lemma RED appended) | `maxsd.md` | CORRECT |
| Lemma 6.3 | `k4/oc1_hall.md` §19 (`claude/k4-oc1-hall`); `k4/ttc.md` §13 | `e2b4701`; `77bcab1` | `4f2a226` | unchanged | `maxsd.md`, `oc1_hall.md` §6, `ttc_t5.md` | CORRECT |
| Prop. 7.4 (PW5) | `k4/ksens.md` §1 (`claude/k4-ksens`) | `ceba5c7` | `6308933` | unchanged | `ksens.md` | CORRECT (the aside on one-agent moves is incomplete but not needed) |
| Lemma 7.5 (PL) | `k4/ksens.md`, status block | `7ec7073` | `6308933` | unchanged | `ksens.md` §5 | CORRECT |
| Lemma 7.6 (PWk(a)) | `k4/ksens.md` §7 | `7ec7073` | `6308933` | fix applied in the source | `ksens.md` §5 | CORRECT WITH FIXES (applied) |
| Lemmas 9.1, 9.2, Theorems 9.4, 9.5 | `k4/k3_oc1.md` §2–§3 (`claude/k4-k3-oc1`) | `949718a` | `48bcf05` | unchanged (B\*'s statement clarified) | `k3_oc1.md` | CORRECT (R1C: DE's core case) |
| Lemma 9.3 | `k4/k3_oc1.md` §2 | `949718a` | `48bcf05` | **fix not yet applied in the source**; applied here | `k3_oc1.md` §3 | CORRECT WITH FIXES (applied here) |
| Theorem 10.1 | `k4/vm.md` §1–§2, §8 (`claude/k4-vm`) | `7a78df6` | `0595a29` | unchanged | `vm.md` | CORRECT (ordinary EFX; the reconstruction) |

**Not refereed, included with their verification status.** These are Propositions 7.1–7.3, 7.7, the Remark in §7.2,
the $k$-ladder cells marked [V] or [E], Lemma 11.2, and every conjecture of §11.

**Lean.** On branch `formal/k4-oc1max` at `838fb0e`, this write-up's session ran `lean/check.sh`. The result: CHECK
PASSED, with 1,246 audited statements and 2,350 theorems, every declaration on `propext`, `Classical.choice` and
`Quot.sound` only, and the `leanchecker` replay passing. The certificates for `EFX.OC1Max.sdpo`,
`EFX.OC1Max.exists_order_maximum`, `EFX.OC1Max.max_no_augment`, `EFX.OC1Max.picks_no_junk` and
`EFX.OC1Max.target4_of_conjOC1max` are in `paper/campaign/lean_check_oc1max.log`. The branch is not yet merged into
`main`.

## Appendix B. Other refereed results

The referee also found these results CORRECT. They support the conjectures of §11 but are not developed in this
draft. Statements and proofs are in the files named.
- *Completion at fixed bases* (`k4/oc1_hall.md` §1, §4–§6; report `k4/referee/oc1_hall.md`).
  - Lemma 2 and Lemma 2\* give the exact condition for a one-absorber completion with a given owner: a system of
    distinct representatives of admissible holders (Corollary 2.1).
  - Lemma 4 (helpers) and Proposition 3.
  - Theorem F1₁: one frozen agent with one wanter, $n \ge 3$, completes after at most one swap. Its case (B2) uses
    Theorem DT₁ and Lemma GDT of `k4/sdc.md` §30, both re-derived by the referee.
  - One wording fix: Corollary 2.1's gloss "a transversal of the demands" holds only if a demand is a set whose
    presence *threatens*.
- *Induction along the SD order* (`k4/sd_induct.md`; report `k4/referee/sd_induct.md`).
  - Lemmas D, F, S, Corollary TP and Lemma BOTH-TP.
  - Lemma U is CORRECT WITH FIXES: its statement needs the hypothesis "the first agent is unfrozen".
  - In passing: Lemma H, Proposition PR-step and Theorem PR-TP, where "PR completion" must presuppose EFX₀.
- *The repaired V-M procedure* (`k4/vm.md` §7, §7.4; report `k4/referee/vm.md` §5–§6).
  - Lemmas SND (soundness) and TERM (termination, potential $\Phi \le 15n$), and the invariants (I1)–(I5) of VM1.
  - Lemmas P0 and P1′ ("exactly when" needs strict values) and Proposition HDT.
- *Facts F1–F6 at Pareto maxima of linear instances* (`k4/girth.md` §4): CORRECT for additive valuations. F2 fails for
  monotone valuations (counterexample in `k4/referee/girth.md` §3).
