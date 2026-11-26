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
