# EFX₀ with Few Relevant Goods per Agent: Refereed Results of a Campaign on Four Goods

*Draft, 2026-11-27. Workstream `paper/campaign`. This is a write-up of results from the repository; it changes no
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
following. (i) For two agents, from either serial-dictatorship order, either both picks are kept (the first agent may add
unpicked goods it values, and the other agent absorbs the rest), or one improving chain from the first agent to the
second repairs them; the allocation is computed in $O(m \log m)$ at every number of relevant goods. Bare
existence for two agents is due to Plaut and Roughgarden; the shape is new. (ii) A charity bound that does not depend
on the number of agents: if every agent values at most $k$ goods and every good has at most $d$ valuers, some partial
EFX₀ allocation with strong charity leaves at most $\min\{(k-2)d-1,\ R(d)\}$ goods out, where $R(d) < ed$ is the rainbow
cycle number. Also: exact EFX₀ with $O(\sqrt{kn})$ charity; complete EFX₀ for instances whose agent–good graph has two
or more components with agents; and welfare maxima can strand two goods at $k = 3$ and $k = 4$. (iii) EFX₀ exists for
monotone valuations when the agent hypergraph is linear and some agent lies on no Berge 3-cycle, which extends the
girth-4 theorem of Lianeas, Sgouritsa and Sotiriou. (iv) Serial-dictatorship facts that the campaign's move-based
conjectures rest on, with Lean proofs: serial-dictatorship outcomes are exactly the Pareto-optimal matchings (strict values), some order
picks a maximum matching, and at such picks no agent reachable from an unmatched agent by an alternating path values an
unpicked good. (v) At $k = 3$, in the core case of Draft and Exchange, one improving chain suffices from every order
whose draft is compatible with the peeling priority. EFX₀ also exists for monotone valuations with at most three
relevant goods per agent. (vi) A complete proof that a reconstruction of the 4-limited algorithm of Viswanathan and
Mehta, with one necessary correction, gives ordinary EFX (not EFX₀). (vii) For $k = 4$, the lemmas behind a
two-move programme: a short certificate that one move fails, exact matching criteria for one-absorber completions,
reductions of the one-move case to named obstacles, two theorems proving the one-move statement outright where they
apply, and a refereed second-move mechanism (settle one dangerous agent by an earliest-wanter chain, then one move
in the smaller instance) that repairs, on every strict four-agent core, every start that needs two moves. On the
negative side we give
counterexamples, each printed in full:
- "one chain from every order" fails on strict $k = 4$ cores;
- the campaign's central conjecture OC₁^max (one move from every maximum-matching order) fails at $k = 4$, on a
  four-agent core that millions of random tests had missed;
- one round of disjoint chains fails, at $k = 4$ and with all values positive;
- value-monotone methods can get stuck already at $k = 3$;
- the two-move welfare and leximin lemmas fail at $n = 4$, $k = 4$, even with set moves.

We end with the case tree of the $k = 4$ programme, its open statements, and the conjectures that survive, with the
evidence for each. OC₂^max, two sequential moves from every maximum-matching order, is certified for every strict
core profile with at most four agents and on 3,605 five-agent cores. At four agents every two-move start has a
refereed explicit repair. TARGET₄ stays open along two fully specified routes, each ending in a Lean-checked
implication. The first is receiver-first orders, which needs the completion half of Conjecture RF in its existential
form RF∃: some receiver-first order completes after one move. The every-order form is false at $k = 5$. The second is
rounds of settlements, which needs a corrected base case, Conjecture BASE-R, and its Lean frame now takes exactly that
hypothesis. The receiver-first Lean frame on main still requires a unique receiver, which fails at five agents; a
pull request restates it.

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
9. Three relevant goods: one chain from R1-compatible orders, and monotone valuations
10. Ordinary EFX for 4-limited instances: a reconstruction of Viswanathan–Mehta
11. The k = 4 programme after OC₁^max
12. Open problems and conjectures
13. References

Appendix A. Verification record. Appendix B. Other refereed results. Appendix C. Reproducing the instance checks.
Appendix D. Written after the referee's table (not included).

## 0. How to read this draft

**Labels.** Every numbered statement has one of these labels.
- **[R]** Proved. A written proof is given here or in the file named, and the campaign's independent referee
  (branch `claude/k4-referee`, `k4/referee/`) found it CORRECT. The referee's checks are written from the raw
  definitions and share no code with the authors' sessions.
- **[R′]** Proved. The referee found it CORRECT WITH FIXES, and the fix is applied in this text. The fix is stated.
- **[L]** Also machine-checked in Lean 4 (core Lean only, standard axioms only).
- **[V]** A counterexample checked by at least two independent programs from the raw definitions, but **not** in the
  referee's table. The programs are named.
- **[Cert]** A finite statement certified by an exhaustive computer search, whose certificate was re-checked by a
  separately written checker, but not refereed.
- **[E]** Evidence only: computation on finite data. Random testing can miss rare failures, so [E] never means proved.
- **[C]** Conjecture.

Section 11 also uses **[W]** (a written proof on the branch named, not checked by the referee) and **OPEN** (no proof
known). No result of this draft depends on a [W] statement.

**Sources.** Each result names its source: the file, the section, and the branch where that file lives. The
repository is `evanlin23/efx0-three-goods`. The referee read the sources at the commits named in Appendix A, and
Appendix A also records whether the cited section changed afterwards. "Session" means one of the campaign's parallel
working sessions, and "coordinator" the session that integrated them (branch `claude/kind-lamport-y8fdme`, log
`k4/attack_log.md`).

**What the computations are.** Unless a statement says otherwise, computations here are the sessions' and the
referee's, and they are logged in the repository. Appendix C adds one check by this write-up's session
(`paper/campaign/check_instances.py`). It re-verifies every instance printed in this draft from the printed data, so
transcription errors would show up.

**A caution.** Several statements here passed millions of random tests and were then refuted by a small instance
found by exhaustive or designed search. The clearest case is OC₁^max (§7.3). Evidence [E] in this draft is therefore
weak evidence, whatever its size.

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
- For most of the campaign the central conjecture was **OC₁^max**: from every order whose picks form a maximum
  matching, the picks need at most one improving move, after which one agent absorbs the leftover goods. It implies
  TARGET₄, and that implication is machine-checked (Corollary 6.4). In the campaign's last hour an exhaustive search
  refuted it on a four-agent core (Proposition 7.4).
- The candidates now are two sequential moves (OC₂^max) and some-order forms (§12.1). The machine-checked
  implication applies to them unchanged. Both are certified for every strict core profile with $n \le 4$, and §11
  records how far a proof of OC₂^max has come.

The results below are of four kinds.
1. *Theorems that hold for every $k$*: the two-agent shape (§3), the charity bounds (§4), the linear-hypergraph theorem
   (§5) and the matching lemmas (§6).
2. *Counterexamples* (§7). They show which forms of "one move suffices" are false: from every order, from every
   maximum-matching order (two dangerous agents sharing one junk pair), and in one round. They also show where
   $k \le 4$ helps: after one repair a frozen agent has at most $k - 3$ unpicked goods left, which is at most one at
   $k = 4$ (Lemma 7.6). This count, and the PW family where it is exact, still separates $k = 4$ from $k = 5$.
3. *Evidence* for the surviving conjectures, collected in the $k$-ladder table (§8).
4. *Side results*: one chain suffices at $k = 3$ from orders compatible with the peeling priority (§9); EFX₀ exists
   for monotone valuations with at most three relevant goods (§9.4); and a complete proof of a reconstruction of
   Viswanathan and Mehta's ordinary-EFX algorithm (§10).
5. *The $k = 4$ programme* (§11). These are the refereed lemmas a proof of OC₂^max would use:
   - a certificate that one move fails;
   - exact matching criteria for completions;
   - reductions for one and for several dangerous agents;
   - two theorems that prove the one-move statement outright where they apply (Theorems 11.13 and 11.18);
   - a second-move mechanism (Theorem 11.23) that repairs every $n = 4$ start needing two moves.

   They are arranged in a case tree whose remaining gaps are nine named open statements, in two parts (§11.9).
   Several shapes that held at $n = 4$ fail at $n = 5$, and several owner rules fail already at $n = 4$. At $n \le 5$
   OC₂^max has no counterexample. §11.10 sets out the two routes that remain to TARGET₄, receiver first (RF) and
   rounds (ROUND-RSD with the base case BASE-R), and exactly which statement each still needs.

### 1.3 Related work, and what was already in the repository

Only works that some session read are cited as such; anything else is marked [unverified] (§13 gives read levels).
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
- *Reductions to cores at $k = 4$* (rows K4.CORE, K4.TIE). They are proved and checked in Lean; §2.2 states them.
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
| OC₂^max | the same with at most two sequential moves | `k4/sdc.md` §31 |
| some-order form | *some* maximum-matching order satisfies OC₁ | `k4/sdc.md` §31 |
| RD, RD₁ | from every order, one round, then a completion (free, resp. one-absorber) | `k4/ksens.md` §6 |
| RD² | the same with two rounds applied one after the other | `k4/ksens.md` §6 |

*Status at the end of the campaign.*
- Refuted: OC and OC₁ (§7.2), OC₁^max (§7.3), RD and RD₁ (§7.3, §7.5).
- Conjectures: SD-C, MD, OC₂^max, the some-order form and RD² (§12). OC₂^max and the some-order form are certified
  for every strict core profile with $n \le 4$ (Proposition 11.26).

Each of these move forms implies MD for the orders it covers, because every agent on a chain gains. Each implies a
complete EFX₀ allocation as soon as it holds for one order, hence TARGET$_k$. For the maximum-matching forms this goes
through Lemma 6.2 and the reductions of §2.2.

## 3. Two agents

Source: `kgen/n3.md` §9 (branch `claude/kgen-n3`). Refereed against commit `418f876`; §9's mathematics is unchanged at
the head `419960c`, which only adds the literature paragraph.

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
  (`kgen/n3.md` §3.2–§3.3: 2 of 8,000 random two-agent starts; the smallest $k$ found is 7). On the curated $k = 4$ sets no start needs an addition
  (`kgen/n3.md` §3.3).
- *Peeling in OC₁ form* [R] (referee item 61, `k4/referee/kgen_n3.md` addendum; Appendix B). Lemma P of
  `kgen/n3.md` §2 peels a top-heavy pick in OC₁ form. With Theorem 3.4 it gives Corollary 3 of §11 there: OC₁ holds
  for every order in which $n - 2$ picks are iteratively top-heavy. At $n = 3$ that means every order with a
  top-heavy pick, at every $k$.
- *Not in Lean.* `kgen/n3.md` is on main since PR #97. This write-up found no Lean formalization of Theorem 3.4 in
  `lean/` on main, so it is not marked [L].

**Referee report.** `k4/referee/kgen_n3.md` (branch `claude/k4-referee`): CORRECT, with the instruction to cite
[PR] Theorem 4.3 for existence. Its independent check (`k4/referee/theorem2_ref.py`) tests the construction against
the raw EFX₀ definition and an independent OC₁($t \ge 0$) witness test. That covers 496,162 starts: exhaustive over
small value grids, plus 20,000 random instances with $m \le 14$, with 0 failures. A mutation test shows Lemma 3.2 is
needed exactly where it is used: without it, the one-absorber shape breaks on 973 of 40,000 starts.

### 3.3 Three agents at every $k$ is as hard as three-agent EFX

**Proposition 3.6 (H; `kgen/n3.md` §10, branch `claude/kgen-n3` at `eb95583`) [R′].** If every three-agent
instance with distinct tops and relevance bound $k + 3$ has an EFX₀ allocation, then every three-agent instance with
relevance bound $k$ has one. In particular, OC₁ at $n = 3$ for every $k$, even restricted to distinct tops, implies
EFX₀ for three additive agents.

*Proof.* Given an instance $I$ on $M$, add goods $t_1, t_2, t_3$, with $v_i(t_i) = L + \delta$ and $v_i(t_j) = L$
for $j \ne i$, where $L > \max_i v_i(M)$ and $\delta > 0$. Then $t_i$ is $i$'s unique top, and each $R_i$ grows by
exactly three goods.

Let $X$ be EFX₀ for the new instance. If agent $i$ held no $t$, some $j$ would hold two. Then $X_j \setminus g$
contains a $t$ for every $g \in X_j$, so $v_i(X_j \setminus g) \ge L > v_i(M) \ge v_i(X_i)$, contradicting EFX₀. So
each agent holds exactly one $t$, say $X_i = \{t_{\sigma(i)}\} \cup S_i$, and $S$ is an allocation of $M$. For
$g \in S_j$, EFX₀ gives
$$v_i(S_i) \ \ge\ v_i(S_j \setminus g) + \big(v_i(t_{\sigma(j)}) - v_i(t_{\sigma(i)})\big) \ \ge\ v_i(S_j \setminus g) - \delta,$$
since the difference lies in $\{-\delta, 0, \delta\}$. So $S$ is EFX₀ for $I$ up to $\delta$. Take $\delta \to 0$
with $L$ fixed. Some $S$ repeats infinitely often among the finitely many allocations, and the inequalities are
closed, so that $S$ is EFX₀ for $I$. (With rational values, any $\delta$ below the smallest positive gap works
directly.) The consequence follows because OC₁ produces an EFX₀ allocation, and the relevance bound is at most $m$.
∎

The fix is the sign of the bracket in the display. The source writes "$-\,(v_i(t_{\sigma(j)}) - v_i(t_{\sigma(i)}))$",
which is not what EFX₀ gives. The conclusion is unaffected.

So general-$k$ statements at $n = 3$ are at least as hard as three-agent EFX [CGM] (via L1 of PROMPT.md, the
perturbation lemma; [CGM] itself was not read). The reduction maps $k$ to $k + 3$, so it says nothing about fixed
small $k$ such as $k = 4$. The proposition calibrates; it does not reduce.

**Referee report.** `k4/referee/proph.md`: CORRECT WITH FIXES (the sign). Evidence: 3,000 random three-agent
instances lifted with $\delta$ below the value gaps, and every EFX₀ allocation of each lift checked, with 0 failures.
A control with $\delta$ above the gaps makes the restriction fail 24,671 times, so the limit step is genuinely used.

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

*Step 5 (part 3: the rainbow cycle reduction with $\varepsilon = 0$).* Fix for every agent $a$ a source $\rho(a)$
with $a \in C(\rho(a))$, and for every $s \in S$, $g \in P$ one option, with champion $c(s, g)$. Let
$Q_g = \{c(s, g) : s \in S\}$. Build the $|P|$-partite digraph $\Gamma$ with parts $V_g = \{g\} \times \rho(Q_g)$ and,
for $g \ne h$, an edge $(g, s_1) \to (h, s_2)$ if and only if $\rho(c(s_2, g)) = s_1$.
- Every vertex $(h, s_2)$ has the in-neighbour $(g, \rho(c(s_2, g))) \in V_g$ in every other part $V_g$.
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
contain agents, the instance has a complete EFX₀ allocation. (Additive valuations. The source also states it for
monotone valuations with $R_i$ the support of $v_i$; that extension was not refereed.)

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
with $f \ge 2$ is open (§12.5).

**Referee report.** `k4/referee/chf.md`: CORRECT for both instances; single implementation on the referee's side,
independent of the session's two.

## 5. Linear hypergraphs

Source: `k4/girth.md` §1–§4 (branch `claude/k4-girth`). Refereed against `5b79844`, with the later additions
(generalized Lemma SLACK, Proposition HT) against `90c116f`; the proved statements are unchanged at the head `235bca4`.

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

### 5.3 Completion lemmas

These lemmas hold beyond linear hypergraphs, and Conjecture DYN (§12.4) is built on them. Write $U$ for the
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

**Lemma 5.7 (EC, envy-cycle rotation; `k4/girth.md` §5, branch `claude/k4-girth` at `235bca4`) [R].** For monotone
valuations, in a partial EFX₀ allocation, giving every agent of an envy cycle the bundle of the agent it envies keeps
EFX₀, and keeps (3) if it held.

*Proof.* The bundles are the same sets, and every value weakly rises, strictly on the cycle. An agent never strongly
envies its old bundle, now someone else's: its new value exceeds $v_i(X_i) \ge v_i(X_i \setminus g)$. Toward every
other bundle its value only rose. Agents off the cycle see the same sets at the same values. (3) persists because the
set $U$ of unallocated goods is unchanged. ∎

**Corollary 5.8 (stuck states; same source) [R].** Consider dynamic parking with envy-cycle rotation: leftover goods
are given one at a time to agents that are non-envied at that moment, keeping EFX₀, and envy cycles are rotated.
Start it at a state with (3) for all agents, such as the output of LSS's Algorithm 2 (which ends with FixProp3). If
it reaches a state with leftovers where no good can be placed and no envy cycle exists, then non-envied agents
exist, and every one of them holds at least two goods.

*Proof.* Without an envy cycle the envy graph is acyclic, so it has a source. Parking steps only raise values and
shrink $U$, and Lemma 5.7 keeps (3), so (3) still holds. A non-envied agent holding at most one good could then
absorb any leftover by Lemma 5.6. ∎

The premise "(3) when parking starts" is the referee's addition. Without it the statement is false: on EFX₀ states
without (3), the SLACK step fails 442,797 times in 784,999 tests. Conjecture DYN (§12.4) asks whether such a stuck
state can always be avoided.

**Referee report.** `k4/referee/girth.md` §6: CORRECT (with the premise stated). Evidence: 10,290 rotations at
(3)-states and 5,221 stuck states over additive and non-additive monotone valuations, with 0 failures.

## 6. Serial dictatorship and maximum matchings

Sources: `k4/sdc.md` §28 and §31 (coordinator branch `claude/kind-lamport-y8fdme`) and `k4/oc1_hall.md` §19 (branch
`claude/k4-oc1-hall`). Refereed against `d48084e` and `e2b4701`. Lean: `lean/EFX/OC1Max.lean` on branch
`formal/k4-oc1max` (head `28f3e1e`).

These three lemmas make OC₁^max imply TARGET₄, and they rule out the pickless pigeonhole behind the counterexamples to
"one chain from every order" of §7.2. OC₁^max was the campaign's central conjecture, and it is itself false
(Proposition 7.4). The lemmas, and the Lean frame built on them, are parametrized by the move relation, so they apply
unchanged to the surviving candidates of §12.1, such as two sequential moves. All three are close to known facts about house allocation
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

**Lemma 6.3 (MAX; `k4/oc1_hall.md` §19; also Lemma T5 of `k4/ttc.md` §13) [R; part 1 also L].** Let the picks $Y$ form a maximum
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

### Consequences

**Corollary 6.4 (bounded-move forms imply TARGET₄) [L].** Fix any relation "one step" on states, such as one move,
or two sequential moves. Suppose that in every strict connected $k = 4$ core, from every maximum-matching SD start,
the picks or some state reached in one step have a one-absorber EFX₀ completion. Then every 4-limited additive instance
has a complete EFX₀ allocation. With one move as the step, this is "OC₁^max implies TARGET₄"; its hypothesis is false
(Proposition 7.4).

*Proof.* By §2.2, it suffices to treat strict connected $k = 4$ cores. By Lemma 6.2 one of their orders picks a
maximum matching, and the hypothesis gives an EFX₀ completion for it. ∎ (The referee checked Lemmas 6.1–6.2; the corollary
itself is the machine-checked composition below.)

The Lean statements are `EFX.OC1Max.target4_of_conjOC1maxWith`, for any move relation, and its one-move instance
`EFX.OC1Max.target4_of_conjOC1max`. Their hypotheses (`ConjOC1maxWith`, `ConjOC1max`) are `Prop`s, not axioms.
Both run through Lemma 6.2 and the machine-checked reductions K4.CORE and K4.TIE. The Lean model has values in
$\mathbb{N}$. The lemmas are `EFX.OC1Max.sdpo` (Lemma 6.1), `EFX.OC1Max.exists_order_maximum` (Lemma 6.2) and
`EFX.OC1Max.max_no_augment`, `EFX.OC1Max.picks_no_junk` (Lemma 6.3). `lean/EFX/OC1MaxExamples.lean` shows the
definitions are not vacuous on the MC2 core of §7.2: the failing order there does not pick a maximum matching, and the
order $3, 4, 0, 1, 2$ picks one with a one-absorber completion. The Lean proof of Lemma 6.2 takes a maximum matching
of largest total value; a Pareto improvement of it would be a maximum matching of larger total value.

**What Lemma 6.3 does and does not exclude.** The counterexamples of §7.2 to OC and OC₁ "for every order" share one
shape. Pickless agents value only picked goods. They freeze the pick holders, which then cannot take junk, and the
pickless agents are left as the only junk receivers. At a maximum-matching start this pickless pigeonhole cannot form,
since pickless agents freeze only agents that value no junk. Lemma 6.3 says nothing when every agent picks, and that
is where OC₁^max fails (Proposition 7.4: two dangerous agents share a junk danger pair).

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
it is threatened. If it is exactly that pair, the other bundle has four goods and contains two goods of a triangle:
$\{3, 8\}$, $\{5, 7\}$ or $\{4, 6\}$ when the pair is $\{6, 7\}$, $\{6, 8\}$ or $\{7, 8\}$. ∎

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

So OC₁ "for every instance", as literally stated, is false at $k = 3$. What the conjectures of §12 need is the core
form.

### 7.3 One move fails at $k = 4$, even from maximum-matching starts

**Proposition 7.4 (OC₁^max fails; `k4/sdc.md` §31, end; `k4/oc1_hall.md` §22) [R] †.** OC₁^max is false at
$k = 4$. So are its free-completion form OC^max and OC₁ at perfect starts, the target of Lemma RED (§12.1).
Instance 1 is a strict connected $k = 4$ core in the MC2 class, with $n = 4$ and $m = 7$:

| agent | goods (value) |
|---|---|
| 0 | 0 (2), 1 (10), 2 (4), 5 (7) |
| 1 | 1 (10), 2 (3), 5 (4), 6 (8) |
| 2 | 3 (3), 4 (5), 5 (6), 6 (7) |
| 3 | 3 (3), 4 (2), 6 (4) |

- The order $(0, 3, 2, 1)$ gives the picks 1, 2, 5, 6 to agents 0, 1, 2, 3, and the junk is $\{0, 3, 4\}$.
- Every agent picks, so $\nu = n = 4$ and this is a maximum-matching (indeed perfect) start.
- The instance has 14 complete EFX₀ allocations. None contains the picks, or the bases of any state one move
  (addition, chain or ring) reaches. So there is not even a free completion.

Instance 2 has $n = 4$, $m = 7$ and is also a strict connected MC2-class core:

| agent | goods (value) |
|---|---|
| 0 | 0 (2), 4 (3), 5 (10), 6 (6) |
| 1 | 1 (3), 2 (10), 3 (6), 5 (8) |
| 2 | 1 (5), 3 (3), 5 (7), 6 (6) |
| 3 | 2 (4), 4 (3), 6 (2) |

The order $(3, 1, 2, 0)$ gives the picks 4, 5, 6, 2 to agents 0, 1, 2, 3. It has 24 complete EFX₀ allocations, and
again none completes the picks or any one-move state.

*Mechanism* (`k4/oc1_hall.md` §22). In instance 1, agent 1 is the only unfrozen agent, and it holds its worst good 2.
Agents 2 and 3 are dangerous and **share the junk danger pair** $\{3, 4\}$: $3 + 5 > 6$ for agent 2 and $3 + 2 > 4$
for agent 3. There is at most one free slot. Whoever owns the pair must also hold the leftover junk, and then the
other agent sharing the pair is threatened. Each canonical chain from a dangerous agent fails; §22 there gives
the reason for each. Instance 2
has the same structure, with agents 1 and 2 sharing the pair $\{1, 3\}$. These are not the pickless pigeonhole of
§7.2, which Lemma 6.3 excludes: here every agent picks. The obstruction needs at least two dangerous agents (the
Hall session's analysis for one dangerous agent, `k4/oc1_hall.md` §21, is not contradicted). In terms of Lemma 7.6
(PL), the failure uses exactly the cases PL leaves open: the base a chain releases, and a danger set built on another
agent's pick (`k4/ksens.md` §5).

*What survives on these instances.*
- *Two sequential moves repair both.* In instance 1, the chain $(2, 1)$ is followed by the chain $(0, 1)$.
- *Other orders work.* Of the maximum-matching pick vectors, 4 of 7 (instance 1) and 4 of 6 (instance 2) complete
  at the picks, and the rest after one move, except the failing one.
- *The R1-priority form fails too* [V] (the referee did not check this remark). Both failing starts are also produced by R1-priority orders: $(3, 2, 0, 1)$ for
  instance 1 (the printed order $(0, 3, 2, 1)$ is not R1-priority) and $(3, 1, 2, 0)$ for instance 2.
- *One round fails too* [V]. No round of vertex-disjoint chains and additions repairs either start, even with the
  free completion. So RD and RD₁ fail at $k = 4$ as well. Three groups found this, all for all 11 failing cores
  except where noted:
  - this write-up's checker, with two methods (Appendix C), on instances 1 and 2;
  - the $k$-sensitivity session, with its two checkers, SAT and brute force (`k4/ksens/refute_oc1max_k4.py`,
    `results/k4_ksens/refute_oc1max_k4.log`);
  - the coordinator, on instances 1 and 2.

  Two sequential rounds (RD²) repair both.

*Scope of the search* (`k4/oc1cert.md`, branch `compute/k4-oc1max-cert`). The certifier ran an ordinal CEGAR over
every strict profile of every core hypergraph with $n \le 4$, through the agents' order types.
- *OC₁^max* holds for every profile of all 5 hypergraphs with $n = 2$, all 51 with $n = 3$, and 991 of the 1,002
  with $n = 4$ [Cert]. It fails on the other 11, listed in `results/k4_oc1max/oc1max_cex_n4.json`; instances 1 and 2
  are two of them.
- *Two sequential moves (OC₂^max)* suffice for every strict profile of every core hypergraph with $n \le 4$, which is
  1,058 hypergraphs [Cert]. The certificate is `results/k4_oc1max/cert_4_depth2.json.gz`. A separately written SAT
  checker re-checks it ("every certified hypergraph (1002) covered for every type profile and every
  maximum-matching SD order", `check_4_depth2.log`), and $n \le 3$ also has a brute-force coverage check.
- The coordinator checked the 11 failing hypergraphs independently: every maximum-matching order needs at most two
  moves (`k4/sdc/oc2max_cex_check.py`, `results/k4_sdc/oc2max_cex_check.log`).
- None of this has been refereed.

*Verification of the refutation.*
- Found by the certifier's ordinal CEGAR.
- Replayed independently by the coordinator, from the raw EFX₀ definition by brute force with no SAT
  (`k4/sdc/oc1max_cex_verify.py`, `results/k4_sdc/oc1max_cex_verify.log`).
- Re-analysed by the Hall session (`k4/oc1_hall.md` §22) and brute-forced on all 11 (`brute_verify_cex_n4.log`).
- Appendix C re-checks both printed instances.
- The referee confirmed both printed instances (`k4/referee/oc1_hall_d1.md` §2) and all 11 failing cores
  (`k4/referee/oc1cert.md`), by its own brute force over every allocation and every one-move state. Its check
  includes ordinality: order-preserving perturbations of each profile fail in the same way.
- Lemma T6 (§11.2) turns the failure into a short argument, given the list of EFX₀ allocations that value-dominate
  the picks.

Ledger K4.SDC.OC1MAX is REFUTED.

**A caution on evidence.** Before this, OC₁^max had no failure on:
- 11,002,996 maximum-matching orders of random strict profiles of all 31,584 core hypergraphs with $n = 5$;
- 33,082 maximum-matching orders of the known counterexamples to the every-order forms;
- adversarial climbs up to $n = 8$.

The counterexamples have only $n = 4$ and $m = 7$, and were found by exhaustive search over all strict profiles.
Random profiles had never produced two dangerous agents sharing one junk danger pair with no free slot. ROUND⁺
(§7.5) and Conjecture W (§12.5) also fell to exhaustive or designed searches after passing large random tests. On
this problem, millions of random starts are weak evidence.

### 7.4 One chain fails at $k = 5$: the PW family

**Proposition 7.5 (PW5; `k4/ksens.md` §1) [R] †.** The following instance has $n = 5$, $m = 9$, and is 5-limited.
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
start. Hence OC and OC₁ fail at $k = 5$, and so at every $k \ge 5$; so do OC^max and OC₁^max. (They fail at
$k = 4$ already, by Proposition 7.4, through a different mechanism. PW5 matters for the count that follows.)

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

**Lemma 7.6 (PL, pool leftover; `k4/ksens.md`) [R].** Let $Y = \mathrm{SD}(\pi)$ with junk $J$. Let $x$ be an agent
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
Proposition 7.5. ∎

PL covers only the old junk $J \setminus H$. Released picks, agents that share only one good with $H$, and danger
sets that use another agent's pick are not covered; these are the parts a $k = 4$ proof still has to handle
(`k4/ksens.md`, "What PL does not cover").

**Lemma 7.7 (PWk(a), the PW family at $k \le 4$; `k4/ksens.md` §7) [R′].** In the family PW($f, W, r$), $f$ frozen
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

### 7.5 One round of disjoint chains fails at $k = 5$, and for positive values

**Proposition 7.8 (RD5; `k4/ksens.md` §6) [V] †.** The following instance has $n = 4$, $m = 7$, strict values, and
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

**Remark (ROUND⁺: one round fails with every value positive; branch `proof/kgen-rounds`, PR #111) [R] †.** RD5+
is RD5 with $v_0(4) = 23$, all values multiplied by 100, and every zero replaced by 1. So every agent values every
good: $n = 4$, $m = 7$, and $k = 7$.

| agent | values of goods 0–6 |
|---|---|
| 0 | 2600, 5700, 1, 4400, 2300, 3300, 1 |
| 1 | 1, 1200, 1100, 600, 1, 1, 1 |
| 2 | 1, 900, 800, 600, 100, 1, 1 |
| 3 | 3600, 1, 5300, 1, 1, 4700, 400 |

From the order $(0, 3, 1, 2)$, which gives agents 0–3 the picks 1, 3, 4, 2, no single round of disjoint chains
reaches bases with an EFX₀ completion, free or with one absorber. Two rounds repair it. With all values positive,
EFX₀ and EFX coincide.

*A two-round repair.* Round 1 is the chain $(3, 1)$: agent 1 takes good 2, and agent 3 takes $H_0 = \{0, 5\}$,
which releases good 3. Round 2 is the chain $(0, 2)$: agent 2 takes good 1, and agent 0 takes good 4 of agent 2's
base together with good 3, worth $6700 > 5700$. The bases are then $(\{3, 4\}, \{2\}, \{1\}, \{0, 5\})$, and
agent 0 absorbs good 6: $(\{3, 4, 6\}, \{2\}, \{1\}, \{0, 5\})$ is EFX. This is the repair printed in
`kgen/rounds.md` §3.1, with the referee's fix applied. The printed version also added good 6 to agent 0 in round 1,
and then the chain rule hands agent 2 all of $\{1, 6\}$, so the printed final allocation does not contain agent 2's
base (`k4/referee/rounds_r1.md` §2).

*Verification.* The session's certificate (`kgen/rounds/refute_roundplus.py`) shows the following by raw
enumeration: every EFX allocation that value-dominates the picks has an agent that would need two foreign picks.
Two further checkers of the session agree (`rnd.c`, `bruter.py`), and so does the $k$-sensitivity session's SAT
pipeline. The coordinator replayed a second instance of the same kind ($n = 4$, $m = 7$, order $(2, 1, 3, 0)$;
`k4/sdc/roundplus_cex_check.py`). Appendix C re-checks RD5+.

This corrects the earlier evidence that with every good valued one round always sufficed (`k4/ksens.md` §8; §8 below).

The certificate the session used is a general lemma.

**Lemma 7.9 (R1; `kgen/rounds.md` §1, branch `proof/kgen-rounds` at `a33b135`) [R].** Let $X$ be a complete
allocation that contains the bases after one round from SD picks $y$. Then:
- $v_i(X_i) \ge v_i(y_i)$ for every $i$, strictly when $y_i \notin X_i$;
- every base contains at most one pick of another agent. A receiver $x_i$ gets the one passed pick $y_{x_{i-1}}$,
  the start of a chain with $t \ge 1$ at most its own chain's end pick $y_{x_t}$, and an off-chain agent or an
  addition its own pick.

*Proof.* Off-chain agents and additions keep their pick. A receiver $x_i$ gets $\{y_{x_{i-1}}\} \cup H_i$ with
$H_i \subseteq J$. A start takes $H_0 \subseteq J \cup \{y_{x_t}\}$ from its own chain's end only (§2.4). Chain
agents gain strictly over their pick, and bases lie inside the final bundles. Only nonnegativity is used. ∎

**Corollary 7.10 (starved-agent certificate; same source) [R].** Call an agent $a$ *starved* in $X$ if
$y_a \notin X_a$ and $v_a(\{f\} \cup (X_a \cap J)) \le v_a(y_a)$ for every foreign pick $f \in X_a$, and also
$v_a(X_a \cap J) \le v_a(y_a)$. If every EFX₀ allocation that value-dominates the picks has a starved agent, then no
round from the picks has a completion, free or one-absorber.

*Proof.* A completion $X$ after one round value-dominates the picks by Lemma 7.9, so it has a starved agent $a$.
Since $y_a \notin X_a$, agent $a$ passed its pick and lies on a chain with $t \ge 1$. Its base, worth more than
$v_a(y_a)$, lies inside $\{f\} \cup (X_a \cap J)$ for its at most one foreign pick $f$. That contradicts
starvation. ∎

This is the analogue for rounds of Corollary 11.2. On RD5+, every one of the 6 EFX allocations that value-dominate
the picks starves agent 0, which holds $\{3, 4\}$, two foreign picks. The referee confirmed this, and the same for
the two further instances of the source (C4G, and a two-type instance), by its own enumeration of every round
(`k4/referee/rounds_r1.md` §2).

**Referee report.** `k4/referee/rounds_r1.md`: Lemma R1 and the corollary CORRECT; the refutations of ROUND⁺ CONFIRMED;
the printed two-round repair of RD5+ needs the fix applied above. Evidence: 398,577 (round, completion) pairs from
8,050 random positive starts, with 0 violations of Lemma 7.9.

**Summary of §7.3–§7.5.**
- One move from every maximum-matching start fails at $k = 4$, when two dangerous agents share a junk pair
  (Proposition 7.4).
- In the PW family, one move fails at $k = 5$, while every $k \le 4$ member passes (Proposition 7.5, Lemma 7.7).
- One round fails at $k = 4$ (§7.3) and at $k = 5$ (Proposition 7.8), and also with all values positive (RD5+).
- The two-move form OC₂^max and the two-round form RD² have no known counterexample (§12.1, §12.6).

## 8. The $k$-ladder (mostly evidence)

Source: `k4/ksens.md` §4, §7, §8 (branch `claude/k4-ksens`), with the $k = 3$ entries from `k4/k3_oc1.md` (branch
`claude/k4-k3-oc1`). **This section is mostly evidence.** Only the cells marked [R] or [V] are established, and those marked [Cert] for the finite range stated;
"holds" means "no failure on the data", never "proved".

How much repair do SD picks need, as a function of $k$? A *start* is the SD picks of an order. Each row asks for a
complete EFX₀ completion after the stated repair, from every start of the stated kind.

| statement | $k \le 2$ | $k = 3$ | $k = 4$ | first failure | smallest counterexample known |
|---|---|---|---|---|---|
| no repair: the picks extend | proved (K3.SD2, Lean) | **fails** [V] | fails | $k = 3$ | $n = 2$, $m = 4$ (below) |
| one move from every order (OC₁, OC) | (no move needed) | proved for R1-compatible orders in DE's core case [R] (§9); exhaustive over every strict profile of every connected hypergraph with $n \le 4$, every start (§9) [Cert]; fails outside cores at $n = 5$ [V] (§7.2) | **fails** on strict cores [V] (§7.2, §7.3) | $k = 3$ outside cores, $k = 4$ on cores | $k = 3$: $n = 5$, $m = 9$; $k = 4$: $n = 4$, $m = 7$ (§7.3) [V] |
| one move from maximum-matching starts (OC₁^max, OC^max) | | | **fails** [R] (§7.3); also at $n = 5$ (§11.9) | **$k = 4$** | $n = 4$, $m = 7$ [R]; at $k = 5$ also PW5 [R], and N3K5 with $n = 3$ [R] |
| one move from *some* maximum-matching order (OC₁^∃max) | | | certified for every strict core profile with $n \le 4$ [Cert] (§11.7) | none found | (§12.1) |
| two sequential moves from maximum-matching starts (OC₂^max) | | | certified for every strict core profile with $n \le 4$ [Cert]; holds [E] beyond | none found | (§12.1) |
| one move from R1-priority starts | | | **fails** [V] (§7.3; on cores with two private goods already §7.2) | $k = 4$ | $n = 4$, $m = 7$ [V] |
| one move from the need-2 neediest-first start | | | holds [E] (not the failing start on the §7.3 instances) | $k = 6$ | NF2-6, $n = 6$, $m = 11$ [V] |
| one move from LB₄ʳ's Phase 1 (need-2, R1) | | | holds [E] | none found | |
| $c$ moves in sequence | $c = 0$ | $c = 1$ [E] | $c = 1$ fails; $c = 2$ [Cert] for $n \le 4$ from maximum-matching starts | $c = 1$: $k = 4$; $c = 2$: $k = 7$ [V]; in the PW family $c$ chains fail at $k = 2c + 3$ ($c \le 3$) | §7.3; PW($c+2$, $c+1$, $2c+2$): $c = 1$ [R]; $c = 2$, PW(4, 3, 6) with $n = 7$, $m = 13$, from a maximum-matching start [V]; $c = 3$ one SAT encoding [E] |
| one round of disjoint chains (RD, RD₁) | | | **fails** [V] (§7.3) | $k = 4$ | $n = 4$, $m = 7$; at $k = 5$ RD5 [V] and N3K5 [R] |
| one round with non-end agents taking end goods (ROUND-P) | | | holds [E] at every $n = 4$ two-move start and every sampled $n = 5$ one (§11.7) | none found | |
| one round with all values positive (ROUND⁺; $k = m$) | | | | fails at $n = 4$, $m = 7$ | RD5+ [R] (§7.5) |
| two rounds (RD²), from maximum-matching starts | | | [Cert] for $n \le 4$ (a chain is a round); repairs the §7.3 instances | none found | (§12.6) |
| SD-C (some order, no repair) | proved | holds [E] | holds [E] | none found ($k \le 8$) | |
| MD (every start value-dominated) | proved for strict values (K3.SD2 with Lemma 6.1) | open (TARGET₃ is the empty matching only) | holds [E] | none found ($k \le 8$) | |

Notes on the cells.
- *One move fails at $k = 5$ already for three agents* (`k4/ksens.md` §8, branch `claude/k4-ksens`; N3K5) [R] †.
  Agent 0 values goods 0, 2, 3, 4, 5 at 3, 22, 23, 38, 43; agent 1 values goods 1, 2, 3, 4, 5 at 15, 17, 27, 40, 43;
  agent 2 values goods 1, 4, 5 at 1, 2, 4. The order $(1, 0, 2)$ gives the picks 4, 5, 1, a maximum-matching start.
  There is no completion, free or one-absorber, at the picks, after one move, or after one round. Two chains repair
  it. The session's two checkers (SAT and brute force) agree, and so does this write-up's (Appendix C). The referee
  confirmed N3K5 and N3K5⁺, and noted that OC₁′ repairs both (`k4/referee/ksens.md` §7).
  - At $k = 5$, one chain fails on 13 of the 617 connected $n = 3$ hypergraphs, and two chains suffice on all 617
    [Cert]. Two chains also suffice on all 1,138 core-like $n = 4$ hypergraphs with $m \le 7$ [Cert]
    (`kcegar_k5_core5_n4_D2_m5-7.log`). At $k = 4$ one move first fails at $n = 4$, and at $k = 3$ it never fails
    from a maximum-matching start for $n \le 5$.
  - With its zeros replaced by small positive values, N3K5 still needs two rounds (N3K5⁺). So one round fails for three
    agents with every good valued, where EFX allocations are known to exist [CGM].
- *CGM's three-agent hypergraph at $k = 6$* (ledger K4.KSENS.CGM6, `k4/ksens.md` §8) [Cert]. The hypergraph of
  Chaudhury, Garg and Mehlhorn's three-agent example has the sets $\{0,1,2,3,5,6\}$, $\{0,2,3,4,6\}$, $\{4,5,6\}$.
  On it OC₁^max holds for every strict profile: from every maximum-matching start, the picks or one improving chain
  have a one-absorber completion (`kcegar_cgm_exact.log`).
  - The certificate is a CEGAR in exact six-good mode. The grid only proposes cores, and a rational LP confirms every
    cut, so all strict profiles are covered.
  - The exact mode was validated on 16 of 16 cases against complete type lists and a pure LP route
    (`kcegar_exact_check.log`). The LP added 5,956 strict points that the $B = 48$ grid lacks, so grid-only runs would
    have been partial.
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
  - *Two sequential chains fail at $k = 7$* (ledger K4.KSENS.CHAINS, REFUTED; `k4/ksens.md` §4) [V]. The witness is
    PW(4, 3, 6): $k = 7$, $n = 7$, $m = 13$, from the natural order, a maximum-matching start where every agent
    picks. No state that two chains reach has an EFX₀ completion, not even a free one, with empty passes allowed.
    Three chains repair it.
  - The two programs are `ocseq.py` (two chains in one SAT encoding) and `kchains.py`. The second lists all 158,100
    one-chain states by SAT, uncapped, and tests each with a separate call for one more chain
    (`ladder_pw436_bfs2_free.log`).
  - So the number of sequential moves needed grows with $k$. Rounds do not grow this way within PW (§12.6).
- *Orders.* The orders where one chain first fails depend on the order class: every order fails at $k = 5$, and
  R1-priority and need-2 neediest-first orders fail at $k = 6$ (each case checked by two SAT encodings and a SAT-free
  enumeration, `refute_oc1_r1.log`). LB₄ʳ's Phase 1 order and "some order" (SD-C) have no counterexample at any $k$
  tested.
- *What fails at $k = 5$ beyond these rows.* The conclusions of Theorem DT, Lemma GDT and Theorem DT₁ (`k4/sdc.md` §6,
  §30), which hold at $k = 4$, fail at $k = 5$ [V]. The instance DT5 has $n = 2$, $m = 6$: agent 0 values goods 0
  (100) and 2, 3, 4, 5 (91, 92, 93, 94), and agent 1 values goods 1 (100) and 2, 3, 4, 5 (94, 93, 92, 91). The tops
  are distinct, and yet the picks have no one-absorber completion †. The instance DT1-5 has $n = 3$, $m = 8$
  (`k4/ksens.md` §3).

**The $k$-dependence in one count** (Lemma 7.6). A frozen agent's junk danger sets live in its at most $k - 1$ junk
goods, and a repair spends two of them.
- $k \le 2$: no danger set, no chain.
- $k = 3$: a danger pair, one chain, nothing left.
- $k = 4$: one good left, never a danger set for the repaired agent or for an agent sharing two of its goods
  (Lemma 7.6 (b), (c)). But two dangerous agents sharing one junk pair defeat one move (Proposition 7.4), and two
  sequential moves suffice on all data.
- $k = 5$: two goods left, a danger set for the agents sharing the pool (PW5); or the repair needs two foreign picks
  (RD5).

The $k \le 4$ inputs a proof of OC₂^max, or of any bounded-move form, can use are these:
- Lemma 7.6 (b), (c);
- Lemma 7.7;
- the one-agent counts in Theorem DT's (F4) and in DT₁'s step 3 (`k4/sdc.md` §6, §30);
- RD5's five-good requirement.

**Unrestricted $k$** (`k4/ksens.md` §8 and `proof/kgen-rounds`). Lift PW5 to full valuations, with every agent valuing
every good (strict, positive, $k = m = 9$): one chain still fails, and one round repairs [E]. So PW's mechanism does
not need zero values.
- The $k$-sensitivity session found that a lift of RD5 needs only one round, and that with every good valued no start
  within $n \le 5$, $m \le 9$ needed two rounds (climbs and random profiles) [E].
- That evidence was overturned. RD5+, a different lift of RD5, needs two rounds (§7.5, [V]). It was found by seeded
  climbs, which the random profiles had missed.
- So zero values are not what makes the second round necessary. Two rounds suffice on every instance found.

## 9. Three relevant goods: one chain from R1-compatible orders, and monotone valuations

Source: `k4/k3_oc1.md` §1–§3 (branch `claude/k4-k3-oc1`). Refereed against `949718a`; §2–§3 are unchanged at the head
`48bcf05`. The proofs build on construction LB⁺ (`proofs/lb_last_step.md`, machine-checked as `EFX.target`) and on
Draft and Exchange (DE; `paper/k3-simple`, [Lin-k3s]).

TARGET₃ is known. The question here is whether its constructions have the OC₁ shape: one-absorber completions of SD
picks, after at most one improving chain. A positive answer at $k = 3$ was meant as the base case for the
one-move forms at $k = 4$; those are now refuted at $k = 4$ (Proposition 7.4), but OT at $k = 3$ is open.

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

**One chain at $k = 3$, exhaustively for $n \le 4$** (`k4/ksens.md` §8, branch `claude/k4-ksens`) [Cert]. From every
start, maximum-matching or not, one chain followed by a one-absorber completion repairs every strict profile of every
connected hypergraph with $n \le 4$ in which every agent values at most three goods. Profiles are covered through
order types. At $n = 4$ that is 1,885,816 profiles and 4,982,948 starts, of which 126,994 need a chain. It holds
under both move rules (chains that may or may not pass an empty base).
- This covers more than DE's core case: agents with fewer goods and top-heavy agents are included.
- The session's program re-checks every repair from the raw definitions, and a SAT pipeline agrees on all
  maximum-matching starts at $n = 3$ and on a sample at $n = 4$.
- The referee confirmed it exhaustively with its own code: its own hypergraph enumeration, types, SD, chains and
  completions (`k4/referee/ksens.md` §6). All four counts at $n = 3$ and $n = 4$ agree. The claim also holds with
  fewer goods than agents ($m < n$), which the session's range $n \le m \le 3n$ left out.
- It is consistent with the $n = 5$ non-core failure of §7.2.
- The run for $n = 5$ was still going when this draft was written.

**Beyond Theorem 9.5: Conjecture T′ and its strong form T′_k** (`k4/k3_oc1.md` §12, branch `claude/k4-k3-oc1` at
`9719be2`). Conjecture T′ says that at every hard perfect draft of a core, some *rotation into a terminal* has a
one-absorber completion. A rotation into $t$ starts from an exposed agent $k$ of the terminal $t$, and is a chain or a
ring through $t$. The strong form T′_k asks for that completion with no owner or with owner $k$, which is Theorem
9.5's owner.
- *T′_k is false at $n = 7$* [V] †. Every agent values its goods $a > b > c$ at $10, 8, 7$, and $(a, b, c)$ is
  $(7, 0, 8)$, $(5, 7, 9)$, $(5, 10, 7)$, $(0, 3, 2)$, $(1, 2, 6)$, $(1, 6, 4)$, $(3, 4, 6)$ for agents 0–6 ($m = 11$,
  a core of `results/certs_7_11.json.gz`).
  - The order $(2, 1, 0, 5, 6, 3, 4)$ gives the draft $(0, 7, 5, 2, 6, 1, 3)$ with junk $\{4, 8, 9, 10\}$, and the
    draft has no one-absorber completion.
  - The only terminal is agent 4. Its exposed agents 5 and 6 share the pair $\{4, 6\}$.
  - There are exactly two rotations into 4. In one, agent 5 takes $\{6, 4\}$ and agent 4 receives good 1. In the
    other, agent 6 takes $\{4, 6\}$, agent 3 receives good 3, and agent 4 receives good 2.
  - After either one, every one-absorber completion has absorber 3 or 4, and none has no absorber or absorber $k$.
    The other sharer holds its top, and the shared pair now sits inside $k$'s bundle, so $k$'s bundle plus any junk
    good threatens it.
- *Verification.* Found by the session's sampler and replayed by `attempts/k4_k3oc1_tprime_k.py` (raw definitions, no
  repository code). This write-up's checker confirms the draft, its hardness, and the absorber sets after both
  rotations (Appendix C). Not refereed.
- *What survives* [E]. T′ itself, and T-E∃ (some earliest-wanter rotation completes, with owner nobody, the chain's
  end, or $k$), hold here with owner 4. T′_k holds on every hard perfect draft with $n \le 6$ (338,916 at $n = 6$),
  and this is the only failure among 30,045 hard drafts sampled at $n = 7$.

**Referee report.** `k4/referee/k3_oc1.md`. The verdicts are:
- Lemmas 9.1 and 9.2: CORRECT;
- Lemma 9.3: CORRECT WITH FIXES (applied above);
- Theorem 9.4: CORRECT, with the scope statement above;
- Theorem 9.5: CORRECT.

The referee ran LB⁺ with unit caps on every R1-compatible order of exhaustive $n = 3$ data and random data up to
$n = 6$ (about 735,000 runs). Every completion was EFX₀ with one absorber, and an independent brute force over OC₁
agreed.

### 9.4 Monotone valuations with three relevant goods

Here valuations are *normalized* ($v_i(\emptyset) = 0$) and *monotone* ($S \subseteq T \Rightarrow v_i(S) \le
v_i(T)$), not necessarily additive. A good $g$ is relevant to $i$ if $v_i(S \cup \{g\}) > v_i(S)$ for some $S$.
Monotonicity gives $v_i(S) = v_i(S \cap R_i)$: remove the irrelevant goods of $S$ one at a time. EFX₀ is the raw
all-goods notion of §2.1.

**Lemma 9.6 (S3, an additive surrogate; `monotone/k3.md`, branch `claude/monotone-k` at `06e4b02`) [R].** Let $v$ be
normalized and monotone with $v(S) = f(S \cap R)$, $|R| = r \le 3$, and $f$ injective on $2^R$ (*nondegenerate*).
Then there is an additive $w$ with natural-number values, $w(g) > 0$ exactly for $g \in R$, such that for all
disjoint $A, B \subseteq R$: $v(A) < v(B) \iff w(A) < w(B)$.

*Proof.* Monotone and injective means strictly increasing under inclusion, so the singletons are distinct. Rank them
$s_1 > s_2 > s_3$. Put $w(s_1, s_2, s_3) = (4, 3, 2)$ if $v(\{s_1\}) < v(\{s_2, s_3\})$ and $(6, 3, 2)$
otherwise; for $r = 2$ put $(2, 1)$, and for $r = 1$ put $1$. Disjoint nonempty subsets of a set of at most three
goods have sizes $(1, 1)$ or $(1, 2)$. Two singletons are ordered by the ranking under both $v$ and $w$. For $\{x\}$
against $Y = R \setminus \{x\}$: if $x \ne s_1$, then $s_1 \in Y$, so $v(Y) > v(\{s_1\}) > v(\{x\})$, and
$w(Y) \ge 4 > 3 \ge w(x)$. If $x = s_1$, both put $\{s_1\}$ below $\{s_2, s_3\}$ exactly in the first case, since
$4 < 3 + 2$ and $6 > 3 + 2$. Pairs involving $\emptyset$ are trivial. ∎

**Theorem 9.7 (M3; same source) [R].** Every instance with normalized monotone valuations in which every agent has
at most three relevant goods has a complete EFX₀ allocation.

*Proof.*
1. *Nondegenerate profiles suffice.* List $R_i = \{g_1, \dots, g_r\}$ and put $w_i(S) = \sum_{g_t \in S \cap R_i}
   2^t$. For $\varepsilon > 0$, $v_i^\varepsilon = v_i + \varepsilon w_i$ is normalized and monotone, depends only on
   $S \cap R_i$, has relevant set exactly $R_i$, and is injective on $2^{R_i}$ except for finitely many
   $\varepsilon$. Take $\varepsilon_t \to 0$ avoiding them. If each $v^{\varepsilon_t}$ has an EFX₀ allocation, one
   allocation $X$ occurs infinitely often, and each inequality $v_i^{\varepsilon_t}(X_i) \ge
   v_i^{\varepsilon_t}(X_j \setminus g)$ passes to the limit.
2. *EFX₀ depends only on disjoint comparisons.* For $i \ne j$ and $g \in X_j$, the sets $X_i \cap R_i$ and
   $(X_j \setminus g) \cap R_i$ are disjoint subsets of $R_i$. "$\ge$" is the negation of "$<$". So by Lemma 9.6,
   with each surrogate $w_i$ extended by 0 outside $R_i$, the EFX₀ allocations of $(v_i)$ and of $(w_i)$ coincide.
3. $(w_i)$ is an additive instance with natural-number values and at most three relevant goods per agent. TARGET₃
   (ledger row T, machine-checked over ℕ as `EFX.target`) gives it an EFX₀ allocation, which is EFX₀ for $(v_i)$. ∎

*Where it stops.* Lemma 9.6 fails for $r = 4$. The order $a > b > c > d$ with $\{c, d\} > \{a, b\}$ is a linear
extension of the Boolean lattice, and no additive $w$ with $w(a) > w(c)$ and $w(b) > w(d)$ has $w(ab) < w(cd)$. So
4-limited monotone instances form a strictly larger ordinal class than 4-limited additive ones, and monotone EFX₀ at
$k = 4$ would imply TARGET₄.

**Referee report.** `k4/referee/mono_m3.md` (check `k4/referee/mono_ref.py`): CORRECT. Evidence: Lemma 9.6 on all
$1 + 2 + 48$ nondegenerate monotone orders with $r \le 3$; 4,000 random monotone 3-limited instances (half with ties
and zeros), each with an EFX₀ allocation; 2,000 instances on which the EFX₀ sets of $v$ and $w$ coincide.

*The upper end.* Let $k^*_{\mathrm{mono}}$ be the smallest $k$ at which monotone EFX₀ can fail. Theorem 9.7 gives
$k^*_{\mathrm{mono}} \ge 4$. The three-agent, eight-good instance of [AMMSW] (v4, §3.1.1, as read by the
monotone session) has no EFX₀ allocation, and every agent values all eight goods. The
referee built the instance as described in `monotone/amm_check.py` with its own code and found 0 EFX₀ allocations,
without verifying the attribution. So $4 \le k^*_{\mathrm{mono}} \le 8$.

**Proposition 9.8 (MONO.N3K6; `monotone/threshold.md`, same branch, ledger row MONO.N3K6 there) [Cert].** Every
three-agent instance with normalized monotone valuations and at most six relevant goods per agent has an EFX₀
allocation.

*Method.* A minimal counterexample has no junk, a connected incidence graph, $|R_i| \ge 3$, every agent sharing at
least two of its goods, and $m \ge 8$ for $n = 3$ (`monotone/threshold.md` §2; it uses L3, L6 and the peeling rules
for monotone valuations, Mahara's $m \le n + 3$ theorem, and Theorem 1.2 of Akrami et al. for $n = 3$, $m \le 7$, as
read by that session). That leaves 604 hypergraphs with $m = 8, \dots, 15$. For each, a CEGAR over allocations decides
whether some monotone profile has no EFX₀ allocation. All 604 are UNSAT, and an independent checker
(`monotone/check_cert.py`) re-checks every certificate. Not refereed.

So at $n = 3$, monotone EFX₀ cannot fail below $k = 7$, while the known counterexample has $k = 8$.

**Proposition 9.9 (MONO.K4S; same source, ledger row MONO.K4S there) [Cert].** Every instance with normalized
monotone valuations, at most five agents and at most four relevant goods per agent has an EFX₀ allocation. The
method is the same, and it covers 18,829 hypergraphs at $n = 5$ ($m = 9, \dots, 15$). Every certificate is checked
by the independent checker. Not refereed.

Additive valuations are monotone, so Proposition 9.9 gives TARGET₄ for $n \le 5$ by a method independent of the
earlier certified rows K4.R5–K4.R6a. Those rows already put a minimal counterexample at $n \ge 6$ (§12.0).

## 10. Ordinary EFX for 4-limited instances: a reconstruction of Viswanathan–Mehta

Source: `k4/vm.md` §1, §2, §8 (branch `claude/k4-vm`). Refereed against `7a78df6`; these sections are unchanged at the
head `559eec6`.

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
  Its repair toward EFX₀ was VM1, which fails on a $k = 4$ core; the surviving form is Conjecture VM1-chain (§12.3).

**Referee report.** `k4/referee/vm.md`: CORRECT, for ordinary EFX and for the reconstruction of §10.1. The referee
extracted the abstract's text from the PDF and confirmed that the quotations in `k4/vm.md` §1 are verbatim. Its own
implementation enumerated every resolution of every choice point: about 8.3 million runs, exhaustive over small value
sets for $n = 2$ ($m \le 6$) and $n = 3$ ($m \le 4$), plus random and contested-top instances, with values 0 and ties
allowed. Every run
ended in a complete ordinary-EFX allocation, with every step's invariants asserted. The referee's two requirements are
kept here: the scope (ordinary EFX only; a reconstruction), and the remark that Phase III must serve $N_3$ before
$N_2$.

## 11. The $k = 4$ programme after OC₁^max

After OC₁^max fell (Proposition 7.4), the campaign's route to TARGET₄ became OC₂^max (Conjecture 12.1): from every
maximum-matching start, the picks or the bases after at most two sequential moves have a one-absorber completion.
This section records where a proof of OC₂^max stands. It follows the Hall session's integration, `k4/oc1_hall.md`
§23.2 (the case tree), §23.4 and §24 (the open core), branch `claude/k4-oc1-hall` at `700888f`. Leaf statuses are
updated with the referee's verdicts up to item 44 (`k4/referee/README.md` at `70f6e5c`), and with the sessions'
newer refutations, each re-checked here where an instance is printed.

> **TARGET₄ is open.** Two routes are fully specified, and each ends in an implication checked in Lean. Neither
> route's remaining hypothesis is proved. §11.10 gives the exact statements.
> - *Route 1, receiver first:* RF∃ ⟹ OC₁^∃max ⟹ TARGET₄. It needs RF∃ (or the extremal form RKMAX) for every $n$,
>   that is, the completion half after Lemma RF-PATH. The Lean frame on main still requires a unique receiver, which
>   fails at $n = 5$. PR #147 restates it.
> - *Route 2, rounds:* BASE-R ⟹ TARGET₄ (Lean, PR #151). It needs Conjecture BASE-R, equivalently its two base
>   lemmas B1 and B2.

**Where things stand.**
- **OC₂^max has no known counterexample at $n \le 5$.** It is certified for every strict profile of every core with
  $n \le 4$, and of 3,605 of the 31,584 cores with $n = 5$ (Proposition 11.26 item 2), with no start needing three
  moves.
- **One move is not enough, and a round may be.** OC₁^max fails at $n = 4$ and $n = 5$, and so do OC₁′, the wider
  single move, and one plain round. The uniform one-step candidate is **ROUND-P**: one round of vertex-disjoint
  chains whose non-end agents may also take an end's goods. It holds at every $n = 4$ two-move start and at every
  sampled $n = 5$ one [E].
- **Settle-and-lift is not enough as a sequential induction.** REC-S and RSD repair every $n = 4$ two-move start, by
  refereed mechanisms. At $n = 5$, two starts defeat every sequential settle-and-lift form, because each sharer's set
  threatens an agent that only the other sharer's chain improves. The inductive candidates are **RSD-D**, which
  defers the lift condition and carries demands, and **ROUND-RSD**, which settles a round at a time [C].

> **Nothing in this section proves OC₂^max or TARGET₄.** The refereed statements below are reductions or partial
> cases. The open items are listed in §11.9 and marked **OPEN** wherever they occur. This draft has not checked
> that the case tree is exhaustive. That claim is the Hall session's, and it is labelled [W].

Two labels are used here in addition to those of §0:
- **[W]** A written proof exists on the branch named, but the referee has not checked it. No result of this draft
  depends on a [W] statement.
- **OPEN** No proof is known.

For TARGET₄ only cores with $n \ge 6$ matter (§12.0). Every statement here is for all $n$, and every finite
certificate is for $n \le 4$.

### 11.1 Setting and words

Throughout, $k \le 4$, values are strict, and $Y$ is a **perfect start**: an SD outcome in which every agent with a
relevant good holds a pick. Lemma 12.3 (RED, [R]) reduces maximum-matching starts to perfect starts, allowing *null
agents*, which value nothing. Write $p_i = v_i(y_i)$, with $p_i = 0$ for a null agent. Then:
- $F$ is the set of frozen agents, and $D \subseteq F$ the dangerous ones (frozen, valuing some junk good; §2.3);
- a **receiver** is an agent unfrozen at the picks that holds a pick;
- a **holder** of a state is an unfrozen agent whose base has at most one good;
- the start is **hard** if the picks have no one-absorber completion;
- $d \in D$ is **truly dangerous** if $J$ threatens $d$ at $p_d$; $D_T$ is the set of truly dangerous agents. The
  others in $D$ are *pick-dangerous*: no subset of $J$ threatens them at any value $\ge p_d$;
- for an unfrozen $z$, $\Theta(z)$ is the set of $d \in D$ threatened by $J \cup B_z$ at $p_d$.

A **canonical chain** from $k \in D$ is $P = (k = x_0, x_1, \dots, x_t = z)$ with $t \ge 1$:
- each $x_i$ ($i \ge 1$) wants $y_{x_{i-1}}$ at the picks and takes it alone;
- the head $z$ is unfrozen at the picks;
- $k$ takes an *improving* set $H_0 \subseteq \Pi \cap R_k$, $v_k(H_0) > p_k$, from the *pool*
  $\Pi = J \cup \{y_z\}$.

It is an improving chain in the sense of §2.4. $B'$ is the state after it and $J' = \Pi \setminus H_0$ its junk. An
*ED chain* is the same with the head also allowed to take junk.

An **S\* completion** with owner $o$ gives each holder other than $o$ at most one junk good, gives nothing to the
other agents, and gives the rest of the junk to $o$. At a perfect start it is a one-absorber completion with absorber
$o$.

Three SD facts are used everywhere (`k4/oc1_hall.md` §21; `k4/oc1max_multi.md` §2):
- **(π)** if $i$ wants $y_j$, then $j$ precedes $i$ in the order, and $v_j(y_i) \le p_j$ whenever $j$ precedes $i$;
- **(I2)** every junk good is worth less to each of its valuers than that valuer's pick (§2.3);
- **(U)** nobody wants the pick of a receiver.

### 11.2 Why one move fails: Lemma T6

**Lemma 11.1 (T6; `k4/ttc.md` §14.2, branch `claude/k4-ttc`) [R].** Let $Y$ be an SD start in which every agent
holds exactly one pick, with junk $J$. Let $X$ be a complete allocation obtained from $Y$ by one improving move
(addition, chain or ring), followed by any completion that keeps the new bases (free, any number of absorbers).
Then:
- (a) $X$ value-dominates $Y$: $v_i(X_i) \ge v_i(y_i)$ for every $i$;
- (b) every $X_i$ contains at most two picks of other agents;
- (c) if $X_i$ contains two picks of other agents, the move is a chain $(x_0, \dots, x_t)$, $i = x_j$ with
  $j \ge 1$, $y_{x_t} \in X_i$, and $i$'s step took $y_{x_{j-1}}$ with junk $H_j \subseteq J \cap R_i$ such that
  $v_i(y_{x_{j-1}}) + v_i(H_j) > p_i$.

*Proof.* (a) Movers strictly improve their bases, the others keep theirs, and completions only add goods. For (b)
and (c), count the foreign picks an agent can end with.
- A ring gives each member one other base (a single pick) plus junk, and releases no pick.
- An addition moves no base.
- In a chain, $x_0$ takes junk and possibly $y_{x_t}$, and each $x_j$ ($j \ge 1$) takes exactly $y_{x_{j-1}}$ plus
  junk. The only pick that can enter the pool is $y_{x_t}$.

So the completion can hand at most one pick, $y_{x_t}$, to anyone. An agent holds two foreign picks only if it is
some $x_j$ with $j \ge 1$ (holding $y_{x_{j-1}}$) that also receives $y_{x_t}$, and then $j \ne t$. Its step was
improving. ∎

**Corollary 11.2 (a certificate that one move fails; same source) [R].** Let $\mathcal T$ be the set of complete
EFX₀ allocations that value-dominate $Y$. Suppose every $T \in \mathcal T$ has an agent $i$ such that either $T_i$
contains three or more foreign picks, or $T_i$ contains exactly two, $P$ and $Q$, with
$v_i(P) + v_i(J \cap R_i) \le p_i$ and $v_i(Q) + v_i(J \cap R_i) \le p_i$. Then no single move, followed by any
completion, gives an EFX₀ allocation.

*Proof.* Such an allocation lies in $\mathcal T$ by (a). By (b) it avoids three foreign picks in one bundle. If the
blocked agent $i$ held two, (c) would give an improving step made of one of them plus junk inside $R_i$, which the
hypothesis forbids. ∎

*Use.* On instance 1 of Proposition 7.4, 6 of the 14 EFX₀ allocations value-dominate the picks. In all 6, agent 0
holds goods 2 and 5, which are the picks of agents 1 and 2. Agent 0 values its junk only at good 0 (worth 2), and
$4 + 2 \le 10$, $7 + 2 \le 10$. So Corollary 11.2 applies through agent 0. Given the list of six targets, a finite
computation, this is a human-checkable proof that one move fails there. The referee confirmed the corollary's
hypothesis on all 11 failing $n = 4$ cores, each time through a single agent (`k4/referee/ttc_t6.md`, own brute force
over all $n^m$ allocations). In the TTC session's words: a cycle serves unit demands, and agent 0's demand is for the
houses of two other owners.

**Referee report.** `k4/referee/ttc_t6.md`: CORRECT. Evidence: 141,215 (move, completion) pairs from 4,557 random
perfect starts satisfy (a)–(c), with 0 failures.

### 11.3 Completion at fixed bases

These are the exact tools for deciding whether a state has an S\* completion. They are stated for any state $B$ with
junk $J$.

**Lemma 11.3 (M; `k4/matching.md` §1, branch `proof/k4-matching`) [R].** Suppose (G1) no bundle of a non-holder
threatens anybody at base values, and (G2) no junk good is wanted. Fix an owner $o$, let $N_1$ be the holders other
than $o$ and $Q$ the other agents, and for $H \subseteq J$ put $X(H) = (B_o \cup J) \setminus H$. Let
- (H1)(H): no $q \in Q$ is threatened by $X(H)$ at $v_q(B_q)$;
- $E(H)$: the holders $u \in N_1$ threatened by $X(H)$ at $v_u(B_u)$ (*exposed*);
- $\Gamma(H)$: the bipartite graph on $H \times N_1$ with $h \sim u$ iff $u \notin E(H)$, or $u$ values $h$ and is
  not threatened by $X(H)$ at $v_u(B_u) + v_u(h)$.

Then for every $d \ge 0$, $B$ has an S\* completion with owner $o$ and $d$ dummy slots iff some $H \subseteq J$
satisfies (H1)(H), and $\Gamma(H)$ has a matching that covers $E(H)$ and has at least $|H| - d$ edges. So
$$\delta^*(B, o) = \min\{|H| - \nu(\Gamma(H)) : H \subseteq J,\ \text{(H1)}(H),\ E(H) \text{ coverable}\}.$$

*Proof.* `k4/matching.md` §1. (⇒) takes $H$ to be the junk given to holders or dummies. (⇐) gives $o$ the set
$X(H)$ and each matched holder its good: a holder's bundle is then at most two goods nobody wants, which threatens
nobody. The formula uses the Mendelsohn–Dulmage theorem. Lemma M is equivalent to the Hall session's Lemma 2\*
(Appendix B), and both are exact (`k4/oc1_hall.md` §23.1).

**Lemma 11.4 (EX\*; `k4/matching.md` §5) [R].** Let $P$ be an official chain from any state $B$, and $B'$ the state
after it, with junk $J'$. Fix an owner $o$. The slots of $B'$ are its holders other than $o$. Suppose (W′) every good
of $J'$ is unwanted at $B'$; (G1′) no multi-good bundle of $B'$ other than $o$'s threatens anybody; (1′) for some
$H \subseteq J'$, $X = B'_o \cup (J' \setminus H)$ threatens no non-holder other than $o$; and (2) the exposed slots
can all be matched to compensating goods of $H$, within a matching of all of $H$ into the slots. Then $B'$ has an S\*
completion owned by $o$.

*Proof.* This is Lemma 11.3 at $B'$: (W′) is (G2), (1′) is (H1), and (2) is the matching condition with $d = 0$. The
referee notes that Lemma M's (⇐) direction uses (G1) only for non-holders other than the owner, so (G1′) suffices.
∎

The earlier Lemma EX of `k4/matching.md` §3, a chain read as an exchange in the picks' slot graph, is also CORRECT,
but as a sufficient condition only: on an $n = 2$ instance, a state has an S\* completion that EX cannot certify
(`k4/oc1_hall.md` §23.1, `ex_not_exact.py`). EX\* contains EX.

**Lemma M^c (the compensated form; `k4/oc1max_multi.md` §9, branch `proof/k4-oc1max-multi` at `3d157f3`) [R].**
Let $B$ satisfy (G2), and fix an owner $o$. Write $b_i = v_i(B_i)$. In the *shape S^c*:
- $o$ takes the junk not handed out;
- every other agent with at most one base good takes at most one junk good. These are the holders $N_1$ and the
  *frozen singles* $F_1$;
- agents with two or more base goods take nothing.

For $H \subseteq J$ and a set $F_s \subseteq F_1$ of *frozen slots*, put $X = B_o \cup (J \setminus H)$. Let
$\tau_i$, the requirement of $i$, be the largest of:
- $b_i$;
- $\max_h v_i(B_q \setminus h)$ over the non-owner multi-good bundles $B_q$;
- $v_i(y_j)$ over the $j \in F_s$ whose good $i$ wants.

Agent $i \ne o$ is *needy* if $\tau_i > b_i$ or $X$ threatens $i$ at $b_i$. The graph $\Gamma^c(H, F_s)$ on
$H \times (N_1 \cup F_s)$ joins $h$ and $i$ iff $i$ is not needy, or $i$ values $h$,
$b_i + v_i(h) \ge \tau_i$, and $X$ does not threaten $i$ at $b_i + v_i(h)$. Then for every $d \ge 0$, $B$ has an
S^c completion with owner $o$ and $d$ dummy slots iff some $(H, F_s)$ satisfies all three of:
- (C1) every needy agent lies in $N_1 \cup F_s$;
- (C2) $v_o(X) \ge \tau_o$;
- (C3) $\Gamma^c(H, F_s)$ has a matching that covers every needy agent and has at least $|H| - d$ edges.

At a perfect start S^c is exactly the one-absorber shape, frozen slots included. So Lemma M^c decides one-absorber
completability there exactly.

*Proof.* `k4/oc1max_multi.md` §9. The core is a per-allocation claim: an S^c-shaped allocation is EFX₀ iff every
agent reaches its requirement and $X_o$ threatens nobody. (G2) is used exactly once there: a two-good bundle
$\{y_j, z_j\}$ with $z_j$ junk can threaten only through $y_j$. The rest is Lemma 11.3's matching argument. ∎

**Referee reports.** `k4/referee/matching.md` (Lemma M, Lemma EX: CORRECT), `k4/referee/lift.md` §1 (EX\*: CORRECT)
and `k4/referee/oc1max_multi.md` §9 (M^c: CORRECT). The last also has evidence: 391,846 owner tests against a raw
brute force over S^c-shaped allocations, with 0 mismatches.

### 11.4 One move with one dangerous agent

Here $D = \{k\}$ and the start is hard. The source is `k4/oc1_hall.md` §21 (branch `claude/k4-oc1-hall`, refereed
at `a14932d`). The proofs are given there in full, and are short applications of Lemma 2\*.

**Lemma 11.5 (D1-chain) [R].** $k$ has a canonical chain. If the picks form a maximum matching, the head of every
canonical chain holds a pick.

*Proof.* $k$ is frozen, so some $x_1$ wants $y_k$. While $x_i$ is frozen, some $x_{i+1}$ wants $y_{x_i}$. These
agents are distinct by (π), so the walk ends at an unfrozen agent. With a maximum matching, that agent lies on a
want-chain above a dangerous agent, so it holds a pick by Lemma 6.3 (2). ∎

**Proposition 11.6 (3′, the pool is improving) [R].** If $z$ is unfrozen at the picks, then
$v_k((J \cup B_z) \cap R_k) > p_k$. So every canonical chain from $k$ has an improving $H_0$.

*Proof.* Otherwise Lemma 2\* at the picks with owner $z$ and $H = \emptyset$ gives an S\* completion. A frozen
$q \ne k$ values no junk, so it meets $J \cup B_z$ only in $B_z$, worth at most $p_q$ since $z$ is unfrozen. That
contradicts hardness. ∎

**Lemma 11.7 (D1-red) [R].** Let $P$ be a canonical chain from $k$ with an improving $H_0$, and $a = y_{x_{t-1}}$ the
head's new good. Define the two obstacles at $B'$:
- **HEAD**: $x_t$ is frozen at $B'$ and threatened by $\Pi$ at $v_{x_t}(a)$;
- **CROWD**: some holder $u \ne k$ at $B'$ has $|H_0 \cap R_u| \ge 2$ and $v_u(H_0 \cap R_u) > v_u(B'_u)$.

$B'$ has an S\* completion owned by $k$ iff some $H \subseteq J'$ satisfies both (H1′) ($x_t$ is not frozen at
$B'$, or not threatened by $\Pi \setminus H$ at $v_{x_t}(a)$) and the condition that $H$ has distinct admissible
holders covering every crowded exposed holder. In particular, **if neither HEAD nor CROWD occurs, $B'$ has an S\*
completion owned by $k$**. Also, $x_t$ is frozen at $B'$ only if $a$ has a second wanter off $P$ at the picks, and
for a longest canonical chain that second wanter is unfrozen at the picks (Remark 2 there).

**Lemma 11.8 (D1-C₀, favourites) [R].** Let $z$ be unfrozen at the picks, $\Pi = J \cup B_z$, $\Pi_k = \Pi \cap R_k$.
For $u \notin \{k, z\}$ unfrozen at the picks and valuing a good of $\Pi$, let $b_u$ be its favourite good of $\Pi$.
(a) $|\Pi \cap R_u| \le 3$, and no $S \subseteq \Pi \setminus \{b_u\}$ threatens $u$ at $v_u(B_u) + v_u(b_u)$.
(b) If such agents $U''$ have pairwise distinct favourites, all in $J$, then
$v_k(\Pi_k \setminus \{b_u : u \in U''\}) > p_k$.

**Proposition 11.9 (D1-C′) [R].** Let $P$ be a canonical chain from $k$ without HEAD. Let $U'$ be the agents off $P$,
unfrozen at the picks, valuing at least two goods of $\Pi_k$, and suppose their favourites are pairwise distinct and
lie in $J$. Then some minimal improving $H_0$ avoids their favourites. Every such $H_0$ that does not both crowd the
head and contain $y_{x_t}$ leaves an S\* completion owned by $k$.

Where $k \le 4$ enters: $|\Pi \cap R_u| \le 3$ in Lemma 11.8, and "at most two junk goods" for the head in
Proposition 11.9.

**Theorem D1-C (`k4/d1.md` §3, branch `proof/k4-d1` at `a9232a0`, PR #113) [R].** Let the start be hard with
$D = \{k\}$, with every good relevant to some agent (true in cores). Let $P$ be a canonical chain from $k$ without
HEAD. Then some inclusion-minimal improving $H_0 \subseteq \Pi \cap R_k$ leaves a state with an S\* completion owned
by $k$.

*Proof.* `k4/d1.md` §3, by cases A-a to A-e and B. It uses Fact R: if $i$ holds one good and $Q$ is a set of at most
three goods, each worth at most $v_i(y_i)$, then every $h \in Q$ except possibly the strict minimum is *robust*,
$v_i(y_i) + v_i(h) \ge v_i(Q \setminus h)$. Here $k \le 4$ enters again. ∎

So the case $|D| = 1$ reduces to starts at which **every** canonical chain from $k$ has HEAD (§11.8, leaf 3b).

**Referee reports.** `k4/referee/oc1_hall_d1.md`: all five CORRECT. Evidence: 17,028 hard starts with $|D| = 1$ and
42,857 chains with every improving $H_0$; Lemma 11.7's "iff" has 0 mismatches against brute force. The same report
confirms instances 1 and 2 of Proposition 7.4 by brute force. `k4/referee/d1.md`: Theorem D1-C, with Fact R, Tool T
and Lemmas O, C3 and HC, CORRECT.

### 11.5 One move with several dangerous agents

The source is `k4/oc1max_multi.md` §2–§4, §6 (branch `proof/k4-oc1max-multi`, refereed at `6959fc9`, `1ccbb94` and
`d31a8f1`). Most statements are reductions: a chain *with a named property* repairs. The source says so itself
("Honest scope", §7). Theorem 11.13 is the exception.

**Lemma 11.10 (D-red) [R].** Let $P = (k, \dots, z)$ be a canonical chain from $k \in D$ with an improving
$H_0 \subseteq \Pi \cap R_k$, and owner $k$.
1. (G1) and (G2) hold at $B'$, and no agent other than $k$ wants a good of $\Pi$.
2. Every agent frozen at $B'$, other than $k$, is frozen at the picks or is $z$. An agent of $F \setminus D$, and any
   $d \in D \setminus (\Theta(z) \cup \{k\})$, is threatened by no subset of $\Pi$ at any value at least its pick
   value.
3. An exposed holder at $B'$ is $z$, an agent off $P$ unfrozen at the picks, or an agent of $D \setminus \{k\}$ that
   the chain unfroze. It is non-movable iff it is crowded by $H_0$.
4. So $B'$ has an S\* completion owned by $k$ iff some $H \subseteq J'$ satisfies (H1″) (no
   $q \in (D \setminus \{k\}) \cup \{z\}$ frozen at $B'$ is threatened by $\Pi \setminus H$ at $v_q(B'_q)$) and has
   distinct admissible holders covering every crowded exposed holder. In particular, $B'$ has one if none of HEAD,
   CROWD and **DEMAND** occurs, where DEMAND means that some $d \in D \setminus \{k\}$ is frozen at $B'$ and
   threatened by $\Pi$ at $v_d(B'_d)$ (and then $d \in \Theta(z)$).

The referee's wording fix is applied in item 2: the source's "a set holding one good it values never threatens it"
is false in general, and the correct reason is the bound $v_q(y_z) \le p_q$ from (U).

**Proposition 11.11 (T0) [R].** At a hard perfect start, $\Theta(z) \ne \emptyset$ for every unfrozen $z$ (null
agents included), and every $k \in \Theta(z)$ values $J \cup B_z$ above $p_k$. So a canonical chain from such a $k$
to $z$, if one exists, has an improving $H_0$.

*Proof.* If $\Theta(z) = \emptyset$, Lemma 2 at the picks with owner $z$ and $H = \emptyset$ gives an S\* completion
(the hypotheses are checked as in Proposition 11.6), contradicting hardness. ∎

*Corollary TR* (immediate from item 2): if $\Theta(z) \subseteq \{k\}$, DEMAND cannot occur on the chain, and only the
obstacles of §11.4 remain.

**Lemma 11.12 (KEEP) [R].** Let $P = (k, \dots, z)$ be a canonical chain with an improving $H_0 \subseteq J \cap R_k$
(the head's pick is not used). Suppose:
- (K1) some holder $u \ne k$ at $B'$ is admissible for $y_z$ against $J$;
- (K2) no holder at $B'$ is crowded by $H_0$;
- (K3) every frozen $q \in (D_T \setminus \{k\}) \cup \{z\}$ at $B'$ is unthreatened by $J$ at $v_q(B'_q)$.

Then $B'$ has an S\* completion owned by $k$ in which $u$ receives $y_z$. If $z$ is unfrozen at $B'$, (K1) holds with
$u = z$, because $v_z(J \cap R_z) < 2p_z < v_z(a) + p_z$: here $k \le 4$ enters, since $R_z \supseteq \{a, y_z\}$
leaves at most two junk goods.

**Theorem 11.13 (U, one truly dangerous agent) [R].** Let $Y$ be a hard perfect start with $D_T = \{k\}$ and $|D|$
arbitrary. Let $E_J$ be the set of receivers that $J$ threatens at their pick value. Let $P = (k, \dots, z)$ be a
*longest* canonical chain from $k$, and $H_0 \subseteq J \cap R_k$ any improving set. Suppose $E_J \subseteq \{z\}$,
and that $z$ is unfrozen at $B'$ if $z \in E_J$. Then $B'$ has an S\* completion owned by $k$. The owner's bundle is a
subset of $J$, and $y_z$ goes to $z$ or to an unfrozen second wanter of $a$.

*Proof* (`k4/oc1max_multi.md` §3).
- *The chain exists.* $k$ is frozen, so canonical chains from $k$ exist (Lemma 11.5), and so does a longest one. $J$
  threatens $k$, so an improving $H_0 \subseteq J$ exists.
- *A holder for $y_z$.* If $z$ is unfrozen at $B'$, take $u = z$, as in Lemma 11.12. Otherwise $a$ has a wanter $w$
  at $B'$, off $P$, that wanted $a$ at the picks. Then $w$ is unfrozen at the picks: otherwise the walk up from $w$
  would give a longer canonical chain, with distinct agents by (π). So $w$ is a receiver other than $z$, hence
  $w \notin E_J$. It is a holder at $B'$, unexposed against $J$, hence admissible. Take $u = w$. In this case
  $z \notin E_J$, so $J$ does not threaten $z$ at $v_z(a) > p_z$.
- *Lemma 2\* at $B'$ with owner $k$ and $H = \{y_z\}$.* Then the owner's remaining set is $J$. (H1) holds: $F \setminus D$
  values no junk, and each $d \in D \setminus \{k\}$ is pick-dangerous, so it is unthreatened by $J$ at its value
  after the chain, which is at least its pick value. The head is covered by the previous step. No exposed holder
  other than $u$ exists: an unfrozen agent off $P$ is exposed iff it lies in $E_J \subseteq \{z\}$, and a dangerous
  agent unfrozen at $B'$ would lie in $D_T$. ∎

**Corollary 11.14 (U1) [R].** OC₁ holds at every perfect start with exactly one receiver and exactly one truly
dangerous agent, whatever $|D|$ is, null agents allowed. Every longest canonical chain from $k$, with every improving
$H_0 \subseteq J$, repairs.

*Proof.* With one receiver $z$, every chain ends at $z$ and $E_J \subseteq \{z\}$. A wanter of $a$ at $B'$ would be a
second receiver, by the second step of the proof above, so $z$ is unfrozen at $B'$. ∎

Unlike the other lemmas of this section, Theorem 11.13 has a hypothesis about the start only, and the chain's
existence is part of the proof. So it proves OC₁ outright where it applies. On the multi session's 8,383 hard starts
that is 2,880 starts, 2,234 of them through Corollary 11.14 [E].

**Lemmas 11.15–11.17 [R]** (statements in `k4/oc1max_multi.md` §4 and §6).
- **Lemma 11.15 (SET).** For a canonical chain from $k$ with an improving junk pair $H_0 = \{g, g'\}$, and an
  S\*-shaped completion whose owner $o \notin \{k, x_1\}$ has a base that $k$ does not want, $k$ takes nothing,
  nobody strongly envies $k$, and $k$ strongly envies nobody. So these completions are exactly $X_k = H_0$ together
  with an EFX₀ S\* completion of the instance without $k$ and $H_0$. This uses $|R_k| \le 4$.
- **Lemma 11.16 (OWN, the overlap completion).** With $H_0 = \{g, g'\}$ as in Lemma 11.15, suppose the owner $o$
  has a *free base*: $o \notin \{k, x_1\}$, it holds at most one good, it is unfrozen at $B'$, and neither $k$ nor
  any agent frozen at $B'$ values that good. Suppose also (W1) that no frozen $d \in D_T \setminus \{k\}$ is
  threatened by $W = B'_o \cup (J \setminus H_0)$, and (W3) that some holder $u \ne o$ is admissible for $y_z$
  against $W$, with $z$ unthreatened by $W$ if it is frozen at $B'$. Then $B'$ has an S\* completion owned by $o$ in
  which $u$ receives $y_z$ and $k$ keeps exactly $H_0$. This is the owner of Lemma 7.7's completion, in general.
- **Lemma 11.17 (RING-red).** A *dangerous ring* from $k \in D$ is an ED chain $k \to x_1 \to \dots \to d$ ending at
  a dangerous agent $d$ that takes $y_{x_{t-1}}$ plus junk $H_t$, while $k$ takes $\{y_d\} \cup G$ with
  $G \subseteq J \setminus H_t$. No pick is released. If (R1) $d$'s bundle threatens nobody, (R2) no agent other
  than $k$ wants a good of $H_0$, (R3) $d$ and every other agent frozen at $B'$ is unthreatened by $H_0 \cup J'$, and
  (R4) no holder is crowded by $H_0$, then $B'$ has an S\* completion owned by $k$.

**Referee report.** `k4/referee/oc1max_multi.md`: D-red, T0, Corollary TR, KEEP (with Corollary KEEP-1), SET, OWN
and RING-red CORRECT; Theorem U and Corollary U1 CORRECT (§8 there). There are two wording fixes: the one applied in
Lemma 11.10, and $v_k(\ell) < p_k$ in OWN's case $q = k$. Evidence: 71,497 hard starts. Each lemma's hypotheses are
needed: dropping one gives failures (DEMAND: 865, CROWD: 332, HEAD: 79, (K2): 74, (K3): 399, (W1): 21). For Theorem
11.13, the mutations "any canonical chain, not only longest" (406 failures) and "drop $E_J \subseteq \{z\}$" (21)
show that both hypotheses are used.

**Theorem 11.18 (S, Theorem U with a junk good kept out; `k4/oc1max_multi.md` §10, branch `proof/k4-oc1max-multi` at
`b107719`) [R].** Let $Y$ be a perfect start, $k \in D$, $P$ a *longest* canonical chain from $k$ with head $z$ and
$a = y_{x_{t-1}}$, and $h \in J$. Put $W = (J \setminus \{h\}) \cup \{y_z\}$, and suppose:
- (S-a) $v_k(W) > p_k$;
- (S-b) $W$ threatens no agent of $D \setminus \{k\}$ at its pick value;
- (S-c) $W$ threatens no receiver other than $z$ at its pick value;
- (S-d) $z$ values no junk good other than $h$.

Then OC₁ holds at $Y$. The move is $P$ with any improving $H_0 \subseteq W$. In the completion, $h$ goes to $z$ if
$z$ is unfrozen after $P$, and otherwise to an unfrozen wanter of $a$. $k$ takes the rest, so its bundle is $W$, and
everyone else keeps its state good. Hardness is not assumed.

In the *relaxed form*, (S-d) is replaced by (S-d′): $W$ does not threaten $z$ at its value in that allocation. With
$h = y_z$, so that $W = J$, the relaxed form contains Theorem 11.13.

*Proof.* `k4/oc1max_multi.md` §10.
- *The move exists.* By Lemma 11.5 a longest canonical chain exists, and (S-a) gives an improving $H_0 \subseteq W$.
  Then $h \notin W \supseteq H_0$, so $h$ is junk after the chain, and $k$'s final bundle $H_0 \cup (J' \setminus
  \{h\})$ equals $W$.
- *The receiver of $h$ is a holder.* If $z$ is frozen after $P$, a wanter $w$ of $a$ is a receiver unfrozen after
  $P$, by the argument of Theorem 11.13.
- *EFX₀.* Only two bundles have two or more goods.
  - The receiver's pair $\{B'_r, h\}$ threatens nobody: $B'_r$ is unwanted, and $v_i(h) \le p_i$ by (I2).
  - $W$ threatens nobody, case by case: $z$ by (S-d) or (S-d′); $D \setminus \{k\}$ by (S-b); the other receivers by
    (S-c); $F \setminus D$ because those agents meet $W$ only in $y_z$, worth at most their pick; pickless agents
    because they are null. ∎

The *chain-level* form, Lemma HS, has three conditions: $z$ unfrozen at $B'$, $z$ admissible for $h$ against $W$, and
everyone else unthreatened by $W$. The source also proves HS-U1: with one receiver, the head of a longest chain is
unfrozen after it. Both are refereed with Theorem 11.18.

*Coverage* [E]. On the multi session's 8,383 hard starts with $|D| \ge 2$, Theorems 11.13 and 11.18 (relaxed, $h \in
J \cup \{y_z\}$) together prove OC₁ outright at 7,441 starts, which is 88.8%. That compares with 2,880 for Theorem
11.13 alone. Of the 585 SLOT starts (leaf 4d), 424 are covered. The referee reproduced all four counts.

**Referee report.** `k4/referee/oc1max_multi.md` §10: Theorem S (both forms), Lemma HS and HS-U1 CORRECT. Evidence:
205,634 tests over the data and random perfect starts, including every improving $H_0$ and every wanter, with 0
failures. Dropping the "longest" condition, (S-b), (S-c), or (S-d) together with (S-d′) each gives failures. One fix:
the source prints its smallest SLOT-residue instance, log613, with wrong values for agents 1 and 2. The data's values
make the narrative right. This draft does not print that instance.

### 11.6 The second move

The 11 failing $n = 4$ cores of Proposition 7.4 all need two moves, and on all of them the second move has one
shape: a first chain $P_1$ ends at the unique receiver $z$ and absorbs a danger pair shared with a second dangerous
agent, and a second chain $P_2$ ends at $z$ again. Write $B_1$, $B_2$ for the states after $P_1$ and $P_2$, and $J_1$,
$J_2$ for their junk.

**Lemma 11.19 (LIFT-red; `k4/matching.md` §6 at `0ee5969`) [R].** Assume:
- $Y$ is a perfect start and $z$ a holder of $Y$;
- $P_1$ is an official chain ending at $z$, with $|H_0^1| = 2$ and $H_0^1 \subseteq J \cup \{y_z\}$, in which the
  agents after the head take no junk;
- $z$ is a holder of $B_1$;
- $P_2$ is a canonical chain at $B_1$ ending at $z$, giving $z$ a single good;
- $P_2$'s head $h$ is not $P_1$'s head, and $B_2(h) = H_0^2$ is $h$'s improving set.

Then no bundle of $B_2$ other than $h$'s threatens anybody, and every junk good of $B_2$ is unwanted. So Lemma 11.3
applies at $B_2$ with owner $h$. In particular, giving $h$ the set $X = H_0^2 \cup J_2$ and keeping every other base
is EFX₀ iff $X$ threatens no agent $i \ne h$ at $v_i(B_2(i))$.

*Proof.* Values rise along both chains. Every good of $J$, of $H_0^1$, $y_z$ and $a = B_1(z)$ is unwanted at $B_2$:
junk by (I2), $y_z$ because $z$ is a holder of $Y$, and $a$ because $z$ is a holder of $B_1$. The other bundles are
single goods and the pair $H_0^1$, possibly moved one step along $P_2$. A single good, or a pair of unwanted goods,
threatens nobody. ∎

The condition that $P_1$'s agents after its head take no junk is needed: allowing middle junk gives 14 failures in
the referee's mutation test (`k4/referee/lift.md` §2, with an instance).

**Lemma 11.20 (LIFT-1, $k \le 4$; same source, extended at `7e6cd80`) [R].** Assume Lemma 11.19's hypotheses. Let
$t$ be $z$'s single good at $B_2$, $X = H_0^2 \cup J_2$, and $g$ $z$'s most valuable good of $J_2$ ($v_z(g) = 0$ if
$z$ values none). Suppose (L3): every agent other than $h$ and $z$ values at most one good of $X$.
- (a) If (L1) $z$ is unfrozen at $B_2$ and (L2′) $v_z(H_0^2 \cap R_z) \le v_z(t) + v_z(g)$, then giving $h$ the set
  $X \setminus \{g\}$, giving $z$ the set $\{t, g\}$, and keeping every other base is EFX₀, and S\*-shaped with
  owner $h$.
- (b) If (Lb) $v_z(X \cap R_z) \le v_z(t)$, then giving $h$ all of $X$ and keeping every other base is EFX₀.

*Proof* (`k4/matching.md` §6). Every good of $X$ is unwanted at $B_2$. Bundles other than $h$'s threaten nobody,
$z$'s $\{t, g\}$ included, by (L1). $X \setminus \{g\}$ does not threaten an agent $i \notin \{h, z\}$, by (L3). It
does not threaten $z$: write $A = H_0^2 \cap R_z$ and $G = J_2 \cap R_z$; then $|A| + |G| \le 3$ since $|R_z| \le 4$,
and $v_z(A) + v_z(G \setminus g) \le v_z(t) + v_z(g)$ case by case on $|A|$, using (L2′) when $|A| = 2$. In case (b),
$z$ keeps the singleton $\{t\}$, which threatens nobody even if $t$ is wanted, and (Lb) says $X$ does not threaten
$z$. ∎

The source calls $t$ "$z$'s favourite good". The referee shows that this is not needed: every good of $X$ is junk,
$y_z$ or $a$, and each is worth less than $t$ to $z$. The referee refereed the first version, with
(L2): $v_z(H_0^2 \cap R_z) \le v_z(t)$ and case (a) only, and then the extension (`k4/referee/lift.md` §7). A mutation
that drops (L2′) gives 26 failures, so the condition is needed.

**Lemma 11.21 (LIFT, the second move as a move of a smaller instance; `k4/oc1max_multi.md` §8) [R].** Let $B$ be a
state, and $k$ an agent holding a pair $T$ such that every other agent with a relevant good values each good of $T$
below its value at $B$. Let $I^-$ be the instance without $k$ and $T$, and $B^-$ the restriction of $B$.
1. Every official move of $I^-$ from $B^-$ is an official move of $I$ from $B$ that leaves $k$'s bundle unchanged.
2. If $C^-$ is reached from $B^-$ by official moves of $I^-$, and $X^-$ is a one-absorber completion of $C^-$ in
   which no bundle threatens $k$ at $v_k(T)$, then $X^-$ together with $X_k = T$ is a one-absorber completion in $I$.

The hypothesis holds after a canonical chain whose improving set is a junk pair, by (I2).

**Referee report.** `k4/referee/lift.md`: EX\*, LIFT-red, LIFT-1 (both versions) and LIFT CORRECT. Evidence: 8,413
$(P_1, P_2)$ pairs for LIFT-red and about 9,900 constructions for LIFT-1, with 0 failures; 573,538 lifted completions
for LIFT.

These lemmas are conditional, and the refutation of LIFT-SHAPE⁺ at $n = 5$ (§11.9) does not touch them. At $n = 4$
they turn the second move into a statement about where goods sit and a few value comparisons, certified on every
start (Proposition 11.26 item 6). At $n = 5$ the second chain can avoid $z$. The general mechanism is Lemma 11.21's
recursion: settle one sharer, then make one move in $I^-$. The next two results prove that mechanism.

**The earliest-wanter chain.** Let $Y$ be the SD outcome of the order $\sigma$, and $k$ frozen. $E(k) = (k = x_0, x_1,
\dots, x_t = z)$ takes $x_l$ to be the $\sigma$-earliest wanter of $y_{x_{l-1}}$, and stops at the first agent $z$
whose pick nobody wants. A wanter of $y_j$ picks after $j$, so $\sigma$ increases along $E(k)$. Hence $E(k)$ is a
canonical chain, and it exists for every frozen $k$.

**Lemma 11.22 (SD-E; `k4/oc1max_multi.md` §12 at `6c3fd95`) [R].** Let values be strict, $Y$ a perfect start, and
$T \subseteq J \cup \{y_z\}$. Let $B_1$ be the state after $E(k)$ in which $k$ takes $T$ (each $x_l$ holds
$y_{x_{l-1}}$, and everyone else keeps its pick). Let $I^-$ be the instance without $k$ and $T$. Then $B_1$ restricted
to $I^-$ is the SD outcome of $\sigma$ with $k$ deleted, and it is a perfect start of $I^-$.

*Proof.* Write $b_a$ for $a$'s good at $B_1$. Run $\sigma \setminus k$ in $I^-$. By induction, every agent $a$ takes
$b_a$.
- $b_a$ is available at $a$'s turn: only $a$ holds it, and $b_a \notin T$ since it is a pick other than $y_z$.
- Suppose $a$ preferred an available good $g$ to $b_a$, so $v_a(g) > v_a(b_a) \ge p_a$.
  - $g$ is not junk of $I$, since junk was available at $a$'s turn in $\sigma$.
  - $g$ is not $y_z$: $y_z$ is unwanted, and $z$'s new value exceeds $p_z$.
  - So $g = y_j$, a pick that $a$ wants. Then $\sigma(j) < \sigma(a)$. Its holder at $B_1$ comes after $a$, and is $j$
    itself unless $j = x_l$, when it is $x_{l+1}$. It cannot be $j$, so $\sigma(x_l) < \sigma(a) < \sigma(x_{l+1})$
    and $a$ wants $y_{x_l}$. That contradicts the choice of $x_{l+1}$ as the earliest wanter. ∎

Without the perfect-start hypothesis the conclusion can fail. The referee's example: $v_0 = \{0: 9\}$,
$v_1 = \{0: 5, 1: 4\}$, $v_2 = \{0: 1\}$, $\sigma = (0, 1, 2)$, where $E(0) = (0, 1)$ leaves agent 2 pickless while
it values good 0.

**Theorem 11.23 (REC-S, OC₂ by settling a sharer; same source) [R].** Let values be strict, $Y$ a perfect start,
$k \in D$, and $T \subseteq (J \cup \{y_z\}) \cap R_k$ an improving pair for $E(k)$. Suppose:
- (R) in $I^-$ at $B_1^-$, some $(k', P', h)$ satisfies Theorem 11.18 in its relaxed form, with
  $h \in J^- \cup \{y_{z'}\}$ (this includes Theorem 11.13);
- (K) no bundle of the resulting allocation $X^-$ threatens $k$ at $v_k(T)$.

Then OC₂ holds at $Y$. The repair is $E(k)$ with $k$ taking $T$, then the chain $P'$, then the completion $X^-$ with
$X_k = T$.

*Proof.* $B_1^-$ is a perfect start of $I^-$ (Lemma 11.22). Theorem 11.18, which needs no hardness, gives $P'$ and the
EFX₀ S\* completion $X^-$. By Lemma 11.21 (1), $P'$ is an official move of $I$ that leaves $k$'s bundle unchanged.
Lemma 11.21's hypothesis holds automatically here: every $i \ne k$ with a pick values each good of $T$ below $p_i$
(junk by (I2); $y_z$ is unwanted; and $v_z(y_z) = p_z < v_z(a)$), and values only rise. So by Lemma 11.21 (2) with
(K), $X^- \cup \{k : T\}$ is a one-absorber completion in $I$. ∎

The source states a third hypothesis, (L), which is Lemma 11.21's hypothesis. The referee showed it is implied by
strictness, the perfect start and $T \subseteq J \cup \{y_z\}$, and it is omitted here. (K) is genuine: it fails
at 188 of 6,065 random Theorem S cases, and each allocation where it fails is not EFX₀. Strictness and the
earliest-wanter choice are both needed, by the referee's mutations.

*Example* (checked in Appendix C). On instance 1 of Proposition 7.4, $E(2) = (2, 1)$ with agent 2 taking
$T = \{3, 4\}$ is followed in $I^-$ by the chain $(0, 1)$ of Theorem 11.18 with $h = 0$ kept out for agent 1. The
final allocation $(\{2, 5\}, \{0, 1\}, \{3, 4\}, \{6\})$ is EFX₀.

*Coverage.* REC-S repairs all 12 known OC₁^max failures, the 4,955 walk failures near them, and 23,943 rows of the
matching session's $n = 5$ walks, including 5_pure #164 [E]. At $n = 4$ it repairs every start with no one-move
repair [Cert] (Proposition 11.26 item 8). Its existence part, that some $k \in D$ and some pool pair $T$ of $E(k)$
meet (R) and (K), **fails at $n = 5$**: on the certifier's first $n = 5$ chunk, REC-S repairs 273 of the 280 sampled
two-move starts (below). OC₂ holds at all 280 by other mechanisms.

**Referee report.** `k4/referee/oc1max_multi.md` §11: Lemma SD-E, Theorem REC-S and Lemma LIFT CORRECT, with the
remarks above.

**Iterated reduction** (`k4/matching.md` §6 at `8498cde`, branch `proof/k4-matching`). A *reduction step* at a perfect
SD start of the current instance $I'$ is:
- a canonical chain from an agent $k$ that is dangerous in $I'$, with $k$ taking an improving
  $T \subseteq (J' \cup B_{\text{end}}) \cap R_k$;
- (L\*): $T$ threatens no other agent of $I'$ at its value after the chain;
- deleting $k$ and $T$ leaves a perfect SD outcome of $I' - k - T$.

**RSD** repairs a start if some sequence of reduction steps reaches a state whose one-absorber completion *lifts*: the
deleted agents keep their sets and receive nothing, the absorber is a present agent, and the result is raw EFX₀ in
$I$. REC-S is RSD with one step and a Theorem S completion. Two refereed lemmas make RSD a proof device.

**Lemma 11.24 (LIFT\*, the iterated lift; same source) [R].** Let $I_0 = I$ and $I_j = I_{j-1} - k_j - T_j$ for
reduction steps $j = 1, \dots, r$, each with (L\*). Let $X$ be an EFX₀ allocation of $I_r$ that extends the last
state. Suppose (Φ): no bundle of $X$, and no $T_j$ with $j > i$, threatens $k_i$ at $v_{k_i}(T_i)$. Then $X$ together
with all the $T_j$ is EFX₀ in $I$.

*Proof.* Values never fall along the process: a step changes only its chain agents, which gain, and $k_j$, which
gains; the completion only adds goods. EFX₀ for an agent is monotone in its own value. Take agents $a \ne b$.
- If both are present in $I_r$, $X$ is EFX₀ there, and their bundles hold only goods of $I_r$.
- If $a = k_i$: a bundle of $X$, or $T_j$ with $j > i$, is covered by (Φ). For $T_j$ with $j < i$, $a$ was present
  at step $j$, so by (L\*) $T_j$ did not threaten it then, nor later.
- If $b = k_j$ and $a$ was present at step $j$, the same argument applies. ∎

It uses nothing about $k$ or $|T|$, and it does not claim that the moves are official in $I$, which matters only for
counting moves.

**Lemma 11.25 (PHANTOM; same source; $|R_k| \le 4$) [R].** Let $k$ hold $T \subseteq R_k$ with $v_k(T) > v_k(y)$,
where $y \notin T$ is its former pick, and let $X$ be a bundle disjoint from $T$.
1. If $|T| = 3$, $X$ never threatens $k$.
2. If $|T| = 2$ and $R_k = T \cup \{y, \ell\}$, $X$ threatens $k$ exactly when (P1) $\ell \in X$, $|X| \ge 2$ and
   $v_k(\ell) > v_k(T)$, or (P2) $\{y, \ell\} \subseteq X$, $|X| \ge 3$ and $v_k(y) + v_k(\ell) > v_k(T)$.

*Proof.* $X \cap R_k \subseteq R_k \setminus T$. If $|T| = 3$ this is at most $\{y\}$, and $v_k(y) < v_k(T)$. If
$|T| = 2$, go by cases. A singleton, or $X \cap R_k = \emptyset$, gives threat 0. $X \cap R_k = \{y\}$ gives at most
$v_k(y)$. $X \cap R_k = \{\ell\}$ with $|X| \ge 2$ gives $v_k(\ell)$, since another good of $X$ is worth 0. $X =
\{y, \ell\}$ gives $\max(v_k(y), v_k(\ell))$. $X \supsetneq \{y, \ell\}$ gives $v_k(y) + v_k(\ell)$. ∎

So an induction through reduction steps must carry, for each deleted agent with $|T| = 2$, at most two *phantom
constraints* on the rest: "$\ell$ is alone in its bundle" and "$y$ and $\ell$ are not together in a bundle of three or
more goods". It carries none for $|T| = 3$.

**Referee report.** `k4/referee/lift.md` §8: LIFT\* and PHANTOM CORRECT. PHANTOM's prediction equals the raw threat
test in 677,280 tests on the witnesses' deleted agents and 258,691 random tests, with 0 mismatches.

*RSD on the data.*
- At $n = 4$, RSD repairs every one of the 112,880 two-move starts in two steps [Cert] (Proposition 11.26 item 9). The
  sets $T$ must be allowed three goods: with pairs only, 7,680 starts have no RSD repair.
- RSD must choose its steps. From 16,240 of the $n = 4$ starts, some sequence of steps reaches a *dead end*: a state
  with no lifting completion and no reduction step. The referee reproduced this count.
- **RSD-IND, the matching session's inductive form, is false.** It said that a start carrying phantom constraints
  from earlier steps either completes or has a reduction step after which the hypothesis holds again.
  - As written it fails at its own dead ends, which satisfy its hypothesis (`k4/referee/lift.md` §8).
  - Its existential intent fails at $n = 5$ too [V]. At two of the certifier's sampled starts, 5_pure #419
    ($m = 10$) and #447 ($m = 11$), no RSD sequence of any depth repairs (§11.9).
- What survives is the *deferred* form, **Conjecture RSD-D** [C]: steps without (L\*), with (L\*) read at the final
  values, and with *demands* carried alongside the phantom constraints. A present agent $i$ threatened by a deleted $T$
  must end with value at least $v_i(T) - \min_{g \in T} v_i(g)$. Lemma 11.24 holds for RSD-D with (L\*) read at the
  final values.
- The matching session's *ROUND-RSD* [C], under test, applies a round of simultaneous settlements, deletes the settled
  agents and their sets, and recurses. If it holds, it unifies the second move with the disjoint repairs of §11.9.

*The certifier's first $n = 5$ chunk* (`k4/matching.md` §6). The 280 sampled two-move starts of chunk 5_pure_s5o0
(up to three per hypergraph, from the 137 of its 935 hypergraphs that have one) are a sample, not an enumeration
[E]. Every one is hard and has exactly one receiver. Mechanisms that repair them:

| mechanism | starts repaired, of 280 |
|---|---|
| CM₂ (a first move, then a Lemma 11.4 exchange) | 280 |
| ROUND-P (one round of at most two disjoint OC₁′ moves; the coordinator's `roundp_check.py`) | 280 (one move at 234, two at 46) |
| RSD-D (two deferred steps) | 280 |
| RSD | 278 |
| OC2-REC (two implementations) | 274, 276 |
| REC-S (Theorem 11.23) | 273 |
| LIFT-SHAPE⁺ | 132 |

RSD's two failures are #419 and #447, which also defeat OC2-REC and REC-S. One start (5_pure $m = 9$, #38) fails
only REC-S, and every other failure of OC2-REC or REC-S is repaired by RSD. Of the 280, 240 have a vertex-disjoint
repairing pair of moves and 40 do not. Lemma 11.4 (EX\*) is no longer exact on the second move at $n = 5$, because a
junk good can be wanted after the first move.

### 11.7 Finite certificates

**Proposition 11.26 (certified at $n \le 4$; `k4/oc1cert.md` and `results/k4_oc1max/`, branch
`compute/k4-oc1max-cert` at `dcd2098`; `k4/matching.md` §6; `k4/oc1max_multi.md` §12) [Cert].** For every strict profile of every core hypergraph:
1. **OC₁^max** holds for all $n \le 3$ (56 hypergraphs) and for 991 of the 1,002 with $n = 4$. It fails on 11
   (§7.3).
2. **OC₂^max** holds for all $n \le 4$ (1,058 hypergraphs; §7.3). At $n = 5$ it is certified so far on 3,605 of the
   31,584 cores: list 5_n4_1 (1,735 cores) and chunks 5_pure_s5o0 and 5_pure_s5o1 (935 each). Each chunk has an
   independent check (`results/k4_oc1max/n5/*_check.log`, branch `compute/k4-oc1max-cert` at `7516064`; the coordinator's
   count in `k4/attack_log.md` on main). No start needing three moves has been found.
3. **The some-order form OC₁^∃max** holds for all $n \le 4$: some SD order whose picks form a maximum matching
   satisfies OC₁. On the 991 cores it follows from item 1 and Lemma 6.2. On the 11 failing cores an ∃-CEGAR over
   types (`k4/oc1cert/exists.py`) certifies it (`results/k4_oc1max/exists_4_fail11.json.gz`). An independent checker
   (`check_exists.py`) re-checks it with its own types, its own SD per order, its own move rules and raw EFX₀.
4. **Every $n = 4$ failing start is known.** There are exactly 112,880 (type profile, picks) pairs without a
   one-move repair, on the 11 hypergraphs. They are exported in `results/k4_oc1max/two_move_starts_n4.json.gz`, and
   `check.py` with these pairs excluded confirms that every other pair is covered.
5. **R2 at $n = 4$**: each of the 112,880 has exactly one receiver. So "two or more receivers imply one move" holds
   at $n = 4$. It fails at $n = 5$ (ledger K4.SDC.R2.N5; §11.10). More precisely, **R2-C** holds: at every hard perfect start with at least two receivers, some canonical
   chain (from a dangerous $x_0$, with $x_1$ wanting $y_{x_0}$) ending at a receiver is followed by a one-absorber
   completion (`results/k4_oc1max/cert_4_r2c.json.gz`, checked by `check.py` with `OC1_R2=c`). The stronger forms
   with a prescribed owner fail at $n = 4$ [V]:
   - **R2-M** (Lemma M^c's shape with owner $x_0$, at most one junk good each) fails on 306 of the 1,002 cores;
   - **R2★** (no owner: nobody takes two junk goods) fails on 230;
   - **R2-O** and **R2-O′** (another receiver owns) fail on 9.

   Each failure set was found by the CEGAR, re-checked by the independent checker, and sampled by a raw brute force
   (`k4/oc1cert/verify_r2.py`: 20 R2-M failures verified, 5 of them also R2★ failures; all 9 R2-O failures). The
   referee confirmed the R2-M refutation at all 306 listed starts, of which 74 also refute R2★, and R2 holds at all
   of them (`k4/referee/r2m.md`). This write-up's checker confirms the first R2-M failure (Appendix C). The
   earliest-wanter form R2-E fails too, on 273 cores. So no single owner rule survives at $n = 4$. In
   one R2-O example the owner must be the other receiver, and in another it must be $z$ or $x_0$
   (`k4/oc1_hall.md` §24.1).
6. **LIFT-SHAPE⁺ at $n = 4$** (ledger row K4.MATCH.LIFT.N4, branch `proof/k4-matching`): each of the 112,880 has
   the two-chain shape of §11.9 item 7, 109,680 through LIFT-1's case (a) and 3,200 through its case (b). A
   self-contained checker re-verifies every witness allocation from the raw definitions
   (`k4/matching/check_lift_n4.py`).
7. **OC₁′^max** (`k4/oc1cert.md` at `46a9006`, ledger row K4.SDC.OC1PMAX.N4 there) holds for every strict profile of
   every core with $n \le 4$. OC₁′ is the move of `kgen/rounds.md` §4.6: as in OC₁, except that every chain agent
   other than the end may also take goods of the end's base. The certificate is checked by `check.py` with
   `OC1_PRIME=1`, and the move generator agrees exactly with the rounds session's own on 400 random starts. At
   $n = 5$ it fails: 24 of the first 137 $n = 5$ OC₁^max failures in list 5_pure have no OC₁′ repair, rings included,
   each verified by the rounds session's raw brute force (`results/k4_oc1max/oc1prime_cex_n5_verify.log`). 13 of them
   are in the MC2 class, and all are perfect starts. One is the start of §11.9 (5_pure #164). The coordinator and a
   third implementation agree on it, and so does this write-up's checker, where the wider rule adds no chain state
   beyond the ordinary ones (Appendix C).
   - **The referee confirmed both halves** (`k4/referee/oc1prime.md`). At 5_pure #164, none of the 21 OC₁′ move states
     completes, 9 EFX₀ allocations value-dominate the picks, and two moves repair. At $n = 4$, OC₁′ holds at all
     112,880 exported starts, by a third implementation. The all-cores claim is correct conditional on the
     certifier's export.
   - **The mechanism is two disjoint conflicts** (`k4/sdc.md` §31). Every one of the 9 value-dominating EFX₀
     allocations swaps agents 0 and 1 and also upgrades agent 3, whose pick is worth 2 to it. One chain or ring fixes
     only one of the two. One round of two vertex-disjoint moves fixes both, for example the ring $0 \leftrightarrow 1$
     with junk 0 and 1 and the ring $3 \leftrightarrow 4$ with junk 6 (Appendix C). 12 of the 20 two-move repairs are
     such disjoint pairs.
   - So a one-step candidate at $k = 4$ must allow disjoint moves. **ROUND-P^max** is one round of vertex-disjoint
     chains, in which every non-end agent may also take goods of an end's base (`kgen/rounds.md` §4.9; ledger row
     K4.SDC.ROUNDP). It contains OC₁′ and the plain round. It holds at all 112,880 $n = 4$ two-move starts, where one
     plain round fails at every one, and at all 280 sampled $n = 5$ two-move starts [E]. The $n = 4$ count is from two
     implementations that agree on 1,256 cross-checked starts. The narrowest form, a round of disjoint OC₁′ moves,
     is never separated from it on the data.
   - *Is REC-S's repair one ROUND-P round?* On the data, yes: at all 112,880 $n = 4$ starts, REC-S's final allocation
     is a one-round witness, with a single chain on the agents of $E(k)$ and the second chain. The rounds session's
     sketch of why the two moves always splice has a **gap**, found by the referee (`k4/referee/rounds_r1.md`,
     addendum; row 43). Step 2 fails when the second chain's head releases $y_k$ and the completion puts it on an
     agent that keeps its own pick. Then $X$ is no round witness, even in the wide form. There is an $n = 4$, $m = 8$
     instance, and 71 of 13,608 random configurations fail this way. ROUND-P still holds at all 71. The repaired
     statement, Lemma SPLICE, is refereed CORRECT WITH TWO SMALL FIXES. A REC-S repair is one round of OC₁′ moves
     exactly when an explicit configuration (EX) does not occur (§11.10).
9. **RSD at $n = 4$** (ledger row K4.MATCH.RSD.N4, branch `proof/k4-matching`). Two reduction steps and a lifted
   one-absorber completion repair every one of the 112,880 starts. The sets $T$ have sizes (2, 2) at 103,600 starts
   and (2, 3) at 9,280. The session's `check_rsd.py` verifies the witnesses. The referee re-validated all 112,880 with
   its own code, including that every step is an official move of the full instance (`k4/referee/lift.md` §8,
   CONFIRMED).
8. **REC-S at $n = 4$** (ledger row K4.MULTI.RECS.N4, branch `proof/k4-oc1max-multi`). Theorem 11.23's mechanism
   repairs every one of the 112,880 starts. For each, a witness gives an order, $k$, $E(k)$, $T$, the chain $P'$ with
   its sets and $h$, and the final allocation (`recs_witnesses_n4.json.gz`). `check_recs.py` checks every witness
   from the definitions and imports nothing from the workstream; it rejects all 8,241 mutated witnesses, and it
   matches the witness starts to the export as a multiset. The referee re-validated every witness with its own code,
   each a genuine Theorem 11.18 case with (K) (`k4/referee/oc1max_multi.md` §12, CONFIRMED).

Items 1–5 are not refereed, except the refutations in item 5. The referee did re-check, as evidence, the 11 counterexamples (including ordinality
under perturbation) and 66,080 sampled starts against the depth-2 certificate, with 0 disagreements
(`k4/referee/oc1cert.md`). The referee re-verified items 6, 7 (OC₁′), 8 and 9 at every exported start, each with its own code
(`k4/referee/lift.md` §7–§8, `oc1prime.md`, `oc1max_multi.md` §12). Their completeness rests on item 4.
- Item 3 makes the some-order form (Conjecture 12.2) a certified statement at $n \le 4$.
- Items 5, 6 and 8 confine every $n = 4$ two-move start to one receiver and one shape.
- Item 8 gives OC₂^max at $n = 4$ an explicit mechanism whose every step is refereed: Lemma 11.22, Lemma 11.21 and
  Theorem 11.18.

### 11.8 The case tree

Each leaf is a named statement. Its status uses this draft's labels, and the owner is the session whose branch
holds it. Leaves 1–4 are the one-move side, and leaf 5 is the second move.

| leaf | case | statement | status | owner |
|---|---|---|---|---|
| 0 | maximum-matching start ⟶ perfect start | Lemma 12.3 (RED) with Lemma 6.3 (MAX) | [R] (RED refereed as RED₃; part machine-checked, `EFX.OC1Max.red`) | coordinator; Hall |
| 1 | the picks complete, or a state completes | Lemma 1 (slots), Lemma 2\*, Lemma 11.3 (M), Lemma 11.4 (EX\*), Lemma M^c | 2\*, M, EX\*, M^c: [R]. Lemma 1: [W] | Hall; matching; multi |
| 2 | a hard start has $D \ne \emptyset$ | Proposition 11.11 (T0) | [R] | multi |
| 3 | $\|D\| = 1$: one move | Lemmas 11.5, 11.7, 11.8, Propositions 11.6, 11.9 | [R] | Hall |
| 3a | $\|D\| = 1$, CROWD residuals C-a to C-c | D1-C via Lemmas C3 and HC (needs every good relevant) | [R] | k4-d1 (`k4/d1.md` §3, PR #113) |
| 3a′ | $\|D\| = 1$, CROWD in general | Theorem D1-C (§11.4): every canonical chain without HEAD has a minimal repairing $H_0$ | [R] | k4-d1 |
| 3b | $\|D\| = 1$, every canonical chain has HEAD | D1-H2: some canonical chain, or its extension through the other wanter of $a$, repairs with owner $k$. Proposition D1-H₃′: D1-H2 on all 763 three-agent core structures. Lemma CONTRACT ($t = 1$): without extra active agents or a third wanter, the start reduces to the three-agent core | D1-H₃′, CONTRACT: [W], computer-verified (SMT, two encodings; the referee sampled 6,818 three-agent cores of the earlier D1-H₃, 0 failures). The route through S2 is closed: **S2 is false** (S2-X). **OPEN: extra active agents or a third wanter, and $t \ge 2$** | k4-d1 (`k4/d1.md` §7) |
| 4 | $\|D\| \ge 2$ after a canonical chain | Lemma 11.10 (D-red): the obstacles are HEAD, CROWD, DEMAND | [R] | multi |
| 4a | the head has $\Theta(z) \subseteq \{k\}$ | Corollary TR: no DEMAND, so leaf 3 applies | [R] | multi |
| 4b | one truly dangerous agent | Theorem 11.13 (U), Theorem 11.18 (S), Lemma 11.12 (KEEP), Corollary KEEP-1; residue KEEP-C | U, S, KEEP, KEEP-1: [R]. U and S together prove OC₁ outright at 7,441 of the 8,383 data starts. **OPEN: KEEP-C** (8 starts in the data) | multi |
| 4c | $k$ takes a shared junk pair | Lemmas 11.15 (SET), 11.16 (OWN) | [R] | multi |
| 4d | several truly dangerous agents, or DEMAND with none | SLOT: one or two slots, the head's among them, cover what the chain leaves | Theorem 11.18 covers 424 of the 585 SLOT starts [R]. **OPEN: SLOT2**, the 161 left, which need two or three slots | multi |
| 4e | the head is a second dangerous agent | Lemma 11.17 (RING-red); residue RING2 | RING-red: [R], covers 151 starts. **OPEN: RING2** (45 starts left; every one is repaired by a move of length at most 3) | multi |
| 4f | disjoint danger sets | one chain repairs when no two dangerous agents share a pool danger set | [E]: 7,755 starts without sharing, all one move | multi |
| 5 | no one-move repair: the second move | Theorem 11.23 (REC-S); its iteration RSD (Lemmas 11.24, 11.25); or a round (item 4a) | REC-S, LIFT\*, PHANTOM: [R]. REC-S and RSD certified at $n = 4$ on every start (Proposition 11.26 items 8–9). REC-S existence **fails at $n = 5$** (7 of 280 sampled starts), and RSD at 2 of them. **OPEN: RSD-D or ROUND-RSD** | multi; matching |
| 5a | the shape of a two-move start | R2: two or more receivers imply one move; R2-C: by a canonical chain to a receiver. Lemmas R2-0, R2-G2. LIFT-SHAPE⁺ | R2, R2-C: [Cert] at $n \le 4$ (Proposition 11.26 item 5). R2-M, R2★, R2-O: **refuted at $n = 4$** [V]. R2-0, R2-G2: [W]. **OPEN: R2-C in general.** LIFT-SHAPE⁺: [Cert] at $n = 4$, **refuted at $n = 5$** | TTC (R2); matching, multi |
| 5b | SHARE₂ (ii), route M | Lemmas 11.19 (LIFT-red), 11.20 (LIFT-1) | [R]; they settle every $n = 4$ start, but at $n = 5$ their shape can be absent | matching |
| 5c | SHARE₂ (ii), route R | Lemma 11.21 (LIFT) with Lemma 11.22 (SD-E); Lemma 11.24 (LIFT\*) for several steps | [R] | multi; matching |
| 5d | a wider single move, or one round, instead | OC₁′; ROUND-P: one round of disjoint chains whose non-end agents may take an end's goods | OC₁′: [Cert] at $n \le 4$, **refuted at $n = 5$** [R]. ROUND-P^max: [E], holds at all $n = 4$ two-move starts and all 280 sampled $n = 5$ ones. The sketch that REC-S's two moves splice into one round had a gap. Lemma SPLICE, refereed, is exact up to a configuration (EX) | kgen-rounds; certifier |
| 6 | three moves needed? | three sharers of one pool pair with no slots | none found. OC₂^max: [Cert] at $n \le 4$, [E] on the first ~700 pure $n = 5$ cores; a targeted search runs at $n = 5$–7 | certifier |

> **Sub-lemma SHARE₂ (`k4/oc1_hall.md` §23.2) — (ii) false as stated at $n = 5$; the route-R form is OPEN.** Let $Y$ be a hard perfect start ($k \le 4$, strict) with no
> one-move repair.
> - (i) *Shape.* $Y$ has exactly one receiver $z$. Some dangerous $k$ has a canonical chain $P_1$ to $z$ whose
>   $H_0 = T \subseteq J \cup \{y_z\}$ is improving for $k$ and for a second dangerous agent.
> - (ii) *Second move.* At $B_1$, some canonical chain $P_2$ ends at $z$ and gives $z$ its favourite good, and the
>   state after $P_2$ has a one-absorber completion in which $k$ keeps exactly $T$.

Route M certifies (ii) by Lemmas 11.19 and 11.20 at $B_2$. Route R certifies it in $I^- = I - k - T$ by Lemma 11.21.
At $n = 4$ both produce the same $P_2$. **At $n = 5$, (ii) as stated fails** (§11.9 item 7): after every first chain
ending at $z$, no second chain ending at $z$ with $z$'s favourite good leaves a completable state. That start is
repaired by a second chain disjoint from the first. What survives is (i) together with the route-R form of the second
move, now proved as Theorem 11.23 up to existence (§11.9 item 7). The one-move alternative OC₁′ (leaf 5d) fails at $n = 5$, so leaf 5 is
needed.

**Two short lemmas of leaf 5a** (`k4/ttc.md` §14.6, branch `claude/k4-ttc`) [W]. They are not refereed. The proofs
are the source's, and this write-up checked them.
- *Lemma R2-0.* At a perfect start with $|J| \le |U|$, $U$ the receivers, the picks have a completion in which every
  agent receives at most one junk good. *Proof.* Give the junk goods to distinct receivers. Removing $g$ from
  $\{y_u, g\}$ leaves $y_u$, and $v_i(y_u) \le p_i$ since $u$ is unwanted. Removing $y_u$ leaves $g$, and
  $v_i(g) < p_i$ by (I2) if $i$ values $g$. Singletons are never strongly envied. ∎
- *Lemma R2-G2.* After any chain from a perfect start whose end $z$ is a receiver, no junk good is wanted. *Proof.*
  The new junk is $J \setminus H_0$ and possibly $y_z$. Junk is worth at most $p_i \le v_i(B'_i)$ by (I2). For
  $i \ne z$, $v_i(y_z) \le p_i$ since $z$ was a receiver, and $z$'s step was improving. ∎

So, by Lemma M^c, R2 would follow from the matching statement R2-M. R2-M is refuted at $n = 4$ (Proposition 11.26
item 5), and the target is now R2-C (§11.9 item 6).

### 11.9 The open core: a two-part plan

Everything not listed here is refereed, certified or written in the tree above. The Hall session's integration
(`k4/oc1_hall.md` §24, branch `claude/k4-oc1-hall` at `565f029`) restates what remains as a plan in two parts for
OC₂^max at a hard perfect start ($k \le 4$, strict values, every good relevant). Each item below is **OPEN**. "Data"
means the sessions' finite data, which are evidence [E] only.

**Part 1: OC₁ wherever one move suffices.** Theorems 11.13 and 11.18 cover 7,441 of the 8,383 data starts with
$|D| \ge 2$. For $|D| = 1$, §11.4 and Theorem D1-C cover every start with a canonical chain without HEAD. The residue:

1. **D1-H2 with extra active agents** (leaf 3b; `proof/k4-d1`) — **OPEN.** D1-H2 at hard all-HEAD perfect starts
   with $D = \{k\}$ and $t = 1$ that have an extra *active* agent (unfrozen, outside the wanters of $a$, valuing
   junk) or a third wanter of $a$. Without either, Lemma CONTRACT and Proposition D1-H₃′ settle $t = 1$.
   - The earlier route asked for (S1) $a$ has exactly two wanters, and (S2) they are the only agents unfrozen at the
     picks. **S2 is false**, even in the MC2 class. The smallest counterexample, S2-X, has $n = 4$, $m = 9$, relevant
     sets $[\{0,1,5,7\},\{3,4,6,7\},\{0,2,5,7\},\{8,6,7,3\}]$ and values
     $[(26,3,25,27),(19,17,25,30),(9,14,7,29),(14,11,1,7)]$. The order $(0,1,2,3)$ gives the picks $(7,6,2,8)$,
     $D = \{0\}$, agents 1 and 2 want good 7, and agent 3 is unfrozen and values junk good 3. It was found by
     `proof/k4-d1` (`k4/d1/s2_probe.py`) and re-verified by the Hall session (`k4/oc1_hall/s2x_check.py`). This
     write-up's checker confirms every printed fact except "all-HEAD" (Appendix C).
   - D1-H2 still holds at S2-X: the chain $(0, 2)$ repairs, because the extra agent supplies a slot. It also holds at
     all 76 such starts of the probe. S1 has no counterexample in 4,159 climbed starts.
2. **D1-H2 for $t \ge 2$** (leaf 3b; `proof/k4-d1`) — **OPEN.** D1-H2 at all-HEAD starts whose longest canonical
   chain has $t \ge 2$.
   - Data: 456 starts. In 449 of them a middle agent is a free slot after the chain.
   - Smallest test so far (not a core): $n = 4$, $m = 7$, relevant sets
     $[\{1,2,4,5\},\{2,4\},\{0,3,4,5\},\{2,5,6\}]$, values $[(26,29,24,25),(20,29),(22,17,30,23),(29,21,25)]$,
     order $(2, 1, 0, 3)$, picks $(1, 2, 4, 6)$, $k = 2$, chains $(2, 1, 0)$ and $(2, 1, 3)$.
   - Next step proposed: an SMT check of the four-agent core.
3. **SLOT2** (leaf 4d; multi session) — **OPEN.** If no (k, longest $P$, $h$) meets Theorem 11.18 or 11.13, then some
   canonical chain from some $k \in D$ has a Lemma 11.3 certificate (owner $k$) with $|H| \le 3$.
   - Data: 161 SLOT starts remain (7 + 11 need one kept-out good, 138 need two, 5 need three). The smallest is
     log613 ($n = 3$, $m = 7$), whose printed values in the source need the referee's fix (§11.5).
   - The obstruction: a holder is threatened by the owner's bundle only because that bundle holds goods the holder
     does not value, and EFX₀ removes such a good at no cost. Keeping each such good out costs a slot.
4. **RING2** (leaf 4e; multi session) — **OPEN.** At a hard perfect start where no canonical chain from $D$ repairs
   with owner $k$, some move of length at most 3 repairs. If $D_T = \emptyset$ and no other move repairs, the repair is
   a swap of two dangerous agents with the wanters compensated by their own junk goods.
   - Data: all 45 RING starts are repaired by moves of length at most 3; 43 have no truly dangerous agent. Smallest:
     T3 with the order $(0, 2, 1)$ ($n = 3$, $m = 6$).
5. **KEEP-C** (leaf 4b; multi session) — **OPEN.** If $D_T = \{k\}$ and no KEEP or OWN chain exists, some canonical
   chain from $k$ repairs with owner $k$.
   - Data: 8 starts, all with $n = 5$; smallest n4_4#1715.0 ($n = 5$, $m = 8$).
6. **R2-C** (leaf 5a; TTC session) — **OPEN** beyond $n = 4$. At a hard perfect start with at least two receivers,
   some canonical chain from a dangerous $x_0$, with $x_1$ wanting $y_{x_0}$, to a receiver is followed by a
   one-absorber completion. It is certified at $n = 4$ (Proposition 11.26 item 5), where it is the one-move
   statement.
   - The owner-specific targets R2-M, R2★, R2-O and R2-O′ are refuted at $n = 4$ (Proposition 11.26 item 5).
   - Smallest earlier test, the first case Lemma R2-0 does not cover ($n = 3$): relevant sets
     $[\{0,1,2,3\},\{0,1,4,5\},\{2,3,4,5\}]$, values $[(8,6,4,1),(4,2,8,5),(4,6,8,3)]$, order $(0, 2, 1)$, picks
     $(0, 5, 4)$, $D = \{2\}$, receivers $\{0, 1\}$, $|J| = 3$. One move repairs it (Appendix C).

**Part 2: the second move elsewhere.**

7. **The second move: settle-and-lift, or a round** (leaf 5; matching, multi and rounds sessions) — **OPEN.** At
   every hard perfect start with no one-move repair, either some RSD-D sequence repairs (a settle-and-lift
   induction with deferred lift and demands), or some round of vertex-disjoint moves does. ROUND-RSD would combine
   the two.
   - *REC-S existence, the earlier form of this item, is false at $n = 5$.* REC-S's hypotheses hold for no $(k, T)$
     at 7 of the 280 sampled two-move starts of the certifier's first $n = 5$ chunk (§11.6). RSD covers five of the
     seven, and RSD-D and ROUND-P cover all seven. REC-S is certified at $n = 4$ (Proposition 11.26 item 8).
   - *Two starts where every sequential form fails* [V]: 5_pure #419 and #447 (`k4/oc1_hall.md` §24.4,
     `attempts/k4-matching-rsd-lstar.md`). The first has $n = 5$, $m = 10$, relevant sets
     $[\{0,2,6,7\},\{1,4,8,9\},\{3,5,8,9\},\{4,5,7,9\},\{6,7,8,9\}]$, values
     $[(6,3,10,8),(4,8,2,3),(2,8,4,3),(6,7,5,3),(10,7,2,6)]$, and picks $(6,4,5,9,7)$.
     - None of its 19 one-move states completes.
     - The chain $(0, 4)$, with agent 0 taking $\{0, 7\}$, and the chain $(1, 3)$, with agent 1 taking
       $\{1, 8, 9\}$, are vertex-disjoint, and together they repair it.
     - But $\{0, 7\}$ threatens agent 3, which only $(1, 3)$ lifts, and $\{1, 8, 9\}$ threatens agent 4, which only
       $(0, 4)$ lifts. So whichever sharer is settled first violates (L\*), and REC-S, OC2-REC and RSD fail at every
       depth.
     - Applied together, the two chains commute and repair, so OC₂^max holds.
     - Found by the matching session with two independent brute forces, and re-checked by the Hall session. This
       write-up's checker confirms no one-move repair, the repair by the pair, and the two threats at both starts
       (Appendix C).
   - *Item 4a, disjoint repairs that must be applied together* (owner: the rounds session). The natural statement is
     ROUND-P^max. A proof that REC-S's repair is always one ROUND-P round would reduce it to the settle-and-lift
     side, but the splice sketch has a gap (Proposition 11.26 item 7).
   - An alternative is the matching session's Conjecture CM₂: some first move leads to a state where Lemma 11.4
     (EX\*) applies. It holds at all 280 sampled $n = 5$ starts.

   *The uniform shape LIFT-SHAPE⁺ is refuted at $n = 5$* (`k4/matching.md` §6 at `5fc71a9`,
   `attempts/k4-matching-lift-shape.md`). It asked for a second chain $P_2$ ending at $z$ with $z$'s favourite good,
   plus (L1)–(L3) or (Lb). It is certified at $n = 4$ (Proposition 11.26 item 6) and held on all 8,073 walk starts
   (7,496 at $n = 4$, 577 at $n = 5$). It fails at the first $n = 5$ two-move start the certifier found (list 5_pure,
   index 164).
   - The instance: $n = 5$, $m = 8$, relevant sets $[\{0,2,3,7\},\{1,2,6,7\},\{3,4,5,6\},\{3,4,5,7\},\{4,5,6,7\}]$,
     values $[(1,8,6,4),(4,8,2,7),(6,7,3,5),(7,10,2,6),(7,5,3,6)]$, order $(1,4,2,0,3)$, picks $(7,2,3,5,4)$, junk
     $\{0,1,6\}$. The single receiver is $z = 3$, whose favourite good is 4.
   - No free completion exists at the picks or after one move, so OC₁^max fails at $n = 5$ too.
   - Two chains repair it. For instance, $(2, 3)$ with agent 2 taking $\{5, 6\}$, then the disjoint chain $(1, 0)$ with
     agent 1 taking $\{1, 7\}$, give the EFX₀ allocation $(\{2\}, \{0,1,7\}, \{5,6\}, \{3\}, \{4\})$.
   - But after no chain ending at $z$ does a second chain ending at $z$ with good 4 in $z$'s bundle leave a
     one-absorber-completable state. The matching session's self-contained script and this write-up's checker
     (Appendix C, with the moves of §2.4) both find this. Not refereed.
   - Theorem 11.23 covers the start: after $(2, 3)$, deleting agent 2 and $\{5, 6\}$ leaves an $n = 4$ SD start that
     one move repairs.

**Common to both parts.**

8. **Existence of the named chains** (multi session) — **OPEN.** A hard start has a KEEP, OWN or clean chain, or a
   Theorem 11.13 or 11.18 configuration, or else is in the SLOT2 or RING2 configuration. The data find one in every
   start.
9. **No third move** (certifier) — **OPEN** beyond $n = 4$. OC₂^max for $n \ge 5$. No start needing three moves is
   known. Two glued copies of 5_pure #164, which a naive count predicts need three moves, already complete at the
   picks (`k4/sdc.md` §31).

*Can Part 1 be dropped?* No, not this way (`k4/oc1_hall.md` §24.3, the multi session's census on its 8,383 hard
starts with $|D| \ge 2$; their implementation) [E]. Settling first, by one REC-S step and then *any* official move of
$I^-$ or none, still fails at 362 starts that one move repairs in $I$. Most of these are starts that Theorem 11.18
repairs at the picks, and settling first breaks them. The smallest are T3 with the order $(0, 2, 1)$, and an
$n = 3$, $m = 6$ start. So Part 1 is needed in $I$ itself.

*What a proof of TARGET₄ along this route still needs.* It needs items 1–9. It also needs the referee's check of the
[W] leaves (Lemma 1, D1-H₃′, CONTRACT, R2-0, R2-G2) and of the claim that the tree covers every hard start. Then
OC₂^max follows at perfect starts, Lemma 12.3 transfers it to maximum-matching starts, and Corollary 6.4 gives
TARGET₄. Each step is open or unrefereed, and none is claimed here.

### 11.10 TARGET₄: the two routes and what each still needs

Statuses here are those of LEDGER.md on main at `15dbe93` and in PR #155 (branch `claude/kind-lamport-y8fdme` at
`8943344`), with the referee's verdicts up to item 67. **TARGET₄ is open.** OC₂^max (Conjecture 12.1) is the
campaign's main surviving conjecture, and it implies TARGET₄ in Lean (`EFX.OC1Max.target4_of_conjOC2max`). Two routes
toward a proof of TARGET₄ are fully specified, and each ends in an implication checked in Lean:
- Route 2's Lean frame now takes the corrected hypothesis, Conjecture BASE-R (PR #151, on main).
- Route 1's frame on main still carries a false uniqueness clause. PR #147, which drops it, is not yet merged.

The hypotheses themselves are open.

**Route 1: receiver first (RF).** A *receiver* of a start is an agent whose pick no other agent prefers to its own.
The last picker of any order is a receiver.

> **Conjecture RF (ledger K4.SDC.RF, amended 04:22 UTC) [C].** In every strict connected $k = 4$ core, at every
> maximum-matching SD start where OC₁ fails, for every receiver $u$ of the start: some order with $u$ first gives a
> maximum matching, and every such order satisfies OC₁.

- *RF ⟹ OC₁^∃max ⟹ TARGET₄* [L] (`EFX.OC1Max.conjOC1exmax_of_conjRF`, `EFX.OC1Max.target4_of_conjRF`; ledger
  K4.SDC.RF.LEAN). The proof takes a maximum-matching order (Lemma 6.2). Either OC₁ holds there, or RF's
  receiver-first order is a maximum-matching order where it does.
- **Two forms, and the one to prove.** The *every-order* form above asks that every maximum-matching $u$-first order
  satisfy OC₁. **RF∃** asks only that some maximum-matching $u$-first order does, for some receiver $u$. RF∃ is all the
  frame uses, and it is the target.
  - *The every-order form is false at $k = 5$* (ledger K4.SDC.RF.K5EVERY) [V] †. The instance is $n = 4$, with
    relevant sets $[\{0,1,2,5,6\},\{1,2,4,5,6\},\{3,4,5,6\},\{3,4,5,6\}]$ and values
    $[(3,35,33,43,39),(20,26,16,43,32),(8,2,7,4),(8,2,7,4)]$. Agents 2 and 3 are twins.
  - At the maximum-matching start $(6, 5, 4, 3)$, OC₁ fails and the only receiver is 2. The 2-first order
    $(2, 1, 0, 3)$ gives $(6, 5, 3, 4)$, the same start with the twins' picks swapped, where OC₁ fails again. The other
    five 2-first vectors satisfy OC₁, so RF∃ holds.
  - Found by the $k$-sensitivity session and replayed by the coordinator. This write-up's checker confirms it
    (Appendix C).
  - At $k = 4$ the every-order form is not refuted. It is certified at $n \le 4$ and holds on the $n = 5$ exports.
- **Lemma REC-∃ (`k4/referee/rfmin.md` §1, proved by the referee) [R].** Take any instance (ties allowed, SD index
  tie-breaking) and a maximum-matching start $Y = \mathrm{SD}(\sigma)$ with no receiver holding a pick. Then some agent
  is pickless, no agent values a junk good, and the picks, with all of $J$ given to one pickless agent, form an EFX₀
  one-absorber completion. *So every OC₁-failing maximum-matching start has a receiver holding a pick.*

  *Proof.*
  - If every agent held a pick, the last agent of $\sigma$ would be a receiver. So some agent is pickless.
  - A wanter of $y_j$ picks after $j$. With no receiver, every pick holder has a wanter, and the wanter chain runs to
    a pickless agent $p$. This gives an alternating path from $p$, so by Lemma 6.3 no pick holder values junk.
  - Pickless agents value no junk either, since junk was free at their turn.
  - So all of $J$ can go to one pickless agent: its bundle is worth 0 to everyone, and every other bundle is a
    singleton. ∎

  With REC-∃, RF∃ implies OC₁^∃max with no existence clause. Random check here: 57 maximum-matching starts without a
  receiver, all completing as stated (Appendix C).
- **The Lean statement.** On main, `ConjRF` (`lean/EFX/RF.lean`) still says that the start has *exactly one*
  receiver, which is false at $n = 5$ (5_pure #650, below). PR #147 restates the frame with RF∃ and drops uniqueness
  (`target4_of_conjRFsome`). It was not yet merged when this draft was written.
- **The structural half is proved, for every $n$.**
  - *Lemma RF-PATH (`k4/girth.md` §7, branch `claude/k4-girth`, generalized form at `712a568`) [R].* Let $Y$ be the SD
    picks of $\sigma$, with every agent holding a good, let $u$ be a receiver of $Y$ with top good $t$, and let
    $Y' = \mathrm{SD}(u, \sigma - u)$. If $t = y_u$ then $Y' = Y$. Otherwise:
    - (a) $t = y_{x_1}$ for another agent, and there are agents $x_1, \dots, x_\ell$, in increasing $\sigma$-order, with
      $Y'_u = t$, $Y'_{x_i} = y_{x_{i+1}}$, and $Y'_{x_\ell}$ a junk good of $Y$, or $y_u$, or nothing; every other
      agent keeps its pick;
    - (b) every $x_i$ strictly loses value, and $u$ strictly gains;
    - (c) if $x_\ell$ receives a good, nobody wants it at $Y'$.

    *Proof* (the source's). Only later pickers can want a pick. By induction, the goods still free just before each
    agent's turn differ between the two runs by one *missing* good, plus $y_u$ after $u$'s old turn. An agent whose
    pick is the missing good is ejected to its best remaining good, which it values less, by strictness. ∎
  - *Lemma RF-ROT (`k4/ttc.md` §14.7, branch `claude/k4-ttc`) [R].* At a start with exactly one receiver, the receiver
    is the last picker, so RF's order is the rotation $\sigma \mapsto (\sigma_n, \sigma_1, \dots, \sigma_{n-1})$.
  - The referee re-derived both, with 800,000 random orders, 378,973 path cases, and 156,628 cases with $u$ not the
    last picker, with 0 failures (`k4/referee/girth.md` §7).
- **The completion half is OPEN.** It is the girth session's uniform statement (`k4/girth.md` §7). At the RF start,
  one of the following holds:
  - (i) the agent after $u$ on the path, or its end, owns a one-absorber completion;
  - (T) a receiver and a pick-dangerous agent trade, the latter adding one junk good;
  - (C/C′) a two-agent chain from a truly dangerous agent repairs.

  It holds at all 292,080 $n = 4$ failing orders and all stored $n = 5$ ones [E]. The Hall session proved its
  sub-case A1 (32,000 $n = 4$ starts), conditional on four facts that hold at all of them. Its Lemmas RF-A1, RF-B,
  REPAIR-Y and Proposition RF-B4 are refereed CORRECT (`k4/referee/oc1_hall.md`, RF residue addendum). Sub-cases A2
  and B are open.
- *Evidence for RF.* At $n = 4$ it holds at all 112,880 OC₁^max-failing starts, two independent implementations agree,
  and with the certifier's certificate this covers every strict profile [Cert]. At $n = 5$ it holds at every failing
  pair the certifier's CEGAR met in its first two 5_pure chunks, 550 in the first alone (`k4/attack_log.md`, 04:37
  UTC; certifier commit `d830b54`) [E].
- **R2 is false at $n = 5$** (ledger K4.SDC.R2.N5) [V] †. R2 said that two or more receivers give OC₁. The
  counterexample is 5_pure #650.
  - Relevant sets $[\{0,1,5,7\},\{0,5,6,7\},\{1,5,6,7\},\{2,3,4,6\},\{2,3,4,7\}]$, values
    $[(3,6,7,5),(2,10,7,6),(2,8,4,3),(4,5,6,8),(5,4,6,8)]$, picks $(5,0,1,6,7)$: a strict connected MC2 core at a
    perfect start with receivers $\{1, 2\}$, where OC₁ fails.
  - Two frozen twins share three junk goods, and neither receiver values junk.
  - The certifier found four such cores, and three independent replays confirm them. This write-up's checker confirms
    the core, the receivers, the failure of OC₁, and RF for both receivers (Appendix C).
  - R2 stays certified at $n \le 4$. RF and OC₂^max hold at all four cores.
- *RF beyond $k = 4$* [Cert]. RF holds for every strict profile of every connected $n = 3$ hypergraph with at most
  five relevant goods per agent (ledger K4.KSENS.RF5; single CEGAR). That includes N3K5, where OC₁^max fails.
- **The completion half at $n = 5$: the DEMOTE classes.** On the certifier's $n = 5$ exports (1,285,930 starts), the
  RF starts split into classes by the receivers and the truly dangerous agents after the rotation (`k4/girth.md` §7).
  - **DEMOTE-0** (one receiver, no truly dangerous agent; 113,484 starts) is covered by refereed pieces:
    - 71,443 complete at once by the form of *Lemma RF-A1\** (`k4/k3_oc1.md` §13.5) [R];
    - 42,009 are repaired by a trade, whose allocation is EFX₀ exactly under Lemma RF-T's conditions, and Corollary
      RF-T′ gives sufficient ones (`k4/girth.md` §7) [R];
    - the last 32 are repaired by a three-ring (T\*), each certificate replayed by the referee (CONFIRMED).
  - **Class (1, 3)** (7,733 starts) is covered by *Lemma C13* (`k4/ttc.md` §14.8) [R′]. The fix is the hypothesis "the
    path's end $d$ is a receiver", which the proof uses and the statement omitted. Without it there is a three-agent
    counterexample.
  - These lemmas are certificate lemmas: their hypotheses were checked at every start of the class. The coverage is
    therefore of the exported starts [E], not a proof for all $n$. Hall's Lemma RF-B′ (`k4/oc1_hall.md` §24.10) [R]
    feeds the class DEMOTE-2 (140,111 starts), which the Hall session holds. The SINK form of DEMOTE is a conjecture.
- **Minimal counterexamples and RF** (`k4/RFMIN.md`, branch `proof/k4-rf-min`, PR #156; `k4/referee/rfmin.md`).
  - *Proposition RF-𝒦* [R′]: if RF holds on the class 𝒦 of strict type profiles allowed for a minimal counterexample
    (β ≥ 5, $n \ge 6$ with the K4.MC2–K4.MC9 restrictions), then TARGET₄ holds. The fix is that the proof needs a
    receiver at the failing start. Lemma REC-∃ supplies it.
  - *Lemma RF-TOP* [R]: if $u$'s pick is its top good, moving $u$ to the front does not change the picks. Hence, under
    RF, no receiver of an OC₁-failing start holds its top good, and OC₁ holds at every start of a core where some
    agent's top good is private.
  - *Lemma ABS* [R] ($k \le 4$): if some agent $f$ holds a good nobody else values, and no frozen agent values the
    junk set above its pick, then the picks have a one-absorber completion with absorber $f$. The construction lets
    each other receiver take its best free junk good if it gains, and then $f$ takes the rest.
- **RKMAX, an extremal form of the same target** (`k4/sdc.md` §31 end, ledger K4.SDC.RKMAX) [C]. At a pick vector
  $Y$, let $\mathrm{rank}_i(Y) = 1 + \#\{g \in R_i : v_i(g) > v_i(y_i)\}$, and let the signature
  $\sigma(Y) = (\#\text{rank } 1, \dots, \#\text{rank } 4)$.

> **Conjecture RKMAX.** In every strict connected $k = 4$ core, every maximum-matching SD pick vector whose signature
> is lexicographically maximal among the maximum-matching SD vectors satisfies OC₁.

  - *RKMAX ⟹ OC₁^∃max ⟹ TARGET₄*, and RKMAX holds iff every OC₁-failing maximum-matching start has a
    maximum-matching SD vector of larger signature. Both are refereed CORRECT (`k4/referee/rkmax.md`). No Lean frame
    yet.
  - *Certified* at $n \le 4$ (ledger K4.SDC.RKMAX.N4) [Cert]: every σ-maximal vector satisfies OC₁ at all 111,600
    profiles of the complete $n = 4$ failure export. Three implementations agree (coordinator, referee,
    `proof/k4-rkmax`). Also certified on the complete failure lists of 5_pure #419, #447 and #38, 583,680 profiles
    (K4.SDC.RKMAX.SEL2).
  - *False at $k = 5$* (K4.SDC.RKMAX.K5) [V], at N3K5 (§8). The three agents share their two top goods, so every SD
    vector has $\sigma = (1, 1, 1, 0, 0)$, and RKMAX reduces to OC₁^max, which fails there. So RKMAX is a $k = 4$
    statement, and RF, which holds at N3K5, is the candidate for general $k$.
  - *Plan (a) is false* [V]. Plan (a) said that a σ-maximal start has two receivers or one receiver with one truly
    dangerous agent. The counterexample is 5_pure #358 (`k4/oc1_hall.md` §24.14): relevant sets
    $[\{0,1,4,5\},\{1,3,6,7\},\{2,3,6,7\},\{2,4,5,7\},\{4,5,6,7\}]$, values
    $[(17,4,2,19),(13,14,20,16),(2,16,20,17),(5,17,15,7),(20,17,4,8)]$.
    - Its σ-maximal vectors $(5,7,6,2,4)$ and $(5,6,7,2,4)$ have $\sigma = (3,1,0,1)$, the single receiver 3, and junk
      $\{0,1,3\}$. Hall's class is (1, 2): one receiver and two truly dangerous agents.
    - OC₁ holds there after one move, so RKMAX survives.
    - The printed integers have two subset-sum ties ($17 + 2 = 19$ for agent 0, and $5 + 17 = 15 + 7$ for agent 3).
      This write-up's checker finds the same facts for a strict perturbation, which is a strict connected core
      (Appendix C).
- *What route 1 still needs:* RF∃, or RKMAX, for every $n$, that is, the completion half. At $n = 5$, DEMOTE-0 and
  class (1, 3) are covered on the exports by refereed lemmas, but a proof for every $n$ is open. Route 1 also needs PR
  #147 merged.

**Route 2: rounds (ROUND-RSD).** Settle a round of dangerous agents along vertex-disjoint earliest-wanter prefixes,
delete them with their sets as *phantoms*, and recurse in the smaller instance.
- **The frame, now with BASE-R** [L] (ledger K4.BASE.GR.LEAN, `lean/EFX/BaseR.lean`, PR #151 on main): Conjecture
  BASE-R ⟹ TARGET₄ (`EFX.Round.target4_of_conjBaseR`, `target4_of_conjGR`, `conjGR_iff_conjBaseR`), for any move
  class of base repairs.
  - Every stop of GR is an EFX₀ allocation of the whole instance.
  - Each P1-free round deletes an agent, so GR terminates.
  - BASE-R is monotone in the move class.
  - The Lean bridge to the earlier frame is `liftedAt_iff`, by LIFT-SEP.
  - Proposition SEP and Corollary LIFT-SEP are in Lean too (`lean/EFX/Sep.lean`, ledger K4.BASE.SEP.LEAN) [L].
  - The referee checked that the Lean statement is the corrected BASE-R and not GRR. `VisitedGR` requires no stop at
    the predecessor, and the stops, `P1Free` and the admissible rounds match the note. This is item 68, on
    `claude/k4-referee` at `11cae62f`, not yet on main.
- *The earlier frame* [L] (ledger K4.MATCH.ROUNDRSD.LEAN, `lean/EFX/RoundRSD.lean`, PR #141): ConjRoundInd ∧
  ConjBasePhi ⟹ TARGET₄ (`EFX.Round.target4_of_roundRSD`). Its base case is false as posed (below), so PR #151
  replaced it with the BASE-R frame.
  - **ConjRoundInd:** at every state reachable by admissible rounds that has no one-move repair, an admissible round
    exists.
  - **ConjBasePhi:** at every reachable state that has a one-move repair, there is one whose one-absorber completion
    threatens no phantom at its threshold.
- *Its tools, all refereed and in Lean* (ledger K4.MATCH.LIFTSTAR.LEAN, K4.MULTI.S.LEAN, K4.MULTI.SPHI.LEAN, PR #149):
  - Lemmas 11.24 (LIFT\*, also for rounds) and 11.25 (PHANTOM);
  - Lemma SD-E(round) (`k4/referee/oc1max_multi.md` §15: CORRECT; earliest-wanter prefixes are needed);
  - Theorem 11.18 (S);
  - **Theorem S^φ**, Theorem S with phantom constraints (`k4/oc1max_multi.md` §16, branch `proof/k4-oc1max-multi-2`)
    [R′; L]. Let $(k, P, h, H_0)$ meet Theorem 11.18's hypotheses in the present instance, and suppose:
    - (S-φ1) $W$ threatens no phantom at its threshold;
    - (S-φ2) the receiver's good is not wanted by a phantom;
    - (S-φ3) if $h = y_z$, no phantom values $y_z$ above its threshold;
    - (P3) $v_\varphi(h) \le \tau_\varphi$ for every phantom.

    Then OC₁ holds with the phantom constraints. The fix is (S-φ3), which the proof uses; without it, 44 random cases
    fail (`k4/referee/oc1max_multi.md` §14). The Lean form needs no (S-φ3) because it takes $h$ junk. Corollary
    S^φ(round), with phantoms settled in rounds, is refereed CORRECT (§16 there).
- *The witnesses* [Cert]. ROUND-RSD repairs every $n = 4$ two-move start, all 280 sampled $n = 5$ starts and 23,924
  walk starts. The referee validated all of them (`k4/referee/lift.md` §9). Earliest-wanter-prefix rounds repair all
  583,680 two-move starts of the three adversarial $n = 5$ cores #419, #447 and #38 (ledger K4.MULTI.ROUNDE.SEL2,
  CONFIRMED by the referee).
- **The base case as posed is false** (ledger K4.BASE.PHI, REFUTED; `k4/base_phantom.md` §2). The smallest instance is
  T3 ($n = 3$, $m = 6$; §11.9 item 4).
  - Its only admissible round settles agent 2 along $E(2) = (2, 1)$ with $T = \{1, 3\}$. That round is improving,
    satisfies (L\*), and leaves agents 0 and 1, whose picks complete with no phantom constraint.
  - But no allocation of the present goods is EFX₀ among agents 0 and 1 without threatening agent 2 at
    $v_2(T) = 32$: good 0 is worth 38 to agent 2, and it cannot be alone.
  - So that state has a one-move repair but none that respects the phantom.
  - This write-up's checker confirms each step (Appendix C). By this write-up's reading of the Lean definitions (the
    round is an earliest-wanter prefix, and (H), (P2), (P3) are vacuous there), T3 falsifies `ConjBasePhi` as
    formalized. That reading is not machine-checked.
  - At $n = 4$, the dead ends (reachable states with no lifted completion and no admissible round) are 32,480 states
    from 16,240 starts. 29,280 of them admit no EFX₀ allocation keeping the phantoms' sets, and every one carries an
    "ℓ alone" phantom (ledger K4.BASE.DEAD.N4 [Cert], CONFIRMED by the referee).
- **The correction: P1-free rounds** (`k4/base_phantom.md` §4–§5, branch `proof/k4-base-phantom`, PR #139). A
  settlement is *P1-free* if every good of $R_k \setminus T$ is worth at most $\tau_k = v_k(T)$ to $k$.
  - *Proposition SEP* [R] (`k4/referee/basephantom.md`: CORRECT; 1,156,525 raw-threat tests, 0 violations). A P1-free
    phantom is threatened only by a bundle of three or more goods containing two goods of $R_k \setminus T$. For a pair
    $T$, that means exactly a bundle $X \supseteq \{y_k, \ell_k\}$ with $|X| \ge 3$ and
    $v_k(y_k) + v_k(\ell_k) > \tau_k$. So P1-free phantoms only separate pairs. *Proof:* Lemma 11.25 with
    $v_k(\ell) \le \tau_k$ rules out (P1). ∎
  - *At $n = 4$, P1-free rounds never dead-end* (ledger K4.BASE.P1FREE.N4) [Cert]. From each of the 112,880 two-move
    starts, every sequence of admissible P1-free rounds ends in a lifted completion. Two implementations agree, and the
    referee confirmed it exhaustively.
  - *A P1-free round need not exist at $n = 5$* (ledger K4.BASE.P1FREE, REFUTED) [V]. At 12 of the 280 sampled
    two-move starts, every admissible round settles an agent with an "ℓ alone" constraint. At all 12, a round of one
    P1-free and one P1 settlement is followed by a completion at once.

The greedy process **GR** works as follows:
- it stops at a lifted completion, at a *final round* (an admissible round of any kind followed at once by a lifted
  completion), or at an *ED repair* (an ED move followed by a lifted one-absorber completion);
- otherwise it takes any admissible P1-free round.

A *GR-visited* state is a hard perfect start, or a state obtained by a P1-free round from a GR-visited state that
has none of the three stops.

> **Conjecture BASE-R (ledger K4.BASE.GR, corrected form) [C].** Every GR-visited state (strict values, at most four
> relevant goods per agent) with none of the three stops has an admissible P1-free round. Equivalently, GR never gets
> stuck.

  With Lemmas 6.2 and 12.3, BASE-R implies TARGET₄, with no existential choice of rounds. This is machine-checked in
  the frame above.
  - *The first statement was too strong.* It covered every state reached by P1-free rounds, including rounds taken
    where a final round already existed. That form, K4.BASE.GRR, is refuted [V]: 8 of the 280 sampled 5_pure starts
    get stuck that way, with two implementations agreeing. So GR must stop at its base first.
  - *Lemma B3 and Corollary B3′* [R] (`k4/base_phantom.md` §5.1; `k4/referee/basephantom.md` addendum). At a reachable
    state, a one-move-and-completion allocation that is EFX₀ among the present agents and threatens no phantom is
    EFX₀ in $I$. For P1-free phantoms, the second condition is SEP's separation.
    - Hence Theorems U and S, RING-red, D-red, KEEP and OWN give phantom-respecting ED repairs wherever they apply and
      the large bundles separate the phantoms' pairs.
    - BASE-R follows from B1 ∧ B2:
      - **B1** (OPEN): no admissible round implies an ED repair;
      - **B2** (OPEN): rounds exist but none is P1-free, which implies a final round or an ED repair.
  - *Certified* [Cert] on all 583,680 two-move starts of 5_pure #419, #447 and #38 (ledger K4.BASE.GR.SEL2). Two
    implementations agree, and every stop there is a final round.
  - *Evidence* [E]: GR never gets stuck on 112,880 ($n = 4$, all), 1,285,930 (the certifier's whole $n = 5$ export),
    14,047 (an $n = 5$ partial export), 4,955 (walks), 280 (5_pure) and 8,539 one-move starts.
  - Each stop is needed. Without the final round, 12 5_pure starts get stuck; without the ED repair, 47 one-move
    starts do.
- *What route 2 still needs:* Conjecture BASE-R, which has three parts:
  - OC₁ by an ED move where no admissible round exists (6 known starts);
  - a final round where every admissible round creates an "ℓ alone" phantom (the 12);
  - OC₁ with separation constraints elsewhere.

  Equivalently, it needs B1 and B2. The Lean frame for it is done (PR #151).

**Also refereed this period** (not needed above):
- *Lemma SPLICE* (`kgen/rounds.md` §4.10, `k4/referee/rounds_r1.md` addendum 2: CORRECT WITH TWO SMALL FIXES). A
  REC-S repair is one round of OC₁′ moves, except in an explicit configuration (EX), and the converse holds too.
  This replaces the sketch whose gap is recorded in Proposition 11.26 item 7. The same report confirms that REC-S
  existence fails at exactly the 7 named $n = 5$ starts (ledger K4.MULTI.RECS.EXIST.N5).
- *The pick graph* (`kgen/rounds.md` §4.11): Lemmas PG, GAIN, RING, RHO, FIX and Theorem ROUND-SIMPLE CORRECT. As
  proved, "ROUND-P^max ⟺ SIMPLE-MD" holds only in the direction ⟸.
- *Lemma UNTANGLE* (§4.13 there): proved parts (1)–(5) CORRECT. The open parts cannot be closed by any rule for $h$.
- *K4.MC9* (`k4/TWINS.md` §4): a minimal counterexample has no claw, three P3 agents on a good of degree 3 (certified
  reduction, SOUND).

## 12. Open problems and conjectures

Everything in this section is open. Evidence is finite data, and random data can miss rare structures. Several
statements of this campaign survived millions of random starts and then fell to one designed or exhaustively found
instance (§7.2, §7.3, §7.5, §12.5).

### 12.0 TARGET₄

**TARGET₄ is open.** What is known comes from earlier certified work (ledger rows K4.R5–K4.R6a, K4.MC0–K4.MC7) with the
reductions of §2.2. A minimal counterexample is a strict connected $k = 4$ core in the MC2 class, and it has:
- at least six agents, at least one of them with four goods (at least two if $n = 6$);
- cyclomatic number at least 5.

By L1 (PROMPT.md), a counterexample would also refute EFX existence for strictly positive additive valuations.
Monotone EFX₀ at $k = 4$ is also certified for $n \le 5$ (Proposition 9.9), by a method independent of those rows.

The two routes toward a proof, and exactly what each still needs, are in §11.10:
- Route 1 needs RF∃ for every $n$: some receiver-first maximum-matching order whose picks, or one move from them,
  complete. That is the completion half after Lemma RF-PATH. The extremal form RKMAX would also do; it is a $k = 4$
  statement (false at $k = 5$).
- Route 2 needs Conjecture BASE-R, equivalently the two base lemmas B1 and B2. Its Lean frame is done (PR #151).

### 12.1 After OC₁^max: two moves, and some-order forms

OC₁^max (one move from every maximum-matching start) was the campaign's central conjecture until its last hour. It is
false at $k = 4$ (Proposition 7.4). Two weakenings survive. Both imply TARGET₄.

> **Conjecture 12.1 (OC₂^max; `k4/sdc.md` §31) [C].** In every strict connected $k = 4$ core, for every SD order whose
> picks form a maximum matching: the picks, or the bases after at most two sequential improving moves, have a
> one-absorber EFX₀ completion.

> **Conjecture 12.2 (some-order forms; `k4/sdc.md` §31) [C].** In every strict connected $k = 4$ core, *some* SD order
> whose picks form a maximum matching satisfies OC₁: its picks, or a state one move away, have a one-absorber EFX₀
> completion.

SD-C (Conjecture 12.5) is the zero-move some-order form. OC₂^max implies TARGET₄ by Corollary 6.4, with two
sequential moves as the step (the Lean frame `ConjOC1maxWith` takes any move relation). Conjecture 12.2 implies it
directly.

*Evidence* [E]. All of OC₁^max's evidence is evidence for both, since a start that needs at most one move needs at
most two. That evidence consists of:
- every start of the earlier OC₁ data (every order with $n \le 5$; 120,050 starts);
- 11,002,996 maximum-matching orders of random strict profiles of all 31,584 core hypergraphs with $n = 5$;
- 33,082 maximum-matching orders of the known counterexamples to the every-order forms;
- the Hall session's 2,071 one-absorber-hard maximum-matching starts;
- adversarial climbs on strict cores up to $n = 8$.

In addition:
- *OC₂^max is certified for $n \le 4$* [Cert]. It holds for every strict profile of every core hypergraph with
  $n \le 4$ (1,058 hypergraphs; §7.3), the 11 failing ones included. The coordinator's independent check of those 11
  agrees, and two sequential moves repair both printed instances (Appendix C). At $n = 5$ it is certified so far on
  3,605 of the 31,584 cores (Proposition 11.26 item 2), with no failure. The $n = 4$ two-move starts all have
  explicit refereed repairs (REC-S and RSD; Proposition 11.26 items 8–9).
- *The some-order form on the counterexamples.* On both instances of Proposition 7.4, other maximum-matching orders
  complete at the picks.
- *Conjecture 12.2 is certified for $n \le 4$* [Cert] (Proposition 11.26 item 3). On the 991 cores where OC₁^max
  holds it follows from that certificate, and on the 11 failing cores an ∃-CEGAR certifies it, re-checked by an
  independent checker.
- *Every $n = 4$ two-move start is known* [Cert]. There are 112,880 of them, each with exactly one receiver and each
  of the two-chain shape LIFT-SHAPE⁺ (Proposition 11.26 items 4–6).

*Limits and the next test.*
- In the PW family, two sequential chains fail at $k = 7$ (§8, one SAT encoding [E]). So OC₂^max, like OC₁^max, is at
  best a $k \le 4$ (or small-$k$) statement.
- The obstruction of Proposition 7.4 is a junk danger pair shared by two dangerous agents with no free slot. The Hall
  session notes that $s$ dangerous agents sharing one pair would need about $s - 1$ lifts. So three sharers might
  defeat two moves (`k4/oc1_hall.md` §22). At $n = 5$ a second kind of obstruction appears: two disjoint conflicts
  that need two moves at once (§11.9 item 7). A round repairs it, but three disjoint conflicts could defeat two
  sequential moves. Gluing two copies of 5_pure #164 does not produce that: the glued start completes at the picks
  (`k4/sdc.md` §31).

**Lemma 12.3 (RED, reduction to perfect starts; `k4/sdc.md` §31) [R].** Read by the Hall session (`k4/oc1_hall.md`
§21), and refereed CORRECT as Lemma RED₃ of `k4/k3_oc1.md` §11 (`k4/referee/k3_oc1.md`, addendum). RED₃ is RED in
Draft and Exchange notation, and its proof never uses $|R_i| \le 3$. The referee's evidence includes 10,768
non-perfect maximum-matching starts with up to four goods per agent and 127,354 lifted completions, with 0
failures. Its allocation part (i)–(ii) and the frame below are machine-checked:
`EFX.OC1Max.red` and `EFX.OC1Max.target4_of_conjOC1perfWith` in `lean/EFX/OC1Perf.lean`, branch `formal/k4-oc1max`
at `28f3e1e`.

Let $Y$ be maximum-matching picks of any instance with strict values. Let $U \ne \emptyset$ be the pickless agents,
$S$ the agents reachable from $U$ by $Y$-alternating paths, $T$ the remaining agents, and $J$ the junk.
- (i) No agent of $U \cup S$ values a junk good (Lemma 6.3).
- (ii) Every good valued by an agent of $U \cup S$ is the pick of an agent of $S$.
- (iii) Let $I'$ be the instance with agents $T \cup U$ and goods $\{Y_t : t \in T\} \cup J$, values restricted. The
  agents of $U$ become *null agents*, valuing nothing. Then every one-absorber EFX₀ completion of $I'$, at its picks
  or after a move of $I'$, extends to one of $I$: the agents of $S$ keep their single picks, and the agents of $U$
  get what they get in $I'$.

*Proof sketch* (from the source).
- For (ii): a good valued by $u \in U$ is picked, else $u$ could be matched to it. It is the pick of some $b$, and
  $b \in S$. A good valued by $s \in S$ is not junk by (i), so it is a pick $Y_b$, and again $b \in S$.
- For (iii), every EFX₀ constraint involving $S \cup U$ holds in the extension:
  - agents of $S \cup U$ value only picks of $S$, which are held alone, and removing a singleton's good leaves
    nothing;
  - agents of $S \cup U$ value no junk, so they never envy the bundles of $U$ agents;
  - agents of $T$ compare $S$ holders' singletons only, which never violates EFX₀.

Every move of $I'$ is a move of $I$, and the absorber counts are the same. ∎

So statements at maximum-matching starts reduce to the same statements at **perfect starts** (every agent with a
relevant good holds a pick). Null agents are allowed, and they count as ordinary agents in the absorber count. Since
every move of $I'$ is a move of $I$, the reduction applies move by move to sequences of moves. That remark is this
write-up's; the source states one move, and the Lean frame takes any move relation.
- Its original target, **OC₁ at perfect starts, is false**: instance 1 of Proposition 7.4 is a perfect start.
- The lemma itself stands, and it transfers OC₂^max to perfect starts. $I'$ need not be a core, so this route needs
  the perfect-start form for all 4-limited instances.

*A proof along these lines* is the subject of §11. It sets out the refereed tools (Lemma T6, Lemmas M and EX\*, the
reductions for one and several dangerous agents, Theorem U, and the second-move Lemmas LIFT-red, LIFT-1 and LIFT),
the case tree, and the nine open statements that remain (§11.9). Also refereed and relevant: the Hall session's
Lemma 2\* and Theorem F1₁ (Appendix B), and Lemma 7.6.

### 12.2 MD and SD-C

> **Conjecture 12.4 (MD; `k4/sdc.md` §28) [C].** In every 4-limited instance, every matching is value-dominated by a
> complete EFX₀ allocation.

> **Conjecture 12.5 (SD-C; `k4/sdc.md` §2) [C].** In every 4-limited instance, some SD order's picks extend to a
> complete EFX₀ allocation.

MD contains TARGET₄ (take the empty matching). By Lemma 6.1 it is equivalent, for strict values, to value domination
of every order's picks. On the instances of Proposition 7.4 both hold, since two moves repair and other orders
extend. Neither conjecture has a counterexample at any $k \le 8$ tested (§8). For every $k$, both contain EFX₀
existence for all additive instances.

### 12.3 VM1 and VM1-chain: one move from a Viswanathan–Mehta matching

**VM1** (`k4/vm.md` §7.3, branch `claude/k4-vm`) asked that for every 4-limited instance there be:
- a V-M matching $Y$ (Phases I–II of §10.1, some resolution of ties);
- at most one move: a pool upgrade, or a two-agent exchange in which $i$, holding a single good, takes any good $z$
  of $j$ plus pool goods, both agents gaining and EFX₀ kept;
- an order of the remaining goods;

such that placing each good on some agent whose bundle stays EFX₀-unenvied, rotating envy cycles before each
placement, ends in a complete EFX₀ allocation. VM1 implies TARGET₄. Every state of such a run satisfies five
invariants, (I1)–(I5) of `k4/vm.md` §7.3, which the referee checked (Lemmas SND and TERM; `k4/referee/vm.md` §6):
- (I1) partial EFX₀;
- (I2) domination of the start;
- (I3) a good someone prefers to its own bundle is held alone;
- (I4) bundles of two or more goods are envied only by agents that value all their goods;
- (I5) a potential rises at every move.

**VM1 is false at $k = 4$, on a connected core** (`attempts/k4-vm-vm1-core.md`) [R] †. The instance P34 has $n = 4$
and $m = 7$, and every agent values four goods:

| agent | goods (value) |
|---|---|
| 0 | 0 (4), 2 (3), 4 (2), 5 (8) |
| 1 | 0 (4), 2 (3), 4 (2), 6 (8) |
| 2 | 1 (4), 3 (2), 5 (8), 6 (5) |
| 3 | 1 (4), 3 (2), 5 (8), 6 (5) |

- *V-M.* Agents 0 and 1 are strong ($8 > 4 + 3$) and take goods 5 and 6. Agents 2 and 3 tie on good 1, and the
  loser takes good 3. The pool $\{0, 2, 4\}$ is valued only by agents 0 and 1.
- *No move completes.* With no move, the only unfrozen agent (the loser) can take at most two pool goods. The only
  legal moves are agent 0's or agent 1's upgrade to $\{0, 2, 4\}$. After either, the released good (5 or 6) has no
  EFX₀-safe place, there is no envy cycle, and the exchange that would park the displaced good breaks EFX₀.
- *Two moves complete:* $(\{0, 2, 4\}, \{6\}, \{5\}, \{1, 3\})$, in which agent 0 upgrades, agent 2 takes the
  released 5, and the released 1 goes to agent 3. This is one chain of DE's kind, whose released good returns to the
  pool.
- *Verification.* The session's exhaustive certifier found it. `vm1_verify.py` checked it uncapped, and an
  independent replay with its own core check agrees. The referee confirmed it with a search wider than VM1's
  (`k4/referee/vm.md` §7). This write-up's checker confirms the core conditions and the two-move completion
  (Appendix C). VM1 fails on exactly 3 of the 1,058 core hypergraphs with $n \le 4$, and on five cores found at
  $n = 5$.
- At larger $k$ the form fails as well [V]: one move fails at $k = 6$ (PW(4, 3, 5)#1, $n = 7$, $m = 12$) and at
  $k = 7$ (PW(2, 3, 6), $n = 5$, $m = 11$), and two moves fail at $k = 9$ (PW(3, 3, 8)), where three suffice
  (`attempts/k4-vm-vm1-k6.md`, `attempts/k4-vm-vm1-k7.md`). VMX₂, with any number of moves, completes every
  failure found.

> **Conjecture 12.6 (VM1-chain; `k4/vm.md` §7.7) [C].** The same as VM1, except that the one move may instead be one
> *DE chain*. In a DE chain, an agent $x$ holding a single good upgrades to a pool set and releases its good. Then,
> any number of times, an agent holding a single good that it values below the released good takes it and releases
> its own. Only the final state must be EFX₀.

- *Certified for $n \le 4$* [Cert]: VM1-chain holds for every strict profile of every $k = 4$ core with $n \le 4$, all
  1,058 hypergraphs (`k4/vm.md` §7.9). The ordinal CEGAR over order types has two implementations that share no code,
  and neither finds a gap.
- Rotation is needed: without it (VM1-chain-plain) the statement fails on 384 profiles at $n = 3$.
- *Evidence* [E]: it completes 19 of the 20 collected VM1 failures, all but PW(3, 3, 8) at $k = 9$, and all 315
  instances of a fresh PW grid up to $k = 9$. The 11 $n = 4$ and 24 $n = 5$ OC₁^max counterexample cores satisfy VM1
  itself with no move.
- *Limits.* With *narrow* exchanges (the taker must value $z$), VM1 fails already at $n = 3$, $m = 7$
  (`attempts/k4-vm-vm1.md`). The unproved step is placeability. P1's state GM4-E (§7.1) shows that (I1), (I3) and
  (I4) alone do not imply it.

### 12.4 DYN: LSS's algorithm with dynamic parking

> **Conjecture 12.7 (DYN; `k4/girth.md` §5) [C].** For every 4-limited instance there are a vertex 0 and a labeling
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
  It has not been reported on the instances of Proposition 7.4.
- *Variants refuted*: DYN without the G1 repair (`attempts/k4-girth-dyn-plain.md`), and a single sink instead of dynamic
  parking (at $n = 2$).

The linear case of DYN (Conjecture LR-dyn, `k4/girth.md` §4) would give EFX₀ for every linear additive instance at
every $k$.

### 12.5 Two statements named W

**(a) Conjecture W, the one-step welfare lemma** (`k4/haxell.md` §6, branch `claude/k4-haxell`). The statement: from
every partial EFX₀ allocation with a nonempty pool, a composite of at most two moves reaches a partial EFX₀ allocation
with a smaller pool, or with the same pool and strictly larger welfare $\sum_i v_i(X_i)$. A move is one of these:
- giving one good to another agent (a pooled good may be placed; nothing returns to the pool);
- swapping the holders of two goods (the pool counts as a holder);
- rotating the bundles along a cycle of agents.

The pair (pool size, $-$welfare) is well-founded, so W would give TARGET₄. It is not value-monotone: a step may lower
any agent, which is how it escapes P1's stuck state.

**Conjecture W is false** (`attempts/k4-haxell-conjecture-w.md`) [V] †. The instance has $n = 2$, $m = 7$, $k = 4$:

| agent | goods (value) |
|---|---|
| 0 | 0 (40), 1 (10), 2 (11), 3 (12) |
| 1 | 0 (70), 4 (10), 5 (40), 6 (11) |

The state $(\{1, 2, 3\}, \{4, 5, 6\})$, with good 0 pooled, is partial EFX₀.
- Good 0 must end up alone, since in a bundle of two or more goods the other agent strongly envies it.
- So its receiver must give away all three of its other goods, and no composite of two moves improves.
- Three moves do: swap good 0 with agent 1's good 4 through the pool, then move goods 5 and 6 to agent 0.

The instance was checked by the session's replay (`attempts/k4_haxell_w.py`, from the raw definition) and by this
write-up's own move search (Appendix C).

**W^sub and L^sub are false at $n = 4$, $k = 4$** (`k4/haxell.md` §6 at `f10440b`; `attempts/k4-haxell-wsub-welfare.md`,
`attempts/k4-haxell-lsub-leximin.md`) [V] †. W^sub is W with set moves: giving a nonempty set of one holder's goods
(an agent's, or pooled goods) to one agent counts as one move. L^sub is the same with the **leximin** order (the
sorted vector of the agents' values) in place of welfare. Both were candidates after W fell. Each is refuted by an
$n = 4$, $m = 7$ strict balanced $k = 4$ core, and the two fail at different states.
- *W^sub (welfare), instance WS4.* Agent 0 values goods 4, 5, 6 at 9, 47, 39; agent 1 values 1, 2, 4, 5 at 8, 3, 2,
  4; agent 2 values 0, 1, 3, 5 at 7, 4, 1, 9; agent 3 values 0, 4, 6 at 38, 7, 32. The state is
  $(\{5\}, \{2, 3, 4\}, \{1\}, \{0\})$ with good 6 pooled. Every placement of good 6 is blocked by strong envy,
  and no composite of at most two moves reaches a partial EFX₀ allocation with a smaller pool or higher welfare.
  Leximin has a step there. Three moves reach the complete EFX₀ allocation $(\{3, 6\}, \{1, 2, 4\}, \{5\}, \{0\})$.
- *L^sub (leximin), instance LS4.* Agent 0 values goods 3, 4, 5, 6 at 30, 20, 55, 57; agent 1 values 1, 3, 4, 5 at
  31, 12, 5, 39; agent 2 values 0, 1, 3 at 44, 32, 29; agent 3 values 0, 1, 2, 6 at 60, 31, 7, 43. The state is
  $(\{2, 3, 4\}, \{5\}, \{0\}, \{6\})$ with good 1 pooled. No composite of at most two moves shrinks the pool or
  raises leximin. Welfare has a step there.
- *Verification.* The session's C checker (`gstar_measure.c`) and an independent Python enumeration
  (`attempts/k4_haxell_wsub.py`) agree on both. This write-up's checker confirms both refutations with its own move
  enumeration, and the cross-steps (Appendix C). Not refereed.
- The Pareto form P^sub, which implies both, fails too.

**Conjecture 12.8 (three moves: W₃ and P^sub₃; `k4/haxell.md` §6) [C].** What survives:
- **W₃** (welfare, three single-good moves), a candidate for $k \le 4$. It fails at $k = 5$ by the same mechanism as
  W (instance W5), since the radius needed grows like $k - 1$.
- **P^sub₃** (three moves, set moves allowed, the measure step a Pareto improvement), and with it **W^sub₃** and
  **L^sub₃**. P^sub₃ implies both, and it is ordinal, so checks over strict types are complete for it.
- *Evidence* [E]. Three moves give a step at all 40 known two-move failures, for welfare, leximin and Pareto. Earlier,
  W^sub had no stuck state on over 45 million partial EFX₀ states, which include every state of the screen set, the
  suite, small cores, PW5/RD5, B< and B>, random instances at $k = 3$–7, and the CH-F welfare maxima of
  Proposition 4.5. The two-move forms do hold for $n \le 3$ where checked: at $n = 2$ for every strict type profile
  with $k \le 4$ (the session's Theorem N2, computer-verified by a C enumeration and an independent Python one [Cert];
  the referee found its reduction to finitely many type classes, Lemmas TD and OR, CORRECT and reproduced the 45,999
  classes, `k4/referee/haxell_n2.md`),
  and at $n = 3$ for P^sub with $k \le 3$ (14,100 type classes, C checker only).
- *A warning.* The radius grew from two to three moves at $n = 4$, and it may keep growing with $n$.

**(b) Question W($k$): welfare maxima** (`kgen/charity.md` §6).

> **Question 12.9 [C].** Is there an $f$, independent of $n$, with W($k, f$)? That is: does every $k$-limited instance
> have a welfare maximum over partial EFX₀ allocations leaving at most $f$ goods out?

- W($k, f$) implies a charity bound $f(k) \le f$ (§4.4).
- W(3, 0) and W(4, 0) fail (GM4-G, `w_brute.log`), and W(3, 1) and W(4, 1) fail by Proposition 4.5. So $f \ge 2$ is
  needed at both $k = 3$ and $k = 4$.
- The S′($\sigma, k$) family is the natural test: if it carries welfare-maximal stranded states for every $\sigma$,
  W($k$) fails for every $f$. The $\sigma = 4$, $k = 4$ search (three goods stranded, $n = 20$) was running when this
  draft was written.

At $k = 4$ the only $n$-independent charity bounds proved are those of §4, for instances whose goods have few valuers.
The open case is connected instances whose unallocated goods all have many valuers (Corollary 4.3).

### 12.6 RD²: two rounds of disjoint chains

> **Conjecture 12.10 (RD²; ledger K4.KSENS.RD2, `k4/ksens.md` §6, §8) [C].** For every $k$ and every additive
> instance, from every maximum-matching SD start, two rounds of vertex-disjoint improving chains, applied one after
> the other, reach bases with a one-absorber completion.

RD² is the round conjecture, and it is where "two moves" is still alive at every $k$. Sequential chains do not stay
at two: two chains fail at $k = 7$ (PW(4, 3, 6), §8 [V]), and within PW the least number of chains is
$\lfloor (k-1)/2 \rfloor$ for $k = 5, \dots, 9$. One round repairs all 90 PW instances tested ($k = 5$–$9$,
`round_pw.log`) [E].

*Certified* [Cert] wherever two chains are, since a chain is a round:
- $k = 4$: every strict core profile with $n \le 4$;
- $k = 5$: every strict profile of all 617 connected $n = 3$ hypergraphs, of the 1,138 core-like $n = 4$ ones with
  $m \le 7$, and of 25 named ones;
- $k = 6$: CGM's three-agent hypergraph (§8), and the exact sweeps finished so far.

One round is false in three places:
- at $k = 4$, on the 11 cores of Proposition 7.4 ([V], §7.3);
- at $k = 5$ (RD5, Proposition 7.8);
- with every value positive (RD5+, §7.5, refuting ROUND⁺).

Two rounds repair all of them. In RD5 the first round releases the foreign picks and the second collects them. For
this mechanism two rounds suffice however many picks are needed.
- *Evidence* [E]: climbs at $n \le 6$, $k = 5, 6, 8$ found no start needing three rounds. The ROUND⁺ session's
  climbs found starts needing exactly two rounds at $n = 4, 5$, never three (`proof/kgen-rounds`).
- *Strength*: RD² for every $k$ contains EFX₀ existence for all additive instances.
- *A design to try next*: RD5's mechanism one level deeper, which needs $n \ge 6$. No construction for depth is
  known (`attempts/k4-ksens-depth-composition.md`).

### 12.7 Smaller questions

- *OC₁ at $k = 3$ for every order* (candidate theorem OT, `k4/k3_oc1.md` §4). The open drafts are those covered by
  neither Theorem 9.4 nor Theorem 9.5: least deficit 2, or exposed agents sharing junk goods. The exhaustive
  computation of §9 settles $n \le 4$ for connected instances; $n = 5$ from maximum-matching starts was running.
- *The ladder.* Conjecture L of `k4/ksens.md` §4 ($\lfloor (k-1)/2 \rfloor$ chains from every order) is false at
  $k = 4$ (Proposition 7.4). The $k$-sensitivity session's corrected form is **Conjecture L′** [C]: from every
  maximum-matching start, $\lfloor k/2 \rfloor$ chains suffice. Every rung known fits it:
  - $k = 3$ needs one chain (exhaustive at $n \le 4$);
  - $k = 4$ needs two, which is tight, and two suffice at $n \le 4$ [Cert];
  - $k = 5$ needs two in the PW family;
  - $k = 7$ needs three, from a maximum-matching start (PW(4, 3, 6), §8) [V];
  - $k = 9$ needs four in PW(5, 4, 8), by one SAT encoding only [E].

  The deciding rung is $k = 6$: does it need three chains? The exact $k = 6$ sweeps have found no start needing a
  third chain so far. L′ for every $k$ contains EFX₀ existence. Rounds are the other count (Conjecture 12.10).
- *Bounded charity CH($k$) at $k = 4$*: is there an $f(4)$ independent of $n$ and $d$? Theorem 4.1 gives
  $\min\{2d - 1, R(d)\}$.

## 13. References

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
  §2, §9 (`proofs/citations.md`). Version v4 (with more authors) contains the monotone three-agent, eight-good
  counterexample used in §9.4. The monotone session read v4 §2 and §3.1–§3.2 (`monotone/threshold.md` §1). The
  referee rebuilt the instance as described and confirmed it, but did not verify the attribution.
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

**Referee.** `k4/referee/README.md` on main at `15dbe93`, items 1–67. Item 68, on the Lean statement of BASE-R, is
on `claude/k4-referee` at `11cae62f` and not yet on main (§11.10). Statuses are from LEDGER.md on main at `15dbe93`
plus PR #155 (`claude/kind-lamport-y8fdme`) at `8943344`. The checks are under `k4/referee/*.py`, with logs under
`results/k4_referee/`.

**Sources.** The "head" column is the branch head when this draft was written. "Unchanged" means the cited sections
were compared between the refereed commit and the head by this write-up's session: proofs identical, at most remarks
or citations added.

| result here | source (branch) | refereed at | head | cited sections since | report | verdict |
|---|---|---|---|---|---|---|
| Fact 3.1, Lemmas 3.2–3.3, Theorem 3.4, Cor. 3.5 | `kgen/n3.md` §9 (`claude/kgen-n3`) | `418f876` | `419960c` | unchanged (literature paragraph added) | `kgen_n3.md`, `lit_n2.md` | CORRECT |
| Prop. 3.6 (H) | `kgen/n3.md` §10 | `eb95583` | `680d177` | unchanged; **sign fix not yet applied in the source**; applied here | `proph.md` | CORRECT WITH FIXES (applied here) |
| Theorem 4.1, Cor. 4.3 | `kgen/charity.md` §8 (`claude/kgen-charity`) | `1e986c6`, `0c85d91` | `0c85d91` | unchanged | `chkd.md` | CORRECT |
| Theorem 4.2 | `kgen/charity.md` §2–§3 | `78deef1` | `0c85d91` | unchanged (Prop. DU added) | `charity.md` | CORRECT |
| Prop. 4.4 (DU) | `kgen/charity.md` §3 | `8862555` | `0c85d91` | unchanged | `charity.md` §5, `chf.md` | CORRECT |
| Prop. 4.5 (CH-F) | `kgen/charity.md` §6, `attempts/kgen-charity-welfare-maxima.md` | `8862555` | `0c85d91` | unchanged | `chf.md` | CORRECT |
| Theorem 5.1, Cor. 5.2, Lemmas 5.4–5.6 | `k4/girth.md` §3–§4 (`claude/k4-girth`) | `5b79844`, `90c116f` | `235bca4` | unchanged (a remark on the valuation class added) | `girth.md` | CORRECT (PARK: state $N \ne \emptyset$) |
| Prop. 5.3 ($H_t$) | `k4/girth.md` §4 | `90c116f` | `235bca4` | unchanged | `girth.md` §5 | CORRECT ($HH_t$ not rebuilt) |
| Lemma 5.7 (EC), Cor. 5.8 | `k4/girth.md` §5 | `235bca4` | `671cd1b` | unchanged | `girth.md` §6 | CORRECT (premise "(3) when parking starts" stated here) |
| Lemmas 6.1, 6.2 | `k4/sdc.md` §28, §31 (`claude/kind-lamport-y8fdme`) | `d48084e` | `62946e0` | unchanged (Lemma RED and the OC₁^max refutation appended) | `maxsd.md` | CORRECT |
| Lemma 6.3 | `k4/oc1_hall.md` §19 (`claude/k4-oc1-hall`); `k4/ttc.md` §13 | `e2b4701`; `77bcab1` | `1a40886` | unchanged | `maxsd.md`, `oc1_hall.md` §6, `ttc_t5.md` | CORRECT |
| Prop. 7.5 (PW5) | `k4/ksens.md` §1 (`claude/k4-ksens`) | `ceba5c7` | `6308933` | unchanged | `ksens.md` | CORRECT (the aside on one-agent moves is incomplete but not needed) |
| Lemma 7.6 (PL) | `k4/ksens.md`, status block | `7ec7073` | `6308933` | unchanged | `ksens.md` §5 | CORRECT |
| Lemma 7.7 (PWk(a)) | `k4/ksens.md` §7 | `7ec7073` | `6308933` | fix applied in the source | `ksens.md` §5 | CORRECT WITH FIXES (applied) |
| Prop. 7.4 (both instances; all 11 cores) | `k4/oc1_hall.md` §22; `k4/oc1cert.md` (`compute/k4-oc1max-cert`) | `a14932d`; `fa8e971` | `a6b1e0c`; `46a9006` | instances unchanged | `oc1_hall_d1.md` §2, `oc1cert.md` | CONFIRMED |
| RD5+ (Remark, §7.5), Lemma 7.9 (R1), Cor. 7.10 | `kgen/rounds.md` §1, §3 (`proof/kgen-rounds`) | `a33b135` | `e0a2d42` | §1 unchanged | `rounds_r1.md` | CORRECT; refutations CONFIRMED; the two-round repair fixed here |
| Lemmas 9.1, 9.2, Theorems 9.4, 9.5 | `k4/k3_oc1.md` §2–§3 (`claude/k4-k3-oc1`) | `949718a` | `48bcf05` | unchanged (B\*'s statement clarified) | `k3_oc1.md` | CORRECT (R1C: DE's core case) |
| Lemma 9.3 | `k4/k3_oc1.md` §2 | `949718a` | `48bcf05` | **fix not yet applied in the source**; applied here | `k3_oc1.md` §3 | CORRECT WITH FIXES (applied here) |
| Lemma 9.6, Theorem 9.7 (M3) | `monotone/k3.md` (`claude/monotone-k`) | `06e4b02` | `8157265` | unchanged | `mono_m3.md` | CORRECT (the $k = 8$ attribution not verified) |
| §9 exhaustive $k = 3$ claim | `k4/ksens.md` §8 (`claude/k4-ksens`) | `08883f6` | `be55a01` | not re-compared | `ksens.md` §6 | CONFIRMED exhaustively ($n = 3, 4$) |
| Theorem 10.1 | `k4/vm.md` §1–§2, §8 (`claude/k4-vm`) | `7a78df6` | `559eec6` | unchanged | `vm.md` | CORRECT (ordinary EFX; the reconstruction) |
| Lemma 11.1 (T6), Cor. 11.2 | `k4/ttc.md` §14.2 (`claude/k4-ttc`) | `71c7b83` | `dd993e9` | unchanged | `ttc_t6.md` | CORRECT; certificate confirmed on all 11 |
| Lemma 11.3 (M), Lemma EX | `k4/matching.md` §1, §3 (`proof/k4-matching`) | `2c0198e` | `5fc71a9` | unchanged (the referee's minor point on the $\min_H$ form added) | `matching.md` | CORRECT |
| Lemma 11.4 (EX\*), Lemmas 11.19–11.20 | `k4/matching.md` §5–§6 | `0ee5969`; extension `7e6cd80` | `5fc71a9` | unchanged except data counts (3,190 → 3,179) | `lift.md` §1–§3, §7 | CORRECT |
| Lemma M^c | `k4/oc1max_multi.md` §9 (`proof/k4-oc1max-multi`) | `3d157f3` | `56cd676` | unchanged | `oc1max_multi.md` §9 | CORRECT |
| Lemmas 11.5, 11.7, 11.8, Props. 11.6, 11.9 | `k4/oc1_hall.md` §21 (`claude/k4-oc1-hall`) | `a14932d` | `a6b1e0c` | unchanged (one remark on Theorem U updated) | `oc1_hall_d1.md` | CORRECT |
| Theorem D1-C | `k4/d1.md` §3 (`proof/k4-d1`) | `a9232a0` | `6f6c3be` | unchanged | `d1.md` | CORRECT |
| Lemmas 11.10, 11.12, 11.15–11.17, Prop. 11.11 | `k4/oc1max_multi.md` §2–§4, §6 | `6959fc9`, `1ccbb94` | `56cd676` | statements unchanged; the referee's wording fixes applied in the source | `oc1max_multi.md` | CORRECT |
| Theorem 11.13 (U), Cor. 11.14 | `k4/oc1max_multi.md` §3 | `d31a8f1` | `56cd676` | unchanged (a paragraph on $D_T = \{k\}$ added) | `oc1max_multi.md` §8 | CORRECT |
| Lemma 11.21 (LIFT) | `k4/oc1max_multi.md` §8 | `0d26500` | `56cd676` | unchanged | `lift.md` §4 | CORRECT |
| Lemma 12.3 (RED, as RED₃) | `k4/k3_oc1.md` §11 (`claude/k4-k3-oc1`); `k4/sdc.md` §31 | `974853c` | `84160e3` | unchanged | `k3_oc1.md` addendum | CORRECT |
| K4.MC8 (Appendix B) | `k4/TWINS.md` §1 (`proof/k4-twins`) | `29bb2e6` | `49b10b3` | theorem unchanged ($\beta = 5$ counts added) | `twins.md` | CORRECT (certified reduction) |
| Theorem 11.18 (S), Lemma HS, HS-U1 | `k4/oc1max_multi.md` §10 (`proof/k4-oc1max-multi`) | `b107719` | `3143a33` | unchanged (the referee's wording remark on Theorem U applied) | `oc1max_multi.md` §10 | CORRECT (log613's printed values need a fix; not printed here) |
| Lemma 11.22 (SD-E), Theorem 11.23 (REC-S) | `k4/oc1max_multi.md` §12 | `6c3fd95`, proofs unchanged at `10d3bdf` | `3143a33` | the perfect-start hypothesis made explicit and the referee's remarks added | `oc1max_multi.md` §11 | CORRECT ((L) redundant) |
| Prop. 11.26 item 8 (K4.MULTI.RECS.N4) | `k4/oc1max_multi.md` §12 | `b8bdc69` | `3143a33` | not re-compared | `oc1max_multi.md` §12 | CONFIRMED (all 112,880 witnesses) |
| Prop. 11.26 item 7 (OC₁′^max) | `k4/sdc.md` §31, `kgen/rounds.md` §4.6 | main `9cb9a45` | main `c6a7a44` | not re-compared | `oc1prime.md` | CONFIRMED at $n = 5$; $n = 4$ correct conditional on the export |
| Prop. 11.26 item 7 (the splice sketch) | `kgen/rounds.md` §4.10 (`proof/kgen-rounds`) | `f91c6bc` | `f436bf9` | not re-compared | `rounds_r1.md` addendum | **GAP** (the $n = 4$ data claim stands) |
| Prop. 11.26 item 5 (R2-M, R2★ refuted) | `results/k4_oc1max/r2m_fails_n4.jsonl` (`compute/k4-oc1max-cert`) | `c0de02c` | `352db21` | data file | `r2m.md` | CONFIRMED (all 306) |
| Lemmas 11.24 (LIFT\*), 11.25 (PHANTOM); Prop. 11.26 item 9 (RSD.N4); RSD-IND | `k4/matching.md` §6 (`proof/k4-matching`) | `8498cde` | `e2e4b79` | unchanged | `lift.md` §8 | CORRECT; CONFIRMED; RSD-IND FALSE as written |
| §8, N3K5 and N3K5⁺ | `k4/ksens.md` §8 (`claude/k4-ksens`) | `1ac11ad` | `1ac11ad` | — | `ksens.md` §7 | CONFIRMED |
| §12.3, VM1 fails on the core P34 | `attempts/k4-vm-vm1-core.md` (`claude/k4-vm`) | `b5a2d6a` | `3b936a7` | not re-compared | `vm.md` §7 | CONFIRMED |
| §12.5, Theorem N2's type reduction | `k4/haxell.md` §6 (`claude/k4-haxell`) | `158b4d9` | `a4355b2` | not re-compared | `haxell_n2.md` | CORRECT |
| Appendix B: release lemmas ($k = 3$) | `k4/k3_oc1.md` §12; `kgen/n3.md` §15.6 | `9719be2`; `a319483` | `9719be2`; not re-compared | — | `k3_release.md` | CORRECT |
| Appendix B: Lemma WG | `k4/oc1max_multi.md` §13 | `6b6cf7b` | `8924c6b` | unchanged | `oc1max_multi.md` §13 | CORRECT (K-loc WRONG as stated; phantom class GAP) |
| Appendix B: K4.MC8 filter | `k4/TWINS.md` §1 (`proof/k4-twins`) | `450a58f` | not re-compared | — | `twins.md` addendum | SOUND |
| §11.10, Lemma RF-PATH (both forms) | `k4/girth.md` §7 (`claude/k4-girth`) | `8f7ba8a`, `712a568` | `db48160` | not re-compared | `girth.md` §7 | CORRECT |
| §11.10, Lemma RF-ROT | `k4/ttc.md` §14.7 (`claude/k4-ttc`) | `d451ea0` | `0247c41` | not re-compared | `girth.md` §7 | CORRECT |
| §11.10, RF residue lemmas (RF-A1, RF-B, REPAIR-Y, RF-B4) | `k4/oc1_hall.md` §24.6, §24.8 | `01f986d` | main `898d80b` | not re-compared | `oc1_hall.md` addendum | CORRECT |
| §11.10, Theorem S^φ; SD-E(round); S^φ(round) | `k4/oc1max_multi.md` §16–§17 (`proof/k4-oc1max-multi-2`) | `52f5b0b`; `85981d1`; `d10b8f2` | not re-compared | — | `oc1max_multi.md` §14–§16 | CORRECT WITH ONE FIX (S-φ3); CORRECT; CORRECT |
| §11.10, ROUND-RSD witnesses; LIFT\* for rounds | `k4/matching.md` §6 | `56e64a9` | not re-compared | — | `lift.md` §9 | all valid; CORRECT |
| §11.10, K4.MULTI.ROUNDE.SEL2 | `proof/k4-oc1max-multi-2` | `4f8a992` | — | — | `oc1max_multi.md` §17 | CONFIRMED |
| §11.10, Proposition SEP; K4.BASE.DEAD.N4; K4.BASE.P1FREE.N4 | `k4/base_phantom.md` (main) | `0e6d9ab` | main `898d80b` | not re-compared | `basephantom.md` | CORRECT; CONFIRMED; CONFIRMED |
| §11.10, Lemma SPLICE; RECS.EXIST.N5 | `kgen/rounds.md` §4.10 | `7ffbfd2` | not re-compared | — | `rounds_r1.md` addendum 2 | CORRECT WITH TWO SMALL FIXES; CONFIRMED |
| §11.10, pick-graph lemmas, ROUND-SIMPLE; UNTANGLE (1)–(5) | `kgen/rounds.md` §4.11, §4.13 | `d79599e`; `50c1fc4` | not re-compared | — | `rounds_r1.md` addenda 3–4 | CORRECT |
| §11.10, K4.MC9 | `k4/TWINS.md` §4 (`proof/k4-twins-2`) | `ea71fb5` | not re-compared | — | `twins.md` addendum 2 | SOUND |
| §11.10, Lemma B3, Cor. B3′ (item 58) | `k4/base_phantom.md` §5.1 (`proof/k4-base-phantom`) | `172e856` | `cd4a74b` | not re-compared (file grew) | `basephantom.md` addendum | CORRECT (B3′ wording remark) |
| §11.10, Lemma RF-T, Cor. RF-T′ (item 59) | `k4/girth.md` §7 (`claude/k4-girth`) | `3e64bf0` | `56941dc` | not re-compared (file grew) | `girth.md` §7 (end) | CORRECT |
| §11.10, Lemma RF-B′ (item 60) | `k4/oc1_hall.md` §24.10 (`claude/k4-oc1-hall`) | `7336e31` | `143e33c` | not re-compared (file grew) | `oc1_hall.md` addendum | CORRECT |
| §3 and Appendix B, kgen-n3's remaining items (item 61) | `kgen/n3.md` §2, §11, §15 (`claude/kgen-n3`; on main via PR #97) | `0bfe993` | `a684169` | not re-compared (6 lines added, 3 removed) | `kgen_n3.md` addendum | CORRECT (G3 wording) |
| §11.10, SINK form of DEMOTE (item 62) | `k4/girth.md` §7 | `ea279bb` | `56941dc` | not re-compared | `girth.md` §7 (end) | a CONJECTURE (no new proof) |
| §11.10, Lemma C13, class (1, 3) (item 63) | `k4/ttc.md` §14.8 (`claude/k4-ttc`, PR #125) | `699cc11` | `884310d` | not re-compared | `ttc_c13.md` | CORRECT WITH FIXES (fix (0), "d is a receiver", applied here) |
| §11.10, Conjecture RKMAX at $n = 4$ (item 64) | `k4/sdc.md` §31 (`claude/kind-lamport-y8fdme`) | `c1b2756` | `8943344` (snapshot) | not re-compared | `rkmax.md` | CONFIRMED by a second implementation |
| §11.10, Lemma RF-A1\*, Lemma NA (item 65) | `k4/k3_oc1.md` §13.5 (`claude/k4-k3-oc1`) | `17777f1` | `68f6a4c` | not re-compared | `k3_oc1.md` addendum | CORRECT |
| §11.10, RF-𝒦, RF-TOP, ABS, census; Lemma REC-∃ (item 66) | `k4/RFMIN.md` (`proof/k4-rf-min`, PR #156) | `d32e566` | `824d660` | not re-compared | `rfmin.md` | RF-TOP, ABS CORRECT; RF-𝒦 CORRECT WITH FIXES (needs a receiver, supplied by REC-∃); census CONFIRMED; REC-∃ proved by the referee |
| §11.10, the 32 T\* certificates (item 67) | `k4/girth/oc1_tstar.py` (`claude/k4-girth`) | `bbf55da` | `56941dc` | unchanged | `girth.md` addendum (T\*) | CONFIRMED by replay |
| §11.10, the Lean statement of BASE-R (item 68) | `lean/EFX/BaseR.lean` (PR #151, on main) | PR #151 | main `15dbe93` | — | `basephantom.md` addendum (on `claude/k4-referee`) | the corrected BASE-R, not GRR |

**Not refereed, included with their verification status.** These are:
- Propositions 7.1–7.3 and 7.8; the Remark in §7.2; the one-round failure at $k = 4$ and the R1-priority remark in
  §7.3; the refutation of Conjecture W in §12.5;
- the $k$-ladder cells marked [V], [Cert] or [E];
- Propositions 9.8, 9.9 and 11.26 (items 1–5; the referee re-checked samples, and items 6–8 in full);
- in §11: the [W] statements, S2-X, the $n = 5$ refutation of LIFT-SHAPE⁺, the $n = 4$ refutations of R2-O and
  R2-E, the $n = 5$ counterexamples to RSD-IND's existential form (5_pure #419, #447), the $n = 5$ census (§11.6),
  and the ROUND-P counts;
- the refutation of T′_k (§9), and the refutations of W^sub and L^sub (§12.5);
- in §11.10: R2 at $n = 5$, K4.BASE.P1FREE at $n = 5$, Conjecture RF's evidence, Conjecture BASE-R's evidence, and
  this write-up's reading that `ConjBasePhi` fails at T3;
- in §11.10 (revision 8): the $k = 5$ refutation of RF's every-order form (K4.SDC.RF.K5EVERY), RF at $n = 3$,
  $k = 5$ (K4.KSENS.RF5), RKMAX beyond $n = 4$ (5_pure #419, #447, #38 and SEL2), its $k = 5$ refutation
  (K4.SDC.RKMAX.K5), the refutation of plan (a) at 5_pure #358, the coverage counts of the DEMOTE classes at $n = 5$,
  the refutation of GRR, and K4.BASE.GR.SEL2;
- in §8 and §12.6: two sequential chains failing at $k = 7$ (K4.KSENS.CHAINS), CGM's hypergraph at $k = 6$
  (K4.KSENS.CGM6), and the certificates behind RD²;
- every conjecture of §12.

Heads were re-checked at about 06:50 UTC on 2026-11-27. Main has since moved to `309e132` (PR #134, `k4/vm.md`
data only); LEDGER.md is unchanged there. PR #155's branch has moved past the snapshot `8943344` (burst 10, RFσ),
which this revision does not include.

**Lean.** This write-up's session ran `lean/check.sh` on branch `formal/k4-oc1max` twice.
- At `838fb0e`: CHECK PASSED, with 1,246 audited statements and 2,350 theorems.
- At `28f3e1e`, which adds `lean/EFX/OC1Perf.lean`: CHECK PASSED, with 1,253 audited statements and 2,358 theorems.
  The coordinator reports the same.

Both runs have every declaration on `propext`, `Classical.choice` and `Quot.sound` only, and the `leanchecker` replay
passing. The certificates for `EFX.OC1Max.sdpo`, `EFX.OC1Max.exists_order_maximum`, `EFX.OC1Max.max_no_augment`,
`EFX.OC1Max.picks_no_junk`, `EFX.OC1Max.target4_of_conjOC1maxWith`, `EFX.OC1Max.red` and
`EFX.OC1Max.target4_of_conjOC1perfWith` are in `paper/campaign/lean_check_oc1max.log`. The frames are implications;
their one-move hypotheses are false (Proposition 7.4). That branch has since been merged.

A third run, on main at `898d80b0`, which includes the frames and tools of §11.10 (PRs #141, #143, #149), gave
**CHECK PASSED**: 1,371 audited statements and 2,644 theorems, with a warning-free build and no `sorry`. All 10,002
declarations of the library use only `propext`, `Classical.choice` and `Quot.sound`. The certificates of the
declarations cited in §11.10 are in `paper/campaign/lean_check_main.log`:
- `EFX.OC1Max.target4_of_conjRF` and `conjOC1exmax_of_conjRF`;
- `EFX.Round.target4_of_roundRSD`, `exists_efx0_of_rounds`, `inv_of_reach` and `lift_base`;
- `EFX.Round.liftStar`;
- `EFX.OC1Max.thmS` and `thmS_oc1`;
- `EFX.Round.oc1PhiAt_of_sPhi` and `conjBasePhi_of_sPhi`.

A fourth run, on main at `15dbe933`, which adds `lean/EFX/BaseR.lean` and `lean/EFX/Sep.lean` (PR #151), gave
**CHECK PASSED**: 1,389 audited statements and 2,666 theorems, with a warning-free build and no `sorry`. All 10,049
declarations of the library use only `propext`, `Classical.choice` and `Quot.sound`. The certificates are in
`paper/campaign/lean_check_main_15dbe93.log`: those of the third run, and
- `EFX.Round.target4_of_conjBaseR`, `target4_of_conjGR`, `conjGR_iff_conjBaseR` and `liftedAt_iff`;
- `EFX.Round.sep_small`, `sep_one`, `sep_two`, `sep_three` and `liftSep`.

These are implications, and none of their hypotheses is proved. As §11.10 explains:
- `ConjRF`, as stated on main, is false: it requires a unique receiver;
- `ConjBasePhi` is false at T3;
- `ConjBaseRWith` is the corrected Conjecture BASE-R, which is open.

## Appendix B. Other refereed results

The referee also found these results CORRECT. They support the conjectures of §12 but are not developed in this
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
- *K4.MC8, double edges in a minimal counterexample* (`k4/TWINS.md` §1, branch `proof/k4-twins` at `29bb2e6`, PR
  #117; report `k4/referee/twins.md`: CORRECT, as a certified reduction).
  - Let $H$ be a minimal counterexample to TARGET₄ (or one within $\mathcal C_\beta$) with strict types, and let
    $e \ne f$ be agents sharing two goods that no other agent values. Then at least one of $e, f$ is a Q4 agent: four
    relevant goods, none private.
  - More precisely, every strict type profile of the pairs Q3–Q3, Q3–P4 and P4–P4 is excluded, with or without a
    further common good. Q3–Q4 and P4–Q4 with a further common good are excluded too. The remaining pairs are
    reduced on most profiles (for example 1,708 of 1,728 for open Q3–Q4).
  - The exclusions are local reductions certified through Lemmas M1 and M1(b) (ledger K4.MC1). Two implementations
    agree on every count.
  - The referee checked three things: the gadgets are legal and keep $\mathcal C_\beta$; M1(b) is the lemma used;
    and 773,190 stored extensions realized on 710 concrete instances, with 0 failures. A mutation is caught. Effect:
    of the 5,558 $\beta = 4$ candidate cores of K4.MC7, 2,392 contain a certified double edge.
- *Lemma EX* (`k4/matching.md` §3; report `k4/referee/matching.md`): CORRECT as a sufficient condition (§11.3). The
  same report confirms the refutation of "deficiency at most 1 at perfect starts" (`k4/matching.md` §2).
  - The referee later found the session's candidate filter, and its prune at the level of Γ′, sound
    (`k4/referee/twins.md`, addendum). It reproduced the counts: at $\beta = 4$, 2,392 of the 5,558 candidate cores
    have a certified double edge and 3,166 do not; at $\beta = 5$, $n = 6$, the counts are 9,455 and 20,882.
- *The release lemmas at $k = 3$* (`k4/k3_oc1.md` §12, branch `claude/k4-k3-oc1` at `9719be2`; `kgen/n3.md` §15.6,
  branch `claude/kgen-n3` at `a319483`; report `k4/referee/k3_release.md`: all six CORRECT). These are the tools
  behind Conjecture T′ (§9):
  - Lemma 4, shared pairs die together;
  - Lemma 5, the release count: a trade with $q$ pair-takers gives $\omega' = \omega - r$, where $r$ is the number of
    released goods, and no owner is needed iff $r \ge \omega$, or $r \ge \omega - 1$ using $k$'s slot;
  - Lemma 6: in a hard state every terminal has a frozen exposed agent;
  - Lemma 7, the pointer walk: if no single rotation is valid, the walk closes into a cycle with at least two pair
    arrows;
  - kgen-n3's Lemma G5 and Corollary G5′: rotations by Rule E, the earliest-wanter rule, keep the want graph acyclic.
    Rule E is needed: arbitrary need chains give 2,678 cycles.
- *kgen-n3's remaining written items* (`kgen/n3.md` §2, §11, §15.2, §15.5, §15.17, §15.18 at `0bfe9933`, PR #97, on
  main; referee item 61, `k4/referee/kgen_n3.md` addendum: all CORRECT, with one wording remark on G3).
  - *Lemma R, reachability.* An EFX₀ allocation $X$ is a one-absorber completion after some chain with path
    $x_0, \dots, x_t$ iff three conditions hold for the sets $H^*_i = X_{x_i} \cap J \cap R_{x_i}$ (and
    $H^*_0 = X_{x_0} \cap (J \cup B_{x_t}) \cap R_{x_0}$): placement of the passed picks, the gains, and at most one
    absorber. So OC₁ is a statement about EFX₀ allocations with prescribed pick positions.
  - *Lemma P, peeling.* If $v_z(y_z) \ge v_z(M \setminus y_z)$ and OC₁ holds for $\pi - z$ on $I - z - y_z$, it holds
    for $\pi$ on $I$. *Lemma S:* in an EFX₀ allocation a pick is lost only as a singleton of another bundle.
  - *Corollary 3* (§3 above): with Theorem 3.4, OC₁ for every order with $n - 2$ iteratively top-heavy picks.
  - *The one-terminal gap at $k = 3$* (maximum-matching starts after R1C and B\*). Lemma G1: B\* applies iff
    $|E_t| = 1$. G2: $t$ holds $b_t$ or $c_t$. G3: after a need-chain rotation into $t$, the exposed set is
    $E_t \setminus \{k\}$. G4: a rotation that gives every receiver its top keeps the want graph acyclic.
  - *Proposition A.* If some $k \in E_t$ has a pair that no other exposed agent shares, and the other exposed pairs
    minus $k$'s pair have a common good, then $k$'s Rule E rotation completes with owner $k$. Corollary A1 covers
    $|E_t| = 2$ with distinct pairs.
  - *Lemmas G6, G7.* With $t$ last in Rule E's order, $t$ stays a terminal after the rotation. Its new exposed agents
    are old exposed agents with pairs disjoint from $k$'s, or agents holding their top with pair $\{g, j\}$, where
    $g$ is $t$'s new good and $j$ is junk.
  - The referee's checks: 1,307 Proposition A cases at $k = 3$, with every terminal's completion EFX₀ and G6, G7 at
    all of them; 17,221 top-heavy cases for Lemma P and Corollary 3, with 0 violations.
- *Lemma WG, worthless goods* (`k4/oc1max_multi.md` §13 at `6b6cf7b`; report `k4/referee/oc1max_multi.md` §13:
  CORRECT, and (W1) is unused). Let $B$ satisfy (G1) and (G2), with owner $o$, and let $i \ne o$. Put $H = J \setminus
  R_i$, the junk goods worth 0 to $i$, and $X = B_o \cup (J \cap R_i)$. If $X$ threatens no agent other than $o$ at
  its value at $B$, and there are at least $|H|$ holders other than $o$, then $B$ has an S\* completion with owner
  $o$ and kept-out set $H$. It isolates the count behind SLOT2 and RING2 (§11.9): one holder per worthless junk good.
  The same report finds the session's Proposition K-loc **wrong as stated**, because the good $\ell$ can travel along
  the second chain to the receiver; its corrected form is exact on all data. It also finds a **gap** in the
  "phantom class" argument, which needs (G2) for phantom constraints. Neither is used in this draft.

## Appendix C. Reproducing the instance checks

`paper/campaign/check_instances.py` was written by this write-up's session from the draft's printed tables and the
definitions of §2.4. It uses only the Python standard library, imports nothing from the repository and uses no SAT.
Run it from the repository root:

```
python3 paper/campaign/check_instances.py          # about 25 s; log: paper/campaign/check_instances.log
python3 paper/campaign/check_instances.py quick    # skips the slowest instance (B<)
```

*Method.* For each instance it enumerates every complete EFX₀ allocation once, by backtracking over the goods. The
prune is sound: it cuts a branch only when some threat toward a bundle already exceeds what the threatened agent could
still reach, and threats never decrease as bundles grow. A state reached from the picks by one move has an EFX₀
completion $X$ if and only if $X$ meets the move's placement and gain conditions with the largest possible junk sets
$H$ (Lemma R of `kgen/n3.md` §2). Enlarging $H$ by goods its receiver values keeps every gain and only shrinks the goods
outside the bases, so this is exact for the free and for the one-absorber completion. Every "no state one move
reaches" claim is therefore a check over that list of allocations, with moves as in §2.4: additions, chains whose
passed bases are nonempty, and rings. Rounds and two sequential chains (RD5 only) are enumerated directly.

*What it checks* (77 checks; all pass, `paper/campaign/check_instances.log`):
- **Theorem 3.4**: the construction exactly as transcribed in §3.2, on 40,000 random two-agent starts. These come
  from 20,000 instances with ties, zeros and sparse values, $m \le 12$, in both orders. Every output is a complete
  EFX₀ allocation of shape (A1), (B) or (D).
- **Proposition 4.5**: the printed state is EFX₀ with strong charity and total 198. Welfare maximality is not
  re-checked here; the referee's exact search covers it.
- **Propositions 7.1 and 7.2**: the core conditions where claimed, that $X$ is partial EFX₀, that the left-out good
  fits nowhere, no dominating partial EFX₀ allocation over all $5^7$ partial allocations, and exactly 15 (resp. 58)
  complete EFX₀ allocations, each below $X$ for some agent.
- **Proposition 7.3**:
  - (a): B< and B> are strict connected cores, and order $0..5$ gives the printed picks. Of the 1,138 complete EFX₀
    allocations of B<, none completes the picks or a one-move state with one absorber. OC₁ fails for exactly 24 of
    the 720 orders. The printed free completion is EFX₀.
  - (b): the core is strict, connected and in the MC2 class. None of its 198 EFX₀ allocations completes the picks
    or a one-move state, even freely. The 12 failing orders and the 50 maximum-matching orders are as stated.
- **The Remark of §7.2**: no one-absorber completion at the picks or after any addition, chain or ring. A chain that
  passes an empty base repairs it. Under the free completion the picks extend.
- **Proposition 7.4**, both instances:
  - each is a strict connected MC2-class core in which every agent picks;
  - there are 14 (resp. 24) complete EFX₀ allocations, none completing the picks or a one-move state, even freely;
  - one round fails, by two methods: the backward characterization, and a forward enumeration of every round with
    every choice of junk sets;
  - two sequential chains repair, with one absorber;
  - there are 7 (resp. 6) maximum-matching pick vectors, 4 of them completing at the picks;
  - some R1-priority order gives the failing picks.

  The two round methods also agree on PW5 (one round repairs, as `k4/ksens.md` found) and on RD5 (it does not).
- **The ROUND⁺ remark of §7.5** (RD5+): one round fails, by both methods, and two sequential chains repair. The
  corrected two-round repair is a pair of legal chains and ends in an EFX₀ allocation. In the printed version, round 2
  would hand agent 2 the set $\{1, 6\}$, which the printed final allocation does not contain.
- **Corollary 11.2** on both instances of Proposition 7.4: every value-dominating EFX₀ allocation (6, resp. 4) has a
  blocked agent. In instance 1 that agent is always agent 0, holding $\{2, 5\}$.
- **The $n = 5$ start of §11.9 item 7** (5_pure #164), with the moves of §2.4:
  - it is a strict connected core, with the printed picks, one receiver ($z = 3$) and $D = \{0, 1, 2, 4\}$;
  - none of its 38 EFX₀ allocations completes the picks or a one-move state, even freely;
  - two chains repair, and the printed allocation is EFX₀;
  - after every first chain ending at $z$ (7 of the 39 chains from the picks), no second chain ending at $z$ with
    good 4 in $z$'s bundle leaves a state with a one-absorber completion. The source counts more first chains,
    because its move generator also lets chain agents take goods they do not value. Its conclusion is the stronger
    one;
  - no OC₁′ chain state has a free completion. At this start the OC₁′ rule adds no chain state beyond the ordinary
    ones.
- **S2-X** (§11.9 item 1): a core with the printed picks; $D = \{0\}$; good 7 wanted by agents 1 and 2; agent 3
  unfrozen and valuing junk good 3; no one-absorber completion at the picks; the chain $(0, 2)$ repairs. "Every
  canonical chain has HEAD" is not re-checked.
- **The R2 test** (§11.9 item 6): the picks, $D$, the receivers and $|J| = 3$ as printed; no one-absorber completion
  at the picks; one move repairs.
- **Lemma R2-0** (§11.8) on 1,234 random perfect starts with $|J| \le |U|$: junk to distinct receivers is EFX₀.
- **Lemma 9.6** on all 48 nondegenerate monotone orders of a 3-set (the linear extensions of the Boolean lattice): the
  surrogate weights reproduce every disjoint comparison.
- **Theorem 11.23's example**: on instance 1 of Proposition 7.4, $E(2) = (2, 1)$ is the earliest-wanter chain; with
  agent 2 taking $\{3, 4\}$ it is official; the reduced state is the SD outcome of the reduced order (Lemma 11.22);
  the chain $(0, 1)$ is official there; and the final allocation is EFX₀ and complete.
- **The R2 forms** at the first R2-M failure of the certifier's list (4_n4_2 #80): a perfect hard start with
  receivers $\{0, 1\}$; after no canonical chain to a receiver (in the certifier's sense) is there a completion with
  at most one junk good per agent (so R2★ and R2-M fail); some such chain has a one-absorber completion (R2-C); one
  move repairs.
- **The round of two disjoint rings** at 5_pure #164: both rings gain, and the allocation is EFX₀ and complete.
- **WS4 and LS4** (§12.5), with set transfers, swaps and rotations of every length: no composite of at most two
  moves gives a welfare step at WS4 or a leximin step at LS4, while the other measure has a step at each. The
  three-move target at WS4 is EFX₀.
- **T′_k at $n = 7$** (§9): the draft, its hardness (all $7^4$ junk assignments), and the absorbers of every
  one-absorber completion after each rotation ($\{3, 4\}$ both times, never none or $k$).
- **N3K5** (§8): the picks; no free completion after one move, rings included; one round fails, by both methods;
  two chains repair.
- **The RSD-IND counterexamples** (§11.9 item 7). Both are cores, and the picks are SD outcomes. Neither has a state
  within one move (19 and 41 moves) with a one-absorber completion, and some pair of vertex-disjoint chains repairs
  each. At #419 the two printed chains repair together, and each one's set threatens the agent that only the other
  chain lifts.
- **P34** (§12.3): a strict connected core, and the printed two-move completion is EFX₀.
- **5_pure #650** (§11.10): a strict connected core whose printed picks are an SD outcome. The start is perfect with
  receivers $\{1, 2\}$, and OC₁ fails. For each receiver $u$, some $u$-first order is maximum, and every maximum
  $u$-first order satisfies OC₁.
- **T3's base case** (§11.10): the picks, $D$ and the receiver; the round settling agent 2 with $\{1, 3\}$ is
  improving and satisfies (L\*). Afterwards the picks of agents 0 and 1 complete. No allocation of the present goods
  is EFX₀ between them while also not threatening agent 2 at $v_2(\{1, 3\})$.
- **K4.SDC.RF.K5EVERY** (§11.10, $k = 5$): at the picks $(6, 5, 4, 3)$, OC₁ fails and the only receiver is agent 2.
  The SD orders that put agent 2 first give six distinct pick vectors, and OC₁ fails at exactly one of them,
  $(6, 5, 3, 4)$, which is the twins' swap. So the every-order form fails and RF∃ holds there.
- **5_pure #358** (§11.10, plan (a) of RKMAX): the σ-maximal vectors are $(5, 6, 7, 2, 4)$ and $(5, 7, 6, 2, 4)$,
  with $\sigma = (3, 1, 0, 1)$. Each has the single receiver 3 and junk $\{0, 1, 3\}$. Its picks do not complete,
  and one move does. The printed values have two subset-sum ties (agents 0 and 3, as the core test reports). So the
  check also runs on a strict perturbation, $1000\,v + r$ with $r$ drawn from 1–99 (seed 0), which is a strict
  connected core with the same facts.
- **Lemma REC-∃** (§11.10), a random test, so evidence only: 4,000 random draws of an instance with $n \le 5$ and an
  order (seed 11). The 57
  maximum-matching starts without a receiver each have an agent without a pick, no junk good valued by anyone, and
  an EFX₀ completion of the picks. 0 failures.
- **Conjecture W (§12.5)**: the printed state is partial EFX₀. No composite of at most two moves (the move class of
  §12.5) reaches a better partial EFX₀ allocation, and three moves do.
- **Proposition 7.5**: 186 complete EFX₀ allocations, as the referee found. No free completion at the picks or after
  any addition, chain or ring. The failing start comes from exactly 12 orders, and $\nu = 5$.
- **Proposition 7.8**: the picks and the junk; no completion after one move; no completion after one round (free
  completion, rounds enumerated as sets of disjoint chains and additions); two sequential chains repair with one
  absorber.
- **§8**: the $k = 3$ "no repair" instance (the picks do not extend; one chain repairs) and DT5 (distinct tops, no
  one-absorber completion of the picks, a free one exists).

While this appendix was written, the check found one inaccuracy in an earlier wording of the Remark of §7.2. That
wording said the instance needs one chain under the free completion; in fact its picks extend freely. The text has
been corrected. The check also produced one new observation: one round does not repair the instances of
Proposition 7.4 (§7.3). The $k$-sensitivity session's two checkers and the coordinator have since confirmed it.

## Appendix D. Written after the referee's table (not included)

These statements have written proofs on their branches but had not been refereed when this draft was written. They
are **not** results of this draft, and nothing outside §11 refers to them. §11 lists them with the label [W] where
they enter the case tree:
- Lemma 1 of `k4/oc1_hall.md` (slots; leaf 1);
- Proposition D1-H₃′ and Lemma CONTRACT (`k4/d1.md` §7, branch `proof/k4-d1`; leaf 3b). The earlier Proposition
  D1-H₃ (§6 there) is an SMT computation, which the referee sampled but did not re-prove;
- Lemmas R2-0 and R2-G2 (`k4/ttc.md` §14.6; leaf 5a). Their short proofs are given in §11.8, and this write-up checked
  them.

The previous revision also listed Theorem M3, Theorem D1-C, Lemma RED and Lemma M^c here. All four have since been
refereed CORRECT: they are Theorem 9.7, the Theorem D1-C of §11.4, Lemma 12.3, and the Lemma M^c of §11.3.
