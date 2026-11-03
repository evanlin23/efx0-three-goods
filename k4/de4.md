# DE4: Draft and Exchange for four relevant goods

Workstream `proof/k4-de4` (branch `claude/kind-lamport-y8fdme`), ledger rows K4.DE4.*, open item 29. The aim was a
proof of TARGET₄ with the architecture of DE (`paper/k3-simple` in evanlin23/efx0-three-goods-proof): a state space of
holdings, a validity invariant, a finishing rule and an improvement step measured by a potential. **This file does
not contain a proof of TARGET₄.** It contains a state space and a potential for which *every maximum is completable*
on all data (the form of candidate that `k4/strategy.md` reports no potential over 𝒫 survived), written proofs of the
parts of DE that carry over, and the exact step that is missing.

**Status.**
- *Conjecture DE4* (§2): every maximum of the level sum (then value-Pareto) over the valid DE4 states of a strict R1-core
  profile has an EFX₀ completion. With the peeling lemma and the tie reduction it implies TARGET₄ (§2, Lemma 3).
- *Evidence* (§4): no failure on every strict profile of every core with n = 2 (252,288) and n = 3 (all 51 cores,
  439,582,464 profiles, C implementation), the 155 suite instances that fit (n ≤ 6, m ≤ 15), random profiles of every
  certified core with n = 3, 4 and 5, and 20,000 random R1-cores with tied values. Two implementations
  (`k4/de4/de4lib.py`, `k4/de4/de4.c`) agree on every profile compared. Also every strict profile of every n = 4 core
  with one 4-good agent (8,398,080). The algorithm form (DE4-ALG: draft, chains, DE's own rings) finished on every
  run: 155 suite instances and 21,060 random profiles of every core with n = 3 and n = 4.
- *Proved in writing* (§3, not refereed; each statement also checked by brute force as stated,
  `k4/de4/verify_lemmas.py`): the draft is valid; completions are sound; the upgrade (chain) lemma, which at k = 4
  needs an argument for three-good holdings; its corollaries (at a maximum nobody is threatened by the leftover goods,
  every agent holds a good, and few leftover goods can be absorbed); and DE's ring argument for the states in which
  it applies (Proposition 6).
- *Refuted* (`attempts/k4-de4-variants.md`, replay `python3 k4/de4/variants.py`): DE's own holdings; upper sets
  without the lower pair; every "minimal set beating a single value" (it contains the dead end of
  `attempts/k4-ls-dead-end.md`); value-Pareto maxima instead of the level sum; DE's single-owner finishing rule;
  owners restricted to agents holding at most one good.
- *Missing* (§5, made precise in §7): the improvement step. §7 proves it (Lemmas 7, 8, Theorem 9, Corollary 10) except in
  one case: DE's walk reaches a free agent holding two or more goods after a *partial* labelled arc was chosen. For that
  case Conjecture 11 names two bounded moves (P, K) that resolve every instance found.
- *Not in Lean.* Nothing here is formalized: the step that would make DE4 a theorem is missing, and the parts that are
  proved are short.

The output of a completion is not D2-shaped in general (hall-cyc6, §5), so DE4 says nothing about K4.D.

## 1. Definitions

**Setting.** After peeling by rule R1 (DE's peeling lemma, which holds for any number of relevant goods), every remaining
agent i values 3 or 4 remaining goods R_i and is strictly balanced: v_i(a_i) < v_i(R_i ∖ a_i) for its top a_i (if it
valued at most two, or its top were worth at least the rest, R1 would apply). Goods nobody values may remain. No rule
R2, no connectivity and no private-good bound are used. We write a ≻ b ≻ c (≻ d) for i's goods by value and assume
the profile **strict**: all subset sums of each R_i are distinct (ties: Lemma 3).

**Holdings.** A holding of agent i is one of:
- the empty set, or a single good of R_i;
- an *upper set*: S ⊆ R_i with v(S) > v(a) whose proper nonempty subsets are all worth at most v(a). For a 4-good
  agent these are {a, x} for every x, the pairs of {b, c, d} worth more than a, and {b, c, d} when v(b) + v(c) < v(a)
  (the agent is *big-top*); for a 3-good agent, {a, b}, {a, c}, {b, c};
- the *lower pair* {c, d} of a 4-good agent, when v(b) < v(c) + v(d) < v(a).

**Levels.** ℓ(∅) = 0; ℓ(a), ℓ(b), ℓ(c), ℓ(d) = 4, 3, 2, 1; ℓ(lower pair) = 3; ℓ(upper set) = 5. The lower pair
has b's level but more value: moving between them is a *lateral* move.

**States.** A state Y gives every agent a holding, pairwise disjoint; J is the set of *leftover* goods. Agent i *wants*
g ∈ R_i ∖ Y_i if v_i(g) > v_i(Y_i). Y is *valid* if
- (V1) every wanted good is the whole holding of some agent, and
- (V2) no holding threatens another agent: θ_i(Y_j) ≤ v_i(Y_i) for all i ≠ j, where θ_i(B) = max_{h ∈ B} v_i(B ∖ h).

An agent is *frozen* if its holding is a single wanted good, and *free* otherwise. F₁ is the set of free agents
holding at most one good.

**Completions.** A completion of Y gives every leftover good to some agent. Y is *completable* if some completion is
an EFX₀ allocation. DE's *single-owner rule* is the special case: one free agent o takes all leftover goods but a set
H, and each good of H goes to a different agent of F₁ ∖ {o}.

**Order.** Φ(Y) = Σ_i ℓ_i(Y_i). A *maximum* is a valid state with the largest Φ that no valid state with the same Φ
value-Pareto-dominates.

## 2. The conjecture

**Conjecture DE4.** For every strict profile of every R1-core (k ≤ 4), every maximum is completable.

**Improvement form** (stronger; what an algorithm would use). Every valid state that is not completable has a valid
state in which no agent's level is lower and either some level is higher or the values Pareto-improve.

**Conjecture DE4-ALG (the algorithm).** Peel by R1; draft (Lemma 2); then repeat: if DE's single-owner rule finishes,
stop; otherwise apply the chain of Lemma 4/4′ for the first agent (index order) that has an upgrade; otherwise trade
along DE's ring, built by DE's pointer rule: distinct leftover goods are chosen greedily, in index order, for the free
agents holding at most one good (each points to the first blocker, in index order, whose upgrade uses the fewest
leftover goods not yet used); frozen agents point to their first wanter; the walk starts at the first agent holding a
single good (the first free agent if there is none), and a free agent holding two or more goods gets its pointer, by
the same rule, only when the walk reaches it. The conjecture: the walk always closes a ring whose trade is valid and
improving. The loop terminates, because every move gives a state that is better in the order of §1 (a strict order on
a finite set). The same algorithm with the greedy choice made for *all* free agents fails (V7 of
`attempts/k4-de4-variants.md`, two n = 4 profiles). The states reached violate Proposition 6's hypotheses at some ring
steps (§4), so a proof would need invariants of the reachable states beyond Proposition 6.

**Lemma 3 (DE4 ⟹ TARGET₄).** Peel by R1 (DE's peeling lemma: the peeled agent's bundle is worth at least its remaining
goods and has at most one good). On the R1-core that remains, the draft (Lemma 2) is a valid state, so maxima exist,
and an EFX₀ completion of a maximum is an EFX₀ allocation of the core; the peeling lemma extends it. Ties: perturb
v_i to v_i + εw_i with w_i supported on R_i and all subset sums distinct; this keeps every R_i and strict balance, and
for small ε the profile is strict and of one fixed type for every ε, so an allocation that is EFX₀ for that type is
EFX₀ for all small ε and, the conditions being closed, for ε = 0 (K4.TIE of `k4/SCOUT.md` §2, unchanged). ∎

## 3. What is proved (written here; not refereed)

**Lemma 1 (structure).** In a valid state:
(a) Among an agent's holdings, a higher level never has a lower value, and a higher value never has a lower level.
(b) No good of a holding with two or more goods, and no leftover good, is wanted.
(c) A holding of two goods threatens nobody. The only holdings of three goods are the upper sets {b, c, d} of big-top
agents, so (V2) is a condition on those alone.

*Proof.* (a) Singles are ordered by value and level alike; v(b) < v(lower pair) < v(a) < v(upper set). (b) By (V1),
a wanted good is a whole one-good holding. (c) θ_i({g, h}) = max(v_i(g), v_i(h)), and by (b) neither good is wanted by
i, so each is worth at most v_i(Y_i) (or 0 if outside R_i). An upper set {a, x, y} is not minimal ({a, x} is worth
more than a), R_i is not either, and {b, c, d} is minimal exactly when every pair of it is worth less than a, i.e.
v(b) + v(c) < v(a). ∎

**Lemma 2 (the draft).** If the agents, in index order, each take the best of their goods not yet taken (or nothing),
the result is a valid state. *Proof.* As DE's draft lemma: if i wants g, then g was taken before i's turn as the whole holding
of an earlier agent, and holdings do not change during the draft. (V2) is empty: there is no holding of three goods. ∎

**Lemma 4 (upgrades).** Let Y be valid and x an agent with v_x(J ∩ R_x) > v_x(Y_x). Then a valid state Y′ exists in
which every agent's value is at least its value in Y and some agent's value is higher; the agents whose holding changes
all gain value, so (Lemma 1(a)) no level drops.

*Proof.* (i) *An upgrade inside J.* Let D = J ∩ R_x. Its goods are not wanted by x (Lemma 1(b)), so each is worth less
than Y_x (strict profile). We find an allowed holding N ⊆ D with v(N) > v(Y_x):
- Y_x = {a}: a minimal subset of D worth more than a is an upper set.
- Y_x = {b}: a is wanted, so D ⊆ {c, d}, hence (4-good) N = {c, d} with c + d > b; it is an upper set if c + d > a,
  else the lower pair. For a 3-good agent D ⊆ {c}: not possible.
- Y_x = {c} or {d}, or Y_x = ∅: D has at most one good worth less than Y_x, or D = ∅ (an agent holding nothing wants
  all its goods). Not possible.
- Y_x = lower pair: a is wanted (a > c + d), so D ⊆ {b}, worth less than c + d. Not possible.
- Y_x an upper set S of two goods: D ⊆ R_x ∖ S has at most two goods, each worth at most v(a) < v(S), so D is a pair
  worth more than a with both goods worth at most v(a): an upper set. For S = {b, c, d}, D ⊆ {a}. Not possible.

So N exists, and it has three goods only if x is big-top, Y_x = {a} and D = {b, c, d}. If such an x is free, take
N = {a, b} ⊆ Y_x ∪ J instead (an upper set; a is not wanted).
(ii) *The chain* (as in DE's chain lemma). Let j₀ = x and, as long as j_t holds a single good that some agent wants, let j_{t+1}
be the first such agent. If an agent repeats, the agents from its first occurrence on form a cycle in which each wants
the good of the one before; trade along it (each takes the good it wants). Otherwise the walk stops at j_k, and: x
takes N, each j_t (1 ≤ t ≤ k) takes the good of j_{t−1}, and the goods of the old holding of j_k that nobody took
become leftover (for a free x the walk has k = 0, and these are the goods of Y_x outside N). In both cases the
agents that move strictly gain value and the others keep their holdings, so every agent's wanted set can only
shrink. A good wanted in Y′ was wanted in Y, hence a one-good holding in Y; if its
holder moved, the good is now the whole holding of the next agent of the walk (the goods released at the end are not
wanted). So (V1) holds. Holdings of two goods threaten nobody (Lemma 1(c)); holdings that did not change threaten
nobody new, since nobody's value dropped.
(iii) *Three goods.* It remains the case where N = {b_x, c_x, d_x} (x frozen, big-top) threatens some agent i ≠ x in Y′.
Then v_i(J ∩ R_i) ≥ v_i(N ∩ R_i) ≥ θ_i(N) > v_i(Y′_i) ≥ v_i(Y_i), so i also satisfies the hypothesis. Its upgrade from
(i) is not a triple: otherwise i is a frozen big-top agent holding a_i with b_i, c_i, d_i ∈ J, and then N ∩ R_i ⊆
{b_i, c_i, d_i}; if N ⊄ R_i, at most two of these lie in N and θ_i(N) ≤ v(b_i) + v(c_i) < v(a_i); if N ⊆ R_i, then
N = {b_i, c_i, d_i} and θ_i(N) = v(b_i) + v(c_i) < v(a_i); either way i is not threatened. So the chain of i gives Y′
by (ii), with no three-good holding created. ∎

**Lemma 4′ (free self-upgrades).** If a free agent x has an allowed holding N ⊆ Y_x ∪ J with |N| ≤ 2 and v(N) >
v(Y_x), then x taking N and leaving Y_x ∖ N to the leftover goods gives a valid state better in value for x and equal
for everybody else. *Proof.* As (ii): released goods are not wanted (x is free), N is a pair or a single, wanted sets
only shrink. ∎

**Corollary 5 (at a maximum).** Let Y be a maximum (or any valid state with no valid state that is value-Pareto-better
by Lemma 4 or 4′). Then:
(a) v_x(J ∩ R_x) ≤ v_x(Y_x) for every agent x: the leftover goods alone threaten nobody;
(b) if some agent holds nothing, Y is completable: that agent is free and takes all of J;
(c) if |J| ≤ |F₁|, Y is completable: each leftover good goes to a different agent of F₁;
(d) hence if Y is not completable, every agent holds at least one good and |J| > |F₁|.

*Proof.* (a) Lemma 4; Lemma 4 gives a strictly Pareto-better state, which has Φ at least as large (Lemma 1(a)), so it
would contradict maximality. (b) The bundle J threatens x by at most v_x(J ∩ R_x) ≤ v_x(Y_x); the agent itself holds J
and by (V2) no holding threatened it while it held nothing, so none threatens it now; one-good holdings threaten
nobody. (c) A bundle {y, h} of a free agent's good y and a leftover good h has threat at most max(v_i(y), v_i(h)), and
neither good is wanted (Lemma 1(b)); the receivers only gain. (d) From (b) and (c). ∎

**Proposition 6 (DE's ring argument, where it applies).** Let Y be valid with Corollary 5(a), and suppose:
(i) every agent's holding is a single good or a *robust* set (v(S) ≥ v(R ∖ S)); and
(ii) no big-top agent holding its top has two of b, c, d in J.
If some agent holds a single good and no agent of F₁ can finish by DE's single-owner rule, then trading along a ring
of want arrows and pair arrows (DE's definition of rings) with pairwise distinct leftover goods gives a valid state in which
every agent of the ring gains value. (If no agent holds a single good, Y is completable: by Corollary 5(b) nobody
holds nothing, so every holding is robust, and any agent can take all leftover goods, since a robust agent is never
threatened.)

*Proof.* DE's proof of its Improvement Lemma, with three changes. (1) A robust holder wants nothing and is never
threatened (every other bundle meets R in R ∖ S), so it is never a taker and never needs a pointer. (2) A *blocker* of
o ∈ F₁ for H ⊆ J is an agent x threatened by {y_o} ∪ (J ∖ H); it holds a single y_x, all its goods in that bundle are
worth less than y_x, and by Corollary 5(a) y_o is one of them. A minimal set N ∋ y_o of these goods with v(N) > v(y_x)
can be chosen with exactly one leftover good. Let D′ be x's goods in {y_o} ∪ (J ∖ H); v(D′) > v(y_x) and y_o ∈ D′.
For y_x = a, x a 4-good agent that is not big-top: if |D′| = 2, N = D′; if D′ = {b, c, d}, then y_o ≠ d (else
{b, c} ⊆ J would be worth more than a, against Corollary 5(a)), so N = {b, c} ∋ y_o. For y_x = a and x a 3-good agent,
N = D′ = {b, c}. For y_x = b (4-good), a is wanted, so N = D′ = {c, d}; a 3-good holder of b, and a holder of c or
d, is never threatened; and big-top
holders of a with two leftover goods are excluded by (ii). N is an upper set or the lower pair. (3) Hence, for
|U| ≤ |F₁| − 1, a blocker of o for H = U has a pair arrow into o whose leftover good avoids U, which is exactly what DE's choice of distinct leftover goods q_o needs.
The pointers σ, the cycle and the validity of the trade are then as in DE: frozen agents point to their first
wanter, which holds a single good (a robust holder wants nothing, the lower pair is not robust, and an agent holding
nothing could finish); agents of F₁ point to their chosen blockers, which hold single goods; so the walk from an
agent holding a single good stays among such agents and closes a cycle. Every new holding is a single good or a pair,
which threatens nobody by Lemma 1(c). ∎

Proposition 6 is not a step of a proof of TARGET₄: its trades create lower pairs and non-robust upper sets, so its
hypotheses are not preserved. It shows which features of k = 4 DE's argument does not handle (§5).

## 4. Evidence (EVIDENCE; exhaustive only where said)

"Fails" means: some maximum of the profile is not completable.

| what | profiles | fails | DE single-owner rule fails | log |
|---|---|---|---|---|
| every strict profile, every core with n = 2 (5 cores), both implementations | 252,288 (exhaustive) | 0 | 0 | `results/k4_de4/exhaustive_2.log`, `exhaustive_2_c.log` |
| every strict profile, every core with n = 3 (51 cores), `de4.c` | 439,582,464 (exhaustive) | 0 | not checked | `results/k4_de4/exhaustive_3.log` |
| every strict profile, every core with n = 4 and one 4-good agent (135 cores), `de4.c` | 8,398,080 (exhaustive) | 0 | not checked | `results/k4_de4/exhaustive_4_n4_1.log` |
| suite: every complete instance with n ≤ 6, m ≤ 15 (c4-H2, c4-H5, lmbt-HH3, lmbt-Hq3 skipped) | 155 | 0 | 1 (hall-cyc6) | `results/k4_de4/suite.log` |
| random strict profiles, every certified core with n = 3 (51 cores, 300 each) | 15,300 | 0 | 0 | `results/k4_de4/certs_3.log` |
| random strict profiles, every certified core with n = 4 (1,002 cores, 40 each) | 40,080 | 0 | 0 | `results/k4_de4/certs_4.log` |
| random strict profiles, every pure n = 5 core (4,674, 2 each) | 9,348 | 0 | 0 | `results/k4_de4/certs_5_pure.log` |
| random strict profiles, every n = 5 core with three or four 4-good agents (19,707, 1 each) | 19,707 | 0 | 0 | `results/k4_de4/certs_5_n4_34.log` |
| random R1-cores, n = 2..4, tied values, any number of private goods, junk goods | 20,000 | 0 | 0 | `results/k4_de4/r1ties.log` |

**The algorithm DE4-ALG** (`python3 k4/de4/check.py algo`, `results/k4_de4/algo_suite.log`,
`results/k4_de4/algo_random.log`): it finishes on all 155 suite instances with n ≤ 8, m ≤ 16 (73 chains, 26 rings) and
on 20 random strict profiles of each of the 1,053 cores with n = 3 or 4 (21,060 runs; 1,353 chains, 141 rings),
never needing a fallback. Proposition 6's hypotheses hold at 7 of the 26 ring steps on the suite and 114 of the 141
on the random runs.

**The lemmas of §3**, checked as stated (`python3 k4/de4/verify_lemmas.py`, `results/k4_de4/verify_lemmas.log`): on
every valid state of the suite instances with n ≤ 4, m ≤ 10 and of random profiles of every core with n ≤ 4, no
violation of Lemma 1(c), Lemma 2, Lemma 4 (with its three-good switch), Corollary 5(b), (c) or Proposition 6.

Two implementations: `k4/de4/de4lib.py` (Python, SAT for completions) and `k4/de4/de4.c` (C, brute-force completions)
agree on the number of valid states, of maxima and of failures on every compared profile (16 cores, n = 2 and 3;
`results/k4_de4/xcheck.log`). Both are by the same author; they share definitions, not code.

**Moves** (`python3 k4/de4/check.py moves`, `results/k4_de4/moves.log`; suite instances with n ≤ 5, m ≤ 12). Of the
582 valid states that DE's rule does not finish (256 of them are completable by a general completion), every one has
a better valid state: 581 a value-Pareto-better one,
one (gm4-B) only a level-monotone one, through a lateral move. Constructively: Lemma 4's chain finds one for 483, DE's
ring with the global choice of leftover goods for 96, the same ring assigned along the walk from some start for 1
(red-pm-offpath-hypothesis), a ring in which a blocker keeps part of its own holding for 1 (induct-g-r1), and none of
these for gm4-B.

## 5. The missing step

Conjecture DE4 needs: if a valid state satisfies Corollary 5 and is not completable, some trade raises Φ without
lowering any level (or raises values at equal Φ). DE's proof gets the trade from a count: with (NC), every free agent
has blockers with at least |F| distinct leftover goods, so distinct goods can be chosen for all free agents at once
and any cycle of pointers is a ring. At k = 4 that count fails, and every way it fails occurs on the suite:

- **(G1) Owners holding two or three goods.** Free agents holding a lower pair or an upper set can own the leftover
  goods but cannot take one more (their bundle would have three goods and could threaten), so they count in |F| but
  not among the receivers. In the stuck states of the suite (DE's rule does not finish, no chain applies), such an
  owner has a blocker arc using no leftover good in 41 cases and only arcs using one in 11 (`results/k4_de4/moves.log`).
  Three instances show what is then needed:
  - *gm4-B* (n = 4, m = 7): agents 0 and 1 hold lower pairs and compete for the one leftover good; no valid
    state is value-Pareto-better, and the improvement found lowers agent 0 from {c, d} to b (lateral) while agent 2
    goes from a to a rich pair;
  - *hall-cyc6* (n = 6, m = 15): every agent holds an upper pair, three goods are left over, no valid state is better
    (it is a maximum), no single owner can take the three goods, and giving them to **two** agents works
    ({4, 5, 12, 14} and {6, 7, 13}); this is why completions, not DE's single-owner rule, appear in the conjecture;
  - *induct-g-r1* (n = 2, m = 5): the two agents exchange their b's and keep their c's.
- **(G2) Big-top blockers.** A frozen big-top agent holding a, with one of b, c, d in an owner's holding and two in J,
  is protected by removing one leftover good, but its upgrade {b, c, d} uses two. In the same stuck states, 15 free
  agents holding one good have only arcs using two leftover goods, and every one of these is such a big-top blocker
  (e.g. c4x-n3m6-onefour-a); 20 have an arc using none (the blocker keeps part of its own holding) and 30 one.
- **(G3) Global choice.** On red-pm-offpath-hypothesis DE's greedy choice over all free agents uses the only leftover
  good for a free agent that no improving cycle visits; the walk must be chosen.

What a proof needs is a cycle lemma of Hall type: in the digraph in which each frozen agent points to its wanters (and
lower-pair holders whose b it holds) and each free agent to its blockers, labelled by the leftover goods they use,
non-completability (every distribution of J leaves a threatened agent) forces a cycle with pairwise disjoint labels.
Theorem Z (`k4/c4min.md` §3) is the case where every agent holds a pair and nobody is frozen, proved by an injectivity
argument (each agent is threatened by at most one owner) that fails once owners hold single goods.

**Relation to earlier spaces.** 𝒫 of `k4/c4x.md` allows every base of at most two goods and measures bases by
value levels; its Pareto-maxima, and the maxima of more than 40 potentials, are not all completable (from n = 2 or
3), and its completions are D2-shaped. DE4 differs in four ways, each needed on the suite (`attempts/k4-de4-variants.md`):
the holdings are only singles, minimal upper sets and the lower pair (so the dead end of `attempts/k4-ls-dead-end.md`,
which uses {b, d} worth less than a, is not a state); levels are ranks, with the lower pair at b's level; upper sets
of three goods are allowed, with (V2); completions may give leftover goods to several agents.

## 7. The ring step: what is proved, and the one remaining case

This section replaces the abstract cycle lemma of §5 by a concrete construction and proves all of it but one case.
Throughout, Y is a valid state of a strict profile such that **(H)**: Lemma 4 and Lemma 4′ give no improvement (so
Corollary 5(a) holds and no free agent can upgrade inside its holding plus the leftover goods), every agent holds a
good, and Y is not completable. Every maximum that is not completable satisfies (H).

**Lemma 7 (danger sets).** For an agent i, a *danger set* is a minimal set D of goods of R_i, outside Y_i and not
wanted by i, with v_i(D) > v_i(Y_i).
(a) A bundle B with no good of Y_i and no good wanted by i threatens i (θ_i(B) > v_i(Y_i)) if and only if B strictly
contains a danger set of i.
(b) Every danger set of i is an allowed holding of i.
(c) Under (H), no danger set of any agent lies inside J.

*Proof.* (a) If B ⊋ D, remove a good h ∈ B ∖ D: v_i(B ∖ h) ≥ v_i(D) > v_i(Y_i). Conversely, if v_i(B ∖ h) > v_i(Y_i),
a minimal subset of the goods of R_i in B ∖ h worth more than Y_i is a danger set inside B ∖ h ⊊ B. (b) As in Lemma 4(i):
the goods outside Y_i that i does not want are, for Y_i = {a}, goods worth less than a, and a minimal set of them
worth more than a is an upper set; for Y_i = {b} of a 4-good agent they are c and d, and {c, d} is an upper set or the
lower pair; for Y_i an upper pair they are at most two goods, each worth at most v(a), so a danger set is a pair worth
more than a, an upper set; in every other case there is no danger set. (c) A danger set D ⊆ J would give
v_i(J ∩ R_i) ≥ v_i(D) > v_i(Y_i), against Corollary 5(a). ∎

Lemma 7 is checked by brute force: `python3 k4/de4/cycle.py danger` (every bundle of up to four goods, every agent,
every valid state of the suite instances with n ≤ 4, m ≤ 9; `results/k4_de4/cycle_danger.log`).

**Arcs.** An *arc into* a free agent o is a pair (x, D) with x ≠ o, D a danger set of x, D ⊆ Y_o ∪ J and D ∩ Y_o ≠ ∅.
Its *label* is D ∩ J. It is *full* if Y_o ⊆ D, *partial* otherwise. By Lemma 7, under (H): for T ⊆ J, the bundle
Y_o ∪ T threatens x if and only if it strictly contains D for an arc (x, D) into o with label ⊆ T. Arcs into a free
agent holding one good are full. F₁ is the set of free agents holding one good.

**Lemma 8 (self-absorption).** Under (H), let o_1, …, o_f be the agents of F₁ in index order, and choose for o_t an arc
(x_t, D_t) whose label L_t avoids L_1 ∪ … ∪ L_(t−1), with the fewest labels and then the fewest goods. Such an arc
exists for every t, the labels are pairwise disjoint, and no bundle D_t strictly contains a danger set of anyone.

*Proof.* The second claim: if D_t ⊋ D′ for a danger set D′ of some agent i, then D′ meets Y_(o_t) (else D′ ⊆ J, against
Lemma 7(c)), so (i, D′) is an arc into o_t whose label is a proper subset of L_t, contradicting the choice. For the
first claim, let U = L_1 ∪ … ∪ L_(t−1) and complete Y by giving o_s the goods L_s (s < t) and o_t all of J ∖ U. The
bundle of o_s is D_s, which threatens nobody (second claim); the other holdings threaten nobody by (V2), and nobody's
value dropped. As Y is not completable, the bundle Y_(o_t) ∪ (J ∖ U) threatens someone, so it strictly contains D for
an arc (x, D) into o_t, whose label lies in J ∖ U. ∎

The same argument gives: **(8′)** if the arcs already chosen for free agents holding two or more goods are full, a
further free agent u has an arc avoiding all labels chosen so far. Each such agent absorbs its own label (its bundle
is then exactly its arc's D), and u takes the rest. The argument breaks only for *partial* arcs, whose owner cannot
absorb the label: its bundle would strictly contain D.

**Theorem 9 (DE's walk).** Under (H), define σ:
- σ(o_t) = x_t for o_t ∈ F₁ (Lemma 8);
- σ(j) = the first agent that wants the good of j, for a frozen agent j;
- for a free agent u holding two or more goods, σ(u) = x for an arc (x, D) into u whose label avoids all labels
  chosen so far, with the fewest labels and then the fewest goods. This is chosen when the walk reaches u.

Start at the first agent holding one good (the first free agent if there is none) and follow σ. If the walk closes a
cycle, then trading along it (each agent on the cycle takes from its predecessor the wanted good, or its danger set D)
gives a valid state in which every agent on the cycle has strictly more value. This is a strict Pareto improvement, so
no level drops.

*Proof.* Each frozen agent has a wanter, and wanters hold a good (by (H) nobody holds nothing). So σ is defined along
the walk except where stated. On the cycle every agent takes from exactly one agent. The labels are pairwise disjoint
by construction, so the new holdings are disjoint; the goods of a giver that its taker does not take become leftover.
Every taker strictly gains (a wanted good, or a danger set, worth more than its holding), and every new holding is
allowed (Lemma 7(b)). Wanted sets only shrink, so a good wanted afterwards was wanted before. It was then a one-good
holding of a frozen agent j; if j is on the cycle, the good is now the whole holding of σ(j), which wants it. This is
(V1). For (V2): holdings that did not change threaten nobody new; a new pair threatens nobody (Lemma 1(c)). Let a new
triple D (a big-top blocker's {b, c, d}, taken through an arc into a giver v) threaten an agent i. By Lemma 7(a), D
strictly contains a danger set D′ of i for its new holding.
- If i ≠ v: D′ is disjoint from Y_i and from the goods i wants, and it is worth more than i's new holding, hence than
  Y_i. So it contains a danger set D″ of i for Y_i with D″ ⊊ D. Then (i, D″) is an arc into v (Lemma 7(c)) with fewer
  labels or fewer goods, contradicting the choice.
- If i = v: D′ ⊆ Y_v ∪ J is an allowed holding of v (Lemma 7(b)), a pair (D′ ⊊ D), worth more than v's new holding,
  hence than Y_v. As v is free, Lemma 4′ would apply, against (H). ∎

**Corollary 10.** Under (H), if the walk of Theorem 9 never has to choose an arc for a free agent holding two or more
goods after a partial labelled arc has been chosen, it closes a cycle and gives a strict Pareto improvement. In
particular, if no free agent holds two or more goods, a non-completable state satisfying (H) has an improvement. This
is the four-good analogue of DE's Improvement Lemma for such states, including big-top blockers, whose arcs use two
leftover goods.

*Proof.* By Lemma 8 and (8′), every choice the walk makes exists, and the walk is finite, so it closes a cycle;
Theorem 9 applies. ∎

**Conjecture 11 (the remaining case).** Under (H), if the walk stops at a free agent holding two or more goods (no arc
avoiding the labels chosen so far), then one of these moves gives a better state (in the order of §1):
- **(P) partial path:** a free agent u holding two or more goods and a partial arc (x, D) into u. x takes D; u keeps its
  most valuable allowed subset of Y_u ∖ D; if x is frozen, x's good passes down the first-wanter walk (Lemma 4(ii)),
  and the old holding at its end becomes leftover. This may lower u's level, so it is an improvement only when the
  level sum rises;
- **(K) keep-own exchange:** two free agents re-divide their holdings and leftover goods, each keeping part of its own,
  both strictly gaining.

Moves P and K are each bounded in the number of agents they touch, apart from the wanter walk in P. The
evidence is in `results/k4_de4/cycle_*.log`, produced by `python3 k4/de4/cycle.py`. On the suite, of the 326
non-completable valid states:
- 230 are improved by Lemma 4 or 4′;
- 94 by the walk;
- the walk stops in 2 states, gm4-B (resolved by P) and induct-g-r1 (resolved by K).

There is no violation of Lemma 8 or Theorem 9. The random runs are summarized in the log.

**What remains for a proof of DE4.** Conjecture 11. With it, every maximum is completable: a non-completable maximum
satisfies (H), and Corollary 10, P or K would give a better state. Conjecture 11 is the precise form of gaps G1 and G3
of §5. Gap G2 (big-top blockers using two leftover goods) is closed by Lemma 8.

## 6. Reproduce

```
python3 k4/de4/check.py suite                                   # ~3 min
python3 k4/de4/check.py exhaustive k4_certs_2.json.gz 2         # every strict profile, n = 2, ~1 min on 4 CPUs
python3 k4/de4/run_exhaustive.py k4_certs_3.json.gz             # every strict profile, n = 3, C, ~1 h on 4 CPUs
python3 k4/de4/run_exhaustive.py k4_certs_4_n4_1.json.gz        # every strict profile, n = 4 with one 4-good agent
python3 k4/de4/check.py certs k4_certs_3.json.gz 300            # likewise k4_certs_4_*.json.gz 40, k4_certs_5_*.json.gz
python3 k4/de4/check.py r1ties 100                              # 20,000 random R1-cores with ties
python3 k4/de4/check.py moves                                   # §4 "Moves", ~10 min
python3 k4/de4/check.py xcheck                                  # Python against C
python3 k4/de4/check.py algo                                    # the algorithm DE4-ALG on the suite
python3 k4/de4/verify_lemmas.py                                 # the lemmas of §3 by brute force
python3 k4/de4/variants.py                                      # the refuted variants
bash k4/de4/run_all.sh                                          # every log of §4 except the two C exhaustive runs
```
Needs python-sat (`requirements.txt`) and gcc.
