# DE4: Draft and Exchange for four relevant goods

Workstream `proof/k4-de4` (branch `claude/kind-lamport-y8fdme`), ledger rows K4.DE4.*, open item 29. The aim was a
proof of TARGET₄ with the architecture of DE (`paper/k3-simple` in evanlin23/efx0-three-goods-proof): a state space of
holdings, a validity invariant, a finishing rule and an improvement step measured by a potential. **This file does
not contain a proof of TARGET₄, and its central conjecture is false.** It contains a state space and a potential for
which every maximum was completable on the data first searched, written proofs of the parts of DE that carry over,
and the counterexample that ends the approach in this form.

**Status.**
- *Conjecture DE4* (§2) **is refuted** (`attempts/k4-de4.md`, ledger K4.DE4; replay `python3 k4/de4/refute_de4.py`;
  machine-checked in Lean, `EFX.DE4.Refute.not_conjDE4`).
  The exhaustive run over every strict profile of every n = 4 core with two 4-good agents (922,669,056 profiles,
  `results/k4_de4/exhaustive_4_n4_2.log`) found 8 profiles, all of one core (m = 7), with a maximum that has no EFX₀
  completion. That maximum satisfies (H) and no valid state is better, so the improvement form and Conjecture 11″
  (§7.7) fail too, and so do the hypotheses of the Lean frame. Its mechanism is that of GM₄'s counterexample: two
  frozen blockers need the one leftover good, which is the b of both hungry agents. Every profile of that class has
  *some* completable maximum. A different state space, DE4ᵛ³ (the lower pair only while b is held, §8), removes every
  known failure but is refuted as well (§9, instance R4: every agent holds an upper set). Scale-invariant tie-breaks
  after the level sum do not repair DE4 either: they remove these 8
  failures but create 1,620 elsewhere in the same class, or keep them (`attempts/k4-de4.md`, ledger K4.DE4.TB). The
  rest of this status list describes the work before the refutation; the proved lemmas (§3, §7) are about valid
  states and stand.
- *Conjecture DE4* as stated: every maximum of the level sum (then value-Pareto) over the valid DE4 states of a strict
  R1-core profile has an EFX₀ completion. With the peeling lemma and the tie reduction it would imply TARGET₄ (§2,
  Lemma 3).
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
  owners restricted to agents holding at most one good; the lower pair only for big-top agents; DE's greedy over all
  free agents; Conjectures 11 and 11′ of §7.
- *Missing* (§5, made precise in §7): the improvement step. §7 proves it (Lemmas 7, 8, 12, 14, Theorem 9, Corollary
  10) except in one case: DE's walk reaches a free agent holding two or more goods after a *partial* labelled arc was
  chosen. Lemma 13 shows that this is a Hall-type obstruction among the leftover goods. Every instance found has a
  *dead* leftover good, i.e. one that no free agent can take alone. The improvement then exists, but in some
  instances only through a *lateral* move: some agent's value drops while its level stays. So DE's value-Pareto
  argument cannot close the gap (§7.7; Conjectures 11 and 11′ are refuted, Conjecture 11″ is open).
- *Lean* (`lean/EFX/DE4.lean`, `DE4Moves.lean`, `DE4Upgrade.lean`, `DE4Ring.lean`, `DE4Cor10.lean`, row
  K4.DE4.LEAN). Machine-checked:
  - the definitions of §1, and the existence of maxima;
  - Lemmas 1(a), 2, 4 (with its chains, want-rings and three-good switch), 4′, Corollary 5(b), and Lemma 3;
  - hence "Conjecture 11″ (under (H), a better valid state exists) ⟹ improvement form ⟹ DE4 ⟹ TARGET₄";
  - from §7: Lemma 7(a), Lemma 7(b) in general form, Theorem 9's trade along a cycle with labels, Lemma 8, and
    Corollary 10 when every free agent holds one good. So Conjecture 11″ needs proving only for the (H) states in
    which some free agent holds two or more goods (`EFX.DE4.ConjDE4H₂`).

  The hypothesis `EFX.DE4.ConjDE4H₂` is the open step; nothing else is assumed.

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

**Conjecture DE4 (refuted).** For every strict profile of every R1-core (k ≤ 4), every maximum is completable. False at
n = 4, m = 7 (`attempts/k4-de4.md`): agents with relevant goods {0, 2, 4, 6}, {1, 3, 5, 6}, {2, 3, 6}, {4, 5, 6} and
values {0:3, 2:8, 4:2, 6:4}, {1:3, 3:2, 5:8, 6:4}, {2:4, 3:2, 6:3}, {4:2, 5:4, 6:3}; the maximum ({0, 4}, {1, 3},
{2}, {5}) with leftover {6} has no EFX₀ completion and no valid state is better than it.

**Improvement form** (what an algorithm would use). Every valid state that is not completable has a better valid
state, in the order of §1. A maximum is exactly a valid state that no valid state is better than, so on each
profile the improvement form is *equivalent* to Conjecture DE4. Its strong form, where moreover no agent's level is
lower, is false (V11 of `attempts/k4-de4-variants.md`, §7.7): some improvements must lower a frozen agent's level.

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
| every strict profile, every core with n = 4 and two 4-good agents (309 cores), `de4.c` | 922,669,056 (exhaustive) | **8** (all in core 131, m = 7; the counterexample of `attempts/k4-de4.md`) | not checked; every profile has a completable maximum | `results/k4_de4/exhaustive_4_n4_2.log` |
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

**Conjecture 11, first form (refuted).** Under (H), if the walk stops at a free agent holding two or more goods (no arc
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

**It is false as stated** (V8 of `attempts/k4-de4-variants.md`). In a run of 50,000 random profiles, one stopped walk
(n = 4, m = 8) has neither P nor K, and no improvement changing at most two agents. Its improvement is a 3-cycle in
which one blocker keeps part of its own holding. This leads to the refinement below.

### 7.6 Which arcs carry labels

**Lemma 12.** Under (H), let (x, D) be an arc into a free agent u with a nonempty label, and x free. Then either x is
a big-top 4-good agent holding its b, or some good g ∈ D ∩ Y_u and some good q ∈ Y_x make {g, q} an upper set of x
worth more than Y_x: a *keep-own arc*, in which x takes g from u, keeps q, and uses no leftover good.

*Proof.* Cases by the holding of x (free, so its goods are not wanted); a holding without a danger set has no arc.
- Y_x = {a}: a good h ∈ J ∩ R_x would give the upper set {a, h} ⊆ Y_x ∪ J, worth more than Y_x, so Lemma 4′ would
  apply. Hence J ∩ R_x = ∅, and every arc of x has an empty label.
- Y_x = {b}, 4-good, D = {c, d}: one of c, d is in J and the other in Y_u (Lemma 7(c)). If x is not big-top, then
  {b, c} is an upper set. If c ∈ J, it lies in Y_x ∪ J and Lemma 4′ applies; so c ∈ Y_u, and {c, b} is a keep-own
  arc.
- Y_x = {a, d} with v(b) + v(c) > v(a) + v(d), D = {b, c}: if b or c were in J, {a, b} or {a, c} ⊆ Y_x ∪ J would be
  an upper set worth more than Y_x (Lemma 4′). So D ⊆ Y_u and the label is empty.
- Y_x a rich pair P = {p, p′} ⊆ {b, c, d} whose complement {a, s} is worth more, D = {a, s}: if a ∈ J, then
  {a, p} ⊆ Y_x ∪ J is an upper set worth more than P (as v(a) > v(p′)), and Lemma 4′ applies. So a ∈ Y_u, and
  {a, p} is a keep-own arc.
- 3-good agents: every pair holding is robust (no danger set), and Y_x = {a} is the first case. ∎

So, under (H), the only arcs that must use leftover goods are arcs into free agents holding one good, which are
self-absorbed by Lemma 8, and arcs whose blocker is frozen or a free big-top holder of its b. The walk can stop only
on a conflict between two *partial* arcs of the second kind (Lemma 8′).

**Conjecture 11′ (the remaining case).** Under (H), if the walk of Theorem 9 stops, then a better state is given by
one of these:
- the *refined walk* (`walk2` in `k4/de4/cycle.py`). Free blockers may use the keep-own arcs of Lemma 12; a kept good
  is never taken later and a given good never kept; at each free agent holding two or more goods, an arc whose blocker
  is already on the walk, with a label disjoint from the labels on the cycle it closes, is preferred;
- move P.

Evidence (`results/k4_de4/cycle_suite.log`, `results/k4_de4/cycle_walk_n34.log`): on the suite, the walk stops in 2
of 326 non-completable states, resolved by P (gm4-B) and by the refined walk (induct-g-r1). On 30,000 random profiles
of every certified core with n = 3, 4, there are 18,720 non-completable valid states:
- 12,902 are improved by Lemma 4 or 4′;
- 5,814 by the walk;
- in the remaining 4 the walk stops, and all 4 are resolved by the refined walk.

No violation of Lemma 8 or Theorem 9 occurs. The validity of the refined walk's trades is checked, not yet proved:
keep-own arcs produce upper pairs, so the argument of Theorem 9 should carry over.

**Correction to the remark after Lemma 12.** For a free holder x of its b that is not big-top, the keep-own arc keeps
x's whole holding ({b} becomes {b, c}). Then no agent can take anything from x, so the arc cannot lie on a cycle; it
can only end a path. So free holders of their b (big-top or not) are, with frozen agents, the blockers whose partial
labelled arcs can conflict.

### 7.7 Conjecture 11′ is false; what survives

**Two counterexamples** (V9 of `attempts/k4-de4-variants.md`, replayed by `k4/de4/variants.py`).

*First* (n = 4, m = 7, three 4-good agents). Agent 0 values goods 0, 2, 5, 6 at 2, 3, 8, 4; agent 1 values 0, 3, 4, 6
at 5, 4, 2, 8; agent 2 values 1, 2, 4, 6 at 4, 5, 2, 8; agent 3 values 1, 3, 5 at 2, 3, 4. Take
Y = [{0, 2}, {3, 4}, {6}, {5}], with J = {1}:
- agents 0 and 1 hold their lower pairs and want their tops 5 and 6, which the frozen agents 3 and 2 hold;
- agent 2's danger set {1, 2} gives a partial arc into agent 0, and agent 3's danger set {1, 3} one into agent 1;
- both arcs have the label {1}.

So the one leftover good cannot be taken by either free agent, alone or with anything else. Y is valid, (H) holds,
the walk stops, and neither the refined walk nor P improves. Worse, **no valid state is value-Pareto-better than Y**.
Every better state lowers some value. Five of them lower no level, e.g. [{5}, {0}, {6}, {1, 3}]:
- agent 0 takes its top from agent 3;
- agent 3 takes {1, 3}: the leftover good and agent 1's c;
- agent 1 takes its b, good 0, which agent 0 has released. Moving from the lower pair to b keeps its level (lateral).

The level sum goes from 14 to 16. Every maximum of this profile is completable.

*Second* (n = 3, m = 8, nobody frozen, every agent holds a pair). The refined walk and P fail again, because the
greedy choices take the wrong arcs. A rotation in which each agent keeps one good and takes one good from the next is
value-Pareto-better. It has the shape of Theorem Z's rotations (`k4/c4min.md` §3).

**Consequence.** The improvement step of DE4 is not a value-Pareto lemma like DE's Improvement Lemma: it must allow
lateral moves. The order of §1 already allows them, since it compares level sums first. The improvement form of §2
survives:

**Conjecture 11″ (refuted with DE4, `attempts/k4-de4.md`)** (row K4.DE4.C11B; in Lean `EFX.DE4.ConjDE4H`). Under
(H), there is a better valid state in the
order of §1: the level sum is higher, or it is equal and the values Pareto-improve. Every non-completable valid state
either satisfies (H) or is improved by Lemma 4 or 4′ (or some agent holds nothing, and then it is completable:
Corollary 5(b)). So Conjecture 11″ is the improvement form of §2, hence equivalent to DE4. In Lean,
`EFX.DE4.target4_of_conjDE4H` derives TARGET₄ from it, and with Corollary 10 (machine-checked when every free agent
holds one good, `EFX.DE4.cor10`) `EFX.DE4.target4_of_conjDE4H₂` derives TARGET₄ from its case where some free agent
holds two or more goods. What the walk and §7 add is a proof strategy: DE4 holds at
every (H) state where the walk closes, and the open case is the stopped walk.

*Its strong form is false* (V11). The strong form asks that no agent's level be lower. A strict profile with n = 6,
m = 9 refutes it; it was built by hand so that the two hungry agents share no goods:
- two lower-pair holders with disjoint goods;
- frozen blockers holding their tops, both valuing the one leftover good;
- each lower-pair holder's b held by a frozen agent.

The state satisfies (H), and no better state keeps every level. In each better state a frozen blocker gives its good
to a hungry agent and drops from its b to its c, while the other blocker takes its lower pair with the dead good
(level sum 20 → 21). Such *downgrades* of frozen agents are needed in general; repaired "downgrade swaps" appear also
in `k4/hall.md`.

**Why the walk stops.** Call a free agent z an *absorber* of a leftover good h if Y_z ∪ {h} threatens nobody (with
the values of Y), i.e. z is not *closed* (Y_z is not a danger set of another agent) and no arc into z has label {h}
and is partial. Every agent of F₁ absorbs every leftover good, since its arcs are full with nonempty labels.

**Lemma 13.** Under (H), let the walk of Theorem 9 stop at a free agent u (u holds two or more goods, by Lemma 8).
Let U_P be the set of goods in the labels of the partial arcs chosen so far. Then the goods of U_P cannot be given,
injectively, to absorbers outside {u}, F₁ and the agents whose chosen arc is full. So, by Hall's theorem, some
nonempty S ⊆ U_P has fewer than |S| such absorbers. In particular, if U_P = {h}, then h has no absorber outside these
agents.

*Proof.* Suppose such an assignment exists. Complete Y as follows:
- each agent of F₁ takes its label (Lemma 8), and each agent whose chosen arc is full takes its label ((8′));
- each good of U_P goes to its absorber;
- u takes the rest of J.

Which bundles can threaten?
- The bundle of an agent that took its label is the danger set of its arc, which threatens nobody (Lemma 8, second
  claim, and (8′)).
- An absorber's bundle threatens nobody, by definition.
- Unchanged holdings threaten nobody, by (V2).

Values only rise, so a threat in the completion is a threat for the old values. As Y is not completable, u's bundle
Y_u ∪ (J ∖ U) threatens someone, where U is the set of all labels chosen so far. By Lemma 7 this gives an arc into u
whose label lies in J ∖ U, so the walk does not stop at u. ∎

A leftover good is *dead* if it has no absorber at all. Then F₁ = ∅, and every free agent is closed or has a partial
arc with label {h}. A dead good is the smallest obstruction of Lemma 13, and the only one found. The data split
Conjecture 11″ into two statements:
- **(D)** if the walk stops, some leftover good is dead;
- **(E)** if some leftover good is dead (and (H) holds), an improvement as in Conjecture 11″ exists.

**Label-free cycles.** Write G₀ for the digraph of the *label-free arcs*:
- frozen j → every agent that wants j's good;
- closed u → every agent whose danger set is Y_u.

Call a free agent that is not closed *hungry*: it is a sink of G₀.

**Lemma 14.** Under (H), trading along a cycle of G₀ gives a valid state in which every agent on the cycle has strictly
more value. In the trade, each agent takes its predecessor's good (want arc) or whole holding (closed arc).

*Proof.* As Theorem 9, with no labels. Every frozen agent on the cycle hands its good, alone, to an agent that wants
it, so (V1) holds. A new triple D = Y_u (a closed arc into a big-top x) can threaten an agent i only if D strictly
contains a danger set D′ of i for its new holding. Then:
- if i ≠ u, then D′ contains a danger set of i for Y_i (no good of a triple is wanted, by (V1)), so Y_u threatened i
  in Y, against (V2);
- if i = u, then v_u(D′) > v_u(Z_u) > v_u(Y_u) > v_u(D′), since D′ ⊊ Y_u. ∎

A hungry agent u with an arc (x, D) of label {h} whose blocker x reaches u in G₀ gives a cycle with one label: x takes
D, and the agents of the G₀ path from x to u pass their goods along. When D is a pair, Theorem 9's argument shows that
this trade is valid and a strict Pareto improvement.

**Hard dead-good states.** Call a state with a dead good *hard* if G₀ has no cycle and no such one-label cycle exists.
In a hard state, the improvement found is move PR or the refined walk (§7.6), and most often move PR:
- take a hungry u, an arc (x, D) into u with label {h}, and a G₀ path from x to a sink r ≠ u;
- x takes D, and each agent of the path takes its predecessor's good (want arc) or holding (closed arc);
- r releases its holding;
- u takes its best allowed holding among the goods left over: what remains of its own holding, the leftover goods
  but h, and r's released goods.

In the instances inspected, u holds a lower pair and takes its b from r's released holding (a lateral move), or an
upper pair made of its b and the good it kept. That case is a theorem:

**Lemma 15 (the lateral path).** Let Y be valid (no part of (H) is needed). Let:
- u be a free agent holding its lower pair, and (x, D) an arc into u with x frozen, D ∩ J = {h} and D ∩ Y_u = {g};
  let k_u be the other good of Y_u;
- x = p_0 → p_1 → ⋯ → p_k = r (k ≥ 1) be a simple path of label-free arcs that avoids u and ends at a free agent r;
- u's b lie in Y_r or in J ∖ {h}.

Trade as follows:
- x takes D;
- each p_t takes p_(t−1)'s good (want arc) or holding (closed arc);
- r's old holding is released;
- u takes N_u = {b_u, k_u} if this is an upper set of u, else {b_u}.

Then the new state Z is valid, no agent's level is lower, and the level sum is higher.

*Proof.* The holdings are disjoint: g and h go to x, b_u comes from r's released holding or from J ∖ {h}, and the
path passes holdings forward. They are allowed: D is a danger set (Lemma 7(b)), and so are the closed holdings taken
along the path. Every agent other than u gains value, so its level does not drop (Lemma 1(a)). The agent p_1 takes x's
wanted good alone, so its level rises: a single good worth more than a holding has a higher level. u keeps level 3
(the good b) or reaches 5 (an upper pair).

(V1). Take an agent i ≠ u and a good q that i wants in Z.
- Since v_i(Z_i) ≥ v_i(Y_i), i wanted q in Y, so q was the single good of a frozen agent j.
- If j is off the trade, q is still j's single good.
- Otherwise j is one of p_0, …, p_(k−1): it is frozen, while r is free and u is free. A frozen agent's label-free arc
  is a want arc, so q went alone to the next agent.

If N_u = {b_u}, u wants only its top a_u, since c_u, d_u < b_u. u wanted a_u in Y as well (a_u > c_u + d_u), so the
same argument applies. If N_u is an upper set, u wants nothing. Released goods are wanted by nobody: they were goods
of free agents, and only u's wanted set grew.

(V2). Holdings of one good threaten nobody, and pairs threaten nobody once (V1) holds (Lemma 1(c)). D is a pair. A
triple T of Z is either unchanged or the closed holding Y_o of an agent o on the path, now held by o's blocker:
- for i ≠ u, θ_i(T) ≤ v_i(Y_i) ≤ v_i(Z_i) by (V2) in Y; for i = o, o's new holding is worth more than Y_o;
- for i = u, T contains none of u's goods: a_u is a single holding, c_u and d_u were u's, and b_u was in Y_r or J.
  So θ_u(T) = 0. ∎

`k4/de4/lemma15.py` checks Lemma 15 by brute force on every valid state (§7.8). Lemma 15 resolves a hard dead-good
state whenever some hungry lower-pair holder's b is leftover or held by the end of a path from one of its frozen
blockers. That this always happens, or something replaces it, is the open part of (E).

**Evidence** (`python3 k4/de4/dead.py`, logs `results/k4_de4/dead_*.log`; EVIDENCE): see §7.8.

**What remains for a proof of DE4.** Conjecture 11″, e.g. through (D) and (E). For (E) the open case is the hard
one: show that some move PR (Lemma 15 is the lower-pair case with b available) or a refined-walk cycle is valid and
lowers no level, or find the improvement otherwise. Gap G2 is closed by
Lemma 8; gap G1 by Lemma 12 for free blockers holding their top, an {a, d} pair or a rich pair; label-free cycles by
Lemma 14.



### 7.8 Evidence for (D) and (E)

`k4/de4/dead.py` (EVIDENCE; seeds in the logs) checks two kinds of states.

At every (H) state where the walk stops, it checks:
- whether some leftover good is dead (D), and whether F₁ is empty;
- whether a better state that lowers no level exists (Conjecture 11″, brute force over all valid states);
- which construction finds one: the refined walk, Lemma 14's label-free cycle, the one-label cycle, or move PR.

At every (H) state with a dead good (whether or not the walk stops), it checks:
- whether a label-free cycle, a one-label cycle, move PR or the refined walk gives such an improvement.

Each cycle's trade is built and checked (valid, strict Pareto improvement). `k4/de4/lemma15.py` checks Lemma 15 as
stated on every valid state.

| run | profiles | found | result | log |
|---|---|---|---|---|
| stopped walks, n = 4 cores with two or three 4-good agents | 160,000 | 6 (H) states with a stopped walk | all: dead good, F₁ = ∅, hard; move PR resolves all 6 (the refined walk 5) | `dead_stuck_n4.log` |
| stopped walks, random R1-cores (n = 3..5, m ≤ 11) | 100,000 | 7 | all: dead good, F₁ = ∅; 5 hard (PR resolves 4, the refined walk the fifth) and 2 one-label cycles | `dead_stuck_rand.log` |
| stopped walks, n = 5 cores with three or four 4-good agents | 2,400 | 0 | | `dead_stuck_n5.log` |
| stopped walks, the 17 hypergraphs of the stopped walks found by the scratch searches | 40,000 | 60 | all: dead good, F₁ = ∅; 44 hard, all resolved by PR (29 also by the refined walk); 16 one-label cycles | `dead_stuck_stuckhyper.log` |
| dead goods, the hypergraph of V9's first instance | 20,000 | 806 (H) states with a dead good | 638 label-free cycles, 150 one-label cycles, 18 hard (all PR; 12 also the refined walk) | `dead_hard_v9.log` |
| dead goods, n = 4 cores with two or three 4-good agents | 40,000 | 5,826 | 5,728 label-free cycles, 98 one-label cycles, no hard state | `dead_hard_n4.log` |
| dead goods, the 17 hypergraphs | 40,000 | 2,556 | 1,815 label-free cycles, 707 one-label cycles, 34 hard (33 PR, 1 only the refined walk) | `dead_hard_stuckhyper.log` |
| hard dead-good states: does Lemma 15 apply, and the fewest agents an improvement lowering no level changes (the same seeds as the two runs above) | 20,000 + 40,000 | 18 + 34 hard states | Lemma 15 applies in 14 of the 52; the fewest agents changed is 2 in 29 states, 3 in 22, 4 in 1 | `dead_minimal_v9.log`, `dead_minimal_stuckhyper.log` |
| Lemma 15 as stated, every valid state: suite (n ≤ 5, m ≤ 12), V9's hypergraph, n = 4 cores, random R1-cores | 3,241 + 679,867 + 337,257 + 910,225 states | 9 + 963 + 215 + 478 instances | the conclusion holds in all 1,665 | `lemma15_*.log` |

All logs are in `results/k4_de4/`. In total, 73 stopped walks satisfy (H), and every one has a dead good, F₁ = ∅ and
a better state that lowers no level. Every cycle trade built is valid and a strict Pareto improvement. Every hard
dead-good state is resolved by move PR or the refined walk. A dead good does not by itself make a state
non-completable: 499 states with a dead good (the "completable" lines) are completable, because the receivers'
values rise. Neither (D) beyond a dead good (a Hall obstruction of size two or more) nor a hard state that both PR
and the refined walk miss has been seen.

**The open case looks local (in small instances only).** In the hard states found, Lemma 15 covers the frozen blockers of lower-pair holders
whose b is available (14 of 52). The rest have a free blocker: a free agent holding a rich pair {b, c} whose danger
set is its top (held by the hungry agent) with the dead good. In every hard state some improvement changes at most
four agents. In a scratch classification of the 52 states (not a committed artifact):
- the 2-agent improvements re-divide the holdings of the two hungry agents, or of a hungry agent and a frozen one;
- the 3-agent ones add one closed or frozen agent;
- every hard state has exactly two hungry agents.

These instances are small (n ≤ 5, with heavily shared goods). In V11 the two hungry agents share no goods, and the
improvements change at least three agents, including a frozen agent that loses a level. So the locality is an effect
of the size. The improvement step has to use downgrades of frozen agents.

## 8. A different state space: DE4 with the lower pair only while b is held

After the refutation, state spaces of the same kind were screened (`attempts/k4-de4-ss.md`, ledger K4.DE4.SS). One
change removes every known failure:

**(V3)** an agent may hold its lower pair {c, d} only while its b is held by some agent.

A lower pair is then a consolation for an agent whose b is taken. In the counterexample of `attempts/k4-de4.md` the
failing maximum is not (V3)-valid: the leftover good is the b of both lower-pair holders. With (V3), a holder of its
lower pair values no leftover good at all (it holds c and d, its a is held alone by (V1), its b is held by (V3)).

**Conjecture DE4ᵛ³ (refuted, §9: instance R4, n = 4, m = 9)** (row K4.DE4V3). For every strict profile of every R1-core with k ≤ 4, every maximum of the
level sum, then value-Pareto, over the states valid for (V1), (V2) and (V3), is completable. The draft is (V3)-valid
(single goods only), so maxima exist, and as in Lemma 3 the conjecture implies TARGET₄. Machine-checked, with the
conjecture as a hypothesis: `EFX.DE4.target4_of_conjDE4V3` (`lean/EFX/DE4V3.lean`). The variant that also allows
{c, d} with v(c) + v(d) < v(b) at level 2.5 survives the same tests.

**Evidence** (EVIDENCE; `k4/de4/de4v.c`, run by `k4/de4/run_variants.py`, which checks DE4, DE4ᵛ³ and the variant
at once; `k4/de4/ss_screen.py` and `k4/de4/ss_sample.py` in Python):

| what | profiles | DE4 fails | DE4ᵛ³ fails | log |
|---|---|---|---|---|
| the screen of 168 instances (all known counterexamples) | 168 | 2 | 0 | `results/k4_de4/ss_screen.log` |
| every strict profile, every core with n = 2 | 252,288 | 0 | 0 | `results/k4_de4/variants_2.log` |
| every strict profile, every core with n = 4 and one 4-good agent | 8,398,080 | 0 | 0 | `results/k4_de4/variants_4_n4_1.log` |
| every strict profile of the 16 stuck hypergraphs (n = 3, 4; where the tie-breaks fail at n = 3) | 911,720,448 | 16 | 0 | `results/k4_de4/variants_stuckhyper.log` |
| suite instances with n ≤ 6, m ≤ 15 outside the screen; random profiles of n = 5 cores with one or two 4-good agents | 7 + 2,000 | 0 | 0 | `results/k4_de4/ss_sample.log` |

Still to run: every strict profile of every n = 4 core with two 4-good agents (the class of the DE4 counterexample)
and with n = 3. One implementation for the exhaustive runs (`de4v.c`); it agrees with the Python screen on cores 131
and 127.

**What a proof needs.** The improvement form changes: every non-completable (V3)-valid state needs a better
(V3)-valid state. The lemmas of §3 and §7 are about (V1)–(V2) states, so each move must also keep (V3): a move that
releases some agent's b to the leftover goods breaks (V3) for that agent's lower pair, unless the agent also moves (to
b, laterally). The hard dead-good states of §7.7 with frozen downgrades (V11) are (V3)-valid, so (V3) does not by
itself remove the open case of §7.

## 9. The improvement step for DE4ᵛ³: what holds, and why it fails

The improvement form of DE4ᵛ³ asks: every (V3)-valid state without an EFX₀ completion has a better (V3)-valid state.
Two lemmas reduce it to the states of the largest level sum, and a counterexample there refutes it.

**Lemma R (repair).** Let Z be valid ((V1), (V2)). Repeatedly let an agent u that holds its lower pair {c_u, d_u}, while
its b_u is leftover, take {b_u} instead (c_u and d_u become leftover). This ends, and the result Z* is (V3)-valid, with
every agent at the same level as in Z; only the switched agents' values change (they drop).

*Proof.* Each step lowers the number of lower-pair holders, so the process ends. Consider one step. (V1): u now wants
only goods worth more than v(b_u), i.e. its top a_u, which it wanted before (v(a_u) > v(c_u) + v(d_u)), so a_u is held
alone. Nobody else's value changed; c_u and d_u were in a two-good holding, so nobody wanted them (Lemma 1(b)), and
b_u was leftover, so nobody wanted it. (V2): {b_u} threatens nobody. Every two- or three-good holding misses R_u: a_u is
held alone, b_u is u's, c_u and d_u are leftover. So nobody threatens u. The other values and holdings are unchanged.
Levels: v(b_u) has level 3, the lower pair's level. ∎

**Lemma V (moves that release nothing keep (V3)).** Let Y be (V3)-valid and Z valid, with every agent's value in Z at
least its value in Y and every good held in Y held in Z. Then Z is (V3)-valid.

*Proof.* Let w hold its lower pair in Z. If it held it in Y, its b was held in Y, hence in Z. Otherwise
v_w(Y_w) < v(c_w) + v(d_w). If v_w(Y_w) < v(b_w), then w wanted b_w in Y, so b_w was held (V1). Otherwise Y_w is a
holding worth at least v(b_w) and less than v(c_w) + v(d_w): the only one is {b_w} (a single good other than b worth
that much would be a_w, worth more than the pair; a set of two or more goods would be an upper set, worth more than
a_w, or the lower pair). So b_w was held in Y, and it is held in Z. ∎

Both lemmas are checked by brute force on every valid state, and every such pair of states, of random profiles with
n = 3, 4 and of the screen instances with n ≤ 4 (`python3 k4/de4/verify_repair.py`, `results/k4_de4/verify_repair.log`).

**Consequences.**
- *The level sum is free.* By Lemma R, the largest level sum Φ* over (V3)-valid states equals the largest over all
  valid states, and a (V3)-valid state Y with Φ(Y) < Φ* has a better (V3)-valid state (repair any state of level sum
  Φ*). So the improvement step needs proving only at Φ*: every non-completable (V3)-valid state with Φ(Y) = Φ* needs a
  (V3)-valid value-Pareto-better state with Φ = Φ*. There, no valid state has a higher level sum. This excludes every
  improvement of the hard states of §7.7 (V9, V11), which all raise the level sum.
- *Rotations keep (V3).* The labelled trades of Theorem 9 and Lemma 14 move whole holdings and release nothing, and
  every taker gains, so by Lemma V they keep (V3). Hence Corollary 10 (machine-checked, `EFX.DE4.cor10`) holds for
  DE4ᵛ³ as stated: under (H), if every free agent holds one good, the walk's trade is a better (V3)-valid state.
- *At Φ*, Lemma 4's walk is trivial.* An agent threatened by the leftover goods alone is free: otherwise its upgrade
  passes its good to a wanter, whose level rises, so the level sum would rise. So at Φ* the remaining (V3)-specific
  moves are lateral free upgrades. Of these, b to the lower pair always breaks (V3), because it releases the agent's
  own b. One upper set to a better one breaks it exactly when it releases another agent's b.

**Data at Φ*.** Non-completable (V3)-valid states with Φ = Φ* are rare: none in 1,200 random profiles with n = 3, 4. In
2,400 profiles of the stuck hypergraphs and the failing cores, all 37 such states have every agent holding an upper
set, and each is improved by Lemma 4′ or by the walk. The screen set has nine, all improved, by Lemma 4′, the walk's
rotations, or keep-own exchanges.

**The all-upper case and the counterexample.** If every agent holds an upper set (level 5), nobody wants anything,
(V3) is vacuous, and the order is value-Pareto alone. Theorem Z's argument (`k4/c4min.md` §3) carries over almost
verbatim:
- without Lemma 4′ moves, a non-robust agent ({a, d} with v(a) + v(d) < v(b) + v(c), or a rich pair {p, q} with
  v(a) + v(s) > v(p) + v(q)) is threatened by at most one agent's bundle together with J, and robust agents by none;
- so if no single owner can take J, the threat map is a permutation;
- along a cycle of it, each agent can take what it needs from its threatener: {b, c}, or {a, s}, or {a, x} keeping one
  of its own goods that its successor does not need. Everyone gains.

This fails exactly when two agents of the cycle need the same leftover good as their fourth good. The instance R4 of
`attempts/k4-de4-ss.md` is built that way (n = 4, m = 9, every agent 4-good). Its all-upper state with one leftover
good is a maximum of DE4ᵛ³ (and of DE4) with no EFX₀ completion. **So Conjecture DE4ᵛ³ and its improvement step are
false.** Theorem Z avoids the conflict by maximizing the number of robust agents, which here is 0 and is 1 at every
completable maximum.

**Next candidate.** Give robust upper sets level 6 (or 5.5) and non-robust ones level 5. A robust set is worth at
least half of v(R_i) and a non-robust one less, so Lemma 1(a) still holds. With (V3) this passes the screen and R4
(`attempts/k4-de4-ss.md`); without (V3) it still fails on A131. Its exhaustive tests and its improvement step are
open. In its all-upper case the rotation above raises the level sum whenever it makes one agent robust and keeps
everyone's level, so the Pareto requirement, which is what R4 breaks, is no longer needed there.

## 10. The robust order: the improvement step, proved except one case

The candidate of §9 (ledger K4.DE4V3R): the states of DE4ᵛ³ ((V1), (V2), (V3)) and DE4's levels, except that an upper
set S of agent i is *robust* if v_i(S) ≥ v_i(R_i ∖ S), and robust upper sets have level 6, non-robust ones level 5. The
order is the level sum Φ, then value-Pareto. The improvement step asks: every non-completable (V3)-valid state has a
better (V3)-valid state.

**What carries over.** Lemma 1(a) holds: a robust upper set is worth at least v_i(R_i)/2 and a non-robust one less, so
among an agent's holdings value and level still agree. Lemma R and Lemma V (§9) do not involve the levels of upper sets.
So, as in §9:
- a (V3)-valid state with Φ < Φ* (the largest level sum over all valid states) has a better (V3)-valid state;
- at Φ*, every valid state is a candidate only through value-Pareto improvements, and no valid state has a larger Φ.

**Theorem 16.** Let Y be (V3)-valid and not completable. Then Y has a better (V3)-valid state in each of these cases:
1. Φ(Y) < Φ*;
2. some agent holds nothing (then, unless the leftover goods alone threaten someone, Y is completable: Corollary 5(b));
3. some agent x is threatened by the leftover goods alone and its upgrade of Lemma 4 keeps (V3). At Φ*, such an x is
   free and its upgrade is lateral (same level), since otherwise the level sum would rise;
4. a free agent has a self-upgrade (Lemma 4′) that keeps (V3);
5. (H) holds and no free agent holds two or more goods (Corollary 10);
6. (H) holds and DE's walk of Theorem 9 closes;
7. every agent holds an upper set (Theorem A′ below).

*Proof.* Case 1 is Lemma R. Cases 3 and 4: the moves are value-Pareto, so Φ does not drop (Lemma 1(a)). At Φ*, if x were
frozen its good would pass to a wanter, whose level rises, and Φ would exceed Φ*. Cases 5 and 6: Theorem 9's trade
moves whole holdings and labelled leftover goods, releases nothing, and every taker gains, so by Lemma V it keeps (V3),
and it is value-Pareto-better. Case 7 is Theorem A′. ∎

**Theorem A′ (all-upper states).** Let every agent of Y hold an upper set, Y not completable, and no free self-upgrade
(Lemma 4′) apply. Then the rotation below gives a valid state with a larger level sum.

*Proof.* Nobody wants anything (every holding is worth more than any single good), and (V3) is vacuous: nobody holds a
lower pair. Let J ≠ ∅ be the leftover goods.
- A robust agent i is threatened by no bundle B: θ_i(B) ≤ v_i(B ∩ R_i) ≤ v_i(R_i ∖ Y_i) ≤ v_i(Y_i). Upper sets of 3-good
  agents, {a, b} and {a, c}, and {b, c, d} are robust. So a threatened agent is a 4-good agent of kind D (it holds
  {a, d} with v(a) + v(d) < v(b) + v(c)) or kind R (it holds a rich pair {p, q}, v(p) + v(q) > v(a), with
  v(a) + v(s) > v(p) + v(q) for its fourth good s).
- Without a self-upgrade, b, c ∉ J for kind D (else {a, b} or {a, c}) and a ∉ J for kind R (else {a, p}). Let the
  owner o take Y_o ∪ J (at least three goods). A kind-D agent is threatened by it iff {b, c} ⊆ Y_o; a kind-R agent iff
  a ∈ Y_o and s ∈ Y_o ∪ J. So every agent is threatened by at most one owner.
- Y is not completable, so no owner is valid. Choosing for each owner o an agent σ(o) it threatens gives an injective
  map, hence a permutation, so every agent is threatened and every agent is of kind D or R.
- Take a cycle of σ and give each agent i = σ(o) of it, from o:
  - kind D: {b_i, c_i} ⊆ Y_o, robust, so level 5 → 6;
  - kind R: {a_i, s_i}, robust (level 6), if s_i ∈ Y_o, or if s_i ∈ J is not yet used on the cycle (then i is the
    *winner* of s_i); otherwise {a_i, x}, keeping a good x of Y_i that its successor does not need (an upper set,
    level ≥ 5); otherwise {a_i} (level 4: a *loser*). The successor σ(i) needs {b, c} ⊆ Y_i if it is of kind D, and
    a and, when it lies in Y_i, s if it is of kind R.
- A loser's successor needs all of Y_i and gains a level (it becomes robust). Losers' successors are distinct
  (σ is injective) and are not losers. A winner is not the successor of a loser: such a successor takes its s from
  Y_i, not from J. Losers exist only when two agents of the cycle need the same leftover good, and then that good
  has a winner. So the level sum changes by at least (number of winners) ≥ 1 if there is a loser, and by the
  cycle's length ≥ 2 otherwise, unless agents keep their own goods, which happens only next to a winner. Either way
  Φ rises.
- Validity: nobody wants anything (every new holding is an upper set or the agent's top), so (V1) holds and two-good
  holdings threaten nobody. A loser has all of R_i held by agents of the cycle (a_i by itself, the goods of Y_i by its
  successor, s_i by the winner), so no unchanged three-good holding threatens it. Nobody holds a lower pair: (V3). ∎

Theorem A′ is the argument of Theorem Z (`k4/c4min.md` §3) with DE4's holdings. The robust level is what lets the
rotation raise Φ instead of having to improve everyone's value, which is how R4 refutes DE4ᵛ³.

**What remains.** The non-completable (V3)-valid states with Φ(Y) = Φ* that are not all-upper, satisfy (H) (once the
moves of cases 3 and 4 are exhausted), have a free agent holding two or more goods, and at which the walk stops. Also
included are those where the only moves of cases 3 and 4 break (V3) (a free holder of b whose upgrade is its lower pair,
or a lateral upper-set upgrade that releases another agent's b). Equivalently, it suffices to prove:

**Claim T** (row K4.DE4V3R.T). In the robust order, every non-completable (V3)-valid state of the largest level sum is
all-upper.

With Theorem 16 and Theorem A′, Claim T implies the improvement step, hence the conjecture K4.DE4V3R, hence TARGET₄.

**Evidence** (`python3 k4/de4/verify_robust.py`, `results/k4_de4/verify_robust.log`; and `k4/de4/de4r.c`, which counts
Claim T's failures in the exhaustive runs of K4.DE4V3R): every step of the proofs above (Theorem A′'s construction,
the freeness at Φ*, Corollary 10 and the closed walk in the robust order) holds on every state checked (7,800 random
profiles: Theorem A′ in 61 cases, Corollary 10 in 905, the closed walk in 536), and no non-completable state of the
largest level sum that is not all-upper has been found; in those profiles none of the largest level sum occurs at all.

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
python3 k4/de4/variants.py                                      # the refuted variants (V1-V10)
python3 k4/de4/dead.py stuck k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz 4000 40 1000   # §7.8; other runs: see the logs
python3 k4/de4/lemma15.py suite                                 # Lemma 15 by brute force
bash k4/de4/run_all.sh                                          # every log of §4 except the two C exhaustive runs
```
Needs python-sat (`requirements.txt`) and gcc.
