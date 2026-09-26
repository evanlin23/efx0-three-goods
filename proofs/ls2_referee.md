# Referee report on Theorem C of `proofs/local_search.md` (Algorithm LS2)

Workstream `formal/k3-algo`, Track B (the coordinator's request, relaying the owner): an independent review of §4 of
`proofs/local_search.md` (Theorem C, Claims 1–5), with the lemmas of §1 it uses. It is backed by brute-force checks
written from the raw definitions, not from `src/ls_alg.c` or `src/local_search.py`. Ledger rows: LS3 (unchanged,
CONJECTURE), K3.LS2 (this review), K3.LS2.RUN (the computations).

**Verdict.** I found no error in §4. Every step of Claims 1–5 follows from Lemmas 1–3 and L4 as written. The brute-force
checks below confirm every claim, under exactly the preconditions the proof uses and at every choice point: on every
junk-free EFX₀ partial allocation of every core with n ≤ 4 (connected or not) and every strict ranking profile, and on
complete runs of LS2 with random choices for every core with n ≤ 5. The remarks at the end are imprecisions, none of
which affects correctness. This is one review. Per the owner's policy, LS3 stays CONJECTURE until LS2's correctness is
also machine-checked.

## 1. Line by line

**Lemma 1** (partial EFX₀ in a core is ordinal and local).
- The five cases on S_i are complete for a core agent. Each "iff" is argued in both directions:
  - |S_i| ≥ 2: the other goods of R_i lie in at most one other bundle each, worth at most a < b + c.
  - S_i = {a}: rule (Q).
  - S_i = {b}: a must be free.
  - S_i = {c}: a and b must be free.
  - S_i = ∅: all three must be free.
- The case "X_j contains a good outside R_i, so θ = v(U)" uses F1's convention that the minimum over X_j is 0.
- Checked: the rule equals the raw definition, under three balanced realizations, on every partial allocation of
  every core with n ≤ 4 whose owned goods are valued by their holders (below).

**Lemma 2.** Correct. The first sentence uses (F): a good that k envies is free, so if it lies in X_j then
X_j = {x}.
- Otherwise every good of X_j ∩ R_k is worth at most v_k(X_k), so v_k(X_j) > v_k(X_k) needs two such goods.
- The four cases of S_k then force S_k = {a_k} and X_j ∩ R_k = {b_k, c_k}; (Q) gives |X_j| = 2.

**Lemma 3.** Correct.
- Monotonicity of θ: θ_h(B) − θ_h(B′) = v_h(D) − min_B + min_{B′} ≥ 0.
- The case that matters is B = X_h, where h's old bundle now belongs to someone else. It is handled by θ_h(X_h) ≤ v_h(X_h).
- The parenthetical claim for Z = {g, y} with g, y unenvied is right: θ_h(Z) ≤ max over the two goods, and an unenvied
  good is worth at most v_h(X_h).

**Algorithm LS2.** The loop tests steps 1–5, then stops if a bundle is empty, then tests 6 and 7. This matches the
preconditions the proofs use:
- steps 3–5 are applied only when step 1 does not apply;
- steps 6–7 are applied only when steps 1–5 do not apply and no bundle is empty.

The brute force (§2) checks each step under exactly these minimal preconditions. That is stronger than checking the
algorithm's order.

**Claim 1.**
- Junk-freeness is immediate: every taker takes goods of its own R.
- Lemma 3 (i) holds: the takers strictly improve, and the others keep their bundles.
- Lemma 3 (ii), per step:
  - Step 1: a singleton.
  - Step 2: subsets of old bundles.
  - Step 3: two pool goods, unenvied because step 1 does not apply.
  - Step 4: u is unenvied; a_i is unenvied because nobody envies i and Y_i = {a_i}.
  - Step 5: u is unenvied; y is the single good of a source.
  - Step 6: subsets of old bundles, plus {u, y}.
- Details that the text leaves implicit and that hold:
  - In step 6, s ≠ i, since an a-holder holds a_i, not y ∈ {b_i, c_i}. So r ≥ 1.
  - The envy path is simple: steps 1–5 do not apply, so the envy graph is acyclic.
  - The taken sets are disjoint, since they lie in the bundles of distinct successors, plus u ∈ U.
  - The old bundle {a_i} of i = t_r is taken by t_{r−1}.
- Σℓ strictly increases, because levels are strictly monotone in the value of the own goods.

**Claim 2.** (a)–(e) restate that steps 1–5 do not apply.
- (f) uses junk-freeness: a source with ≥ 2 goods holds ≥ 2 of its own, so it is rich and envies nobody (Lemma 2 (a)).
- (g) uses acyclicity and L4 (m ≤ 2n). L4 needs the core conditions: every good is valued, and at most one private
  good per agent (remark 2).
- (h): walking backwards from i, which is not a source by (d), reaches one-good sources with envy paths to i. If s
  had one, step 6 would apply, so the source reached is some s′ ≠ s.

**Claim 3.**
- f exists by (h) and has no fixed point, so it has a cycle of length ≥ 2.
- On the closed walk W, one-good sources have no incoming envy edges, and the chosen a-holders i_s envy nobody:
  - an a-holder envies no good;
  - it could envy only a bundle equal to {b_i, c_i} (Lemma 2), and one of these goods is in U.
- So in a shortest closed sub-walk C (a simple cycle), every agent has a determined outgoing edge: an envy edge, or
  a dirty edge i_s → s.
- C must contain a dirty edge (acyclicity). Its dirty edges enter distinct sources, so they carry distinct SDR goods.
- The move is Lemma 3:
  - the takers improve (envy; balance for the dirty edges);
  - the taken sets are disjoint (distinct successors, distinct pool goods);
  - the new bundles are old subsets or pairs {ℓ(s), y_s} of unenvied goods.
- Every envy path P_s has length ≥ 1, since f(s) is a source and i_s is not (Claim 2 (d)). So every source on C takes
  something and strictly improves.

**Termination.** Each step raises Σℓ ≤ 7n by at least 1, so Phase 1 takes at most 7n steps. If U = ∅ the output is
Y, complete, EFX₀, with bundles of ≤ 2 goods.

**Claim 4.**
- Receivers value no good of U:
  - case (a): an empty agent that valued a pool good would envy it (step 1);
  - case (b): receivers are one-good sources, Claim 2 (e).
- So levels and envied goods are unchanged.
- (F): envied goods are alone in non-source bundles, which receive nothing.
- (Q):
  - both goods in U is excluded by step 3;
  - both in Y in one bundle: that bundle is {b_h, c_h}, whose holder h envies, so it receives nothing;
  - one good u ∈ U and the other y in Y_j: u joins y only through a dirty triple, and the alternating-tree
    placement puts u ∈ D(T) at M(u) ≠ s*, alone with y.
- The well-definedness facts are the standard alternating-tree facts for a maximum matching:
  - an unmatched good in D(T) would end an augmenting path;
  - M(u) ∈ T;
  - s* is unmatched, so M(u) ≠ s*.
- Checked for every maximum matching and every unmatched s* (§2).

**Claim 5.** Correct, by induction on the steps; Phase 2 enlarges only X_e or X_{s*} beyond two goods.

## 2. Brute-force checks (`k3/ls2_referee.py`)

Written from the raw definitions:
- envy: v_i(Y_j) > v_i(Y_i);
- envy of a good: g ∈ R_i and v_i(g) > v_i(Y_i);
- levels: the rank of v_i(S_i) among the eight subset sums;
- EFX₀: v_i(X_i) ≥ v_i(X_j ∖ {g}).

All of these are computed numerically from a balanced realization; every produced allocation is checked for EFX₀
under three realizations.

**Mode `states`.** The inputs:
- every core with n ≤ 4: the connected cores of `results/certs_lb_2_6.json.gz` and the disconnected ones of
  `results/certs_lb_disconnected_4_6.json.gz`;
- every strict ranking profile;
- every junk-free partial allocation (each good in the pool or with one of its valuers).

For each such state, it checks:
- Lemma 1 against the raw definition (three realizations), for every state;
- for every EFX₀ state with U ≠ ∅:
  - Claim 1 for every instance of steps 1–6 under the proof's preconditions: junk-free, EFX₀, larger Σℓ, and bundles
    of ≤ 2 goods when Y has them;
  - Claim 2 (f), (g), (h);
  - Claim 3 for every SDR, every choice of dirty triples, successors and envy paths, every cycle of f and start, and
    every shortest closed sub-walk of W, read linearly and cyclically. For each: C is simple and has a dirty edge,
    the taken sets are disjoint, and the result is junk-free, EFX₀ and has larger Σℓ;
  - Claim 4 and Claim 5 for Phase 2 (a), with every empty bundle, and Phase 2 (b), with every maximum matching and
    every unmatched s*, including the facts about T, D(T) and M.

Result (`results/ls2_referee_states_4.log`):
- 53 cores (n = 2, 3, 4) and 10,650,186 junk-free EFX₀ states with a nonempty pool;
- checked instances: 40,847,004 of step 1, 974,676 of step 2, 118,060 of step 3, 491,968 of step 4, 756,240 of
  step 5, 19,876 of step 6 and 240 of step 7 (every choice), plus 14,976 Phase 2 (a) and 132,320 Phase 2 (b)
  completions;
- Claim 2 checked in 94,466 states;
- 0 failures, including Lemma 1 against the raw definition on every junk-free state.

Sampled n = 5 (`results/ls2_referee_states_5_sample.log`): every junk-free state for 20 random profiles of every core
with n ≤ 5. This covers 3,711,362 states, 104 step-7 instances (every choice), 7,273 Phase 2 (a) and 30,103 Phase 2 (b)
completions, with 0 failures.

**Mode `runs`.** LS2 from the empty allocation, with a random choice at every choice point (including step 7's), on
every profile of every core with n ≤ 5. Each output must be complete and EFX₀ (raw, three realizations), have at most
one bundle of more than two goods, and take at most 7n Phase-1 steps.

Result (`results/ls2_referee_runs_5.log`): 360 cores (307 with n = 5) and 2,445,840 runs. Of these, 1,735,316 end
complete after Phase 1, 126,832 in Phase 2 (a) and 583,692 in Phase 2 (b). At most 19 Phase-1 steps at n = 5 (bound
35). 0 failures.

## 3. Remarks (imprecisions; none affects correctness)

1. *Remark 1 of §4 (running time)* is correct in substance, but step 7's construction needs a word:
   - the envy paths P_s and f(s) can be found by breadth-first search from i_s in the reversed envy graph, which is
     O(n + m) per source;
   - W has O(n²) vertices, and a shortest closed sub-walk is found in one pass;
   - Phase 2's maximum matching takes O(n · |edges|) by augmenting paths.

   So a Phase-1 step costs O(n (n + m)), and LS2 costs O(n²(n + m)), which is O(n³) on a core
   (m ≤ 2n by L4). The implementation `k3/ls2.py` does
   exactly this (written analysis, not machine-checked).
2. *The core conditions are used, through L4.*
   - Claim 2 (g) needs m ≤ 2n (L4). L4 holds in a core because every good is valued and every agent has at most one
     private good.
   - With goods that nobody values, m can exceed 2n, and the proof of Claim 2 (g) no longer applies.
   - So an algorithm for general instances must run the full CORE reduction first:
     - L3: set the goods nobody values aside, and at the end eliminate envy cycles and give them to a source;
     - R2: peel agents with two private goods;
     - R1.
   - K3ALG (`proofs/k3_algorithm.md`) needs only R1, since LB⁺ allows goods nobody values and more private goods.
   - The envy-cycle elimination of L3 is polynomial here: each rotation raises the sum of the levels, which is at
     most 7n.
3. *Ties.* LS2 decides on a strict ranking (ties broken by index). The output is EFX₀ for every balanced valuation
   consistent with the strict ranking, so for the tied one too (L5 (iv)); §4 says so. The example in §4 shows that
   deciding on tied numbers directly can fail.

## 4. What this does not settle

- LS2's correctness is not machine-checked. Formalizing it would need a new Lean development: partial allocations
  with a pool, the envy graph and its paths, the closed walk of Claim 3, maximum matchings with the
  no-augmenting-path argument of Claim 4, and a computable CORE reduction with L3's envy-cycle elimination. It is
  handed to a second session (PR comment); see ledger row K3.LS2.
