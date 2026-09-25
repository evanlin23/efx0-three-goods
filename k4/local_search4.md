# Two-phase local search for k = 4 cores (Algorithm LS4)

Workstream `proof/k4-localsearch`. Ledger rows `K4.LS.*`. This carries the two-phase local search of
`proofs/local_search.md` (Algorithm LS2, Theorem C, row LS3) from three to four relevant goods per agent. It is a
route to TARGET₄ that does not go through construction LB₄ (`k4/SCOUT.md` §5).

**Status in one paragraph.**
- *Proved here, pending review:* Algorithm LS4 is sound and terminates in at most Σ_i (2^{d_i} − 1) ≤ 15n Phase-1 steps (Theorem 1). Every state it produces is a junk-free EFX₀ partial allocation. Every output is a complete EFX₀ allocation. The algorithm fails only if it reaches a state that no move improves and that no placement of Phase 2 completes.
- *Open:* that this never happens is **conjecture TP₄** (§4). With K4.CORE and K4.TIE it would give TARGET₄.
- *For cores whose agents all have three goods,* TP₄ follows from the proof of Theorem C of `proofs/local_search.md` (Proposition 3, conditional on that proof, which is itself pending review).
- *Computation (EVIDENCE):* LS4 never fails in the runs of §5. These are exhaustive for n ≤ 3, ties included, and for the mixed n = 4 cores with at most two 4-good agents. The other n = 4 and n = 5 cores of the certificate files are sampled.
- *Negative results:* four natural variants fail, each with a small configuration replayed by an independent brute force (§6, `attempts/k4-ls-*.md`).
- *Not proved:* a polynomial bound on the total running time. The number of steps is linear, but the implementation searches for exchange cycles and for the Phase-2 split by enumeration.

## 0. Setting and notation

An instance with additive values; R_i = {g : v_i(g) > 0}, d_i = |R_i| ≤ 4. The algorithm and Theorem 1 need nothing
else. TP₄ is stated for k = 4 cores (K4.CORE in `k4/SCOUT.md`): d_i ∈ {3, 4}, every agent strictly balanced, at most
d_i − 2 private goods, every good valued by someone; connectivity is not needed.

*Strict types.* The algorithm runs on V_i = 32 v_i + w_i, with w_i(g) = 2^(position of g in R_i) on R_i and 0 elsewhere,
for integer values v_i (every type has an integer representative in [1, 16]⁴, K4.OT).
- V_i is *strict*: its 2^{d_i} subset sums on R_i are distinct, since the parts w_i(S) < 32 are distinct.
- V_i *refines* v_i: v_i(S) > v_i(T) implies V_i(S) > V_i(T).
- Conversely V_i(S) ≥ V_i(T) implies v_i(S) − v_i(T) ≥ (w_i(T) − w_i(S))/32 > −1/2, so v_i(S) ≥ v_i(T), because the values are integers. Hence **an allocation that is EFX₀ for V is EFX₀ for v**, since EFX₀ is a conjunction of weak inequalities v_i(A) ≥ v_i(B).
- The algorithm only compares subset sums of one agent. So its run depends only on the strict type of V (the order of its subset sums on R_i).

For real values, K4.TIE reduces tied profiles to strict ones. §5 covers the tied profiles of n ≤ 3 cores directly.

*Partial allocations.* Y assigns each good to at most one agent; U is the pool (unallocated goods).
- σ_i := V_i(Y_i).
- Y is *junk-free* if Y_i ⊆ R_i for all i.
- The *threat* of a nonempty bundle B to agent i is θ_i(B) := max_{g∈B} V_i(B ∖ {g}). It equals V_i(B) if B contains a good outside R_i, and V_i(B) − min_{g∈B} V_i(g) otherwise.
- Agent i is *safe* if σ_i ≥ θ_i(Y_j) for every j ≠ i with Y_j ≠ ∅. Y is EFX₀ if every agent is safe; the pool imposes nothing.
- A set Z is *threat-free for agent h* if θ_x(Z) ≤ σ_x for every x ≠ h.
- i *envies* j if V_i(Y_j) > σ_i. A *source* is an agent nobody envies.

*Levels.* ℓ_i := #{T ⊆ R_i : V_i(T) < σ_i} ∈ {0, …, 2^{d_i} − 1} for junk-free Y. It strictly increases with σ_i, since V_i is strict. Φ := Σ_i ℓ_i ≤ Σ_i (2^{d_i} − 1) ≤ 15n.

## 1. Two general lemmas

**Lemma A (threat bound; `proofs/local_search.md` Lemma 3, which never uses k).**
- θ_i is monotone: ∅ ≠ B′ ⊆ B implies θ_i(B′) ≤ θ_i(B).
- Let Y be EFX₀ and let Y′ be a partial allocation such that
  - (i) V_h(Y′_h) ≥ σ_h for every h, and
  - (ii) every nonempty Y′_j is contained in a bundle of Y, or is threat-free for j with respect to Y.

  Then Y′ is EFX₀.

*Proof.* Monotonicity: for B = B′ ∪ D, max_{g∈B} V(B ∖ g) ≥ max_{g∈B′} V(B ∖ g) ≥ max_{g∈B′} V(B′ ∖ g).

Fix h and j ≠ h with Y′_j ≠ ∅.
- If Y′_j ⊆ Y_l, then θ_h(Y′_j) ≤ θ_h(Y_l). This is ≤ σ_h: if l ≠ h because Y is EFX₀, and if l = h because θ_h(B) ≤ V_h(B).
- Otherwise θ_h(Y′_j) ≤ σ_h by (ii).

In both cases θ_h(Y′_j) ≤ σ_h ≤ V_h(Y′_h). ∎

**Lemma B (envy is inside R).** If Y is EFX₀ and i envies j, then Y_j ⊆ R_i.

*Proof.* Otherwise Y_j contains a good g ∉ R_i, and θ_i(Y_j) ≥ V_i(Y_j ∖ g) = V_i(Y_j) > σ_i. ∎

## 2. Algorithm LS4

Start with Y_i = ∅ for all i and U = M. Repeat:
1. **(M1, single-agent rebundle)** Some agent h has a set Z ⊆ R_h ∩ (Y_h ∪ U) with V_h(Z) > σ_h that is threat-free for h. Then Y_h := Z; the goods of Y_h ∖ Z go to U.
2. **(R, rotation)** The envy graph has a cycle. Each agent on it takes the bundle of the agent it envies.
3. If U = ∅, output Y. If Phase 2 below applies, apply it and output the result.
4. **(X, exchange cycle)** There are distinct agents i_0, …, i_{L−1}, L ≥ 2, and pairwise disjoint sets Z_t ⊆ R_{i_t} ∩ (Y_{i_t} ∪ Y_{i_{t+1}} ∪ U) (indices mod L) such that each Z_t meets Y_{i_{t+1}}, V_{i_t}(Z_t) > σ_{i_t}, and Z_t is threat-free for i_t. Then each i_t takes Z_t; every other good of these agents' bundles goes to U. So an agent may keep part of its own bundle and take part of the next one; the rest of both goes to the pool.
5. Otherwise stop: **failure**.

**Phase 2.** Let U ≠ ∅.
- (a) If some bundle Y_e is empty: Y_e := U.
- (b) Else, if some source s values no good of U and Y_s ∪ U is threat-free for s: Y_s := Y_s ∪ U.
- (c) Else, if there are a source s* and J ⊆ U ∖ R_{s*} with Y_{s*} ∪ J threat-free for s*, and the goods of U ∖ J can be given one each to distinct sources s ≠ s* with u ∉ R_s and Y_s ∪ {u} threat-free for s: do so (*DM*: a dump plus solo goods).

*Choice points.* Any valid choice may be taken. The implementation `k4/ls4alg.c` takes, in step 1, the first agent in index order with a move and its least valuable improving Z. In step 2 it takes the first cycle found. In step 4 it takes the first cycle in order of length, then agent set, then order, then sets. In Phase 2 it takes the first s, s*, J and matching found. Theorem 1 holds for every choice; the evidence of §5 is for this rule.

Every rule compares subset sums of single agents only, so the run is determined by the profile of strict types.

## 3. Soundness and termination

**Theorem 1.**
- (i) Every state Y of LS4 is a junk-free EFX₀ partial allocation.
- (ii) Every move of steps 1, 2 and 4 raises Φ by at least 1. So LS4 performs at most Σ_i (2^{d_i} − 1) ≤ 15n₄ + 7n₃ moves.
- (iii) Every output is a complete allocation that is EFX₀ for V, hence for v.
- (iv) LS4 fails only at a state Y with U ≠ ∅ where no M1, R or X move applies and none of (a)–(c) applies.

*Proof.* The empty allocation is junk-free and EFX₀.

(i) and (ii):
- *M1.* Z ⊆ R_h, so no junk is created. Only h's bundle changes, and h's value rises. Z is threat-free for h, so Lemma A applies: every other bundle is an old bundle. ℓ_h rises and the other levels are unchanged.
- *R.* By Lemma B each agent on the cycle receives a subset of its own relevant goods. Each strictly improves, and the new bundles are old bundles, so Lemma A applies.
- *X.* The Z_t are disjoint subsets of R_{i_t}. Each mover strictly improves, the others keep their bundles, and each new bundle Z_t is threat-free for its holder, so Lemma A applies.

In each case Φ strictly increases and is bounded, so there are at most Σ_i (2^{d_i} − 1) moves.

(iii) *Phase 2 (b), (c).* Every receiver r gets goods outside R_r, so all values σ_h are unchanged. Consider h and a bundle X_j with j ≠ h.
- If j received nothing, θ_h(X_j) = θ_h(Y_j) ≤ σ_h, since Y is EFX₀.
- If j received, θ_h(X_j) ≤ σ_h by the threat-freeness condition.

So X is EFX₀ and complete.

*Phase 2 (a)* is applied only after step 1 found no move, so Lemma 2 below applies.
- V_e(u) ≤ σ_e = 0 for every u ∈ U by (F1), so e values nothing in U.
- For h ≠ e: θ_h(U) ≤ V_h(U) = V_h(U ∩ R_h) ≤ σ_h by (F2).
- Every other bundle and every value is unchanged.

(iv) is the case analysis of the loop. ∎

**Lemma 2 (what the absence of M1 moves gives; uses d_h ≤ 4).** Let Y be junk-free and EFX₀ with no M1 move. Then:
- (F1) V_h(u) ≤ σ_h for every agent h and every u ∈ U;
- (F2) V_h(U ∩ R_h) ≤ σ_h for every agent h.

*Proof.* (F1) Otherwise h can take Z = {u}: θ_x({u}) = 0 for every x, a valid M1 move.

*Pairs.* If P ⊆ U ∩ R_h has two goods and V_h(P) > σ_h, then h can take P. By (F1), θ_x(P) is the larger of x's two single values, which is ≤ σ_x. This would be a valid M1 move. So V_h(P) ≤ σ_h.

(F2) If U ∩ R_h ≠ ∅, then σ_h > 0 by (F1), so Y_h ≠ ∅ and W := U ∩ R_h has at most 3 goods. Let x ≠ h.
- If W ⊄ R_x, then θ_x(W) = V_x(W ∩ R_x), and |W ∩ R_x| ≤ 2, so it is ≤ σ_x by (F1) and the pair bound.
- If W ⊆ R_x, then θ_x(W) is the value of x's best two goods of W, ≤ σ_x by the pair bound.

So W is threat-free for h, and V_h(W) > σ_h would give a valid M1 move. ∎

## 4. The conjecture, and the case of three goods

**Conjecture TP₄.** Let Y be a junk-free EFX₀ partial allocation of a k = 4 core with U ≠ ∅, and suppose no M1, R or X move applies. Then Phase 2 (a), (b) or (c) applies.

By Theorem 1, TP₄ implies that LS4 always outputs a complete EFX₀ allocation. With K4.CORE and K4.TIE (`k4/SCOUT.md` §2) this gives TARGET₄. The implementation tests the equivalent lazy form on every state it reaches: whenever no M1 or R move applies and (a)–(c) fail, an X move exists.

The shape of (c) is forced, in the following sense. Some state stable under every Pareto move, even every coalition move, admits no single dump (b). The only complete EFX₀ allocation that is at least as good for everyone as that state splits the pool over two sources (`attempts/k4-ls-single-dump.md`). So Phase 2 must be able to split the pool, as LS2's matching does at k = 3.

**Proposition 3 (three goods; conditional on `proofs/local_search.md` §4).** If every agent of the core has three goods, TP₄ follows from Claims 2–4 of Theorem C of `proofs/local_search.md`.

*Proof.* Every step of LS2 is an M1, R or X move of LS4:
- LS2's steps 1, 3, 4 and 5 give EFX₀ results (Claim 1) in which one agent takes a set of its own goods from its bundle and the pool, so they are M1 moves.
- Step 2 is R.
- Step 6 (champion path s = t_0 → … → t_r = i, with i taking {u, y} ⊆ Y_s ∪ U) and step 7 (the cycle C of Claim 3) are X moves:
  - each agent takes a subset of its successor's bundle, plus at most one pool good, that meets the successor's bundle;
  - the taken sets are disjoint and every agent strictly improves;
  - each new bundle is either an old bundle, whose threat to anyone other than its old holder is bounded because Y is EFX₀, and to its old holder by θ ≤ V, or a pair {u, y} of two goods nobody envies.

Now let Y be as in TP₄. If some bundle is empty, (a) applies. Otherwise steps 1–7 of LS2 do not apply, so by Claims 2 and 4, LS2's Phase 2 (b) gives a complete EFX₀ allocation. In it, a one-good source s* that values no good of U (Claim 2 (e)) receives U ∖ D(T), and each u ∈ D(T) goes alone to a distinct one-good source M(u) ≠ s* that does not value it. Every bundle of an EFX₀ allocation is threat-free for its holder, and the σ_h are unchanged. So this placement is a DM placement, and (c) applies. ∎

**Where the k = 3 proof stops at four goods.** Each of the following is observed in LS4's stable states:
- *Lemma 1 of `proofs/local_search.md` fails.* A 4-good agent's safety is not a condition on single goods: it compares sets, type by type (K4.OT: 12 behaviourally distinct types per ranking).
- *Lemma 2 fails.* An agent may envy a bundle of two or three goods. A source with two goods may envy. So backward envy walks need not end at one-good sources.
- *m ≤ 3n.* One-good sources need not exist.
- *Placement constraints are not per good.* At a source s, a minimal set J ⊆ U such that Y_s ∪ J is not threat-free can have one, two or three goods. Two-good sets whose goods are both valued by the envier occur at n = 3 (`k4/ls4.c`, counters B1, B2a, B2b, B3). At k = 3 every such constraint is "u must sit alone next to the source's single good".
- *Exchange cycles must keep own goods and can be long.* Cycles without keep fail at n = 3 (`attempts/k4-ls-exchange-no-keep.md`). Length ≤ 2 fails at n = 4. Cycles in which at most one agent takes pool goods fail at n = 5 (§6).

## 5. Computational evidence (not part of any proof)

`k4/ls4alg.c` implements LS4 exactly as in §2. The driver `k4/ls4alg_run.py` takes the cores from the certificate files `results/k4_certs_*.json.gz` (complete core lists by the orbit count of `k4/check4.py`) and the types from `k4/check4.py`'s `core_domains`. After every Phase-1 step the program checks junk-freeness, EFX₀ and the rise of Φ. It checks every output for completeness, EFX₀ under V, and EFX₀ by the raw definition v_i(X_i) ≥ v_i(X_j) − v_i(h) with the integer representative.

*Ties.* A tied profile runs exactly like the strict profile of its perturbations (§0). With `--ties`, every balanced weak type of `core_domains(..., ties=True)` is attached to the strict type of its perturbation 32 v + w, and the output is also checked by the raw definition against every attached tied type. So one strict run covers every tied profile that maps to it. Every tied type maps into the strict domain (asserted).

*Sensitivity test* (`results/k4_ls4_sensitivity.log`). Without exchange cycles (`-DNOX`) the n = 2 run reports failures. So does a Phase 2 that dumps U unchecked (`-DBADDUMP`), and the raw check reports it too. Both runs have exit status 1.

RESULTS_TABLE

## 6. Variants that fail (`attempts/k4-ls-*.md`; replayed by `python3 k4/ls4_attempts.py`)

`k4/ls4_attempts.py` is an independent brute force in plain Python, working from the raw definition and the explicit integer values. It enumerates every move of each family and every completion.

| variant | smallest failing configuration found | file |
|---|---|---|
| Phase 1 = M1 and R only | n = 2, m = 4: a stable state with no completion at all | `attempts/k4-ls-no-exchange.md` |
| exchange cycles without keeping own goods (includes the k = 3 champion cycles) | n = 3, m = 6: a stable state with no completion at all | `attempts/k4-ls-exchange-no-keep.md` |
| Phase 2 = one dump only | n = 4, m = 7: stable even under all coalition moves; the only EFX₀ completion splits the pool | `attempts/k4-ls-single-dump.md` |
| exchange cycles of length ≤ 2, or with at most one pool-using agent | n = 4 (length), n = 5 (pool); random samples, `k4/ls4.c -L 2`, `-1` | this section |
| Phase 2 = "clean" placement plus solo matching, ignoring values | fails in about 3% of stable n = 3 states, where the value slack makes a dump valid | this section |

The last two rows are single-implementation sample counts from `k4/ls4.c` (the exploratory engine, `k4/ls4_run.py`).
- Length ≤ 2: 302 failures in 219,000 pure n = 4 profiles.
- At most one pool-using agent: 3 failures in 5,468,000 n = 5 profiles.
- Clean placement: 8,821 failures in 304,901 stable states.

## 7. Complexity

- The number of Phase-1 moves is at most Σ_i (2^{d_i} − 1) ≤ 15n (Theorem 1).
- Steps 1 and 2 and Phase 2 (a), (b) take polynomial time.
- The implementation finds step 4's exchange cycles and Phase 2 (c)'s split by enumeration: over agent sequences and over subsets of the pool.
  - Cycles of every length up to n occur (§5), so bounding the length is not an option (§6).
  - Edge-local validity (threat-freeness of each Z_t with respect to the old values, which is how X is defined) loses nothing in the samples. So an exchange cycle is a cycle in a product graph on (agent, kept part of its bundle). The only non-local constraint is that the pool goods used by different agents must be disjoint.
- Whether an improving exchange cycle, and a DM placement, can always be found in polynomial time is open. So is whether a Hall-type argument as at k = 3 decides between them.

## 8. Status

- Theorem 1, Lemmas A, B, 2: written proofs here, pending review (ledger K4.LS.SOUND, CONJECTURE until reviewed).
- Proposition 3: conditional on Theorem C of `proofs/local_search.md`, pending review (K4.LS.K3).
- Conjecture TP₄: open; EVIDENCE in §5 (K4.LS.TP).
- Refuted variants: §6, EVIDENCE with independent brute-force replay (K4.LS.VAR).
