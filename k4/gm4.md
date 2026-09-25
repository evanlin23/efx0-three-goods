# GM₄ is false: maxima of the level sum can be dead ends (k = 4)

Workstream `proof/k4-gm4`, ledger rows `K4.GM.*`. This builds on:
- `k4/ls4plus.md`: Algorithm LS4⁺, Theorem 1⁺, conjecture GM₄, and its equivalent form;
- `k4/local_search4.md`: Algorithm LS4, Theorem 1, Lemma 2, Lemma 5, Propositions 4 and 7.

**Status.** The refutations below are REFUTED in the ledger: GM₄, GM₄ˢ, GM₄∃ and the variants, as the coordinator asked for GM₄ and GM₄ˢ. Each counterexample is saved with a checker, `k4/gm4_counterexample.py`, a plain-Python brute force from the raw definitions that shares no code with the searches. The key facts of the smallest instances are also checked by hand. The coordinator reports an independent re-check of every counterexample with its own code (not recorded in this repository). Everything else here is EVIDENCE or CONJECTURE.
- **Conjecture GM₄ is false** (§2.1–2.2). Some junk-free EFX₀ partial allocations that maximize the level sum Σℓ admit no placement of their pool; they are dead ends. The smallest counterexample found has n = 4, m = 7 and two 4-good agents; pure n = 4 and pure n = 5 cores have them too.
- **The single-dump form GM₄ˢ is false already with one 4-good agent** (n = 4, m = 6; §2.3). The only placements there split the pool, so no rule that picks one dump source can prove GM₄.
- **The existence form GM₄∃ is false too** (§2.4; pure n = 4, m = 7). The profile has a *unique* Σℓ-maximum and it is a dead end. The 16 complete EFX₀ allocations of the profile reach at most Σℓ = 20 < 21. So **no argument of the form "take a Σℓ-maximum", with any tie-break, gives TARGET₄**.
- **Consequences** (§3):
  - the equivalent form "no dead end maximizes Σℓ" is false;
  - LS4⁺_n fails under some valid choices: the bad maximum of each of instances A–G is reached from the empty allocation by 4 single-agent rebundles (checked by `k4/gm4_counterexample.py`);
  - the route "GM₄ ⇒ LS4⁺ never fails ⇒ TARGET₄" is closed.

  **LS4⁺'s default rule has not failed**. It had 0 failures on:
  - the 136 distinct profiles with a bad maximum from the random and exhaustive runs;
  - the 2,247,609 distinct profiles next to the seven n = 4 counterexamples, which include the 148 profiles whose maxima are all bad;
  - the 16,546,776 distinct profiles around those 148.

  It stops early at placeable states. K4.LSP.RUN is unaffected, but the rule's correctness cannot be proved through GM₄ or GM₄∃.
- **Other potentials** (§6). Every potential tried has maxima without a placement, so each "every maximum" form fails. The potentials tried:
  - tie-breaks among the Σℓ-maxima (Σℓ², leximax, leximin);
  - Σℓ²;
  - Σ 2^ℓ;
  - leximax (Σ 16^ℓ);
  - fixed priority (the level vector in a fixed agent order, compared lexicographically; #29's `POT=2`).

  For Σℓ² and every Σℓ tie-break, the existence form fails as well (instance G). For fixed priority it fails for some agent orders (instance Q), though every profile tested has some order that works. For **Σ 2^ℓ and leximax** the existence form survives. In the targeted searches (7,750,832 distinct profiles for Σ 2^ℓ, 19,652,066 for leximax) and in 92M random profiles each, every profile had a placeable maximum. The targeted search closed at 384 distinct profiles with a bad maximum: changing one agent's type of any of them (both potentials), or two agents' types (leximax only), gives no new one. This is the only surviving statement of this kind: conjecture K4.GM.POT, evidence only.
- **Where GM₄ does hold** (§4; exhaustive, one implementation):
  - every strict profile of every k = 4 core with n ≤ 3;
  - n = 4 with one 4-good agent;
  - all-3-good cores with n = 5.

  In all of these, every maximum with a nonempty pool admits the empty-bundle dump or a single dump, except 2 maxima (one 4-good agent) that need a split.

Notation as in `k4/ls4plus.md` and `k4/local_search4.md` §0:
- Y is a junk-free partial allocation and U its pool;
- σ_i = v_i(Y_i);
- θ_i(B) = max_{g∈B} v_i(B ∖ g) is the threat of B to i;
- ℓ_i(S) = #{T ⊆ R_i : v_i(T) < v_i(S)} and Σℓ = Σ_i ℓ_i(Y_i);
- a *placement* of U gives each good of U to some agent so that the complete allocation is EFX₀ (LS4's Phase-2 shapes (a)–(d); at a maximum they are all junk placements).

All profiles are strict: all nonempty subset sums of each R_i are distinct, and every agent is strictly balanced. The integer representatives are those of `k4/check4.py` (`core_domains`).

## 1. The statements tested

- **GM₄** (`k4/ls4plus.md` §2). For every k = 4 core and every strict profile, every junk-free EFX₀ partial allocation that maximizes Σℓ among all junk-free EFX₀ partial allocations admits a placement. Equivalent form (referee of #29): no dead end maximizes Σℓ. A *dead end* is a junk-free EFX₀ partial allocation that no complete EFX₀ allocation weakly dominates.
- **GM₄ˢ** (the coordinator's sharpening, suggested by the data of #29). Every Σℓ-maximum with a nonempty pool admits the empty-bundle dump (a) or a single dump (b): some source s values no good of U and Y_s ∪ U is threat-free for s.
- **GM₄∃** (new). For every k = 4 core and every strict profile, *some* Σℓ-maximum admits a placement. Equivalently, the largest Σℓ of a junk-free EFX₀ partial allocation equals the largest Σℓ of the valued part of a complete EFX₀ allocation.

GM₄ˢ ⇒ GM₄ ⇒ GM₄∃ ⇒ TARGET₄, the last with K4.TIE and K4.CORE, by taking a maximum; no algorithm is needed.

## 2. The counterexamples

### 2.1 The smallest found: n = 4, m = 7, two 4-good agents (instance E)

It is the smallest found in two respects, by exhaustive runs of one implementation (`k4/gm4_fast.c`, §4). GM₄ holds for every profile with n ≤ 3 and for n = 4 with one 4-good agent. With two 4-good agents at n = 4, it fails only at m = 7, at 128 maxima in 3 cores.

Agents (good: value):
- agent 0: 0:3, 2:10, 4:6, 6:2 (4 goods; good 0 private);
- agent 1: 1:3, 3:4, 5:8, 6:2 (4 goods; good 1 private);
- agent 2: 2:4, 6:3, 3:2 (3 goods, ranking 2 > 6 > 3);
- agent 3: 5:4, 6:3, 4:2 (3 goods, ranking 5 > 6 > 4).

Good 6 is valued by all four agents. Goods 2, 3, 4, 5 each have one 4-good valuer and one 3-good valuer. It is a k = 4 core: connected, strictly balanced (10 < 11, 8 < 9, 4 < 5, 4 < 5), one private good per 4-good agent, strict subset sums.

Let Y = {0, 4} | {1, 3} | {2} | {5}, with pool U = {6}. The values are σ = (9, 7, 4, 4) and the levels (6, 6, 3, 3), so Σℓ = 18.

**Proposition GM-1.**
- (i) Y is junk-free and EFX₀.
- (ii) No assignment of good 6 to an agent gives an EFX₀ allocation. So Y admits no placement.
- (iii) Y maximizes Σℓ among all junk-free EFX₀ partial allocations of this profile.
- (iv) Y is a dead end: none of the 15 complete EFX₀ allocations gives every agent at least σ_i.
- (v) Y is reached from the empty allocation by four M1 moves: agent 2 takes {2}, agent 1 takes {1, 3}, agent 3 takes {5}, agent 0 takes {0, 4}.
- (vi) This profile has two other Σℓ-maxima, {2} | {1, 3} | {6} | {5} and {0, 4} | {5} | {2} | {6}, and both admit a placement.

*Proof of (i), (ii) and (v) by hand.*
- (i) The multi-good bundles are {0, 4} and {1, 3}.
  - {0, 4} meets only agents 0 and 3. θ_3({0, 4}) = v_3(4) = 2 ≤ 4.
  - {1, 3} meets only agents 1 and 2. θ_2({1, 3}) = v_2(3) = 2 ≤ 4.

  Singletons threaten nobody.
- (ii) Good 6 can go to any of the four agents:
  - at agent 0: θ_3({0, 4, 6}) ≥ v_3({4, 6}) = 5 > 4;
  - at agent 1: θ_2({1, 3, 6}) ≥ v_2({3, 6}) = 5 > 4;
  - at agent 2: θ_0({2, 6}) ≥ v_0(2) = 10 > 9;
  - at agent 3: θ_1({5, 6}) ≥ v_1(5) = 8 > 7.
- (v) Each step is a strict improvement of one agent to a set of its own goods from the pool.
  - After step 2: θ_2({1, 3}) = 2 ≤ 4; nobody else values goods of {1, 3}.
  - After step 4: θ_3({0, 4}) = 2 ≤ 4; nobody else values goods of {0, 4}.
  - Singletons threaten nobody, so every intermediate state is EFX₀.

*(iii), (iv) and (vi) by computation:*
- `k4/gm4_counterexample.py` enumerates all 1,620 junk-free partial allocations (each good in the pool or with one of its valuers) and all 4⁷ complete allocations, from the raw definition v_i(X_i) ≥ v_i(X_j ∖ g) with every good removable. Log: `results/k4_gm4_counterexample.log`.
- The same maximum was found independently by the branch-and-bound search `k4/gm4_fast.c` and re-checked by `k4/gm4_analyze.py`. The three programs share no code.

Every claim compares subset sums of one agent, so it holds for every valuation with these strict types. ∎

*Why the pool is stuck.* The envy graph has two edges: 0 → 2 (v_0(2) = 10 > 9) and 1 → 3 (v_1(5) = 8 > 7). So the sources are the two 4-good agents, 0 and 1.
- At source 0, the single dump fails because agent 3 envies {4, 6} ⊆ Y_0 ∪ U. Agent 3 is Lemma 5's champion for source 0, and it is reachable only from source 1.
- Symmetrically, agent 2 envies {3, 6} ⊆ Y_1 ∪ U and is reachable only from source 0.

The exchange cycle that Lemma 5 points to would need good 6 twice: 1 takes {5}, 3 takes {4, 6}, 0 takes {2}, and 2 takes {3, 6}. This is the Hall-type obstruction of `k4/local_search4.md` §4: the pool parts of the champion sets at different sources overlap.

In k = 3 terms, agents 2 and 3 are a-holders whose bottom pairs {6, 3} and {6, 4} share the pool good 6. At k = 3 the dirty good would go alone to a one-good source (Theorem C, Phase 2 (b)). Here the only one-good bundles belong to envied agents, and the two sources hold two goods each.

### 2.2 Pure cores

Four pure n = 4, m = 7 counterexamples (instances A–D, found in 43.8M random pure n = 4 profiles) have exactly the same mechanism: two sources, each envying a different singleton holder, and one pool good that both champions need. Instance A:
- agents 0: {0:3, 2:6, 5:2, 6:10}, 1: {1:1, 4:6, 5:8, 6:4}, 2: {2:2, 3:7, 5:8, 6:4}, 3: {3:6, 4:3, 5:4, 6:8};
- maximum Y = {0, 2} | {1, 4} | {5} | {6}, pool {3};
- agent 2 envies {2, 3} ⊆ Y_0 ∪ U, and agent 3 envies {3, 4} ⊆ Y_1 ∪ U.

None of the cores of A–F is isomorphic to the core of Proposition 7's dead end (networkx check). That dead end is not a maximum; these are.

Pure n = 5 has them as well (§4). Every counterexample found by the random and exhaustive runs has another maximum that admits a placement. These are A–F, the 128 exhaustive maxima and the four at n = 5 (`k4/gm4_counterexample.py` lists all maxima of A–F; `pallfail` = 0 in the logs of §4). The targeted search of §6 finds profiles where no maximum does (§2.4).

### 2.3 GM₄ˢ fails with one 4-good agent (instance S; n = 4, m = 6)

Agents:
- 0: {0:1, 2:6, 3:4, 4:8};
- 1: {1:2, 2:3, 5:4};
- 2: {1:3, 4:4, 5:2};
- 3: {3:3, 4:2, 5:4}.

The maximum Y = {4} | {5} | {1} | {3} has pool {0, 2}. No agent can take the whole pool with an EFX₀ result. Only the two split placements work: 0 → agent 2 with 2 → agent 3, and 0 → agent 3 with 2 → agent 2. Checked by `k4/gm4_counterexample.py`.

In the exhaustive run over all 7,247,232 profiles with one 4-good agent, this happens at exactly 2 maxima (the same core, two profiles; `results/k4_gm4_4_n4_1.log`). So a Phase 2 limited to one dump fails at maxima too, as it does at LS4-stable states (`attempts/k4-ls-single-dump.md`).

### 2.4 GM₄∃ fails: a unique maximum that is a dead end (instance G; pure n = 4, m = 7)

Take instance A and change agent 2's type from (2:2, 3:7, 5:8, 6:4) to (2:3, 3:6, 5:8, 6:4). Agents:
- 0: {0:3, 2:6, 5:2, 6:10};
- 1: {1:1, 4:6, 5:8, 6:4};
- 2: {2:3, 3:6, 5:8, 6:4};
- 3: {3:6, 4:3, 5:4, 6:8}.

**Proposition GM-2.**
- (i) Y = {0, 2} | {1, 4} | {5} | {6}, with pool {3}, is the *unique* junk-free EFX₀ partial allocation with the largest level sum, Σℓ = 21.
- (ii) It admits no placement.
- (iii) The profile has 16 complete EFX₀ allocations. The largest level sum of their valued parts is 20.

*Proof of (ii) by hand.* Good 3 is valued by agents 2 and 3.
- At agent 0: θ_2({0, 2, 3}) ≥ v_2({2, 3}) = 9 > 8.
- At agent 1: θ_3({1, 3, 4}) ≥ v_3({3, 4}) = 9 > 8.
- At agent 2: θ_1({3, 5}) ≥ v_1(5) = 8 > 7.
- At agent 3: θ_0({3, 6}) ≥ v_0(6) = 10 > 9.

(i) and (iii) by computation (`k4/gm4_counterexample.py`, instance G; found by `k4/gm4_fast.c`). ∎

So for this profile, no maximizer of Σℓ can be completed. Any argument that takes a Σℓ-maximum and places its pool fails here, whatever tie-break chooses among the maxima. This is the only maximum, and every LS4⁺ run that reaches a maximum stops with failure.

Such profiles are not isolated. The one-agent and two-agent neighbourhoods of the seven GM₄ profiles found at n = 4 contain 148 distinct such profiles (§6), 8 of them one agent away. All 148 lie in one core, the core of A and G. The bad maximum of G is reached from the empty allocation by 4 M1 moves (`k4/gm4_counterexample.py`).

## 3. Consequences for LS4⁺

- **LS4⁺_n fails under some choices.** For each of instances A–G, `k4/gm4_counterexample.py` prints a path of M1 moves from the empty allocation to the bad maximum; for E it is the path of Proposition GM-1 (v). M1 has priority in LS4 and LS4⁺ (`k4/local_search4.md` §2, `k4/ls4plus.md` §2), so the path is a valid run with some choices. At the bad maximum, no M1, R, X or C_n move applies: each of them raises Σℓ, and the envy graph is acyclic. Phase 2 has no placement. So LS4⁺_n stops with failure, exactly as Theorem 1⁺ allows.

  In instance G every maximum is bad, so every run of LS4⁺_n that reaches a maximum fails.
- **The default rule** (`k4/ls4alg.c -DCMOVE=8`, PR #29's program, used unchanged) completes all of these profiles. It stops early at a placeable state: at G it dumps at Σℓ = 17.
  - Both it and the alternative rule `-DALT` complete, without a coalition move, all 136 distinct profiles with a bad maximum from the random and exhaustive runs: the 7 seeds, the 128 exhaustive maxima with two 4-good agents, and the 4 at n = 5 (`results/k4_gm4_ls4plus_gmfail.log`).
  - `k4/gm4_ls4plus_around.py` ran it on every profile that changes the types of two agents of one of the seven GM₄ profiles found at n = 4: 2,260,332 runs covering 2,247,609 distinct profiles, including the 148 profiles whose maxima are all bad. It had 0 failures and never needed a coalition move (`results/k4_gm4_ls4plus_around2_4.log`; distinct counts in `results/k4_gm4_distinct.log`).
  - On the 148 profiles themselves, #29's alternative rule `-DALT` (most valuable rebundle first) with coalition moves also completes all 148, and so does the default rule (`results/k4_gm4_ls4plus_gmall_4.log`, via `k4/gm4_tols4.py`).
  - It also ran on every profile that changes two agents' types of one of those 148 profiles: 73,654,272 runs covering 16,546,776 distinct profiles. Again 0 failures and no coalition move (`results/k4_gm4_ls4plus_around2_gmall_4.log`).
  - So the evidence K4.LSP.RUN for that rule stands. But if the rule is correct, the reason is where it stops, not GM₄ or GM₄∃.
- **"No dead end maximizes Σℓ" is false**, and the level sum does not separate dead ends from completable states even in the existence sense (instance G). A proof along the LS4⁺ route needs one of:
  - a potential whose maxima all admit a placement (none found, §6);
  - an existence argument with a potential for which some maximum always admits a placement (Σ 2^ℓ and leximax survive, §6);
  - a choice rule, such as the default rule, together with a proof that it stops at a placeable state before it can reach a bad maximum.

## 4. Evidence

`k4/gm4_fast.c` finds all Σℓ-maxima of a profile by branch and bound over agents' bundles, with EFX₀ checked by the raw definition. For each maximum with a nonempty pool it checks, in order:
- (a) the empty-bundle dump;
- (b) a single dump;
- otherwise, every junk placement.

In the logs cited below, (a) counted a maximum with an empty bundle as placed without checking. That is sound by Lemma 2 of `k4/local_search4.md`: a maximum admits no M1 move, so an empty agent values no pool good and the pool is threat-free. The code now checks the dump from the raw definition and counts failures in `emptyfail`. Reruns with the check report `emptyfail` = 0 and otherwise identical counts. Maxima with an empty bundle, per class:
- n = 4, one 4-good agent: 115,581 (`results/k4_gm4_4_n4_1_echeck.log`);
- all-3-good n = 5: 74,025 (`results/k4_gm4_k3cores_5_echeck.log`);
- n = 4, one to three 4-good agents: 171,295 (`results/k4_gm4_4_mixed_sample_echeck.log`);
- n = 5, one or two 4-good agents: 344,310 (`results/k4_gm4_5_n4_12_sample_echeck.log`);
- n = 5, three: 186,391 (`results/k4_gm4_5_n4_3_sample_echeck.log`);
- n = 5, four: 62,772 (`results/k4_gm4_5_n4_4_sample_echeck.log`);
- pure n = 5: 26,798 (`results/k4_gm4_5_pure_sample_echeck.log`);
- n = 4, two 4-good agents, exhaustive: 3,046,488 (`results/k4_gm4_4_n4_2_echeck.log`).

These are all the classes of §4 with such maxima.

Checks on the tool and the data:
- It agrees exactly with the full enumeration `k4/gm4_explore.c` on the n = 2 run (236,176 maxima, 2,286 with a pool). It also agrees on a pure n = 4 sample of 438,000 profiles (2,000 per core): 622,450 maxima, 25,713 with a pool (`results/k4_gm4_fast_4_pure_2000.log` against `results/k4_gm4_h1_4_pure_sample.log`).
- At n = 2 it also agrees with #29's independent `k4/ls4_gm.c`, which counts the same 236,176 maximal states (`results/k4_gm_2.log`).
- Its n = 3 run covers 299,837,376 strict profiles, the count in row K4.LS.RUN.
- Cores come from the certificate files, whose core lists are complete by the orbit count of `k4/check4.py`, or from genbg via `k4/search4.py` (n = 5).
- Every counterexample is re-checked by `k4/gm4_counterexample.py`. Instances A–H, P, Q and S are checked for all their stated claims. All 136 distinct maxima without a placement in the GMFAIL lines of the random and exhaustive runs are checked for the core conditions, EFX₀, maximality and the absence of a placement (its BATCH line). These are the 7 seeds, the 128 exhaustive maxima with two 4-good agents and the 4 at n = 5 (3 of the seeds are among the 128, so 136 in all).

| class | profiles | how | maxima with a pool | no single dump | no placement (GM₄ fails) | log |
|---|---|---|---|---|---|---|
| n = 2 | 189,216 | exhaustive | 2,286 | 0 | 0 | `results/k4_gm4_2.log` |
| n = 3 | 299,837,376 | exhaustive | 9,227,950 | 0 | 0 | `results/k4_gm4_3.log` |
| n = 4, one 4-good agent | 7,247,232 | exhaustive | 1,131,363 | 2 | 0 | `results/k4_gm4_4_n4_1.log` |
| n = 4, two 4-good agents | 724,847,616 | exhaustive | 85,832,084 | 274 | 128 (all m = 7, in 3 cores) | `results/k4_gm4_4_n4_2.log` |
| n = 4, one to three 4-good agents | 39,150,000 | 50,000 random per core | 4,385,569 | 10 | 3 | `results/k4_gm4_4_mixed_sample.log` |
| n = 4, pure | 43,800,000 | 200,000 random per core | 2,583,713 | 5 | 4 | `results/k4_gm4_4_pure_sample.log` |
| n = 5, all agents with 3 goods | 2,270,592 | exhaustive | 430,501 | 0 | 0 | `results/k4_gm4_k3cores_5.log` |
| n = 5, pure (4,674 cores) | 93,480,000 | 20,000 random per core | 7,871,760 | 4 | 3 | `results/k4_gm4_5_pure_sample.log` |
| n = 5, one or two 4-good agents (7,203 cores) | 14,406,000 | 2,000 random per core | 2,588,416 | 0 | 0 | `results/k4_gm4_5_n4_12_sample.log` |
| n = 5, three 4-good agents (9,861 cores, genbg) | 19,722,000 | 2,000 random per core | 2,777,846 | 3 | 0 | `results/k4_gm4_5_n4_3_sample.log` |
| n = 5, four 4-good agents (9,846 cores, genbg) | 19,692,000 | 2,000 random per core | 2,179,195 | 1 | 1 | `results/k4_gm4_5_n4_4_sample.log` |

For the random classes, "profiles" are draws with replacement, so a profile may be counted more than once. "No single dump" counts maxima with a nonempty pool, no empty bundle and no source admitting the single dump. "No placement" counts those among them that admit no junk placement either.

*Every* maximum of the profile lacks a placement (GM₄∃ fails): never in these runs. The counter `pallfail` is 0 in every log that has it. `results/k4_gm4_3.log` and `results/k4_gm4_k3cores_5.log` predate the counter, but there `fail` = 0 implies it. This includes the exhaustive run with two 4-good agents: there GM₄ fails at 128 maxima, but every one of the 724,847,616 profiles has a placeable maximum. For pure n = 5 this was checked separately for the 3 failing profiles (`results/k4_gm4_5_pure_check.log`). The per-profile counters `pfail`/`pallfail` in `results/k4_gm4_5_pure_sample.log` are partial, because the base binary was rebuilt with those counters while that run was in progress; its per-maximum counts are complete. GM₄∃ fails only in the targeted search of §6 (instance G, §2.4).

## 5. Structure of maxima (exploration; EVIDENCE)

Found with `k4/gm4_explore.c` (full enumeration) and the plain-Python `k4/gm4_analyze.py` / `k4/gm4_structure.py`. None of this is proved.
- **No empty bundle at n ≤ 3.** At n = 2 and n = 3 no maximum with a nonempty pool has an empty bundle (exhaustive, §4). At n = 4 some do (6,663 of 175,467 in the mixed sample, `results/k4_gm4_h1_4_mixed_sample.log`).
- **H0: a maximum with a nonempty pool is never envy-free.** 0 envy-free ones among 66,023 (n = 3 sample, `results/k4_gm4_h1_3_sample.log`), 25,713 (pure n = 4, `results/k4_gm4_h1_4_pure_sample.log`) and 175,467 (mixed n = 4, `results/k4_gm4_h1_4_mixed_sample.log`). When the envy graph has an edge, a backward walk from it ends at a source that envies someone.
- **H1: every source that envies someone admits the single dump.** True on the n = 3 sample (67,045 envier sources, 0 failures). **False at n = 4**: 100 of 27,914 envier sources fail in the pure sample, 947 of 194,709 in the mixed one. The smallest failure found has n = 4, m = 6 and one 4-good agent (`attempts/k4-gm4-envier-source.md`; instance H of `k4/gm4_counterexample.py`).
- **Selection rules for the dump source** (`results/k4_gm4_structure_4_pure.log`: 65,700 random pure n = 4 profiles; 1,397 maxima with at least two sources, some of which fail):
  - the source with the most reachable agents, or with the most out-edges, always included a working source: all chosen work in 1,382 cases, some in 15;
  - the fewest goods (11 failures), the lowest level (3) and the fewest other agents valuing its goods (14) sometimes chose only failing sources.

  GM₄ˢ is false (§2.3), so every such rule fails somewhere.
- **Champions of failing sources** (same log). The inclusion-minimal envied sets E ⊊ Y_s ∪ U at a failing source s were envied by a non-source in all but 2 of 1,480 (source, champion) pairs.

  For failing sources that value no pool good, the sources from which a champion is reachable were all working sources in 1,272 of 1,274 cases. The counterexamples of §2 are the missing case: a 2-cycle of failing sources whose champions need the same pool good.
- **Near-misses.** Hill-climbing over profiles (`k4/gm4_climb.c`) readily finds states without a single dump at Σℓ = max − 1. All 86 found in one run have a single-agent Pareto improvement (`results/k4_gm4_gap1_4_pure.log`).

  States without a single dump that admit no Pareto improvement at all are rare: 2 in 43,800 random pure n = 4 profiles (`results/k4_gm4_escape_4_pure_sample.log`, `k4/gm4_escape.c -DPSTABLE`). Each is escaped by a 2-agent re-division with one loser, which matches #29's escape study.

## 6. Other potentials (EVIDENCE)

On the six GM₄ profiles A–F the bad maximum tends to be among the more *equal* Σℓ-maxima:
- its level vector is leximin-largest in A and E, and tied for leximin-largest in C, D and F;
- in B it is not: the placeable [4, 5, 5, 6] is leximin-larger than the bad [4, 4, 6, 6];
- it is never the unique largest in Σℓ² or in leximax.

So `k4/gm4_fast.c` has variants:
- tie-breaks among the Σℓ-maxima: `-DTB=1` keeps those with the largest Σℓ², `-DTB=2` the leximax-largest, `-DTB=3` the leximin-largest;
- other potentials maximized instead of Σℓ: `-DW=1` Σℓ², `-DW=2` Σ 2^ℓ, `-DW=3` Σ 16^ℓ. For n < 16 the last orders level vectors exactly like leximax: sorted in decreasing order and compared lexicographically.

Each variant keeps LS4⁺'s soundness and termination. M1, R and X moves raise some levels and lower none, so they raise every such potential, and a coalition move is defined as raising the potential in use. What each variant needs is its own GM statement: "every maximum admits a placement" (GM), or the existence form "some maximum does" (GM∃).

To search where failures are likely, `k4/gm4_run.py --around=… --vary=K` runs a variant on every profile that changes the strict types of K agents of a given profile, exhaustively over those agents' types. The seeds are the seven GM₄ profiles found in the random n = 4 runs (`results/k4_gm4_seeds_4.txt`).

| potential | GM ("every maximum") | GM∃ ("some maximum") | where |
|---|---|---|---|
| Σℓ | false (A–F) | false (G) | 2 agents changed around the seeds: 2,260,332 runs, 2,247,609 distinct profiles; 1,728 distinct profiles with a bad maximum (2,043 runs), 148 with only bad maxima (164 runs), all in one core. 1 agent changed: 6,351 distinct profiles, 147 with a bad maximum, 8 with only bad maxima (`results/k4_gm4_around2_4.log`, `results/k4_gm4_around1_4.log`, `results/k4_gm4_distinct.log`) |
| Σℓ, ties broken by Σℓ², leximax or leximin | false | false (G: unique maximum) | leximin already fails on A and E |
| Σℓ² | false | false (G: its unique Σℓ²-maximum is the same dead end) | |
| Σ 2^ℓ | false (instance P) | **no failure** | 2 agents changed around the seeds: 32 distinct profiles with a bad maximum, none with only bad maxima (`results/k4_gm4_w2_around2_4.log`). 2 agents changed around those 32: 15,925,248 runs, 5,428,320 distinct profiles, 384 distinct profiles with a bad maximum (2,688 runs), none with only bad maxima (`results/k4_gm4_w2_around2b_4.log`). 1 agent changed around the 384: 442,368 runs, 118,656 distinct profiles; the profiles with a bad maximum are exactly the 384 again (5,888 runs), so the search closed (`results/k4_gm4_w2_around1c_4.log`). In all 7,750,832 distinct profiles (`results/k4_gm4_distinct.log`) |
| leximax (Σ 16^ℓ) | false (instance P) | **no failure** | the same counts as Σ 2^ℓ (`results/k4_gm4_w3_around2_4.log`, `results/k4_gm4_w3_around2b_4.log`, `results/k4_gm4_w3_around1c_4.log`). Also 2 agents changed around the 384: 191,102,976 runs, 13,696,128 distinct profiles; the profiles with a bad maximum are exactly the 384 again (33,792 runs), none with only bad maxima (`results/k4_gm4_w3_around2c_4.log`). In all 19,652,066 distinct profiles |
| fixed priority (level vector in agent order, lexicographic; `-DW=4`) | false | false for some agent orders (instance Q: E with order 2, 3, 0, 1) | `k4/gm4_priority.py` over all 24 agent orders: of the 7 seeds, 6 have an order whose maxima are all bad (26 of 168 orders), and so do all 148 profiles of instance-G type (888 of 3,552 orders). No profile had every order bad (`results/k4_gm4_priority_seeds_4.log`, `results/k4_gm4_priority_gmall_4.log`) |

Instance P (pure n = 4, m = 7) makes the "every maximum" forms of Σ 2^ℓ and leximax fail:
- agents 0: {0:1, 2:6, 5:8, 6:4}, 1: {1:1, 4:6, 5:4, 6:8}, 2: {2:4, 3:5, 4:2, 6:8}, 3: {3:5, 4:4, 5:8, 6:2};
- Y = {0, 2} | {1, 4} | {6} | {5}, pool {3}, is a maximum of both and has no placement;
- the other maximum of both, {0, 2} | {6} | {3, 4} | {5}, admits one.

It is checked by `k4/gm4_counterexample.py`.

In random runs over whole classes, the convex potentials never had a maximum without a placement. Only the targeted searches above find one:

| class | profiles | Σ 2^ℓ: maxima with a pool / no single dump / no placement | leximax: the same | logs |
|---|---|---|---|---|
| n = 4, pure, 200,000 random per core | 43,800,000 | 5,957,875 / 1 / 0 | 6,023,613 / 1 / 0 | `results/k4_gm4_w2_4_pure_sample.log`, `results/k4_gm4_w3_4_pure_sample.log` |
| n = 4, one to three 4-good agents, 50,000 per core | 39,150,000 | 6,630,258 / 68 / 0 | 6,678,024 / 68 / 0 | `results/k4_gm4_w2_4_mixed_sample.log`, `results/k4_gm4_w3_4_mixed_sample.log` |
| n = 5, pure, 2,000 per core | 9,348,000 | 1,659,461 / 0 / 0 | 1,678,691 / 0 / 0 | `results/k4_gm4_w2_5_pure_sample.log`, `results/k4_gm4_w3_5_pure_sample.log` |

## 7. Status and open questions

- GM₄, GM₄ˢ and GM₄∃ are false: counterexamples in §2, confirmed by an independent brute force (rows K4.GM.CEX, K4.GM.S, K4.GM.E, REFUTED). So are the variants of §5–6 (K4.GM.VAR). K4.LSP.GM (#29's row, now on main) is marked REFUTED as well, citing K4.GM.CEX, and `k4/ls4plus.md` points here.
- LS4⁺_n with arbitrary choices is not correct (§3). Its default rule has no known failure (K4.LSP.RUN, and §3 here).
- Every potential tried has bad maxima (§6). For Σ 2^ℓ and leximax, some maximum was always placeable in every profile searched (conjecture K4.GM.POT). This is the only statement of the GM kind left that would give TARGET₄, and only as an existence argument.
- The obstruction, at a maximum, is a Hall-type conflict between the champion sets of different sources: two champions need the same pool good, and no one-good source can take that good alone. Theorem C resolves it at k = 3 with a matching. At k = 4 it can survive at every Σℓ-maximum of a profile (instance G). So a proof along these lines must either favor unequal level vectors (the convex potentials of §6) or stop before the conflict arises (LS4⁺'s default rule).
