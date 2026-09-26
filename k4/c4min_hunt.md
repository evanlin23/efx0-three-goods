# Hunting for a counterexample to C₄ᵐⁱⁿ

Workstream `compute/k4-c4min-hunt` (the refuter side; the prover side is `proof/k4-c4min`, PR #41), ledger rows
K4.C4MINH.* (EVIDENCE only). Target: conjecture C₄ᵐⁱⁿ of `k4/c4x.md` §5 (PR #36, branch `proof/k4-c4x`, row
K4.C4X.MIN there): for every strict profile of every k = 4 core, some valid pre-allocation in 𝒫 with the fewest frozen
agents has deficit ≤ 0 (is removal-only completable, with the owner's needs from its bundle).

**Status. No counterexample to C₄ᵐⁱⁿ found.** Everything here is EVIDENCE (one exact implementation per exhaustive
class, no stored certificates; random and local search elsewhere). Nothing here changes K4.D or K4.T.
- **Exhaustive** (§2): C₄ᵐⁱⁿ holds on every strict profile of every k = 4 core with n ≤ 4 (with PR #36's runs), with
  n = 5 and at most three 4-good agents, and with n = 6 and one 4-good agent: about 6.6·10¹² profiles, 0 failures.
- **Adversarial** (§3): hill-climbing toward "an owner is needed and the best min-frozen pre-allocation has positive
  deficit" on all 14,520 n = 5 cores with four or five 4-good agents (three objective orders, 13 restarts per core,
  then 20 more on the 400 tightest), 1,600 random cores with n = 6–8, glued pairs of small cores, and from the hard
  profiles of PR #36 and PR #30: the least deficit d* reaches 0 on many cores and never 1.
- **Structured families** (§4): H_t of `k4/c4.md` §7 with §7's values up to t = 16 and about 24,000 random and
  perturbed profiles of H_4–H_10, gadget chains, cycles, trees and grids (n up to 68, exact test, SAT for the large
  ones); owner-rigid and tight gadgets glued in pairs (3.6 million glued profiles) and in chains, cycles and stars of
  up to five (4,000): 0 failures.
- **The weaker forms** (some min-frozen P completable with any deficit; K4.D by SAT) were never needed: C₄ᵐⁱⁿ itself
  held everywhere. **A stronger form fails** (§5): with the owner's needs from its base instead of its bundle, beyond
  PR #36's n = 2 cases, on 26,496 pure n = 4 profiles (smallest m = 8), confirmed by three implementations; C₄ᵐⁱⁿ holds
  on all of them, so its bundle needs are essential.
- Not done: n = 5 with four or five 4-good agents exhaustively (4·10¹⁴ and 9·10¹⁵ profiles; only two order-type
  classes per agent, §2.1, running when this was written) and anything exhaustive with n ≥ 6 beyond one 4-good agent.

## 1. Definitions and tools

Notation of `k4/c4x.md` §1 and `k4/lb4.md` §1. For one strict profile of a k = 4 core:
- 𝒫: bases B_i ⊆ R_i with |B_i| ≤ 2, pairwise disjoint; needs N_i = {g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)}; valid iff
  every good of NA = ⋃ N_i is the whole base of one agent; frozen agents F (a one-good base in NA), |F| = |NA|;
  cap(i) = 0 for frozen i, else 2 − |B_i|; S = Σ cap; J = the goods in no base.
- def(P) = |J| − S if that is ≤ 0; otherwise the least |C| − S_o(C) over free owners o and C ⊆ J such that
  X_o = B_o ∪ (J ∖ C) threatens no j ≠ o holding B_j alone (max_{h ∈ X_o} v_j(X_o ∖ h) > v_j(B_j)), S_o(C) the slots of
  the agents other than o with frozen status recomputed from the owner's needs N_o^X = {g ∈ R_o ∖ X_o : v_o(g) >
  v_o(X_o)} (variant `-w0`: from its base, S_o = S − cap(o)); +∞ if no (o, C) works.
- f* = the least |F| over 𝒫; d* = the least def over the P ∈ 𝒫 with |F| = f*. **C₄ᵐⁱⁿ holds at the profile iff
  d* ≤ 0.** Since |J| − S = |F| − σ (σ = 2n − m), every min-frozen P has def = f* − σ ≤ 0 when f* ≤ σ: C₄ᵐⁱⁿ can only
  fail where f* > σ ("an owner is needed").
- Weaker forms tracked: (W1) some min-frozen P is completable (exact test, any deficit; `k4/c4x.md` §1's
  "completable"); (W2) K4.D (an EFX₀ allocation with at most one bundle of more than two goods).

Tools (all in `k4/`):
- `c4min_hunt.c`: an exact C₄ᵐⁱⁿ test written from the definitions above; it shares no code with `k4/c4x.c`.
  - Valid pre-allocations are enumerated by a depth-first search with |NA| bounded (static agent order for n ≤ 6,
    dynamic most-constrained-agent order above); f* by branch and bound; then the pre-allocations with |F| = f* are
    enumerated until one has deficit ≤ 0.
  - The deficit is a branch and bound over C: at a node, a threatened agent j is chosen and one branches on the
    nonempty sets D of junk goods of X_o ∩ R_j to move into C (or on making X_o ⊆ R_j). Every threat-free C* contains
    a leaf of this search, and |C| − S_o(C) only grows with C (S_o is non-increasing in C), so the least leaf value is
    the deficit. `-D` replaces it by the plain enumeration of every C ⊆ J; both agree on every profile tested (below).
  - Exhaustive mode (`-E`): the profiles are processed in *slices* (all types of the last agent L at once, as a
    bitmask). A certificate (P, owner o, C) found by the exact search at one profile is turned into a *template*: the
    base options, the need sets of every agent, o and C. Its validity at another profile depends on each agent's type
    only through per-agent conditions: agent i's need set for its base option (so validity, NA, F and S are
    unchanged), "j is not threatened by X_o" for j ≠ o, the owner's slot count S_o(C) (through o's type), and, when
    the template has f > σ frozen agents, f*(profile) ≥ f (computed per slice as a mask: the types of L for which some
    valid P has |NA| ≤ f − 1). Each of these is a mask over L's types, so one template covers many profiles at
    once; templates are cached across slices. A profile is either covered by a template whose conditions hold there
    (so C₄ᵐⁱⁿ holds there) or solved exactly; failures are printed. `-V` re-solves every profile from scratch and
    stops at the first disagreement with the masks.
  - `-1` (one profile: f*, d*, counts, (W1)), `-1q` (f*, holds, a certificate), `-R` (random profiles), `-H`
    (hill-climbing, §3).
- `c4min_brute.py`: a brute-force referee written from the definitions, sharing no code with the C tools or with
  PR #36's `k4/c4x_check.py`: every tuple of bases (itertools), deficits over every C ⊆ J with threats computed
  literally (every h ∈ X_o), completability by every map of the junk goods to agents with (OC₄) checked literally and
  every completion re-checked EFX₀ by the raw definition; K4.D by every allocation; and `verify_certificate` (a
  certificate (bases, owner, C) re-checked literally, the completion built and checked EFX₀).
- `c4min_crosscheck.py` (the three implementations profile by profile), `c4min_hunt_run.py` (exhaustive runs over the
  certificate files of K4.R3–R5c), `c4min_climb.py` (climbing), `c4min_sample.py` (random profiles on families),
  `c4min_families.py` (H_t and other gadget families; random cores), `c4min_common.py`.

### 1.1 Validation of the tools

- **Against PR #36's exhaustive runs** (`k4/c4x.c`): the exhaustive mode finds 0 failures of C₄ᵐⁱⁿ on every strict profile
  with n ≤ 3 (189,216 + 299,837,376) and n = 4 with one or two 4-good agents (7,247,232 + 724,847,616), the same
  profile counts and the same result as `results/k4_c4x_n3.log`, `k4_c4x_n4_1.log`, `k4_c4x_n4_2.log`.
- **A variant that does fail**: with the owner's needs from its base (`-w0`), the exhaustive mode finds exactly 720
  failing profiles at n = 2, the number `k4/c4x.c -w0 -R` gives (`results/k4_c4x_variants.log` of PR #36), and none
  with n = 3 or n = 4 with at most two 4-good agents (`results/k4_c4min_hunt_w0.log`). So failures are found when
  they exist, and the owner's needs from its bundle are needed only at n = 2 among these classes.
- **Self-check of the masks** (`-V`: after each slice, every profile is re-solved from scratch by the exact search and
  compared with the result of the masks; `results/k4_c4min_hunt_selfcheck.log`): all 1,032,121,440 profiles with
  n ≤ 3 or n = 4 with at most two 4-good agents, 200,060,928 profiles of 12 pure n = 4 cores (the first type of the
  first agent) and 95,551,488 profiles of 40 n = 5 cores with three 4-good agents: 0 disagreements.
- **Per profile, three implementations** (`k4/c4min_crosscheck.py`, `results/k4_c4min_hunt_crosscheck.log`): on random
  profiles of every class with n ≤ 5, `c4min_hunt.c -1` against `k4/c4x.c -1s -R -a` (f*, d*, the numbers of valid,
  min-frozen and good pre-allocations) and, for n ≤ 4 and m ≤ 8, against the brute force (the same, and (W1)); and
  `c4min_hunt.c` against itself with the plain enumeration of C (`-D`) and with static and dynamic agent orders
  (`-Y0`, `-Y1`), on all outputs including a checksum of the deficits of all valid pre-allocations: 4,254 random
  profiles (n = 2–5, both owner-needs conventions), 2,606 of them also against the brute force, 0 mismatches.
- **The SAT encoding** (`k4/c4min_sat.py`, §4) against `c4min_hunt.c` (`k4/c4min_satcheck.py`,
  `results/k4_c4min_hunt_satcheck.log`): f*, whether C₄ᵐⁱⁿ holds, d*, and, where an owner is needed, the exact set of
  agents that can be the owner (`c4min_hunt.c -1o`), on 1,353 random profiles (n = 3–8; 445 with an owner needed):
  0 mismatches.
- The brute force is also the referee of certificates on large instances: `verify_certificate` rebuilds the completion
  from (bases, owner, C) and checks it EFX₀ by the raw definition; used on samples of every family in §4.

## 2. Exhaustive checks

`k4/c4min_hunt.c -E` through `k4/c4min_hunt_run.py`, on the core lists of the K4.R* certificates (every connected k = 4
core of the class, up to isomorphism; `k4/check4.py` checks that the lists are complete), every strict profile (the
strict balanced types of `k4/check4.py`, 288 per 4-good agent, 144 with two private goods, 6 per 3-good agent).

| class | cores | strict profiles | C₄ᵐⁱⁿ fails | wall time (4 CPUs) | log |
|---|---|---|---|---|---|
| n = 4, three 4-good agents | 339 | 34,971,844,608 | 0 | 30 s | `results/k4_c4min_hunt_n4_3.log` |
| n = 4, pure (four 4-good agents) | 219 | 1,022,496,473,088 | 0 | ≈ 22 min | `results/k4_c4min_hunt_n4_pure.log` |
| n = 5, one 4-good agent | 1,735 | 574,615,296 | 0 | < 1 min | `results/k4_c4min_hunt_n5_12.log` |
| n = 5, two 4-good agents | 5,468 | 80,025,864,192 | 0 | ≈ 2 min | the same |
| n = 5, three 4-good agents | 9,861 | 6,423,281,565,696 | 0 | 2 h 17 min (3 jobs) | `results/k4_c4min_hunt_n5_3.log` |
| n = 6, one 4-good agent | 26,866 | 54,698,374,656 | 0 | 8 min (3 jobs) | `results/k4_c4min_hunt_n6_1.log` |

With PR #36's exhaustive runs (n ≤ 3; n = 4 with one or two 4-good agents; `k4/c4x.c`), which this tool reproduces
(§1.1), **C₄ᵐⁱⁿ holds on every strict profile of every k = 4 core with n ≤ 4, and with n = 5 and at most three 4-good
agents, and with n = 6 and one 4-good agent** (about 6.6·10¹² profiles in all). A counterexample, if any, has n ≥ 5, and at n = 5 four or five 4-good
agents (the classes of §3's climbing and of §2.1's restricted runs). Each row is one
implementation (`k4/c4min_hunt.c`), so the status is EVIDENCE; the certificates (templates) are not stored.

### 2.1 n = 5 with four or five 4-good agents, two order-type classes

`results/k4_c4min_hunt_classes.log` (resumable: `.ckpt` per class pair). Every 4-good agent restricted to the 48
strict types of two order-type classes (`k4/c4min_common.py` `type_class`; the rest of the profile space is only
climbed, §3): classes 10, 11 (a > b + c, the kind of G1 in `k4/c4x.md` §5 and of the `-w0` counterexample of §5) and
classes 0, 1 (flat, a < c + d, G4). 3-good agents keep all their types.

| class pair | cores | profiles | C₄ᵐⁱⁿ fails |
|---|---|---|---|
| 10, 11 (a > b + c), n = 5 with four 4-good agents | 9,846 | 223,148,556,288 | 0 |
| 0, 1 (flat), n = 5 with four 4-good agents | 9,846 | 223,148,556,288 | 0 |
| 10, 11 and 0, 1, pure n = 5 | 4,674 | (running; about 1.2·10¹² profiles each, several hours) | |

## 3. Adversarial search

**Climber** (`k4/c4min_hunt.c -H`, driver `k4/c4min_climb.py`). A profile is scored lexicographically by
(an owner is needed (f* > σ), d*, −good), good = the number of min-frozen P with deficit ≤ 0 (C₄ᵐⁱⁿ fails iff good = 0
iff d* > 0). The first key matters: where f* ≤ σ every min-frozen P has deficit f* − σ ≤ 0, and an objective without it
drifts to such trivially tight profiles (d* = 0 with one witness). Moves re-type one agent (or two, with probability
1/4) at random; a move is kept if the score does not drop; a restart ends after 400 moves without a strict
improvement. Every profile with d* > 0 would be printed (CEX) and re-evaluated by `k4/c4x.c` and the brute force.

**n = 5 with four or five 4-good agents** (`results/k4_c4min_hunt_climb_n5_45.log`): every one of the 14,520 cores
(9,846 with four, 4,674 pure), 3 restarts of up to 3,000 moves each (≈ 2.4 million evaluations, 11 min on one CPU).
No profile with d* > 0. Best score per core:

| owner needed at the best profile | d* = 0 | d* = −1 | d* = −2 |
|---|---|---|---|
| yes (13,560 cores) | 1,860 (26 of them with exactly two witnesses, none with one) | 11,563 (3,802 with exactly one witness) | 137 |
| not reached (960 cores; on a core with m ≤ n it never is, since f* ≤ n ≤ σ) | 850 | 105 | 5 |

So on 1,860 cores the climber reaches profiles where an owner is needed and the best witness has no slack at all
(d* = 0), and on 3,802 cores profiles with a single witness; none goes further.

**Second n = 5 campaign** (`results/k4_c4min_hunt_climb_n5_b.log`; per-core bests in `…_climb_n5_b.jsonl.gz`): the
same 14,520 cores with the order (−good, d*) and 6 restarts, then with (owner needed, f*, −good, d*), annealing (3%)
and 4 restarts of up to 4,000 moves, and PR #30's eight GM₄ profiles as starting points (20 restarts of up to 20,000
moves): no profile with d* > 0 (d* = 0 on 227 and 193 cores). **The 400 tightest cores** of this campaign (an owner
needed; highest d*, then fewest witnesses: from d* = 0 with two witnesses to d* = −1 with one) re-climbed with 20
annealed restarts of up to 10,000 moves each (`results/k4_c4min_hunt_climb_tight.log`): d* = 0 on 222, never above.

**Profiles where simpler potentials fail** (`results/k4_c4min_hunt_attempts.log`): the 11 distinct profiles of PR
#36's `attempts/k4-c4x-*.md` (n ≤ 4) and PR #30's eight n = 5 GM₄ profiles (`k4/gm4.md`,
`results/k4_c4min_hunt_seeds_gm4.json`): C₄ᵐⁱⁿ holds on all 19 (d* between −2 and 0), and the brute force agrees on
every n ≤ 4 one. (The n ≤ 4 ones are inside §2's exhaustive runs anyway.)

**Random connected cores, n = 6–8** (`results/k4_c4min_hunt_climb_rand.log`; `k4/c4min_families.random_core`, uniform
random good sets accepted by `k4/check4.py`'s `is_core`): 60 cores for each of (n, m, number of 4-good agents) =
(6, 9, 3), (6, 12, 4), (6, 14, 6), (6, 16, 6), (7, 12, 4), (7, 15, 7), (7, 18, 7), (8, 14, 5), (8, 17, 8), (8, 20, 8),
two restarts each: no profile with d* > 0; an owner is needed at the best profile of 570 of the 600 cores, and 117 of
them reach d* = 0. A second pass (100 other cores per class, order (−good, d*), annealing: a worse move is kept with
probability 3%, three restarts of up to 3,000 moves): no profile with d* > 0; an owner is needed at the best profile of
755 of the 1,000 cores, 11 reach d* = 0.

**Glued cores** (`results/k4_c4min_hunt_climb_glue.log`): 40 random pairs for each of (n = 3 core, n = 3 core),
(n = 3, pure n = 4), (pure n = 4, pure n = 4), (n = 3, n = 4 with three 4-good agents), each joined in three ways (a
good of one identified with a good of the other; a 4-good connector agent {a, b, p, q} with two private goods; a
3-good connector {a, b, p}), n = 6–9, climbed with two restarts: no profile with d* > 0 (best d* = 0 on a few).

**Owner-rigid gadgets glued in pairs** (`k4/c4min_rigid.py`, `results/k4_c4min_hunt_rigid.log`). A profile is
owner-rigid if an owner is needed and exactly one agent can be it (`c4min_hunt.c -1o`: the least deficit over the
min-frozen P when only o may own). With one owner for the whole instance, a gadget whose excess junk only its own
owner can absorb must be protected through slots instead; two such gadgets with different owners are the natural
candidate for a failure that no small core shows. 83 owner-rigid profiles among 20,400 random profiles of the 51 n = 3
cores, 4 among 33,480 of the n = 4 cores with three or four 4-good agents. 230 random pairs, glued in every way: every
pair of goods identified (12,230 profiles), or a connector agent on every pair of goods with every one of its types
(1,761,120 profiles, exhaustive over the connector's type with `-E`): **0 failures**. The same with the 420 tightest
n = 5 profiles of the second campaign as gadgets (an owner needed, d* = 0; 200 random pairs, n = 10–11): 12,808 merged
and 1,844,352 connected profiles, 0 failures.

**Chains, cycles and stars of tight gadgets** (`k4/c4min_chains.py`, `results/k4_c4min_hunt_chains.log`): 4,000
composites of 2–5 of those 420 gadgets (random with repetition), joined along a path, a cycle or a star by shared goods
or connector agents with random types (n up to about 30), each checked with the SAT encoding: 0 failures.

## 4. Structured families

Families of `k4/c4min_families.py`, all pure (every agent has four goods) except the heads:
- `ht T`: H_T of `k4/c4.md` §7 (PR #33), n = 4T + 1, m = 10T + 3: a head ℓ = {g_1, z, u, u′} and T gadgets of three
  x_{j,i} = {a_{j,i}, b_{j,i}, c_{j,i}, g_j} and y_j = {a_{j,1}, a_{j,2}, a_{j,3}, e_j}, e_j = g_{j+1}, e_T = z; §7's values
  (8, 6, 5, 4) for ℓ and (8, 6, 4, 3) for every x and y. (`k4/d_stress.py`'s `cycle T` of PR #42 is H_T again, with
  its head's z renamed w.)
- `ht2 T`: two x's per gadget, y_j = {a_{j,1}, a_{j,2}, p_j, e_j} with p_j private; `htx T`: the x's of a gadget share
  their lower goods around the gadget, x_{j,i} = {a_{j,i}, b_{j,i}, b_{j,i+1}, g_j} (no private goods); `htc T`: T
  gadgets in a cycle without a head (e_T = g_1).
- From `k4/d_stress.py` (PR #42, loaded from its branch): `chain T H` (H heads, each starting a chain of T gadgets),
  `tree T` (gadgets in a binary tree, a second child joined by a head-like agent); and `grid R C` here (R rows of C
  gadgets, one 4-good agent joining consecutive rows).

**Exact test per profile with `k4/c4min_hunt.c -R`** (`results/k4_c4min_hunt_families.log`; 20 certificates per family
re-checked literally by the brute force, `verify_certificate`): 400 uniform random profiles each of H_4, H_5, ht2 4,
htx 4, htc 4, grid 2×2, chain 2 2, tree 4 (and cycle 4 = H_4); and 400 profiles each of H_4, H_5, htc 4 at §7's values
with 1, 2, 4 or 8 agents re-typed at random. **0 failures** (8,400 profiles); an owner is needed in all of them except
htx 4 (m = 31 < 2n). f* reaches 4 on random profiles; near §7's values it is almost always 0. The exact search of
`c4min_hunt.c` has a heavy tail on H_6 (one profile needed 18 s to prove f* = 2), so larger instances use the SAT
encoding.

**SAT encoding** (`k4/c4min_sat.py`, `results/k4_c4min_hunt_famsat.log`; every certificate re-checked by the brute force):
- §7's values on H_T for every T = 1, …, 16 (up to n = 65, m = 163): C₄ᵐⁱⁿ holds, f* = 0, in under a second each.
- 300 uniform random profiles each of H_6, H_8, H_10, ht2 8, htx 8, htc 8, grid 3×3 (n = 39), chain 3 2, chain 4 3
  (n = 51), cycle 8 (= H_8), tree 7 and tree 15 (n = 68, m = 167): 0 failures; f* up to 8 (tree 15).
- 300 profiles each of H_6, H_8, H_10 and htc 8 at §7's values with 1, 2, 4, 8 or 16 agents re-typed: 0 failures
  (6,000 profiles; f* ≤ 2).
- In all, 9,609 SAT-checked profiles of the large families, 0 failures, every certificate re-checked literally.

- The grids of §5 (`lt R C`: agent (i, j) = the three lower goods of row i and the top of column j; `ltp R C`: one
  private good instead of the third lower good), with the types of the `-w0` counterexample (lower goods 2, 3, 4, top 8)
  for R, C ≤ 5 and 300 uniform or perturbed profiles each of seven of them: 6,312 profiles, 0 failures. Without private
  goods these grids need no owner beyond 2 × 2 (σ grows with the grid).

**SAT hill-climbing** (`c4min_sat.py --climb`, `results/k4_c4min_hunt_climbsat.log`; score (an owner is needed, d*,
fewest owners o with a min-frozen P of deficit ≤ 0 under o), 3 restarts on each of H_3, H_4, H_5, htc 4, htx 4,
ht2 4, grid 2×2, tree 4, cycle 4, chain 2 2): best d* between −3 and −1, with 13 to 21 feasible owners out of
13 to 21 agents. These families are far from failing: random profiles have millions of witnesses (`c4min_hunt.c`
counts 361,584 min-frozen pre-allocations with deficit ≤ 0 on one random profile of H_4), and the climber cannot
bring d* above −1.

## 5. The strengthening with the owner's needs from its base fails beyond n = 2

`k4/c4x.md` takes the owner's needs from its bundle; PR #36 (`attempts/k4-c4x-variant-spaces.md`) showed that the
needs from the base fail at n = 2. The exhaustive runs with `-w0` (`results/k4_c4min_hunt_w0.log`) find no other failure
with n = 3, n = 4 with one to three 4-good agents, or n = 5 with one or two, but **26,496 failing profiles in 14 pure
n = 4 cores** (m = 8–12). The smallest: pure n = 4, m = 8, agents {0, 2, 4, 6}, {0, 2, 5, 6}, {1, 3, 4, 7},
{1, 3, 5, 7}, each with values (2, 3, 8, 4), a > b + c; its 36 min-frozen pre-allocations all have deficit ≥ 1 from
the base needs and none is completable, while 32 have deficit ≤ 0 from the bundle needs. The failure counts are
multiples of 6⁴: only each agent's top good and its kind (a > b + c) matter. Confirmed by the brute force,
`k4/c4min_hunt.c` and `k4/c4x.c` (`attempts/k4-c4min-w0-owner-base.md`, `attempts/k4_c4min_w0_replay.py`). So a
proof of C₄ᵐⁱⁿ has to use the unfreezing that the owner's bundle needs allow, already at n = 4.

## 6. Reproduce

Every log starts with its command, the commit and the sha1 of `k4/c4min_hunt.c`. `k4/c4min_hunt_runs.sh SECTION`
(run from the repository root; `JOBS=k` sets the parallelism) writes them:

| section | what | log(s) | time (4 CPUs) |
|---|---|---|---|
| `n4` | exhaustive, n = 4 with three and four 4-good agents | `k4_c4min_hunt_n4_3.log`, `k4_c4min_hunt_n4_pure.log` | 25 min |
| `n5a`, `n5b`, `n6a` | exhaustive, n = 5 with one/two and three 4-good agents, n = 6 with one | `k4_c4min_hunt_n5_12.log`, `k4_c4min_hunt_n5_3.log`, `k4_c4min_hunt_n6_1.log` | 3 min, 2.3 h, 8 min |
| `classes` | exhaustive, n = 5 with four or five 4-good agents restricted to two order-type classes | `k4_c4min_hunt_classes.log` | ≈ 8 h |
| `selfcheck`, `crosscheck`, `satcheck` | validation (§1.1) | `k4_c4min_hunt_selfcheck.log`, `k4_c4min_hunt_crosscheck.log`, `k4_c4min_hunt_satcheck.log` | 5 min, 20 min (one CPU), 1 min |
| `w0small`, `w0big` | the `-w0` strengthening (§5) | `k4_c4min_hunt_w0.log` | 30 min |
| `attempts` | the hard profiles of PR #36 and PR #30 | `k4_c4min_hunt_attempts.log` | seconds |
| `climb5`, `climb5b`, `climbtight` | climbing on n = 5 (§3) | `k4_c4min_hunt_climb_n5_45.log`, `k4_c4min_hunt_climb_n5_b.log` (+ `.jsonl.gz`), `k4_c4min_hunt_climb_tight.log` | 11 min (one CPU), 25 min, 10 min |
| `climbrand`, `climbrand2`, `climbglue`, `climbfam` | climbing on random, glued and family cores | `k4_c4min_hunt_climb_rand.log`, `k4_c4min_hunt_climb_glue.log`, `k4_c4min_hunt_climb_fam.log` | about 1 h (one CPU) |
| `rigid`, `rigid5`, `chains` | glued gadgets (§3) | `k4_c4min_hunt_rigid.log`, `k4_c4min_hunt_chains.log` | minutes |
| `families`, `famsat`, `famlt`, `climbsat` | structured families (§4) | `k4_c4min_hunt_families.log`, `k4_c4min_hunt_famsat.log`, `k4_c4min_hunt_climbsat.log` | about 1 h |

`climbtight`, `rigid5` and `chains` read `results/k4_c4min_hunt_climb_n5_b.jsonl`, which is committed gzipped
(`gunzip -k results/k4_c4min_hunt_climb_n5_b.jsonl.gz` first); `climbtight` writes the 400 cores it climbs to
`results/k4_c4min_hunt_tight_n5.jsonl`. The `-w0` replay: `python3 attempts/k4_c4min_w0_replay.py`. The tools need
python-sat (SAT encoding), gcc, and `k4/c4x.c` of PR #36 for the cross-checks (read from `origin/proof/k4-c4x` with
`git show` until that PR is merged). Several logs carry a note that the wrapper shell was stopped and a watcher wrote
the last line: `k4_c4min_hunt_runs.sh` had been edited in place while it ran (bash reads scripts incrementally), which
also made one shell run a garbled `climbglue` fragment once (its output was discarded); the Python runs themselves were
not affected.
