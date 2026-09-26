# Adaptive insertion for LB₄ʳ

Workstream `proof/k4-adaptive` (ledger open item 18; rows K4.AD.*). Notation as in `k4/lb4.md` (LB₄, LB₄ʳ, §1–§2, §5)
and `k4/c4.md` (PR #33: exposure, Theorems A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺, the cores H_t of §7, Proposition H). Tools:
`k4/adaptive.c` (LB₄ʳ with a swappable insertion rule), `k4/adaptive_run.py` (driver), `k4/adaptive_H.py` (H_t and
relabeled copies), `k4/adaptive_verify_H.py` (Proposition H′ in PR #33's independent model), `k4/adaptive_mine.py`,
`k4/adaptive_crosscheck.py`, `k4/adaptive_lb4check.py`, `k4/adaptive_uncovered.py`, `k4/adaptive_matching_ties.py`,
`k4/adaptive_gm4_profiles.py`; logs `results/k4_adaptive_*`.

**The question.** LB₄ʳ with a fixed insertion order needs unboundedly many nested rotations: on H_t, index order needs
⌈2t/3⌉ (Proposition H), and a relabeled H_5 defeats every fixed order (`k4/c4.md` §7). Is there a polynomial-time
*adaptive* insertion rule, choosing the next agent from the state and the valuations, with which LB₄ʳ never fails with
at most R nested rotations, R as small as possible?

**Status.**
- **Rule F** (§1): choose the *first* agent by lookahead, then insert in index order. With at most **R = 1** rotation
  it fails on no profile tested: every strict profile of every certified core with n ≤ 4 and at most three 4-good agents
  (exhaustive, 3.6·10¹⁰ profiles), pure n = 4 (4,380,000 random profiles and 1,095,000 hill-climbing steps; the
  exhaustive run did not finish),
  1.6·10⁸ random profiles over the five n = 5 classes, hill-climbing towards profiles that need two
  rotations on #32's hard and random cores up to n = 8, #30's GM₄ profiles, and H_1–H_8 with relabelings (47 of 48
  runs finished, none needing a rotation; the 48th is covered by Proposition H′) (§2). R = 1
  is the least possible: 263,336 profiles at n = 3 need a rotation under every insertion order (`attempts/lb4-no-rotation.md`).
- **Rule F is optimal where it was compared** (§4): on every profile with n ≤ 4 and at most three 4-good agents, the
  fewest rotations of rule F equal the fewest over *all* insertion sequences. More: some first agent makes *every*
  continuation work with that fewest number (n ≤ 3, and n = 4 with one or two 4-good agents; conjecture
  **K4.AD.C1**, "Theorem C₄ after the first insertion").
- **Proved (written proof, §3, refereed in the #44 review; checked in an independent model for t ≤ 5): Proposition H′.** On H_t, for
  every t, every run of Phase 1 in which an agent of gadget 1 is processed before ℓ gives LB₄ʳ an allocation with **no
  rotation** (need-shrinking upgrades, owner r). So on every relabeling of H_t rule F needs no rotation: adaptivity at
  a single step removes #33's obstruction.
- **Cheaper rules fail with one rotation** (§5, `attempts/k4-adaptive-*.md`): lookahead on ω or on the needed-alone
  set, static features (4-good first, 3-good first, least or most contested top), c4one's key: each needs two rotations
  at n = 3, m = 6 (confirmed in the independent model).
- **The theorems of #33 and #37 do not reach the multi-4-good case** (§6): with two or more 4-good agents some
  profiles have no insertion sequence whose run they cover (12,420 of 189,216 at n = 2). LB₄ʳ solves all of them, at
  n ≤ 3 with no rotation, mostly by need-shrinking upgrades, which those theorems do not treat. **Theorem A₄⁺ᴺ** (§6,
  written proof, found correct in the #44 review; 0 violations against the exact owner test on every run and every
  owner it admits) extends #37's count to need-shrinking upgrades and reduces the uncovered profiles (n = 2: 12,420 →
  1,020; n = 3: 7,503,039 → 119,616; n = 4 with two 4-good agents: 155,947 → 62,536). Most of the rest (300, 90,336
  and 30,024) LB₄ʳ solves with the owner's needs from its base and no rotation, so there the gap is in the counting;
  the others need one rotation with the needs from the base, and the owner's needs from its bundle avoid it at n ≤ 3
  and on 1,200 profiles at n = 4 (§6).

Nothing here changes K4.D or K4.T. Rows K4.AD.* are CONJECTURE or EVIDENCE.

**Related work** (as of this revision). #36 (merged) states C₄ᵐⁱⁿ (`k4/c4x.md`, conjecture K4.C4X.MIN): some valid
pre-allocation with the fewest frozen agents is completable. #41 (`proof/k4-c4min`, open) proves it, in its Theorem Z,
on every profile whose fewest frozen agents is 0, which covers every H_t; Theorem Z is machine-checked on main
(#49, row K4.C4MIN.Z.LEAN), and #46 (merged, `k4/hall.md`) gives H_t a removal-only completable pre-allocation without
frozen agent (K4.HALL.HT). Proposition H′ is the algorithmic counterpart: LB₄ʳ with a chosen first agent reaches a
state with no frozen agent. #52 (merged, `k4/hall_bt.md`) treats the exposed frozen agents that remain. #43
(`proof/k4-induct`, open, induction on the number of 4-good agents) and #40 (merged, `compute/k4-nsw`, unbounded
rotations guided by Nash welfare) attack the multi-4-good gap by other routes. Read from their descriptions and ledger
rows only.

## 1. The rules

`k4/adaptive.c` computes an insertion sequence τ with the rule, then runs LB₄ʳ(τ) (`k4/lb4.md` §5: Phase 1(τ) with LB's
P-step key; the three upgrade policies; the owner step, owner's needs from its bundle; nested rotations along need
chains, chains may end at upgraded agents; `lb4.c -u3 -w1 -c1`) with the rotation bound outermost (every policy at
bound 0, then at bound 1, …; `lb4.c -d2`), so a success reports the fewest rotations over the policies. It matches
`lb4.c -i0/-i1 -u3 -o0 -r3 -d2 -w1 -c1` of #32 on every core with n ≤ 3, per core, for index order and for every order:
same profile counts, rotation and policy histograms on all 56 cores (`k4/adaptive_lb4check.py`,
`results/k4_adaptive_lb4check.log`; n = 3, index order: 289,807,786 / 10,017,550 / 12,040 profiles needing 0 / 1 / 2
rotations; every order: 982,611,638 / 22,021,602 / 25,240 runs).

**Rule F (`-A16`).** For b = 0, 1, …, R: for each agent a in index order, let τ_a = (a, then index order at every later
insertion step); if LB₄ʳ(τ_a) succeeds with at most b rotations, use τ_a. It runs LB₄ʳ at most n(R + 1) times.

Variants with the same success set on every class tested (§2): `-A15` (the index run, or the index run with one
insertion step changed: #37's Lemma X′ family); `-A12`, `-A14` (the same families, choosing by (rotations, ω); `-A14`
also on n = 4 with three 4-good agents, `results/k4_adaptive_A14_n4_3.log`);
`-A3` (at every insertion step, the candidate whose continuation in index order needs the fewest rotations: a
rollout, never worse than index order). `-A24` (statistics): the first agent minimizing the *largest* number of
rotations over every continuation. `-i2`: the fewest rotations over every insertion sequence.

**Polynomial time.** Rule F adds a factor n(R + 1) to LB₄ʳ. LB₄ʳ itself, as defined and implemented, is not
polynomial: its owner step searches the slot sets C exactly (`k4/adaptive.c` prunes that search without changing its
result, which makes H_t up to t = 8 feasible), and its rotation search follows need chains. Rule F is polynomial given
LB₄ʳ; making the whole algorithm polynomial means replacing the exact owner search by a polynomial test, for example
the counting conditions of the theorems, which do not reach the multi-4-good case (§6). The cheap rules of §5 (ω or
|NA| lookahead: a few Phase 1 runs per step) are polynomial but need two rotations.

## 2. Evidence (`k4/adaptive_run.py`, `k4/adaptive_H.py`; single implementation, every output checked against the raw EFX₀ definition)

Rule F with at most three rotations allowed, counting the fewest each profile needs (`-A16 -r3`):

| class | profiles | 0 rotations | 1 rotation | 2 or more | log |
|---|---|---|---|---|---|
| n = 2, exhaustive | 189,216 | 189,216 | 0 | 0 | `results/k4_adaptive_rules_n23.log` |
| n = 3, exhaustive | 299,837,376 | 299,574,040 | 263,336 | 0 | `results/k4_adaptive_rules_n23.log` |
| n = 4, one 4-good agent, exhaustive | 7,247,232 | 7,246,416 | 816 | 0 | `results/k4_adaptive_rules_n4.log` |
| n = 4, two, exhaustive | 724,847,616 | 724,640,736 | 206,880 | 0 | `results/k4_adaptive_rules_n4.log` |
| n = 4, three, exhaustive | 34,971,844,608 | 34,961,492,780 | 10,351,828 | 0 | `results/k4_adaptive_A16_n4_3.log` |
| n = 4, pure, random (20,000 per core) | 4,380,000 | 4,378,184 | 1,816 | 0 | `results/k4_adaptive_A16_pure4.log` |
| n = 5, one 4-good agent, random (5,000 per core) | 8,675,000 | 8,674,942 | 58 | 0 | `results/k4_adaptive_A16_n5_sample.log` |
| n = 5, two, random | 27,340,000 | 27,339,644 | 356 | 0 | same |
| n = 5, three, random | 49,305,000 | 49,303,628 | 1,372 | 0 | same |
| n = 5, four, random | 49,230,000 | 49,226,628 | 3,372 | 0 | same |
| n = 5, pure, random | 23,370,000 | 23,365,955 | 4,045 | 0 | same |

Adversarial and structured sets:
- *Hill-climbing against rule F* (`-H`, score: rotations needed, then policy, then rotation attempts; change one
  agent's type, undo a change that makes the profile easier, restart every 500 steps) on #32's core lists
  (`results/k4_lb4r_cores_*.json.gz`): the two cores where need-shrinking needs three rotations, the 276 and 396 cores
  where weaker variants fail (n ≤ 5), 5,000 cores grown from them (n = 4 to 7), and 6,000 random cores with n = 6, 7, 8:
  24,022,000 profiles, none needing two rotations (`results/k4_adaptive_hill.log`).
- *Hill-climbing on pure n = 4* (the 219 certified cores, 5,000 steps each, 1,095,000 profiles): none needing two
  rotations (`results/k4_adaptive_A16_pure4.log`).
- *#30's GM₄ profiles* (the 148 profiles whose level-sum maxima are all dead ends, the GM₄ seeds and failing maxima,
  instances A–H, P, Q, S: 442 lines, 434 distinct profiles; `k4/adaptive_gm4_profiles.py` rebuilds
  `results/k4_adaptive_gm4_profiles.jsonl` from #30's files, `results/k4_adaptive_gm4_profiles.log`): no rotation
  needed, by index order already (`results/k4_adaptive_hard.log`).
- *H_1–H_8 and five relabelings of each* (owner's needs from its base, `-w0`, as #33 and #32 do from t = 4; a `-w0`
  completion is also a `-w1` one): no rotation needed on 47 of the 48 (`results/k4_adaptive_A16_H.log`). The 48th,
  H_8 in #33's labeling, hit the 20-minute limit: rule F first tries ℓ, whose run is the cascade, and LB₄ʳ's exact
  owner search on it is slow; the next candidate, x_{1,1}, needs no rotation by Proposition H′.

## 3. H_t: Proposition H′

H_t is as in `k4/c4.md` §7: goods g_1, …, g_t, z, u, u′, a_{j,i}, b_{j,i}, c_{j,i}; agent ℓ = {g_1, z, u, u′} with
values (8, 6, 5, 4); for each gadget j, x_{j,i} = {a_{j,i}, b_{j,i}, c_{j,i}, g_j} with (8, 6, 4, 3), and
y_j = {a_{j,1}, a_{j,2}, a_{j,3}, e_j} with (8, 6, 4, 3), where e_j = g_{j+1} for j < t and e_t = z. The goods u, u′,
b_{j,i}, c_{j,i} are private.

**Proposition H′.** Let ρ be a run of Phase 1 on H_t (any insertion choices, P-steps in any order) in which some agent
of gadget 1 is processed before ℓ. Then after need-shrinking upgrades (LB₄'s rule, LB₄ʳ's first policy) no agent has a
need, and the owner r (the last-processed agent that is not upgraded) is valid: some completion with owner r satisfies
(OC₄). So LB₄ʳ succeeds on ρ without rotation, and its owner step finds the completion. This holds for every τ whose
first agent lies in gadget 1, whatever the rest of τ, and on every relabeling of H_t.

*Proof.* **Step 1: who takes what.** We show by induction along ρ: ℓ takes g_1; every x_{j,i} takes a_{j,i} or
b_{j,i}; every y_j takes one of its a's. Suppose it holds before the next agent p is processed.
- p = ℓ: none of g_1, z, u, u′ has been taken (the others take a's and b's), so p is inserted and takes g_1.
- p = x_{j,i}: b_{j,i} is private and still there, so p takes a_{j,i} if it is there and b_{j,i} otherwise.
- p = y_j: we show that at most one of its a's is gone, so p takes one. Only x_{j,i} takes a_{j,i} (by induction; y_j
  is unprocessed). Let x_{j,i} be the first agent of gadget j to take its a. From that step on y_j has lost a good, so
  every step is a P-step until y_j is processed, and another x_{j,i′} is processed in that time only if it has lost a
  good: a_{j,i′} (only x_{j,i′} and y_j take it) or g_j. For j ≥ 2 nobody takes g_j = e_{j−1} (induction). For j = 1
  only ℓ takes g_1, and ℓ, which never loses a good, is only ever inserted, so not while y_1 waits; nor before
  x_{1,i}: the first agent of gadget 1 to be processed comes before ℓ (hypothesis) and has lost nothing, so it is
  inserted; if it is y_1, y_1 is processed with all its goods; if it is an x, it takes its a, so it is x_{1,i}.

In particular no y_j takes e_j, and ℓ's goods other than g_1 stay junk. (If instead ℓ is processed while gadget 1 is
untouched, the x_{1,i} lose g_1 together and whether y_1 then takes e_1 = g_2 depends on the order of the P-steps,
which LB's key breaks by index. In #33's labeling the x_{1,i} take their a's before y_1, and y_1 takes e_1: the
cascade of Proposition H. On other labelings it need not happen: with ℓ inserted first and index order after it, #33's
model finds the cascade on 60 of the 120 relabelings of H_1 and on 99 of 200 random relabelings of H_2 and of H_3,
`k4/adaptive_verify_H.py 3 200 --relabel`, `results/k4_adaptive_verify_H_relabel.log`.)

**Step 2: the Phase 1 state, gadget by gadget.** The first agent of gadget j to be processed has lost nothing (Step 1),
so it is inserted. Then:

| first agent of gadget j | picks | needs |
|---|---|---|
| y_j | y_j: a_{j,1}; x_{j,1}: b_{j,1}; x_{j,2}: a_{j,2}; x_{j,3}: a_{j,3} | x_{j,1}: {a_{j,1}} |
| x_{j,1} | x_{j,1}: a_{j,1}; y_j: a_{j,2}; x_{j,2}: b_{j,2}; x_{j,3}: a_{j,3} | y_j: {a_{j,1}}; x_{j,2}: {a_{j,2}} |
| x_{j,2} (x_{j,3}: the same with 2 and 3 exchanged) | x_{j,2}: a_{j,2}; y_j: a_{j,1}; x_{j,1}: b_{j,1}; x_{j,3}: a_{j,3} | x_{j,1}: {a_{j,1}} |

(y_j is processed right after the first a is taken and takes its favourite remaining a; the x that lost its a takes
its b; the other x's take their a's whenever they come.) ℓ holds its top g_1. Every other agent holds its top and needs
nothing. The junk contains z, u, u′, g_2, …, g_t, every c, and the b of every x that holds its a.

**Step 3: need-shrinking upgrades empty NA.** An x holding b_{j,i} needs {a_{j,i}}; its pick is private, so not in NA;
c_{j,i} is junk and 8 < 6 + 4, so adding c_{j,i} removes the need: x is eligible, and c_{j,i} is its ≻-best eligible
good (g_j, if junk, is also eligible but ranked lower). A y_j holding a_{j,2} (second row) needs {a_{j,1}}; once
x_{j,2} is upgraded, a_{j,2} ∉ NA; e_j is junk and 8 < 6 + 3, so y_j is eligible. No upgrade takes another's good (c's
are private; e_j is taken only by y_j, since x_{j+1,i} upgrade with their c's and ℓ has no need), so each of these
agents stays eligible until it is upgraded, and at the fixpoint every agent that had a need holds a two-good base with
no need. These bases need not be envy-free ({b, c} = 10 < a + g = 11 for x), so below only their values are used.
NA = ∅: no agent is frozen.

**Step 4: the owner r and a completion.** Let U be the upgraded agents. Every other agent holds its top as a pick and
has one slot, so S = n − |U|, |J| = m − n − |U| and ω = m − 2n = 2t + 1 ≥ 3: an owner is needed. Let r be the
last-processed agent not in U (it holds its top; LB₄ʳ's owner step tries it first). Put into the slots, one good per
agent other than r:
- each free x_{j,i} ≠ r (it holds a_{j,i}) takes b_{j,i};
- ℓ, if ℓ ≠ r, takes u;
- each free y_j ≠ r (it holds a_{j,1}) takes e_j.

These goods are distinct junk goods, one per slot, so |C| = S − cap(r) = S − 1, the size LB₄ʳ tries first. Let
X_r = {Y_r} ∪ (J ∖ C). Then |X_r| = ω + 2 ≥ 5 > 4 ≥ |R_p| for every p, so X_r ⊄ R_p and (OC₄) for p reads
v_p(X_r ∩ R_p) ≤ v_p(X_p). Note that for j ≥ 2, g_j = e_{j−1} is in X_r only if r = y_{j−1} (otherwise y_{j−1} holds it
in its slot or, if upgraded, in its base); and z = e_t likewise only if r = y_t.
- ℓ ≠ r holds {g_1, u} = 13; X_r ∩ R_ℓ ⊆ {z, u′} = 10.
- A free x_{j,i} ≠ r holds {a, b} = 14; X_r ∩ R_x ⊆ {c, g_j} = 7.
- An upgraded x_{j,i} holds {b, c} = 10; X_r ∩ R_x ⊆ {a_{j,i}, g_j}. a_{j,i} is in X_r only if r holds it, that is
  r = y_j holding a_{j,1} (first and third rows, i = 1); then g_j ∉ X_r (g_1 is ℓ's pick, and g_j = e_{j−1} is in
  X_r only if r = y_{j−1}), so X_r ∩ R_x ⊆ {a_{j,1}} = 8. Otherwise X_r ∩ R_x ⊆ {g_j} = 3.
- An upgraded y_j holds {a_{j,2}, e_j} = 9; its other goods a_{j,1}, a_{j,3} are picks of x_{j,1}, x_{j,3}, and at
  most one of them (r's pick) is in X_r: at most 8.
- A free y_j ≠ r holds {a_{j,1}, e_j} = 11; its other goods a_{j,2}, a_{j,3} are picks, at most one (r's) in X_r: at
  most 6.

No agent is frozen, NA = ∅, so the pre-allocation is valid and every bundle but X_r has at most two goods; by Theorem
1′₄ (`k4/lb4.md` §1, machine-checked) the completion is EFX₀. LB₄ʳ's owner test is exact for a given C (a protecting
good in each threatened agent's own slot, by augmenting paths), and it tries every C of size S − cap(r); r's needs are
empty whether taken from its base or its bundle. So the first policy's owner step succeeds with owner r. ∎

**Corollary.** On every relabeling of H_t, rule F (and each rule of §1 that can choose the first agent) needs no
rotation: at bound 0 it tries every first agent, and one of gadget 1 satisfies Proposition H′ whatever the index order
does afterwards. By Proposition H, index order needs ⌈2t/3⌉ rotations, and relabeling defeats every fixed order.

**Checked independently** (`k4/adaptive_verify_H.py` → `results/k4_adaptive_verify_H.log`): in PR #33's model of LB₄ʳ
written from `lean/EFX/LB4R.lean` (`k4/c4_verify_H/lb4r.py`, no shared code), for t ≤ 5 and 200 random insertion
sequences each: every sequence that processes an agent of gadget 1 before ℓ (900 in all) has no cascade, no need after
need-shrinking upgrades, and an output with owner r under both owner-needs conventions; every other sequence (100)
has y_1 take e_1 (in #33's labeling, which the check uses; see the remark after Step 1).

**Where the hypotheses enter.** |R_p| ≤ 4 < |X_r| lets (OC₄) be read as a bound on v_p(X_r ∩ R_p). One slot good
protects an agent holding its top because the top plus one of its goods beats the other two (the mechanism of Lemma
2₄, which needs |R_p| ≤ 4). The needs disappear with *one* added good because the needing agents' types satisfy
a < b + c (x on b) and a_1 < a_2 + e (y on its second good): at a 4-good agent holding b, need-shrinking by one good
needs a < b + c; for a type with a > b + c it would not work, and such types are what a general theorem must handle
(§6). Private goods (b, c, u) give every protected agent its own slot good, so the slot goods never compete; this is
where H_t's structure is used, and what a general theorem must replace by a count.

## 4. Structure: optimality, and "Theorem C₄ after the first insertion"

- *Rule F is optimal where compared.* `-i2` (fewest rotations over every insertion sequence) gives the same histogram
  as rule F on n ≤ 3 and on n = 4 with one, two and three 4-good agents (`results/k4_adaptive_rules_n23.log`,
  `results/k4_adaptive_rules_n4.log`, `results/k4_adaptive_exists_n4_3.log`). Rule F's count is at least the optimum on
  every profile, so equal histograms mean equality on every profile. So on these classes the insertion order matters
  only through the first agent, and the optimum is at most one rotation.
- *Every continuation.* `-A24` (for each first agent, the largest number of rotations over every continuation)
  reaches the same histogram on n ≤ 3 and on n = 4 with one or two 4-good agents (`results/k4_adaptive_rules_n23.log`,
  `results/k4_adaptive_rules_n4.log`; the run with three was lost with the container and not repeated): some first
  agent makes *every* later insertion order work with the fewest rotations. Proposition H′ is an instance (H_t, no rotation). This is LB⁺'s Theorem C (every run of Phase 1
  works) after one chosen step:

**Conjecture K4.AD.C1.** For every strict profile of every k = 4 core there is an agent a such that for every
insertion sequence τ that starts with a, LB₄ʳ(τ) succeeds with at most one rotation, and with none if some insertion
sequence needs none.

- *Which agent.* Index order needs a rotation on 10,029,590 profiles at n = 3; `k4/adaptive_mine.py` takes up to 60
  leaf representatives per core, 2,556 in all (`results/k4_adaptive_mine_n3.log`). Rule F's first agent is usually
  not the index leader: on 1,703 of the 2,556 (two thirds) it is an agent that the index leader's need chain reaches,
  holding its second or third good in the index run: inserting it first realizes, inside Phase 1, the rotation along
  that chain (the mechanism of #37's Lemma Ω). Of the other 853, 137 are the index leader itself (there rule F also
  needs a rotation), 576 hold their top (often frozen), and 140 hold their second good without being reachable from
  the leader. No single feature decides it (§5).

## 5. Rejected rules (`attempts/k4-adaptive-*.md`)

With at most one rotation, each of these fails (LB₄ʳ with two rotations succeeds): `results/k4_adaptive_rules_n23.log`
has the counts, `results/k4_adaptive_smallest.log` the smallest failures, and `attempts/k4_adaptive_attempts.py`
(`results/k4_adaptive_attempts.log`) reproduces each and confirms it in PR #33's independent model and by brute force.

| rule | n = 3 profiles needing 2 rotations | smallest failure |
|---|---|---|
| index order (`-A0`) | 12,040 | n = 3, m = 6 |
| least \|NA\| of the new block (`-A1`, lb4.c's `-i3`) | 12,040 | n = 3, m = 6 |
| least ω after envy-free upgrades, rest in index order (`-A2`) | 11,520 | n = 3, m = 6 |
| least ω after need-shrinking upgrades (`-A4`); after none (`-A5`) | 11,520; 12,040 | n = 3, m = 6 |
| 4-good first (`-A6`); 3-good first (`-A7`) | 12,040; 12,160 | n = 3, m = 6 |
| least / most contested top (`-A8`, `-A9`) | 11,520; 13,720 | n = 3, m = 6 |
| least ω, then fewest frozen 4-good agents (`-A10`); c4one's key generalized (`-A11`) | 11,520; 11,520 | n = 3, m = 6 |
| least ω at the first step only (`-A13`) | 11,520 | n = 3, m = 6 |

The smallest failure is the same profile for most rules: agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values
(1, 4, 6, 8), (2, 3, 4, 8), (2, 7, 8, 4). Only agent 1 first needs one rotation; agents 0 and 2 first need two.
After envy-free upgrades (`-A2`) or none (`-A5`) every first agent gives ω = 2, so the tie goes to agent 0; after
need-shrinking upgrades (`-A4`) the first agents 0, 1, 2 give ω = 1, 2, 1, so ω prefers a failing agent. Neither ω
nor any single feature tried sees the difference.
`attempts/k4-adaptive-greedy-omega.md` and `attempts/k4-adaptive-local-features.md` have the details.

**Matching-based orders** (the first round of Sgouritsa–Sotiriou, arXiv 2502.09777 §3, Lemma 3.7, as summarized in
`proofs/pq_bounded.md` §2.5; `attempts/k4-adaptive-matching.md`). A matching of the agents to their first or second
choice, of largest size and then most first choices (`k4/adaptive.c` `choice_matching`, checked against brute force by
`k4/adaptive_matching_check.py`, `results/k4_adaptive_matching_check.log`), orders the insertion steps: `-A17` agents
matched to their first choice first, then second, then unmatched; `-A18` second-choice agents first; `-A25` the
matching recomputed at every insertion step. Fewest rotations LB₄ʳ needs on the rule's sequence
(`results/k4_adaptive_matching.log`):

| test set | `-A17` first choice first | `-A18` second choice first | `-A25` recomputed |
|---|---|---|---|
| n = 3, exhaustive (299,837,376) | 11,520 | 8,120 | 11,520 |
| n = 4, one 4-good agent, exhaustive | 0 | 0 | 0 |
| n = 4, two, exhaustive (724,847,616) | 216 | 232 | 216 |
| n = 4, three, exhaustive (34,971,844,608) | 28,256 | 13,376 | 28,256 |
| n = 5, five classes, 1,000 random profiles per core (31,584,000) | 1 | 6 | 1 |
| #30's 442 GM₄ profiles | 0 | 0 | 0 |
| hill-climbing on #32's hard n ≤ 5 cores (1,344,000) | 420 | 1,069 | 420 |
| H_1, H_2, H_3 in #33's labeling (rotations needed) | 1, 2, 2 | 0, 0, 0 | 1, 2, 2 |
| H_1–H_3, five relabelings each | 0 | 0 | 0 |

(Profiles needing two rotations; none needs three. n = 2: none. Rule F needs at most one on every row. The `-A17` rows
were run before a fix to `-A18`, which does not change `-A17`; the log records the source hash of each run.)

*Ties.* When a profile has several optimal matchings, `choice_matching` returns the one its successive-shortest-path
computation ends with (Bellman–Ford over the edges in a fixed order: agents in index order, each agent's first-choice
edge before its second; a strictly shorter path replaces the current one). That is deterministic but is not a
tie-break by index, and the counts above depend on it. `k4/adaptive_matching_ties.py` enumerates every optimal
matching by brute force and runs PR #33's model on every insertion sequence the rule can produce under some choice of
them (for `-A25`, at every insertion step): at n = 3, 16 of the 96 failing leaves of `-A17` and `-A25` (weight 640 of
11,520) and 88 of the 200 of `-A18` (weight 6,280 of 8,120) need two rotations under every optimal matching (checked
on each leaf's representative profile; `results/k4_adaptive_matching_ties.log`, from the leaves in
`results/k4_adaptive_matching_deep_n3.log`; on every leaf `adaptive.c`'s own sequence is among those derived and needs
two in the model). The smallest failures recorded below (P1, P3 of `attempts/k4-adaptive-matching.md`) are
tie-dependent; the profile T there fails for all three rules under every optimal matching.

All three fail with one rotation at n = 3, m = 6: with `adaptive.c`'s matching, `-A17` and `-A25` on the profile of
the table above and `-A18` on `-A9`'s; under every optimal matching, all three on T: agents {0, 1, 4, 5},
{2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8), (3, 5, 7, 6), (2, 3, 4, 8) (confirmed in PR #33's model,
`results/k4_adaptive_attempts.log`, `results/k4_adaptive_matching_ties.log`). On H_t the optimal matching is unique
(ℓ, y_j, x_{j,2}, x_{j,3} get their first choice, x_{j,1} its second), so `-A17` and `-A25` insert ℓ first in #33's
labeling, which is index order (Proposition H: ⌈2t/3⌉ rotations), while `-A18` inserts the x_{j,1} before ℓ, whatever
the labels, and needs no rotation on every relabeling (Proposition H′).

## 6. The gap: the theorems do not cover the multi-4-good case

`k4/adaptive.c -A20/-A21/-A22` ports the coverage test of #37 (`k4/c4check.c -X -P2` of proof/k4-c4one: a run is
covered when, after envy-free upgrades, ω ≤ 0 or Theorem A₄, B₄, B₄ʷ, A₄ᵀ, A₄⁺ or A₄⁺(o) applies). The port agrees
with c4check.c on every profile count (`k4/adaptive_crosscheck.py`, `results/k4_adaptive_crosscheck.log`). With one
4-good agent every profile has a covered insertion sequence (as #37 found); with two or more it does not:

| class | profiles with no covered insertion sequence | ... also none among index and one-step changes |
|---|---|---|
| n = 2 (both agents 4-good) | 12,420 of 189,216 | 12,420 |
| n = 3 | 7,503,039 of 299,837,376 | 7,503,039 |
| n = 3, one / two / three 4-good agents | 0 / 48,492 / 7,454,547 | |
| n = 4, one 4-good agent | 0 | 0 |
| n = 4, two | 155,947 of 724,847,616 | 157,421 |

The smallest: two agents with the same four goods and values (2, 4, 5, 8) (`attempts/k4-adaptive-coverage-multi4.md`).
After envy-free upgrades (there are none) agent 0 holds its top, frozen and exposed; the 4-good r = 1 is exposed after
the only rotation, so B₄ʷ does not apply, and A₄⁺ counts one good against no slot. LB₄ʳ's first policy upgrades
agent 1 from b to {b, c} (need-shrinking: 8 < 5 + 4), nobody is frozen, ω = 0, and no owner is needed.

How rule F succeeds where no run is covered (`results/k4_adaptive_uncovered.log`):

| class | no covered sequence | need-shrinking upgrades, no owner / owner r / other owner / one rotation | envy-free upgrades, owner r / other | no upgrades, owner r / other |
|---|---|---|---|---|
| n = 2 | 12,420 | 3,600 / 2,520 / 6,300 / 0 | 0 / 0 | 0 / 0 |
| n = 3 | 7,503,039 | 2,907,589 / 3,749,002 / 831,723 / 0 | 13,189 / 1,536 | 0 / 0 |
| n = 4, one 4-good agent | 0 | | | |
| n = 4, two | 155,947 | 44,769 / 67,280 / 12,344 / 31,312 | 168 / 10 | 32 / 32 |

(The first policy under which rule F's sequence succeeds, and how its owner step ended.) At n ≤ 3 no uncovered profile
needs a rotation; at n = 4 with two 4-good agents 31,312 do, which none of the theorems addresses.

So a proof of rule F, or of K4.AD.C1, needs a counterpart of Theorems A₄–A₄⁺ for **need-shrinking upgrades**: an
agent holding b (or its second good) with a < b + c gives up its need with one junk good, which unfreezes the holder
of its top, as in Proposition H′. Such an upgraded pair need not be envy-free, so it can be threatened by the owner's
bundle (the reason #33's theorems used envy-free upgrades). The counting theorem carries over once such agents are
counted like frozen ones:

**Theorem A₄⁺ᴺ (written proof below, found correct in the #44 review).** Let P be the state after any run of Phase 1 and
need-shrinking upgrades to a fixpoint (LB₄'s rule, any order), with ω ≥ 1. Let o be an agent that is not frozen and
has a base of at most one good, or an upgraded agent. Put W_o := B_o ∪ J, and let E_o be the agents x ≠ o threatened
by W_o with their base, *upgraded agents included*. Let dem(x) = 1 if x is free (neither frozen nor upgraded), holds a
pick, and |B_o ∩ R_x| ≤ 1; otherwise dem(x) = ρ_o(x), the least size of a set D ⊆ R_x ∩ J such that x is not
threatened by W_o ∖ D with its base (∞ if none). If Σ_{x ∈ E_o} dem(x) ≤ S − cap(o), then o is a valid owner with its
needs from its base.

*Proof.* This is the proof of A₄⁺(o) (`k4/c4one.md` §5, after `k4/c4.md` §4c) with one change: there, upgraded agents
hold envy-free bases and are never threatened; here an upgraded agent may be threatened, and it is treated like a
frozen one (it holds exactly its base and has no slot).
- Validity: need-shrinking upgrades keep the pre-allocation valid (`k4/lb4.md` §2). W_o ∩ NA = ∅: J by (V1); B_o
  because o is not frozen or, if upgraded, by (V2). So every good of R_x ∩ W_o is ranked below x's pick, an agent
  without a pick is not threatened, and every free x ∈ E_o holds a pick and has a junk good of R_x (it is threatened,
  so |R_x ∩ W_o| ≥ 2, and at most one of these goods is in B_o).
- Fill the slots of the free agents of E_o with dem(x) = 1 first, one agent at a time, each with its ≻-best junk good
  not yet placed. By Lemma 2₄ (`k4/lb4.md` §1, |R_x| ≤ 4; its proof is per agent, uses only |B_o ∩ R_x| ≤ 1 and that
  later placements only shrink X_o) none of them is threatened by X_o, whatever is placed afterwards.
- For every other x ∈ E_o (frozen, upgraded, or free with two goods of R_x in B_o) fix D_x of size ρ_o(x). The goods of
  ⋃ D_x not yet placed number at most Σ ρ_o(x) ≤ S − cap(o) − #{free x ∈ E_o with dem 1}, the number of slot places
  left among the free agents other than o; place them there (a free agent's slot may take any junk good). Fill the
  remaining places with junk, so that |C| = S − cap(o) < |J| (ω ≥ 1), and let X_o = B_o ∪ (J ∖ C) ⊆ W_o.
- (OC₄): an agent not in E_o holds at least its base and X_o ⊆ W_o, so it is safe by monotonicity (`k4/c4.md` §1); an
  x ∈ E_o with a set D_x holds at least its base and X_o ⊆ W_o ∖ D_x: safe by the choice of D_x and monotonicity; the
  others are safe by Lemma 2₄. Frozen agents hold exactly their bases, and only X_o has more than two goods (upgraded
  bases have two, free agents one good plus one slot good), so Theorem 1′₄ applies, with the owner's needs from its
  base. ∎

*Checked* (`results/k4_adaptive_cover_N.log`), 0 violations in both modes:
- `k4/adaptive.c -A22 -C3 -Z2`: on every insertion sequence of every strict profile (leaf by leaf), after
  need-shrinking upgrades, the exact owner test with no owner when ω ≤ 0 and otherwise with *every* owner whose count
  A₄⁺ᴺ admits (needs from the base, no rotation): 35,326 instances at n = 2, 82,725,197 at n = 3, 6,960,194 at n = 4
  with one 4-good agent, 366,750,792 with two (an instance is a leaf, a sequence and an owner; a leaf is a set of
  profiles on which every comparison made agrees).
- `-Z1` (the first check): only the first covered sequence of each profile, where #33's and #37's theorems are
  tried first, and only the owner found. (Its `rot` and `pol` columns in logs before the #44 review round were wrong:
  a split inside the check left the upgrade policy and owner-needs convention it had set; fixed, and the log regenerated.)

A₄⁺ᴺ covers much of the gap, not all of it (profiles with no covered insertion sequence, every sequence tried):

| class | #33 + #37 | + A₄⁺ᴺ |
|---|---|---|
| n = 2 | 12,420 | 1,020 |
| n = 3 | 7,503,039 | 119,616 (0 / 280 / 119,336 with one / two / three 4-good agents) |
| n = 4, one 4-good agent | 0 | 0 |
| n = 4, two | 155,947 | 62,536 |

What LB₄ʳ needs on these, over every insertion sequence (`k4/adaptive.c -A26`: `-i2` with the coverage recorded;
`k4/adaptive_uncovered.py`, `results/k4_adaptive_basewants.log`):

| class | uncovered | owner's needs from its base: no rotation | … one rotation | of those, no rotation with the owner's needs from its bundle | one rotation under both conventions |
|---|---|---|---|---|---|
| n = 2 | 1,020 | 300 | 720 | 720 | 0 |
| n = 3 | 119,616 | 90,336 | 29,280 | 29,280 | 0 |
| n = 4, two 4-good agents | 62,536 | 30,024 | 32,512 | 1,200 | 31,312 |

(They agree with the plain runs over whole classes, in the same log: `-i2 -r0 -w0` fails on 720, 292,616 and 208,096
profiles, the 720, 29,280 and 32,512 above plus 0, 263,336 and 175,584 covered ones; `-i2 -r3` needs a rotation on 0,
263,336 and 206,880, the 0, 0 and 31,312 above plus covered ones.) So the larger part of what A₄⁺ᴺ leaves is a
*counting* gap: LB₄ʳ's exact owner test finds an owner valid with its needs from its base, without rotation, and no
count of the theorems certifies it. The rest needs either one rotation or the owner's needs from its bundle (the smallest: n = 2, m = 5, agents {0, 2, 3, 4} and
{1, 2, 3, 4}, both with values (2, 3, 4, 8) on their goods in index order: with needs from the base it needs one
rotation, with needs from the bundle none). At k = 4 the owner's large bundle can remove its own needs, which frees the
holder of its top (`k4/lb4.md` §3, item 4); none of the counting theorems uses that. That, the rotations (the
one-rotation profiles of §2, and the 31,312 above), and a choice of the first agent that makes one of these theorems
apply are what a proof of K4.AD.F still needs.

## 7. Reproduce

```
python3 k4/adaptive_run.py results/k4_certs_3.json.gz -A16 -r3                   # rule F, n = 3 (10 s)
python3 k4/adaptive_run.py results/k4_certs_4_n4_3.json.gz -A16 -r3               # n = 4, three 4-good agents (~5 min)
python3 k4/adaptive_run.py results/k4_certs_4_pure.json.gz -A16 -r3               # pure n = 4 (hours on 4 CPUs)
python3 k4/adaptive_run.py results/k4_certs_5_pure.json.gz -A16 -r3 -S5000        # random profiles
python3 k4/adaptive_run.py results/k4_lb4r_cores_hard5.json.gz -A16 -r3 -H3000 -K2  # hill-climbing against rule F
python3 k4/adaptive_run.py results/k4_certs_3.json.gz -i2 -r3                     # fewest rotations over every order
python3 k4/adaptive_run.py results/k4_certs_3.json.gz -A24 -r3                    # some first agent, every continuation
python3 k4/adaptive_H.py 1,2,3,4,5,6,7,8 --perms=5 -A16 -r1 -w0                   # H_t and relabelings
python3 k4/adaptive_verify_H.py 5 200                                            # Proposition H', PR #33's model
python3 attempts/k4_adaptive_attempts.py                                         # rejected rules, smallest failures
python3 k4/adaptive_lb4check.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz   # per core against lb4.c -d2
python3 k4/adaptive_run.py results/k4_certs_3.json.gz -A22 -C3 -Z2 -r3            # A4+N on every run and owner
python3 k4/adaptive_uncovered.py results/k4_certs_3.json.gz -A26 -C3 -r0 -w0      # the gap A4+N leaves, needs from the base
python3 k4/adaptive_matching_ties.py                                             # matching rules under every optimal matching
bash k4/adaptive_runs.sh                                                         # every log of this file
```
The driver's result lines give the histogram `rot=[…]` of rotations 0 … R; logs written before the #44 review round
label it "(last entry: fails)", which was wrong: failures are the `fails=` count.
`k4/adaptive_verify_H.py` and `attempts/k4_adaptive_attempts.py` use PR #33's `k4/c4_verify_H/` (on main since #33
merged); `k4/adaptive_crosscheck.py` needs `k4/c4check.c` of branch proof/k4-c4one (PR #37) compiled (`C4CHECK_BIN`),
which differs from main's `k4/c4check.c` (#33) by A₄⁺(o).
