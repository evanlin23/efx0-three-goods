# k = 4 minimal counterexample, round 3: double edges, twins, near-twins

Workstream `proof/k4-twins`. New local reductions for a minimal counterexample to TARGET₄, in the certified style of
`k4/MINCEX.md` (rows K4.MC0–K4.MC7; notation, kinds P3/Q3/P4/Q4 and Γ′ as there). A configuration (S, I) with its
agents' types is excluded once every admissible local state of an EFX₀ allocation of a smaller gadget instance has an
extension (Lemma K4.MC1: M1 and M1(b) at k = 4).

- Generator: `k4/twins4.py`, on `k4/reduce4.py` (DEL, and one-agent gadgets h on boundary goods plus 0–2 gadget goods,
  from reduce4's menu of valuation classes; greedy choice; every chosen gadget re-run directly).
- Independent check: `k4/check_twins4.py`. It runs `k4/check_reductions4.py`'s functions unmodified (own type
  enumeration, own local states, raw EFX₀ definition, gadget legality including H′ ∈ 𝒞_β, every stored extension checked
  against M1/M1(b); no code shared with reduce4.py or twins4.py) with the new configurations hard-coded in the checker.
  A record whose declared configuration differs from the hard-coded one is rejected. Sensitivity test in each check log.
- Candidate filter: `k4/twins_filter.py` (structural: does a core contain a certified double edge; `gamma_prune` does
  the same on Γ′; `cut_domains` for the partial cases). Candidate pipeline with it: `k4/twins_count.py`.

**Summary.**
- *Certified* (K4.MC8): no double edge between two agents of kinds in {Q3, P4} (open or closed), and no closed one
  between a Q3 or P4 agent and a Q4 agent. With K4.MC3 and K4.MC5, every double edge has a Q4 end. The open E3–Q4 ones
  and the Q4–Q4 ones are only partly reduced (profiles left recorded).
- *Effect*: β = 4 candidates 5,558 → 3,166; β = 5 candidates per n in §1. The counting bound n ≤ 3(β − 1) is unchanged.
- *Certified, round 3b* (K4.MC9, §4): no good of degree 3 is valued by three P3 agents (a *claw*). It needs gadgets
  with two agents, found with a C extension search (`k4/reduce4c.c`, validated against reduce4). β = 5 candidates
  502,638 → 320,348; β = 4: 3,166 → 2,079.
- *Failed* (attempts/): twins with the same relevant set (provably irreducible under M1 when no good is private to the
  pair), P3 twins, near-twins with ≤ 1 such good, claws with one-agent gadgets alone (solved by two-agent ones, §4),
  triangles, closed single edges, Q4 stars.

## 1. Results

**Theorem K4.MC8 (double edges).** Let H be a minimal counterexample to TARGET₄ (or one within 𝒞_β), with strict types
(K4.MC0). Let e ≠ f be agents that share two goods g0, g1 which no other agent values (a *double edge* of Γ′). Then
at least one of e, f is a Q4 agent. More precisely, writing c for the number of further goods e and f have in common:

| kinds of e, f | c = 0 (open) | c = 1 (closed) | c = 2 |
|---|---|---|---|
| Q3, Q3 | **excluded** (36 of 36) | **excluded** (36 of 36) | – |
| Q3, P4 | **excluded** (1,728 of 1,728) | **excluded** (1,728 of 1,728) | – |
| P4, P4 | **excluded** (82,944 of 82,944) | **excluded** (82,944 of 82,944) | – |
| Q3, Q4 | 1,708 of 1,728 reduced | **excluded** (1,728 of 1,728) | – |
| P4, Q4 | 81,944 of 82,944 reduced | **excluded** (82,944 of 82,944) | – |
| Q4, Q4 | 50,392 of 82,944 reduced | 71,512 of 82,944 reduced | 80,152 of 82,944 reduced |

(A P3 agent in a double edge is configuration px-closed of K4.MC5, or two P3 agents sharing a good of degree 2, K4.MC3.)
CERTIFIED (both implementations agree on every count, the reduced ones included). The profiles no reduction covers are
recorded by the checker (`results/k4_twins/dbl_q3_uncovered.json`, `results/k4_twins/dbl_p4q4_uncovered.json`); in a
minimal counterexample the profile of every partially reduced double edge lies in them, under every labeling, and
`k4/twins_filter.py` cuts type domains accordingly. Each entry is a configuration
dbl-K1-K2[-cC] (§2); the reduced counts are of the pair's strict type profiles (6 types for a 3-good agent, 288 for a
4-good agent).

Reading of the open Q3–Q4 case (the 20 profiles left, `results/k4_twins/dbl_q3_uncovered.json`): e (Q3, on g0, g1, a)
ranks a first, and f (Q4) ranks first the double-edge good that e ranks last, and last the other one.

**Effect on the candidate lists** (`k4/twins_filter.py`, certified rows only):
- β = 4 (`results/k4_min_cex_shapes_4.json.gz`, the 5,558 cores of K4.MC7): 2,392 contain a certified double edge,
  3,166 do not. Four of the six graphical all-P4 cores (n = 6, m = 15) have a P4–P4 double edge, so K4.MC8 alone
  excludes them; the other two (agent multigraph the prism, and K₃,₃) have none.
- β = 5, n = 6 (the hunt session's 30,337 candidates, `results/k4_hunt/mc_n6_b5.json.gz` on `claude/k4-hunt-cegar`):
  9,455 excluded, 20,882 left; by m (candidates → left): 9: 3,488 → 2,590; 10: 8,992 → 6,567; 11: 10,360 → 7,208;
  12: 5,839 → 3,669; 13: 1,490 → 781; 14: 168 → 67.
- β = 5, n = 7 (its sample of 675): 316 excluded, 359 left.
- β = 5, every n (`k4/twins_count.py`: `k4/mincex_shapes.py`'s pipeline as the hunt session's `mc_n.py` runs it,
  genbg's Γ′ list, K4.MC3, K4.MC5's structural prune and px domain cuts, isomorphs merged, with K4.MC8 added at the Γ′
  level by `twins_filter.gamma_prune`, which agrees with `twins_filter.excluded` on all 36,570 cores tested). Logs
  `results/k4_twins/count_n<n>_b5.log`, lists `results/k4_twins/mc_n<n>_b5_mc8.json.gz`. Single implementation of the
  pipeline (it reproduces the 20,882 of n = 6 found by filtering the hunt session's own list):

  | n | before K4.MC8 | after |
  |---|---|---|
  | 6 | 30,337 (hunt session) | 20,882 |
  | 7 | 122,006 (hunt session) | 78,118 |
  | 8 | 249,672 | 152,568 |
  | 9 | 260,846 | 156,162 |
  | 10 | 134,113 | 78,616 |
  | 11 | – | 15,621 |
  | 12 | – | 671 |

  The "before" counts for n ≥ 8 are `twins_count.py N 5 --no-mc8` (`results/k4_twins/count_n<n>_b5_baseline.log`).
  The β = 5 total after K4.MC8 is 502,638 candidate cores (n ≤ 3(β − 1) = 12 by K4.MC4; at n = 11 and 12 the
  Γ′ prune removes 379,810 and 812,295 graphs), which a direct certification of β = 5 (as K4.MC7 did for
  β = 4) would have to cover.

*Domain cuts.* Applying K4.MC5's px cuts and then K4.MC8's partial double-edge cuts (`twins_filter.cut_domains`, the
uncovered files above) empties the domains of only a few more candidates: 217 of the 20,882 at β = 5, n = 6 (20,665
left; profile total 4.3·10¹⁶ → 2.4·10¹⁶); 6 of the 359 in the n = 7 sample; 8 of the 3,166 at β = 4. Single
implementation. `twins_filter.restricted_domains(sets, m, fail, load_uncovered())` is a drop-in for
`mincex_shapes.restricted_domains` that applies both; `twins_count.py N 5 --cuts` writes the cut lists
(`results/k4_twins/mc_n6_b5_mc8cut.json.gz`, log `count_n6_b5_cuts.log`). At n = 7 the cuts leave 77,427 of 78,118
candidates (profile total 3.5·10¹⁸ → 2.6·10¹⁸; `mc_n7_b5_mc8cut.json.gz`, `count_n7_b5_cuts.log`).

The counting bound n ≤ 3(β − 1) of K4.MC4 counts P3 incidences, so K4.MC8 does not change it. (In its extremal case
every E3 agent has one P3 neighbour through a degree-2 good and its two other incidences are degree-2 goods shared with
E3 agents, so the E3 agents form disjoint cycles through degree-2 goods; K4.MC8 rules out the cycles of length 2, and
length ≥ 3 remains.)

## 2. Configurations and why they reduce

*Configuration dbl-K1-K2[-cC].* S = {e, f}. e has goods g0, g1, then its other goods: Q3: a; P4: a, p_e; Q4: a, b.
f has g0, g1, then Q3: x; P4: x, p_f; Q4: x, y. With c = 1 (c = 2), f's x (x and y) is renamed to e's a (a and b).
I = {g0, g1} plus the private goods p_e, p_f; ∂ = the other goods. As K4.MC1's remarks say, a boundary good need not
have an outside valuer, so the configuration also covers the cases where a further common good also has degree 2
(e.g. three goods shared only by e and f), where a, x or y is private (e.g. a P3 agent on g0, g1, a, which is
K4.MC5's closed px), and where e or f has more private goods than its kind says.

*Reductions.* The gadget replaces e and f by one agent h on ∂ and one gadget good z′ (a pendant good valued only by
h), so H′ has one agent fewer, ≤ 4 goods per gadget agent, and lies in 𝒞_β (h is a star on ∂; the checker verifies this
for every way the rest of H can connect the boundary goods). Typical gadgets: h valuing only z′ (it reduces exactly the
profiles DEL does, 1,132 of 1,728 for Q3–P4); h = (a: 2, x: 0, z′: 1); h = (a: 2, x: 4, z′: 1). (Intuition, not used:
the two interior goods g0, g1 are what make the double edge reducible: in every state e and f can each take one of
them, plus moved items, and h's safety in Y rules out most states that would threaten them through ∂.)

## 3. Explored (coverage only, single implementation unless noted)

Logs: `results/k4_twins/explore_dbl_big.log` (dbl-P4-P4, dbl-P4-Q4 with the copy gadgets; its dbl-Q4-Q4 part was stopped
and superseded by the certificate run), `results/k4_twins/explore_tri.log`, `results/k4_twins/explore_q4twins_z2.log`.
The failed configurations are written up in `attempts/k4-twins-same-R.md`, `attempts/k4-twins-near.md`,
`attempts/k4-twins-claw.md`, `attempts/k4-twins-triangles.md` and `attempts/k4-twins-q4-double-edges.md`, each with its
smallest failing profile and the command that replays it.

| configuration | profiles | reduced |
|---|---|---|
| dbl-Q4-Q4-c2 (twins: R = {g0, g1, a, b}) with two gadget goods | 82,944 | 80,152 (no gain over one) |
| DROP-g0 (two copy agents: g0 deleted) on dbl-Q3-Q3, dbl-Q4-Q4-c2, dbl-P4-P4-c1 | | 0, 0, 41,323 (no gain) |
| xyc-Q3-Q3 (one shared good of degree 2, one shared boundary good) | 36 | 15 |
| xyc-Q3-P4 | 1,728 | 1,249 |
| twins-Q3-0 (R = {a, b, c}, all boundary) | 36 | 0 |
| twins-Q3-1 (R = {g0, a, b}, g0 of degree 2) | 36 | 26 |
| twins-P3 (two P3 agents on the same two shared goods) | 36 | 26 (two gadget goods and copy gadgets add nothing) |
| near-Q3-Q4-0 (three common goods, all boundary) | 1,728 | 0 |
| near-Q3-Q4-1 | 1,728 | 740 |
| near-Q3-P4-0 | 1,728 | 432 |
| near-Q3-P4-1 | 1,728 | 1,564 |
| tri-Q3-Q3-Q3 (three Q3 agents pairwise sharing a good of degree 2) | 216 | 208 (left: every agent ranks its boundary good first) |
| tri-Q3-Q3-P4 | 10,368 | 10,288 |
| tri-Q3-P4-P4 | 497,664 | 496,864 |
| claw (three P3 agents on one good of degree 3), one-agent gadgets only | 216 | 177 (all 216 with two-agent gadgets, §4) |
| star-Q4-2 (a Q4 agent sharing goods of degree 2 with two P3 agents) | 10,368 | ≥ 3,220 (partial run) |

*Why twins without degree-2 goods cannot be reduced this way* (proved). Suppose I = ∅ (twins-Q3-0: R_e = R_f = {a, b, c},
all boundary; near-Q3-Q4-0 likewise). A smaller gadget has at most one agent h (|S′| < |S| = 2, since |I′| < |I| = 0
is impossible). Take any valuation of h, let b maximize v_h over R, and take the state in which h holds b and all of
I′, a and c each lie in an outside bundle together with outside goods, and the unenvied bundle is h's own. h is safe
(each other bundle threatens it by at most v_h(a) or v_h(c), both ≤ v_h(b)), so the state is admissible. The moved items
are {b} only, so one of e, f receives nothing, and it is threatened by the bundle holding a (or c) and outside goods.
So no reduction under Lemma M1/M1(b) exists for any gadget, whatever the types, identical or not; the twins that reduce
are the ones with two goods nobody else values (dbl-…-c1, dbl-…-c2). Twins with identical
valuations are classical in the EFX literature (EFX₀ exists when all agents share one valuation; the
Plaut–Roughgarden repair, as restated in Akrami–Ashuri–Chaudhury–Mehlhorn–Soldatov, arXiv 2608.08864, which
`proofs/citations.md` lists as read; the original Plaut–Roughgarden paper is [unverified] here), but those arguments are
global and do not give a local reduction.

## 4. Claws (K4.MC9, round 3b)

**Theorem K4.MC9 (claws).** In a minimal counterexample to TARGET₄ (or one within 𝒞_β), with strict types, no good of
degree 3 is valued by three P3 agents. CERTIFIED (both implementations agree on every count).

*Configurations.* claw: S = {f1, f2, f3}, f_i on (G, y_i, p_i), G valued by them only, p_i private, y1, y2, y3 distinct
boundary goods; I = {G, p1, p2, p3}. claw-y12: y1 = y2 (f1 and f2 also share their other good); claw-y123: y1 = y2 =
y3. 216 profiles each. (A boundary good need not have an outside valuer, so these also cover y's of degree 2 or 3.)

*Reductions.* DEL; one-agent gadgets h on the boundary goods plus 0–2 gadget goods; and **two-agent gadgets**: fixed
agents h1, h2, each on some boundary goods and one gadget good of its own (z1′, z2′), the two forming a forest on the
boundary goods (for the claw: a path y_a – h1 – y_c – h2 – y_b, or h1 on all three and h2 pendant at one), every valuation
class of reduce4's menus for each. H′ has two agents instead of three and lies in 𝒞_β (the checker tests every way the
rest connects the boundary goods; one sensitivity case is a gadget pair that closes a cycle, rejected).

| configuration | one-agent gadgets and DEL | with two-agent gadgets | records |
|---|---|---|---|
| claw | 177 | **216 of 216** | 11 (7 two-agent) |
| claw-y12 | 196 | **216 of 216** | 4 (1 two-agent) |
| claw-y123 | **216 of 216** | – | 2 |

Why two agents (intuition, not used): in the claw's hardest profile (every f_i ranks G > y_i > p_i), every state in
which two of the y's lie in outside bundles of ≥ 2 goods is fatal for any extension (each such f_i must hold G, and
there is one G). A single gadget agent cannot make all such states inadmissible (it can always hold its favourite y),
but h1 on {y_c, y_a} and h2 on {y_c, y_b} can: whichever two y's are outside, one of h1, h2 holds neither of its goods.
The gadget goods z1′, z2′ make the gadget bundles inner, which the domination condition needs when a private good joins
a boundary good (the obstacle of `attempts/k4-mincex-drop-private.md`).

*Tools.*
- `k4/reduce4c.c` enumerates the extensions of a local state exactly as `reduce4.Reduction.extensions` does, and proposes
  one per distinct tuple of views. `k4/reduce4c.py` rebuilds every proposal and re-checks it with reduce4's own code
  (domination, moved-items test, views, safe masks) before using it, so the C code can only lose coverage.
  `reduce4c.py test` (log `results/k4_twins/reduce4c_test.log`): on 12 reductions (pair, loop, px, dbl, claw, triangle;
  copy and fixed gadgets) it agrees exactly with `reduce4.run` on the reduced profiles and on every state's coverage.
- `reduce4c.gadget_search2`: the coverage of a state does not depend on the gadget valuations, so it is computed once;
  admissibility is the conjunction of one menu vector per gadget agent (reduce4.menu_admissible).
- Generator `twins4.py certify2`; certificates `results/k4_twins/claw.json.gz`, `claw_y12.json.gz`,
  `claw_y123.json.gz`; independent check `results/k4_twins/check_claw.log` (check_reductions4's functions through
  check_twins4.py with the three configurations hard-coded; sensitivity tests on claw and claw-y12, 21 cases rejected).
- Also tried: the two-agent copy gadget "delete f1, keep f2 and f3" reduces 105 of the claw's 216 profiles, none new
  (`results/k4_twins/claw2c.log`); for the Q3 triangle, "delete one agent, keep two copies" reduces 44 of 216, none new.

*Effect* (`twins_filter.has_claw`, `gamma_claw`; they agree on all 502,638 β = 5 candidates):

| β = 5, n | 6 | 7 | 8 | 9 | 10 | 11 | 12 | total |
|---|---|---|---|---|---|---|---|---|
| after K4.MC8 | 20,882 | 78,118 | 152,568 | 156,162 | 78,616 | 15,621 | 671 | 502,638 |
| after K4.MC9 | 20,553 | 72,166 | 119,387 | 85,351 | 21,482 | 1,393 | 16 | 320,348 |

Lists `results/k4_twins/mc_n<n>_b5_mc9.json.gz`, log `results/k4_twins/count_b5_mc9.log`. β = 4: 3,166 → 2,079.

*Bound.* K4.MC4's n ≤ 3(β − 1) is still attained by the counting: its extremal case can have t = 0 (every shared good
of degree 2: Q4 agents with four P3 neighbours, E3 agents with one), where claws do not occur. With claws excluded, the
count gives A ≤ 2t; the bound improves to n ≤ (8/3)(β − 1) only for cores without Q4 agents. Moving it in general needs
the Q4 stars (a Q4 agent sharing goods of degree 2 with two or more P3 agents).

## Reproduce

```
cd k4
python3 twins4.py certify dbl-Q3-Q3 dbl-Q3-Q3-c1 dbl-Q3-P4 dbl-Q3-P4-c1 dbl-Q3-Q4 dbl-Q3-Q4-c1 --zs=0,1 --jobs=1 \
    --write=../results/k4_twins/dbl_q3.json.gz                                   # ~30 s
python3 check_twins4.py ../results/k4_twins/dbl_q3.json.gz --jobs=1 --expect=dbl-Q3-Q3:36 --expect=dbl-Q3-Q3-c1:36 \
    --expect=dbl-Q3-P4:1728 --expect=dbl-Q3-P4-c1:1728 --expect=dbl-Q3-Q4:1708 --expect=dbl-Q3-Q4-c1:1728 \
    --uncovered-out=../results/k4_twins/dbl_q3_uncovered.json                   # ~10 s
python3 check_twins4.py ../results/k4_twins/dbl_q3.json.gz --jobs=1 --selftest
python3 twins4.py certify dbl-P4-P4-c1 dbl-P4-Q4-c1 dbl-Q4-Q4-c2 dbl-Q4-Q4-c1 dbl-P4-P4 dbl-P4-Q4 dbl-Q4-Q4 --zs=0,1 \
    --jobs=4 --write=../results/k4_twins/dbl_p4q4.json.gz                       # ~30 min on 4 CPUs (dbl-Q4-Q4 most)
python3 check_twins4.py ../results/k4_twins/dbl_p4q4.json.gz --jobs=4 --expect=dbl-P4-P4:82944 --expect=dbl-P4-P4-c1:82944 \
    --expect=dbl-P4-Q4:81944 --expect=dbl-P4-Q4-c1:82944 --expect=dbl-Q4-Q4:50392 --expect=dbl-Q4-Q4-c1:71512 \
    --expect=dbl-Q4-Q4-c2:80152 --uncovered-out=../results/k4_twins/dbl_p4q4_uncovered.json   # ~5 min
python3 check_twins4.py ../results/k4_twins/dbl_p4q4.json.gz --jobs=4 --selftest
python3 twins4.py explore twins-Q3-0 twins-Q3-1 twins-P3 claw tri-Q3-Q3-Q3      # the explored configurations
python3 twins4.py why twins-Q3-0                                                # a failing state per reduction
python3 twins_filter.py ../results/k4_min_cex_shapes_4.json.gz                  # candidates without a certified double edge
for n in 6 7 8 9 10 11 12; do python3 twins_count.py $n 5 --write=../results/k4_twins/mc_n${n}_b5_mc8.json.gz; done
                                                                                # beta = 5 lists; n = 12 ~1 h, the rest < 20 min
python3 twins_count.py 8 5 --no-mc8                                             # a baseline without K4.MC8 (~10 min, ~6 GB)
python3 twins4.py claw2 --jobs=1                                                # the two-agent copy gadget, block search (~15 min)
gcc -O2 -o /tmp/reduce4c_bin reduce4c.c && python3 reduce4c.py test             # C search vs reduce4, ~2 min
python3 twins4.py certify2 claw --zs=1 --write=../results/k4_twins/claw.json.gz          # ~12 min on 4 CPUs
python3 twins4.py certify2 claw-y12 --zs=1,2 --write=../results/k4_twins/claw_y12.json.gz # ~2 min
python3 twins4.py certify claw-y123 --zs=0,1 --write=../results/k4_twins/claw_y123.json.gz
python3 check_twins4.py ../results/k4_twins/claw.json.gz --expect=claw:216; python3 check_twins4.py ../results/k4_twins/claw.json.gz --selftest
python3 check_twins4.py ../results/k4_twins/claw_y12.json.gz --expect=claw-y12:216
python3 check_twins4.py ../results/k4_twins/claw_y123.json.gz --expect=claw-y123:216
python3 twins_filter.py ../results/k4_min_cex_shapes_4.json.gz ../results/k4_twins/dbl_q3_uncovered.json \
    ../results/k4_twins/dbl_p4q4_uncovered.json                                  # also the domain cuts (profile counts)
```
