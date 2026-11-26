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
- Candidate filter: `k4/twins_filter.py` (structural: does a core contain a certified double edge).

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

The counting bound n ≤ 3(β − 1) of K4.MC4 counts P3 incidences, so K4.MC8 does not change it.

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
| claw (three P3 agents on one good of degree 3) | 216 | 177 |
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
python3 twins_filter.py ../results/k4_min_cex_shapes_4.json.gz ../results/k4_twins/dbl_q3_uncovered.json \
    ../results/k4_twins/dbl_p4q4_uncovered.json                                  # also the domain cuts (profile counts)
```
