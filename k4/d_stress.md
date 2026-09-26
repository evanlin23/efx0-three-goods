# Stress test of K4.D (the D2 shape) on large structured cores of 4-good agents

Workstream `compute/k4-d-stress`. Ledger rows `K4.DS.*`, all EVIDENCE. Random and hill-climbed value profiles on fixed
structures, where every single decision is exact (SAT) and every witness is re-checked by the raw definition.

**Question.** Does the D2 shape of K4.D survive on large structured instances made of many 4-good agents? K4.D says
every strict k = 4 core has an EFX₀ allocation with at most one bundle of more than two goods. The instances include
the cores H_t of `k4/c4.md` §7, on which LB₄ʳ at index order fails for t ≥ 5 (PR #33).

**Answer (evidence).** Yes, on every structure tried: 21 structures, all agents 4-good, n up to 29, m up to 73, β up to
21.
- **5,400 random strict profiles:** every one has a D2 EFX₀ allocation. Every witness was re-checked by the raw
  definition and the D2 shape as it was found (5,407 with the 7 paper values). The 5,400 random-profile witnesses are
  committed, and `d_stress_check.py FILE` re-checks them from the files (§1).
- **Paper values:** the values of H_t in `k4/c4.md` §7 (t ≤ 7) have one too. That section already gives an explicit D2
  allocation for them, raw-checked for t ≤ 8 by `k4/c4_chain.py`, and row K4.HALL.HT (`k4/hall.md`, PR #46)
  proves K4.D on every H_t at these values with another one. They each have at least 32 D2 allocations (the
  counting cap). For H_1 the exact number is 2,126, by the plain enumeration `k4/d_stress_brute.c` (no SAT;
  `results/k4_dstress_verify.log`), which matches the reviewer's own count.
- **No counterexample**, so nothing is REFUTED.

The owner-count margin (§3) is informative only on H_1 and H_2, where it is 4 of 5 and 9 of 9. On the pure cores it is
n, because every pure-core profile checked has an EFX₀ allocation with all bundles ≤ 2 (§2).

## 1. Method

**Instances.** A structure is a hypergraph (every agent's goods). It must be a k = 4 core: `check4.is_core`
(connected, 3 or 4 goods per agent, at most d − 2 private goods). A profile gives each agent one type from
`search4.domain`: strictly balanced, strict, and p + q < s + t for two private goods. That is, a strict core profile.

**Decision** (`k4/d_stress.py`). search4.Core's SAT model, built fresh for each profile with every agent's domain fixed
to its one type, model D2 ("at most one bundle with more than 2 goods"). One SAT call decides a profile. Every
allocation returned is re-checked by `d_stress_check.raw` (the plain EFX₀ definition) and by the shape. The logs
report the number of witnesses re-checked, and the witnesses are in `results/k4_dstress_witnesses/*.json.gz` (sets,
values, allocation). The runs are deterministic, so the same commands reproduce the same profiles.

**Witness files** (`results/k4_dstress_witness_check.log`). `d_stress_check.py FILE` reads a witness file. For every
record it checks three things: the values are a strict core profile (one type of `search4.domain` per agent), the
allocation is EFX₀ by the raw definition, and it has the D2 shape. All 5,400 records pass. `d_stress_verify.py corrupt` (`results/k4_dstress_verify.log`)
tests this checker. An intact copy of three records passes. Four copies, each with one corrupted record, are all
rejected: a shifted allocation, a value vector outside the domains, every good in one bundle, and an allocation missing
a good.

With `--decide` it also decides each profile with the second encoding (below, solved by CaDiCaL). With a 600 s
limit per file, that encoding found D2 satisfiable in 5,100 of the 5,400 profiles: every file except tree 5,
chain 2 with 3 heads, and chain 7 (300 profiles), which hit the limit. An earlier pass with glucose4 did not finish
H_3 in 17 minutes; on one tree 3 profile glucose4 took 157 s
and CaDiCaL 0.1 s.

**Provenance.** The random-profile logs name commit bd5cb4d without an "uncommitted changes" flag. They were run
with the code later committed as 78a81fa, before it was committed, and the commit printer of that working tree did not
yet flag uncommitted changes. 78a81fa adds only docstrings, that flag, and `d_stress_check.py`'s file mode and
self-test change; the decision code is the same.

`d_stress_verify.py reproduce` reruns three of these runs at feee6c9: chain 2, cycle 3 and pure 6 8. Their output is
identical to the logged blocks (commit line dropped, timings masked), and their witnesses are identical to the
committed files (`results/k4_dstress_verify.log`). The check logs name 78a81fa, af85fd1 (the second encoding solved by CaDiCaL)
or later commits.

**Second encoding** (`k4/d_stress_check.py`, written from scratch). pysat, with:
- an owner per good;
- reified "more than 2 goods" indicators, at most one of them;
- EFX₀ as forbidden patterns derived directly from v_i(X_i) ≥ v_i(X_j) − v_i(g), with a forced "X_j holds a good
  outside R_i" indicator.

The encodings are independent, but since af85fd1 the solver is shared. The second encoding is solved by CaDiCaL 1.5.3
(pysat's `cadical153`), which is also the solver search4's model uses (`cd15`). The owner climbs and the self-test
entries before af85fd1 used glucose4.

Its self-test (`results/k4_dstress_check_selftest.log`) compares the two encodings on random profiles of:
- pure 3 5, pure 4 7 and pure 6 8 (random hypergraphs built with `Random(5)`, not the table's pure cores);
- H_1 (150 profiles), H_2, H_3 and tree 3 (30 each).

It compares them both for D2 and for "all bundles ≤ 2". The two agree everywhere.
- D2 was satisfiable in every self-test profile (`d_stress_verify.py replay` replays the streams with `d_stress.py`,
  `results/k4_dstress_verify.log`), so the D2-unsatisfiable direction has not been cross-checked on a real instance.
- The unsatisfiable agreement is on "all bundles ≤ 2": trivial on the chains (m > 2n) and non-trivial in 4 cases.
- For m > 2n "all bundles ≤ 2" is unsatisfiable by counting, and its SAT calls are pigeonhole-hard. The first runs
  on H_1 and H_2 made them anyway. The code now skips them, so H_3, tree 3 and the reruns compare D2 only.
- The first five entries of the log predate the commit printer. All seven self-tests were rerun at feee6c9 (appended),
  with the same results.
- The self-test profiles are not among the 5,400. Each of those is backed instead by its raw-checked witness.

**Margin.** `owners(profile)` (second encoding, one solver, assumptions per candidate owner) is the set of agents that
can own the large bundle in some D2 allocation. It is empty iff D2 fails. `--owners=STEPS` hill-climbs profiles (one
or two agents' types changed per step, accepted if not worse) toward fewer owners. Owner infeasibility comes from this
one encoding only, except on H_1. There `d_stress_verify.py brute` counts every D2 EFX₀ allocation by owner with
`k4/d_stress_brute.c`, a plain enumeration with no SAT, at the paper values and at the three logged climb minima. At
all three minima it finds the same owner sets as the second encoding. At the 4-of-5 minimum, y_1 (agent 4) owns
none of the 418 D2 EFX₀ allocations (`results/k4_dstress_verify.log`).

## 2. Families

- **chain t:** H_t of `k4/c4.md` §7. A head ℓ = {g_1, z, u, u′}, then t gadgets. Gadget j has three x's
  {a_{j,i}, b_{j,i}, c_{j,i}, g_j} and a y {a_{j,1}, a_{j,2}, a_{j,3}, e_j}, with e_j = g_{j+1} and e_t = z.
  n = 4t + 1, m = 10t + 3. At the paper values, `chain(t)` is isomorphic to H_t as built by `k4/c4_chain.py`, with agents and goods
  relabelled and every value kept. `d_stress_verify.py iso` checks this for t ≤ 8 with networkx (`results/k4_dstress_verify.log`).
- **chain t h:** h heads, each with its own chain of t gadgets, all chain ends linked to the shared good z.
- **cycle t:** gadgets only, in a cycle: e_j = g_{(j+1) mod t}, no head. A pure core with n = 4t, m = 10t. The
  version of commit afc888c built H_t itself (review item B1). It is replaced, and its runs are dropped.
- **tree t:** gadgets in a binary tree (heap order). Gadget j's y links to its first child's g; a leaf's y links to
  the root good z. A second child is joined to g_j by a head-like agent {g_j, g_child, p, q}.
- **pure n m:** one random connected pure core per (n, m), fixed by its seed and printed in the log. Every agent is
  4-good, m is small, so β = 3n − m + 1 is high (11 to 21). Since m < 2n, the large bundle is not forced there by
  counting. m < 2n does not by itself imply an EFX₀ allocation with all bundles ≤ 2. But one exists in every
  pure-core profile checked: the 2,400 random ones and the 12 logged climb minima, 2,412 in all
  (`d_stress_verify.py small`, second encoding, raw-checked, `results/k4_dstress_verify.log`). So these profiles do not exercise
  the large bundle.

## 3. Results

Random profiles (`results/k4_dstress_{chain,cycle,tree,pure}.log`, witnesses in `results/k4_dstress_witnesses/`):

| structure | n | m | β | random profiles | without D2 |
|---|---|---|---|---|---|
| chain 1 (H_1) | 5 | 13 | 3 | 500 | 0 |
| chain 2 (H_2) | 9 | 23 | 5 | 400 | 0 |
| chain 3 | 13 | 33 | 7 | 300 | 0 |
| chain 4 | 17 | 43 | 9 | 200 | 0 |
| chain 5 | 21 | 53 | 11 | 120 | 0 |
| chain 6 | 25 | 63 | 13 | 80 | 0 |
| chain 7 | 29 | 73 | 15 | 60 | 0 |
| chain 2, 2 heads | 18 | 45 | 10 | 200 | 0 |
| chain 2, 3 heads | 27 | 67 | 15 | 120 | 0 |
| cycle 2 | 8 | 20 | 5 | 300 | 0 |
| cycle 3 | 12 | 30 | 7 | 200 | 0 |
| cycle 4 | 16 | 40 | 9 | 150 | 0 |
| tree 3 | 14 | 35 | 8 | 250 | 0 |
| tree 5 | 23 | 57 | 13 | 120 | 0 |
| pure 6 8 | 6 | 8 | 11 | 500 | 0 |
| pure 7 9 | 7 | 9 | 13 | 500 | 0 |
| pure 8 10 | 8 | 10 | 15 | 400 | 0 |
| pure 9 12 | 9 | 12 | 16 | 300 | 0 |
| pure 10 13 | 10 | 13 | 18 | 300 | 0 |
| pure 11 15 | 11 | 15 | 19 | 200 | 0 |
| pure 12 16 | 12 | 16 | 21 | 200 | 0 |

**Owner climbs** (`results/k4_dstress_climbs.log`, from commit afc888c).
- **H_1:** 3 climbs of 60 steps, minimum **4 of 5** feasible owners. This is exact: the brute force (§1) finds no D2
  EFX₀ allocation owned by y_1 at that profile.
- **H_2:** 4 climbs of 20–30 steps (two of them logged as "cycle 2", which was H_2 then), **9 of 9**. The traces are
  flat.
- **Pure cores (n = 6–10):** the count stayed at n, but for a trivial reason. In every profile checked, including all
  12 logged climb minima, an EFX₀ allocation with all bundles ≤ 2 exists (§2), so every agent is a feasible owner.
  This is an empirical finding: m < 2n alone does not imply it.
- **H_3 and tree 3:** the climbs were stopped before finishing.

So there is no evidence here about how the margin behaves as n grows.

**Counts.** Counting D2 allocations with blocking clauses gives no gradient on these structures. The logged counts are
the paper values of H_1–H_7, each at least 32 (the cap). The count-based climbs of the first exploratory run were not
committed, and no claim rests on them.

*All profiles.* H_1 is a pure n = 5 core, so K4.R5p already certifies D2 on it under every strict profile. H_2 has 7
agents with two private goods (144 types each) and 2 y's (288 each), so 144⁷ · 288² ≈ 1.06·10²⁰ profiles. Exhaustive
certification was not attempted.

## 4. What this does and does not show

- It is EVIDENCE (PROMPT.md §5 rule 3). Random profiles miss rare failures: at k = 3, some failures occurred in 1 of
  23,000 profiles.
- On the chains, cycles and trees (m > 2n) the large bundle is forced, and D2 held in every one of the 3,000 random
  profiles there. The 2,400 pure-core profiles do not exercise the large bundle (§2).
- LB₄ʳ's failure on H_t (PR #33) is a failure of that construction's bounded rotations, not of the D2 shape.
- Not done (handoff, also LEDGER open item 20):
  - gadgets of other sizes and shapes, and gadgets sharing goods;
  - exhaustive certification beyond n = 5;
  - an owner metric that counts an owner only when its bundle can have more than 2 goods, climbed on H_3+, the trees
    and the multi-head chains;
  - an adversarial objective with a real gradient, such as the least size of the large bundle versus m − 2n + 2;
  - pure cores with m > 2n.

## Reproduce

```
cd k4
python3 d_stress.py chain 7 --values=paper --profiles=60 --seed=7 --witnesses=OUT.json.gz   # one table row; commands in the logs
python3 d_stress.py cycle 3 --profiles=200 --seed=21
python3 d_stress_check.py --selftest chain 2 30                                              # the two encodings agree
python3 d_stress_check.py ../results/k4_dstress_witnesses/chain_7.json.gz                    # re-check committed witnesses
python3 d_stress_verify.py brute                                                             # H_1 by plain enumeration
```
