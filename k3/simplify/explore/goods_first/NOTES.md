# Goods-first and envy-graph algorithms for EFX₀ with at most three goods per agent

Exploration on branch `proof/k3-simplify` (parent: K3S, `proofs/k3_simple.md`). Question: is there an algorithm
simpler than K3S, ideally without K3S's repair step (the rotation along a need chain), that processes goods or uses
the envy graph? **Everything here is evidence, not proof.**

**Verdict.**
- Every pure goods-first rule fails at n ≤ 3: Lipton's envy-cycle elimination with any good order or source rule,
  picking sequences by envy-graph sources, and "each good to its top valuer".
- So does every "one good each, then place the leftovers" rule, with or without the envy graph, because the picks
  themselves must sometimes change (the instances where K3S rotates).
- One envy-graph rule survives every test: **EP** (§2). It uses K3S's draft, then the "envy the pool" swap of the
  little-charity algorithm (an agent that prefers a set of unallocated goods to its bundle takes a minimal such set
  and returns its bundle), then places the remaining goods one at a time: valuers first, otherwise with a source of
  the envy graph, always checking EFX₀.
- EP has no HitSet, no exposed or free agents, and no need-chain rotation: the swap cascade does the rotation's
  job. 0 failures on 4.3 million profiles and instances (§3).
- Its correctness is **open**. Step 1 is proved to keep EFX₀ and to end. The missing piece is that step 2 always
  finds a source (§4). Both simplifications run in full fail: one absorber instead of 2(b), and EP′ (no peel
  priority plus upgrades only). Three single changes passed the screen up to n = 4, m = 5 but were not run in full.

Code (this folder; single process; run from this folder):
- `common.py`: EFX₀ threat function, envy graph, cycle rotation (F2 of `proofs/lemmas.md`), sources, the test suites,
  and `explain` (who is unsafe and why).
- `algos.py`: the candidate families (envy-cycle elimination, source picking, draft plus envy-graph leftovers,
  top-valuer assignment, envy-the-pool).
- `ep.py`: the surviving candidate EP, written as a self-contained statement, with switches for the ablations.
- `screen.py` (stop at the first failing set), `full.py` (the whole protocol), `bigrun.py` (n = 6 cores, random
  n ≤ 9), `allprof.py` (every labelling of the goods), `stats.py` (EP's steps against K3S's rotation).
- Logs: `logs/`.

Test protocol (values (4, 3, 2), raw EFX₀ check `k3s.efx0`):
1. every ranking profile of `test_k3s.gen_small(n, m)` for (n, m) in (2, 3..6), (3, 4..7), (4, 5..6);
2. `lbx.core_profiles(5, sample=200, minn=5)` (61,400 profiles of n = 5 cores), with the three balanced
   realizations (4, 3, 2), (10, 9, 2), (10, 6, 5);
3. random ranking profiles with n ≤ 8 and random general instances with n ≤ 8 (values 1–6: ties, top-heavy agents,
   a = b + c, agents valuing 0–3 goods).

## 1. Results in one table

"Smallest failure" is the first failing profile in the order of the protocol (smallest n, then m). Every row up to
"Envy the pool with draft priority" is reproduced by `logs/screen_families.log` (32 variants; run `python3 screen.py`
with the expressions printed after each `==`); the EP rows by the logs named in §3.

| Candidate | First failing set: failures / profiles | Smallest failure (rankings a ≻ b ≻ c) |
|---|---|---|
| Lipton envy-cycle elimination, goods by index, to the source valuing the good most | n=3, m=4: 81 / 576 | (0,1,2) (0,2,1) (0,2,3) |
| the same, but a source (else any agent) for which EFX₀ is kept, goods by index | n=3, m=4: 83 / 576 | (0,1,2) (0,3,1) (0,3,1) |
| … goods by number of valuers, decreasing | n=3, m=4: 42 / 576 | (0,1,2) (0,3,1) (0,3,2) |
| … goods by number of valuers, increasing | n=3, m=4: 205 / 576 | (0,1,2) (0,1,2) (0,1,3) |
| … goods by (#agents ranking it first, second, third), or by best rank among valuers (4 source rules) | n=2, m=4: 1 / 24 | (0,1,2) (0,3,2) |
| … goods least-important first | n=2, m=3: 4 / 6 | (0,1,2) (0,1,2) |
| Picking sequence: a source of the envy graph picks its favourite good (4 tie rules, EFX₀-kept check) | n=3, m=5: 106–138 / 3,600 | (0,1,2) (0,3,1) (0,3,4) |
| … without the EFX₀-kept check | n=2, m=4: 4 / 24 | (0,1,2) (3,0,2) |
| Each good to a valuer ranking it highest (ties: index / fewest goods), worthless goods to a source | n=2, m=3: 2 / 6 | (0,1,2) (0,1,2) |
| K3S's draft or serial dictatorship (one good each), then leftovers in index order, each to an agent keeping EFX₀ (5 rules) | n=2, m=4: 1 / 24 | (0,1,2) (0,3,2) |
| … leftovers ordered by number of valuers | n=3, m=5: 46 / 3,600 | (0,1,2) (0,3,1) (0,3,4) |
| K3S's draft, then greedy placement (valuer moves first, then sources) | n=3, m=5: 42 / 3,600 | (0,1,2) (0,3,1) (0,3,4) |
| Envy the pool without draft priority (envier by index, poorest, last, peelable first), placement good by good | n=3, m=5: 24–58 / 3,600 (n=2, m=5: 4 / 60 with "non-valuer first") | (0,1,2) (1,2,4) (0,1,2) |
| Envy the pool with draft priority (or poorest envier first), placement good by good | n=3, m=6: 24 / 14,400 | (0,1,2) (1,3,5) (0,3,1) |
| EP with ONE absorber (envy the pool, draft priority, valuer moves, then one source takes all) | n=4, m=6: 1,632 / 1,728,000; n=5 cores: 22 / 61,400 | (0,1,2) (0,3,1) (4,2,3) (0,4,1) |
| **EP (envy the pool, draft priority, valuer moves, then each good to a source)** | **none** (§3) | — |
| EP′ = EP without peel priority and with upgrades only | 2 of 20,000 random profiles n ≤ 8 (0 on every canonical small profile and the n = 5 cores) | (3,1,4) (0,4,1) (3,0,1) |

Explanations of the smallest failures (each checked with `common.explain`):
- **Envy-cycle elimination**, n = 3, m = 4, (0,1,2) (0,2,1) (0,2,3): output {0}, {1, 2}, {3}. Agent 2 holds its c (3)
  and needs 2 alone, but 2 sits with 1: v₂({1, 2} ∖ {1}) = 3 > 2. Lipton's rule gives a good to an unenvied
  agent, but "unenvied" is not "nobody needs its good alone" once the bundle grows.
- **Top-valuer**, n = 2, m = 3, both 0 ≻ 1 ≻ 2: agent 0 gets {0, 2} (it ranks 2 no lower than agent 1); agent 1 holds b
  and needs 0 alone.
- **Goods to sources by best rank**, n = 2, m = 4, (0,1,2) (0,3,2): output {0}, {1, 2, 3}. Agent 0 holds a and its b, c
  (1, 2) are together in a bundle of three goods. This is the core of `attempts/peel_insert_dump.md`: the right
  answer is {0, 1}, {2, 3}, i.e. agent 1 must take its b and c *before* good 1 is placed.
- **Source picking**, n = 3, m = 5, (0,1,2) (0,3,1) (0,3,4): agent 0 picks 0, agent 1 picks 3, agent 2 picks 4 (its c);
  goods 1, 2 (agent 0's b and c) are left and no agent can take either without breaking agent 0, 1 or 2. None of
  the 7 EFX₀ allocations gives 0 to agent 0, which took it first (brute force; K3S rotates here). So any method
  that keeps the one-good-each picks fails here.
- **K3S's draft plus any placement of the leftovers**: the same instance. The picks are wrong, so no placement rule
  can work (compare `attempts/k3s-two-absorbers.md`).
- **Envy the pool without draft priority**, n = 3, m = 5, (0,1,2) (1,2,4) (0,1,2): agent 0 takes 0, then agent 0 (holding
  only its top, with b and c in the pool) already "envies" the pool, and the minimal envied set {1} goes to agent 1,
  before agent 2 (which has lost its top) can take 1. Agent 2 ends with its c, and agent 1's c (4) has nowhere to go.
- **Envy the pool, placement good by good**, n = 3, m = 6, (0,1,2) (1,3,5) (0,3,1): good 2 is placed (as junk with
  agent 1) before good 5, and then agent 1's c (5) can go nowhere. Placing 5 first (agent 1 takes it) works:
  valuer moves must come before junk placement, as K3S's upgrades come before its absorber.
- **EP with one absorber**, n = 4, m = 6, (0,1,2) (0,3,1) (4,2,3) (0,4,1), good 5 worthless: the draft gives 0, 3, 4, 1
  and leaves {2, 5}; nobody envies the pool and no valuer can take 2 (agents 0 and 2 hold goods that agents 1 and
  3 need alone). The sources are agents 1 ({3}) and 3 ({1}). Agent 1 absorbing breaks agent 2 (its b = 2, c = 3 in
  {2, 3, 5}); agent 3 absorbing breaks agent 0 (b = 1, c = 2 in {1, 2, 5}). Splitting works: {2, 3} and {1, 5}, which
  is K3S's output (HitSet puts 2 with the free agent 1, r = 3 absorbs 5). So one absorber without HitSet is not
  enough, even after the pool swaps.

## 2. The candidate EP

`ep.py`, `ep(n, m, v)` (defaults: `place='greedy'`). State: bundles X₁…Xₙ (initially empty) and the pool P
(initially all goods). "i envies S" means v_i(S) > v_i(X_i). Before every step, rotate envy cycles (F2 of
`proofs/lemmas.md`) until the envy graph is acyclic.

> **EP**
> 1. **Draft and swaps.** While some agent envies P:
>    - (a) if an agent with an empty bundle envies P: the first such agent that can be peeled (its favourite pool good
>      is worth at least its other pool goods together), else the first such agent, takes its favourite pool good;
>    - (b) else, if some agent prefers a single pool good to its bundle: the first such agent takes its favourite
>      pool good and puts its old bundle back into P;
>    - (c) else the first agent that envies P takes the shortest prefix of its ranking (within P) that it envies,
>      and puts its old bundle back into P. With three goods this is: an agent holding only its top a, whose b and c
>      are both in P, trades a for {b, c}.
> 2. **Placement.** While P is non-empty:
>    - (a) if some agent values a pool good and can add it to its bundle keeping EFX₀, the agent for which that good
>      is best ranked does so (ties: smallest agent, then smallest good);
>    - (b) otherwise the smallest pool good goes to the first source of the envy graph for which EFX₀ is kept.

Step 1(a) is K3S's draft (peelable agents first, otherwise a leader by index). Steps 1(b) and 1(c) are the move of
the "little charity" algorithm of Chaudhury, Kavitha, Mehlhorn and Sgouritsa ([unverified]: we have not read that
paper here; the move and its invariant are re-proved in §4). An agent that envies the pool takes a *minimal* envied
set and returns its old bundle. When an agent holding its top a trades a for {b, c}, a returns to the pool. The agent
that wants a most takes it via 1(b), its old good returns to the pool, and so on. That cascade is a need chain, so
step 1 does the job of K3S's rotation. It fires whenever a leader's b and c are both left over, not only when
HitSet does not fit. Step 2(a) contains K3S's upgrades. Step 2(b) is the junk lemma L3 applied one good at a time,
with an EFX₀ check because the goods are not junk. Step 2(b) also does what HitSet does: it puts a protecting good
with a source other than the one that gets the rest.

**Variant EP′** (`ep(..., peel=False, up='bc')`, *fails*, §3): step 1(a) without peel priority (so step 1 starts as
plain serial dictatorship in index order), and step 2(a) only for an agent holding exactly its second good, which
takes its third (K3S's upgrade, with an EFX₀ check instead of "nobody needs b alone"). Each of the two changes alone
passed the screen up to n = 4, m = 5, but together they fail on a random profile. So peel priority (or the general
valuer move) is doing real work.

What EP removes from K3S: leaders, blocks, "free" and "exposed" agents, HitSet, the absorber r, and the need-chain
rotation. What it adds: a "check EFX₀ before adding a good" test (a local test of one bundle against every agent) and
cycle rotation. The check itself is how K3S's conditions are discharged. "Nobody needs b alone" and "free" are what
the check amounts to for the bundles in question.

## 3. Results for EP

Commands (from this folder): `python3 full.py "epv('greedy')"`, `python3 bigrun.py "epv('greedy')" 30 100000 11`,
`python3 allprof.py "epv('greedy')" 2 3 2 4 2 5 2 6 3 4 3 5 3 6`, `python3 stats.py small 3 6`, `python3 stats.py core5`.

| Test (EP, defaults) | Profiles or instances | Failures | Log |
|---|---|---|---|
| every ranking profile, (2, 3..6), (3, 4..7), (4, 5..6), agent 0 fixed to 0 ≻ 1 ≻ 2 | 2,006,886 | 0 | `logs/full_ep_greedy.log` |
| n = 5 cores, 200 random profiles per core, × 3 realizations | 61,400 | 0 | same |
| random ranking profiles n ≤ 8 / random general instances n ≤ 8 | 20,000 / 20,000 | 0 / 0 | same |
| n = 6 cores, 30 random profiles per core (seed 11), × 3 realizations | 96,210 | 0 | `logs/big_ep_greedy.log` |
| random ranking profiles n ≤ 9 / random general instances n ≤ 9 | 100,000 / 50,000 | 0 / 0 | same |
| every ranking profile with every labelling of the goods, n = 2, m ≤ 6 and n = 3, m ≤ 6 | 1,976,436 | 0 | `logs/allprof_ep_greedy.log` |

**Caveat on "every profile".** `gen_small` fixes agent 0's ranking to 0 ≻ 1 ≻ 2. That is exhaustive only for an
algorithm that does not look at good indices. EP breaks ties by good index (2(a) ties, and 2(b) takes the smallest
pool good first), so different labellings are different runs. EP′ shows that this matters: it passes every
canonical profile but fails on a relabelling found by the random test. `allprof.py` covers every labelling for
n ≤ 3, m ≤ 6.

**Ablations: which parts are needed.** Screened with `screen.py` or `full.py` (logs `screen_ep_variants.log`,
`screen_ep_ablation.log`, `screen_ep_greedy_ablation.log`, `full_ep_onesource.log`, `full_ep_greedy_sd_bc.log`).
"Passes to (4, 5)" means every canonical profile up to n = 4, m = 5, with nothing larger run.

| Change to EP | Result | Smallest failure |
|---|---|---|
| no swaps 1(b), 1(c) (K3S's draft, then step 2) | n = 3, m = 5: 42 / 3,600 | (0,1,2) (0,3,1) (0,3,4) |
| no cycle rotation | n = 3, m = 5: 84 / 3,600 | (0,1,2) (0,3,1) (0,3,1) |
| no 2(a) (all pool goods by 2(b)) | n = 3, m = 6: 12 / 14,400 | (0,1,2) (1,3,5) (0,3,5) |
| 2(b) replaced by ONE source taking all of P (first source that keeps EFX₀) | n = 4, m = 6: 1,632 / 1,728,000; n = 5 cores 22 / 61,400; random 1 / 20,000 | (0,1,2) (0,3,1) (4,2,3) (0,4,1) |
| … with a fixed absorber: first source / last source / most recent bundle / K3S-like r | n = 3, m = 5: 168 / 60 / 212 / 80 | (0,1,2) (0,1,3) (0,4,1) and others |
| … and no peel priority / upgrades only / no 2(a) | n = 3, m = 5: 32; n = 2, m = 4: 8; n = 2, m = 4: 12 | (0,1,2) (1,0,2) for upgrades only |
| no peel priority in 1(a) | passes to (4, 5) | — |
| 2(a) only for an agent holding exactly b, taking c (K3S's upgrade) | passes to (4, 5) | — |
| 2(b) to any agent, not only a source | passes to (4, 5) | — |
| EP′: no peel priority **and** upgrades only | every canonical profile incl. (4, 6) and the n = 5 cores pass; 2 / 20,000 random profiles fail | (3,1,4) (0,4,1) (3,0,1) |

EP′'s failure, n = 3, m = 5, rankings (3,1,4) (0,4,1) (3,0,1), good 2 worthless: serial dictatorship gives 3, 0, 1.
2(b) puts the worthless good 2 with the only source, agent 2 ({1, 2}), and then good 4 (agent 1's b, agent 0's c)
fits nowhere: {1, 2, 4} holds both agents' b and c, and agents 0 and 1 hold goods that agent 2 needs alone. With peel
priority, agent 2 (which lost 3) picks 0 before agent 1, and EP returns K3S's allocation {3}, {1, 4}, {0, 2}.

**How often each step is used** (`stats.py`, log `logs/stats_ep.log`):

| Set | Profiles | swap 1(c) fired | swap 1(b) fired | valuer move 2(a) | pool goods to ≥ 2 agents | 2(b) needed a non-source | K3S rotates | K3S rotates and 1(c) fired |
|---|---|---|---|---|---|---|---|---|
| every canonical profile n = 3, m = 5 | 3,600 | 1,200 | 268 | 3,200 | 92 | 0 | 154 | 42 |
| every canonical profile n = 3, m = 6 | 14,400 | 8,100 | 1,800 | 13,458 | 774 | 0 | 462 | 210 |
| n = 5 cores (200 per core), values 4, 3, 2 | 61,400 | 21,124 | 6,807 | 45,437 | 1,447 | 0 | 817 | 674 |

So EP's swap 1(c) fires far more often than K3S's rotation (it fires whenever a leader's b and c are both left over),
and some instances on which K3S rotates are solved by EP without 1(c), by splitting the pool over two sources.
Step 2(b) never needed a non-source.


## 4. What is proved, and a proof plan

Proved (short, for any additive instance; written here, not refereed):
- **Step 1 keeps EFX₀ and ends.** Rotation keeps EFX₀ (F2). In 1(a) and 1(b) a singleton is created (θ = 0 for
  everyone). In 1(c), 1(b) did not fire, so nobody envies a single pool good. The taker i holds a bundle it values
  (every non-empty bundle has positive value to its holder: it was taken or rotated in by envy). So at most two of
  its goods are in P, Z has at most two goods, and Z minus any one good is a single pool good, which nobody envies.
  Hence θ_j(Z) ≤ v_j(X_j) for every j. The taker's value rises and no other bundle changes. So every step and every
  rotation raises some agent's value and lowers none. Each agent's value takes at most 2³ levels, so step 1 has
  O(n) steps. At its end nobody envies P.
- **Step 2 keeps EFX₀**: every addition is checked, and rotations keep it. It also keeps "nobody envies P": bundles
  only grow and rotations only raise values, while P shrinks. The only way EP can fail is that 2(b) finds no source
  (the code then falls back to any agent, and marks a failure if none works). On every test, 2(b) always found a
  source (counts in §3).
- **Consequences of "nobody envies P"** for a strict agent i (a ≻ b ≻ c, a < b + c): if i holds only a (among its
  goods), at most one of b, c is in P; if it holds b, then a ∉ P; if it holds c, then a, b ∉ P; if it holds none of its
  goods, none is in P.
- **When can a source s take a pool good g?** (strict agents). Non-valuers of g are fine, because s is a source:
  θ_i(X_s ∪ g) ≤ v_i(X_s) ≤ v_i(X_i). For a valuer i of g:
  - if i holds b with g = c, it is at risk only if a ∈ X_s, but then i envies s, so s would not be a source;
  - if i holds b and c, or holds a and one of b, c, its threat is below its value;
  - if i holds only a among its goods (g ∈ {b, c}), the threat is v(b) + v(c) > v(a) exactly when the other good h of
    {b, c} is in X_s and X_s ≠ {h}.

  So: **s can take g iff no agent i holding exactly its top a (among its goods), with g ∈ {b_i, c_i}, has the other
  one in X_s while X_s has a second good.** An agent with an empty bundle can always take g.
- **A blocked exposed agent with a singleton bundle is not a source.** Let i hold X_i = {a_i}, with g ∈ P one of its
  b, c. If step 2(a) did not let i take g, some j has θ_j({a_i, g}) > v_j(X_j). That threat is v_j of the more
  valuable of the two goods (or of the only one j values), and v_j(g) ≤ v_j(P) ≤ v_j(X_j). So v_j(a_i) > v_j(X_j):
  j envies i.

**Open (the whole difficulty):** step 2(b) always finds a source. A failure needs a pool good g and, at every source
s, an a-holder i_s with g ∈ {b, c} of i_s and the other good of i_s in X_s, where X_s has two or more goods. So
every source holds a bundle that has grown: a pair {b, c} taken in step 1(c), an upgrade, or junk from earlier 2(b)
steps. A proof would charge each grown source to the step that grew it, and show that some source is never
charged for g. This is the analogue of Lemma `count` / Theorem A of `paper/k3/long.tex` for K3S's HitSet; the
order of 2(b) (smallest good first) is arbitrary; the all-labellings test (§3) found no labelling, hence no such
order, that fails up to n = 3, m = 6. It is not done.
