# K3S without the rotation: the first leader (exploration notes)

Workstream `proof/k3-simplify`. Scripts are in this folder. Each one runs in one process, from this folder:
`python3 <script>.py <source>`, where `<source>` is `cores N [MINN [SAMPLE]]`, `small N M` or `rand K SEED MAXN`
(`survey.py cases`). This is an exploration, not a ledger item. `LEDGER.md` and `proofs/` are unchanged.

## 0. Summary

- **Not proved:** Conjecture FL, Conjecture LL, and any other rotation-free rule for every n.
- **Proved (short, written proofs, §2, not refereed):** four lemmas, R, NX, FF and TOP. They turn parts of
  Lemma T into checks that can be made when a block ends. Lemma R: if the absorber r is a leader, step 3 succeeds. Lemmas NX and FF: if some leader's b or c
  is taken by an agent of a block that is not the last, or a block that is not the last has two agents that are
  free and can never be upgraded, step 3 succeeds, whatever the later leaders are. With these lemmas, the rule
  `sec_small` (§4) is correct whenever one of its three guarded branches fires.
- **Checked by computer:** Conjecture FL holds for every instance with n ≤ 3 (exhaustive, §3.1). For n = 2, K3S
  never rotates.
- **A stronger form holds on every case tested** (Robust FL, §3.2): some first leader x works whatever the later
  leaders are, even when they are chosen adversarially.
- **Refuted (§3.3):** every natural "named first leader" lemma fails. These are r, x₁, any chain agent other than
  k\*, r or the holder of r's top, a first leader that is itself never exposed, and a first leader that makes r a
  leader. "k\* works when the index run has two leaders" holds on every core with n ≤ 5, but fails on a disjoint
  union with n = 6, m = 10 (§3.4). Idea 1 of the brief
  also fails (§5): no draft run reproduces or dominates the rotated pre-allocation P′. Smallest instance: n = 3,
  m = 5.
- **Best rotation-free rules (§4):** `sec_small` (a deterministic lookahead leader rule) and `iter_r` (index run,
  then rerun with the failed run's r as first leader). Neither ever needed the rotation in the tests below:
  - every core profile with n ≤ 5 (2,445,840 profiles; 33,104 rotation cases for K3S);
  - 962,100 sampled profiles of the n = 6 cores;
  - 1,000,000 random ranking profiles with n ≤ 9;
  - every ranking profile with n = 3 and 5 ≤ m ≤ 7, and with n = 4 and m = 5, 6;
  - 147,432 disjoint unions of two rotation cases.

  Where the branches were traced, `sec_small` always reached a branch that carries a proof (§4). The traced sets
  are every core profile with n ≤ 5, every profile with n = 3 and m = 6, and the rotation cases among 100,000
  random profiles. So in these sets the runs that never needed the rotation are guaranteed, not lucky. In the
  traced sets, `iter_r` needed at most 2 reruns.

## 1. Setting

Rotations happen only on instances where every agent is *strict*: it values exactly three goods, with
a < b + c. By Lemma T, any easy agent makes block 0 non-empty, and then step 3 succeeds for every leader rule.
On a strict instance, K3S's draft depends only on the rankings. An agent can be peeled iff it has lost a good,
and among those that can, the one with the smallest index goes. Goods nobody values never matter for step 3:
they are leftover, they lie in no pair {b_x, c_x}, and no agent needs them. All notions are those of
`proofs/k3_simple.md` §1 and `paper/k3/long.tex` §4:
- *free* means terminal, with one slot;
- E_r is the set of agents exposed for r, with base(r) = {Y_r};
- step 3 *succeeds* iff HitSet(E_r) has at most F entries, where F is the number of free agents other than r.

A *run* is a draft with any sequence of leader choices. The paper's results hold for every order with R1
priority, and Lemma T for every run, so everything below applies to every run.

`fl.py` is a trace-keeping copy of K3S's steps 1–3. `python3 fl.py check` checks it against `k3s.py` on 76,608
profiles: cores n ≤ 4, and every profile with n = 3 and m = 5, 6. On the 2,264 rotation cases among them, every
choice of first leader agrees too.

## 2. Proved lemmas

Fix a run on a strict instance. Its leaders are L₁, …, L_p, its blocks are B₁, …, B_p (block 0 is empty), and
B_p = B\* is the last block.

**Lemma 0 (where r is).** r lies in the last block.
*Proof.* This is the remark after Lemma `r`. The leader of any block after r's block picks its top, so it is not
upgraded, and it is processed after r. That contradicts the choice of r. ∎

**Lemma R (r a leader).** If r is a leader, step 3 succeeds.
*Proof.* As in Lemma T's proof, every block β contains a free agent: z_β, its last agent that is not upgraded.
These agents are distinct, and z_{B\*} = r, so F ≥ p − 1. By Lemma `lead`, E_r consists of leaders, and r ∉ E_r by
the definition of exposure. As r is a leader, |E_r| ≤ p − 1. HitSet(E_r) has at most |E_r| entries, all leftover
goods: π_x ≠ ∅ by Lemma `lead`, so one(z) is junk, and a shared good is junk by definition. So it fits. ∎

When the last block is its leader alone, or its leader plus upgraded agents, r is that leader. This is how the
only working first leader of the instance in §5 succeeds.

**Lemma NX (an unexposed leader).** Suppose some leader L has b_L or c_L either
- picked by an agent other than r (in particular, by an agent of a block other than the last, by Lemma 0), or
- equal to c_u for some u ∈ U.

Then step 3 succeeds.
*Proof.* A pick of an agent other than r is neither junk nor Y_r, because picks are distinct goods. The good c_u
(u ∈ U) is not junk, by the definition of junk, and not a pick, by the definition of a pre-allocation. So
{b_L, c_L} ⊄ J ∪ base(r), and L ∉ E_r. By Lemma T, if r failed, every leader would be exposed. ∎

**Lemma FF (free for good).** Let β be a block other than the last, and let z ∈ β satisfy two conditions at the
moment β ends:
- (i) z has no pick, or no agent of β needs Y_z (that is, ranks Y_z above its own pick, or has no pick and
  values Y_z);
- (ii) Y_z ≠ b_z, or c_z is already picked.

Then z is free at the end of the run, and z ≠ r. If β contains two such agents, step 3 succeeds.
*Proof.*
- z ∉ U. Upgrading z needs Y_z = b_z and c_z ∈ J, and a picked c_z is never junk.
- z is not frozen. Suppose some j ∉ U needs Y_z at the end. By (B2), Y_z was picked by an agent processed before j
  in j's block. That agent is z, so j ∈ β, and j comes after z. The needs of j ∉ U are the goods it ranks above
  Y_j, which was fixed at j's turn, so j already needed Y_z when β ended. This contradicts (i).
- z ≠ r by Lemma 0.
- Two such agents give β two free agents. By Lemma T, if r failed, every block other than B\* would have exactly
  one free agent. ∎

**Lemma TOP (tops are taken).** If step 3 fails, then for every leader L, each of b_L, c_L that is the top of
another agent is Y_r. So if b_x and c_x are both tops of agents other than x, every run in which x leads succeeds.
*Proof.* Let g ∈ {b_L, c_L} with g = a_y, y ≠ L. If g were never picked, y would have found its top available
at its turn and picked it. So g is picked. As L is exposed (Lemma T), g ∈ J ∪ {Y_r}, so g = Y_r. ∎ (This is the
first condition of `provable` in `k3s.py`.)

*Remark.* `mechanism.py` sorts every successful run from a working first leader by the condition of Lemma T that
it breaks. On every rotation case of every core profile with n ≤ 5, there are 128,345 such runs: 4,748 at n ≤ 4
and 123,597 at n = 5, of which 108,528 are single-block. Each success is explained by one of these conditions,
which agrees with Lemma T:
- r is a leader;
- some leader is unexposed through a pick, or through an upgrade good;
- a block other than the last has two free agents;
- the last block has a free agent other than r;
- two exposed agents share a junk good.

No single condition explains all rotation cases. `('nx_up',)` alone occurs 7 times and `('r_leader',)` alone
189 times (`mechanism_cores5.log`).

## 3. Conjecture FL: what holds and what does not

### 3.1 FL holds for n ≤ 3 (exhaustive)

On a strict instance with three agents, at most 9 goods are valued, and the other goods do not matter (§1).
Relabel the goods so that agent 0 ranks 0 ≻ 1 ≻ 2 and the other valued goods are among 3, …, 8.
`survey.py small 3 m`, for m = 4, …, 9, enumerates every such profile, with every ranking for agents 1 and 2, so
every index order is covered.

| m | rotation cases | some first leader works | robust first leader | r works | x₁ works |
|---|---|---|---|---|---|
| 4 | 28 | 28 | 28 | 28 | 28 |
| 5 | 154 | 154 | 154 | 146 | 146 |
| 6 | 462 | 462 | 462 | 438 | 438 |
| 7 | 1,036 | 1,036 | 1,036 | 988 | 988 |
| 8 | 1,960 | 1,960 | 1,960 | 1,880 | 1,880 |
| 9 | 3,318 | 3,318 | 3,318 | 3,198 | 3,198 |

(`fl_n3_exhaustive.log`.) So FL, and Robust FL, hold for every instance with n ≤ 3. For n = 2, K3S never rotates
(`survey.py small 2 m`, m ≤ 6, finds no rotation case). This is a computer check of a finite case analysis, and it
relies on the reduction in §1.

### 3.2 Robust FL (stronger, open)

**Conjecture RFL.** On every instance, some agent x has this property: *every* run with first leader x succeeds,
whatever the later leaders are.

RFL implies FL. It holds on every rotation case tested (`survey.py`, row "robust first leader exists"):
- every core profile with n ≤ 5 (1,648 + 31,456);
- every profile with n = 3 and m ≤ 9;
- every profile with n = 4 and m = 6 (`survey_small_4_6.log`).

Most successful runs from a working first leader are single-block: 108,528 of 123,597 at n = 5. For such a
leader, robustness is automatic, because no later leader is chosen. In the other cases the first block secures
the run (Lemmas NX and FF), or the later choices happen not to matter. This was not separated further.

### 3.3 Natural lemmas that would give FL, refuted

`lemmas.py` tests these on the rotation cases. The core profile counts are for cores with n ≤ 4, then cores with
n = 5.

| | Claim | Core profiles where it holds | Smallest failure |
|---|---|---|---|
| A | the failed run's r works as first leader | 1,643 / 1,648; 31,419 / 31,456 | n = 3, m = 5: (0,1,2), (0,3,1), (0,3,4); core n = 4, m = 5: (0,1,2), (0,3,4), (4,1,3), (4,3,2) |
| B | x₁ works | 1,622; 31,243 | (0,1,2), (0,3,4), (0,3,1), m = 5; core (2,0,3), (2,1,4), (2,1,0), m = 5 |
| C | some chain agent other than k\* works | 1,647; 31,456 | (0,1,2), (3,0,1), (3,0,4), m = 5; core n = 4, m = 6: (4,1,5), (0,2,1), (0,4,3), (4,2,3) |
| D | some first leader x is itself never exposed (b_x or c_x is taken by an agent other than r, or is an upgrade good) | 1,640; 31,444 | (0,1,2), (0,2,3), (2,3,4), m = 5; core (0,3,2), (2,1,4), (0,2,1), m = 5 |
| E | some first leader makes r a leader | 187; 3,037 | core (1,2,3), (0,1,2), (0,1,2), m = 4 |
| F | some working first leader lies in B\* ∖ {k\*} | all | trivial when the failed run has one leader |
| L | r or q works, where q holds r's top a_r in the failed run (in instance C below, q is the only working leader) | 1,645 / 1,648 (n ≤ 4) | (0,1,2), (0,3,1), (0,3,4), m = 5; core n = 4, m = 6, as for C |
| G | `iter_r` ends with success | all | — |
| H | Robust FL (§3.2) | all | — |
| J, K | §5 | | n = 3, m = 5 |

Instance C, worked by hand. The rankings are 0: (0, 1, 2), 1: (3, 0, 1), 2: (3, 0, 4), with m = 5.
- **Index run.** 0 takes 0. Then 1 takes 3, and 2 takes 4 (it has lost 0 and 3). The leftover goods are {1, 2}.
  r = 2, and E_r = {0}.
- **Why step 3 fails.** Both 0 and 1 are frozen, because 2 needs 3 and 0. So F = 0.
- **The chain** is 0 → 2, so x₁ = r = 2.
- **First leader 2 fails.** 2 takes 3, 1 takes 0, and 0 takes 1 and is upgraded with 2. r = 1, and 2 is exposed
  through b₂ = 0 = Y_r and c₂ = 4. F = 0.
- **First leader 1 is the only one that works.** 1 takes 3, 2 takes 0 and 0 takes 1. Then 0 is upgraded, so 2
  needs only 3, and 2 is upgraded too. E_r = ∅.

The working leader is the frozen agent that holds r's top. It is not on the chain.

**Structure of the set W of working first leaders.**
- W is never empty.
- W always meets B\* ∖ {k\*}.
- When the index run has two leaders, k\* was in W on all 660 core profiles with n ≤ 5 and all 504 profiles with
  n = 4 and m = 6. It is **false** in general. On disjoint unions (§3.4), k\* works in only 4,704 of 6,468
  cases. Example with n = 6, m = 10: (0,1,2), (0,4,2), (4,3,0), (5,6,7), (5,9,8), (9,8,5). The leaders are 0 and
  3, and W = {1, 2, 4, 5} (`union.log`).
- On average, 58–79% of the agents are in W (`proofs/k3_simple.md` §7).
- No fixed role is always in W (A, B, C above).

### 3.4 Disjoint unions (a targeted stress test)

With later leaders chosen by index, the component of a disjoint union that does not contain the first leader is
drafted by index. So it is short of free agents by one. Exposure for an absorber outside a component differs from
exposure for the component's own r: Y_r no longer protects, and an r that holds its top, with b and c left over,
becomes exposed. Unions are therefore a natural place to look for a counterexample. `union.py` builds the union
of every ordered pair of rotation cases (n = 3, m = 5), plus 100,000 pairs that also include the core rotation
cases with n ≤ 4, with the agents in component order or randomly interleaved.

| Unions | Unions where K3S rotates | FL failures | `sec_small` / `iter_r` failures | k\* works as first leader |
|---|---|---|---|---|
| 23,716 | 6,468 | 0 | 0 | 4,704 |
| 23,716 (interleaved) | 834 | 0 | 0 | 625 |
| 100,000 | 2,263 | 0 | 0 | 1,157 |

Every rotation case here has at least two leaders, one per component. So the unions refute "k\* works when the
index run has two or more leaders", which had held on all cores.

## 4. Rotation-free rules

`rules.py` defines the rules; `sec_branches.py` traces which branch of `sec_small` decides each run.

**Rule `sec_small`.** At each insertion step, with unprocessed agents R, try the following in order:
1. If the run is already *secured*, choose the smallest index. *Secured* means one of two things:
   - some leader so far has b or c picked in one of the blocks so far (all of them are non-last); or
   - one of those blocks has two agents satisfying Lemma FF's (i) and (ii).
2. Otherwise, choose the smallest x ∈ R whose block (simulated: x takes its top, then R1 steps by smallest index)
   leaves some agent of R unprocessed and secures the run.
3. Otherwise, choose the smallest x whose block takes all of R and whose finished run passes step 3.
4. Otherwise, choose the x with the smallest block, ties by index.

**Proposition.** If branch 1, 2 or 3 is taken at some step, K3S with `sec_small` succeeds at step 3 without the
rotation.
*Proof.* The block simulated for x is exactly the block the draft produces, because the R1 steps are
deterministic. Branches 1 and 2 look only at blocks that are not the last: another block follows, since some
agent of R is still unprocessed. So Lemma NX or Lemma FF applies, whatever happens later. Branch 3 checks the
completed run itself. ∎

**Conjecture S.** In every strict instance, the `sec_small` run takes branch 1, 2 or 3 at some insertion step.
Conjecture S implies that K3S with `sec_small` never needs the rotation.

Evidence for Conjecture S: no run ever ended without a guarded branch.
- Every core profile with n ≤ 4 (58,608 profiles). 489 of them, including 14 of the 1,648 rotation cases, used
  the smallest-block fallback first, 1 to 3 times, before a guarded branch.
- Every profile with n = 3 and m = 6 (14,400). 324 of them, including 36 rotation cases, used the fallback first.
- Every core profile with n = 5 (2,387,232; `sec_branches_cores5.log`). 4,252 of them, including 14 of the
  31,456 rotation cases, used the fallback first, 1 to 4 times.

The fallback matters. With "index" as fallback (rule `sec`), the run fails on 14 core profiles with n ≤ 4.
Smallest: (0,3,2), (2,1,4), (0,2,1), m = 5. With LB's lookahead as fallback (`sec_lb`), it fails on 4.

Cost: at most n block simulations per insertion step, plus at most n full runs at a step of type 3. It is
polynomial, and it is a lookahead rule like construction LB's, not a search over leader sequences.

**Rule `iter_r`.** Run K3S with index leaders. While step 3 fails, rerun with the failed run's r as the first
leader, until an r repeats. In the traced sets it needed at most 2 reruns. The number of rotation cases that
needed 2:
- 5 of 1,648 core cases with n ≤ 4;
- 37 of 31,456 core cases with n = 5;
- 24 of 462 profiles with n = 3, m = 6;
- 19 of 719 random rotation cases.

**Test counts (failures, i.e. step 3 fails without rotation).**

| Set | Profiles | Index fails | `sec_small` | `iter_r` | Log |
|---|---|---|---|---|---|
| every core profile, n ≤ 4 | 58,608 | 1,648 | 0 | 0 | `rules_small.log` |
| every core profile, n = 5 | 2,387,232 | 31,456 | 0 | 0 | `rules_test1.log` |
| n = 6 cores, 300 random profiles per core | 962,100 | 4,536 | 0 | 0 | `rules_cores6_300.log` |
| random ranking profiles, n ≤ 9 | 1,000,000 | 7,056 | 0 | 0 | `rules_rand1M.log` |
| every ranking profile, n = 3, m = 5, 6, 7 | 62,100 | 1,652 | 0 | 0 | `rules_small.log`, `rules_test1.log` |
| every ranking profile, n = 4, m = 5 | 216,000 | 4,344 | 0 | 0 | `rules_test1.log` |
| every ranking profile, n = 4, m = 6 | 1,728,000 | 33,168 | 0 | 0 | `rules_small_4_6.log` |
| disjoint unions (§3.4) | 147,432 | 9,565 | 0 | 0 | `union.log` |

In the logs written before zero counts were printed (`rules_test1.log`, `rules_rand1M.log`, `rules_cores6*.log`,
`rules_small_4_6.log`), a rule that is named in the header but has no `fails` key failed 0 times.

Rules that fail on core profiles with n ≤ 4:
- `small` (the smallest block every time): 1,340;
- `large`: 1,644;
- `sec`: 14;
- `sec_lb`: 4.

## 5. Idea 1 of the brief: compare with the rotated state P′ (obstruction)

The idea was to show that some draft run, with a different first or last leader, produces a pre-allocation at
least as good as P′ (Theorem B). `lemmas.py` tests two forms of it:
- J: P′'s picks are produced by some draft run, under any leader choices;
- K: some first leader gives a run with NA ⊆ NA(P′).

Both fail already at n = 3, m = 5. One core instance where both fail has rankings 0: (0, 3, 2), 1: (2, 1, 4),
2: (0, 2, 1), with m = 5. It is also the smallest core instance where D fails and where rule `sec` fails.

- **Index run.** 0 takes 0, 2 takes 2, and 1 takes 1. The leftover goods are {3, 4}. Agent 1 is upgraded (it holds
  b₁ = 1, c₁ = 4 is left over, and nobody needs 1), so J = {3}. Then r = 2, and agent 0 is exposed: b₀ = 3 ∈ J and
  c₀ = 2 = Y_r. Agent 0 is frozen (2 needs 0), so F = 0 and step 3 fails. The chain is 0 → 2.
- **P′.** 2 takes 0, and 0 holds {3, 2} and is upgraded. P′ = {3, 2}, {1, 4}, {0}, with J′ = ∅ and NA′ = ∅.
- **Why no draft produces P′.** In P′, agent 1 holds its b, 1, while its top 2 is c₀, an upgrade good. In a draft,
  an agent holds its b only if its top was *picked* earlier, and an upgrade good c_u is never a pick. The
  rotation hands r's old pick (here 2 = c_{k\*}) to k\*. If that good was the top of an upgraded agent, the state
  cannot come from a draft. No draft run has NA = ∅ here either: K fails.
- **Draft runs, by first leader.**
  - The run from 0 is the index run.
  - From 1, the run fails with E_r = {1}.
  - Only first leader 2 works: blocks [2, 0] and [1]. The absorber r = 1 leads its own block, so it succeeds by
    Lemma R, not by imitating P′. Its NA = {0} is not contained in NA′.

So "at least as good as P′" is the wrong invariant. The working runs succeed through a condition of Lemma T
(here, r is a leader), not by dominating P′.

## 6. What a proof would need

By Lemmas R, NX and FF, a run fails only if all of these hold:
- no block's leader has b or c picked by an agent other than r, or used as an upgrade good;
- every block other than the last has exactly one free agent, counting agents that might later be upgraded;
- the last block is not "its leader plus upgraded agents".

A proof of Conjecture S (or FL) has to show that some first leader breaks one of these. The data rule out the
easy routes:
- no single mechanism is always available (§2, remark);
- no agent with a fixed role always works (§3.3);
- the working leader can be an agent off the need chain (instance C).

What the data do support:
- the first block can be chosen to settle everything (Robust FL);
- following r twice (`iter_r`) always worked.

A proof along `iter_r` would need a potential that strictly improves from the run from k\* to the run from r, and
from there to the run from r′. I did not find one. The count of upgraded agents is not such a potential. On the §5
instance, the index run has one upgraded agent, and the successful run from r has none.

## 7. Files

| File | What |
|---|---|
| `fl.py` | trace-keeping K3S steps 1–3, `all_runs` (every leader sequence), `check` against `k3s.py` |
| `survey.py` | W, robust first leaders, roles (r, k\*, x₁, chain, B\*), number of leaders; `cases()` sources |
| `lemmas.py` | candidate lemmas A–M of §3.3 and §5 (M: when r fails, the absorber of the run from r is q; it fails too) |
| `mechanism.py` | which condition of Lemma T each successful run breaks |
| `rules.py` | rules `sec`, `sec_lb`, `sec_small`, `small`, `large`, runner `iter_r` |
| `sec_branches.py` | Conjecture S trace: branch of `sec_small` that decides each run; reruns of `iter_r` |
| `union.py` | disjoint unions of rotation cases |
| `*.log` | the outputs quoted above |

Reproduce, from this folder (one process each):
- `python3 fl.py check`
- `python3 survey.py cores 5 5`
- `python3 survey.py small 3 9`
- `python3 lemmas.py cores 5 5`
- `python3 mechanism.py cores 5 5`
- `python3 rules.py index,sec_small,iter_r cores 5 5`
- `python3 rules.py index,sec_small,iter_r rand 1000000 11 9`
- `python3 rules.py index,sec_small,iter_r cores 6 6 300`
- `python3 sec_branches.py cores 5 5 --all`
- `python3 union.py`
- `python3 union.py shuffle`
- `python3 union.py cores limit=100000 shuffle`
