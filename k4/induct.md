# k = 4: induction on the number of 4-good agents (insertion lemma)

Workstream `proof/k4-induct`. Ledger rows `K4.IND.*` (CONJECTURE / EVIDENCE only; the proofs below are written, not yet
reviewed). K4.D and K4.T are unchanged.

**The avenue.** Induct on j = the number of agents with 4 relevant goods. Base j = 0 is TARGET (k = 3, proved). Step
j → j + 1: pick a 4-good agent w and a good d ∈ R_w; I − d has at most j four-good agents, so it has an EFX₀ allocation
X′; an *insertion lemma* would turn X′ into an EFX₀ allocation of I by placing d with a bounded repair.

**Summary.**
- *As posed, the insertion lemma is false* (§2). For every choice of w and d, some EFX₀ allocation X′ of I − d is at
  repair distance ≥ 1 from every EFX₀ allocation of I already at n = 2, m = 4; ≥ 2 at n = 2, m = 5; ≥ 3 at n = 3, m = 5;
  ≥ 4 at n = 5, m = 6 (one 4-good agent); at n = 5 over half of the sampled profiles need 4. Deleting w together with d
  (B-form) or only w's value of d (V-form) also fails for every ρ ≤ 2 at n ≤ 4. Taking X′ extremal for a potential (w's
  value, the number of agents envying w, utilitarian or Nash welfare, and five more) fails too, each at n ≤ 3. Every
  failure is confirmed by an independent brute force (`attempts/k4_induct_attempts.py`, 21 claims).
- *For a private good the right statement is exact* (§3, Lemma 2, written proof): if d is valued by w only, X′ + (d → w) is
  EFX₀ **iff nobody envies w in X′**. So the step needs the right X′, never a repair.
- *Prescribed source* (PS(J, w)): J has an EFX₀ allocation in which nobody envies w. **Conjecture PS₄** (K4.IND.PS):
  PS holds for every agent of every instance with ≤ 4 relevant goods per agent. No failure in any test (§4): every
  strict profile of every k = 4 core with n = 2 (630,720 tests), every profile of the 251 connected k = 3 cores with
  n = 5, 6 of `results/certs_5_6.json.gz`, samples of k = 4 cores with n ≤ 6, the chain cores H_1–H_5 of `k4/c4.md` §7
  (n ≤ 21, by SAT, D2 shape), and 162,000 random general additive instances (zeros and ties allowed).
- *Conditional step* (§3, Theorem 4, written proof): if PS holds on the instances with ≤ j four-good agents, then every
  instance with ≤ j + 1 four-good agents in which some 4-good agent has a private good has an EFX₀ allocation, and a
  minimal counterexample among those with ≤ j + 1 is a connected strict k = 4 core **all of whose 4-good agents are
  Q4** (no private good). **This does not close the induction**: its hypothesis (PS below) is stronger than the
  conclusion (TARGET above), and PS itself (which implies TARGET₄ outright) is open already for k ≤ 3.
- *PS reduces to two configurations* (§3, Proposition 5, written proof): a minimal counterexample (I, w*) to PS is connected,
  has no junk good, w* has no private good, and no other agent can be peeled (R1, R2). Not reduced: R1 at w* (w*
  top-heavy), and a private good of another agent (Lemma 2 would need that agent unenvied as well).
- *The gap: Q4 agents* (§5). For a 4-good agent without a private good every removable good is shared, and placing it
  needs margins for its other valuers that "w unenvied" does not give. No rule "take X′ ∈ E(I − d) with the fewest
  agents envying h, give d to h" works for any (w, d, h) on 128 of 2,200 sampled profiles of the n = 3 cores whose
  4-good agents are all Q4, and on 813 of 4,700 of the n = 4 cores whose only 4-good agent is Q4, i.e. already for
  j = 0 → 1 (smallest: n = 3, m = 5).
- *A constructive route to PS at k = 3* (§4b): run LB⁺ with the target w processed *last*. Lemma 7 (written proof): if w
  ends Phase 1 with its top good, w is a valid owner and hence unenvied. Conjecture LBO (K4.IND.LBO): with the upgrade
  loop stopped anywhere and at most one LB⁺ rotation, some run always makes w an owner or gives it a free slot; no miss
  on every profile of every k = 3 core with n ≤ 5, nor on the instances I − p Theorem 4 needs (n ≤ 3 exhaustively).
  What is missing is the choice of the run, the same kind of exchange argument PR #37 needs for C₄¹∃.

## 0. Setting and notation

Instances: agents N, goods M, nonnegative additive valuations, R_i = {g : v_i(g) > 0}. E(J) = the EFX₀ allocations of
an instance J (complete, raw definition: v_i(X_i) ≥ v_i(X_j ∖ {h}) for all i ≠ j and h ∈ X_j). θ_i(B) = v_i(B) −
min_{g ∈ B} v_i(g) (0 if |B| ≤ 1); i is safe iff v_i(X_i) ≥ θ_i(X_j) for all j ≠ i. Agent j *envies* w in X if
v_j(X_w) > v_j(X_j). 𝒞_j = the instances with |R_i| ≤ 4 for every i and at most j agents with |R_i| = 4. Kinds of 4-good
agents in a k = 4 core (`k4/MINCEX.md`): P4 (one private good), PP4 (two), Q4 (none); a good is *private* to i if no
other agent values it.

For a 4-good agent w and d ∈ R_w, three smaller instances:
- **G-form** I − d: the good d deleted (every agent loses it). X′ ∈ E(I − d).
- **B-form** I − w − d: agent w and the good d deleted. X′ ∈ E(I − w − d).
- **V-form** I_{w,d}: nothing deleted; only v_w(d) := 0. Y ∈ E(I_{w,d}).

Each has at most j four-good agents when I has j + 1 (w loses a good or leaves; nobody gains one).

*Repair distance.* For X′ of the smaller instance, r(X′) = min over X ∈ E(I) of the number of goods (other than d, in
the G- and B-forms, where d is placed freely) whose owner differs in X and X′. r(X′) = 0 in the G-form means "place d,
move nothing"; in the B-form "give w nothing but (possibly) d, move nothing"; in the V-form "Y itself is EFX₀ for I".

## 1. Tools

- `k4/induct.c`: every EFX₀ allocation of the smaller instance (backtracking with a sound prune: once every good an
  agent values is placed, its value is final and θ only grows), the exact r(X′) (direct search up to radius 3, then a
  scan of every EFX₀ allocation of I), the worst r among the maximizers of 8 potentials, and PS tests (task P: every
  EFX₀ allocation; task Q: an early-exit search with the extra prune "a completed agent may not envy w"; task H: the
  rules of §5).
- `k4/induct_run.py`: driver over the certified cores (`results/k4_certs_*.json.gz`) and random strict profiles
  (integer representatives of strict balanced types, `k4/order_types.json`).
- `k4/induct_ps.py`: PS over every profile (or samples) of the certified cores.
- `k4/induct_sat.py`: an independent SAT encoding of EFX₀ and of "w unenvied" (per ordered pair (i, j), from agent
  i's own ≤ 4 goods), with every model re-checked by the raw definition; builds the chain cores H_t of `k4/c4.md` §7 from
  their description. Agrees with brute force on 2,362 random tests (PS and existence, with and without D2).
- `k4/induct_rules.py`: the placement rules of §5. `k4/induct_lbo.py`: the LBO tests of §4b (exact Lemma 1 tests of
  `proofs/lb_last_step.md` on every state; every state checked to be a valid pre-allocation).
- `k4/induct_bf.py`: an independent pure-Python brute force (itertools over all allocations, raw definition), used
  by `attempts/k4_induct_attempts.py` to re-derive every failure claimed here.

Two bugs found and fixed during the work: a D2 counter indexed with the unassigned-good marker, and the allocation
store sized with the previous instance's m (found by AddressSanitizer). All logs in `results/k4_induct_*` were produced
after both fixes; `k4/induct.c` is ASan-clean on 5,043 mixed tasks.

## 2. The insertion lemma as posed is false

**Every X′, bounded repair.** "For some 4-good w and some d ∈ R_w, every X′ of the smaller instance has r(X′) ≤ ρ"
fails for every fixed ρ tested, in each of the three forms; smallest failures (all re-derived by independent brute
force, `attempts/k4_induct_attempts.py`):

| form | ρ = 0 fails | ρ = 1 fails | ρ = 2 fails | ρ = 3 fails |
|---|---|---|---|---|
| G (delete d) | n = 2, m = 4 | n = 2, m = 5 | n = 3, m = 5 | n = 5, m = 6 (one 4-good agent) |
| B (delete w and d) | n = 2, m = 4 | n = 3, m = 5 | n = 4, m = 7 | none found |
| V (w stops valuing d) | n = 2, m = 5 | n = 3, m = 5 | n = 3, m = 6 | n = 3, m = 6 |

Distribution of the least ρ that works for the best (w, d) of each profile (exact r; random strict profiles, except
n = 2, which is every strict profile):

| profiles | G-form: ρ = 0 / 1 / 2 / 3 / 4 | B-form: 0 / 1 / 2 / 3 | V-form: 0 / 1 / 2 / 3 / 4 |
|---|---|---|---|
| n = 2: all 189,216 | 176,340 / 12,780 / 96 / 0 / 0 | 25,632 / 163,584 / 0 / 0 | 162,456 / 26,760 / 0 / 0 / 0 |
| n = 3: 500 per core, 25,500 | 19,750 / 3,198 / 2,511 / 41 / 0 | 8,764 / 16,598 / 138 / 0 | 16,893 / 8,126 / 472 / 6 / 3 |
| n = 4: 5 per core, 5,010 | 3,886 / 532 / 366 / 226 / 0 | 1,958 / 3,008 / 43 / 1 | 3,539 / 1,422 / 46 / 3 / 0 |
| n = 5, one or two 4-good agents: 800 | 126 / 3 / 97 / 159 / 415 | 724 / 75 / 1 / 0 | (not run) |

(`results/k4_induct_n2.log`, `results/k4_induct_n3.log`, `results/k4_induct_n4.log`, `results/k4_induct_n5.log`; each
log also lists, per statistic, its two smallest failing profiles.) The G-form gets worse with n: at n = 5 more than
half of the sampled profiles need 4 moved goods for every choice of (w, d). The B-form stays small (≤ 3 so far), and
its obstruction is identified in §6. Two smallest configurations (`attempts/k4-induct-bounded-repair.md`):
- *ρ = 0, G-form* (n = 2, m = 4): agent 0 on {0, 1, 2, 3} with values (2, 3, 8, 4) (good 0 private), agent 1 on
  {1, 2, 3} with (2, 4, 3). For d = 0, 1, 2, 3 the worst X′ needs 3, 2, 1, 2 moved goods.
- *ρ = 3, G-form* (n = 5, m = 6): agent 0 on {0, 3, 4, 5} with (10, 4, 3, 8), agents on {1, 4, 5}, {2, 4, 5},
  {3, 4, 5}, {3, 4, 5} with (4, 2, 3), (2, 3, 4), (3, 4, 2), (4, 3, 2). Every d ∈ R_0 has an X′ at distance 4. Yet the
  private good 0 inserts with no repair into every X′ that leaves agent 0 unenvied, and such X′ exist (Lemma 2
  below; the replay script checks it as a positive control).

**Extremal X′.** Since E(I − d) is finite and nonempty, a proof may take an X′ that maximizes a potential Φ. For each
Φ below, some profile has, for every (w, d), a maximizer of Φ on E(I − d) into which d cannot be placed (r ≥ 1)
(`attempts/k4-induct-potentials.md`):

| Φ (maximized on E(I − d)) | smallest failure | failing profiles: n = 3 (of 25,500) / n = 4 (of 5,010) / n = 5 (of 800) |
|---|---|---|
| v_w(X′_w) | n = 3, m = 4 | 1,092 / 194 / 298 |
| −v_w(X′_w) | n = 2, m = 4 | 3,348 / 509 / 648 |
| −#agents envying w | n = 3, m = 5 | 74 / 70 / 267 |
| (−#agents envying w, v_w) | n = 3, m = 5 | 10 / 21 / 109 |
| utilitarian Σ v_i(X′_i) | n = 3, m = 6 | 3 / 0 / 4 |
| Nash welfare (#positive, then Σ log v_i) | n = 3, m = 6 | 3 / 0 / 5 |
| (−#agents envying w, utilitarian) | n = 3, m = 5 | 10 / 3 / 5 |
| −#agents that envy someone | n = 3, m = 4 | 239 / 64 / 149 |
| V-form: (−#agents envying w, utilitarian) on E(I_{w,d}) | n = 2, m = 5 | 66 of the 189,216 n = 2 profiles |

## 3. What is proved

**Lemma 1 (a worthless good shields a bundle).** Let X be EFX₀, j ≠ w, and suppose X_w contains a good g with
v_j(g) = 0. Then j does not envy w.

*Proof.* EFX₀ with h = g: v_j(X_j) ≥ v_j(X_w ∖ {g}) = v_j(X_w). ∎

Consequences: (a) with |R_j| ≤ 4 for all j, a bundle of 5 or more goods is envied by nobody (it has a good outside every
R_j); at k = 3 the same holds from 4 goods; (b) a bundle that contains a good private to its owner is envied by nobody;
(c) j can envy X_w only if X_w ⊆ R_j.

**Lemma 2 (insertion of a good with one valuer).** Let I be any additive instance, p a good with v_j(p) = 0 for every
j ≠ w (v_w(p) ≥ 0 arbitrary), and X′ ∈ E(I − p). Then X′ + (p → w) is EFX₀ for I **if and only if** no agent envies w
in X′. In that case nobody envies w in X′ + (p → w) either.

*Proof.* Let X = X′ + (p → w): X_w = X′_w ∪ {p}, every other bundle as in X′, and nobody's valuation changes on the
goods of X′.
(⇐) Agent w: its value only grew, and it sees the other bundles as in X′. Agent j ≠ w, toward a bundle X_k with
k ≠ w: as in X′. Toward X_w: for h ∈ X_w, v_j(X_w ∖ {h}) ≤ v_j(X_w) = v_j(X′_w) ≤ v_j(X′_j) = v_j(X_j), since j does not
envy w in X′. The same inequality says nobody envies w in X.
(⇒) If j envies w in X′, then with h = p: v_j(X_w ∖ {p}) = v_j(X′_w) > v_j(X′_j) = v_j(X_j), so j is not safe. ∎

So for a private good the whole question is the choice of X′, and no repair is ever needed. Equivalently (by Lemma 1):
*some X′ ∈ E(I − p) leaves w unenvied iff some X ∈ E(I) gives p to w and leaves w safe without p.*

**Lemma 3 (placing p elsewhere).** With p, w, X′ as in Lemma 2 and h ≠ w, X′ + (p → h) is EFX₀ iff (i) no agent other
than h and w envies h in X′, and (ii) θ_w(X′_h ∪ {p}) ≤ v_w(X′_w). (If X′_h = ∅ both hold: {p} is a singleton.)

*Proof.* As for Lemma 2: h's value and view do not change (v_h(p) = 0); an agent j ∉ {h, w} sees X′_h ∪ {p} with p
worthless, so its threat is v_j(X′_h) (remove p) and it is safe iff it does not envy h; w sees X′_h ∪ {p}. ∎

**Theorem 4 (conditional induction step).** Let j ≥ 0 and suppose *PS holds on 𝒞_j*: for every instance J ∈ 𝒞_j and
every agent w of J, some X ∈ E(J) leaves w unenvied. Then:
- (a) every instance I ∈ 𝒞_{j+1} in which some agent w with |R_w| = 4 has a good p that no other agent values has an
  EFX₀ allocation (in which w is unenvied);
- (b) a counterexample to TARGET₄ in 𝒞_{j+1} with the fewest agents, and among those the fewest goods, is a connected
  k = 4 core with strict types **in which no agent with four relevant goods has a private good**.

*Proof.* (a) I − p ∈ 𝒞_j: w has three relevant goods left, and no other agent's relevant set changes because nobody
else values p. By PS, some X′ ∈ E(I − p) leaves w unenvied, and by Lemma 2, X′ + (p → w) ∈ E(I), with w unenvied.
(b) 𝒞_{j+1} is closed under deleting agents and goods (relevant sets only shrink) and under K4.TIE's perturbation
(supported on each R_i, so every R_i is kept). The proof of K4.MC0 (a)–(c) (`k4/MINCEX.md` §1) uses only these
operations: each K4.CORE step (L3, R1, R2) and each component is a sub-instance with fewer agents or goods, and the
strict perturbation keeps the hypergraph. So it applies within 𝒞_{j+1}, and a minimal counterexample I is a connected
k = 4 core with strict types. (The closure for j = 0 is PR #39's `atMostOne4_sublist`, in Lean, not yet merged.) By
(a), no 4-good agent of I has a private good. ∎

*What Theorem 4 does not give.* Its hypothesis, PS on 𝒞_j, is stronger than TARGET on 𝒞_j, and its conclusion is
TARGET (not PS) on part of 𝒞_{j+1}. So it does not iterate: the induction on j closes only if PS itself is proved at
every level, and PS on 𝒞_4 already implies TARGET₄. What it does show is that, *as far as the P4 and PP4 agents are
concerned*, the whole difficulty of the step j → j + 1 is the choice of X′, and that the choice needed is exactly an
unenvied w (Lemma 2 is an equivalence).

Where the hypotheses enter: |R_i| ≤ 4 only through 𝒞_j (I − p has one 4-good agent fewer); the core structure only
through "a P4 or PP4 agent has a private good"; strictness and connectivity only to place the minimal counterexample
among the certified and structured objects of `k4/MINCEX.md`. Lemma 2 itself uses nothing but additivity.

**Proposition 5 (PS is inductive away from two configurations).** Let 𝒦 be a class of instances closed under deleting
agents and goods (e.g. 𝒞_j), and let (I, w*) be a counterexample to PS in 𝒦 (no X ∈ E(I) leaves w* unenvied) with
the fewest agents, then the fewest goods. Then:
- (a) every good is valued by some agent;
- (b) w* values no good that no other agent values;
- (c) no agent i ≠ w* can be peeled by R1 (its favorite good a_i has v_i(a_i) ≥ v_i(R_i ∖ {a_i})) or by R2 (P = its
  private goods, nonempty, with v_i(P) ≥ v_i(R_i ∖ P));
- (d) I is connected.

*Proof.* In each case a smaller instance I′ ∈ 𝒦 has, by minimality, some X′ ∈ E(I′) leaving w* unenvied, and we extend
it.
- (a) A good z valued by nobody: I′ = I − z, and X′ + (z → w*) by Lemma 2 (with v_{w*}(z) = 0).
- (b) A good p valued by w* only: I′ = I − p, and X′ + (p → w*) by Lemma 2.
- (c) R1 for i ≠ w*: I′ = I − i − a_i, X = X′ + (i ↦ {a_i}). Agent i: every other bundle meets R_i inside
  R_i ∖ {a_i}, worth at most v_i(a_i), so i envies nobody (in particular not w*); {a_i} is a singleton; every other
  agent sees the bundles of X′ unchanged. R2 for i ≠ w*: the same with P, which nobody else values (so no agent's
  threat from P is positive). In both cases w*'s bundle and the other agents' envy toward it are as in X′.
- (d) If I is disconnected, the component C containing w* is smaller, so it has X¹ ∈ E(C) leaving w* unenvied; every
  other component D is smaller and in 𝒦, so it has an EFX₀ allocation (PS for any agent of D gives one). Agents of
  different components value nothing in each other's bundles, so the union is EFX₀ and w* stays unenvied. ∎

So the two configurations PS's own induction does not reduce are: **w* top-heavy or with at most two goods** (R1 at the
target: w* would take its favorite good, which others may envy), and **a private good of an agent other than w***
(Lemma 2 needs that agent unenvied as well, and two agents cannot in general both be unenvied: two identical agents
with a strict type always have one envying the other).

**Proposition 6 (PS as junk absorption; the easy cases).**
- (a) PS(J, w) holds iff J + z, with z a new good valued by nobody, has an EFX₀ allocation that gives z to w
  (Lemma 2 with v_w(z) = 0; conversely Lemma 1, and deleting z changes nobody's values).
- (b) Hence PS(J, w) holds whenever some EFX₀ allocation of J, after adding goods valued by nobody, gives w a bundle
  that no R_j contains: for instance, when w can be the owner of the large bundle of a D2 allocation padded to
  k + 1 goods (Lemma 1(a)). At k = 3 this is the owner of LB⁺ (`proofs/lb_last_step.md`) when the owner can be
  prescribed; at k = 4, the owner of LB₄.
- (c) PS(J, w) holds when |R_i| ≤ 2 for every agent i ≠ w (w arbitrary): run serial dictatorship with w last (each agent takes its favorite
  remaining good; w takes the rest). This is EFX₀ (L2c), and an agent i ≠ w values X_w at most at the value of the
  good of R_i it did not pick, which was still available at its turn, so at most v_i(X_i).

*Proof of (c).* Take i ≠ w with pick g_i (if i picked nothing, every good of R_i was taken before its turn, so X_w
contains no good of R_i). X_w ∩ R_i ⊆ R_i ∖ {g_i}, which has at most one good, and that good was available when i
picked g_i, so v_i(X_w) ≤ v_i(g_i) ≤ v_i(X_i). EFX₀ for i ≠ w: the bundles other than X_w are single goods; toward
X_w, θ_i(X_w) ≤ v_i(X_w) ≤ v_i(X_i). For w (any number of goods): every bundle other than X_w is a single good. ∎

## 4. Evidence for PS (K4.IND.PS, K4.IND.PSE)

PS(I, w) for every agent w, and PS(I − p, w) for every 4-good w with a private good p (the input Theorem 4 needs), with
`k4/induct_ps.py` (early-exit search, `k4/induct.c` task Q, cross-checked against the full enumeration of task P on
889 random instances, and against the independent SAT encoding of `k4/induct_sat.py` on 400 random k = 4 core
profiles: 5,074 tests, 0 mismatches, `results/k4_induct_ps_satcheck.log`), and with the SAT encoding alone for the
chain cores:

| instances | tests | failures (all X / D2 X) | log |
|---|---|---|---|
| every strict profile of every k = 4 core with n = 2 (189,216) | 378,432 PS(I, w) + 252,288 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n2.log` |
| k = 4 cores with n = 3: 14,782,912 profiles (35 cores exhaustively, 16 with 100,000 random profiles each) | 44,348,736 PS(I, w) + 49,737,600 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n3.log` |
| every k = 4 core with n = 4 or 5 (32,586 cores): 20 random profiles each (651,720) | 3,238,560 PS(I, w) + 1,497,520 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n45.log` |
| every ranking profile of the 251 connected k = 3 cores of `results/certs_5_6.json.gz` (n = 5, m = 9; n = 6, m = 10, 11) | see log | see log | `results/k4_induct_ps_k3_56.log` |
| H_1–H_5 (`k4/c4.md` §7; n = 5, 9, 13, 17, 21), SAT | every agent (65) and every private-good insertion | 0 (D2) | `results/k4_induct_ht.log` |
| random general additive, n = 3 (m = 4..8), n = 4 (m = 4..7), values 0..R with zeros and ties | 162,000 instances, 558,000 tests | 0 | `results/k4_induct_ps_general.log` |

Random and sampled tests are EVIDENCE only (PROMPT.md §5 rule 3). The exhaustive rows are single-implementation
exhaustive searches; they are evidence for a conjecture, not a certificate of anything in the ledger.

## 4b. PS at k = 3 through LB⁺ with the target processed last

The P4 step at j = 0 needs PS(I − p, w) where I − p is a k = 3 instance: every agent other than w values three goods
and is balanced (they are core agents of I), and w values the three shared goods it had in I, with any values (w may be
top-heavy in I − p). By Proposition 6(b) it suffices that w own the large bundle of an LB⁺-type allocation, or hold a
junk good in a slot. LB⁺ itself (`proofs/lb_last_step.md`) makes the last-processed agent r the owner, but Phase 1's
R1 priority can force w early, and LB's upgrade loop and rotation can freeze or upgrade w. The fix that works in every
test is to **postpone w to the end of Phase 1**.

*Phase 1 with w last.* Process the agents other than w by Phase 1's rules (an agent i ≠ w with |R_i ∩ G| ≤ 2 first,
else an insertion step at any unprocessed i ≠ w), then w; each takes its favorite remaining good or nothing. (I1),
(I2) hold for any order. For i ≠ w, (I3) holds as before, and so do (B1′) "when a block starts, every unprocessed agent
other than w has R_i ⊆ G" and (B2′) "if j ≠ w needs g (g ∈ R_j, g ≻_j Y_j or Y_j = none), g was picked earlier in j's
block": if g had been picked in an earlier block, j would have been unprocessed at the start of its block with g ∉ G.
(B2′) fails for w: w's needs may lie in any block. P = (Y, ∅) is valid ((V1) from (I2)).

*Theorem 1′ in this setting.* Its proof (`proofs/lb_last_step.md` §2) uses balance only for upgraded agents, and the
three-goods structure of an agent i only for the bundles i sees; the owner o sees no other bundle of more than two
goods. So Theorem 1′ and Lemma 1 hold verbatim when the owner w (never upgraded) has at most three goods and any values.

**Lemma 7.** If, in some run of Phase 1 with w last, w picks its top good a_w, then w is a valid owner of P = (Y, ∅),
and I has an EFX₀ allocation in which nobody envies w.

*Proof.* (i) *w is a terminal and needs nothing.* An agent i ≠ w that needed Y_w would, by (I1), see Y_w picked before
its turn, but w picks last; and w holds its top, so N_w = ∅. (ii) *Exposed agents lead blocks.* Let x ∈ E_w, that is
x ≠ w, Y_x = a_x and {b_x, c_x} ⊆ J ∪ {Y_w}. At x's turn a_x, the junk and Y_w were all still available, so
R_x ⊆ G, and by (I3) x was processed at an insertion step: it leads its block. Distinct exposed agents lead distinct
blocks. π_x = {b_x, c_x} ∩ J is nonempty, and no exposed pair lies in base(w) = {Y_w}. (iii) *A terminal per exposed
agent.* If x ∈ T, let τ(x) = x (cap 1). If x ∈ F, some j ∉ U needs Y_x; j ≠ w because N_w = ∅, so by (B2′) j lies in
x's block and comes after x. Repeating while the current agent is frozen follows a need chain inside x's block (the
processing order increases, so it stops) that ends at a terminal τ(x) ≠ w of x's block, with cap ≥ 1. (iv) *Count.*
The τ(x) lie in distinct blocks, so they are distinct terminals other than w, and S − cap(w) ≥ |E_w| ≥ |H| for H made of
one good of each π_x. By Lemma 1, with ω ≥ 1 there is a completion with owner w that satisfies (OC), and it is EFX₀ by
Theorem 1′. (v) *Unenvied.* Add goods valued by nobody before running Phase 1 (they are never picked, so the run is
unchanged) until ω ≥ 2. The owner's bundle then has ω + 2 ≥ 4 goods (`proofs/lb_last_step.md` Remark 1), so no
R_j (three goods) contains it, and by Lemma 1 nobody envies w. Deleting the added goods changes no one's value of any
bundle and only shrinks X_w, so the allocation stays EFX₀ and w stays unenvied. ∎

Lemma 7 is the easy case: N_w = ∅, so no need chain can leave its block through w, and LB⁺'s bad case cannot occur.
When w picks its second or third good, or nothing, chains from up to |N_w| ≤ 3 blocks can end at w, each costing one
terminal in the count.

**Conjecture LBO** (K4.IND.LBO). In the setting above (agents other than w: three goods, balanced; w: at most three
goods), there are a run of Phase 1 with w last, a state of LB's upgrade loop (stopped anywhere; never upgrading w if it
is top-heavy), and optionally one LB⁺ rotation (Theorem B's, along a need chain from the last block's leader, exposed
w.r.t. w, to w), whose valid pre-allocation has w as a valid owner (Lemma 1), or has w as a terminal with a slot while
some other valid owner o leaves a slot free (|H| ≤ S − cap(o) − 1). Either way, by Theorem 1′ and Lemma 1 (padding as in
Lemma 7), I has an EFX₀ allocation in which nobody envies w.

LBO would give PS on the instances Theorem 4(a) needs at j = 0, and hence: *TARGET₄ holds for every instance with at
most one 4-good agent unless the minimal counterexample's 4-good agent is Q4* (for a PP4 agent, I − p leaves w with three
goods, one of them private, which is inside LBO's setting).

*Evidence* (`k4/induct_lbo.py`: exact Lemma 1 tests on every state; every state is checked to be a valid
pre-allocation; single implementation):
- every ranking profile of every connected k = 3 core with n ≤ 4 (`results/certs_lb_2_6.json.gz`; 217,224 (profile, w)
  pairs) and n = 5 (see `results/k4_induct_lbo_n5.log`): no miss (`results/k4_induct_lbo_n234.log`);
- the instances J = I − p for every strict profile of every k = 4 core with n ≤ 3 whose only 4-good agent is P4, and
  samples for n = 4, 5 (`results/k4_induct_lbo_k4_n*.log`), about half of them with w top-heavy in J: no miss;
- *every ingredient is needed* (`results/k4_induct_lbo_variants.log`): without "w last" (every run of Phase 1 with LB's
  R1 priority for every agent), 1,134 misses among the 583,200 pairs of the n = 5, m = 9 cores (none at n ≤ 4);
  without stopping the upgrade loop early, 4,098 misses at n = 4; without the rotation, 3,608; with w as owner only
  (no slot witness), 48;
- *the run must be chosen*: requiring every run of Phase 1 with w last to work fails on 2,188 of the 212,544 n = 4
  pairs (smallest: n = 4, m = 5).
- *by w's final pick* (every run of Phase 1 with w last, every n = 4 core and profile, `results/k4_induct_lbo_bytype_n4.log`):
  every one of the 483,376 runs in which w ends with its top gives a witness, as Lemma 7 says (a computational check of
  it); runs in which w ends with its second good, its third good, or nothing fail in 64 of 272,688, 1,936 of 138,524
  and 2,080 of 83,460 cases even with the rotation (1,052, 11,528 and 16,932 without it).

The step still missing for a proof of LBO is the choice of the run when w ends Phase 1 without its top: an exchange
argument on insertion sequences of the kind PR #37 (K4.C4.1X, Lemma X) needs for C₄¹∃.

## 5. The gap: 4-good agents without a private good (Q4)

For a Q4 agent every d ∈ R_w is shared, and Lemma 2 does not apply: d → w needs, besides w unenvied by the other
agents, the margin θ_j(X′_w ∪ {d}) ≤ v_j(X′_j) for every other valuer j of d. Tested rules:
- *GPS* ("some X′ ∈ E(I − d) admits d → w", for some d ∈ R_w): fails for some Q4 agent on 119 of the 12,000 sampled
  n = 3 profiles that have a Q4 agent (`results/k4_induct_n3.log`, statistic GPS_Q4_anyd), and on 134 of 3,275 at
  n = 4 (`results/k4_induct_n4.log`). There d can only go to another agent.
- *PS-selected placement* H(w, d, h): take X′ ∈ E(I − d) minimizing the number of agents envying h, and give d to h.
  For P4 agents with d private and h = w it always works (Lemma 2 plus PS: 13,600 of 13,600 n = 3 cases). In the
  n = 3 cores whose 4-good agents are all Q4, no triple (w, d, h) works on 128 of 2,200 sampled profiles
  (`results/k4_induct_rules_n3.log`); in the n = 4 cores whose only 4-good agent is Q4 (the case j = 0 → 1), on 813 of
  4,700 (`results/k4_induct_rules_n4_1.log`). Smallest configuration (`attempts/k4-induct-q4-rules.md`): n = 3, m = 5,
  agents {0, 3, 4} (2, 4, 3), {1, 2, 3, 4} (6, 4, 8, 3), {1, 2, 4} (2, 3, 4).
- *B-form* for a Q4 agent (delete w and d; give w nothing but d): for the best d, repair r ≤ 1 on every sampled n = 5
  profile (cores with one or two 4-good agents, `results/k4_induct_n5.log`), but r = 2 and r = 3 occur at n = 3
  (267 and 2 of the 12,000 profiles with a Q4 agent).

What a proof of the Q4 step would have to supply is an X′ with *two* properties at once (w unenvied, and the valuers of
d satisfied with margin), which is what Proposition 5 also cannot supply for a second agent.

**H_t from this point of view.** In the chain cores H_t of `k4/c4.md` §7 (where LB₄ʳ needs unboundedly many
rotations), ℓ and the x_{j,i} are PP4 agents and only the y_j are Q4. PS held for every agent of H_1–H_5 and for every
H_t − p with p a private good (`results/k4_induct_ht.log`), so Lemma 2 inserts each private good with no repair; the
difficulty of H_t for the induction is concentrated in its t Q4 agents y_j, whose goods are the tops
a_{j,i} of three PP4 agents and a good of the next gadget.

## 6. The B-form and LB₄'s owner constraint

In the B-form with d = a_w (w's top), X′ + (w ↦ {a_w}) is EFX₀ iff no bundle of X′ threatens w holding a_w
(the others see a new singleton only, L10). Bundles of ≤ 2 goods never do (θ_w of such a bundle is at most one good,
worth ≤ v_w(a_w)); so for a D2-shaped X′ the only obstruction is the large bundle containing a threatening set of
{b_w, c_w, d_w}, which is LB₄'s owner constraint (OC₄) (`k4/lb4.md` §1). With the best d the B-form needed r ≤ 2
everywhere tested (n ≤ 5), and r ≤ 1 for every sampled n = 5 core with one 4-good agent; but the statement "every X′"
fails at r = 1 already at n = 3 (§2).

## 7. What remains

1. **PS on 𝒞_0** (k ≤ 3 instances), at least for the instances I − p of §4b. With Theorem 4 it removes the P4 and PP4
   agents from a minimal counterexample with one 4-good agent. Route: conjecture LBO (§4b). Lemma 7 proves it when w
   ends Phase 1 (w last) with its top. Open: the runs in which w ends with its second or third good or with nothing,
   where need chains from up to three blocks end at w; the upgrades (second good) and one rotation (third good,
   nothing) repair them in every test, but only for a well-chosen run, so a proof needs an exchange argument on
   insertion sequences, like PR #37's Lemma X for C₄¹∃.
2. **PS on 𝒞_j in general**, whose own induction (Proposition 5) stops at R1 on the target and at a second agent's
   private good. Without it, Theorem 4 does not iterate beyond j = 0.
3. **Q4 agents**: an insertion rule for a shared good; none of the tested selection rules works (§5), already with a
   single Q4 agent (j = 0 → 1).

## Reproduce

```
gcc -O2 -o /tmp/k4_induct k4/induct.c -lm            # (the drivers compile it on first use)
python3 k4/induct_run.py results/k4_certs_2.json.gz --all --jobs=2 --rmax=3 --no-a --v --log=results/k4_induct_n2.log
python3 k4/induct_run.py results/k4_certs_3.json.gz --samples=500 --seed=7 --jobs=2 --rmax=3 --no-a --v --log=results/k4_induct_n3.log
python3 k4/induct_run.py results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
    results/k4_certs_4_pure.json.gz --samples=5 --seed=2 --jobs=2 --rmax=3 --no-a --v --log=results/k4_induct_n4.log
python3 k4/induct_run.py results/k4_certs_5_n4_1.json.gz results/k4_certs_5_n4_2.json.gz --samples=1 --max-cores=400 \
    --seed=3 --jobs=2 --rmax=3 --no-a --log=results/k4_induct_n5.log
python3 attempts/k4_induct_attempts.py                                    # every failure above, by brute force, < 1 s
python3 k4/induct_ps.py results/k4_certs_2.json.gz --all --jobs=2 --log=results/k4_induct_ps_k4_n2.log
python3 k4/induct_ps.py results/k4_certs_3.json.gz --max-all=3000000 --samples=100000 --jobs=2 --log=results/k4_induct_ps_k4_n3.log  # ~20 min
python3 k4/induct_ps.py --general --per=2000 --jobs=2 --log=results/k4_induct_ps_general.log
python3 k4/induct_ps.py results/certs_5_6.json.gz --all --jobs=4 --log=results/k4_induct_ps_k3_56.log   # ~3 h
(cd k4 && for t in 1 2 3 4 5; do python3 induct_sat.py ht $t --d2; done) > results/k4_induct_ht.log   # ~5 min
(cd k4 && python3 induct_sat.py crosscheck 400 1 ../results/k4_certs_3.json.gz ../results/k4_certs_4_n4_2.json.gz \
    ../results/k4_certs_4_pure.json.gz) > results/k4_induct_ps_satcheck.log
python3 k4/induct_rules.py results/k4_certs_3.json.gz --samples=200 --seed=1 --jobs=2 --log=results/k4_induct_rules_n3.log
python3 k4/induct_rules.py results/k4_certs_4_n4_1.json.gz --samples=100 --seed=2 --jobs=2 --log=results/k4_induct_rules_n4_1.log
python3 k4/induct_lbo.py results/certs_lb_2_6.json.gz --n=4 --all --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_n234.log
python3 k4/induct_lbo.py results/certs_lb_2_6.json.gz --n=5 --all --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_n5.log
python3 k4/induct_lbo.py --from-k4 results/k4_certs_2.json.gz results/k4_certs_3.json.gz --all --jobs=2 --last --partial --rot \
    --log=results/k4_induct_lbo_k4_n23.log
```
The variants of LBO (each ingredient dropped; every run) are listed with their commands in
`results/k4_induct_lbo_variants.log`.
