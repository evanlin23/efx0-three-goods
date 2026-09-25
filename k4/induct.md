# k = 4: induction on the number of 4-good agents (insertion lemma)

Workstream `proof/k4-induct`. Ledger rows `K4.IND.*` (CONJECTURE / EVIDENCE only; the proofs below are written, not yet
reviewed). K4.D and K4.T are unchanged.

**The avenue.** Induct on j = the number of agents with 4 relevant goods. Base j = 0 is TARGET (k = 3, proved). Step
j → j + 1: pick a 4-good agent w and a good d ∈ R_w; I − d has at most j four-good agents, so it has an EFX₀ allocation
X′; an *insertion lemma* would turn X′ into an EFX₀ allocation of I by placing d with a bounded repair.

**Summary.**
- *As posed, the insertion lemma is false* (§2): for every choice of w and d, some EFX₀ allocation X′ of I − d is at
  repair distance ≥ 1 from every EFX₀ allocation of I already at n = 2, m = 4; ≥ 2 at n = 2, m = 5; ≥ 3 at n = 3, m = 5;
  ≥ 4 at n = 5, m = 6 (one 4-good agent). Removing the agent w together with d (B-form), or only w's value of d
  (V-form), fails the same way at small sizes. Taking X′ extremal for a potential (w's value, the number of agents
  envying w, utilitarian or Nash welfare, and four more) fails too, each at n ≤ 3. All confirmed by an independent brute
  force (`attempts/k4_induct_attempts.py`).
- *The right statement for a private good is exact and trivial* (§3, Lemma 2, proved): if d is valued by w only, then
  X′ + (d → w) is EFX₀ **iff nobody envies w in X′**. So the step needs X′ with w unenvied, not a repair.
- *Prescribed source* (PS): every instance has, for every agent w, an EFX₀ allocation in which nobody envies w.
  **Conjecture PS₄** (K4.IND.PS). No counterexample in any test (§4): every strict profile of every k = 4 core with
  n = 2 (630,720 tests), 11.1 million profiles of every k = 3 core with n = 5, 6 (exhaustive), samples of k = 4 cores
  with n ≤ 5, the chain cores H_1–H_5 of `k4/c4.md` §7 (n ≤ 21, by SAT), and 32,400 random general additive instances
  (zeros and ties allowed). It held in the D2 shape wherever tested.
- *Conditional step* (§3, Theorem 4, proved): if PS holds for every instance with at most j four-good agents, then a
  minimal counterexample to TARGET₄ among instances with at most j + 1 four-good agents is a connected strict k = 4 core
  **in which no 4-good agent has a private good** (every 4-good agent is Q4). The P4 and PP4 agents are eliminated by
  Lemma 2 with zero repair.
- *PS is inductive except at two configurations* (§3, Proposition 5, proved): a minimal counterexample (I, w*) to PS
  has no junk good, is connected, every agent other than w* is a core agent (R1, R2 do not apply), and w* has no private
  good. What is not reduced: w* itself top-heavy (R1 at the target), and a private good of an agent other than w*
  (placing it needs a second agent unenvied).
- *The gap: Q4 agents* (§5). For a 4-good agent with no private good, every removed good d is shared, and placing it
  needs more than "w unenvied". In the all-Q4 n = 3 cores, no rule "take X′ ∈ E(I − d) with the fewest enviers of h,
  give d to h" works for any (w, d, h) on 5.6% of the sampled profiles (smallest: n = 3, m = 5).

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
- `k4/induct_bf.py`: an independent pure-Python brute force (itertools over all allocations, raw definition), used
  by `attempts/k4_induct_attempts.py` to re-derive every failure claimed here.

Two bugs found and fixed during the work: a D2 counter indexed with the unassigned-good marker, and the allocation
store sized with the previous instance's m (found by AddressSanitizer). All logs in `results/k4_induct_*` were produced
after both fixes; `k4/induct.c` is ASan-clean on 5,043 mixed tasks.

## 2. The insertion lemma as posed is false

**Every X′, bounded repair.** "For some 4-good w and d ∈ R_w, every X′ ∈ E(I − d) has r(X′) ≤ ρ" fails for every
fixed ρ tested; the least ρ needed (for the best (w, d)) grows with n:

| form | ρ = 0 fails | ρ = 1 fails | ρ = 2 fails | ρ = 3 fails |
|---|---|---|---|---|
| G (delete d) | n = 2, m = 4 | n = 2, m = 5 | n = 3, m = 5 | n = 5, m = 6 (one 4-good agent) |
| B (delete w and d) | n = 2, m = 4 | n = 3, m = 5 | none found (n ≤ 5, samples) | none found |
| V (w stops valuing d) | n = 2, m = 5 | n = 3, m = 5 | none found (n ≤ 3) | |

Distribution of the least ρ (the best (w, d) per profile):

| profiles | G-form: ρ = 0 / 1 / 2 / 3 / 4 | B-form: 0 / 1 / 2 | V-form: 0 / 1 / 2 / 3+ |
|---|---|---|---|
| n = 2, all 189,216 strict profiles | 176,340 / 12,780 / 96 / 0 / 0 | 25,632 / 163,584 / 0 | 162,456 / 26,760 / 0 |
| n = 3, 500 per core (25,500) | 19,750 / 3,198 / 2,511 / 41 / 0 | 8,764 / 16,598 / 138 | 16,893 / 8,126 / 472 / 9 |
| n = 4, 5 per core (5,010) | see `results/k4_induct_n4.log` | | |
| n = 5, one 4-good agent, 400 cores | 53 of 200 at ρ = 0, 93 at ρ = 4 (earlier run, §6) | 328 / 68 / 4 | |

(Sources: `results/k4_induct_n2.log`, `results/k4_induct_n3.log`, `results/k4_induct_n4.log`,
`results/k4_induct_n5.log`.)

The smallest configurations, each re-derived by brute force in `attempts/k4_induct_attempts.py`
(`attempts/k4-induct-bounded-repair.md`):
- *ρ = 0, G-form* (n = 2, m = 4): agent 0 on {0, 1, 2, 3} with values (2, 3, 8, 4) (good 0 private), agent 1 on
  {1, 2, 3} with (2, 4, 3). For d = 0, 1, 2, 3 the worst X′ needs 3, 2, 1, 2 moved goods.
- *ρ = 3, G-form* (n = 5, m = 6): agent 0 on {0, 3, 4, 5} with (10, 4, 3, 8), agents on {1, 4, 5}, {2, 4, 5}, {3, 4, 5},
  {3, 4, 5} with (4, 2, 3), (2, 3, 4), (3, 4, 2), (4, 3, 2). Every d ∈ R_0 has an X′ at distance 4. Yet the private good
  0 inserts with zero repair into every X′ that leaves agent 0 unenvied, and such X′ exist (Lemma 2 below; the script
  checks it as a positive control).

**Extremal X′.** Since E(I − d) is finite and nonempty, a proof may take the X′ that maximizes a potential Φ. For each
Φ below, some profile has, for every (w, d), a maximizer of Φ on E(I − d) into which d cannot be placed (r ≥ 1)
(`attempts/k4-induct-potentials.md`); smallest cases:

| Φ (maximized on E(I − d)) | smallest failure |
|---|---|
| v_w(X′_w) | n = 3, m = 4 |
| −v_w(X′_w) | n = 2, m = 4 |
| −#agents envying w | n = 3, m = 5 |
| (−#agents envying w, v_w) | n = 3, m = 5 |
| utilitarian Σ v_i(X′_i) | n = 3, m = 6 |
| Nash welfare (#positive, then Σ log v_i) | n = 3, m = 6 |
| (−#agents envying w, utilitarian) | n = 3, m = 5 |
| −#agents that envy someone | n = 3, m = 4 |
| V-form, (−#agents envying w, utilitarian) on E(I_{w,d}) | n = 2, m = 5 |

The rarest failures are those of Nash welfare and of (−#enviers, utilitarian): 3 and 10 of 25,500 n = 3 profiles.

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
every agent w of J, some X ∈ E(J) leaves w unenvied. Let I be a counterexample to TARGET₄ in 𝒞_{j+1} with the fewest
agents, and among those the fewest goods. Then I is a connected k = 4 core with strict types, and **every agent of I
with four relevant goods has no private good**.

*Proof.* 𝒞_{j+1} is closed under deleting agents and goods (relevant sets only shrink) and under K4.TIE's perturbation
(supported on each R_i, so every R_i is kept). The proof of K4.MC0 (a)–(c) (`k4/MINCEX.md` §1) uses only these
operations: each K4.CORE step (L3, R1, R2) and each component is a sub-instance with fewer agents or goods, and the
strict perturbation keeps the hypergraph. So it applies within 𝒞_{j+1}, and I is a connected k = 4 core with strict
types. (PR #39's `atMostOne4_sublist` is the case j = 0 of the closure, in Lean.) Suppose a 4-good agent w had a
private good p. Then I − p ∈ 𝒞_j: w has three relevant goods left, and no other agent's relevant set changes because
nobody else values p. By PS, some X′ ∈ E(I − p) leaves w unenvied, and by Lemma 2, X′ + (p → w) ∈ E(I). So I is not a
counterexample. ∎

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
- (c) PS holds when |R_i| ≤ 2 for every agent: run serial dictatorship with w last (each agent takes its favorite
  remaining good; w takes the rest). This is EFX₀ (L2c), and an agent i ≠ w values X_w at most at the value of the
  good of R_i it did not pick, which was still available at its turn, so at most v_i(X_i).

*Proof of (c).* Take i ≠ w with pick g_i (if i picked nothing, every good of R_i was taken before its turn, so X_w
contains no good of R_i). X_w ∩ R_i ⊆ R_i ∖ {g_i}, which has at most one good, and that good was available when i
picked g_i, so v_i(X_w) ≤ v_i(g_i) ≤ v_i(X_i). EFX₀ for i ≠ w: the bundles other than X_w are single goods; toward
X_w, θ_i(X_w) ≤ v_i(X_w) ≤ v_i(X_i). For w: every bundle other than X_w is a single good. ∎

## 4. Evidence for PS (K4.IND.PS, K4.IND.PSE)

PS(I, w) for every agent w, and PS(I − p, w) for every 4-good w with a private good p (the input Theorem 4 needs), with
`k4/induct_ps.py` (early-exit search, `k4/induct.c` task Q, cross-checked against the full enumeration of task P on
889 random instances):

| instances | tests | failures (all X / D2 X) | log |
|---|---|---|---|
| every strict profile of every k = 4 core with n = 2 (189,216) | 378,432 PS(I, w) + 252,288 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n2.log` |
| every profile of every k = 3 core with n = 5, 6 (11,127,456) | see log | see log | `results/k4_induct_ps_k3_56.log` |
| k = 4 cores, n = 3 (exhaustive where ≤ 3·10⁶ profiles, else samples) | see log | | `results/k4_induct_ps_k4_n3.log` |
| k = 4 cores, n = 4, 5 (samples) | see log | | `results/k4_induct_ps_k4_n45.log` |
| H_1–H_5 (`k4/c4.md` §7; n = 5, 9, 13, 17, 21), SAT | every agent, every private good | 0 (D2) | `results/k4_induct_ht.log` |
| random general additive, n = 3, 4, m ≤ 8, values 0..R with zeros | 32,400 instances, every agent | 0 | `results/k4_induct_ps_general.log` |

Random and sampled tests are EVIDENCE only (PROMPT.md §5 rule 3). The exhaustive rows are single-implementation
exhaustive searches (the SAT encoding confirms the n = 2 row on samples); they are evidence for a conjecture, not a
certificate of anything in the ledger.

## 5. The gap: 4-good agents without a private good (Q4)

For a Q4 agent every d ∈ R_w is shared, and Lemma 2 does not apply: d → w needs, besides w unenvied by the other
agents, the margin θ_j(X′_w ∪ {d}) ≤ v_j(X′_j) for every other valuer j of d. Tested rules:
- *GPS* ("some X′ ∈ E(I − d) admits d → w", for some d): fails for a Q4 agent on 119 of 12,000 n = 3 (Q4 agent,
  profile) pairs.
- *PS-selected placement* H(w, d, h): take X′ ∈ E(I − d) minimizing the number of agents envying h, and give d to h.
  For P4 agents with d private and h = w it always works (Lemma 2 plus PS). In the n = 3 cores whose 4-good agents are
  all Q4, no triple (w, d, h) works on 62 of 1,100 sampled profiles (`attempts/k4-induct-q4-rules.md`; smallest
  configuration n = 3, m = 5: agents {0, 3, 4} (2, 4, 3), {1, 2, 3, 4} (6, 4, 8, 3), {1, 2, 4} (2, 3, 4)).
- *B-form* for a Q4 agent (delete w and d; give w nothing but d): r ≤ 1 for the best d on every sampled n = 5 core
  with one 4-good agent, r = 2 and 3 at n = 3.

What a proof of the Q4 step would have to supply is an X′ with *two* properties at once (w unenvied, and the valuers of
d satisfied with margin), which is what Proposition 5 also cannot supply for a second agent.

## 6. The B-form and LB₄'s owner constraint

In the B-form with d = a_w (w's top), X′ + (w ↦ {a_w}) is EFX₀ iff no bundle of X′ threatens w holding a_w
(the others see a new singleton only, L10). Bundles of ≤ 2 goods never do (θ_w of such a bundle is at most one good,
worth ≤ v_w(a_w)); so for a D2-shaped X′ the only obstruction is the large bundle containing a threatening set of
{b_w, c_w, d_w}, which is LB₄'s owner constraint (OC₄) (`k4/lb4.md` §1). With the best d the B-form needed r ≤ 2
everywhere tested (n ≤ 5), and r ≤ 1 for every sampled n = 5 core with one 4-good agent; but the statement "every X′"
fails at r = 1 already at n = 3 (§2).

## 7. What remains

1. **PS on 𝒞_0** (k ≤ 3 instances). With Theorem 4 it removes the P4 and PP4 agents from a minimal counterexample
   with one 4-good agent. By Proposition 6(b) it would follow from a *prescribed-owner* version of LB⁺ (every agent can
   be the owner of the padded large bundle); LB⁺'s Theorem A makes r (the last processed agent not upgraded) the owner
   except in its bad case, but the bad case's rotation can freeze r, and postponing w to the end of Phase 1 breaks
   (B2) for w (need chains may end at w in earlier blocks).
2. **PS on 𝒞_j in general**, whose own induction (Proposition 5) stops at R1 on the target and at a second agent's
   private good.
3. **Q4 agents**: an insertion rule for a shared good; none of the tested selection rules works (§5).

## Reproduce

```
gcc -O2 -o /tmp/k4_induct k4/induct.c -lm            # (induct_run.py and induct_ps.py compile it on first use)
python3 k4/induct_run.py results/k4_certs_2.json.gz --all --jobs=2 --rmax=3 --no-a --v --log=results/k4_induct_n2.log
python3 k4/induct_run.py results/k4_certs_3.json.gz --samples=500 --seed=7 --jobs=2 --rmax=3 --no-a --v --log=results/k4_induct_n3.log
python3 k4/induct_run.py results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
    results/k4_certs_4_pure.json.gz --samples=5 --seed=2 --jobs=2 --rmax=3 --no-a --v --log=results/k4_induct_n4.log
python3 k4/induct_ps.py results/k4_certs_2.json.gz --all --log=results/k4_induct_ps_k4_n2.log
python3 k4/induct_ps.py results/certs_5_6.json.gz --all --log=results/k4_induct_ps_k3_56.log
(cd k4 && for t in 1 2 3 4 5; do python3 induct_sat.py ht $t --d2; done)   # H_t, ~5 min
python3 attempts/k4_induct_attempts.py                                    # every failure above, by brute force, < 1 s
```
