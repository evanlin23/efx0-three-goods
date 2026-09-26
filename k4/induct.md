# k = 4: induction on the number of 4-good agents (insertion lemma)

Workstream `proof/k4-induct`. Ledger rows `K4.IND.*`: the written proofs are K4.IND.INS (Lemmas 1–3), K4.IND.STEP
(Theorem 4), K4.IND.PSRED (Propositions 5–6) and K4.IND.LAST (Lemmas 7–8), all CONJECTURE (two reviews of PR #43 found
them correct; the status is left to a later change); the conjectures are K4.IND.PS and K4.IND.LBO; the evidence rows
are K4.IND.PSE and K4.IND.Q4; the failures of §2 are K4.IND.X (REFUTED, re-derived by an independent brute force).
K4.D and K4.T are unchanged.

**The avenue.** Induct on j = the number of agents with 4 relevant goods. Base j = 0 is TARGET (k = 3, proved). Step
j → j + 1: pick a 4-good agent w and a good d ∈ R_w; I − d has at most j four-good agents, so it has an EFX₀ allocation
X′; an *insertion lemma* would turn X′ into an EFX₀ allocation of I by placing d with a bounded repair.

**Summary.**
- *As posed, the insertion lemma is false* (§2). For every choice of w and d, some EFX₀ allocation X′ of I − d is at
  repair distance ≥ 1 from every EFX₀ allocation of I already at n = 2, m = 4; ≥ 2 at n = 2, m = 5; ≥ 3 at n = 3, m = 5;
  ≥ 4 at n = 5, m = 6 (one 4-good agent; smallest found, n ≥ 3 sampled); at n = 5 over half of the sampled profiles need
  4. Deleting w together with d (B-form) or only w's value of d (V-form) also fails for every ρ ≤ 2 at n ≤ 4. For each of
  eight potentials (w's value either way, the number of agents envying w, utilitarian or Nash welfare, and
  combinations), "*every* maximizer of the potential on E(I − d) admits a placement of d" fails at n ≤ 3; on those
  instances the weaker some-maximizer form fails only for three of them (§2). Every failure is confirmed by an
  independent brute force (`attempts/k4_induct_attempts.py`).
- *For a private good the right statement is exact* (§3, Lemma 2, written proof): if d is valued by w only, X′ + (d → w) is
  EFX₀ **iff nobody envies w in X′**. So the step needs the right X′, never a repair.
- *Prescribed source* (PS(J, w)): J has an EFX₀ allocation in which nobody envies w. **Conjecture PS₄** (K4.IND.PS):
  PS holds for every agent of every instance with ≤ 4 relevant goods per agent. No failure in any test (§4): every
  strict profile of every k = 4 core with n = 2 (630,720 tests), 14.8 million profiles of the n = 3 k = 4 cores, samples
  of the k = 4 cores with n ≤ 6, the 251 k = 3 cores of `results/certs_5_6.json.gz` (every profile of the 15 with n = 5,
  m = 9; samples of the 236 with n = 6, m = 10, 11), the chain cores H_1–H_5 of `k4/c4.md` §7 (n ≤ 21, by SAT, D2 shape),
  and 162,000 random general additive instances (zeros and ties allowed; up to 8 relevant goods per agent). §4a
  states PS, where its own induction stops, and a candidate strengthening.
- *Conditional step* (§3, Theorem 4, written proof): if PS holds on the instances with ≤ j four-good agents, then every
  instance with ≤ j + 1 four-good agents in which some 4-good agent has a private good has an EFX₀ allocation; and if
  PS(I − p, w) holds for the connected strict cores I, a minimal counterexample among all instances with ≤ j + 1
  four-good agents is a connected k = 4 core, may be taken with strict types, and has **no 4-good agent with a private
  good** (all are Q4). **This does not close the induction**: its hypothesis (PS below) is stronger than the conclusion
  (TARGET above), and PS itself (PS₄ implies TARGET₄ outright) is open already for k ≤ 3.
- *PS reduces to two configurations* (§3, Proposition 5, written proof): a minimal counterexample (I, w*) to PS is connected,
  has no junk good, w* has no private good, and no other agent can be peeled (R1, R2). Not reduced: R1 at w* (w*
  top-heavy), and a private good of another agent (Lemma 2 would need that agent unenvied as well).
- *Q4 agents* (§5). For a 4-good agent without a private good every removable good is shared, and placing it needs
  margins for its other valuers that "w unenvied" does not give. Two negative results: "some X′ ∈ E(I − d) admits
  d → w" (h = w, existence form) fails for every d on 119 of 12,000 sampled n = 3 profiles with a Q4 agent; and the rules
  "d → h into **every** X′ ∈ E(I − d) with the fewest agents envying h" fail for every (w, d, h) on 128 of 2,200 profiles
  of the all-Q4 n = 3 cores and 813 of 4,700 of the n = 4 cores whose only 4-good agent is Q4. But on every sampled
  all-Q4 profile some (w, d, h) has *some* such minimizer admitting d → h, so a tie-break among minimizers is not ruled
  out. No proved or tested-complete insertion rule for Q4 is known.
- *A constructive route to PS at k = 3* (§4b): run LB⁺ with the target w processed *last*. Lemmas 7 and 8 (written
  proofs): if w ends Phase 1 with its top good (or with its second good in Lemma 8's configuration), w is a valid owner and
  hence unenvied. Conjecture LBO (K4.IND.LBO): with the upgrade loop stopped anywhere and at most one LB⁺ rotation, some
  run always makes w an owner or gives it a free slot; no miss on every profile of every k = 3 core with n ≤ 5, nor on the
  instances I − p of Theorem 4(b) with a P4 agent (n ≤ 4 exhaustively). What is missing is the choice of the run, an
  exchange argument of the kind open PR #37 (not merged) proposes for C₄¹∃.

## 0. Setting and notation

Instances: agents N, goods M, nonnegative additive valuations, R_i = {g : v_i(g) > 0}. E(J) = the EFX₀ allocations of
an instance J (complete, raw definition: v_i(X_i) ≥ v_i(X_j ∖ {h}) for all i ≠ j and h ∈ X_j). θ_i(B) = v_i(B) −
min_{g ∈ B} v_i(g) (0 if |B| ≤ 1); i is safe iff v_i(X_i) ≥ θ_i(X_j) for all j ≠ i. Agent j *envies* w in X if
v_j(X_w) > v_j(X_j). 𝒟_j = the instances with |R_i| ≤ 4 for every i and at most j agents with |R_i| = 4. Kinds of 4-good
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
  their description. Agrees with brute force on 3,162 random checks (PS and existence, with and without D2;
  `k4/induct_selftest.py`, `results/k4_induct_selftest.log`).
- `k4/induct_rules.py`: the placement rules of §5. `k4/induct_lbo.py`: the LBO tests of §4b (exact Lemma 1 tests of
  `proofs/lb_last_step.md` on every state; every state checked to be a valid pre-allocation).
- `k4/induct_bf.py`: an independent pure-Python brute force (itertools over all allocations, raw definition), used
  by `attempts/k4_induct_attempts.py` to re-derive every failure claimed here.

Two bugs found and fixed during the work: a D2 counter indexed with the unassigned-good marker, and the allocation
store sized with the previous instance's m (found by AddressSanitizer). All logs in `results/k4_induct_*` were produced
after both fixes; `k4/induct.c`, built with AddressSanitizer and UBSan, runs 5,043 mixed tasks on random certified
cores with no report (`results/k4_induct_selftest.log`). Its bounds: n ≤ 24 agents, m ≤ 64 goods (checked on input).

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
Φ below, some profile has, for every (w, d), a maximizer of Φ on E(I − d) into which d cannot be placed (r ≥ 1), so
"*every* maximizer admits a placement" fails (`attempts/k4-induct-potentials.md`). The weaker "*some* maximizer admits a
placement" also fails on the smallest instances below only for −v_w, (−#agents envying w, v_w) and (−#agents envying w,
utilitarian); for the other five potentials it holds there and was not tested further:

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

(A reviewer of PR #43 reports, from an own exhaustive run, 88 failures of the V-form potential among 2,237,312 n = 3,
m = 5 profiles; that run is not in this repository [unverified here]. The n = 5 run of §2 did not include the V-form,
so the V_* lines of `results/k4_induct_n5.log` are empty.)

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

So for a private good the whole question is the choice of X′, and no repair is ever needed. Equivalently: *some
X′ ∈ E(I − p) leaves w unenvied iff some X ∈ E(I) gives p to w and leaves w safe without p*, where "w safe without p"
means X − p ∈ E(I − p) (X with p removed from X_w). (⇒: X = X′ + (p → w), and X − p = X′. ⇐: X′ = X − p; since
X = X′ + (p → w) is EFX₀, Lemma 2's (⇒) says nobody envies w in X′.)

**Lemma 3 (placing p elsewhere).** With p, w, X′ as in Lemma 2 and h ≠ w, X′ + (p → h) is EFX₀ iff (i) no agent other
than h and w envies h in X′, and (ii) θ_w(X′_h ∪ {p}) ≤ v_w(X′_w). (If X′_h = ∅ both hold: {p} is a singleton.)

*Proof.* As for Lemma 2: h's value and view do not change (v_h(p) = 0); an agent j ∉ {h, w} sees X′_h ∪ {p} with p
worthless, so its threat is v_j(X′_h) (remove p) and it is safe iff it does not envy h; w sees X′_h ∪ {p}. ∎

**Theorem 4 (conditional induction step).** Let j ≥ 0.
- (a) Suppose *PS holds on 𝒟_j*: for every instance J ∈ 𝒟_j and every agent w of J, some X ∈ E(J) leaves w
  unenvied. Then every instance I ∈ 𝒟_{j+1} in which some agent w with |R_w| = 4 has a good p that no other agent
  values has an EFX₀ allocation (in which w is unenvied).
- (b) Suppose only: PS(I − p, w) holds for every connected k = 4 core I ∈ 𝒟_{j+1} with strict types, every agent w of I
  with |R_w| = 4 and every good p private to w (implied by (a)'s hypothesis, since I − p ∈ 𝒟_j). Let I be a
  counterexample to TARGET₄ among all instances with ≤ j + 1 four-good agents (and ≤ 4 relevant goods per agent, i.e.
  in 𝒟_{j+1}) with the fewest agents, and among those the fewest goods. Then I is a connected k = 4 core, may be taken
  with strict types, and **no agent of I with four relevant goods has a private good**.

*Proof.* (a) I − p ∈ 𝒟_j: w has three relevant goods left, and no other agent's relevant set changes because nobody
else values p. By PS, some X′ ∈ E(I − p) leaves w unenvied, and by Lemma 2, X′ + (p → w) ∈ E(I), with w unenvied.
(b) 𝒟_{j+1} is closed under sub-instances (a sublist of the agents and of the goods, the same values): relevant sets
only shrink, and an agent with four relevant goods in the sub-instance has the same four in the larger one (the
argument of `EFX.atMostOne4_sublist`, `lean/EFX/K4One.lean`, which is the case j = 0). It is also closed under
K4.TIE's perturbation, which keeps every R_i (`EFX.pos_tieBreak_iff`). The proof of K4.MC0 (a)–(c) (`k4/MINCEX.md`
§1) uses only these operations: each K4.CORE step (L3, R1, R2) and each component is a sub-instance with fewer agents
or goods whose EFX₀ allocations extend. So it applies within 𝒟_{j+1}, and a minimal counterexample I is a connected
k = 4 core. (Lean: `EFX.core_reduction4_conn_of`, PR #39, merged, ledger row K4.ONE.FRAME, proves this reduction in
existence form for any class closed under sub-instances, so for 𝒟_{j+1} at every j: if every connected core of the
class has an EFX₀ allocation, every instance of the class has one.) K4.TIE's perturbation I^ε of I has the same
agents, goods and relevant sets, is again a counterexample (K4.TIE), hence again minimal, and has strict types. If a
4-good agent w of I had a private good p, then p would be private to w in I^ε too, and PS(I^ε − p, w) with Lemma 2
would give an EFX₀ allocation of I^ε, a contradiction. ∎

*What Theorem 4 does not give.* The hypothesis of (a), PS on 𝒟_j, is stronger than TARGET on 𝒟_j, and its conclusion
is TARGET (not PS) on part of 𝒟_{j+1}. So the step does not iterate by itself: the induction on j closes only if PS
itself is proved at every level. Indeed **PS₄** (PS for every instance with ≤ 4 relevant goods per agent, any number of
them with four) already implies TARGET₄ outright (PS for any one agent gives an EFX₀ allocation). What Theorem 4 does
show is that, *as far as the P4 and PP4 agents are concerned*, the whole difficulty of the step j → j + 1 is the
choice of X′, and that the choice needed is exactly an unenvied w (Lemma 2 is an equivalence). The hypothesis of (b)
at j = 0 is a statement about k = 3 instances (I − p with I a core with one 4-good agent), which is what §4b's LBO
targets.

Where the hypotheses enter: |R_i| ≤ 4 only through 𝒟_j (I − p has one 4-good agent fewer); the core structure only
through "a P4 or PP4 agent has a private good"; strictness and connectivity only to place the minimal counterexample
among the certified and structured objects of `k4/MINCEX.md`. Lemma 2 itself uses nothing but additivity.

**Proposition 5 (PS is inductive away from two configurations).** Let 𝒦 be a class of instances closed under deleting
agents and goods (e.g. 𝒟_j), and let (I, w*) be a counterexample to PS in 𝒦 (no X ∈ E(I) leaves w* unenvied) with
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
(Lemma 2 needs that agent unenvied as well, and two agents cannot in general both be unenvied: of two identical
agents whose bundles have different values, the poorer envies the richer).

**Proposition 6 (PS as junk absorption; the easy cases).**
- (a) PS(J, w) holds iff J + z, with z a new good valued by nobody, has an EFX₀ allocation that gives z to w
  (Lemma 2 with v_w(z) = 0; conversely Lemma 1, and deleting z changes nobody's values).
- (b) Hence PS(J, w) holds whenever some EFX₀ allocation of J, after adding goods valued by nobody, gives w a bundle
  that no R_j contains: for instance, when w can be the owner of the large bundle of a D2 allocation padded to
  k + 1 goods (Lemma 1(a)). At k = 3 this is the owner of LB⁺ (`proofs/lb_last_step.md`) when the owner can be
  prescribed; at k = 4, the owner of LB₄.
- (c) PS(J, w) holds when |R_i| ≤ 2 for every agent i ≠ w (w arbitrary): run serial dictatorship with w last (each agent takes its favorite
  remaining good; w takes the rest). This is EFX₀, as in L2c (proof below), and an agent i ≠ w values X_w at most at the value of the
  good of R_i it did not pick, which was still available at its turn, so at most v_i(X_i).

*Proof of (c).* Take i ≠ w with pick g_i (if i picked nothing, every good of R_i was taken before its turn, so X_w
contains no good of R_i). X_w ∩ R_i ⊆ R_i ∖ {g_i}, which has at most one good, and that good was available when i
picked g_i, so v_i(X_w) ≤ v_i(g_i) ≤ v_i(X_i). EFX₀ for i ≠ w: the bundles other than X_w are single goods; toward
X_w, θ_i(X_w) ≤ v_i(X_w) ≤ v_i(X_i). For w (any number of goods): every bundle other than X_w is a single good. ∎

## 4. Evidence for PS (K4.IND.PS, K4.IND.PSE)

PS(I, w) for every agent w, and PS(I − p, w) for every 4-good w with a private good p (the input Theorem 4 needs), with
`k4/induct_ps.py` (early-exit search, `k4/induct.c` task Q, cross-checked against the full enumeration of task P on
889 random instances, `results/k4_induct_selftest.log`, and against the independent SAT encoding of `k4/induct_sat.py` on 400 random k = 4 core
profiles: 5,074 tests, 0 mismatches, `results/k4_induct_ps_satcheck.log`), and with the SAT encoding alone for the
chain cores:

| instances | tests | failures (all X / D2 X) | log |
|---|---|---|---|
| every strict profile of every k = 4 core with n = 2 (189,216) | 378,432 PS(I, w) + 252,288 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n2.log` |
| k = 4 cores with n = 3: 14,782,912 profiles (35 cores exhaustively, 16 with 100,000 random profiles each) | 44,348,736 PS(I, w) + 49,737,600 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n3.log` |
| every k = 4 core with n = 4 or 5 (32,586 cores): 20 random profiles each (651,720) | 3,238,560 PS(I, w) + 1,497,520 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n45.log` |
| every k = 4 core with n = 6 and one 4-good agent (26,866 cores): 3 random profiles each (80,598) | 483,588 PS(I, w) + 57,453 PS(I − p, w) | 0 / 0 | `results/k4_induct_ps_k4_n6_1.log` |
| k = 3 cores of `results/certs_5_6.json.gz`: every ranking profile of the 15 with n = 5 (116,640), 200 random profiles of each of the 236 with n = 6 (47,200) | 583,200 + 283,200 PS(I, w) | 0 / 0 | `results/k4_induct_ps_k3_n5.log`, `results/k4_induct_ps_k3_n6.log` |
| H_1–H_5 (`k4/c4.md` §7; n = 5, 9, 13, 17, 21), SAT | every agent (65) and every private-good insertion | 0 (D2) | `results/k4_induct_ht.log` |
| random general additive, n = 3 (m = 4..8), n = 4 (m = 4..7), values 0..R with zeros and ties | 162,000 instances, 558,000 tests | 0 | `results/k4_induct_ps_general.log` |

Random and sampled tests are EVIDENCE only (PROMPT.md §5 rule 3). The exhaustive rows are single-implementation
exhaustive searches; they are evidence for a conjecture, not a certificate of anything in the ledger.

*Literature.* Whether PS (for general additive valuations, or for EFX instead of EFX₀) appears in the literature, or is
known to fail, was not checked [unverified]. For two agents it holds for any additive valuations with an EFX₀ split
for w's valuation: w splits, the other agent chooses and envies nothing. Nothing here uses that remark.

## 4a. PS in three statements (for comparing routes)

**(1) The statement.** PS(J, w): some X ∈ E(J) has v_j(X_w) ≤ v_j(X_j) for every agent j (nobody envies w).
**Conjecture PS₄** (K4.IND.PS): PS(J, w) for every instance J with |R_i| ≤ 4 for all i (any number of 4-good agents)
and every agent w of J.
- Equivalent form (Proposition 6(a)): J + z, where z is a new good valued by nobody, has an EFX₀ allocation giving z
  to w.
- PS₄ implies TARGET₄: PS for any one agent gives an EFX₀ allocation.
- Proved cases: every agent other than w has ≤ 2 relevant goods (Proposition 6(c)); two agents, given an EFX₀ split
  for w's valuation (§4, remark). At k = 3,
  LB⁺ with w processed last covers the runs in which w still finds its top (Lemma 7), with any values of w, and one
  configuration in which w ends with its second good (Lemma 8).
- Evidence: §4 (no failure anywhere) and §4b.

**(2) Where PS's own induction stops** (Proposition 5). A minimal counterexample (I, w*) is connected, every good
has a valuer, w* has no private good, and no agent other than w* can be peeled by R1 or R2. Two configurations are
not reduced:
- *(i) R1 at the target.* w* is top-heavy (v_{w*}(a) ≥ v_{w*}(R_{w*} ∖ {a}) for its top a, which includes
  |R_{w*}| ≤ 2). Peeling (w*, a) gives X = X′ + (w* ↦ {a}) for X′ ∈ E(I − w* − a). This X is EFX₀, but w* is
  unenvied only if v_j(X′_j) ≥ v_j(a) for every valuer j of a. Minimality supplies no such floor.
- *(ii) A private good p of another agent i* (not R2-peelable: v_i(p) < v_i(R_i ∖ {p})). Minimality gives
  X′ ∈ E(I − p) with w* unenvied. By Lemma 2, p → i keeps EFX₀ iff i is also unenvied in X′. By Lemma 3, p → h ≠ i
  needs a margin for i. Asking for two unenvied agents at once is false in general: of two identical agents whose
  bundles have different values, the poorer envies the richer.

**(3) The strongest PS-type hypothesis that might induct.** None is shown to induct. The two plain strengthenings are
false:
- two agents unenvied at once fails (identical agents);
- a floor v_j(X_j) ≥ t_j fails already for two identical agents on two goods, with both thresholds just above the
  smaller good's value.

Obstacle (ii) consumes exactly the following *slack form*, which avoids the identical-agents counterexample:

> **PS₂ˢ(J; w, i, s)** (w ≠ i, s ≥ 0): some X ∈ E(J) has: nobody envies i; nobody other than i envies w; and
> v_i(X_w) ≤ v_i(X_i) + s.

Take J = I − p and s = v_i(p). Then X′ + (p → i) is EFX₀ by Lemma 2, since i is unenvied. And w* is unenvied in it:
agents j ≠ i see p as worthless, and for i, v_i(X′_w*) ≤ v_i(X′_i) + v_i(p). With s = 0, PS₂ˢ is the false two-agent
form; with s = ∞ it asks only that i be unenvied and that w be unenvied by everyone except i. Whether the family
{PS, PS₂ˢ} is closed under Proposition 5's reductions was not checked, and PS₂ˢ was not tested. Obstacle (i) looks better
suited to a construction than to a hypothesis on a smaller instance: in LB⁺ with the target processed last, a
top-heavy target is covered whenever it still finds its top (Lemma 7). Per the change of strategy for k = 4, neither is
opened as new work here.

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

*Proof.* (o) *Padding.* Before running Phase 1, add goods valued by nobody until ω ≥ 2. They are never picked, so
the run is unchanged, and they are junk, so they count in ω; everything below is about the padded instance.
(i) *w is a terminal and needs nothing.* An agent i ≠ w that needed Y_w would, by (I1), see Y_w picked before
its turn, but w picks last; and w holds its top, so N_w = ∅. (ii) *Exposed agents lead blocks.* Let x ∈ E_w, that is
x ≠ w, Y_x = a_x and {b_x, c_x} ⊆ J ∪ {Y_w}. At x's turn a_x, the junk and Y_w were all still available, so
R_x ⊆ G, and by (I3) x was processed at an insertion step: it leads its block. Distinct exposed agents lead distinct
blocks. π_x = {b_x, c_x} ∩ J is nonempty, and no exposed pair lies in base(w) = {Y_w}. (iii) *A terminal per exposed
agent.* If x ∈ T, let τ(x) = x (cap 1). If x ∈ F, some j ∉ U needs Y_x; j ≠ w because N_w = ∅, so by (B2′) j lies in
x's block and comes after x. Repeating while the current agent is frozen follows a need chain inside x's block (the
processing order increases, so it stops) that ends at a terminal τ(x) ≠ w of x's block, with cap ≥ 1. (iv) *Count.*
The τ(x) lie in distinct blocks, so they are distinct terminals other than w, and S − cap(w) ≥ |E_w| ≥ |H| for H made of
one good of each π_x. By Lemma 1, with ω ≥ 2 there is a completion with owner w that satisfies (OC), and it is EFX₀ by
Theorem 1′. (v) *Unenvied.* The owner's bundle has ω + 2 ≥ 4 goods (`proofs/lb_last_step.md` Remark 1), so no R_j
(three goods) contains it, and by Lemma 1 nobody envies w. Some added goods may land in other agents' slots, not only
in w's bundle. Deleting all the added goods keeps the allocation EFX₀ (a good nobody values changes no one's value of
any bundle, and removing it from a bundle only removes a threat) and changes no one's value of X_w, so w stays
unenvied. ∎

Lemma 7 is the easy case: N_w = ∅, so no need chain can leave its block through w, and LB⁺'s bad case cannot occur.
When w picks its second or third good, or nothing, chains from up to |N_w| ≤ 3 blocks can end at w, each costing one
terminal in the count.

**Lemma 8.** Suppose all agents are balanced. If, in some run of Phase 1 with w last, w picks its second good b_w,
its third good c_w is junk (picked by nobody), and no agent x ≠ w holding its top has {b_x, c_x} = {b_w, c_w}, then w
is a valid owner of P = (Y, {w}) (w upgraded alone), and I has an EFX₀ allocation in which nobody envies w.

*Proof.* P is valid: Y_w = b_w, c_w ∈ J, and b_w ∉ NA because nobody needs Y_w (as in Lemma 7 (i)); in P every good
of NA is still a pick, J shrinks by c_w, and w needs nothing, so NA only shrinks and (V1), (V2) hold. The owner is
w ∈ U with base {b_w, c_w} and cap(w) = 0. An agent x is exposed w.r.t. w iff x ∉ U, Y_x = a_x and
{b_x, c_x} ⊆ (J ∖ {c_w}) ∪ {b_w, c_w} = J ∪ {Y_w}: the same condition as in Lemma 7, so every exposed agent leads its
block (argument (ii) there). By hypothesis no exposed pair lies inside base(w), so each π_x = {b_x, c_x} ∩ (J ∖ {c_w})
is nonempty. Since w ∈ U needs nothing, a need chain from a frozen exposed x never reaches w; as in Lemma 7 (iii) it ends
at a terminal of x's block, and the count S − cap(w) = S ≥ |E_w| ≥ |H| holds. Lemma 1 and Theorem 1′ (which uses
balance for the upgraded w) give an EFX₀ completion with owner w, of |base(w)| + cap(w) + ω = ω + 2 goods; padding
with goods valued by nobody to ω ≥ 2, as in Lemma 7 (v), makes w unenvied. ∎

The excluded configuration is real: when another agent holding its top has lower pair {b_w, c_w}, w with base
{b_w, c_w} threatens it, and (OC) fails for every completion with owner w. Lemmas 7 and 8 are checked directly on
every run of Phase 1 with w last of every profile of every k = 3 core with n ≤ 4 (`k4/induct_lbo.py --lemmas`,
`results/k4_induct_lbo_lemmas_n234.log`: 488,696 runs for Lemma 7 and 109,656 for Lemma 8, no failure; 26,020 runs fall
in the excluded configuration) and n = 5 (`results/k4_induct_lbo_lemmas_n5.log`: 60,581,840 and 13,289,504 runs, no
failure).

**Conjecture LBO** (K4.IND.LBO). In the setting above (agents other than w: three goods, balanced; w: at most three
goods), there are a run of Phase 1 with w last, a state of LB's upgrade loop (stopped anywhere; never upgrading w if it
is top-heavy), and optionally one LB⁺ rotation (Theorem B's: along a need chain from k*, the last agent processed at an
insertion step, when k* holds its top and b_{k*}, c_{k*} ∈ J ∪ {Y_r}, to r, the last-processed agent not upgraded, which
is w unless w was upgraded), whose valid pre-allocation has w as a valid owner (Lemma 1), or has w as a terminal with a slot while
some other valid owner o leaves a slot free (|H| ≤ S − cap(o) − 1). Either way, by Theorem 1′ and Lemma 1 (padding as in
Lemma 7), I has an EFX₀ allocation in which nobody envies w.

LBO would give the hypothesis of Theorem 4(b) at j = 0 (PS(I − p, w) for the connected strict k = 4 cores I with one
4-good agent w and p private to w), and hence: *TARGET₄ holds for every instance with at most one 4-good agent unless
the minimal counterexample's 4-good agent is Q4* (for a PP4 agent, I − p leaves w with three goods, one of them
private, which is inside LBO's setting; the tests below cover P4 only, and for the minimal counterexample to all of
TARGET₄, K4.MC2 already excludes agents with two private goods; whether its proof stays inside 𝒟_{j+1} was not
checked).

*Evidence* (`k4/induct_lbo.py`: exact Lemma 1 tests on every state; every state is checked to be a valid
pre-allocation; single implementation):
- every ranking profile of every connected k = 3 core with n ≤ 5 (`results/certs_lb_2_6.json.gz`): 217,224 (profile, w)
  pairs for n ≤ 4 and 11,391,840 for n = 5, no miss (`results/k4_induct_lbo_n234.log`, `results/k4_induct_lbo_n5.log`);
- 20 random ranking profiles of each of the 3,093 connected k = 3 cores with n = 6 (371,160 pairs): no miss
  (`results/k4_induct_lbo_n6.log`);
- the instances J = I − p for every strict profile of every k = 4 core with n ≤ 4 whose only 4-good agent is P4
  (53,568 for n ≤ 3, 3,172,608 for n = 4), and 20 random profiles per such core with n = 5 (12,520), about half of them
  with w top-heavy in J: no miss (`results/k4_induct_lbo_k4_n23.log`, `results/k4_induct_lbo_k4_n4_all.log`,
  `results/k4_induct_lbo_k4_n5.log`; `results/k4_induct_lbo_k4_n4.log` is an earlier sample of 300 profiles per n = 4
  core). The cores whose only 4-good agent is PP4 were not tested (6 cores with n ≤ 3, 37 with n = 4, 391 with n = 5);
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
argument on insertion sequences of the kind PR #37's Lemma X needs for C₄¹∃ (PR #37 is open and not merged; its
Lemma X is not in this repository, and K4.C4.1X is not a ledger row on main).
No fixed insertion rule can do it: every run of Phase 1 with w last is the index-order run of some relabeling of the
agents, and some runs fail; the choice has to depend on the instance (as LB's lookahead does).

## 5. 4-good agents without a private good (Q4)

For a Q4 agent every d ∈ R_w is shared, and Lemma 2 does not apply: d → w needs, besides w unenvied by the other
agents, the margin θ_j(X′_w ∪ {d}) ≤ v_j(X′_j) for every other valuer j of d. Tested rules:
- *GPS* ("some X′ ∈ E(I − d) admits d → w", for some d ∈ R_w): fails for some Q4 agent on 119 of the 12,000 sampled
  n = 3 profiles that have a Q4 agent (`results/k4_induct_n3.log`, statistic GPS_Q4_anyd), and on 134 of 3,275 at
  n = 4 (`results/k4_induct_n4.log`). There d can only go to another agent.
- *PS-selected placement* H(w, d, h): among the X′ ∈ E(I − d) minimizing the number of agents envying h, give d to h;
  the rule *works* if d → h keeps EFX₀ for **every** such minimizer. For P4 agents with d private and h = w it always
  works (Lemma 2 plus PS: 13,600 of 13,600 n = 3 cases). In the n = 3 cores whose 4-good agents are all Q4, no triple
  (w, d, h) works on 128 of 2,200 sampled profiles (`results/k4_induct_rules_n3.log`); in the n = 4 cores whose only
  4-good agent is Q4 (the case j = 0 → 1), on 813 of 4,700 (`results/k4_induct_rules_n4_1.log`). Smallest
  configuration found (`attempts/k4-induct-q4-rules.md`): n = 3, m = 5, agents {0, 3, 4} (2, 4, 3), {1, 2, 3, 4}
  (6, 4, 8, 3), {1, 2, 4} (2, 3, 4).
- *The existence form of the same rules is not refuted*: on every one of those 2,200 and 4,700 profiles some (w, d, h)
  has *some* minimizer admitting d → h (on the smallest configuration, 6 of its 12 triples). So a tie-break among the
  minimizers may still work; the only existence-form obstruction shown is GPS above, which concerns h = w only.
- *B-form* for a Q4 agent (delete w and d; give w nothing but d): for the best d, repair r ≤ 1 on every sampled n = 5
  profile (cores with one or two 4-good agents, `results/k4_induct_n5.log`), but r = 2 and r = 3 occur at n = 3
  (267 and 2 of the 12,000 profiles with a Q4 agent).

What a proof of the Q4 step would have to supply is an X′ with *two* properties at once (h unenvied, and the valuers
of d satisfied with margin), which is what Proposition 5 also cannot supply for a second agent. No insertion rule for
Q4 is proved, and none is tested complete; the every-minimizer rules above are refuted, their existence forms are
open.

**H_t from this point of view.** In the chain cores H_t of `k4/c4.md` §7 (where LB₄ʳ needs unboundedly many
rotations), ℓ and the x_{j,i} are PP4 agents and only the y_j are Q4. PS held for every agent of H_1–H_5 and for every
H_t − p with p a private good (`results/k4_induct_ht.log`), so Lemma 2 inserts each private good with no repair; the
difficulty of H_t for the induction is concentrated in its t Q4 agents y_j, whose goods are the tops
a_{j,i} of three PP4 agents and a good of the next gadget.

## 6. The B-form and LB₄'s owner constraint

In the B-form with d = a_w (w's top), X′ + (w ↦ {a_w}) is EFX₀ iff no bundle of X′ threatens w holding a_w
(the others see a new singleton only, L10). Bundles of ≤ 2 goods never do (θ_w of such a bundle is at most one good,
worth ≤ v_w(a_w)); so for a D2-shaped X′ the only obstruction is the large bundle containing a threatening set of
{b_w, c_w, d_w}, which is LB₄'s owner constraint (OC₄) (`k4/lb4.md` §1). With the best (w, d) the B-form needed
ρ ≤ 3 everywhere tested (n ≤ 5; §2's table): ρ = 3 on 1 of the 5,010 sampled n = 4 profiles, ρ = 2 on 1 of the 800
sampled n = 5 profiles (cores with one or two 4-good agents), ρ ≤ 1 on the other 799; for the Q4 agents of those n = 5
profiles, ρ ≤ 1 with the best d (§5). The statement "every X′, ρ ≤ 1" fails already at n = 3, and "ρ ≤ 2" at n = 4
(§2).

## 7. What remains

1. **PS on 𝒟_0** (k ≤ 3 instances), at least for the instances I − p of §4b (the hypothesis of Theorem 4(b) at
   j = 0). With Theorem 4(b) it removes the P4 and PP4 agents from a minimal counterexample with one 4-good agent. Route: conjecture LBO (§4b). Lemma 7 proves it when w
   ends Phase 1 (w last) with its top. Open: the runs in which w ends with its second or third good or with nothing,
   where need chains from up to three blocks end at w; the upgrades (second good) and one rotation (third good,
   nothing) repair them in every test, but only for a well-chosen run, so a proof needs an exchange argument on
   insertion sequences, like PR #37's Lemma X for C₄¹∃.
2. **PS on 𝒟_j in general**, whose own induction (Proposition 5) stops at R1 on the target and at a second agent's
   private good. Theorem 4 is stated for every j, but its hypothesis at level j is PS on 𝒟_j (or, for (b), PS(I − p, w)
   for the cores of 𝒟_{j+1}), which none of the results here supplies for any j ≥ 1; §4b targets only j = 0.
   (If PS held for every instance smaller than I in the order (j, n, m), Lemma 2 would remove every agent with a
   private good, P3 included, from a minimal counterexample, leaving only Q3 and Q4 agents; but that is PS at the same
   level j, which is exactly what Proposition 5 cannot reach.)
3. **Q4 agents**: an insertion rule for a shared good. The tested selection rules fail in their every-minimizer form
   (§5), already with a single Q4 agent (j = 0 → 1); their existence forms held on every sampled profile, and the only
   existence-form obstruction shown is GPS (h = w).

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
python3 k4/induct_ps.py results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
    results/k4_certs_4_pure.json.gz results/k4_certs_5_n4_1.json.gz results/k4_certs_5_n4_2.json.gz results/k4_certs_5_n4_3.json.gz \
    results/k4_certs_5_n4_4.json.gz results/k4_certs_5_pure.json.gz --samples=20 --seed=5 --jobs=2 --log=results/k4_induct_ps_k4_n45.log  # ~20 min
python3 k4/induct_ps.py --general --per=2000 --jobs=2 --log=results/k4_induct_ps_general.log
python3 k4/induct_ps.py results/certs_5_6.json.gz --n=5 --all --jobs=4 --log=results/k4_induct_ps_k3_n5.log
python3 k4/induct_ps.py results/certs_5_6.json.gz --n=6 --samples=200 --seed=8 --jobs=4 --log=results/k4_induct_ps_k3_n6.log
python3 k4/induct_ps.py results/k4_certs_6_n4_1.json.gz --samples=3 --seed=6 --jobs=2 --log=results/k4_induct_ps_k4_n6_1.log
(for t in 1 2 3 4 5; do python3 k4/induct_sat.py ht $t --d2; done) > results/k4_induct_ht.log   # ~5 min (the log adds a command line)
python3 k4/induct_sat.py crosscheck 400 1 results/k4_certs_3.json.gz results/k4_certs_4_n4_2.json.gz \
    results/k4_certs_4_pure.json.gz > results/k4_induct_ps_satcheck.log
python3 k4/induct_selftest.py --log=results/k4_induct_selftest.log      # SAT vs brute force, task Q vs P, sanitizers
python3 k4/induct_rules.py results/k4_certs_3.json.gz --samples=200 --seed=1 --jobs=2 --log=results/k4_induct_rules_n3.log
python3 k4/induct_rules.py results/k4_certs_4_n4_1.json.gz --samples=100 --seed=2 --jobs=2 --log=results/k4_induct_rules_n4_1.log
python3 k4/induct_lbo.py results/certs_lb_2_6.json.gz --n=2,3,4 --all --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_n234.log
python3 k4/induct_lbo.py results/certs_lb_2_6.json.gz --n=5 --all --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_n5.log
python3 k4/induct_lbo.py --from-k4 results/k4_certs_2.json.gz results/k4_certs_3.json.gz --all --jobs=2 --last --partial --rot \
    --log=results/k4_induct_lbo_k4_n23.log
python3 k4/induct_lbo.py --from-k4 results/k4_certs_4_n4_1.json.gz --all --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_k4_n4_all.log
python3 k4/induct_lbo.py --from-k4 results/k4_certs_4_n4_1.json.gz --samples=300 --seed=4 --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_k4_n4.log
python3 k4/induct_lbo.py --from-k4 results/k4_certs_5_n4_1.json.gz --samples=20 --seed=5 --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_k4_n5.log
python3 k4/induct_lbo.py results/certs_lb_2_6.json.gz --n=6 --samples=20 --seed=3 --jobs=2 --last --partial --rot --log=results/k4_induct_lbo_n6.log
python3 k4/induct_lbo.py --lemmas results/certs_lb_2_6.json.gz --n=2,3,4 --jobs=2 --log=results/k4_induct_lbo_lemmas_n234.log
python3 k4/induct_lbo.py --lemmas results/certs_lb_2_6.json.gz --n=5 --jobs=2 --log=results/k4_induct_lbo_lemmas_n5.log   # ~25 min
python3 k4/induct_lbo.py --by-type results/certs_lb_2_6.json.gz --n=4 --jobs=2 --log=results/k4_induct_lbo_bytype_n4.log
```
The variants of LBO (each ingredient dropped; every run) are listed with their commands in
`results/k4_induct_lbo_variants.log`.
