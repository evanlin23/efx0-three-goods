# k = 4: one target statement for TARGET₄

Workstream `proof/k4-strategy` (PR #56). Ledger rows K4.STRAT.* (CONJECTURE / EVIDENCE only) and open item 22. Nothing
here changes K4.D or K4.T. The test bed is the counterexample suite `k4/suite/` (README there). Evidence only
(PROMPT.md §5 rule 3): every "survives" below means "no failure on the data named", never a proof.

## Summary

**The question.** Since Theorem Z the k = 4 program has followed one pattern:
1. pick an extremal pre-allocation (a maximum of some potential);
2. argue that a non-completable one admits an improving move;
3. find a small counterexample, and add a new move or sub-case.

The task was to find one target statement S with a single proof architecture such that:
- S, with what is in Lean, implies TARGET₄;
- S survives every known counterexample.

The alternative outcome was to say plainly that no candidate survives.

**What the suite shows.** Three forms of candidate have never survived the next n. The other known instances refute
variants of specific algorithms (LB₄, LS4, GM₄, insertion lemmas) or, as found here, strengthened induction hypotheses
(PS_W, PS-OWNER):
- **"every maximum of Φ is completable"**: over 𝒫, over the configurations at min-frozen keys, over all keys, and over
  the spaces with three-good bases 𝒫_T. It fails for more than 40 potentials, from n = 2 to n = 6.
- **a fixed catalogue of moves raising a proxy potential**:
  - LIL, with the catalogue as #51's text states it, fails at n = 3 and n = 4 (#51's reviewers);
  - LIL with #51's broader implemented catalogue fails on a non-core n = 3 instance;
  - #41's and #53's local lemmas fail at n = 3 and n = 4;
  - Φ′-raising moves that keep the needed set fail at n = 4 (SAME_N).
- **counting certificates**: COUNT, the natural global count behind Theorem Z′ and #51's Lemma C, fails at n = 3,
  m = 8 (§2.1).

Each failure has the same shape: the instance has a completable pre-allocation, but the proxy the argument climbs
(r, Λ, t, Pareto order, a count) does not lead to it.

**What survives the whole suite and every sample tested.**
- Three existence statements:
  - C₄ᵐⁱⁿ (both forms);
  - K4.D;
  - PS (prescribed unenvied agent).

  They are targets, not architectures.
- Two architectures:

| rank | target statement | implies TARGET₄ through (Lean) | proof architecture | status |
|---|---|---|---|---|
| **1** | **Conjecture DL₂** (§3): at the fewest frozen agents the removal-only deficit has no local minimum above 0 for exchanges of at most two agents' bases | DL₂ ⟹ C₄ᵐⁱⁿ (removal-only) by finite descent (to formalize; `EFX.C4min.DeficitLE` is the deficit), then `EFX.C4min.target4_of_C4minRO` / `…ROConn` (K4.C4MIN.FRAME) | one potential, the deficit itself (no proxy); moves unrestricted in form but of size ≤ 2; a case analysis over the covering obstruction of Lemma H1 (augmenting-path style) | CONJECTURE. k* ≤ 2 on every core of the suite and on 24,314 sampled gap profiles with n ≤ 5; k* = 3 only on the non-core LIL instance |
| 2 | LB₄ʳ with rule F and at most one rotation (#44, K4.AD.*; "some first agent, every continuation", K4.AD.C1) | `EFX.LB4R.Succeeds` (K4.C4.FRAME) with a first agent chosen per profile (a C₄∃-type statement) | the k = 3 architecture that worked: Phase 1 counting (A₄⁺ᴺ) plus one rotation (B₄), with the global choice of the first agent | CONJECTURE. #44 found no failure on 3.6·10¹⁰ exhaustive profiles (n ≤ 4, ≤ 3 four-good agents). It succeeds, with at most one rotation, on all 148 core instances of the suite that it was run on; H₅ is covered by #44's Proposition H′ (`results/k4_strategy/suite_rulef.log`) |

**Recommendation.** Put the next proof effort on DL₂. It is the only candidate found that climbs the quantity C₄ᵐⁱⁿ
is about (the deficit) rather than a proxy, so it is immune to the failure shape above. It is also stated with objects
already in Lean. The price is that its moves are "any change of two agents' bases" rather than named moves. A proof
must classify which two-agent change repairs each obstruction, and the data can guide that (§3). If DL₂ breaks at
larger n (k* = 3 on a core), the honest conclusion is that no uniform candidate of the forms tested here survives.
The remaining route would then be rule F's construction, whose architecture is the one that proved k = 3.

**Not recommended as the main route.**
- **PS (route 2).** It is uniform and survives, but it is strictly stronger than TARGET₄. Its induction stalls exactly at
  the core structure. The only closed strengthening, PS_W, is false for twins at n = 2. The owner form PS-OWNER is
  false at n = 3 (§2.2).
- **The minimal-counterexample certification (route 3).** It needs an absolute bound on β. No known reduction touches
  Q4-dense cores (§2.3).

## 1. The counterexample suite

`k4/suite/` holds 155 records: 150 complete instances and 5 local configurations of `k4/MINCEX.md`.

**Sources.**
- main, and PRs #37, #41, #43, #44, #45, #50, #51 and #53, read with `git show`.
- Three instances not in any repository:
  - the non-core counterexample to LIL found by #51's referee;
  - two LIL counterexamples from #51's reviewers (text catalogue).

  All three were re-derived here.
- Each source instance was confirmed with its source's own replay script.

**Implementations.** `k4/suite/model.py` is this workstream's own, written from the definitions. The runner
`k4/suite/run.py` compares it with the other workstreams' independent tools:
- #53's `gap_model`;
- #51's `red_lil`;
- #43's `induct_sat`;
- #44's `adaptive.c`;
- main's `hall_check` and `c4x_check`.

**Findings** (logs in `results/k4_strategy/`):
- **Every refutation the runner can express reproduces**: 52 checks on 34 instances, 46 of them with two
  implementations and 6 with one (the 𝒫_T and LIL-text checks, whose statements are new here), 0 disagreements
  (`suite_expected.log`). The rest are statements about specific algorithms (LB₄ variants, LS4, GM₄,
  NSW, the insertion lemma). Those are confirmed by their sources' replay scripts, cited in each record.
- **TARGET₄, K4.D and PS hold on every complete instance, cores and non-core alike**
  (`suite_baseline.log`, both implementations where they finish). C₄ᵐⁱⁿ (deficit form) holds on 148 of the 150 complete instances with both
  implementations; H₂ and H₅ time out (`suite_baseline2.log`). The configuration form is in the same log.
- **PS-OWNER fails on cores.** PS-OWNER is K4.D with a prescribed owner who is unenvied: an EFX₀ allocation in which
  w is unenvied and every other bundle has at most two goods, for every agent w.
  - It fails on 28 cores of the suite, smallest n = 3, m = 6, and on the non-core LIL instance. Both implementations
    agree (`suite_baseline2.log`).
  - PS itself holds on all of them (§2.2).

## 2. The routes

### 2.1 Route 1: a min–max / duality statement (Hall)

**What H1 gives.** Lemma H1 (`k4/hall.md` §1, proved) makes owner validity at a fixed P a covering condition:

def(P) = ω + 2 − max (|X| + u_o(X)) over free owners o and safe bundles X.

A duality theorem would describe the obstruction globally ("no min-frozen P has a removal-only owner") and show that a
core cannot carry it. Two things stand in the way.

1. **No global dual was found.** The covering is per P: edges are threatening subsets of R_x ∩ W_o, one small gadget
   per agent, overlapping at shared goods. The minimum over P of a transversal number has no LP dual whose feasibility
   is a checkable structure. At every Φ′, BT and LIL counterexample the obstruction has the same shape: every owner
   is blocked by one local threat. That is Theorem Z's permutation, broken by frozen agents threatened by two owners
   (T2, n = 4) or by t > 0. So the "dual certificate" is the exchange-digraph cycle of `k4/c4min.md` §4, and Route 1
   falls back into the move route.
2. **The global counting form fails.** The candidate is
   > **COUNT**: some pool-optimal configuration at a min-frozen key has r′ > |D|, where D is the set of free owners
   > that threaten a frozen agent (with C = ∅).

   COUNT is a sound certificate. At a pool-optimal configuration every free agent is threatened by at most one owner
   (Lemma Z2 with U_y, as in Theorem F's proof), so at least r′ owners threaten no free agent. One of them then
   threatens no frozen agent. It is the global form of #51's Lemma C.
   - It fails on 1,408 of the 74,256 profiles of #53's n = 3 catalogue, on 99 of the 184,014 sampled n = 4 gap
     profiles, and on 2 of 39,450 sampled n = 5 ones (`count_sweep.log`; the n = 5 catalogues with four 4-good agents
     and the pure ones were not reached before a container restart).
   - The first counterexample is `count-n3m8`: three identical big-top agents sharing goods 6 and 7
     (`attempts/k4-strat-count.md`).
   - **SIMPLE** (some configuration has a valid owner with C = ∅) holds on every n ≥ 3 catalogue profile. It fails on
     the 720 n = 2 profiles of category W, so the unfreezing clause is needed.

**What survives: the deficit as its own potential.** For P with the fewest frozen agents and def(P) > 0, let k*(P) be
the least number of agents whose base must change to reach a min-frozen P′ with def(P′) < def(P). Let k* of a profile
be the maximum over such P. It is 0 if no P has def > 0. `k4/suite/deficit_local.py` computes it with `model.py`'s
deficit, a direct transcription of `k4/c4x.md` §1.

| scope | profiles | k* = 0 | 1 | 2 | ≥ 3 | log |
|---|---|---|---|---|---|---|
| suite, every complete instance with ω ≥ 1 and n ≤ 6 (cores) | 98 | 46 | 37 | 15 | 0 | `deficit_local_suite.log` |
| suite, the non-core LIL instance | 1 | | | | **1 (k* = 3)** | the same |
| #53's n = 4 gap catalogues, every 10th record (one, two, three 4-good agents, pure) | 18,404 | 17,383 | 1,000 | 21 | 0 | `deficit_local_catalogs.log` |
| #53's n = 5 gap catalogues, every 20th record | 5,793 | 5,545 | 246 | 2 | 0 | the same |
| #53's hard hunt records (categories W and N, n = 4) | 117 | 41 | 61 | 15 | 0 | the same |

Notes:
- The suite rows include f = 0 profiles: H₁ has k* = 1 and cyc6 (n = 6) has k* = 1. Both are bounded-rotation or
  label-collision obstructions for the proxy potentials.
- Every Φ′, BT, LIL and SAME_N counterexample has k* ≤ 2.
- One-agent exchanges do not suffice: the smallest k* = 2 is `c4min-tlam-n3-m6`.
- A *global* minimum with def > 0 never occurs, since C₄ᵐⁱⁿ holds everywhere.

This is the statement of §3.

### 2.2 Route 2: a strengthened induction hypothesis (PS)

The inductive vehicle is PS(J, w): some EFX₀ allocation of J leaves w unenvied (#43, `k4/induct.md`).
- PS₄ implies TARGET₄ outright.
- It survives every instance of the suite, with both implementations.
- #43's evidence covers n ≤ 6 samples and 162,000 random general instances.

By Lemma 2 (a private good inserts iff its owner is unenvied) and Proposition 5, a minimal counterexample (I, w*) is
connected, has no junk good and no private good of w*, and admits no R1 or R2 peel of another agent. That forces every
agent other than w* to be a k = 4 core agent:
- a 3-good agent has a private good only if p < s + t;
- two private goods p, q of a 3-good agent would need p + q < s, which contradicts balance;
- three private goods of a 4-good agent likewise contradict balance.

So I is a **pointed core**: a core, except that w* is arbitrary without private goods. PS is therefore at least as hard
as K4.D on cores, plus a prescribed unenvied agent.

**Where the induction stalls, and why strengthening does not close it.** A private good p of an agent i ≠ w* can only
be removed if i stays unenvied too (Lemma 2). The closure of PS under this step is PS_W: some EFX₀ allocation leaves
every agent of W unenvied, where W is the set of agents whose private goods were removed. PS_W is **false** at
n = 2, m = 4 (`attempts/k4-strat-psw.md`):
- two P3 twins with the same shared pair and the same ranking;
- stripping both private goods leaves two agents on one pair, and one of them envies the other;
- the core itself (TARGET, PS(I, 0), PS(I, 1)) and the one-stripped instance are fine.

The restrictions of W that would avoid this ("W = agents that had private goods in the core above") are not
properties of the smaller instance, so they are not inductive. In the minimal-counterexample literature these
configurations are handled by gadget reductions (K4.MC2, MC3, MC5), not by a hypothesis. That is route 3.

**PS-OWNER** strengthens PS with the D2 shape and w as the owner. Lemma 7 of #43 is the k = 3 case of this, via LB⁺
with w last. It is **false at k = 4 already at n = 3, m = 6 on cores**: in `c4-lbplus-rotation-n3m6`, agent 1 is never
the unenvied owner of a D2 allocation, though PS(I, 1) holds. It fails on 28 suite cores in all, with both
implementations. So the owner-last route of Lemma 7 does not carry over as a statement about every agent
(`attempts/k4-strat-psw.md`).

**Verdict.** PS is a good *statement*: uniform, surviving, and it implies TARGET₄ with no extra Lean. It is not a
*proof architecture*: its own induction needs a multi-agent version that is false.

### 2.3 Route 3: minimal counterexample plus finite certification

Proved and certified (`k4/MINCEX.md`): a minimal counterexample within 𝒞_β has n ≤ 3(β − 1) (K4.MC4). This gives
TARGET₄ for β ≤ 4 (K4.MC6, K4.MC7).

A finite certification of TARGET₄ needs an **absolute** bound: every connected k = 4 core with β ≥ β₀ contains a
reducible configuration (an unavoidable set, as in the four-colour theorem). Against it:
- **Q4-only cores exist for every β.** An example is a 4-regular multigraph whose agents are the vertices and whose
  goods are the edges, with β = n + 1. None of K4.MC2, MC3, MC5 applies, since they need private goods or degree-2
  goods shared by P3 agents.
- The graph-like part (every good of degree ≤ 2) is covered by the multigraph theorem (ledger T3), for every n. The
  remaining cores have goods of degree ≥ 3 (shared tops), which is where the frozen and big-top phenomena live (H_t,
  core 104, bt4).
- A reducible configuration must hold for all 288^k type profiles of its agents (`k4/reduce4.py`). The closed-xy
  reduction already fails on 9,396 of 82,944 pair profiles (`attempts/k4-mincex-xy-pairs.md`).

**Verdict.** Useful as certification for small β. Implausible as the main architecture: it would need a discharging
argument over hypergraphs with unbounded good degrees and a new family of gadget reductions for Q4 agents, and nothing
suggests one.

### 2.4 Route 4: other uniform candidates

**(a) Three-good bases (𝒫_T, `k4/suite/triples.py`).** The first k = 4 failure of the extremal principle is (G1)
(`k4/c4x.md` §5): a big-top agent (a > b + c) has no base of at most two goods worth more than its top, only the triple
{b, c, d}. 𝒫_bt lets big-top agents hold their lower triple; 𝒫_low lets every 4-good agent do so.
- The extra condition is that no other agent strongly envies a triple; D2 is relaxed, TARGET₄ is not.
- In both spaces, Theorem K3's statement ("every Pareto-maximum is completable") repairs the n = 3 failures of
  `attempts/k4-c4x-pareto-potentials.md` (six of eight Pareto counterexamples tested).
- It fails at n = 3 on `hall-local3`: the Pareto-maximum gives agent 1 its triple, which threatens agent 2.
- It fails at n = 4 on `hall-bt4`: its frozen agents are not big-top, so triples change nothing.

See `attempts/k4-strat-triples.md`. The space trades (G1) for a new obstruction.

**(b) LB₄ʳ with rule F (#44).** This is the one algorithmic candidate with the k = 3 architecture. Rank 2 in the
summary.
- H_t, the family that defeats fixed insertion orders, is proved to need no rotation (Proposition H′).
- The gap is the counting theorem A₄⁺ᴺ with two or more exposed 4-good agents (K4.C4.GAP), plus a rule for the first
  agent that a proof can state. Rule F is a lookahead, and the cheaper rules fail at n = 3, m = 6.
- On the suite: success with at most one rotation on all 148 core instances run (every one except H₅, which
  Proposition H′ covers), including every Φ′, BT, LIL and SAME_N counterexample (`suite_rulef.log`).

**(c) Move catalogues.** Every fixed catalogue tested fails at the next n:
- LIL as #51's text states it fails at n = 3 (`lil-text-n3`) and n = 4 (`lil-text-n4`, 3-good x). Both were
  re-derived here with `k4/suite/lil_text.py` and are improvable with #51's broader catalogue.
- The broader catalogue fails on the non-core `lil-noncore-n3`, so a proof would have to use the private-goods rule,
  which none of the move lemmas uses.
- #53's SAME_N shows that no needed-set-preserving move suffices.

DL₂ avoids naming moves, and so avoids this.

## 3. The plan

**Conjecture DL₂ (K4.STRAT.DL2).** For every strict profile of every k = 4 core with ω ≥ 1, every P ∈ 𝒫 with the
fewest frozen agents and def(P) > 0 has a P′ ∈ 𝒫 with the fewest frozen agents such that:
- P′ differs from P in the bases of at most two agents;
- def(P′) < def(P), with def = +∞ when no free owner has a safe bundle.

*DL₂ ⟹ C₄ᵐⁱⁿ (removal-only).* The min-frozen class is finite and nonempty (`EFX.C4min.exists_minFrozen`). A
pre-allocation of least deficit in it cannot have def > 0 by DL₂, so it is removal-only completable. That is
`TheoremC4minRO`, and TARGET₄ follows by `EFX.C4min.target4_of_C4minRO`. The same argument restricted to connected
cores with a 4-good agent gives `C4minROConn` and `target4_of_C4minROConn`.

*Why this and not another potential.* Every counterexample in the suite defeats a proxy: a potential that is maximal
at a non-completable P while the deficit is not minimal there. DL₂ climbs the deficit itself. It asserts only that the
climb has no local traps of size ≤ 2. The failure of k* ≤ 2 on the non-core instance says a proof must use the core
rules. That is consistent with the rest of the data, and it also locates where they enter.

**Proof architecture.** An augmenting-exchange lemma by case analysis on the covering obstruction at P. Take a best
owner o and a minimum hitting set C of the threat hypergraph H_o (Lemma H1). def(P) > 0 means C exceeds the budget.
The known structure of the blocking threats gives the cases:
- Lemma H3's free exposures e1, e2, e3;
- Lemma H7's frozen exposures G, G1, L;
- #51's Lemma D (x threatened by two owners).

For each case, exhibit a change of at most two bases that either removes an edge of H_o (a threatened agent gets a
better or different base) or raises the budget (unfreezing, a slot), without creating a new unhittable edge. The
proved pieces fit this frame:
- Theorem Z's Lemmas P and R (rotations along a threat cycle; on the data a two-agent change always suffices, even where
  Theorem Z's own cycle is longer);
- Theorem F;
- #52's downgrade swap (two agents);
- #51's path move and Lemma PM.

**Next steps, in order.**
1. **Kill it fast (compute, cheap).** Run DL₂ exhaustively on every profile with n ≤ 3 and on n = 4 with one or two
   4-good agents. That needs a C version of `deficit_local.py`: #53's `gap.c -D` already computes the deficit of
   every min-frozen P, so the addition is the neighbour scan. Also run it on random f = 0 and f ≥ 1 profiles at
   n = 5, 6 and on H₂, H₃. A core with k* = 3 refutes DL₂ as stated. Then record DL_k for the least k that works, or
   conclude that no uniform candidate survives.
2. **Classify the repairs (compute).** For every P with def > 0 in the data, record which two agents change, and how
   (base grows, shrinks, swaps a good with the pool, trades with the other agent), against the obstruction type (H3 or
   H7 class of the blocking threat). A short list of repair types that covers every case is the case analysis the
   proof needs. If the list keeps growing with n, that is evidence against DL₂ as an architecture even where it holds.
3. **Prove the k* = 1 cases (proof).** Single-base repairs: pool improvements and single upgrades. Most of Theorem Z's
   and F's lemmas are of this kind.
4. **Lean.** State `DefLocal2` with `EFX.C4min.DeficitLE` and `MinFrozen`, and prove `DefLocal2 → TheoremC4minRO`, the
   finite descent above. It is short, and it fixes the target in the same terms as K4.C4MIN.FRAME.

**Rank 2, if DL₂ falls.** Rule F. The next step is the A₄⁺ᴺ counting gap of #44 §6 (uncovered profiles with two or
more 4-good agents), and a first-agent rule a proof can state. Proposition H′'s condition ("an agent of gadget 1
before ℓ") is the model.

**What would change this plan.**
- A core with k* ≥ 3.
- A case of step 2 that needs an unbounded repair.
- A proof of LBO / A₄⁺ᴺ.

## 4. Reproduce

Every log starts with its command.
```
python3 k4/suite/run.py --expected                         # every expressible refutation, both implementations (~5 min)
python3 k4/suite/run.py efx0 d2 ps psd2 c4min c4min-cfg     # the baseline (SAT and enumeration; large instances time out)
python3 k4/suite/run.py rulef                              # rule F on the suite's cores (#44's adaptive.c)
python3 k4/suite/deficit_local.py                          # k* on the suite
git archive 245040b k4 results/k4_gap results/k4_certs_2.json.gz results/k4_certs_3.json.gz \
  results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz results/k4_certs_4_n4_3.json.gz \
  results/k4_certs_4_pure.json.gz | tar -x -C k4/suite/.cache/gapbench   # #53's catalogues and bench (read-only)
python3 k4/suite/deficit_sweep.py k4/suite/.cache/gapbench/results/k4_gap/gap_n4_pure_s4000.json.gz --every=10
python3 k4/suite/count_bench.py k4/suite/.cache/gapbench gap_n3.json.gz 0
python3 attempts/k4_strat_attempts.py                      # this workstream's failed routes
```
