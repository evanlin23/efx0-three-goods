# k = 4 attack log (parallel campaign, from 2026-11-26)

Goal: settle TARGET₄ (every additive instance in which every agent values at most four goods has a complete EFX₀
allocation), by proof or by counterexample. The ultimate goal is arbitrary k, which is EFX₀ existence for every additive
instance (every instance is m-limited); k = 4 is the near-term target, and the general-k track starts from n = 3. This file is the coordinator's record: one entry per hourly burst, the
angles in flight, and what each established. Ledger rows change only with artifacts (AGENTS.md §5).

## Where k = 4 stands (start of the campaign)

- **Certified**: TARGET₄ on every core with n ≤ 5 that has a 4-good agent, with n = 6 and exactly one, and for
  β ≤ 4 (rows K4.R5*, K4.R6a, K4.MC6, K4.MC7; ledger open items 15–16).
- **Refuted routes**: every "maximum of a potential is completable" form (K4.SDC.P1: no value-monotone method works,
  n = 4, m = 7), DE4 and its tie-breaks, GM₄, DL₂ and successors, NO/NOF, PHI₄, and the move catalogues (items 17–30,
  `attempts/k4-*.md`).
- **Surviving targets** (`k4/sdc.md`): SD-C, MD, and the sharpest one, **OC₁** (§29): from every serial-dictatorship
  order, the picks have a one-absorber EFX₀ completion, or one improving chain makes one exist. It holds on all
  120,050 starts tested (n ≤ 5) and implies TARGET₄.
- **Proved pieces**: Theorems DT and DT⁺ (distinct tops; no frozen agent values junk), Lemma GDT (completion for
  single goods and satisfied pairs), Theorem DT₁ (one frozen agent with one wanter and an improving pair).
- **Missing**: the count that shows the frozen agents' demands (goods to keep out of the owner's bundle) fit into the
  free slots, or that one improving chain makes them fit (`k4/sdc.md` §30, last paragraph).

## Angles in flight

| angle | session | branch | note |
|---|---|---|---|
| CEGAR counterexample hunt: synthesize values for a fixed core so that no allocation is EFX₀; certify cores for all values otherwise | session_01BYMGeaDXra9RWYSfAKvqid | `claude/k4-hunt-cegar` | `k4/hunt.md` |
| Hall-type count for OC₁: exact completion condition for picks plus owner, then one chain restores it | session_01BYMGeZTVDV38teEA7133jH | `claude/k4-oc1-hall` | `k4/oc1_hall.md` |
| Extend the girth-≥4 hypergraph theorem (Lianeas–Sgouritsa–Sotiriou) to degree-4 hypergraphs with short cycles | session_01BYMGeahqCXt4wer7YeYLty | `claude/k4-girth` | `k4/girth.md` |
| Prove OC₁ at k = 3 with Draft and Exchange's machinery, then lift lemma by lemma to k = 4 | session_01BYMGeZVgBaajhpdHdJtKm2 | `claude/k4-k3-oc1` | `k4/k3_oc1.md` |
| Reconstruct Viswanathan–Mehta's 4-limited EFX algorithm and make it EFX₀ | session_01BYMGebcnNSpPp9qEyjfvuV | `claude/k4-vm` | `k4/vm.md` |
| k-sensitivity: the smallest k at which SD-C, MD, OC and OC₁ fail (adversarial, k = 5, 6, 8), and what k ≤ 4 buys | session_01BYMGeYRzPvVFuMx5JPLStH | `claude/k4-ksens` | `k4/ksens.md` |
| General k, first foothold: OC₁ / SD-C for three agents at arbitrary k (a short proof with a polynomial algorithm would be new), then n = 4 | session_01BYMGeadPp24qCxnUuKsLsB | `claude/kgen-n3` | its own note (`kgen/`) |
| Induction on agents along the serial-dictatorship order (retired 22:35 after PR #103); now CEGAR synthesis against OC₁^max with ν = n | session_01BYMGecgCGycycqxiyS1n7G | `claude/k4-sd-induct` | `k4/sd_induct.md` |
| Housing markets / top trading cycles: SD picks as existing tenants, junk as the pool; find the TTC / YRMH-IGYT-type rule that picks the repairing chain, and core-type invariants | session_01BYMGeao2jUMkZBYQ48pDMw | `claude/k4-ttc` | `k4/ttc.md` |
| General k: bounded charity CH(k): partial EFX₀ with at most f(k) unenvied unallocated goods, f independent of n (relevant-goods analogue of the t − 2 bound for t types) | session_01BYMGeYiET7bXN43NsuXoDR | `claude/kgen-charity` | `kgen/charity.md` |
| The first open cell (k, p) = (4, 3) (≤ 3 valuers per good): a two-envier dump rule replacing the multigraph proofs' unique-envier step | session_01BYMGea7fswSChnvyCWWWm8 | `claude/k4-p3` | `k4/p3.md` |
| Choosing the order by an alternating-tree search with a lexicographic, non-value termination measure (Haxell; restricted Santa Claus) | session_01BYMGeYJ6PFyCSZHphgSyXd | `claude/k4-haxell` | `k4/haxell.md` |
| Lean frame OC₁^max ⟹ TARGET₄ with SDPO, MAXSD and Lemma MAX machine-checked (from 22:36) | session_01BYMGecPDq28nRFGVkqASck | its own branch (formal/k4-oc1max) | `lean/` |
| OC₁ at perfect starts with |D| ≥ 2 dangerous agents (disjoint danger sets via Lemma PL; overlapping via PWk(a)); the Hall session keeps |D| = 1 (from 22:53) | session_01BYMGecLPfLsPCQYak86dm7 | its own branch (proof/k4-oc1max-multi) | draft PR |
| General k: ROUND⁺, one round of disjoint chains from any SD start for strictly positive values (n = 4: a route to EFX for four agents) (from 22:53) | session_01BYMGecn2Gg5F8Q6oyTj69u | its own branch (proof/kgen-rounds) | `kgen/rounds.md` |
| Matching theory: one-absorber completability as a bipartite matching (Lemma 2*), improving chains as augmenting paths; target "deficiency ≤ 1 at perfect starts when k ≤ 4" (from 22:55) | session_01BYMGecJz5BkPspxF3AFESm | its own branch (proof/k4-matching) | draft PR |
| D1 sub-lemmas D1-C (CROWD) and D1-H case H-ii, split with the Hall session (from 22:58) | session_01BYMGebYzRJ5LPzgWyaPyrq | its own branch (proof/k4-d1) | draft PR |
| Certify OC₁^max for ALL strict profiles on n ≤ 5 cores (ordinal CEGAR, second encoding) (from 22:58) | session_01BYMGebCRA4DLjCqvLLXBaY | its own branch (compute/k4-oc1max-cert) | draft PR |
| Side angle: monotone EFX₀ with bounded relevance, the smallest k at which monotone EFX₀ fails (from 22:58) | session_01BYMGeaVoeoAHRPBzXqahDb | its own branch (proof/monotone-k) | draft PR |
| New certified minimal-counterexample reductions: twins, near-twins, dense configurations (toward β = 5) (from 22:58) | session_01BYMGeaE5MHuxY3t8Ktrwqw | its own branch (proof/k4-twins) | draft PR |
| Paper draft of the refereed results (paper/campaign/draft.md) (from 22:58) | session_01BYMGeYMBvUvhfc3gCD1iif | its own branch (paper/campaign) | draft PR |
| Referee: independent, adversarial review of every written proof the angles produce (Theorem VM first) | session_01BYMGeYHb8rxaaJ1BScSCZY | `claude/k4-referee` | `k4/referee/` |
| Base case of ROUND-RSD: OC₁ with phantom constraints; BASE-R, B1–B3, the greedy P1-free round process GR (from 03:29) | session_01BYMGebS9uNs3yyqMaMxxm7 | `proof/k4-base-phantom` | `k4/base_phantom.md` |
| Conjecture RKMAX: OC₁ at rank-maximal maximum-matching starts; prove "failing start ⟹ a σ-raising SD vector" (from 05:35) | session_01BYMGeaZVABiazckLK4GK8q | `proof/k4-rkmax` (or its claude/… branch) | draft PR |

The coordinator (this branch, `claude/kind-lamport-y8fdme`) runs an hourly burst: it checks each angle, verifies any
claimed proof or counterexample independently, integrates verified results here, and works one angle of its own.

## Log

### 2026-11-26 20:35 UTC: campaign started
- Five angle sessions launched from `claude/kind-lamport-y8fdme` (commit `26e79d2`).
- Hourly coordinator burst scheduled (trigger `trig_016DHmg4n61QCy2RopwumejP`, minute 34).

### 2026-11-26 20:37 UTC: sixth angle, k-sensitivity
- Why: SD-C and OC₁ hold at k ≤ 8 on random data. If either held for every k, a proof would settle EFX₀ for all
  additive instances, so a k = 4 proof must use k ≤ 4 somewhere. The session looks for the smallest k where each
  conjecture fails, adversarially, and for the property of k ≤ 4 that the failure shows a proof needs.
- Coordinator's own run: `k4/sdc/oc1_bign.py`, OC₁ beyond n = 5 (2,000 random instances, n = 6–9, 12 orders each),
  log `results/k4_sdc/oc1_bign_6_9.log` (in progress).

### 2026-11-26 20:38 UTC: general-k track
- The ultimate goal is arbitrary k. SD-C, MD and OC₁ are stated for any k. Their first general-k foothold is n = 3:
  EFX₀ is known there (Chaudhury–Garg–Mehlhorn, pseudo-polynomial). OC₁ for n = 3 would give a short proof with a
  polynomial algorithm. Session `claude/kgen-n3` tests it adversarially at large k and tries to prove it, then n = 4.

### 2026-11-26 20:47 UTC: eighth angle; coordinator runs
- New angle: induction on agents along a serial-dictatorship order. This is the agent-count side's method (grow n
  one agent at a time), with our order structure: the last agent is never frozen, and the prefix of an order gives SD
  of the sub-instance. It is not the failed induction on 4-good agents (`k4/induct.md`).
- Coordinator: OC₁ at n = 6–9 on 2,000 random instances, 12 orders each (`results/k4_sdc/oc1_bign_6_9.log`): all
  24,000 starts pass; 115 need one chain, none more. Random instances are easy at this size, so an adversarial climb
  is running (`k4/sdc/oc1_bign_climb.py`, `results/k4_sdc/oc1_bign_climb_6_8.log`).
- Literature survey started (agent-count side, structural side, cross-field techniques); its report will go to
  `reports/`.

### 2026-11-26 20:48 UTC: ninth angle, housing markets
- SD picks are the Pareto-optimal one-good matchings, and our improving chains are trading paths in a housing
  market with existing tenants (the picks) and a pool (the junk), with multi-unit demand. The session tests whether a
  TTC / YRMH-IGYT-type rule picks a repairing chain, where value-based rules fail (`k4/sdc.md` §29). It also asks
  whether core results, including Konishi–Quint–Wako's nonexistence, explain P1.

### 2026-11-26 20:56 UTC: literature survey results, two follow-ups
Notes in `research_notes/EFX literature from the agent side/` (agent-count side, structural side, cross-field
techniques); the synthesized report follows in `reports/`.
- New angle: bounded charity CH(k), from the agent-count survey. With t valuation types the charity bound is t − 2,
  independent of n, and nobody has tried the relevant-goods analogue.
- Hunt session: target the uncovered window 5 ≤ β ≤ 2n − 4 for k = 4 cores. Mahara covers β ≥ 2n − 3 and K4.MC7
  covers β ≤ 4, so first certify β = 5 for all values. A counterexample lifts to every larger n with the same excess
  (arXiv 2604.18216 v4, Lemma 3.5).
- Hall session: the cross-field survey's derivation is that, for a fixed order and owner, the one-absorber completion
  may be a matroid partition problem, with an exact Rado-type condition. The exceptions are overlapping D_i and one
  explicit non-matroid configuration that exists only at k = 4.
- Girth session: Lianeas–Sgouritsa–Sotiriou may need girth ≥ 4 only in Lemma 3.4. The multigraph proofs use their
  graph hypotheses mainly in the "dump on the unique envier" step, and a two-envier dump rule is what goods with
  three valuers need.
- Context: arXiv 2604.18216 v4 ("EFX Need Not Exist", Nov 2026) gives a monotone (weighted-coverage) counterexample
  with 3 agents and 8 goods. The additive case is untouched, and for monotone valuations the relevant-goods
  threshold lies between 3 and 8.

### 2026-11-26 21:11 UTC: literature report; two more angles
- Report: `reports/EFX literature from the agent side.md` (about 7,000 words; read levels and [derived]/[spec] tags).
  No published theorem or cross-field tool closes k = 4. Every ladder (agents, types, relevant goods, monotone
  excess) stalls at four. The first open structural cell is (k, p) = (4, 3).
- Ranked directions and their owners:
  1. matroid-union dual of the fixed-order completion: Hall session;
  2. (k, p) = (4, 3): new session `claude/k4-p3`;
  3. non-value termination: new session `claude/k4-haxell`;
  4. monotone k = 3 threshold: not yet assigned;
  5. charity bound in k: `claude/kgen-charity`;
  6. the two possibly free strengthenings (Lianeas girth, Sgouritsa–Sotiriou degree): girth session;
  7. extend K4.MC7 to β = 5: hunt session;
  8. reductions for agents with all-equal values and for twin agents: coordinator, later burst.

### 2026-11-26 21:35 UTC: hourly burst 1
All 12 angle sessions are active and pushing. Claims below are the sessions' own until the referee or the
coordinator has checked them; "verified" marks the ones checked.
- **Hunt** (`claude/k4-hunt-cegar`): an ordinal CEGAR, in which outer clauses are comparison bits, certifies whole
  cores for every strict profile in seconds. That is ~100× faster than scan2 on the cores timed. It certifies the six
  graphical all-P4 cores of K4.MC7 directly; two encodings agree (CaDiCaL on comparison bits, Glucose on raw unsafe
  sets). So K4.MC7 (TARGET₄ for β ≤ 4) no longer needs the multigraph theorem. Ledger integration is pending the PR.
  Next: the β = 5 window.
- **k-sensitivity** (`claude/k4-ksens`, PR #98):
  - OC and OC₁ are false at k = 5 (PW5: n = 5, m = 9; two programs plus a written proof). The PW family needs
    ⌊(k − 1)/2⌋ chains, k = 5–9.
  - DT's and DT₁'s conclusions fail at k = 5. So the k ≤ 4 steps are sharp.
  - Where k ≤ 4 enters: after one repair a frozen agent has k − 3 pool goods left, which is one at k = 4 and fits the
    single free slot.
  - One ROUND of vertex-disjoint chains repairs everything at k = 5–10. This round conjecture is the new general-k
    candidate.
- **General k, n = 3** (`claude/kgen-n3`): independently, OC₁ fails at n = 4, k = 5, and a packing of disjoint chains
  repairs it. OC₁ (t ≥ 0) survives at n = 3 for every k on about 1.3·10⁹ starts, so the target there is a proof.
- **Charity** (`claude/kgen-charity`, PR #105):
  - CH-A: exact EFX₀ with O(√(kn)) charity, by rainbow cycles with genuine zeros.
  - CH-B: fewer than e·d unallocated goods when every good has ≤ d valuers, independent of n.
  - CH-D, CH-E: no n-independent f(k) can come from CKMS rules or from Pareto maxima.
  - **P1 already fails at k = 3** (n = 4, m = 7, every agent values exactly 3 goods). **Verified** by the
    coordinator's own brute force (`k4/sdc/p1_k3_verify.py`, `results/k4_sdc/p1_k3_verify.log`). So value-monotone
    failure does not distinguish k = 4 from k = 3.
- **Viswanathan–Mehta** (`claude/k4-vm`):
  - Theorem VM, a written proof not yet refereed: the reconstructed algorithm gives complete ordinary EFX on every
    4-limited instance, with one correction (G1), and the abstract's unproved "source" step is proved.
  - For EFX₀ the algorithm breaks at three stages, the matching stage even at k = 3.
- **k = 3 then lift** (`claude/k4-k3-oc1`, PR #96):
  - Theorem R1C, written: OC₁ at k = 3 for every R1-compatible order, in DE's core case (every agent values exactly three goods, strictly balanced; dead goods allowed), not every 3-limited instance (referee scope note, 21:58).
  - Theorem candidate OT, exhaustive on every core with n ≤ 5 (2.7·10⁸ starts) and at n = 6, m ∈ {10, 11}.
- **Girth** (`claude/k4-girth`):
  - Theorem T1, written: EFX₀ for linear instances with an agent on no 3-cycle, monotone valuations.
  - Conjecture L, which would give EFX₀ for every linear additive instance at every k: no counterexample in about
    10⁵ Pareto maxima.
  - The LSS architecture fails with 2-cycles at n = 2.
- **Hall count** (`claude/k4-oc1-hall`, PR #100):
  - The exact count (Lemma 2 / Cor. 2.1) matches SAT on 20,648 owner tests.
  - Theorem F1_1, written: f = 1 with one wanter.
  - The matroid view is sufficient but not exact.
  - Chain statement (Finding B/C): canonical chains from dangerous agents plus at most one junk-assisted step; 20
    configurations need that step.
- **TTC** (`claude/k4-ttc`, PR #101): OC₁-H and OC₁-HD are refuted at n = 6 (independent replay). OC₁-ED survives on
  all data: the endpoint absorbs, the start is dangerous, the middle is pure want arrows, and junk goes only at the
  head. It is to be reconciled with the Hall session's Finding B/C.
- **SD induction** (`claude/k4-sd-induct`): Lemmas D, F, S, U, BOTH-TP, written. Conjecture AB₁ holds on 17,403/17,403.
- **(4, 3) cell** (`claude/k4-p3`): P1 fails inside the cell (GM4-D). The multigraph final shape is impossible
  already at k = 3, so the dump rule has to be redesigned, not patched.
- **Haxell** (`claude/k4-haxell`): literature read; models in progress.
- **New**: referee session (`claude/k4-referee`) for every written proof, in the order Theorem VM, R1C, T1, the Hall
  lemmas, CH-A/B, PW5, the SD-induction lemmas.
- **Coordination sent**:
  - ksens owns the ladder and round conjecture; kgen-n3 owns the n ≤ 3 proofs.
  - The Hall and TTC sessions reconcile Finding B/C with OC₁-ED.
  - Every k = 4 prover is pointed to the k − 3 fact.
- **Coordinator's own runs**: OC₁ at n = 6–9 passes on 24,000 random starts. The adversarial climb at n = 6–8 is still
  running.

### 2026-11-26 21:50 UTC: OC₁ refuted at k = 4 (verified); central conjecture amended
- **OC₁ is false at k = 4** (found by the TTC session, `claude/k4-ttc`, `attempts/k4-ttc-oc1-counterexample.md`).
  **Verified** by the coordinator's own brute force, with no SAT, no shared code and no caps:
  `k4/sdc/oc1_k4_cex_verify.py`, `results/k4_sdc/oc1_k4_cex_verify.log`.
  - Instance: n = 6, m = 10; sets [[0,2,3,1],[1,4,5,9],[1,2,0,8],[1,6,7,8],[3,6,9],[1,3,6,9]], vals
    [[2,7,8,3],[3,6,4,9],[12,2,4,8],[12,6,3,4],[7,2,10],[7,8,4,1]], order 0..5, picks (3, 9, 1, 6, –, –).
  - Agents 4 and 5 get no pick. The frozen agents 0, 1, 3 have disjoint junk danger pairs, so every free completion
    uses two absorbers, namely both pickless agents.
  - None of the 92 states one official move reaches has a one-absorber completion. If a chain may hand on an empty
    base, which glues two disjoint chains through the pickless agents, 27 of 168 states do.
  - OC1-ED* (agreed by the Hall and TTC sessions an hour earlier) falls with it. OC (free completion), MD, SD-C and
    TARGET₄ are unaffected.
- **Amended central conjecture** (to be stated precisely by the Hall and TTC sessions): OC₁ᵖ / OC1-ED*ᵖ. At most one
  absorber among the pick holders, and pickless agents absorb without restriction, like Draft and Exchange's free
  agents that hold nothing. The k-sensitivity "one round of disjoint chains" form is the other candidate.

### 2026-11-26 21:55 UTC: correction, the OC₁ counterexample is not a core
- The TTC session's 84 counterexamples, including the one replayed above, are **not cores**. In the replayed
  instance agent 4 values goods 9, 3, 6 at 10, 7, 2, and 10 ≥ 7 + 2, so rule R1 peels it. Most of the others also
  have ties or private-good dominance. The climb's value mutations do not preserve core-ness. Checked by the
  coordinator for agent 4.
- So OC₁ is refuted only as literally stated in `k4/sdc.md` §29 ("every instance with ≤ 4 relevant goods"). **OC₁
  and OC1-ED* on strict connected cores, the form that implies TARGET₄ via the peeling reductions, are NOT
  refuted.** The pickless-absorber amendment is kept as a robustness candidate, not as a necessity.
- Next (TTC session): an adversarial climb restricted to strict connected cores (`is_core4` after every mutation),
  n = 6–7, to see whether the two-pickless-agents pigeonhole survives the core conditions.

### 2026-11-26 21:50 UTC: OC₁ fails on a strict connected core after all (verified); open form is the K4.MC2 class
- The k4-oc1-hall session (`k4/oc1_hall.md` §16, `k4/oc1_hall/verify_ttc_cex.py`) found that **instance 36** of the
  TTC list, unlike the replayed one, is rejected by `is_core4` only for a tie in agent 2. Both strict perturbations
  B< and B> pass. **Verified** by the coordinator's own code, written from the K4.CORE row's (C1)–(C5) plus strictness
  and connectivity, with no SAT and no shared code: `k4/sdc/oc1_core_cex_verify.py`, `results/k4_sdc/oc1_core_cex_verify.log`.
  - B<: sets [[0,2,3,1],[6,4,5,9],[1,2,3,9],[1,6,7,8],[3,6,9],[1,3,6,9]], vals [[6,14,16,12],[4,18,12,28],
    [28,4,16,21],[16,14,12,6],[28,8,24],[20,30,8,4]]. B> changes agent 2's last value from 21 to 19.
  - Both pass every core condition. Private goods: agent 0 has {0}; agent 1 has {4, 5}; agent 3 has {7, 8}.
  - Order 0..5 gives picks (3, 9, 1, 6, –, –). No state among the 57 one official move reaches has a one-absorber
    completion.
  - Over all 720 orders: OC₁ fails for 24, one move repairs 383, and the picks complete for 313. This is identical
    to the Hall session's count.
- **Mechanism.** The pickless agents 4 and 5 value only picked goods, so every holder of 1, 3, 6 or 9 must stay a
  single-good holder. All six junk goods (four of them the private goods of agents 1 and 3) then go to agents 4 and 5,
  so there are two absorbers. A free completion exists (OC, MD, SD-C, TARGET₄ unaffected); OC₁ᵖ (pickless agents
  absorb freely) holds at these picks.
- **Status.** OC₁, OC1-ED\* and Finding S\* are refuted on strict connected k = 4 cores (n = 6). The form that still
  implies TARGET₄ is OC1-ED\* on strict connected cores in which no agent has two private goods. That is K4.MC2's
  class: K4.MC2 is CERTIFIED, and minimal counterexamples lie in it. OC₁ᵖ-ED\* is the robust alternative.
- **Next.**
  - TTC session: climb inside the K4.MC2 class (is_core4 and no two-private agent after every mutation), and test
    OC₁ᵖ on everything it finds.
  - Hall session: the written proof of Finding D1.
  - Coordinator: whether removing two-private agents also removes the pickless pigeonhole (count the junk:
    |J| = m − #picks, and the private goods are what made |J| = 6 here).

### 2026-11-26 21:56 UTC: new candidate OC₁^max (maximum-matching orders)
- **Observation** (coordinator, `k4/sdc/oc1_max_orders.py`). On B< and B>, every failing order leaves two agents
  pickless: its picks match 4 agents, while the instance has a perfect agent matching (ν = 6). No order whose picks
  form a maximum matching fails.
  - B< and B>: OC₁ holds for all 680 maximum-matching orders, and fails for 48 of the 760 others.
    Log: `results/k4_sdc/oc1_max_orders_core.log`.
  - All 84 TTC instances (`results/k4_ttc/oc1_counterexamples.json`): 0 failures among 30,452 maximum-matching
    orders; all 2,016 failures (24 per instance) come from non-maximum orders. Log: `results/k4_sdc/oc1_max_orders_ttc84.log`.
- **Conjecture OC₁^max.** For every SD order whose picks form a maximum-cardinality matching of the agent /
  relevant-good graph, the picks have a one-absorber completion, or one official move gives a state with one.
  OC1-ED\*^max is the same restriction of OC1-ED\*. All earlier evidence for OC₁ (every order, n ≤ 5; 24,000 random
  starts, n = 6–9) is evidence for it.
- **Such orders exist (proved here; elementary).**
  - A matching M that is Pareto optimal among maximum matchings is Pareto optimal: an improvement keeps every matched
    agent matched, so it is again maximum.
  - Every Pareto-optimal matching M is an SD outcome. If no agent holds its top remaining good, every agent points
    to a better good. That good is unmatched (giving it is an improvement, which contradicts maximality) or matched,
    so following pointers closes a cycle among matched agents, and trading along it is an improvement.
  - So some agent i holds its top good: put it first, remove i and M(i), and repeat. The agents M leaves unmatched
    come last; all their goods are already taken, so they are pickless in SD too.
  - Hence OC₁^max implies TARGET₄ on cores, exactly as OC₁ did. It can also be restricted to the K4.MC2 class.
- **Next.**
  - TTC and sd-induct sessions: climbs and CEGAR against OC₁^max, not OC₁.
  - Hall session: does Lemma 2\* explain why pickless agents of a maximum matching (the Hall-deficient set given by
    König–Egerváry / Gallai–Edmonds) cannot force two absorbers?

### 2026-11-26 21:58 UTC: referee verdicts (claude/k4-referee, k4/referee/README.md)
- **Theorem VM** (`claude/k4-vm`; the reconstructed Viswanathan–Mehta algorithm with correction G1): **CORRECT**, for
  ordinary EFX only. The report is `k4/referee/vm.md`; it has an independent implementation, exhaustive and random checks,
  and mutation tests. So ordinary EFX exists whenever every agent values at most 4 goods, by a refereed proof in the
  repository. EFX₀ (VMX2) is the open step.
- **Theorem R1C, Lemmas 1 and 2, Theorem B\*** (`claude/k4-k3-oc1`, OC₁ at k = 3): **CORRECT** in DE's core case,
  where every agent values exactly three goods, strictly balanced. **Lemma 3** is **CORRECT WITH FIXES**: its first
  sentence is false for a pair-holder owner, and the fix is in `k4/referee/k3_oc1.md` §3.
- Pending: girth (T1, SINK, PARK, SLACK), Hall (Lemma 2/2\*, Cor. 2.1, F1_1), charity (CH-A, CH-B), PW5, sd-induct
  lemmas.
- Coordinator: the OC₁ climb `oc1_bign_climb` was stopped as superseded (18/64 runs, no failure). Two OC₁^max climbs
  on strict cores were started (`k4/sdc/oc1max_climb.py`): one seeded at B<, one on random cores in the MC2 class with n = 6–7.

### 2026-11-26 22:00 UTC: every "for every order" form is refuted on MC2-class cores; OC₁^max and R1-priority survive
- **TTC session, two more strict core counterexamples** (`claude/k4-ttc`; both verified by the Hall session, §16 and §18):
  - an n = 5, m = 9 core with three two-private agents;
  - **an n = 5, m = 9 core in the K4.MC2 class**: sets [[0,3,6,8],[1,4,7,6],[2,5,8,7],[0,1,2],[0,1,2]], vals
    [[10,6,5,7]×3,[4,3,2],[2,4,3]]. Each frozen agent i values y_i, a_i, b_i, b_{i−1}, and every pair of {a_i, b_i, b_{i−1}}
    beats its pick (a danger triangle). The two pickless agents are the only junk receivers.
  - At order 0..4, even **OC fails (free completion, after one move)**, and so do OC₁, OC₁ᵖ and OC1-ED\*. MD, SD-C and
    TARGET₄ stand.
- **Verified by the coordinator** (`k4/sdc/oc_mc2_cex_verify.py`, `results/k4_sdc/oc_mc2_cex_verify.log`).
  - Strict MC2-class core, ν = 5.
  - The 12 failing orders give 3 picks: non-maximum, no free completion at the picks or after any of the 232 moves.
  - **All 50 maximum-matching orders complete at the picks.**
- **OC₁^max on every core counterexample known** (`results/k4_sdc/oc1_max_orders_ttc_cores.log`). The data: the 37
  distinct MC2-class failures of the TTC climb, the two-private n = 5 core, and the MC2 core.
  - All 1,950 maximum-matching orders complete at the picks; not one needs a move.
  - All 468 failures come from non-maximum orders.
  - With B<, B> and the 84 non-core instances: 0 failures in 33,082 maximum-matching orders.
- **Two surviving central candidates.**
  - (A) **OC₁^max**: maximum-matching orders; coordinator's proposal; the existence of such orders is elementary.
  - (B) **R1-priority OC1-ED\***: Hall session. It holds on all 1,855 one-absorber-hard starts (n ≤ 5) and on all 9
    MC2 failures of the TTC climb.
  - Both kill the pickless pigeonhole. Next: test whether each implies the other on the data, and climb against both.
    The TTC session runs both climbs.

### 2026-11-26 22:07 UTC: Lemma MAX, R1-priority narrowed, ledger updated, girth verdict, n = 2
- **Ledger** (this branch, PR #95):
  - K4.SDC.OC and K4.SDC.OC1 are **REFUTED** as every-order statements, with the independent replays as artifacts.
  - New rows: K4.SDC.MAXSD (maximum-matching SD orders exist, PROVED, written proof) and **K4.SDC.OC1MAX**
    (CONJECTURE).
  - `k4/sdc.md` §31 has the instances, the mechanism and the evidence. Open item 30 is updated.
- **Hall session, Lemma MAX** (`k4/oc1_hall.md` §19). At a maximum-matching start, no agent reachable from a pickless
  agent by an alternating path values a junk good; otherwise there is an augmenting path. Checked by the coordinator;
  it is immediate. So the pickless-wanter pigeonhole of every known counterexample cannot form.
  - OC1-ED\*^max holds on all 2,071 one-absorber-hard maximum-matching starts.
  - The R1-priority and maximum-matching order classes are incomparable on 6,617 instances.
  - OC1-ED\*^max is now the central conjecture in the Hall header.
- **TTC session.** R1-priority OC₁ **fails** on the three two-private cores (the n = 5 hand core, B<, B>), so form (B)
  survives only inside the MC2 class. OC₁^max survives on all 41 core counterexamples; every failing order matches
  ν − 2 agents. All R1, max and seeded climbs report no failure. Written up in `attempts/k4-ttc-oc-every-order.md`.
- **Referee, item 3** (`claude/k4-girth`): Theorem T1 and Lemmas SINK, PARK, SLACK are **CORRECT**.
  - T1: EFX₀ for linear hypergraphs with an agent on no Berge 3-cycle, extending LSS's girth ≥ 4.
  - Small fixes: PARK needs N ≠ ∅ when some good is valued by nobody; Fact F2's "monotone" remark is false and is
    unused.
- **kgen-n3** (PR #97, `kgen/n3.md` §8–§10).
  - Conjectures K'' and K''' are refuted.
  - New Theorem 2 (two agents, every k, zeros included: the OC₁ shapes from either order) is proved except Lemma T.
    Lemma T: among allocations keeping both tops with no strong envy by b, every maximizer of v_a is EFX₀. It holds
    on 8,095 instances.
  - At n = 3, "every maximizer" fails, while "some maximizer" (Conjecture T₃) holds on all 2,880 starts per role.

### 2026-11-26 22:10 UTC: PW5 refereed; OC₁^max is false at k = 5 (so it is a k ≤ 4 statement)
- **Referee, item 6:** PW5 (`claude/k4-ksens`) is **CORRECT**. OC, and hence OC₁, fails at k = 5, and so at every
  k ≥ 5 (`k4/referee/ksens.md`, exhaustive over all 5⁹ allocations).
- **Coordinator** (`k4/sdc/pw5_max_check.py`, `results/k4_sdc/pw5_max_check.log`). PW5's failing start is a
  maximum-matching start: every agent picks, and ν = 5. No free completion exists after any of the 555 moves. So
  **OC^max and OC₁^max fail at k = 5**.
  - Mechanism: three frozen agents share a 4-good junk danger set D, and the two receivers each take at most one good
    of D. One chain removes one pair of D, and two goods are left.
  - At k = 4 a danger set has at most 3 junk goods, and one chain leaves at most 1. That is the k − 3 count, and a
    proof of OC₁^max must use it.
  - Recorded in `k4/sdc.md` §31 and in the K4.SDC.OC1MAX row.
- **General k.** The one-move form stops at k = 4. The candidates for arbitrary k are the move ladder (⌊(k−1)/2⌋
  moves, `k4/ksens.md`) and a round of disjoint chains, both restricted to maximum-matching starts. ksens is asked to
  test both on PW5-type families at k = 5, 6, 8.
- **Referee, item 5:** CH-A and CH-B are **CORRECT** (`k4/referee/charity.md`).
- **kgen-charity:** W(k, 0) and W(k, 1) are FALSE at k = 3 and 4 (CH-F, two maximizers), so welfare maxima give no
  bounded charity. Proposition DU: every instance with ≥ 2 components containing agents has a complete EFX₀
  allocation. Checked on reading by the coordinator, and queued for the referee.

### 2026-11-26 22:12 UTC: OC₁^max on every n = 5 core hypergraph; RD refuted at k = 5
- **Coordinator** (`k4/sdc/oc1max_n5_lists.py`, `results/k4_sdc/oc1max_n5_lists.log`, 538 s).
  - The data: all 31,584 n = 5 core hypergraphs of `results/k4_certs_5_*.json.gz` (one to five 4-good agents),
    3 random strict balanced profiles each with (C4), every order.
  - **0 failures among 11,002,996 maximum-matching orders.** 176,670 of them need one move.
  - 12 non-maximum orders fail, which is the pickless shape, rediscovered at random in the n4_3 two-private class.
  - Earlier OC₁ data at n = 5 used only the n4_1 and n4_2 lists. Added to the K4.SDC.OC1MAX row.
- **ksens** (`k4/ksens.md` §6).
  - Lemma PL (pool leftover) is now proved.
  - **RD**, one round of vertex-disjoint chains, is **FALSE at k = 5**. Instance RD5: n = 4, m = 7, only agent 0 has 5
    goods, order (0,3,1,2), picks 1, 2, 3, 4. This is a maximum-matching start. Two sequential chains repair it.
    - Mechanism: agent 0's repair needs a pool pair plus two other agents' picks, which needs 5 goods.
  - The general-k candidates left are sequential ladders (two rounds, RD², is next).
  - K4-G4, "some repairing chain leaves no dangerous frozen agent", holds on all 349 curated and 1,392 PW-design
    hard k = 4 starts.

### 2026-11-26 22:34 UTC: hourly burst 2
**Status.** The central k = 4 conjecture is **OC₁^max** (K4.SDC.OC1MAX). Everything it rests on is refereed CORRECT:
MAXSD, SDPO, Lemma MAX, Hall's Lemmas 2/2\*/4, Cor. 2.1, Prop. 3 and F1₁. There is no failure anywhere:
- 11.0M maximum-matching orders at n = 5;
- 33,082 maximum-matching orders on the known core and non-core counterexamples;
- all climbs: coordinator, TTC deficient/dense/MC2, ksens n = 5.

It is false at k = 5 (PW5, RD5, kgen n = 4), so it is a k ≤ 4 statement. Lemma PWk(a) (ksens) proves it on the whole PW
family at k ≤ 4. The open case is ν = n, with frozen agents wanted by pick holders.

**Referee** (PR #108, ready; all items refereed, no GAP or WRONG):
- since 22:00: Hall lemmas, sd-induct lemmas (Lemma U with fixes), MAXSD and SDPO, Lemma MAX, CH-F (third independent
  method), DU, VM's SND, TERM, (I1)–(I5), P0, P1′, HDT, generalized SLACK, HT;
- ledger rows K4.SDC.SDPO and K4.SDC.MAXSD now say refereed.

**Per angle:**
- **TTC**: OC₁^max climbs on Hall-deficient, dense and MC2 cores (n = 6–8) all clean. Lemma T5 is the same as
  Lemma MAX. Next: a SAT sweep at n = 6 with ν = 6 and two or more 4-good agents.
- **Hall**: next is the written proof of D1 for maximum-matching starts, then |D| ≥ 2, split into disjoint danger
  sets (Lemma PL) and shared ones (the PWk(a) chain).
- **ksens**: Lemma PL proved. Lemma PWk: (a) proved; (b) one chain fails exactly when W ≥ 2 and
  W + 2 ≤ r ≤ min(W + f − 1, 2f − 1). RD (one round) is false at k = 5; the general-k candidate is RD² (two rounds).
  Next: a depth-two RD5 and R(k).
- **VM**: VMX2 succeeds on all 372 named items and survives climbs. VM1's invariant is refereed. V-M matchings are
  Pareto optimal but not always maximum: VM1 completes on B< from non-maximum starts, using rotation. Next: the HDT
  gap classes, and VM1 at k = 5.
- **girth**: Theorem T1 is in the ledger-candidate table. Conjecture DYN (LSS Algorithm 2 plus dynamic parking) has no
  failure on more than 5M profiles. Next: DYN at k = 5, and turning parking into a rule.
- **haxell**: CONN2 (partial EFX₀ allocations reach complete ones in ≤ 2-move steps) survives all tests. Next: k = 5
  robustness, then the termination measure.
- **p3**: retargeted to OC₁^max on the (4, 3) cell; p ≤ 2 would be an algorithmic proof of the multigraph theorem.
- **sd-induct**: finishing PR #103 with the Lemma U fix, then CEGAR synthesis against OC₁^max with ν = n.
- **kgen-n3**: sole focus on Lemma T, which completes Theorem 2 (two agents, every k).
- **kgen-charity**: CH-F and DU refereed. Next: write up the d-dependent bounds, then the many-valuer case.
- **hunt**: the β = 5, n = 6 CEGAR run continues (about 2 h left).
- **k3-oc1**: n = 4 DE-trade rules repair all starts; n = 5 is running.

**New session**: a Lean frame for OC₁^max ⟹ TARGET₄ with SDPO, MAXSD and Lemma MAX (session_01BYMGecPDq28nRFGVkqASck).

**General k.** The surviving arbitrary-k candidates are RD² from maximum-matching starts (ksens), VM1 (rotation-based),
DYN and CONN2. Each session is asked to test its candidate on PW5, RD5 and kgen n = 4.
- **Coordinator's own angle this burst: Lemma RED** (`k4/sdc.md` §31; written proof, not refereed). At maximum-matching
  picks, the pickless agents U, the agents S reachable from them by alternating paths, and all of their goods can be
  removed, and the U agents become null agents. Any completion of the rest extends.
  - So OC₁^max reduces to **OC₁ at perfect starts** (every agent with a relevant good holds a pick, null agents
    allowed), for arbitrary instances with ≤ 4 goods per agent.
  - With MAXSD this gives TARGET₄ without the core reduction.
  - Test of the non-core form: `oc1max_climb.py` with LOOSE=1, running. The 84 non-core TTC instances already pass.
  - Sent to the Hall session (D1 can assume ν = n) and to the Lean session (a second frame, ConjOC1perf ⟹ TARGET₄).

### 2026-11-26 22:53 UTC: Theorem 2 and CH-KD refereed; D1 reduced; RD² survives full valuations; two new sessions
- **Referee:**
  - **Theorem 2** (kgen-n3, PR #97) is **CORRECT**, with Fact L, Lemma M and the Tops Lemma. It gives two-agent
    OC₁ (t ≥ 0) at every k, with ties and zeros, constructed in O(m log m). Bare two-agent EFX₀ existence is
    Plaut–Roughgarden Thm 4.3 (published). The new part is the OC₁ shape: the picks are kept, or one chain a → b
    repairs, and each agent keeps its distinct favourite (Claim T).
  - **Theorem CH-KD** (kgen-charity) is **CORRECT**. A k-limited instance with ≤ d valuers per good has an EFX₀
    state with strong charity leaving at most min{(k − 2)d − 1, max{p : p! ≤ d^(p−1)}} goods out, independent of n.
  - **Lemma PWk(a)** is CORRECT WITH FIXES; the fix has been applied (ksens). **Lemma PL** is CORRECT. **Lemma T5**
    (TTC) is the same as Lemma MAX.
- **Hall** (§21): Finding D1 reduces to two named obstacles, HEAD and CROWD.
  - Every canonical chain free of both repairs; this is proved (Lemmas D1-chain and D1-red, Prop. 3′).
  - Open: D1-H and D1-C, and Conjecture D1-LONG (a longest canonical chain repairs, on 197/197 starts).
  - Lemma RED checked with no hole. Null agents count as ordinary agents; this is noted in §31.
- **ksens**: RD² is not refuted at unrestricted k. With every agent valuing every good (strict, positive), no start
  needs even two rounds: n = 3, m ≤ 9; n = 4, m ≤ 8; climbs; PW5 lifted. So zero values are what make the second
  round necessary.
- **VM**: VM1 holds at k = 5 on PW5, PW4, RD5, RD4 and both kgen n = 4 instances, and on 2,000 random 5-limited
  instances. It is a general-k candidate. Lemma EXT is proved. The repair classes are tabulated (k4/vm.md §7.5).
- **New sessions** (the user asked for more):
  - (1) the |D| ≥ 2 case of OC₁ at perfect starts, in parallel with the Hall session's |D| = 1;
  - (2) ROUND⁺, one round of disjoint chains for strictly positive values; at n = 4 it would imply EFX for four
    additive agents.

### 2026-11-26 22:55 UTC: kgen-n3 redirected; matching-theory session
- **kgen-n3, Proposition H** (`kgen/n3.md` §10). OC₁, or any one-chain or two-round form, at n = 3 for every k implies EFX₀ for three additive agents (the Chaudhury–Garg–Mehlhorn theorem), via distinct tops worth L + δ. So general-k n = 3 proofs are as hard as reproving that theorem. Fixed small k is not covered, because the reduction raises k by 3.
  - Corollary 3: OC₁ (t ≥ 0) at n = 3 holds at every k when some pick is top-heavy.
  - Redirected to option (b): read the simpler three-agent EFX proof, and see whether its potential argument runs as rounds of §29 chains from an SD start, and what n = 4 would need. TARGET₄ at n ≤ 5 is already certified.
- **New session**: matching theory. One-absorber completability is a bipartite matching (Lemma 2\*), and improving chains are augmenting paths. Target: deficiency ≤ 1 at perfect starts when k ≤ 4. PW5 should have deficiency 2.

### 2026-11-26 22:58 UTC: five more sessions (user: as many in parallel as is OK)
- New sessions:
  - D1-C / D1-H (H-ii), split off from the Hall session;
  - ordinal-CEGAR certification of OC₁^max for all profiles at n ≤ 5, aiming at a CERTIFIED row;
  - monotone EFX₀ with bounded relevance (side angle: does bounded k rescue monotone EFX₀, given the 3-agent, 8-good monotone counterexample?);
  - new certified twin and dense-configuration reductions (toward TARGET₄ at β = 5);
  - a paper draft of the refereed results.
- **Haxell**: Conjecture W, at most 2-move composites (reassignment, swap, rotation along any cycle) decreasing (|pool|, −welfare). No stuck state on ~5.8M partial EFX₀ states, including every counterexample, at k = 3, 4, 5, 7 and with every good relevant. Rotations are necessary (family CYC_n). W implies TARGET₄, and its general form implies EFX₀ existence. Asked to test the CH-F and S′ stranded states.
- **Lean** (formal/k4-oc1max, draft PR #109): SDPO (both inclusions), MAXSD, Lemma MAX, the §29 moves, OneAbsorber, ConjOC1max and target4_of_conjOC1max are machine-checked (session's report; the coordinator's independent re-run of lean/check.sh is in progress). Next: ConjOC1perf ⟹ TARGET₄ via RED.

### 2026-11-26 23:12 UTC: Lean frame verified independently; ROUND⁺ refuted; VM1 bounded; n = 6 sweep; W stress
- **Lean** (formal/k4-oc1max, PR #109, head 28f3e1e). The coordinator re-ran `lean/check.sh` independently in a
  fresh worktree: **CHECK PASSED**, 1,253 audited statements, 2,358 theorems, standard axioms only, 0 sorry, 0
  warnings. Machine-checked:
  - SDPO (strict values; both inclusions), MAXSD and Lemma MAX;
  - the §29 moves (IsAddition, IsChain, IsRing) and OneAbsorber;
  - `EFX.OC1Max.target4_of_conjOC1max` (OC₁^max ⟹ TARGET₄);
  - `target4_of_conjOC1perf`: OC₁ at perfect starts for all strict instances with ≤ 4 relevant goods implies
    TARGET₄, with no core reduction, via tie-breaking, MAXSD and RED's allocation part.
  So both reductions of TARGET₄ to the central conjectures are machine-checked.
- **ROUND⁺ is FALSE** at strictly positive values (kgen-rounds, PR #111): n = 4, m = 7, order (2, 1, 3, 0); also an
  RD5 lift and n = 5 cases. The coordinator replayed it independently (`k4/sdc/roundplus_cex_check.py`): 18 EFX₀
  allocations, 8 dominating; no free completion at the picks, after any of the 91 moves, or after any of the 133
  rounds of two disjoint moves. Two rounds suffice everywhere. So RD² (two rounds) remains the round candidate,
  and zero values are not what forces the second round.
- **VM1 is refuted at k = 7** (PW(2,3,6), n = 5, m = 11; VM session, two checkers), so VM1 is a k ≤ 6 statement.
  VMX₂ (any number of moves) survives. The rotation class always needs exactly one ring (Conjecture Ring₄, stated).
- **TTC, n = 6 sweep part 1**: all 119,108 n = 6 hypergraphs with two 4-good agents and ν = 6, 3 profiles each:
  1,812,773 maximum-matching starts, **0 failures**, 37,620 needing a move. The tightest starts have m = n + 2,
  5 agents frozen, a single receiver, and 2 dangerous agents with disjoint junk.
- **Hall and D1 sessions**: Proposition D1-C′ (proved) covers 224 of 227 chains without HEAD. D1 reduces to H(ii)
  and the rare residual cases C-a, C-b, C-c. The split with proof/k4-d1 is agreed.
- **kgen-n3**: AACGMM (arXiv 2205.07638v2) handles EFX₀ at n = 3 but moves picks. Conjecture OPB₃ (one pick per
  bundle together with AACGMM's invariants) is satisfiable on all data. AACGMM with the picks carried breaks in its
  PR start (a 4-good example), in compression and in the choice of g_i. A repaired PR step is next.
- **Haxell W**: W escapes the CH-F stranded welfare maxima in two moves (198 → 197 with one good out, then
  completes), and every S and S′ state up to n = 40. It is exhaustive at n = 6 on B< and B>: 710,279 states each,
  none stuck. Nothing in the data uses k ≤ 4, so W is a general-EFX₀ candidate.

### 2026-11-26 23:14 UTC: OC₁^max REFUTED at k = 4, n = 4 (verified)
- The compute/k4-oc1max-cert session's ordinal CEGAR (n = 4 core list 4_n4_3) found two strict connected MC2-class
  cores with m = 7. In each, a perfect (maximum-matching) SD start has neither a completion at the picks nor one
  after any single move, not even freely.
  - Instance 1: sets [[0,1,2,5],[1,2,5,6],[3,4,5,6],[3,4,6]], vals [[2,10,4,7],[10,3,4,8],[3,5,6,7],[3,2,4]], order
    (0,3,2,1).
  - Verified by the coordinator's own code (`k4/sdc/oc1max_cex_verify.py`, `results/k4_sdc/oc1max_cex_verify.log`).
  - Ledger: K4.SDC.OC1MAX is REFUTED. `k4/sdc.md` §31 has the instances.
- **Lesson**: random profiles, 11M maximum-matching orders at n = 5, missed a failure at n = 4. Only the exhaustive
  ordinal search found it, so random testing is weak evidence, as AGENTS.md warns. Every surviving form must now go
  through the same certifier.
- **Surviving forms.**
  - Two sequential moves repair both instances (OC₂^max).
  - Other maximum-matching orders complete at the picks (the ∃-order forms: SD-C, and OC₁ for some
    maximum-matching order).
  - The Lean implications are unaffected, and their move relation is a parameter.
- **Action**: every proof session working on OC₁^max is redirected.
  - The certifier tests OC₂^max and the ∃-forms exhaustively at n = 4 and 5.
  - The proof sessions keep their lemmas, which are about given states, and retarget.

### 2026-11-26 23:36 UTC: hourly burst 3
**Status.**
- OC₁^max is refuted at n = 4: 11 of the 1,002 n = 4 core hypergraphs, all of them perfect starts in the MC2 class.
- **OC₂^max** (≤ 2 sequential moves from maximum-matching starts) is **certified for every strict profile of all
  n = 4 cores** (compute/k4-oc1max-cert, PR #114, with an independent checker).
  - The coordinator's own check of the 11 failing instances (`k4/sdc/oc2max_cex_check.py`): every maximum-matching
    order needs ≤ 2 moves.
  - New ledger row K4.SDC.OC2MAX (CONJECTURE; the certified n ≤ 4 row comes with PR #114).
  - n = 5 is running. A targeted three-move search is running at n = 5–7 (sd-induct). The ∃-order form is next for
    the certifier.
- The Lean frames are parametrized by the move relation, so OC₂^max ⟹ TARGET₄ is a direct instance. The Lean session
  is adding it, plus a machine-checked refutation of OC₁^max.

**Mechanism of the n = 4 failures** (TTC §14, Hall §22, certifier diagnostics):
- a starved last picker that wants every other pick and is the lone receiver;
- two dangerous agents sharing one junk danger pair (|D| ≥ 2);
- every target allocation gives some agent a bundle pieced from two owners' picks. That is a tree exchange, which no
  single chain or ring performs. Two canonical chains split it.
- R1-priority orders fail as well. Other maximum-matching orders of the same profiles work (the ∃-order form survives).

**Per angle:**
- **Hall**: integrator of the OC₂^max proof plan (case tree with owners). Second reader of Lemmas M and EX.
- **proof/k4-d1**: proving D1-C and H(ii).
- **proof/k4-oc1max-multi** (PR #115): Lemma D-red (new obstacle DEMAND), Prop. T0, Lemma KEEP, Lemma SET, all
  written and not refereed. Its census: 85% of hard |D| ≥ 2 starts are repaired by a KEEP or D-red chain. Sub-lemmas
  SLOT and RING are open. Next: the second move for DEMAND.
- **proof/k4-matching** (PR #116): Lemma M (S* completability is an exact slot-graph matching condition) and Lemma
  EX (an exact one-chain exchange criterion, any owner, any |D|), both written. "Deficiency ≤ 1" is false. Its
  Conjecture CM must fail on the n = 4 starts; it is being calibrated there, then extended to two chains (CM₂).
- **TTC**: the mechanism above. Its canonical rule FP+1 holds on the 11 and on 97 walk failures. An n = 5 OC₁^max
  failure outside MC2 needs first moves of kind (B), so the rule is being extended. Next: a hand-built three-owner
  tree.
- **kgen-rounds** (PR #111): ROUND⁺ refuted (n = 4, m = 7, also with two valuation types). Lemma R1, the
  starved-agent certificate, covers all 61 failures. Two rounds repair everything. One round also fails at k = 4 on
  the n = 4 instances (coordinator's check).
- **Haxell**: W as stated (≤ 2 single-good moves) is refuted at n = 2, m = 7. W₃ (k ≤ 4) and W^sub (set moves,
  k-independent) survive. Exhaustive n = 2 and n = 3 grids are next.
- **VM**: VM1 is refuted at k = 7 and also at k = 6 (PW(4,3,5)#1). VMX₂ survives. Asked for exhaustive n ≤ 4 checks
  of VM1 at k = 4.
- **girth**: DYN plus envy-cycle rotation clears all 376 curated stuck cases, and every random failure completes under
  another labeling. Asked for an exhaustive ∃-labeling check at n ≤ 4.
- **p3**: all 11 failures are repaired by two moves, and OC₁^max holds on multigraph cores with n ≤ 4 (certificate
  pending). Every good in a shared junk danger pair has 3 valuers. Next: certify p ≤ 2 at n = 5 and try a proof.
- **kgen-n3**: OPB₃ is satisfiable. AACGMM with the picks carried breaks in its PR start; a repaired PR step is next.
- **kgen-charity**: Conjecture OL (one loser). Asked for an exhaustive small-n check, then n = 2 and n = 3 proofs.
- **referee**: 14 items done, PR #108 ready. New queue: Lemmas M, EX, D-red, T0, KEEP, SET, D1 lemmas, R1, Prop. H,
  Lemma EC, and spot-checks of the certificates.
- **paper** (PR #110): draft complete, being updated for this hour's refutations.
- **monotone-k, twins, hunt, Lean, k3-oc1**: running (twins: configuration dbl-P4-P4 reduced for all 82,944 types).

**Cross-cutting lesson.** Every surviving conjecture now goes through an exhaustive ordinal or grid check at n ≤ 4
before any proof effort: DYN, W₃/W^sub, VM1, RD², OL and OC₂^max.

### 2026-11-26 23:38 UTC: D1-C proved; k = 3 one-chain exhaustive at n ≤ 4; monotone k ≤ 3 theorem; VM1 at k = 6
- **proof/k4-d1** (PR #113): **Theorem D1-C** proved (written, k4/d1.md §3), stronger than the sub-lemma. At a hard
  start with D = {k}, every canonical chain without HEAD has a minimal improving H₀ whose state has an S* completion
  owned by k.
  - It uses Fact R, a k ≤ 4 fact: of an agent's ≤ 3 pool goods, at most one is non-robust.
  - Its contrapositive is checked on every D = {k} start: 0 gaps, and about 1,500 new CROWD-only chains all repair as
    predicted.
  - So D1 reduces to all-HEAD starts. In the data these are all n = 3, t = 1, f = 1 with two unfrozen wanters.
  - Queued for the referee.
- **ksens**:
  - All 11 n = 4 failures are replayed with two checkers. RD (one round) also fails there, and every neediest-first
    start holds.
  - **k = 3: one chain suffices from every start, exhaustively** for every strict profile of every connected
    hypergraph with n ≤ 4: 1,885,816 profiles and 4,982,948 starts at n = 4, 0 failures, SAT cross-check. n = 5 is
    running.
  - Ladder: Conjecture L′, ⌊k/2⌋ chains. k = 3 needs 1, k = 4 needs 2 (tight), and k = 5 needs 2. The deciding rung
    is k = 6 (three chains?).
- **monotone-k** (PR #112): **Theorem M3** (written proof; queued for the referee). Monotone EFX₀ exists whenever every
  agent has ≤ 3 relevant goods: a nondegenerate monotone valuation on ≤ 3 goods has an additive surrogate with the
  same disjoint-set comparisons, and then TARGET applies.
  - This fails at 4 goods, so monotone k = 4 is a strictly larger class than additive k = 4.
  - SAT search: no monotone counterexample at k = 4 for n = 3, 4, or at k = 5 for n = 3. So the monotone threshold k*
    is in {4, …, 8} (the published counterexample has k = 8).
- **VM**: VM1 is refuted at k = 6 as well (PW(4,3,5)#1, n = 7, m = 12, two checkers).
  - PW(3,3,8) at k = 9 needs exactly three moves.
  - VM1-plain (one move, then F1 placement with no rotation) holds on every k ≤ 5 instance tested, including DE's
    ring-size tree family.
  - Proved: (RS) the shape of envy cycles, (RX) and (MS).

### 2026-11-26 23:42 UTC: OC₂^max case tree (Hall, §23); D1-H refuted, D1-HJ open; OC2-LIFT stated
- **Hall (integrator), `k4/oc1_hall.md` §23.** The case tree for OC₂^max has 15 leaves:

  | leaf | case | status |
  |---|---|---|
  | 0 | reduction to perfect starts (RED + MAX) | refereed |
  | 1 | the picks complete (Lemma 1, 2\*, M) | proved |
  | 2 | a hard start has D ≠ ∅ (T0) | proved |
  | 3 | \|D\| = 1, one move | proved, apart from 3a and 3b |
  | 3a | crowding residuals | D1-C, written by proof/k4-d1 |
  | 3b | all-HEAD starts (D1-HJ) | OPEN |
  | 4 | \|D\| ≥ 2 (D-red) | proved |
  | 4a | TR | proved |
  | 4b | KEEP | proved; KEEP-C open |
  | 4c | SET/OWN | proved |
  | 4d | SLOT | OPEN |
  | 4e | RING | OPEN |
  | 4f | disjoint danger sets need one move | UNVERIFIED |
  | 5 | **the second move, Sub-lemma OC2-LIFT** | OPEN |
  | 6 | three moves | the certifier's search |

  - OC2-LIFT: at a hard perfect start with no one-move repair, some canonical chain P₁ from k ∈ D is followed by a
    move P₂ that either starts at, or unfreezes (by lifting its wanters), every DEMAND agent of P₁, and the result has
    a one-absorber completion.
  - OC2-LIFT holds on 12/12: the 11 n = 4 failures and the TTC n = 5 core. The literal "P₂ starts at the DEMAND
    agent" form fails on 6 of the 12.
  - Second reading of the matching session's lemmas: Lemma M is CORRECT and equivalent to Lemma 2\*. Lemma EX is
    CORRECT as a sufficient condition but not exact (lb4-n2m5-upgrade); the matching session has been told.
- **proof/k4-d1**:
  - D1-H and D1-LONG are REFUTED for canonical chains. D1H-X: n = 3, m = 8. The coordinator checked it: the picks
    have no one-absorber completion and one move repairs.
  - The surviving leaf is D1-HJ: the head may add at most one junk good. Evidence 59/59.
- **Coordinator**: OC₂^max random spot-check at n = 5 (`k4/sdc/oc2max_lists.py`, `results/k4_sdc/oc2max_lists_n5.log`)
  covered all 31,584 hypergraphs × 3 profiles with 0 failures, but random profiles never hit a two-move start, so it
  is weak evidence. The certifier's exhaustive n = 5 run is the real test.
- **Paper** (PR #110): revised for the refutations; its checker passes 50/50.

### 2026-11-26 23:46 UTC: Lemmas M and EX refereed; CM₂ on all two-move data; Theorem U; OPB₄ discrepancy
- **Referee**: the matching session's Lemma M (S* completability as a slot-graph matching) and Lemma EX (one-chain
  exchange, sufficient) are **CORRECT** (`k4/referee/matching.md`).
  - 513,753 and 309,568 tests, 0 failures. Every hypothesis is necessary: dropping any one gives failures.
  - A free strengthening of Ext is noted.
- **matching**:
  - Lemma EX\* (EX at any state) is written. Conjecture CM₂ (a first move, then an EX\* exchange) implies OC₂ at
    perfect starts and hence TARGET₄.
  - CM₂ holds on all 30 hard starts of the 11 n = 4 instances, and on PW5 and RD5. EX\* is exact on all of that data.
  - Mechanism, 57/57 pairs: the first chain absorbs a junk pair shared by two dangerous agents. In 35 of the 57, the
    second head collects two foreign picks, one of them released by the first chain.
  - The certifier is asked to export every n = 4 two-move start, for an exhaustive CM₂ test.
- **multi**: Theorem U and Corollary U1, written. U1: one move suffices at perfect starts with one unfrozen holder and
  one truly dangerous agent, whatever |D| is. The written lemmas now cover a repairing chain at 7,602 of 8,383 hard
  |D| ≥ 2 starts. Lemma OWN and RING-red are added.
- **kgen-rounds**: K4W, a non-core k = 4 instance (it has a top-heavy agent), every good valued, where OC₁ and one
  round fail at perfect starts. Superseded by the core counterexamples.
- **kgen-n3**: OPB₄ (one pick per bundle with improving rings) is claimed on the two n = 4 instances. The coordinator's
  brute force disagrees: 14 EFX₀ allocations, 4 with one pick per bundle, none of type 2+2, none with all movers
  gaining. The paper session independently also gets 14. kgen-n3 is checking its EFX₀ predicate; the suspicion is
  ordinary EFX.

### 2026-11-26 23:48 UTC: k = 3 vs k = 4 explained; Conjecture R2; K4.MC8; OPB₄ refuted
- **k3-oc1** (PR #96): OC₁ at maximum-matching starts at **k = 3 holds exhaustively**, with 0 failures:
  - all cores with n = 3–5, and every n = 6 core with m ∈ {10, 11} (35.4M maximum-matching drafts at n = 6);
  - DE's general core case up to n = 5.
  - One DE trade always repairs, and every hard start is perfect. The k = 3 failures are non-maximum (ν − 2 picks),
    the same signature as at k = 4.
  - **Where k = 4 differs.** In both n = 4 counterexamples, a *b-holder* (holding its second-ranked good) is a
    dangerous agent sharing the junk pair: at k = 4, {c, d} can beat b. At k = 3 a b-holder has no junk danger set,
    and two top-holders sharing a pair are cleared by one DE chain.
  - The referee's Lemma 3 fix and the R1C scope note are applied.
- **TTC: Conjecture R2.** At a maximum-matching start with ≥ 2 receivers, OC₁^max holds. Every one-move failure seen
  has exactly one receiver: the 11, 1,174 walk failures and 17 at n = 5. With one receiver, every base-keeping
  completion puts all the junk there.
  - The certifier is asked to check R2 exhaustively at n = 4. FP+1^max held at all 1,174 walk failures.
  - The three-owner design produced no failure in 4,109 instances.
- **proof/k4-twins** (PR #117): **K4.MC8** certified, with an independent checker and a sensitivity test. Two agents
  sharing two goods valued by nobody else cannot both be non-Q4 in a minimal counterexample, and several partial
  cases are recorded.
  - It prunes the β = 5, n = 6 hunt list from 30,337 to 20,882 and the β = 4 list from 5,558 to 3,166, including 4
    of the 6 graphical all-P4 cores.
  - Identical relevant sets give no local reduction: there is a proved impossibility for I = ∅. Queued for the
    referee.
- **kgen-n3**: the mismatch is resolved. Its A and B instances are the k ≥ 5 ones (A has 63 type-2+2 OPB
  allocations). On the k = 4 instance there are 14 EFX₀ allocations and none with all movers gaining, so **OPB₄ is
  refuted at k = 4**. OPB₃ is next, by exhaustive check.
- **kgen-charity**: Lemma OL0 (reduction) and Prop. P1₂ (n = 2: every Pareto maximum is complete). OL holds
  exhaustively at n = 2 (k = 3, 4), n = 3 (k = 3) and n = 4 (k = 3). CGM's own n = 3 obstruction has a one-loser
  completion.
- **Certifier**: n = 5 OC₂^max is running in chunks (ETA 7–9 h). The failing-profile density at n = 4 is about 10⁻⁵,
  which is why random testing missed it.

### 2026-11-26 23:51 UTC: Lemma T6 (human-checkable refutation certificate); CM₂ on 3,308 failures; VM1 on non-cores
- **TTC: Lemma T6** (written proof, `k4/ttc.md` §14.2). After one de_free move from a perfect start, and then any
  base-keeping completion, the result has these properties:
  - (a) it value-dominates the picks;
  - (b) each bundle holds at most two other agents' picks;
  - (c) a bundle holding two is a chain member j ≥ 1 holding Y_{x_t}, and its own step was improving.

  The certificate corollary: if every dominating EFX₀ allocation has an agent with three or more foreign picks, or
  with two picks P, Q such that v_i(P) + v_i(J ∩ R_i) ≤ v_i(Y_i) and likewise for Q, then no single move works.
  - All 11 n = 4 counterexamples satisfy it, each through one agent. So, given the list of dominating EFX₀
    allocations (brute force), the refutation is checkable by hand.
  - Queued for the referee.
- **matching**: walks of the values near the 11 failing profiles found 3,308 distinct OC₁^max failures, all on the
  same 11 hypergraphs.
  - CM₂ holds at every one, and EX\* is exact on the second move. EX\* is corrected: it is Lemma M at the post-move
    state, with Ext as compensable slots.
  - 88 starts satisfy OC₁ only through a non-S\* completion, so "Finding S\*" fails at n = 4, but CM₂ holds there.
  - Random profiles on the same hypergraphs (33,000) hit none, so the failures cluster in value-space.
- **VM**: VM1 is refuted at k = 4 on NON-cores (K4-min, K4-cut, n = 5) and at k = 5 (K5).
  - VM1 on cores is unrefuted but untested exhaustively; it has been asked to run on the 11 n = 4 cores and on all
    n ≤ 4 profiles.
  - VM1-chain (one VM1 move or one DE chain, then placement with rotation) repairs 19 of the 20 known VM1 failures;
    PW(3,3,8) at k = 9 needs 3 moves. VMX₂ completes every failure.
- **Certifier**: n = 5 chunk 1 (868 hypergraphs) is all OC₂^max-certified and independently checked.
  - Mechanism on all 11: one unfrozen agent, and two frozen agents sharing one junk danger pair. That is the PW5
    mechanism at k = 4.

### 2026-11-26 23:59 UTC: referee confirms the OC₁^max refutation; D1 lemmas and the multi reductions refereed; VM1 on cores refuted
- **Referee** (`k4/referee/oc1_hall_d1.md`, `k4/referee/oc1max_multi.md` on claude/k4-referee):
  - Hall §21–§22, **CORRECT**: Lemma D1-chain, Prop. 3′, Lemma D1-red (with Remarks 1–2), Lemma D1-C₀ and
    Prop. D1-C′. They were checked on 126,879 hard starts, 0 failures.
  - **The OC₁^max refutation is confirmed by brute force**: cex1, cex2 and the TTC n = 5 core are strict and perfect.
    No chain state or addition has a one-absorber completion, and two sequential chains repair each.
  - proof/k4-oc1max-multi, **CORRECT**: D-red, T0, KEEP, SET, OWN, Corollaries TR and KEEP-1, and RING-red. Four
    wording fixes, no gap. 172,394 chains tested, and every hypothesis is necessary. Theorem U is next.
- **VM**: VM1 is refuted on strict connected k = 4 cores too. C0: n = 5, m = 8, MC2 class, three checks. The
  coordinator confirms C0 is a strict MC2 core and that the stated two-move completion is EFX₀. From every
  maximum-matching SD order, OC₁ holds at C0, so VM1 fails because its start is a V-M matching. VM1-chain (one DE
  chain allowed) completes all 5 failing cores and all 315 PW instances up to k = 9 except PW(3,3,8).
- **TTC**: hand-built three-owner and ladder designs give no three-move start. Informal reason: at k = 4 an agent's
  private junk plus its pick leaves room for only two foreign picks (cf. Lemma T6), and each move unfreezes agents. R2
  does not extend to post-move states (blocked holders).
- **kgen-rounds**: C4K, a further n = 4 OC₁^max failure on a strict core, four checks. Its hypergraph is isomorphic to
  the certifier's instance 2 (coordinator's check), so it is consistent with the certificate.
- **Lean** (formal/k4-oc1max, PR #109, head 598e135):
  - `EFX.OC1Max.not_conjOC1max` and `not_conjOC1perf` machine-check the refutation on instance 1 (no completion at
    all, after any OneMove);
  - OCVariants.lean adds ConjOCkmax / ConjOC2max ⟹ TARGET₄ and the ∃-order frame ConjOC1exmax ⟹ TARGET₄.
  - The coordinator's independent check.sh re-run is in progress; it compiled with 0 errors and 0 warnings.
- **Ledger**: new CONJECTURE row K4.SDC.OC1EXMAX (the ∃-order form).

### 2026-11-27 00:04 UTC: Lean refutation of OC₁^max verified independently; OC₁′ (one-move candidate); Lemma LIFT (recursion)
- **Lean** (formal/k4-oc1max, PR #109, head 598e135). The coordinator re-ran `lean/check.sh` independently: **CHECK
  PASSED**, 1,278 audited statements, 2,417 theorems, standard axioms only.
  - `EFX.OC1Max.not_conjOC1max : ¬ ConjOC1max (Fin 4) (Fin 7)` is **machine-checked on instance 1**, together with
    the core, connected, strict and maximum hypotheses. No completion at all exists at the picks or after any OneMove.
  - Also machine-checked: ConjOCkmax ⟹ TARGET₄, ConjOC2max ⟹ TARGET₄, the perfect-start variants, and ConjOC1exmax
    ⟹ TARGET₄.
- **kgen-rounds: OC₁′**, a one-move candidate. It is the official move, except that non-end chain agents may also take
  goods of the end's released base. Every agent still gains, so it implies MD and TARGET₄.
  - It repairs every known OC₁ failure at perfect starts: 77 zero-version starts plus 16 new climb instances (14
    strict n = 4 cores on 3 hypergraphs), C4K, K4W and W4. Two implementations agree.
  - The certifier is asked to test OC₁′^max exhaustively at n = 4.
- **multi: Lemma LIFT** (written proof, k4/oc1max_multi.md §8). After a chain that settles one sharer k with a pair T,
  delete k and T. Moves of the reduced instance I⁻ are moves of I, and its non-threatening completions lift. So OC₂
  becomes "settle one sharer, then OC₁ in I⁻".
  - It holds on the 12 known failures and 4,356 walk failures. The open part is Sub-lemma OC2-REC.
  - Leaf-4f census: 7,755 of 8,383 one-move starts have no sharing. Sharing is necessary for every known two-move
    start but not sufficient.
- **kgen-n3**: OPB₃ is **refuted** exhaustively at n = 3, k = 4 (smallest: m = 5). The OPB line is closed. kgen-n3 and
  k3-oc1 are set to prove OC₁ at maximum-matching starts for k = 3, every n (exhaustively true up to n = 6).
- **Referee**: Lemma R1 and the starved-agent certificate are CORRECT, with a fix to a printed repair. Prop. H is
  CORRECT WITH FIXES (a sign in one display).
- **Open core at k = 4** (Hall §23.2, one owner each):
  - D1-HJ: proof/k4-d1;
  - R2: TTC;
  - LIFT-1 + LIFT-EX(2), or equivalently OC2-REC: matching and multi;
  - SLOT and RING: multi.

### 2026-11-27 00:19 UTC: the second move's tools are refereed; what is left is existence of shapes
- **Referee**:
  - **CORRECT** (`k4/referee/lift.md`, `k4/referee/oc1max_multi.md` §8):
    - Lemma EX\* (= Lemma M at the post-move state);
    - Lemma LIFT-red (its junk-free P₁ condition is necessary: 14 pairs fail without it);
    - Lemma LIFT-1 (slightly stronger than stated: "t is z's favourite" is unnecessary);
    - multi's Lemma LIFT;
    - **Theorem U / Corollary U1**. The hypothesis the Hall session worried about is implied by D_T = {k}.
  - Tested on 98,086 random perfect starts plus 1,388 one-move-failing starts, 0 failures. Every mutation produces
    failures.
- **So the k = 4 second move is now:**
  - refereed lemmas: EX\*, LIFT-red, LIFT-1, LIFT;
  - plus an existence statement: LIFT-SHAPE⁺ (matching) or OC2-REC (multi). It holds on all 8,073 distinct failing
    starts (n = 4 and 5).
  - **Count correction** (matching session): the n = 4 walk count is 3,179, not 3,190 or 3,308, because the 11 stored
    instances had been counted twice. No "holds on all" claim changes.
- **Open core at k = 4** (each with an owner):
  - D1-HJ, now D1-H in the MC2 class: the three-agent core is computer-verified (Prop. D1-H₃); the reduction to the
    core is open (proof/k4-d1);
  - R2 (TTC): Lemma R2-0 is proved; R2★ is the strong form, at 79/79 + 466/466 + 4,027 starts;
  - LIFT-SHAPE⁺ (matching);
  - SLOT and RING (multi), which need the new compensated Lemma M^c, now being built.
  - Plus the one-move alternative OC₁′ (kgen-rounds; it holds on the 11), under the certifier's test.
- **Certifier**: the referee independently re-checked the 11 n = 4 counterexamples and a sample of 35,858 OC₂^max
  witnesses, 0 disagreements. n = 5 is running.
- **VM**:
  - VM1 holds on all 11 OC₁^max cores with zero moves (V-M starts avoid the obstruction).
  - VM1-chain holds on 3,485 VM1-failing cores from targeted walks.
  - Exhaustive VM1-chain certification: n = 2 done, n = 3 and 4 running.
- **DYN** (girth): ∃-labeling certified exhaustively at n = 2, 3 and for n = 4 with ≤ 2 four-good agents (≈ 10⁹
  profiles); larger cases running. "One labeling per hypergraph" is refuted.
- **Monotone** (PR #112): MONO.N3K6 CERTIFIED: three agents with ≤ 6 relevant goods always have monotone EFX₀, so
  the n = 3 monotone threshold is 7 or 8.

### 2026-11-27 00:40 UTC: hourly burst 4
**Status.** TARGET₄ is open. The central candidate is **OC₂^max**: at most two sequential moves from maximum-matching
starts.
- Certified:
  - OC₂^max for every strict profile with n ≤ 4, re-checked by the referee: 35,858 sampled witnesses, 0 disagreements;
  - **OC₁^∃max** (some maximum-matching order needs ≤ 1 move) for every strict profile with n ≤ 4 (∃-CEGAR,
    independent checker);
  - **R2 at n = 4**: all 112,880 failing (profile, picks) pairs on the 11 hypergraphs have exactly one receiver.
- n = 5, in progress:
  - 5_n4_1 (1,735 cores): OC₂^max certified, and OC₁^max holds;
  - 5_pure, first ~700 cores: 128 hypergraphs with OC₁^max failures, every one single-receiver, OC₂^max holds.
  - The coordinator replayed one MC2-class n = 5 failure (5_pure idx 164): a strict MC2 core, OC₁ fails, two moves
    repair.
- Refereed this hour, all CORRECT:
  - EX\*, LIFT-red, LIFT-1, LIFT (the second move's tools);
  - Theorem U / U1;
  - T6 and its certificate;
  - M3 (monotone k ≤ 3);
  - K4.MC8;
  - D1-chain, Prop. 3′, D1-red, D1-C₀, D1-C′;
  - Lemma R1;
  - Prop. H (with a fix);
  - Lemma EC.

**Open core at k = 4** (Hall §23.2):
- D1-H2: computer-verified on the three-agent core; CONTRACT reduces t = 1 to it modulo S1 and S2; t ≥ 2 is open
  (proof/k4-d1).
- R2-M: M^c's condition at the post-chain state with owner x₀. Lemma R2-G2 is proved and R2 is certified at n = 4
  (TTC).
- LIFT-SHAPE⁺: the shape of the two chains; holds on all 8,073 failing starts (matching).
- SLOT and RING: existence counts, since plain Lemma M certifies every repair (multi).
- Shared tool: Lemma M^c (multi, written; matching re-implemented it, 0 mismatches; queued for the referee). It is an
  exact one-move criterion on all data.

**One-move alternatives still alive:**
- OC₁′ (kgen-rounds: middle chain agents may take goods of the end's released base). It holds on all 11 n = 4
  hypergraphs' stored starts; the certifier's exhaustive test comes after its n = 5 chunk.
- VM1-chain (VM): exhaustive certification running; holds on 3,485 VM1-failing cores.
- DYN∃ (girth): certified at n ≤ 3 and for most n = 4 classes.
- W^sub (Haxell): 0 stuck on 470M n = 2 and 742M n = 3 states.

**Dispatch this burst:**
- p3: prove MG (OC₁^max on multigraph cores, p ≤ 2). MG5 is certified at n ≤ 5, and every known failure needs a
  3-valuer good.
- Lean: formalize Lemma M, LIFT-1 and T6.
- paper: next revision with this hour's referee verdicts and certificates, plus the open-core section.
- sd-induct: retired after PR #103, with its three-move search covered by the certifier and TTC.
- ksens: k = 6 three-move test and k = 5 exhaustive two-move test.
- Haxell: finish the n = 3 grid and try a W^sub proof at n = 2.
- multi: the SLOT and RING existence proofs.
- Hall: the numbered open-core list.
- kgen-rounds: RD²⁺ grids, and whether every two-move repair compresses into one OC₁′ move.

**Correction:** the matching session's n = 4 walk count is 3,179 (not 3,190 or 3,308; the earlier figures counted the
11 stored instances twice). No "holds on all" claim changes.

### 2026-11-27 01:02 UTC: burst 4, addendum (OC₁′, merging)
- **OC₁′^max: holds at n = 4, REFUTED at n = 5.** OC₁′ is kgen-rounds' widened single move: non-end chain agents may
  also take the end's released pick.
  - n = 4: it holds at all 112,880 OC₁^max-failing starts of the certifier's export. Implementations: kgen-rounds' rnd.c,
    and the coordinator's own widened generator (`k4/sdc/oc1prime_verify.py`, 140 s). So it holds on every n = 4 core,
    given the certifier's certificate. On a 1/10 sample, every OC₁′ repair even has a free completion, with no
    absorber.
  - n = 5: on the certifier's 5_pure idx 164 (perfect start (7,2,3,5,4)), none of the 21 OC₁′ states completes.
    Implementations: coordinator, verify_k4zero, rnd.c.
  - The cause is **two disjoint conflicts**: 0 ↔ 1 must swap, and agent 3, whose pick is worth 2, must be upgraded from
    agent 4 or agent 2. One round of two disjoint rings repairs it, and so do two sequential moves. Ledger row
    K4.SDC.OC1PMAX, `k4/sdc.md` §31 end.
- **Negative: gluing does not compound conflicts.** Two copies of idx 164 glued at junk good 0 (n = 10, a strict
  connected MC2 core) complete at the picks.
  - One agent absorbs junk of both copies. Goods of the other copy are worth 0 to it, so in EFX₀ they act as a sink.
  - The general point: an SD start's junk is never envied as a singleton, so junk can go next to any unwanted pick.
  - Larger n tends to add sinks. Small, dense cores are where the obstructions live.
- **Candidates now:**
  - OC₂^max: certified n ≤ 4; n = 5 running.
  - ROUND-P^max: one round of vertex-disjoint OC₁′ moves; holds at n = 4 and on idx 164.
  - OC₁^∃max.
  - Hall asked to split leaf 4 into 4a (a disjoint second repair, ROUND form) and 4b (a genuinely sequential second
    move).
- **Merging (the user authorised merging).**
  - The ready PRs #94, #103, #108, #109, #110, #111 and #115 were merged into this branch. Ledger conflicts were resolved
    keeping both sides' rows, with the Lean columns from #109 and the K4.MULTI rows from #115.
  - On the merged tree: `lean/check.sh` CHECK PASSED (1279 audited statements, 2418 theorems), `check_ledger` 426 rows
    with 0 problems, `check_certs` 0 problems.
  - PR #95 is marked ready, to be merged into main once CI is green. Drafts stay open until their sessions mark them
    ready.

### 2026-11-27 01:38 UTC: hourly burst 5
**Status.** TARGET₄ is open. **OC₂^max at n = 4 now has an explicit, refereed mechanism.**
- Lemma SD-E: the earliest-wanter chain E(k) with a pool pair T, after which deleting k and T leaves exactly the SD
  start of I − k.
- Theorem REC-S: E(k) and T, then a Theorem S chain in I⁻, lifted by Lemma LIFT. Both are by the multi session and
  refereed CORRECT; REC-S's hypothesis (L) turned out to be automatic.
- Certified at all 112,880 n = 4 two-move starts (K4.MULTI.RECS.N4; self-contained checker, 8,241 mutations rejected;
  the referee re-validated every witness).
- What remains of OC₂^max from n = 5: (i) **existence** of (k, T) with (R), i.e. Theorem S applies in I⁻, and (K), k
  unthreatened, at starts needing two moves; (ii) the one-move part where one move suffices. There Theorems U and S prove
  OC₁ at 88.8% of the hard starts, and the residue is SLOT2 (161), RING2 (45), KEEP-C (8) and the D1 items.

**Verified, certified or refereed this hour** (by session):
- certifier (#114, merged):
  - OC₁′^max CERTIFIED at n = 4 (all 1,002 cores, independently checked). It is REFUTED at n = 5: 24 of the first 137
    5_pure OC₁^max failures, all raw-verified; the coordinator's idx 164 is one of them.
  - OC₂^max with S*-shaped completions CERTIFIED at n ≤ 4.
  - TTC's R2-M and R2★ REFUTED at n = 4 (306 of 1,002 cores; 20 raw-verified, TTC replayed 2). R2 itself is unaffected.
- matching: LIFT-SHAPE⁺ CERTIFIED at n = 4 (K4.MATCH.LIFT.N4, referee re-verified with its own witness search) but
  REFUTED at n = 5 at idx 164. The recursion OC2-REC CERTIFIED at n = 4 (K4.MATCH.REC.N4).
- kgen-rounds: OC₁′ at all 112,880 by a second implementation (forward brute force).
  - ROUND-P (pooled takes across chains) and RNDOZ (own chain only, the coordinator's form) agree on all data.
  - The two mechanisms separate exactly. At n = 4 the plain round fails at all 112,880 (starvation) and ROUND-P holds.
    At the n = 5 24 the plain round already holds (two cycles).
  - The only MD allocations that ROUND-P misses have one shape, "keep-and-add".
- referee: Theorem S, HS, HS-U1, M^c, LIFT-1 (with (L2′) and case (b)), D1-C, MAX₃/RED₃, SD-E and REC-S all CORRECT.
  K4.SDC.OC1PMAX CONFIRMED by a third implementation. ksens's k = 3 exhaustive one-chain claim CONFIRMED.
- Hall: the open core is updated (§23.4). Item 4 is OC2-REC, certified at n = 4 and holding at idx 164. S2 is refuted
  (S2-X, from k4-d1).
- d1: S2-X; D1-H2 holds on 3,711 starts. Theorem D1-C is refereed CORRECT.
- Haxell:
  - REFUTED at n = 4 (k = 4 cores, strict values): W^sub with welfare (WS4) and W^sub with leximin (LS4).
  - Theorem N2 (n = 2, computational, two implementations): two set moves or one Pareto swap.
  - P^sub (Pareto) holds exhaustively at n = 3 for k ≤ 3. The candidate is now P^sub₃ (three moves).
- VM: VM1 fails on the n = 4 core P34 (m = 7). VM1-chain holds on every failing profile so far; the pure list is
  finishing.
- ksens:
  - k = 5: one move fails already at n = 3 (N3K5). Two moves are certified on all 617 n = 3 hypergraphs with ≤ 5 goods
    per agent, and on the RD5, kgen-n4, PW5 and extended hypergraphs.
  - k = 6 needs exact-LP realizability (being built).
- k3-oc1 and kgen-n3 (k = 3, statement (P)):
  - (P) is exhaustive at n = 5, with and without a dead good.
  - REFUTED at n = 7: the release bound (R), every-k T-E, and T′_k. The surviving forms are T-E∃ and T-ω.
  - Lemmas 4–7, G5 and G5′ are written and queued for the referee.
- monotone: 4 ≤ k* ≤ 8 proved. No monotone counterexample at k = 4 with n ≤ 5 (CERTIFIED, so TARGET₄ for n ≤ 5 by an
  independent method), nor at k ≤ 6 with n = 3.
- twins: K4.MC8 removes 36–40% of the β = 5 minimal-counterexample candidates at n = 6–10; about 500k remain.
- Lean (#109, CI pending): Lemma M, LIFT-1 and T6 are machine-checked; a second structural refutation via T6.

**Merged into main this hour:** #95 (coordinator, integrating #94, #103, #108, #109, #110, #111, #115 at their then
heads), #110 (paper r4), #108 (referee), #114 (certifier, n ≤ 4), #100 (Hall). #109, #111 and #115 are waiting on CI
at their new heads.

**New strategic idea, dispatched to matching, multi and charity: RSD, recursive settle-and-delete.**
- The step: settle a sharer by E(k) and T, delete k and T (SD-E keeps an SD start), and recurse.
- The lift needs k unthreatened, so the inductive statement must carry "phantom" agents: fixed bundles that must stay
  unthreatened.
- If a phantom class closed under the recursion exists, OC₂^max (indeed TARGET₄) follows by induction on n, with no
  bound on the number of moves.
- A side remark: only k's two goods outside T can threaten it, so (K) is a local "keep b and c apart" condition.

**Own angle: hunting for a start that needs three moves** (`k4/sdc/three_move_hunt.py`).
- Each of the 12 two-move seeds (the 11 n = 4 cores and idx 164) is extended by 1–2 random agents that value the seed's
  goods, so that they are not free sinks.
- Every maximum-matching start is classified by the least number of sequential moves, with a numpy exhaustive
  one-absorber completion test.
- A trial of 40: random extensions mostly dissolve the obstruction (0 or 1 moves). Larger runs are in progress.

### 2026-11-27 02:44 UTC: hourly burst 6
**Status.** TARGET₄ is open. OC₂^max (≤ 2 sequential moves) survives everything: it is certified at n ≤ 4, and certified
at n = 5 on 2,670 cores (5_n4_1 and 935 of 4,674 5_pure), with no start needing three moves. Of the uniform repair
mechanisms, only **ROUND-P** (one round of vertex-disjoint OC₁′ moves) survives all data.

**This hour's hard data at n = 5.** The certifier's first 5_pure chunk stores 280 two-move starts.
- **REC-S existence gaps:** 7 starts (kgen-rounds, with multi's own code).
  - The coordinator replayed #773, #963 and #38 (`k4/sdc/recs_gap_check.py`, log): each is hard, needs 2 moves, and
    ROUND-P repairs it.
- **RSD** (settle-delete-recurse with |T| ≤ 3; matching, `check_rsd.py`) repairs 278 of 280.
- **RSD-IND REFUTED.** At 5_pure (m = 10) #419 and (m = 11) #447 no RSD sequence of any depth works. Three independent
  checks agree (matching ×2 and multi). The obstruction is two sharers whose settlements each threaten an agent that
  only the other chain improves.
  - The coordinator replayed #419 (`results/k4_sdc/n5_419_replay.log`): strict core, OC₁ fails, 2 moves. ROUND-P
    repairs it with two disjoint rings, 0 ↔ 4 (agent 0 takes {0,7}) and 1 ↔ 3 (agent 1 takes {1,8,9}).
  - The referee also showed RSD-IND is false as written even at n = 4: dead ends are reachable from 16,240 of 112,880
    starts.
- **ROUND-P** repairs all 280 (matching, with `k4/sdc/roundp_check.py` unmodified): 234 with one move, 46 with a round
  of two.

**Refereed this hour.**
- **Lemma LIFT\* and Lemma PHANTOM: CORRECT.** So TARGET₄ follows from the existential RSD statement ("some step
  sequence ends in a completion"). An induction needs an invariant that excludes dead ends.
- K4.MATCH.RSD.N4 CONFIRMED (all 112,880).
- Lemma WG CORRECT. K-loc WRONG as stated, corrected. Phantom class GAP, fixed.
- The splice sketch (REC-S ⟹ one round) has a GAP: the case where P₂'s head is x₁ and Y_k leaks (71 random
  configurations, all with other ROUND-P witnesses).
- Also refereed CORRECT: k3-oc1 Lemmas 4–7, kgen-n3 G5/G5′, Haxell N2's type reduction, the twins prune. Confirmed:
  R2-M's refutation (all 306), N3K5, P34.

**Other results.**
- multi: Theorem S^φ (Theorem S with phantoms; written, exact on the data).
- TTC: R2-E REFUTED at n = 4 (4_n4_3 #77: one cycle serves both dangerous agents). R2-C certified.
- charity: P1 fails at n = 3, k = 5 (brute force). The cvc5 and MILP re-check pipeline for UNSAT claims is in place.
- kgen-n3: Proposition A (k = 3, one terminal; covers 113,736 of 122,680 drafts).
- Haxell: no third-move failure at n = 5 yet; a fifth agent gives an outlet.

**Merged this burst:** #123 (Lean: SD-E and the REC-S frame) and #127 (the K4.HX ledger rows). Earlier this hour:
#98, #101, #105, #106, #115, #117, #118, #119, #121, #122.

**Dispatch.**
- matching: ROUND-RSD, i.e. a round of simultaneous settlements, delete all, recurse; then the base-case census.
- multi: SD-E and S^φ for a round of settlements.
- kgen-rounds: a direct ROUND-P proof sketch (item 4a).
- TTC: are R2-C repairs ROUND-P witnesses?
- referee: S^φ next.
- paper: r6 material.
- Lean: Theorem U.

**Own angle.** The replays above, plus a question for ROUND-RSD.
- At #419 the two settling chains are vertex-disjoint and their absorbed sets threaten each other's "victims". So a round
  of settlements needs (L*) only at the end of the round, which is exactly ROUND-P's witness.
- Conjecture for the next test: every RSD dead end and every RSD-X start is repaired by settling all agents of one
  "threat component" in one round. The threat component is the agents linked by "my absorbed set threatens an agent your
  chain improves".

- 03:29 UTC: spawned **base-phantom** (session_01BYMGebS9uNs3yyqMaMxxm7, branch proof/k4-base-phantom). Its task is the base case of ROUND-RSD: OC₁ with phantom constraints at the 6 + 35 + T3 + RING2 starts where reduction fails. The d1 session, whose work is complete (PR #113), handed over its tools.

### 2026-11-27 03:37 UTC: hourly burst 7
**Headline: Conjecture RF (receiver first)** (ledger K4.SDC.RF, `k4/sdc.md` §31 end).
- At a maximum-matching start where OC₁ fails, put the start's unique receiver first. Every resulting maximum-matching
  order satisfies OC₁.
- The coordinator checked it independently:
  - all 112,880 n = 4 OC₁^max-failing starts, which with the certifier's certificate certifies it at n = 4;
  - all 280 stored n = 5 starts.
- RF ⟹ OC₁^∃max ⟹ TARGET₄, and the second implication is already in Lean.
- So the one-move, order-choosing route now has a concrete rule. Its source is the certifier's good-order export: rule
  (b), plus (a) "≥ 2 receivers ⟹ good" and (c) "the nearest good vector differs in two agents".
- OC₁^∃max itself is certified on all 935 cores of the first n = 5 chunk (certifier, with an independent check).

**Main route ROUND-RSD.** All of its tools are now refereed: SD-E(round), (L*) at the round's end, LIFT* for rounds,
PHANTOM, S^φ(round). In Lean so far: PHANTOM, LIFT* and SD-E(round) (#136), and Theorem U (#133).
- Open: ROUND-IND, which is existential because greedy rounds hit dead ends from 16,240 n = 4 starts.
- Open: the base case, OC₁ with phantoms. It is needed at 35 of 8,539 hard one-move starts, and at 6 even with
  relaxations. A new session, base-phantom, owns it.

**ROUND-P side (kgen-rounds).**
- Lemmas PG, GAIN, RING, RHO and FIX and Theorem ROUND-SIMPLE are refereed CORRECT. This gives SIMPLE-MD ⟹ ROUND-P; the
  converse is still open.
- Lemma SPLICE: CORRECT with fixes.
- Φ-MAX would give ROUND-P^max ⟺ MD, a characterization. UNTANGLE is in progress: no single swap rule is complete, so
  it needs a local search with potential Φ.

**Others.**
- VM: VM1-chain is CERTIFIED for n ≤ 4 (two implementations). VM1 holds on all 304 n = 5 OC₁^max-failure profiles, so
  the SD and V-M starts are complementary.
- twins: K4.MC9 cuts the β = 5 candidates to 320,348.
- d1: done (PR #113); D1-H2 is certified on the 3-agent and t = 2 4-agent cores.
- monotone: k = 5 needs ≥ 5 agents. The n = 6, k = 4 run needs a larger machine (250–480 CPU-h) and is on hold.

**Merged this hour:** #99, #106, #123, #127, #128, #130, #131, #132, #133 and #136.

**Dispatch.**
- girth: prove RF, or rules (b)/(c), from the export.
- TTC: (ii), "a failing maximum-matching start forces a ≥ 2-receiver maximum-matching outcome".
- certifier: check RF on every failing pair met in the n = 5 runs.
- Lean: the ROUND-RSD frame.

### 2026-11-27 04:37 UTC: hourly burst 8
**State of TARGET₄: open, with two fully specified routes, each with its final implication machine-checked in Lean.**
1. **RF (receiver first)** ⟹ OC₁^∃max ⟹ TARGET₄. Lean: `target4_of_conjRF` (#143, merged); the frame never uses
   receiver uniqueness.
   - Structural half PROVED and refereed, for any n: Lemma RF-PATH. Moving any receiver u to the front changes the SD
     picks along one ejection path; ejected agents strictly lose; the end d is unfrozen. Also TTC's Lemma RF-ROT: the
     last picker is always a receiver.
   - Completion half OPEN: girth's uniform statement. At the RF start, one of:
     - (i) w or d owns a one-absorber completion;
     - (T) a receiver and a pick-dangerous agent trade;
     - (C/C′) a two-agent chain from a truly dangerous agent repairs.
   - It holds at all 292,080 n = 4 failing orders, all 86 stored n = 5 orders, and the 64 two-receiver starts.
   - Hall: sub-case A1 (32,000 n = 4 starts) is proved, conditional on four facts that hold at all of them. The open
     sub-cases are A2 and B (w = d).
   - Evidence for RF itself: certified at n = 4 (two independent implementations); n = 5 holds at every failing pair
     the certifier's CEGAR met in chunks 1–2.
   - R2 is REFUTED at n = 5 (two-receiver failures 5_pure #650, #655, #1014, #1050; three independent replays: certifier,
     coordinator, TTC). So RF was amended to "some receiver"; at #650 one receiver's per-order RF picks are not maximum.
2. **ROUND-RSD** (settle a round, delete, recurse). Lean: `target4_of_roundRSD` from ConjRoundInd ∧ ConjBasePhi (#141).
   - Every tool is refereed. Certified at n = 4, on the 280 stored n = 5 starts, and on all 583,680 two-move starts of
     the adversarial cores #419, #447 and #38.
   - Open: ROUND-IND (existential; greedy rounds dead-end) and the base case (base-phantom session).

**Also this hour.**
- Lean: Theorem U, Theorem S (#142, pending merge), PHANTOM / LIFT* / SD-E(round), and both frames.
- OC₂^max certified on 3,605 n = 5 cores, with no three-move start.
- OC₁^∃max on chunk 1, with an independent check.
- Referee: SPLICE, the §4.11 lemmas, UNTANGLE's proved parts, S^φ(round), K4.MC9 and RF-PATH (both forms), all
  CORRECT (with fixes where noted).

**Merged this hour:** #102 (pending CI), #113, #133, #136, #137, #138, #140, #141, #143 and #144.

**Dispatch.**
- hunt: RF checks at n ≥ 6.
- Hall and girth: the RF completion half.
- Lean: Theorem S^φ.
- certifier: RF at every pair met in chunk 3.

### 2026-11-27 05:34 UTC: hourly burst 9
**Headline: Conjecture RKMAX (coordinator; ledger K4.SDC.RKMAX; `k4/sdc.md` §31 end).** OC₁ holds at every
maximum-matching SD vector whose rank signature σ = (#rank 1, …, #rank 4) is lexicographically maximal.
- n = 4: 111,600 of 111,600 profiles of the complete failure export. With the certifier's certificate, this is a
  certificate at n = 4 once a second implementation agrees (d1 asked).
- n = 5: 583,680 of 583,680 profiles of the complete lists of 5_pure #419, #447, #38, the hardest cores (RSD-IND and REC-S
  counterexamples). Leximin and minimum rank sum hold too. On the six partial lists it holds at all 700,500
  profiles; the σ-optimal picks complete outright at 99.6% of vectors.
- Why it matters: RKMAX ⟺ "every failing start has a σ-larger maximum-matching SD vector". The witness need not satisfy
  OC₁, so a proof needs a structural signature-raising step at a failing start, not RF's completion half.
- At every failing pair some receiver-first vector raises σ (112,880 of 112,880), so RKMAX is RF's potential form.
- New session **rkmax** (session_01BYMGeaZVABiazckLK4GK8q) owns the proof. Lean frame `target4_of_conjRKMAX` requested.

**RF route.**
- Certifier: RF holds EXHAUSTIVELY at all 583,680 failing pairs of the complete lists #419, #447, #38 (1,676,160
  receiver-first vectors). Chunk 2: OC₁^∃max on all 935 cores, and RF at all 484 failing pairs met.
- Girth: the SINK form of DEMOTE (one absorber a ∈ {w, d}, plus at most one other junk good). It holds with 0
  exceptions at all 161,520 n = 4 RF starts and on the full n = 5 classes DEMOTE-0, (1, 3) and DEMOTE-2. The referee
  classes it as a CONJECTURE whose proved instances are RF-A1, RF-B and RF-T.
- TTC (with girth): class (1, 3) by Lemma C13, a two-bin trade w ↔ d. Proved for every n given hypotheses (2)–(4),
  which hold at all 7,733 starts. Peer-checked by girth; sent to the referee. Open: deriving (2)–(4) from the class.
- k3-oc1 locates where the k = 3 template breaks, (DE-a): a b-holder threatened by junk {c, d}. It takes (1, 3) and
  DEMOTE-0's non-trade part together with TTC and girth.

**ROUND-RSD route.**
- GR (settle only P1-free agents until a final round or an ED repair) is never stuck on the complete n = 5 lists:
  K4.BASE.GR.SEL2 CERTIFIED with two implementations (base-phantom's and matching's K4.MATCH.GRX). It is also never
  stuck on all 1,285,930 export starts.
- So ROUND-IND becomes GR-IND, owned by base-phantom.
- PR #152: the BASE-R correction, K4.BASE.GRR REFUTED, K4.BASE.B3 PROVED (refereed, item 58).

**Referee.** Items 58–62:
- B3/B3′, RF-T/RF-T′, RF-B′ and kgen-n3's remaining lemmas (R, P, S, Corollary 3, G1–G7, Proposition A): all CORRECT.
- SINK: a conjecture.

**Correction (kgen-n3).** n = 3 at arbitrary k is NOT proved; the proved arbitrary-k base is n = 2 (Theorem 2). By
Proposition H, OC₁ at every k would imply three-agent EFX₀, which is CGM-hard.

**Merged this hour:** #148, #149. Pending green CI: #102, #129, #150, #152; #147 waits on a merge conflict.

**Dispatch.**
- Idle sessions given new tasks:
  - k3-oc1: the RF completion half on the k = 3 template;
  - multi: ROUND-IND, now GR-IND jointly with base-phantom;
  - TTC: the (1, 3) and DEMOTE-0 rules;
  - write-up: refresh the paper draft;
  - twins: reductions for a minimal RF counterexample, for the hunt;
  - d1: independent RF and RKMAX checkers at n = 4 and 5;
  - kgen-n3: RF and RKMAX at k = 5, 6.
- Hall and girth: their class tables at σ-maximal starts.

### 2026-11-27 06:34 UTC: hourly burst 10
**TARGET₄: still open.** The statements are sharper this hour, and three verified refutations bound the conjectures.

**RKMAX (K4.SDC.RKMAX).**
- CERTIFIED at n = 4 (K4.SDC.RKMAX.N4) and on 5_pure #419, #447, #38 (K4.SDC.RKMAX.SEL2). Two independent
  implementations (coordinator, referee) agree, and d1 and rkmax have third ones.
- No counterexample in 5.6M random strict n = 5 profiles (d1).
- REFUTED at k = 5 (K4.SDC.RKMAX.K5; ksens and kgen-n3, replayed). At n = 3 with a shared top pair, every SD vector has
  the same σ, so RKMAX becomes OC₁^max, which fails at k = 5. RKMAX is a k = 4 statement.
- Hall's plan (a), "σ-max ⟹ hard classes vanish", is refuted by 5_pure #358 (replayed). One-receiver σ-maximal starts
  exist but are rare: 1,822 in 5.6M profiles.
- rkmax session: Observation W (σ is the out-degree profile of the wants digraph); RKDOM (rank dominance); HS-MAX (at
  n = 4, every hard σ-optimum satisfies Theorem S/U's or RF-B's static hypotheses).

**RF.**
- The referee's Lemma REC-∃ (proved): with no receiver holding a pick, a pickless agent absorbs all junk. So every
  failing start has a receiver, and the data form of RF implies RF∃.
- The every-order form is REFUTED at k = 5, n = 4, through twins (K4.SDC.RF.K5EVERY; ksens, replayed): the
  receiver-first order swaps two identical agents. RF∃ survives and is the target.
- Rank rules cannot break the twin tie (RFσ, coordinator).
- RF CERTIFIED at n = 3, k = 5 (K4.KSENS.RF5). The certifier finds RF at all ~1.29M n = 5 export starts. d1 replicated
  it independently (1,285,930 starts).
- n = 5 DEMOTE-0 is fully covered by refereed pieces: RF-A1* (71,443), RF-T/T′ (242 trades), T* (32 rings), plus
  NA's at-once starts. Class (1, 3) is covered by C13, with fix (0).

**ROUND-RSD.**
- multi: every P1-free round is safe on 29.5M rounds, with one exception at 5_pure #963 (which sharer to settle).
- Lean (#151, merged): SEP, LIFT-SEP and the corrected BASE-R frame are machine-checked.

**General k.**
- Theorem 2, two agents at every k (#97, merged, all refereed).
- Sequential chains grow with k (K4.KSENS.CHAINS); rounds do not (RD², CONJECTURE). kgen-rounds now has RD² at n = 3,
  every k.

**Merged this hour:** #102, #129, #135, #151, #154, #157, #159, #160, #97.

**Dispatch.**
- TTC: a canonical RF∃ rule.
- matching: a hunt for k = 4 twin failures.
- k3-oc1: derive RF-A1*'s hypotheses from Y's failure.
- VM: the LP/duality view of RS.
- write-up: revision 8.
- kgen-rounds: RD².
- d1: climb on the one-receiver σ-optima, then n = 6.

### 2026-11-27 07:21 UTC: wind-down, and RF's every-order form refuted at k = 4
- **Wind-down.** At the user's request (usage), all child sessions were told to stop runs, commit and push, mark
  complete PRs ready, and stop. The hourly trigger now runs in single-session mode: merges plus one angle of the
  coordinator's own.
- **Merged during the wind-down:** #96, #116, #120, #124, #125, #126, #134, #147 (pending), #153, #155, #156, #161, #162,
  #163, #164, #165, #167, #168, #169, #170, #172, #175.
- **RF every-order form REFUTED at k = 4, n = 5** (d1's off-export walk, three checkers; coordinator replay
  `k4/sdc/rf_k4_settwin_cex.py`).
  - Instance: 5_pure #440. The unique receiver's first order swaps two set-twins (same goods, different values), and
    the swapped start fails too.
  - RF∃ (new row K4.SDC.RFEX) and Hall's RF-rot∃ hold there, and at all 244,995 off-export (start, receiver) pairs.
  - The k = 4 target is now RF∃ / RF-rot∃. That is what the Lean frame `target4_of_conjRFsome` (#147) and Hall's
    proof plan use.
- **Late results recorded from the sessions.**
  - rkmax: HS-MAX REFUTED at n = 4 by an adversarial climb (44 starts; RKMAX holds there); HS-MAX′ (SINK₁ form)
    survives; RKDOM certified at n ≤ 4.
  - girth: Lemma XD, the first trade-case fact derived from hardness. Referee: ORD and RF-T-A need "Y has exactly one
    receiver".
  - matching: no twin failure of RF∃ at k = 4 in its hunt; Conjecture TWIN-TOP.
  - k3-oc1: Theorem FAIL-STRUCT drafted (`k4/k3_oc1.md` §13.7, unchecked).

### 2026-11-27 08:34 UTC: burst 11 (single-session mode)
- **Wind-down finished.** All child sessions except hunt are archived. Hunt was interrupted at 08:35 so it can commit
  and stop.
- **Merged:** #171 (d1's off-export RF), #176 (Lean RKMAX frame), #177, #178 (Lean REC-∃ and `ConjRFex` ⟹ TARGET₄),
  #179 (TTC: Lemma PTR, RF-MAX, YRMH-F), #180 (carries #112 monotone and #173 base-phantom, with ledger conflicts
  resolved).
- **Closed as superseded:** #112, #147, #173.
- **Drafts left open:** #104 hunt, #107 p3, #158 rkmax, #166 kgen-rounds, #174 twins.
- **Lean correction (Lean session).** `ConjRF`, `ConjRFpick` and `ConjRFsome` all use `ReceiverFirst` (every u-first
  maximum order), so #440 refutes them. The live frame is `ConjRFex` (`target4_of_conjRFex`), with REC-∃ formalized
  (`oneAbsorber_of_noReceiver`).
- **Own angle.** TTC's canonical rule YRMH-F at #440 (`k4/sdc/rf_canon_440.py`): from all four orders giving the
  failing start it yields a receiver-first maximum matching whose picks complete. Plain rotation fails from one of
  them. So RF-canon survives the k = 4 counterexample to the every-form.

### 2026-11-27 09:34 UTC: burst 12 (single-session mode)
- Merged #181. Archived the hunt session (its work was pushed and #104 stays a draft). All child sessions are now
  archived.
- **Own angle: FAIL-STRUCT made precise and checked** (ledger K4.SDC.FAILSTRUCT0; `k4/sdc/failstruct_check.py`).
  - Every OC₁-failing maximum-matching start in all data has exactly one receiver and |D_T| ∈ {0, 2, 3}:
    - |D_T| = 0 ⟹ a dangerous agent and the receiver value each other's picks (S2);
    - |D_T| ≥ 2 ⟹ two truly dangerous agents compete for junk, i.e. their minimal threatening junk sets intersect
      (S1′).
  - Coverage: n = 4 complete (112,880), n = 5 complete lists (583,680), partial lists (702,250).
  - The draft's pair form fails at #447, where |D_T| = 3; the generalization S1′ is needed. The draft's S3 is never
    needed.

### 2026-11-27 10:34 UTC: burst 13 (single-session mode)
- Merged #182 (FAIL-STRUCT₀).
- **Own angle: FAIL-STRUCT₀ off the exports.** Run on d1's walk dump, 241,728 failing n = 5 starts on 277 cores.
  - The dichotomy holds at every one: |D_T| = 0 ⟹ pick swap (S2), 40,994 starts; |D_T| ∈ {2, 3} ⟹ competing junk
    (S1′), 200,734 starts.
  - 3,267 starts have two receivers, so the statement's copied clause "exactly one receiver" is dropped. It
    contradicted K4.SDC.R2.N5 and was my error in burst 12.

### 2026-11-27 11:34 UTC: burst 14 (single-session mode)
- Merged #183.
- Own angle (light): FAIL-STRUCT₀ at the named starts outside the exports (`k4/sdc/failstruct_extra.py`). The k = 5
  failing starts N3K5, n3_m6_93 and RF5, and the k = 4 set-twin start #440, all have |D_T| = 2 with competing junk
  (S1′).

### 2026-11-27 12:34 UTC: burst 15 (single-session mode)
- Merged #184.
- **Own angle: RF-canon off the exports** (`k4/sdc/rf_canon_offexport.py`, ledger K4.SDC.RFCANON). TTC's canonical rule
  YRMH-F gives a receiver-first maximum matching satisfying OC₁ at all 244,995 (start, receiver) pairs of d1's
  off-export walk (241,728 failing n = 5 starts), already from the first listed order. This includes the #440
  every-form failures and the 3,267 two-receiver starts.
- RF-canon is the sharpest surviving statement on the RF route: one explicit order per failing start.

### 2026-11-27 13:34 UTC: burst 16 (single-session mode)
- Merged #185.
- **Own angle: RF-canon by FAIL-STRUCT₀ case** (`k4/sdc/rf_canon_bycase.py`).
  - YRMH-F's outcome mostly completes at the picks (87–100% by case) and mostly has no truly dangerous agent (77%).
  - FAIL-STRUCT₀'s necessary shape is absent at only 33% of the outcomes. So FAIL-STRUCT₀ alone would settle
    RF-canon only there, and a proof needs a sufficient completion condition at Z.

### 2026-11-27 14:34 UTC: burst 17 (single-session mode)
- Merged #186.
- **Own angle: a sufficient condition at YRMH-F's outcome.** New Conjecture REC-LOW (`k4/sdc.md` §31, ledger
  K4.SDC.RECLOW): at every OC₁-failing maximum-matching start, every receiver holds its rank-3 or rank-4 good.
  - It holds on all data: the complete n = 4 export, the complete n = 5 lists, partial6, d1's off-export walk, and the
    named k = 4 and k = 5 failures (1.64 M failing starts in all). One implementation so far.
  - With REC-∃, OC₁ holds at any maximum-matching start with no receiver or a receiver at rank ≤ 2.
  - YRMH-F gives the receiver its top good, and 92% of YRMH-F outcomes escape REC-LOW's shape, against 33% for
    FAIL-STRUCT₀. The two shapes together leave 3.2%.
  - Side facts: at a completing Z some receiver absorbs, and a grab never repairs at Z.
- Next: prove REC-LOW at rank 1, or find its counterexample with random strict cores at n = 5, 6.

### 2026-11-27 15:34 UTC: burst 18 (single-session mode)
- Merged #187.
- **Own angle: try to break REC-LOW** (`k4/sdc/rec_low_rand.py`, `k4/sdc/rec_low_outcome.py`; ledger K4.SDC.RECLOW
  updated). No counterexample found.
  - 48,350 strict perturbations of known failing profiles give 900 failing maximum vectors. All have receivers at
    ranks 3 and 4 only, and all 258,695 escaping vectors satisfy OC₁.
  - Also tested: 20,000 random n = 5, 6 cores (no failures at all there) and B< and B>.
- On the complete n = 4 export no maximum vector has a rank-1 receiver. The escape side there is all rank 2: 800 of
  382,160 vectors need one move.
- The rank-1 case is not a static lemma, because a frozen threat can force a move. One shortcut I tried ("frozen agents
  never receive junk") is false, and I recorded why in `k4/sdc.md`.
- Next: the rank-2 one-move starts (800 at n = 4), to see which move REC-LOW's proof must supply.

### 2026-11-27 16:34 UTC: burst 19 (single-session mode)
- Merged #188.
- Own angle: the 800 rank-2 one-move starts of REC-LOW at n = 4 (`k4/sdc/rec_low_rank2_moves.py`). Every one is
  repaired by a 3- or 4-agent chain or ring through two dangerous agents that gives the receiver its top good. The
  plain swap never repairs.
- Paused for a strategy review at the user's request: this line repeats the pattern `k4/strategy.md` diagnosed
  (extremal start, improving move, counterexample, patch).

### 2026-11-27 17:10 UTC: direction change (prove or refute TARGET₄ itself)
- The user observed that the work was going in circles. Indeed, the conjecture–refute–loosen loop is the one
  `k4/strategy.md` diagnosed: 121 REFUTED and 77 CONJECTURE rows, while TARGET₄ itself has never failed. The user then
  asked to "keep on trying to prove target for or try to refute it". The hourly prompt is retargeted accordingly: no
  new rule- or potential-style conjectures. Track (B) searches for counterexamples to TARGET₄ itself with exact
  checks; track (A) gives proofs by certified checks (reducible configurations, certified ranges). The kill rule is 3
  bursts without an artifact.
- **Started: the n = 6 frontier with two 4-good agents.** `python3 k4/frontier/search.py 6 --n4=2 --tries=2 --jobs=4
  --out=results/k4_certs_6_n4_2.json.gz`, log `results/k4_search_6_n4_2.log`, 119,283 cores. It is the first class
  beyond the certified range (K4.R6a: n = 6 with one 4-good agent). Each core either gets a D2 certificate (checked
  later by `k4/check4_fast.py`) or yields a failing profile. A failing profile would then be tested for TARGET₄
  exactly, which is the refutation side.
  - Estimate: about 24 CPU-hours (`k4/frontier/README.md`), so about 6–8 h on 4 CPUs.
  - The checkpoint `k4/frontier/checkpoint_6_n4_2_all_p0of1.jsonl` is gitignored and lives in the container.

### 2026-11-27 17:34 UTC: burst 20 (track A/B: the n = 6, two-4-good-agent frontier)
- Merged #189.
- The frontier run started at 17:10 died with my turn after 6,925 cores (a `nohup` job does not outlive the turn here).
  I restarted it as a tracked background job; it resumes from the checkpoint. A git sync then unlinked the log file
  under the running process. The checkpoint, the authoritative record (7,216 cores, every line parses), was
  unaffected, so I restarted again, with the live log in the session scratchpad. It is copied into
  `results/k4_search_6_n4_2.log` at each burst.
- So far 0 D2 failures and 0 counterexamples.

### 2026-11-27 18:36 UTC: burst 21 (tracks A1, A3)
- A1: the n = 6, two-4-good-agent frontier is at 29099 / 119,283 cores (m ≤ 7 done, m = 8 in progress), with 0 D2
  failures and 0 counterexamples. Rate about 4 cores/s at m = 8, so roughly 8–12 h remain.
- **A3 dropped:** the ε bridge (`attempts/k4-eps-bridge.md`). The limit lemma "EFX for v^ε along ε → 0 ⟹ EFX₀" is
  proved and trivial. But v^ε is not 4-limited, so Theorem VM does not apply; the bridge only restates EFX₀.
  Smallest instance: V-M's (S3) n = 2, m = 3, with replay `attempts/k4_eps_bridge.py`.
- Next: A2, the β = 5 minimal-counterexample candidates (n ≤ 12 by K4.MC4).

### 2026-11-27 19:40 UTC: burst 22 (track A1)
- The n = 6, two-4-good-agent frontier job was stopped by the harness at its 2-hour background limit (19:35 UTC). It
  had done 43,370 / 119,283 cores: all of m = 4–8, and 4,571 of m = 9's 36,867. There were 0 D2 failures and 0
  counterexamples. The checkpoint parses completely.
- The harness asks not to restart a job that reached the longest allowed timeout. It is not restarted, pending the
  user's decision.
- Kept: a compact per-core summary (m, idx, sets, D2 failures, counterexample flag, number of allocations) in
  `results/k4_frontier_6_n4_2_partial_summary.jsonl.gz`. The full checkpoint (13.6 MB gzipped, with allocations) stays
  in the container, gitignored.
- A partial certificate for m ≤ 8 cannot pass `k4/check4_fast.py`, which requires completeness for every m. So no
  ledger row yet; this is EVIDENCE.

### 2026-11-27 20:40 UTC: burst 23 (track A2: size of the β = 5 candidate list)
- `k4/mincex_shapes.py 5 --nmax=7` was killed for lack of memory (16 GB). It keeps every listed candidate's type
  domains before removing isomorphic copies.
- New `k4/mincex_shapes_count.py` has the same generator, isomorphism test and K4.MC5 restriction, but streams. Log
  `results/k4_min_cex_count_5_n7.log`, 190 s.
  - Candidates left after K4.MC5 at β = 5: n = 5: 2,097; n = 6: 30,337; n = 7: 122,006, up to 1.6·10¹⁷ profiles per
    core.
  - K4.MC4 allows up to n = 12, and the list grows about 4× per n. Compare β = 4: 5,558 candidates in all, n ≤ 9.
  - The n = 5 candidates are already covered by K4.R3–K4.R5p (every n = 5 core).
- **Verdict:** certifying β = 5 directly is out of reach. The β sub-line of A2 can only continue through new
  reductions that cut the list by orders of magnitude, not through more certification. The 1,080 unreduced Q4-open px
  profiles are the natural first target.
- A1 is still stopped, pending the user's decision.

### 2026-11-27 21:40 UTC: burst 24 (track A2: what dominates the β = 5 list)
- `k4/mincex_shapes_count.py 5 --nmin=6 --nmax=7 --kinds` (log `results/k4_min_cex_kinds_5_n67.log`, 213 s).
  - The surviving candidates contain a P3 agent (3 goods, one private) in 25,985 of 30,337 at n = 6 (86%) and 117,390
    of 122,006 at n = 7 (96%).
  - Graphical candidates (no good of degree ≥ 3) number 685 at n = 6 and 3,874 at n = 7. These are covered by the
    multigraph theorem (ledger T3), as at β = 4.
- So the lever for β = 5 is a reduction for P3 agents. K4.MC3 and K4.MC5 only restrict P3 agents that share a degree-2
  good.
- What a P3 agent f = {p private, a, b} needs if it keeps {p} alone (balance gives v_f(p) < v_f(a) + v_f(b)):
  - a and b are not together in a bundle with a third good;
  - each of a and b is alone in its bundle or worth at most v_f(p) to f;
  - if {a, b} is a whole bundle, max(v_f(a), v_f(b)) ≤ v_f(p).

  A P3 reduction would be a gadget that forces this on the smaller instance, or one of f's other options ({p, a},
  {p, b}). The next step is to test such a gadget on the reduce4 machinery for one P3 neighbourhood type.
- Kill-rule count for the β = 5 sub-line: 2 bursts, no certified artifact yet.
- A1 is still stopped, pending the user's decision.

### 2026-11-27 22:40 UTC: burst 25 (track A2: a P3 reduction; β = 5 sub-line dropped)
- A lone P3 agent (S = {e} on (s, t, p), I = {p}, ∂ = {s, t}): `mincex4.explore` reports 6 of 6 profiles reduced by the
  one-agent gadget menu h on (s, t, z′). **This is not a valid reduction.** Lemma K4.MC1 needs H′ smaller
  (|S′| < |S|, or |S′| = |S| and |I′| < |I|), and h on (s, t, z′) has |S′| = 1 = |S|, |I′| = 1 = |I|. It just renames
  e. The smaller form, a gadget on the boundary goods only (|I′| = 0), is the recorded failure
  `attempts/k4-mincex-drop-private.md` (`k4/mincex_attempts.py drop-private`).
- So there is no P3 reduction of the simple kind. Without one the β = 5 list (about 1.5·10⁵ candidates by n = 7,
  growing toward n = 12) cannot be certified.
- **Kill rule: the β = 5 sub-line is dropped** after 3 bursts without a certified artifact. Its useful outputs are the
  streaming counter `k4/mincex_shapes_count.py` and the size and kind counts in `results/k4_min_cex_count_5_n7.log`
  and `results/k4_min_cex_kinds_5_n67.log`.
- **State of the proof tracks:**
  - A1 (n = 6, two 4-good agents) needs about 8–12 CPU-hours beyond the 2-hour job limit, pending the user's
    decision.
  - A2's named steps are out of reach: β = 5 is infeasible without a new idea, and the 6 graphical all-P4 cores
    take more than an hour each, single-core (already covered by the multigraph theorem).
  - A3 is dropped.
  - What remains needs a genuinely new mathematical idea, which hourly bursts have not produced.

### 2026-11-28 07:45 UTC: resumed in autonomous mode
- The user asked why nothing had happened since 22:40 UTC: I had turned the bursts into idle check-ins while waiting
  for their decision on A1. That was the wrong call, and it is fixed.
- The user then said "just work autonomously". The hourly prompt now runs a work queue without waiting:
  1. finish the n = 6 two-4-good frontier in 12 parts of under 2 h;
  2. check it, add ledger row K4.R6b and merge;
  3. move on to the next certifiable class (n = 6 with three 4-good agents, or n = 7 with one), estimated first;
  4. with spare CPU, one focused proof idea under the 3-burst kill rule.
- Part 0/12 started: 9,941 cores, 3,615 already in the checkpoint.
- 08:08 UTC: part 0/12 done in 1,474 s, giving 49,696 / 119,283 cores with 0 D2 failures and 0 counterexamples.
  Parts take about 25 min, so parts 1–4 now run back to back in one background job.
- 08:35 UTC: part 1/12 done and part 2 running. The checkpoints hold 56,375 / 119,283 cores, with 0 D2 failures and 0
  counterexamples.
- 09:35 UTC: parts 0–3 of 12 done and part 4 running: 71,070 / 119,283 cores, with 0 D2 failures and 0
  counterexamples.
- 10:35 UTC: n = 6 two-4-good frontier at 81327/119283 cores (parts 0–5 done), with 0 D2 failures and 0 counterexamples.
