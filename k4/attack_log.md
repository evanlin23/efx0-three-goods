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
| Induction on agents along the serial-dictatorship order (add the last agent, or remove the first / an unwanted one), with an invariant P found by computation | session_01BYMGecgCGycycqxiyS1n7G | `claude/k4-sd-induct` | `k4/sd_induct.md` |
| Housing markets / top trading cycles: SD picks as existing tenants, junk as the pool; find the TTC / YRMH-IGYT-type rule that picks the repairing chain, and core-type invariants | session_01BYMGeao2jUMkZBYQ48pDMw | `claude/k4-ttc` | `k4/ttc.md` |
| General k: bounded charity CH(k): partial EFX₀ with at most f(k) unenvied unallocated goods, f independent of n (relevant-goods analogue of the t − 2 bound for t types) | session_01BYMGeYiET7bXN43NsuXoDR | `claude/kgen-charity` | `kgen/charity.md` |
| The first open cell (k, p) = (4, 3) (≤ 3 valuers per good): a two-envier dump rule replacing the multigraph proofs' unique-envier step | session_01BYMGea7fswSChnvyCWWWm8 | `claude/k4-p3` | `k4/p3.md` |
| Choosing the order by an alternating-tree search with a lexicographic, non-value termination measure (Haxell; restricted Santa Claus) | session_01BYMGeYJ6PFyCSZHphgSyXd | `claude/k4-haxell` | `k4/haxell.md` |
| Referee: independent, adversarial review of every written proof the angles produce (Theorem VM first) | session_01BYMGeYHb8rxaaJ1BScSCZY | `claude/k4-referee` | `k4/referee/` |

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
  - Theorem R1C, written: OC₁ at k = 3 for every R1-compatible order.
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

### 2026-11-26 22:02 UTC: referee verdicts (claude/k4-referee, k4/referee/README.md)
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
