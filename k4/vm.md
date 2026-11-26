# From Viswanathan–Mehta's 4-limited EFX algorithm to EFX₀ (workstream proof/k4-vm)

Branch `claude/k4-vm`, draft PR "[proof/k4-vm] From 4-limited EFX to EFX₀". Code: `k4/vm/`; logs: `results/k4_vm/`.
Everything called evidence below is evidence only (PROMPT.md §5 rule 3). Nothing here changes a ledger row; the
coordinator integrates.

## Status (burst 4: repair classes, Lemma EXT, k = 5)

- **The referee** (via the coordinator) judged Lemmas SND, TERM, the invariant (I1)–(I5), P0, P1′ and Proposition HDT
  correct.
- **Repair classes** (§7.5). For each instance, the simplest repair needed at some V-M matching:

  | class | screen | named |
  |---|---|---|
  | HDT | 115 | 23 |
  | several absorbers | 20 | 70 |
  | unfreezing | 12 | 0 |
  | rotation (a ring) | 10 | 2 |
  | one move (a chain) | 11 | 0 |
  | **none** | **0** | **0** |

- **Lemma EXT** (proved): if the matching extends with an acyclic precedence digraph, F1 without rotation reaches the
  extension. Every extension-class instance on the data has such an extension (147/147, 93/93).
  - So in those classes the open steps are (E), that some V-M matching extends, and (A), that some extension is
    acyclic.
  - Also open: one ring suffices in the rotation class, and one chain in the one-move class.
- **VM1 at k = 5 survives everything tested:**
  - PW5 needs 1 move; RD5 and both kgen n = 4 instances need none;
  - 2,000 random 5-limited instances;
  - short climbs at n = 4, 5.

  OC₁ and OC₁^max fail on PW5 and RD5. VM1 is therefore a general-k candidate (evidence only).

## Status (burst 3: the coordinator's requests on VMX₂; bursts 2 and 1 below)

- **Request 1, named instances: no failure** (§7.2, `vmx2_named.log`). VMX₂ has an EFX₀ run on all 372 items, every
  output re-checked with an independent raw-EFX₀ checker. The items: B< and B> (the OC₁ counterexample core,
  n = 6), T3, Q2, r4253, r3943, `lb4-owner-needs-from-base-n4m8`, and the TTC session's 84 OC₁ counterexamples plus
  2 more, each also under 3 relabellings. The first DFS run already succeeds on every item.
- **Request 2, core-checked climbs (§7.2): no counterexample to VMX₂** at n = 4, 5, 6. That is 57,461 mutations,
  each kept only if `is_core4` passes. The success fraction is pushed down to 0.20 (n = 4), 0.125 (n = 5) and 0.675
  (n = 6), never to 0. The VMX₂ choices cover every order and tie rule the procedure has, and relabellings were run
  as well.
- **Request 3, invariant and proof target (§7.3).** The successful runs have a two-phase shape: moves first, then
  pure placement. More sharply:
  - **Conjecture VM1**: from some V-M matching, *at most one move* (a pool upgrade or an unrestricted two-agent
    exchange), then EFX₀-safe placements with rotation, complete to EFX₀.
  - Evidence: screen 168/168 (157 with no move), named 95/95 (all with no move), random cores n = 3–5
    2,700/2,700, general 3,000/3,000.
  - With *narrow* exchanges (the taker must value z) VM1 is **refuted** at n = 3, m = 7 and n = 4, m = 7
    (`attempts/k4-vm-vm1.md`, independent replay). One unrestricted exchange completes both.
  - Climbs against VM1 with unrestricted exchanges found no counterexample at n = 3, 4 or 5
    (`vm1f_climb{3,4,5}.log`). At the hardest profiles one move is needed, and a third (n = 3, 4) or two thirds
    (n = 5) of the one-move states complete.
  - The invariant (I1)–(I5), all proved: partial EFX₀; domination of the start; wanted goods held alone; bundles of
    two or more goods envied only by agents that value all of their goods; the potential rises.
  - **The unproved step is placeability.** From some V-M matching, after at most one move, the pool can be placed
    by safe placements with rotation. P1's state (GM4-E) shows that (I1), (I3), (I4) and "no pool good is wanted" do
    not imply it, so a proof must use V-M's saturation structure (Lemmas S and PO).

## Status (end of burst 2)

- **PROVED: Theorem VM (§8).** Viswanathan–Mehta's algorithm, as reconstructed (§2, main reading), returns a complete
  *ordinary* EFX allocation on every 4-limited instance, for every resolution of its choices.
  - The abstract's unproved step ("there will be a source in the EFX graph") is proved: the EFX graph is acyclic and
    its directed paths have at most two edges.
  - The literal text needs one correction (G1: remove only the *matched* Phase-I agents). Without it, it fails at
    n = 2, m = 2 (§4.2).
  - Written proof, not refereed. Every step is asserted on 253,151 runs by `vm_thm_check.py`.
- **EFX₀: where V-M breaks.** Exactly at the steps where the proof of Theorem VM dismisses non-valuers.
  - Three stages fail (§5): the rank-greedy matching (S1), Phase III's order (S2) and the EFX graph (S3).
  - The matching stage fails even for 3-limited instances (n = 3, m = 5). The cause is the upper-set trade that
    LB⁺'s upgrades perform, which a rank-greedy matching cannot express.
- **Repairs, killed or confirmed (§6, §7). Every refutation has an independent replay in `attempts/k4-vm-*.md`:**
  - **REFUTED**, each with its smallest instance:
    - Conjecture VC (F1–F3 + rotation complete V-M's matching whenever it extends). It held on 17,263 of 17,264
      instances; the exception has n = 4, m = 8.
    - F1 in an arbitrary order, even with distinct tops: n = 2, m = 5.
    - F5 (strip zero goods and refill): no better than F1–F3 + rotation.
    - Canonical SD starts: fair (leximin-rank) at n = 3, m = 5.
    - VMˣ from every SD outcome: n = 3, m = 5 (needs a three-agent cycle).
    - Every deterministic move rule, including the lookahead algorithm VM-LL: n = 2, m = 5.
    - **Conjecture VMX** (V-M, Phase III, then rotation, upgrades, exchanges and safe placements as choices; some
      run ends EFX₀). It held on all 9,678 instances of §6.4, but **hill-climbing refuted it** at n = 3, m = 6 and
      n = 4, m = 8. Phase III's early second goods block the exchange that a strongly-top agent must make.
  - **CONJECTURE VMX₂** (evidence only, §7.1): VMX without Phase III. Some run ends EFX₀ on every instance tested,
    including both VMX counterexamples, and the climbs that refuted VMX find no counterexample to it (lowest success
    fractions 1/2 at n = 3 and 2/3 at n = 4). VMX₂ ⟹ TARGET₄.
- **PROVED (§7):** Lemma SND (every state is partial EFX₀) and Lemma TERM (at most m placements and 15n moves per
  run). VMˣ and VMˣ₂ are sound nondeterministic procedures, polynomial per run.
  - The runs never lower a value, so P1 (K4.SDC.P1) is why the choice of path matters.
  - Hill-climbs find what random sampling misses: VMX survived 9,300 random instances and fell to a 64-start climb.
- **For the coordinator** (no ledger edits here):
  - proposed rows: Theorem VM (PROVED, written); VC, VMX, VM-LL (REFUTED); VMX₂ (CONJECTURE, evidence);
  - `proofs/citations.md` item 2 can now say that the abstract was re-read via pdftotext, and that its algorithm, with
    G1 corrected, has a complete proof here.

## Status (end of burst 1)

- **Source read in full.** The AAMAS 2024 extended abstract (3 pp.) was fetched from ifaamas.org and its text extracted
  with `pdftotext` (§1). It contains the algorithm in about 25 lines and no proofs.
- **Reconstruction** (§2) with twelve gaps (§3). The literal text has one slip: "Remove A from N^r" after Phase I
  must mean "remove the *matched* agents of A". Read literally, the algorithm is not even EFX at n = 2, m = 2 (§4.2).
- **Ordinary EFX (V-M's claim): supported.** Under the main reading (global ranks, matched Phase-I agents removed,
  N₁ ⊇ Phase-I agents), every resolution of every choice point gives an EFX allocation on all 18,336 instances
  tested. That covers the screen set, the suite, random strict profiles of the certified k = 4 cores with
  n = 3, 4, 5, and random general 4-limited instances with junk, top-heavy agents and ties. The EFX-graph source always
  exists, and the abstract's claim that only N₁ ∪ N₂ʳ value unassigned goods always holds (§4.1). Evidence only.
- **EFX₀: V-M fails at three stages** (§5). On the 168 screen instances:
  - (S1) the one-good matching of Phases I–II: on 21 instances *no* resolution of its choices extends to any EFX₀
    allocation (smallest n = 3, m = 5, checked by brute force: `attempts/k4-vm-skeleton.md`);
  - (S2) Phase III's matchings: 6 more instances have no state after them that extends;
  - (S3) the EFX-graph step: on 59 more, some state after Phase III extends but no run of V-M is EFX₀.

  Only 82 of the 168 have some EFX₀ run, and 24 have only EFX₀ runs. The smallest (S3) failure has n = 2, m = 3. A
  good valued by a single agent i must go to i under V-M's EFX graph, whose nodes are the good's valuers, and the
  other agent envies i's bundle (§5.3).
- **Structural facts proved here** (§2.1): Lemma S (saturation) and Lemma PO (every Phase I–II matching is a
  serial-dictatorship outcome, and Pareto-optimal among matchings). So (S1) says: the rank-greedy SD orders are not
  enough for SD-C (K4.SDC). It is the same phenomenon as `k4/sdc.md` §3, "not every order", now with a canonical
  family of orders.
- **Next (burst 2):** the EFX₀ repairs of §6, kill-or-confirm by computation:
  - F1: EFX₀ graph over all agents;
  - F2: EFX₀-safe Phase III;
  - F3: L3 junk;
  - F4: replace the rank-greedy matching by upper-set options or deferral.

## 1. The source

M. Viswanathan, R. Mehta, "On the existence of EFX under picky or non-differentiative agents", Proc. AAMAS 2024,
pp. 2534–2536, Extended Abstract, https://www.ifaamas.org/Proceedings/aamas2024/pdfs/p2534.pdf.
- How it was read: fetched on 2026-11-26 and converted with `pdftotext -layout`. All of it was read.
- License: the PDF states a Creative Commons Attribution 4.0 International License, so the quotations below are verbatim.
- Entry in `proofs/citations.md`: item 2 and the 2026-09 re-check. What it says agrees with what is read here.

Definitions (p. 2535), quoted:
- "an agent i EFX-envies an agent i′ if v_i(X_i) < v_i(X_i′ \ {j}) for some j ∈ X_i′ with v_i(j) > 0. A partial
  allocation X = (X_1, ... X_n) is EFX if no agent i EFX-envies another agent i′." Footnote 2 (p. 2534) describes the
  stronger notion, where "the removed good may be trivial for agent i".
- "[l-limited] We say that a valuation function v_i is l-limited if |{j ∈ M | v_i(j) > 0}| ≤ l."
- "kth Value Graph. Given a subset S ⊆ N of agents and T ⊆ M of objects, the kth value graph denoted by G_k(S, T) is
  defined as the bipartite graph with vertices S ∪ T and an edge between i ∈ S and j ∈ T if and only if j is the kth
  highest ranked object for agent i."
- "EFX Graph. For good j ∈ M, set S ⊆ N of agents, and partial allocation X, define the EFX graph G_efx(j, S, X) as
  follows: it is a directed graph with nodes for each i ∈ S with v_i(j) > 0, and an edge from i → i′ ⟺
  v_i(X_i) < v_i((X_i′ ∪ {j}) \ {j′}) for some j′ ∈ (X_i′ ∪ {j}) s.t. v_i(j′) > 0."

The algorithm (p. 2535), quoted in full:
> We initialize remaining agents N^r = N, remaining objects M^r = M, and the current partial allocation X to be such
> that no object is assigned yet. The algorithm runs in phases. In phase I, we define a subset of agents, A, that
> strongly prefer their highest ranked object, i.e. value their highest ranked object more than their second and third
> highest ranked objects combined. We assign a 1st choice object to as many agents in A as possible using a maximum
> matching in the 1st value graph on A and all objects, namely G_1(A, M^r). Remove A from N^r and the assigned objects
> from M^r.
>
> In phase II, we assign at most one object to every agent that doesn't have an object, in the best way possible. We
> run the maximum matching algorithm 4 times in sequence. For k = 1, 2, 3, 4, find a maximum matching M_k in graph
> G_k(N^r, M^r). For (i, j) ∈ M_k, assign object j to agent i, and remove the agents and objects in the matching from
> N^r and M^r. Let N_k denote agents with their kth ranked object. Agents in N^r received nothing, while the others
> received exactly one item. Thus this partial allocation is EFX.
>
> In phase III, we look at agents, starting with those that have low-ranked objects. Note that all the objects valued
> by an i ∈ N_4 ∪ N^r have been assigned, and therefore i is taken care of in the sense that i will not EFX-envy any
> agent no matter how the allocation is extended. We then assign a 4th choice object to as many of the agents in N_3 as
> possible. To assign a second object to as many of the agents in N_2 as possible, we first assign a 3rd choice object
> to as many agents in N_2 as possible and then assign a 4th choice object to as many of the agents in N_2 who have
> only one object, as possible. We call the set of agents in N_2 with their 3rd choice, N_2^r. Now, the only agents
> that may have valued objects not yet assigned are in N_1 and N_2^r. At this stage, we are able to prove that for
> every unassigned object j valued by someone, there will be a source in the EFX graph G_efx(j, N_1 ∪ N_2^r, X) where
> X is the current partial allocation. Assigning j to that source ensures that the partial allocation stays EFX.
> Finally, we assign remaining objects, which must be valued zero by all agents, to an arbitrary agent.

Example 2.1 of the text (three agents, four objects) is an EFX graph without a source. It is not a state the algorithm
reaches. `k4/vm/vmlib.py` reproduces it: with the partial allocation A ↦ a, B ↦ b, C ↦ c the EFX graph for d has the
edges A→C, B→A, B→C, C→A, C→B.

## 2. Reconstruction (algorithm VM)

Fix, for each agent i, a ranking r_i(1) > r_i(2) > ... of R_i = {g : v_i(g) > 0} (|R_i| ≤ 4) by value, ties by good
index. G_k(S, T) has the edge (i, r_i(k)) whenever r_i(k) ∈ T. **Each agent has at most one edge**, so a maximum
matching of G_k gives each good that is someone's k-th choice to one of its claimants. *Which* claimant is the only
freedom.

1. **Phase I.** A = {i : v_i(r_i(1)) > v_i(r_i(2)) + v_i(r_i(3))} (missing goods count 0). Each good that is the top
   of some agent of A goes to one of them. The matched agents leave N^r (reading `aout=matched`, see G1).
2. **Phase II.** For k = 1, 2, 3, 4: each good of M^r that is r_i(k) for some i ∈ N^r goes to one such i, and the
   matched agents leave N^r. N_k = agents matched at step k. The Phase-I agents are counted in N₁ for the EFX graph
   (G2).
3. **Phase III.** In this order:
   - each N₃ agent may get its 4th choice;
   - each N₂ agent may get its 3rd choice; those that do form N₂ʳ;
   - each remaining N₂ agent may get its 4th choice.

   Each step is a maximum matching of the same kind.
4. **EFX-graph step.** While some unassigned good j is valued by someone: build G_efx(j, S, X) with
   S = N₁ ∪ N₂ʳ ∪ (Phase-I agents), give j to a source, and repeat.
   - The order of the goods is a choice point.
   - So is the source, when there are several.
5. **Junk.** The goods valued by nobody go to one arbitrary agent (choice point). For EFX₀ we use L3 instead: rotate
   envy cycles away, then give all junk to an unenvied agent. That is harmless for EFX and EFX₀ alike.

`k4/vm/vmlib.py` implements this with every choice point exposed. `all_runs` enumerates every resolution of them by
DFS; past a cap it samples random ones.

### 2.1 Two facts about Phases I–II (proved; main reading)

Write st(i) = 0 for Phase-I winners, st(i) = k for i ∈ N_k, st(i) = ∞ for the agents left in N^r.

**Lemma S (saturation).** After step k of Phase II, every agent i still in N^r has r_i(1), ..., r_i(k) assigned.
Consequently:
- every good valued by an agent of N₄ ∪ N^r is assigned after Phase II;
- for i ∈ N_k, the goods r_i(j) with j < k were assigned to agents with st ≤ j.

*Proof.* At step j, the agent i ∈ N^r has the edge to r_i(j) if that good is unassigned. Every good with an edge is
matched, so r_i(j) is assigned by the end of step j, to an agent with st ≤ j. ∎

**Lemma PO.** The Phase I–II matching Y is the outcome of serial dictatorship for the order "Phase-I winners, N₁, N₂,
N₃, N₄, rest" (any order inside each group). It is Pareto-optimal among one-good matchings, and no agent prefers an
unassigned good to Y_i.

*Proof.* In that order, each agent's favourite remaining good is its own Y_i, by Lemma S and because the goods taken
within a step are distinct. For Pareto-optimality: if i prefers a good g to Y_i, then g = r_i(j) with j < st(i), and
by Lemma S its holder h has st(h) ≤ j < st(i). An improving trading cycle would therefore strictly decrease st all the
way around, which is impossible. No unassigned good is preferred, again by Lemma S. ∎

So V-M's matchings are SD outcomes of the *rank-greedy* orders. Pareto-optimality also follows from Lemma SDPO
(K4.SDC.SDPO, `k4/sdc.md` §28: SD outcomes are exactly the Pareto-optimal matchings); the direct proof above shows
which agents block which. Lemma 1 of `k4/sdc.md` makes "some EFX₀ allocation extends Y" the SD-C completion question
for these orders.

## 3. Gaps of the sketch, and the readings tested

| # | gap | readings implemented |
|---|---|---|
| G1 | "Remove A from N^r": all of A, or the matched agents? | `aout=all` (literal) / `aout=matched` |
| G2 | Do the Phase-I agents belong to N₁ (the EFX graph's node set)? | `n1a=Y` / `n1a=N` |
| G3 | "kth highest ranked": in all of R_i, or among the goods still available? | `rank=G` / `rank=R` |
| G4 | ties in values (rankings) | index tie-break; instances with ties tested |
| G5 | which claimant wins a contested good in each matching | choice point |
| G6 | which N₃/N₂ agents get Phase III goods when contested | choice point |
| G7 | order of the unassigned valued goods in the EFX-graph step | choice point |
| G8 | which source receives the good | choice point |
| G9 | the source claim itself ("we are able to prove") | checked on every run (a run with no source is "stuck") |
| G10 | is i′ = i allowed in the EFX graph? | no (no self-loops) |
| G11 | agents with fewer than 4 (or no) relevant goods | missing ranks have no edges; "third" counts 0 in Phase I |
| G12 | the "arbitrary agent" for junk | choice point (`junk=any`) or L3 (`junk=L3`) |

The **main reading** is rank=G, aout=matched, n1a=Y. Lemma S and the abstract's sentence "all the objects valued by
an i ∈ N_4 ∪ N^r have been assigned" need rank=G. Under aout=all, unmatched A-agents are in no N_k and would value
unassigned goods, contradicting "the only agents that may have valued objects not yet assigned are in N_1 and N_2^r".
Under n1a=N, the goods valued only by Phase-I agents have no EFX-graph node. Every reading was tested anyway (§4.2).

## 4. Ordinary EFX

### 4.1 The main reading: no failure

`python3 k4/vm/vm_test.py SOURCE` runs every resolution of the choice points (DFS up to 2,000 runs per instance, then
200 random ones). It checks every output against ordinary EFX and EFX₀ from the raw definitions (`efx_violations`).

| source | instances | runs | runs stuck (no source) | runs not EFX | log |
|---|---|---|---|---|---|
| screen set (`k4/de4/ss_screen.py`: GM4, A131, B131, C127, D3, suite n ≤ 5) | 168 (all exhaustive) | 11,146 | 0 | 0 | `vm_screen_all.log` |
| suite `k4/suite/instances` (n ≤ 26) | 164 (156 exhaustive) | 31,081 | 0 | 0 | `vm_suite_main.log` |
| nof_var.SPECIAL (T3, Q2, r4253, r3943) | 4 | 65 | 0 | 0 | `vm_special_all.log` |
| hard profiles printed in `results/k4_sdc/*.log` | 42 | | 0 | 0 | `vm_logs_all.log` |
| random strict profiles of certified k = 4 cores, n = 3 / 4 / 5 | 3,000 / 3,000 / 2,000 | 267,668 / 732,434 / 578,705 | 0 | 0 | `vm_cores{3,4,5}_main.log` |
| random general 4-limited (n ≤ 6, m ≤ 10, junk, top-heavy, ≤ 2-good agents) | 5,000 + 3,000 | 136,369 + | 0 | 0 | `vm_gen_main.log`, `vm_gen_all.log` |
| the same with ties (values in 1..4) | 5,000 | 125,879 | 0 | 0 | `vm_gen_ties_main.log` |

The abstract's claim that only N₁ ∪ N₂ʳ value unassigned goods held in every run (`runs claim_outside 0`). This is
evidence for V-M's theorem under the main reading, nothing more.

### 4.2 The other readings fail

On `gen` (3,000 instances, `vm_gen_all.log`):

| reading | instances with a non-EFX run | instances with a stuck run |
|---|---|---|
| G, matched, N | 0 | 1,086 (goods only Phase-I agents value) |
| G, all, Y (literal) | 252 | 214 |
| G, all, N | 81 | 1,164 |
| R, \*, \* | 448 to 724 | 293 to 1,388 |

**Smallest failure of the literal text** (`vm_smallest_gen.log`, `gen:1000`): n = 2, m = 2. Agent 0 values goods 0
and 1 at 13 and 8, agent 1 at 7 and 2. Both strictly prefer good 0 by more than their second good, so both are in A.
Phase I gives good 0 to one agent, and "Remove A from N^r" drops the other. Good 1 then goes to the winner, the only
EFX-graph node valuing it. The loser, holding nothing, EFX-envies a two-good bundle.
- Reproduce: `python3 k4/vm/vm_smallest.py gen:20000:7:3:6`.
- With aout=matched, the loser takes the other good in Phase II.

This is a slip in a 3-page abstract, not evidence against the theorem.

## 5. EFX₀: where V-M fails

### 5.1 Outputs

Main reading, every run (`vm_*_main.log`):

| source | instances with some EFX₀ run | instances with only EFX₀ runs |
|---|---|---|
| screen set | 82 / 168 | 24 |
| suite | 89 / 164 | 24 |
| cores n = 3 | 2,904 / 3,000 | 1,389 |
| cores n = 4 | 2,778 / 3,000 | 1,019 |
| cores n = 5 | 1,764 / 2,000 | 439 |
| general | 4,438 / 5,000 | 2,870 |
| general with ties | 4,650 / 5,000 | 2,977 |

Every EFX₀ violation in an EFX output is a *zero-good* violation: an agent i envies a bundle X_j with |X_j| ≥ 2 that
contains a good worth 0 to i. The logs classify them by (envier's group, holder's group, the step that placed the zero
good).
- On the screen set the top classes are the EFX-graph step (III.efx) placing a good into the bundle of a Phase-I
  agent (A) or of an N₁ agent. That good is worthless to an agent of N₂, N₂ʳ, N₃, N₄ or N^r that envies the holder's
  single top.
- Next come Phase III's 3rd-choice matching for N₂ (III.2-3) and the 4th-choice matchings.

This is the mechanism the abstract relies on for ordinary EFX: "i will not EFX-envy any agent no matter how the
allocation is extended" holds because later goods are worthless to i. Under EFX₀ that is exactly what hurts.

### 5.2 Stage analysis

`python3 k4/vm/vm_extend.py SOURCE --stop=II|IIIm` takes every state V-M can reach after Phase II (the matching) or
after Phase III's matchings. For each it SAT-checks, with `k4/sdc/sdclib.Enc` (the exact EFX₀ encoding), whether some
complete EFX₀ allocation contains it.

| source | instances | some matching (after II) extends | some state after III's matchings extends | some V-M run EFX₀ |
|---|---|---|---|---|
| screen | 168 | 147 | 141 | 82 |
| suite | 164 | 143 | | 89 |
| general n = 3, m ≤ 6 (20,000) | 20,000 | 19,944 | | |
| general n = 2, m ≤ 6, ties (20,000) | 20,000 | 20,000 | | |

So the three stages lose:
- (S1) the matching: 21 screen instances;
- (S2) Phase III's matchings: 6;
- (S3) the EFX-graph step: 59.

Every instance has an EFX₀ allocation (the SAT check agrees).

### 5.3 The smallest failures

- **(S3), n = 2, m = 3** (`vm_smallest_gen.log`, `gen:11350`). Agent 0 values good 0 at 19 and good 1 at 14; agent 1
  values good 0 at 17 and good 2 at 7. Both are in A with top 0.
  - Say agent 0 wins good 0. Agent 1 takes good 2 in Phase II. Good 1 is valued only by agent 0, so it is the only
    node of the EFX graph and gets good 1: X = ({0, 1}, {2}). Agent 1 envies {0, 1} (17 > 7), and good 1 is
    worthless to it.
  - Symmetrically if agent 1 wins.
  - EFX₀ allocation: ({0}, {1, 2}). The good valued by one agent must go to the *other* agent, who is unenvied, and
    V-M's EFX graph never considers a non-valuer.
- **(S1), n = 3, m = 5** (`attempts/k4-vm-skeleton.md`, screen instance `c4-exposure-nonleader-n3m5`, k = 4 core).
  Agent 0 ranks 3 (8) > 1 (6) > 4 (4) > 0 (3), and 8 < 6 + 4, so it is not in A. Agents 1 and 2 both rank
  4 (4) > 3 (3) > 2 (2).
  - Step 1 of Phase II gives good 3 to agent 0: no other agent has it first.
  - Of the four EFX₀ allocations, none gives good 3 to agent 0. Agent 0 always gets {0, 1} (9 > 8) or {0, 1, 2}, and
    good 3 goes to agent 1 or 2.
  - The goods 0 and 1 are valued only by agent 0. They cannot join a bundle that agent 1 or 2 envies, and after the
    matching agent 1 or 2 (holding its 3rd choice, good 2) envies both other bundles.

  So at k = 4 an agent must sometimes refuse its uncontested top for an *upper set*, a pair worth more than the top.
  Ordinary EFX never needs this: there, good 0 or 1 in agent 0's bundle is invisible to agents 1 and 2.

## 6. EFX₀ repairs: what each one fixes (burst 2)

All repairs keep V-M's skeleton and change only the rule for where a good goes.
- **F1, the EFX₀ graph.** A pool good g may go to any agent s such that nobody EFX₀-envies X_s ∪ {g}. For a
  non-valuer i of g this means v_i(X_s) ≤ v_i(X_i); for a valuer, the threat with the minimum over all goods.
- **F2, EFX₀-safe Phase III.** A claimant gets its 3rd or 4th choice only if F1's test passes; otherwise the good
  waits for the F1 step.
- **F3:** junk by L3.
- **rot:** rotate envy cycles before every F1 placement (L3's rotation).
- **F5, the final exchange:** take V-M's EFX output and strip zero-valued goods out of envied bundles until it is
  EFX₀, then re-place them by F1 with rotation. This is the only repair whose steps can lower a value.
- **F6, upgrades.** An agent holding a single good y swaps it for a minimal set S ⊆ pool ∩ R_i with
  v_i(S) > v_i(y), if the state stays EFX₀; y returns to the pool.
- **F6x, exchanges.** F6 plus two-agent exchanges: i (holding a single y) takes {z} ∪ S, where z ∈ X_j and S ⊆ pool;
  j takes X_j − z + y. Both strictly gain, and the state stays EFX₀.

When moves are applied is a mode:
- choice: a move or a placement, at every step;
- eager: a move whenever one exists;
- stuck: moves only when the chosen good has no safe place.

Code: `vmlib.vm0_run` (F1–F3, rot), `vm_strip_run` (F5), `vm6_run` (F6), `vm6x_run` (F6x). Drivers: `vm0_test.py`,
`vm_strip_test.py`, `vm6_test.py`; the S1 check is `vm_extend.py`. Every resolution of the choice points is
enumerated by DFS, up to a cap, then sampled.

### 6.1 F1–F3 and rotation: the completion works whenever V-M's matching extends

| source | instances | some V-M matching extends (S1) | F1–F3: some run EFX₀ | F1–F3+rot: some run EFX₀ | S1 passes but F1–F3+rot fails | log |
|---|---|---|---|---|---|---|
| screen | 168 | 147 | 146 | 154 | **0** | `vm0_screen.log` |
| logged hard profiles | 42 | 34 | 34 | 40 | **0** | `vm0_logs.log` |
| SPECIAL | 4 | 3 | 3 | 4 | **0** | `vm0_special.log` |
| cores n = 3 | 3,000 | 2,977 | 2,977 | 2,992 | **0** | `vm0_cores3.log` |
| cores n = 4 | 3,000 | 2,992 | 2,990 | 2,997 | **1** (`core4:1615`) | `vm0_cores4.log` |
| cores n = 5 | 1,000 | 996 | | 999 | **0** | `vm0_cores5.log` |
| general (n ≤ 6, m ≤ 10, junk) | 10,000 | 9,972 | 9,977 | 9,987 | **0** | `vm0_gen.log` |
| suite (n ≤ 26; DFS capped at 150 runs, then 30 samples) | 164 | 143 | 142 | 150 | **0** | `vm0_suite.log` |

- Without F2, the unfiltered Phase III loses 6 more screen instances (`nof2`).
- F1 alone (no rotation) misses one screen instance where S1 passes (`hall-local3`, n = 3, m = 7).
- Rotation also rescues some S1 failures, because it moves the matched goods: 7 of 21 on the screen set, 15 of 23 on
  cores n = 3.

**Conjecture VC (completion of V-M's matching): REFUTED** (`attempts/k4-vm-completion.md`). VC said: if some EFX₀
allocation contains a Phases I–II matching of V-M, then some run of F2, then F1 with rotation, then F3, from some V-M
matching, ends EFX₀. It held on every instance above except `core4:1615` (n = 4, m = 8, a random profile of a
certified core). There:
- the matching ({7}, {3}, {5}, {4}) extends;
- but V-M's Phase III serves N₃ before N₂ and hands good 6 to agent 2 as its 4th choice;
- both extensions need 6 with agent 1, as its 3rd choice;
- every sequence of safe placements then gets stuck, and no reachable state has an envy cycle (independent replay
  `attempts/k4_vm_completion.py`).

F6x (§6.2) completes it.

VC is specific to V-M's rank-greedy matchings. From an *arbitrary* SD outcome that extends, the same completion fails
on 24 outcomes of the screen set (GM4-A to -G and `gap-ivsetting-n3-m6-n3c23` among them; `vm0_sd_screen.log`).
Still, on all 168 screen instances *some* SD outcome completes this way.

### 6.2 Upgrades and exchanges: every screen instance

| repair (with rotation) | screen: some run EFX₀ | every run EFX₀ | instances with no EFX₀ run (smallest) |
|---|---|---|---|
| F1–F3 | 154 | 77 | 14, all S1 failures; `c4-exposure-nonleader-n3m5` (n = 3, m = 5) |
| F6 eager | 161 | 109 | 7; `lil-text-n3` (n = 3, m = 7) |
| F6 choice | 166 | | 2: `lil-text-n3`, `red-lil-nokeep-b` (n = 3, m = 7) |
| F6x stuck | 166 | 103 | 2: `c4min-tlam-n3-m6`, `c4x-n3m6-3good-first` (n = 3, m = 6) |
| F6x eager | 163 | | 5; `c4x-n3m8-pure-top7` (n = 3, m = 8) |
| **F6x choice** | **168** | 64 | **none** |
| F6x eager with lookahead (`x-eagerL`) | 168 | 141 | none, but its first run (all ties by index) fails on 4 |
| **VM-LL** (`x-eagerLL`: lookahead on moves and placements, fully deterministic) | 168 (first run) | 162 | none on these labels; **14 of 1,284 relabelled instances fail**, smallest n = 2, m = 5 |

Logs: `vm6_screen.log` (F6, F6x choice and stuck) and `vm6_screen_rules.log` (eager, eagerL, VM-LL). The other
sources are in §6.4.

What the moves do on the smallest failures, by brute force over all allocations (`k4/vm.md` §5.3 and
`attempts/k4-vm-deterministic.md`):
- **`c4-exposure-nonleader-n3m5` (S1).** Agent 0 must trade its uncontested top {3} (8) for its private pair {0, 1}
  (9). F6 does that as an upgrade from the pool. The freed good 3 then lets the holder of good 2 upgrade to {3}, and
  every F6-eager run ends EFX₀.
- **`lil-text-n3`.** Every EFX₀ allocation where agent 1 keeps its big top 5 gives agent 0 an upper set containing
  good 6, which V-M gave agent 2 at step 3. The repair is an *exchange*: agent 0 gives 4 to agent 2 and takes 6 and
  pool good 0. A pool-only upgrade cannot do it.
- **`c4min-tlam-n3-m6`** (lazy F6x fails). Agent 0 must swap its top {5} for {0, 1, 2} *before* the pool goods are
  placed. The lazy rule waits until a good is stuck, and by then goods 0 and 1 sit in agent 2's bundle.
- **`c4x-n3m8-pure-top7`** (eager F6x fails). Three agents with the same pattern (two private goods, shared 6 and 7).
  An early upgrade takes the private goods that a later placement needed.

**VM-LL is refuted as an algorithm** (`attempts/k4-vm-deterministic.md`, independent replay). It is deterministic,
polynomial and fast (at most 0.06 s per instance up to n = 5; 39 s for the largest suite instance, n = 26). It fails
at n = 2, m = 5 (`gen:5525`): agent 0 upgrades its top {4} to {0, 1}, after which goods 3 and 4 each fit with agent 1
but not both. The lookahead tests pool goods one at a time. Failure rates:
- 6 of 13,000 random core profiles with n = 3–5 (`vmll_cores.log`);
- 4 of 20,000 general instances (`vmll_gen.log`);
- 2 of 492 relabelled suite instances (`vmll_suite.log`);
- 14 of 1,284 relabelled screen, SPECIAL and logged instances (`vmll_screen_relabel.log`), and none on their original
  labels (`vmll_screen.log`).

So the moves are needed, *and* when to apply them matters: neither "always" nor "only when stuck" works, and a
one-good lookahead is not enough either. This is
P1's lesson (K4.SDC.P1) inside V-M's frame. Every step of F1–F6x is value-monotone (nobody loses), so a run can walk
into a stuck partial EFX₀ allocation, and only the choice of path avoids it.

### 6.3 F5 (strip and refill), canonical SD starts, arbitrary starts, and k = 3

All of these are refuted. The details, with independent replays, are in `attempts/k4-vm-orders.md`,
`attempts/k4-vm-every-start.md` and `attempts/k4-vm-skeleton.md`.

- **F5, strip and refill** (`vm_strip_screen.log`).
  - The only repair whose steps lower values. With rotation it succeeds on 154 of 168, no better than F1–F3 with
    rotation.
  - It fails on the same matching-stage instances, smallest n = 3, m = 5. Stripping removes harmful goods but never
    turns a top into an upper set.
- **Canonical SD outcomes** (`vm0_fair_screen.log`). The repair succeeds from some selected outcome on:
  - 165 of 168 for leximin on ranks (fair);
  - 162 for rank-maximal;
  - 154 for V-M's own matchings.

  The smallest fair failure is `induct-g-r2` (n = 3, m = 5). There the extending outcomes are exactly those in which
  the agent owning a private upper set picks last, and no rank-vector rule can see that.
- **Every SD outcome as a start** (`vm0_sd_screen.log`, `vm6_sd_*.log`). Some outcome completes on all 168. But:
  - 24 outcomes extend yet do not complete under F1–F3 with rotation (the GM4 family among them);
  - VMˣ (with exchanges) has no EFX₀ run from 30 of the 775 screen SD outcomes. The smallest is (0, 4, 3) of
    `nsw-local-n3m5`, n = 3, m = 5. All 3 EFX₀ allocations value-dominate it, and every one needs a three-agent
    cycle.
- **k = 3.** V-M's matching is not a sound base even for 3-limited instances, where TARGET is proved. On random
  general 3-limited instances it fails on 7 of 4,000 (`vm0_gen3lim.log`) and 50 of 20,000 (`vm_smallest_gen3lim.log`),
  smallest n = 3, m = 5. In that instance a balanced agent must trade its uncontested top for the pair worth more,
  LB⁺'s upgrade. VMˣ with free choices succeeds on all 4,000 (`vm6_gen3lim.log`).

### 6.4 F6x with choices (VMX) beyond the screen set

| source | instances | some run EFX₀ | every run EFX₀ | first run (all ties by index) EFX₀ | log |
|---|---|---|---|---|---|
| screen | 168 | **168** | 64 | | `vm6_screen.log` |
| logged hard profiles | 42 | **42** | | 40 | `vm6_logs.log` |
| SPECIAL | 4 | **4** | | 4 | `vm6_special.log` |
| cores n = 3 (random strict profiles) | 1,500 | **1,500** | 1,094 | 1,485 | `vm6_cores3.log` |
| cores n = 4 | 800 | **800** | 665 | 797 | `vm6_cores4.log` |
| general, n ≤ 6, m ≤ 10, junk | 3,000 | **3,000** | 2,838 | 2,996 | `vm6_gen.log` |
| general 3-limited | 4,000 | **4,000** | | | `vm6_gen3lim.log` |
| suite (n ≤ 26; DFS capped at 150 runs, then 30 samples) | see `vm6_suite.log` | | | | |

Choice is essential:
- "every run" fails on 5–30% of the hard sets;
- the first run fails already at n = 2, m = 5;
- the lazy F6x variant fails on 2 of 168 screen instances and on none of the random sets.

**But VMX is false** (`attempts/k4-vm-vmx.md`, independent replay). Hill-climbs that minimize the fraction of
successful runs (`vmx_climb.py`) found profiles of certified cores on which every run is stuck:
- n = 3, m = 6 (4 runs, `vmx_climb_n3.log`);
- n = 4, m = 8 (10 runs, `vmx_climb_n4.log`).

In the n = 3 one:
- agent 0 strongly prefers its top (8 > 4 + 3), so Phase I gives it good 5;
- yet no EFX₀ allocation gives 5 to agent 0, which must take its lower triple (9 > 8);
- the exchange that would do this is blocked by the good that Phase III already gave agent 2.

A breadth-first search over a superset of VMˣ's moves reaches only 3 states from each start. Random sampling never
found these profiles; only the climbs did.

## 7. Proved: soundness and termination of the repaired procedure

Call VMˣ the procedure: V-M's Phases I–II, then Phase III with F2, then (rotation; F6x move or F1 placement)
repeated while a valued good is unassigned, then F3. Each choice point is resolved arbitrarily. Write
ℓ_i(B) = #{T ⊆ R_i : v_i(T) < v_i(B)} and Φ(X) = Σ_i ℓ_i(X_i) ≤ Σ_i (2^{|R_i|} − 1) ≤ 15n.

**Lemma SND (soundness).** Every state of a run of VMˣ is a partial EFX₀ allocation. A run that never finds a good
without a safe place returns a complete EFX₀ allocation.

*Proof.*
- A one-good allocation (after Phase II) is EFX₀: removing the only good of a singleton leaves value 0.
- F2 and F1 add g to X_s only if no agent i ≠ s EFX₀-envies X_s ∪ {g}. Every other bundle is unchanged, and v_s
  does not decrease, so s's own conditions still hold.
- A rotation keeps the set of bundles and raises each rotated agent's value. The bundle an agent gives up is one it
  values less than its new bundle, and envy-freeness up to any good toward it holds a fortiori.
- F6x moves are applied only if the resulting state passes the raw EFX₀ check (`efx_violations`).
- The junk step is L3: after rotations the receiver s is unenvied, and junk is worthless to everyone, so
  v_i(X_s ∪ J ∖ h) ≤ v_i(X_s ∪ J) = v_i(X_s) ≤ v_i(X_i). ∎

**Lemma TERM (termination).** Every run of VMˣ performs at most m placements and at most Φ_max ≤ 15n rotations,
upgrades and exchanges. Each step takes polynomial time.

*Proof.*
- An upgrade takes |S| ≥ 1 goods from the pool and returns one; an exchange takes |S| ≥ 0 goods and returns none. So
  the pool never grows, and each placement shrinks it by one.
- Rotations, upgrades and exchanges strictly raise the value of at least one agent and lower none. If v_i rises from
  v_i(B) to v_i(B′), the set B ∩ R_i is counted in ℓ_i(B′) but not in ℓ_i(B), so Φ strictly rises.
- Placements never lower a value, so Φ never falls.
- Each step enumerates at most n agents, n² · 4 exchange partners and C(4, ≤ 3) pool subsets, and runs an O(n²m)
  EFX₀ check. ∎

So the whole difficulty is in one sentence.

**Conjecture VMX: REFUTED** (`attempts/k4-vm-vmx.md`; n = 3, m = 6 and n = 4, m = 8). VMX said: in every instance in
which every agent values at most four goods, some run of VMˣ never gets stuck.

**Conjecture VMX₂ (evidence only).** The same holds for VMˣ₂, which is VMˣ without Phase III: after Phases I–II, all
remaining goods go to the pool. Lemmas SND and TERM hold for VMˣ₂ with the same proofs. Its tests are in §7.1.

VMX₂ implies TARGET₄ (Lemma SND). It also implies, for the V-M matching the run starts from, the value domination of
Conjecture MD (K4.SDC.MD, `k4/sdc.md` §28): the final allocation value-dominates the start, because no step lowers a
value. VMX₂ is a *path* statement. Its runs are Pareto-monotone, so by P1 they can be trapped, and VMX₂ says that some
path avoids every trap.

### 7.1 Tests of VMX₂

| source | instances | some run EFX₀ | every run EFX₀ | first run (all ties by index) EFX₀ | log |
|---|---|---|---|---|---|
| screen | 168 | **168** | 49 | 165 | `vmx2_screen.log` |
| logged hard profiles | 42 | **42** | 7 | 41 | `vmx2_logs.log` |
| SPECIAL | 4 | **4** | 0 | 4 | `vmx2_special.log` |
| cores n = 3 | 1,500 | **1,500** | 909 | 1,472 | `vmx2_cores3.log` |
| cores n = 4 | 800 | **800** | | | `vmx2_cores4.log` |
| general, n ≤ 6, m ≤ 10 | 3,000 | **3,000** | 2,786 | 2,994 | `vmx2_gen.log` |
| the two VMX counterexamples (§6.4) | 2 | **2** (18/26 and 559/595 runs) | | | `attempts/k4-vm-vmx.md` |

**Climbs against VMX₂** (`vmx_climb.py ... --phase3=0`) used the same budget as the climbs that refuted VMX: 64 climbs
of 80 steps at n = 3, and 48 of 60 at n = 4 (other seeds). They found no counterexample. The lowest success
fractions reached are:
- 6 of 12 runs at n = 3 (`vmx2_climb_n3.log`);
- 20 of 30 runs at n = 4 (`vmx2_climb_n4.log`).

With that budget VMX went to 0 at both sizes. This is evidence only. The next step is longer climbs, n = 5, and
objectives other than the success fraction (e.g. the number of successful runs).

### 7.2 VMX₂ on the coordinator's named instances, and core-checked climbs at n = 4, 5, 6

**Named instances** (`k4/vm/vmx2_named.py`, `results/k4_vm/vmx2_named.log`). The set:
- B< and B>, the OC₁ counterexample on a strict connected n = 6 core (k4/oc1_hall.md §16, on another branch; values
  as sent by the coordinator);
- T3, Q2, r4253 and r3943 (SPECIAL), and `lb4-owner-needs-from-base-n4m8`;
- the TTC session's 84 OC₁ counterexamples, its n = 5 counterexample and its core candidate
  (`results/k4_ttc/*.json` on `claude/k4-ttc`).

Each instance was run under 3 relabellings of agents and goods as well. **All 372 items have an EFX₀ run of VMX₂,
and every output passes an independent raw-EFX₀ checker.** In every case the first DFS run (moves preferred,
first option everywhere) already succeeds.

**Climbs on strict connected cores** (`k4/vm/vmx2_climb.py`). Each mutation changes one agent's order type and
ranking, or swaps one good in one agent's set. It is kept only if `is_core4` (`k4/c4_verify_H/hcore.py`: IsCore4,
strictness, connectivity) passes. The objective is the fraction of 40 random VMX₂ runs that succeed.

| n | climbs × steps | core-checked mutations | lowest success fraction reached | log |
|---|---|---|---|---|
| 4 | 64 × 300 | 15,653 | 0.200 | `vmx2_climb4s.log` |
| 5 | 32 × 150, 64 × 400 | 4,110 + 21,798 | 0.125 | `vmx2_climb5.log`, `vmx2_climb5_long.log` |
| 6 | 32 × 120, 48 × 300 | 3,330 + 12,570 | 0.675 | `vmx2_climb6.log`, `vmx2_climb6_long.log` |

No counterexample to VMX₂. The climbs do find harder instances as they run longer, so this is evidence only.

### 7.3 The structure of the successful runs: one move, then placement (Conjecture VM1)

`k4/vm/vmx2_phases.py` splits a VMX₂ run into two phases:
- Phase A: moves only (rotations, pool upgrades, two-agent exchanges) from a V-M matching;
- Phase B: F1 placements with rotation, no moves.

It explores every Phase-A state Z (capped) and, for each, every Phase-B run (capped).

| source | instances | some Z completes in Phase B (two-phase VMX₂) | fewest moves needed | some Z completes under *every* Phase-B order | log |
|---|---|---|---|---|---|
| screen | 168 | **168** | 0 moves: 157; 1 move: 11 | 164 | `vmx2_phases_screen.log` |
| named (B<, B>, SPECIAL, TTC 84+2, the two VMX counterexamples), at most 1 move | 95 | **95** | 0 moves: 95 | 94 | `vm1_named.log` |
| cores n = 3 (at most 1 move) | 1,500 | **1,500** | 0 moves: 1,495; 1 move: 5 | | `vm1_cores3.log` |
| cores n = 4 (at most 1 move) | 800 | **800** | 0 moves: 800 | 798 | `vm1_cores4.log` |
| cores n = 5 (at most 1 move) | 400 | **400** | 0 moves: 400 | 283 | `vm1_cores5.log` |
| general, n ≤ 6, m ≤ 10 (at most 1 move) | 3,000 | **3,000** | 0 moves: 2,998; 1 move: 2 | 2,923 | `vm1_gen.log` |

Valuer-only placement (a good goes only to an agent that values it) is refuted: on the screen set it finds an EFX₀
run on 117 of 168, smallest failure n = 2, m = 5 (`x2-val` in `vm6_test.py`). Junk-like placement on agents who do
not value the good is essential.

All runs above use narrow exchanges (the good z handed to i must be valued by i).

**With narrow exchanges VM1 is false** (`attempts/k4-vm-vm1.md`, independent replay). Climbs against VM1
(`vmx2_climb.py --obj=vm1`, is_core4 after every mutation) found strict connected cores where no state within one
narrow move completes:
- n = 3, m = 7;
- n = 4, m = 7.

Both need two narrow moves, but **one unrestricted exchange** completes each: there, i may take a good z it values at
0, as when agent 2 gives its top to agent 1 and takes agent 1's good 6 plus pool goods. So VM1 is stated with
unrestricted exchanges (`vmlib.FREE_Z`). The figures in the table, all with narrow exchanges, are therefore also
figures for it.

**Conjecture VM1 (evidence only).** For every 4-limited instance there are:
- a V-M matching Y (Phases I–II, some resolution of the ties);
- at most one move: a pool upgrade, or a two-agent exchange (i, holding a single good, takes any good z of j plus
  pool goods), with both agents gaining and EFX₀ kept;
- an order of the remaining goods;

such that placing each good on some agent whose bundle stays EFX₀-unenvied, rotating envy cycles before each
placement, ends with a complete EFX₀ allocation. VM1 ⟹ VMX₂ ⟹ TARGET₄.

**Invariant and proof target.** Every state of a VMX₂ run satisfies the following, all proved (Lemmas SND, TERM, and
EFX₀ itself):
- (I1) it is a partial EFX₀ allocation;
- (I2) v_i(X_i) ≥ v_i(Y_i) for every agent i, so the state value-dominates the start (Conjecture MD's domination);
- (I3) every good some agent prefers to its own bundle is held alone (EFX₀ implies this);
- (I4) every bundle of two or more goods is envied only by agents that value all of its goods;
- (I5) the pool never grows, and Φ = Σ_i ℓ_i(X_i) rises at every move and rotation.

The one step that is not proved is **placeability**: for some V-M matching, possibly after one move, the pool can be
placed by EFX₀-safe placements with rotation. Two remarks on what that step needs:
- *It is not implied by (I1), (I3) and (I4), even with no wanted pool good.* The state X of P1 (K4.SDC.P1, GM4-E) is
  partial EFX₀ and none of its four agents values the left-out good 6 more than its own bundle, yet good 6 cannot be
  placed. Whether X also value-dominates a V-M matching (I2) was not checked. So the proof must use what V-M's matching provides: Lemma S's
  saturation, and the rank-greedy structure of Lemma PO.
- *The single good-order choice already matters.* With distinct tops the start is ({a_i}), every good is worth at
  most v_i(a_i), and some order succeeds (Theorem DT). But not every order does (`attempts/k4-vm-f1-order.md`).

The natural first target is therefore VM1 at zero moves on the class where it holds on the data (157/168 screen,
95/95 named):
> from some V-M matching, F1 with rotation places the whole pool,

followed by a characterization of the instances that need the one move.

### 7.4 V-M matchings versus maximum matchings, and a Hall-type form of placeability (coordinator's questions)

**V-M matchings are Pareto-optimal SD outcomes (Lemma PO) but not always maximum matchings.**
- Example, not a core: agent 0 values {x, z} with x first; agent 1 values {y, x} with y first; agent 2 values only
  y.
  - Step 1 gives x to agent 0 uncontested and y to agent 1 or 2, and the loser of y gets nothing.
  - So every V-M matching has size 2, while 0:z, 1:x, 2:y has size 3.
- On the data (`vm_max.py`; `vm_max_screen.log`, `vm_max_named.log`):
  - 426 of 449 V-M matchings on the screen set are maximum; on the named set only 49 of 238;
  - on B< and B>, no V-M matching is maximum (ν = 6).

So Lemma MAX (Hall session) does not apply to V-M starts in general. Yet VM1 with no move completes from B< and B>,
whose V-M matchings are all non-maximum, the kind of start at which OC₁ fails.

Neither completion shape contains the other. VM1's no-move completion uses rotation, which moves the picks:
- on the named set, 93 of the 231 successful matchings need it, and of the 138 that keep the picks, 39 are
  one-absorber;
- on the screen set the figures are 54 of 403, and 337 of 349.

I have not run OC₁^max's checker on V-M starts.

**What saturation gives (proved).**

**Lemma P0.** At every V-M matching Y (main reading), no pool good is wanted: v_i(g) ≤ v_i(Y_i) for every agent i
and every unassigned good g.

*Proof.* If v_i(g) > v_i(Y_i), then g is ranked above Y_i, or i has no pick. Ranked above means g = r_i(j) with
j < st(i), which is assigned by Lemma S. With no pick, all of R_i is assigned (Lemma S). Either way g is not
unassigned. ∎ (Checked: 0 violations among 687 matchings, `vm_hall_*.log`.)

**Lemma P1′.** Call u *frozen* if some agent prefers Y_u to its own pick, and *unfrozen* otherwise.
- At a V-M matching, {Y_u, d} is EFX₀-safe for every pool good d exactly when u is unfrozen.
- A frozen agent can receive nothing while it stays frozen.

*Proof.* For k ≠ u, the threat of a two-good bundle is max(v_k(Y_u), v_k(d)). Here v_k(d) ≤ v_k(Y_k) by P0, and
v_k(Y_u) ≤ v_k(Y_k) iff k does not want Y_u. If k wants Y_u, any added good leaves Y_u after the removal of the other
good. ∎

So each unfrozen agent is a universal one-good slot (Theorem DT's (F2), here for every V-M start), and placeability
becomes a covering question.

**Proposition HDT (proved).** Suppose there are an unfrozen agent o and a set D of pool goods, matched injectively
into distinct unfrozen agents other than o, such that the allocation (picks, D placed, all other pool goods and junk
with o) is EFX₀. Then the no-move completion of VM1 succeeds. In Hall form: the goods that must be kept out of the
owner's bundle to protect the frozen agents (and the non-robust unfrozen ones) fit into |U| − 1 universal slots.

*Proof.* First place D one good per slot; these are safe by P1′. Then place the rest on o in any order. The threat
of a bundle is monotone under inclusion, and every other bundle is already final, so each intermediate bundle of o
is safe. This uses the variant without rotation. ∎

**How much of placeability HDT explains** (`vm_hall.py`, `vm_extend.py`), as a strict hierarchy:

| instances where some V-M matching… | screen (168) | named (95) |
|---|---|---|
| is HDT (one unfrozen owner, slots for the rest) | 115 | 23 |
| extends to an EFX₀ allocation with its picks kept (SD-C at a V-M order; several absorbers allowed) | 147 | 93 |
| completes with no move, rotation allowed | 157 | 95 |
| completes with at most one move (VM1) | 168 | 95 |

- HDT ⇒ success held in every case (263/263 and 35/35 matchings).
- The gap between the rows is filled by:
  - several absorbers;
  - *unfreezing*: placing goods on a wanter raises its value until it stops wanting, and rotations then move bundles.
  - On the named set, T3 and the n = 3 VMX counterexample complete only with rotation.

**So the extra hypothesis the coordinator asked for is P0 together with the one-good shape.** GM4-E's stuck state
has no wanted pool good either, but two of its agents already hold pairs, so no unfrozen singleton slots remain.

The proof target sharpens to:
- (i) HDT is a Hall/counting condition: a Theorem A₄ at V-M starts (ledger item 18's count, with every unfrozen
  agent a slot by P1′);
- (ii) when it fails, either an unfreezing placement or one rotation restores it.

### 7.5 The repair classes, Lemma EXT, and VM1 at k = 5 (coordinator's requests)

**Classification** (`vm_classify.py`, SAT with sdclib's exact EFX₀ encoding). Each instance gets the simplest repair
that some V-M matching Y needs:
- *HDT*: Proposition HDT applies;
- *absorbers*: Y extends to an EFX₀ allocation in which every agent frozen at Y keeps a single good, with several
  absorbers;
- *unfreezing*: Y extends, but every extension gives goods to some agent that is frozen at Y;
- *rotation*: Y extends to no EFX₀ allocation, yet F1 placements with rotation complete it;
- *one move*: only VM1's single move helps.

| class | screen (168) | named (95) | k = 5 set (6) |
|---|---|---|---|
| HDT | 115 | 23 | 2 (PW4, kgen-n4-ties) |
| absorbers | 20 | 70 (B<, B>, `lb4-owner-needs-from-base-n4m8`, most of TTC) | 1 (kgen-n4-strict) |
| unfreezing | 12 | 0 | 0 |
| rotation | 10 | 2 (T3, the n = 3 VMX counterexample) | 2 (RD4, RD5) |
| one move | 11 | 0 | 1 (PW5) |
| none (would refute VM1) | **0** | **0** | **0** |

Logs: `vm_classify_{screen,named,k5}.log`.

**Lemma EXT (proved).** Let Y be a one-good matching and X ⊇ Y a complete EFX₀ allocation. Put k → j (k ≠ j) when
θ_k(X_j) > v_k(Y_k), where θ_k(B) = v_k(B) − min_{h∈B} v_k(h). If this digraph is acyclic, F1 placements without
rotation reach X: fill the bundles X_j ∖ Y_j in a topological order, one good at a time.

*Proof.* Suppose g joins j's current bundle X′_j, with Y_j ⊆ X′_j ⊆ X′_j ∪ {g} ⊆ X_j. Take any agent k ≠ j.
- If k's bundle is already complete, k sees θ_k(X′_j ∪ {g}) ≤ θ_k(X_j) ≤ v_k(X_k). The threat is monotone under
  inclusion: removing a good from B lowers v_k(B) by at least the change in the minimum.
- If k's bundle is not complete, then k comes after j in the order, so k ↛ j. Hence
  θ_k(X′_j ∪ {g}) ≤ θ_k(X_j) ≤ v_k(Y_k) ≤ v_k(X′_k).

No other bundle changes. ∎

**On the data, every extension class is covered by Lemma EXT** (`vm_prec.py`). In every instance of the classes HDT,
absorbers and unfreezing, some V-M matching has an extension with an acyclic precedence digraph:
- 147 of 147 on the screen set;
- 93 of 93 on the named set.

So for these classes VM1's no-move completion follows from two facts. Their proof status is:
- (E) some V-M matching extends to an EFX₀ allocation. This is SD-C restricted to rank-greedy orders, and it is
  open: it fails on 21 of 168 screen instances.
- (A) some extension is acyclic in the sense above. This is open too, and holds on all data.

**The rotation class is a ring.** In T3, from ({0}, {4}, {1}):
1. good 3 goes to agent 2 and good 2 to agent 1;
2. that closes the envy cycle 0 → {4, 2}, 1 → {1, 3}, 2 → {0};
3. rotating it gives ({4, 2}, {1, 3}, {0}), and good 5 then goes to agent 2.

The same happens in the n = 3 VMX counterexample and in RD4 and RD5. These are OC's ring moves (k4/sdc.md §29),
performed implicitly by placements and one rotation.

**The one-move class is a chain.**
- An upgrade is a chain with t = 0: the agent takes pool goods worth more than its pick. For example, agent 0 of
  `c4-exposure-nonleader-n3m5` trades {3} for {0, 1}.
- An exchange is a chain with t = 1. In PW5, agents x₁ and x₂ take pairs of the shared pool D and release p₁ and p₂
  to the w's.

So VM1 reads as: from a V-M matching, at most one chain, any number of rings (as rotations), and a free completion
with several absorbers. **What is proved:** P0, P1′, Proposition HDT, Lemma EXT, and Lemmas SND and TERM. **What is
open:**
- (E) and (A) for the extension classes;
- that one ring suffices in the rotation class;
- that one chain suffices in the one-move class.

**VM1 at k = 5.** The code generalizes: Phase II runs one matching per rank up to max |R_i|, and the move sets are
unbounded. The k = 4 results are unchanged (re-run on the screen set). On the k-sensitivity session's instances
(`k4/ksens.md` on `claude/k4-ksens`) and the general-k session's n = 4 counterexamples (`attempts/kgen-n4-oc1.md` on
`claude/kgen-n3`) the results are:

| instance | n, m, k | ν, V-M sizes | fewest moves to a placeable state | VMX₂'s first run |
|---|---|---|---|---|
| PW5 | 5, 9, 5 | 5; 5 | **1** | EFX₀ |
| PW4 | 5, 8, 4 | 5; 5 | 0 | EFX₀ |
| RD5 | 4, 7, 5 | 4; 3 and 4 | 0 (rotation) | EFX₀ |
| RD4 | 4, 7, 4 | 4; 3 and 4 | 0 (rotation) | EFX₀ |
| kgen-n4-strict | 4, 8, 5 | 4; 4 | 0 | EFX₀ |
| kgen-n4-ties | 4, 7, 5 | 4; 4 | 0 | EFX₀ |

Logs: `vm1_k5.log`, `vm1_k5_detail.log`, `vmx2_k5.log`; every output was re-checked with the raw EFX₀ definition.
OC₁ (and OC₁^max) fail on PW5 and RD5, and VM1 survives both. Wider tests at k = 5:
- Random 5-limited instances (2,000; n ≤ 5, m ≤ 10): VM1 holds on all, 1,998 with no move and 2 with one
  (`vm1_gen_k5.log`).
- Adversarial climbs at k = 5 on general instances (`vm1_climb_k.py`; mutations re-draw one agent's values or swap
  one of its goods): no counterexample. The lowest margins are (one move needed, 2/7 of the one-move states complete)
  at n = 4, and (one move needed, 2/3) at n = 5 (`vm1_climb_k5_n{4,5}.log`).

These are short climbs (32 × 80 and 32 × 60), evidence only. VM1 is a general-k candidate, not yet stressed like
the k = 4 statements.

### 7.6 Open fact (A), and the ring of the rotation class (coordinator's requests 2 and 3)

**(A): some extension is acyclic** (`vm_prec2.py`, brute force over every extension of every V-M matching).

| | screen | named |
|---|---|---|
| instances with an extension | 147 | 93 |
| every extension acyclic | 139 | 93 |
| some extensions cyclic, some acyclic ((A) needs a choice) | 8 | 0 |
| every extension cyclic (would refute (A)) | **0** | **0** |

The smallest instance where (A) needs a choice has **n = 2, m = 5** (`c4-exposure-deficit2-n2m5`).

| agent | ranking (good: value) |
|---|---|
| 0 | 3: 10 > 2: 7 > 4: 4 > 0: 2 |
| 1 | 3: 7 > 1: 6 > 4: 5 > 2: 3 |

From Y = ({3}, {1}) there are 4 extensions:
- the cyclic one is ({3, 0}, {1, 2, 4}). Each agent's final threat from the other bundle exceeds its pick
  (θ₀ = 11 > 10, θ₁ = 7 > 6), so neither bundle can be filled first.
- the other three are acyclic: ({3, 0, 2}, {1, 4}), ({3, 2}, {1, 0, 4}) and ({3, 4}, {1, 0, 2}). In each, one agent's
  final threat stays at or below its pick, and that agent can be filled last.

The other V-M matching, ({2}, {3}), has one extension, and it is cyclic. Next smallest: `lb4-n2m5-upgrade` (n = 2,
m = 5) and D3 (n = 3, m = 6); logs in `vm_prec2_*.log`. No proof of (A) yet.

**The rotation class needs one ring, of one shape** (`vm_rot.py`, `vm_rot_shape.py`). On all 14 rotation-class
instances (10 screen, T3, the n = 3 VMX counterexample, RD4, RD5):
- the least number of rotations on a successful run is exactly **one**: a 2-cycle in 13 and a 3-cycle in T3;
- each rotated cycle has exactly **one want arrow**: the taker takes a frozen agent's single pick, which it prefers
  to its own pick;
- the other arrows (one, or two in T3) are **pair arrows**: the taker takes a pick plus pool goods that the earlier
  placements put there, and it values every one of those pool goods.

The number of pool goods on a pair arrow is 1 (6 instances), 2 (7) or 3 (1).

**Comparison with DE's ring lemma at k = 3** (`paper/k3-simple/long.tex`, Theorem `improve` and Lemma `ring`, read
for this). There, if no free agent can finish, every free agent has at least as many blockers with distinct leftover
goods as there are free agents. Each free agent points at a blocker by a pair arrow (the blocker's pair is its good
plus one leftover good). Every other agent points by a want arrow at an agent that wants its good. Following the
pointers closes a ring along which everyone gains.

The k = 4 data has the same shape, a ring of want arrows and pair arrows, with one difference:
- a pair arrow carries 1 to 3 pool goods, where DE's carries exactly one;
- so the distinctness step of DE's proof (distinct leftover goods for distinct free agents) becomes a disjointness
  requirement on sets of up to three pool goods;
- DE's counting, "|H_o| ≥ |F| blockers", has to become a count of disjoint upper sets inside the pool.

DE also needs up to 4n trades in general, and no bounded number of pair arrows suffices (its Appendix). Here one
ring was always enough because VM1 starts at a V-M matching (Lemma P0: no pool good is wanted) and may use several
absorbers.

**Conjecture Ring₄ (evidence only; the proof target for the rotation class).** If no V-M matching extends, then
for some V-M matching Y there is a cycle with exactly one want arrow whose pair arrows carry pairwise disjoint sets of
pool goods valued by their takers. Placing those sets and rotating the cycle gives a state that extends (with an
acyclic extension).

What a proof needs beyond DE: the count of disjoint upper sets inside the pool. That is ledger item 18's Theorem A₄
count again, now for blockers rather than for the owner.

### 7.7 Stressing VM1 at k ≥ 5 (coordinator's request 1)

`k4/vm/vm1_fast.py` checks VM1 with early exit. It searches F1 placements with rotation, memoized, from each V-M
matching and from each state one move away (unrestricted exchanges). Every completion is re-checked with the raw
EFX₀ definition. A failure is re-checked with 50× larger caps, then by the uncapped `vm1_verify.py`.

| data | instances | VM1 holds | moves needed | log |
|---|---|---|---|---|
| unrestricted, n = 3, m = 5–9 (every agent values every good, k = m) | 300 | **300** | 0 | `vm1_full3.log` |
| unrestricted, n = 4, m = 6–9 | 200 | **200** | 0 | `vm1_full4.log` |
| unrestricted, n = 4, m = 10 | 60 | **60** | 0 | `vm1_full4m10.log` |
| PW(f, W, r) grid, f = 2–4, W = 1–3, k = max(r + 1, f + 1) ≤ 9, one instance each | 63 | 61 | 0: 52; 1: 9 | `vm1_pwgrid.log` |
| long climbs, k = 5, 6, 8, n = 4–6 | see the logs | | | `vm1_climb_k*_long.log` |

**VM1 is refuted at k = 7** (`attempts/k4-vm-vm1-k7.md`):
- The instance is PW(2, 3, 6)#0, with n = 5 and m = 11.
- With at most one move nothing completes: 4 matchings and 90 states one move away, checked uncapped and by an
  independent replay over a superset of the moves.
- Two moves suffice: both frozen x's trade their picks for sets of the shared pool D.
- PW(3, 3, 8)#0 (k = 9, n = 6, m = 14) fails with zero, one and **two** moves: 4, 273 and 3,319 states, uncapped
  (`vm1_verify_pw338.log`). So "at most two moves" (VM2) fails at k = 9. **Three moves suffice**: all three frozen
  x's trade their picks for sets of D, e.g. ({6, 7}, {8, 9, 10}, {13, 11, 4, 3}, {2}, {0}, {5, 12, 1}). Replay:
  `attempts/k4_vm_vm2_pw338.py`.
- Every PW instance with k ≤ 6 passes.

So VM1 is not a general-k statement. On the PW family it holds up to k = 6 and fails from k = 7. That fits the
k-sensitivity session's "c chains fail from k = 2c + 3" shifted by two, i.e. c moves of VM failing from k = 2c + 5.
Two data points support this so far: c = 1 at k = 7 and c = 2 at k = 9, and on both the number of moves needed is
exactly f, the number of frozen agents (2 and 3). **VMX₂ (any number of moves) is the general-k form**, and it
completes both PW failures. At k = 4,
VM1 is unaffected.

## 8. Theorem VM: a proof of Viswanathan–Mehta's claim (ordinary EFX), main reading

The abstract asserts the source property ("we are able to prove that ... there will be a source") without proof.
Here is a complete proof for the reconstruction of §2 under the main reading (rank = G, aout = matched, n1a = Y).
Values are nonnegative and additive, ties are allowed, and rankings break ties by good index.

**Theorem VM.** If every agent values at most four goods, every run of VM (any resolution of its choice points) ends
with a complete EFX allocation. At every EFX-graph step the graph G_efx(j, S, X) is acyclic, every directed path in it
has at most two edges, and so it has a source.

Notation:
- st(i): 0 for the Phase-I winners W, k for i ∈ N_k, ∞ for the agents left in N^r;
- r_i(k): i's k-th ranked good;
- for i ∈ W ∪ N₁: a_i = r_i(1) and L_i = R_i ∖ {a_i}, so |L_i| ≤ 3;
- S = N₁ ∪ N₂ʳ ∪ W.

**Fact 0.** For ordinary EFX only X_j ∩ R_i matters: i EFX-envies B iff |B ∩ R_i| ≥ 2 and
v_i(B ∩ R_i) − min_{h ∈ B ∩ R_i} v_i(h) > v_i(X_i).

*Proof.* Removing a good h with v_i(h) > 0 leaves v_i(B ∩ R_i) − v_i(h). The worst case is the least such h. If
B ∩ R_i is a single good, its removal leaves 0. ∎

**Lemma S′ (saturation in Phase III).** After step (a) every N₃ agent's r(4) is assigned. After (b) every N₂ agent's
r(3) is assigned. After (c) every agent of N₂ ∖ N₂ʳ has its r(4) assigned. The proof is the one of Lemma S (§2.1): a
maximum matching in G_k gives every claimed good to some claimant.

*Step 1 (Phase II).* All bundles have at most one good, so the allocation is EFX by Fact 0.

*Step 2 (Phase III keeps EFX).* In each of (a), (b), (c), a bundle {y_s} with y_s = r_s(st(s)) becomes {y_s, g}, where
g = r_s(3) or r_s(4) was unassigned. By Fact 0, an agent i ≠ s EFX-envies {y_s, g} only if it values both goods and
max(v_i(y_s), v_i(g)) > v_i(X_i). That never happens:
- *i ∈ W ∪ N₁.* v_i(X_i) ≥ v_i(a_i), which is at least every single good.
- *i ∈ N₄ ∪ N^r.* By Lemma S all of R_i was assigned after Phase II, and g was not.
- *i ∈ N₃.* By Lemma S, r_i(1) and r_i(2) are held by agents with st ≤ 2.
  - In (a), y_s is held by s, and st(s) = 3, so y_s ∉ {r_i(1), r_i(2)}. Also y_s ≠ r_i(3), which i holds. Hence a
    valued y_s is r_i(4). Likewise a valued g (unassigned) is r_i(4). They cannot both be, since y_s ≠ g.
  - In (b) and (c), r_i(4) is already assigned (S′), so i does not value g at all.
- *i ∈ N₂.* r_i(1) is held by an agent with st ≤ 1. y_s is held by s with st(s) ≥ 2, so y_s ≠ r_i(1), and y_s ≠ r_i(2)
  since i holds that. Also g ∉ {r_i(1), r_i(2)}, because both are assigned. So both goods lie in {r_i(3), r_i(4)}, and
  max(v_i(y_s), v_i(g)) ≤ v_i(r_i(3)) ≤ v_i(r_i(2)) ≤ v_i(X_i).

Every other bundle is unchanged, and the receivers' values only rise.

*Step 3 (the abstract's claim, "the only agents that may have valued objects not yet assigned are in N_1 and
N_2^r").* After Phase III every agent valuing an unassigned good is in S. Go through the other groups:
- N₄ ∪ N^r: by Lemma S, all their goods are assigned.
- N₃: r(1) and r(2) are assigned, r(3) is held, and r(4) is assigned by S′.
- N₂ ∖ N₂ʳ: r(1) is assigned, r(2) is held, and r(3) and r(4) are assigned by S′.
- Unmatched A-agents entered Phase II, so they lie in one of these groups.

The set of unassigned goods only shrinks afterwards, so the claim persists through the EFX-graph steps.

*Step 4 (bundles in S).* A good placed by an EFX-graph step goes to a node, that is, to a valuer. Before those steps:
- an agent of W ∪ N₁ holds {a_i};
- an agent of N₂ʳ holds {r_i(2), r_i(3)}.

So X_i ⊆ R_i for every i ∈ S throughout.

*Step 5 (out-edges).* Fix j, and let B = X_{i′} ∪ {j} for a node i′ ≠ i.
- **(i) W has no out-edges.** Take i ∈ W. Then a_i ∈ X_i, so a_i ∉ B, and B ∩ R_i ⊆ L_i. For T ⊆ L_i,
  v_i(T) − min_T ≤ v_i(r_i(2)) + v_i(r_i(3)) < v_i(a_i) ≤ v_i(X_i), since i ∈ A.
- **(ii) N₁ out-edges.** If i ∈ N₁ has an edge i → i′, then |R_i| = 4, X_i = {a_i}, and B ⊇ L_i, so |X_{i′}| ≥ 2.
  Indeed, T = B ∩ R_i ⊆ R_i ∖ X_i ⊆ L_i. If |T| ≤ 2, then v_i(T) − min_T is at most one good's value, which is at
  most v_i(a_i) ≤ v_i(X_i). So T = L_i has three goods and X_i ∩ L_i = ∅. Since j ∈ T, the other two goods of T lie in
  X_{i′}.
- **(iii) An N₁ agent with at least two goods has no out-edge.** This follows from (ii).
- **(iv) N₂ʳ out-edges go to W.** Let i ∈ N₂ʳ have an edge i → i′. Then T = B ∩ R_i ⊆ R_i ∖ X_i ⊆ {r_i(1), r_i(4)}.
  EFX-envy needs T = {r_i(1), r_i(4)} and v_i(r_i(1)) > v_i(X_i) ≥ v_i(r_i(2)) + v_i(r_i(3)), so i ∈ A. Being in N₂,
  i lost r_i(1) in Phase I to another agent of A, which belongs to W and keeps it (no step of VM removes a good).
  Since r_i(1) ≠ j (it is assigned),
  r_i(1) ∈ X_{i′}, so i′ is that agent of W.

Now follow a directed path from each kind of start:
- from W: it stops at once, by (i);
- from N₁: it goes to an agent holding at least two goods, which is in N₁ (stop, by (iii)), in W (stop), or in N₂ʳ;
- from N₂ʳ: it goes to W and stops.

So every path has at most two edges, and there is no cycle. The node set is nonempty: j is valued by someone, hence
by an agent of S (Step 3). A finite acyclic digraph with at least one node has a source.

*Step 6 (adding j to a source keeps EFX).* Let s be a source.
- Every valuer of j is a node (Step 3), and none of them EFX-envies X_s ∪ {j}, since s has no in-edge.
- For a non-valuer i, (X_s ∪ {j}) ∩ R_i = X_s ∩ R_i, so by Fact 0 nothing changes for i.
- The other bundles are unchanged, and s gains.

*Step 7 (junk).* A good valued by nobody changes no X_j ∩ R_i, so by Fact 0 giving it to anyone keeps EFX. ∎

**Remarks.**
- The bound "two edges" is attained (`results/k4_vm/vm_thm_check_*.log`).
- `k4/vm/vm_thm_check.py` re-runs the phases and asserts Steps 2, 3, 4 and 5 on every run. No assertion failed on the
  screen set (10,222 runs), on 5,000 general instances (120,551 runs) or on 5,000 general instances with ties
  (122,378 runs).
- The proof also shows **exactly where EFX₀ breaks**: Fact 0 has no analogue for EFX₀. In Step 2 the non-valuers are
  dismissed because they "do not value g", and in Step 6 because "nothing changes for i". Under EFX₀ these are the
  agents that envy {y_s} or X_s and see a good worthless to them added (§5.1).
- Both conventions that differ from the literal text are needed:
  - aout = matched: otherwise the n = 2 failure of §4.2;
  - n1a = Y: otherwise the goods valued only by W have no node.
