# From Viswanathan–Mehta's 4-limited EFX algorithm to EFX₀ (workstream proof/k4-vm)

Branch `claude/k4-vm`, draft PR "[proof/k4-vm] From 4-limited EFX to EFX₀". Code: `k4/vm/`; logs: `results/k4_vm/`.
Everything called evidence below is evidence only (PROMPT.md §5 rule 3). Nothing here changes a ledger row; the
coordinator integrates.

## Status (burst 2, in progress; burst 1 below it)

- **Burst 2: EFX₀ repairs of V-M, killed or confirmed by computation** (§6, §7).
  - F1 (EFX₀ graph over all agents), F2 (EFX₀-safe Phase III), F3 (L3 junk) and rotation complete V-M's matching
    wherever it extends, on screen, logs, SPECIAL and cores n = 3 and n = 5.
  - **The completion conjecture VC is REFUTED** at n = 4, m = 8 (`attempts/k4-vm-completion.md`, independent
    replay). V-M's Phase III order hands a good to the wrong agent.
  - Adding **exchange moves (F6x)** gives a run that ends EFX₀ on all 168 screen instances. But the two natural
    deterministic rules fail: "move only when stuck" on 2 instances, "move whenever possible" on 5 (smallest n = 3,
    m = 6).
  - **Proved** (§7): every run of the repaired procedure VMˣ keeps a partial EFX₀ allocation (Lemma SND) and stops
    after at most m placements and 15n value-raising moves (Lemma TERM).
  - The open part is **Conjecture VMX**: some run never gets stuck. VMX implies TARGET₄ and, for V-M's matchings,
    Conjecture MD. Its runs are value-monotone, so P1 (K4.SDC.P1) explains why the choice of path matters.
  - Pending: F5 (strip and refill), the fair order, F6x beyond the screen set.

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

So V-M's matchings are SD outcomes of the *rank-greedy* orders. Lemma 1 of `k4/sdc.md` makes "some EFX₀ allocation
extends Y" the SD-C completion question for these orders.

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

Logs: `vm6_screen.log`; the other sources are in §6.4.

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

### 6.3 F5 (strip and refill) and the fair order

PENDING (`vm_strip_*.log`, `vm0_fair_*.log`).

### 6.4 F6x choice beyond the screen set

PENDING (`vm6_*.log`).

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

So the whole difficulty is in one sentence:

**Conjecture VMX (evidence only).** In every instance in which every agent values at most four goods, some run of VMˣ
never gets stuck.

VMX implies TARGET₄ (Lemma SND). It also implies, for the V-M matching the run starts from, the value domination of
Conjecture MD (K4.SDC.MD, `k4/sdc.md` §28): the final allocation value-dominates the start, because no step lowers a
value. VMX is a *path* statement. Its runs are Pareto-monotone, so by P1 they can be trapped, and VMX says that some
path avoids every trap.
