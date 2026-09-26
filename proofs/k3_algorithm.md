# A polynomial-time algorithm for EFX₀ with at most three relevant goods (K3ALG)

Workstream `formal/k3-algo`, ledger rows K3.ALG, K3.ALG.TIME, K3.OWNER, K3.ALG.RUN, and for LS2 (§8) K3.LS2 and
K3.LS2.RUN; workstream `formal/k3-real-cost`, rows K3.ALG.FINE and K3.ALG.REAL. Lean:
`lean/EFX/K3Algo.lean`, `lean/EFX/Timed.lean`, `lean/EFX/K3CostLB.lean`, `lean/EFX/K3Cost.lean`,
`lean/EFX/K3CostBound.lean`, `lean/EFX/K3CostFine.lean`, `lean/EFX/K3Real.lean`. Implementations: `k3/k3algo.py`; cross-check with Lean: `k3/lean_crosscheck.py`.

**Status.**
- Machine-checked in core Lean, standard axioms only, `lean/check.sh` passes:
  - the algorithm `EFX.K3.algo`, a computable function (`#eval` runs it);
  - its correctness `EFX.K3.algo_efx0`;
  - its running time `EFX.K3.algoC_cost`: at most 400·(n + m + 1)⁴ counted operations, in the cost model of §6;
  - the finer bound of §5, `EFX.K3.algoC_cost_fine`: at most n⁴ + 20n³ + 25n²m + 124n² + 47nm + 119n + 22m + 3
    counted operations, O(n⁴ + n²m);
  - K3ALG on real values in the comparison model (the remark of §3, via L12's surrogate computed with an oracle):
    `EFX.K3.algoOrd_efx0`, `EFX.K3.algoOrdC_cost`.
- Written in this file, with a proof:
  - the resolution of the owner-test issue (§4); its Lean form `EFX.LB.validOwner_iff` was already in the library.
- Evidence only (§7):
  - the implementations agree with each other and with Lean's `#eval`;
  - raw EFX₀ checks on certified cores and random instances;
  - timings.

All existing results are existence results. This file turns them into an algorithm with a proved running time. It adds
no new existence result.

## 1. The result

An instance has n ≥ 1 agents, m goods and additive valuations with natural-number values v_i(g) (the model of
`lean/EFX/Model.lean`; rational values reduce to it by scaling, real values by the remark at the end of §3).
R_i = {g : v_i(g) > 0}.

**Theorem K3ALG.** There is an algorithm that, given any instance with n ≥ 1 agents in which |R_i| ≤ 3 for every
agent i, returns an EFX₀ allocation. On every instance (whatever |R_i|) it performs at most 400·(n + m + 1)⁴
elementary operations, in the cost model of §6. More precisely, it performs O(n⁴ + n²m) of them (§5; Lean
`EFX.K3.algoC_cost_fine`).

In Lean (`lean/EFX/K3Cost.lean`, `lean/EFX/K3CostBound.lean`), with the model's primitives only:

    def algo (I : Inst) (hn : 0 < I.n) : I.Alloc := (algoC I hn).val
    theorem algo_efx0 (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) : I.EFX0 (algo I hn)
    theorem algoC_cost (I : Inst) (hn : 0 < I.n) : (algoC I hn).cost ≤ 400 * (I.n + I.m + 1) ^ 4
    theorem algoC_cost' (I : Inst) (hn : 0 < I.n) : (algoC I hn).cost ≤ 6400 * (I.n + I.m) ^ 4

`algo` takes the proof `hn : 0 < I.n` as an argument: when n = 0 and m > 0 the type `Fin m → Fin 0` of allocations is
empty, so no function `Inst → Alloc` exists. `algoC I hn : Timed I.Alloc` is the algorithm written in a cost monad
(§6). Its value is the allocation and its `cost` is the number of counted operations along the evaluation. `algo`
is defined as that value, so the bound is about the program that computes the allocation.

## 2. The algorithm

Lists are in index order, and "the first" means the smallest index. The Lean names of each step are in brackets.

```
K3ALG(n, m, v):                                                     [EFX.K3.algoC; spec EFX.K3.algoSpec]
  A ← [0, …, n−1];  M ← [0, …, m−1];  peeled ← []
  Stage R: peel by rule R1                                          [reduce, reduceC]
    loop
      if |A| ≤ 1: the agent of A takes all of M; go to OUTPUT
      if M = []: go to OUTPUT
      for the first i ∈ A such that R1STEP(i) ≠ fail:               [findR1, r1Step]
        remove i from A
        if R1STEP(i) = (take p): peeled ← peeled + (i, p); remove p from M
        continue loop
      exit loop (R1 applies to no agent)
  Stage L: LB⁺ on (A, M)                                            [lbStage, lbPlusC]
    for i ∈ A: (a_i, b_i, c_i) ← the goods of M that i values,
        sorted by v_i, largest first, ties in index order           [profileOf, sort3; profTabC]
    order ← R1ORDER(A, M)                                           [LB.r1Order]
    X_L ← LB⁺(a, b, c, A, M, order)                                 [LB.lbPlus]
  OUTPUT: each peeled good goes to its agent; every other good as Stage R or Stage L placed it

R1STEP(i):   (on the current M)
  p ← the first good of M with the largest v_i(p)                   [EFX.favorite]
  if v_i(p) = 0: return (take nothing)                              (rule R1 with P = ∅)
  if v_i(M − p) ≤ v_i(p): return (take p)                           (rule R1)
  return fail

R1ORDER(A, M):   Phase 1's processing order with R1 priority
  pool ← M;  rem ← A;  order ← []
  while rem ≠ []:
    i ← the first agent of rem with at most two of a_i, b_i, c_i in pool; else the first agent of rem
    order ← order + i;  remove i from rem;  remove i's favourite remaining good (first of a_i, b_i, c_i in pool)
  return order

LB⁺(a, b, c, A, M, order):                                          [LB.lbPlus; proofs/lb_last_step.md §6]
  Phase 1: in `order`, each agent picks the first of a_i, b_i, c_i still available (or nothing)
                                                                    [phase1; table Y]
  Upgrades: U ← [];  J ← goods nobody picked                        [lbUp, upgrades]
    repeat: k ← the first agent of A with k ∉ U, pick b_k, c_k ∈ J, b_k ∉ NA(U)
            (NA(U) = goods that some agent outside U ranks above its pick)
            if none: stop;  U ← k :: U;  J ← J − c_k
  J ← junk (goods that are no pick and no c_u, u ∈ U); cap(k) = 0 if k ∈ U or k's pick ∈ NA (frozen),
    2 if k has no pick, 1 otherwise; S = Σ cap                      [junkList, cap, slotSum]
  if |J| ≤ S: return COMPLETE(no owner, H = [])
  r ← the last agent of `order` not in U                            [lastOut]
  E ← agents x ≠ r, x ∉ U, with pick a_x, and b_x, c_x each in J or picked by r      [exposedL]
  H ← HITSET(J, E)                                                  [hitSet, meet]
  if |H| ≤ S − cap(r): return COMPLETE(owner r, H)                  (the exact owner test, §4)
  k ← the first agent of E in r's block                             [kstar; blocks: blkAux]
      (block of an agent = number of insertion steps, i.e. turns of agents with all three goods available, up to its turn)
  if there is none: return COMPLETE(owner r, H)                     (never happens: Theorem A)
  chain ← scan the agents after k in `order`; append each agent j ∉ U that ranks the current agent's pick above
          its own, while the current agent is frozen                                 [chainFrom]
  rotate: each agent of the chain takes its predecessor's pick; k takes b_k and c_k; U ← k :: U     [rotPicks]
  recompute J, cap, S for the rotated state
  if |J| ≤ S: return COMPLETE(no owner, [])
  return COMPLETE(owner k, HITSET(J, E_k))

HITSET(J, E):
  if two agents x ≠ y of E (the first such pair in E's order) have a common junk good g in {b_x, c_x} ∩ {b_y, c_y}:
    return g, then for every other z ∈ E the first of b_z, c_z that is junk
  return for every z ∈ E the first of b_z, c_z that is junk

COMPLETE(o, H):                                                     [complete, fill]
  picks go to their pickers; c_u goes to u ∈ U;
  the junk, in the order H followed by J − H, fills the slots of the agents other than o in index order
  (cap(k) goods to k); the junk that is left goes to o
```

The Lean program `algoC` performs these steps literally: its value lemma `EFX.K3.algo_eq_spec` says that it computes
`algoSpec`, the composition of the existing definitions (`EFX.K3.reduce`, `EFX.LB.r1Order`, `EFX.LB.lbPlus`). It
differs from them only in that it stores in arrays the functions those definitions recompute: the rankings, Phase 1's
picks, the blocks, the slots, the rotated picks, and the output.

## 3. Correctness

Every step is a proved construction; nothing new is needed.

1. **Stage R.** Let i leave with p, where v_i(p) ≥ v_i(M − p). If the remaining agents have an EFX₀ allocation of
   M − p, adding (i, {p}) keeps it EFX₀. This is rule R1 (ledger L2; `EFX.peel`). If v_i(p) = 0, then i values no
   remaining good and leaves with nothing (rule R1 with P = ∅; `EFX.peelEmpty`). One agent taking everything is
   EFX₀ vacuously. By induction on the number of agents: `EFX.K3.reduce_sound`.
2. **When Stage R stops** with at least two agents and some goods, R1 applies to no agent.
   - It fails for the favourite p. Then it fails for every good q: v_i(M − q) = v_i(M) − v_i(q)
     ≥ v_i(M) − v_i(p) > v_i(p) ≥ v_i(q) (`EFX.K3.r1Step_eq_none`).
   - Hence every agent has at least three relevant goods in M, and 2v_i(g) < v_i(M) for every g (`EFX.not_R1`).
   - With |R_i| ≤ 3, every agent has exactly three relevant goods in M and is strictly balanced
     (a_i < b_i + c_i).
   - Goods that no remaining agent values may be left. The CORE reduction would remove them (rule L3) and would peel
     agents with two private goods (rule R2). LB⁺ needs neither:
     - its Theorem C (`proofs/lb_last_step.md` §6) holds for every instance in which each agent values exactly
       three goods and is balanced;
     - its Remark 3 notes that the proof uses neither that every good is valued, nor the private-good condition,
       nor connectivity.
3. **Stage L.** `sort3` returns the agent's three goods sorted by value, with a ≥ b ≥ c > 0 and a ≤ b + c
   (`EFX.K3.sort3_ranking`). So the valuation is consistent with the computed ranking profile, and that profile is
   well formed. `r1Order` is a processing order with R1 priority (`EFX.LB.r1Order_spec`). Theorem C then holds:
   for every such order, LB⁺'s output is a complete EFX₀ allocation with at most one bundle of more than two goods
   (`EFX.LB.lbPlus_sound`, ledger S2.LB+). Lean: `EFX.K3.lbStage_sound`.
4. Together: `EFX.K3.algoSpec_efx0`. With `EFX.K3.algo_eq_spec`: **`EFX.K3.algo_efx0`**.

The theorems cited were proved before this workstream: L2 is PROVED with Lean, and so are S2.R, S2.LB+ and D (PR #18).
This workstream adds only the computable rankings, the peeling loop and its induction, the counted program, and its
agreement with the specification.

*Remark (real values). The comparison-model form is machine-checked (`lean/EFX/K3Real.lean`, ledger K3.ALG.REAL;
see the end of this remark); the first two points are written, not machine-checked.*
- Every decision of the algorithm compares two subset sums of one agent's values:
  - relevance, 0 < v_i(g);
  - the favourite, v_i(g) ≤ v_i(h);
  - v_i(p) = 0;
  - rule R1, v_i(M − p) ≤ v_i(p);
  - the three comparisons of `sort3`.
- For nonnegative real values v, L12 (`proofs/real_values.md`; Lean `EFX.l12`) gives natural-number values w that
  answer every such comparison in the same way. So the run on v is the run on w and returns the same allocation.
  That allocation is EFX₀ for w by the theorem, hence for v (`EFX.efx0_iff_of_agree`).
- The algorithm therefore works verbatim on real inputs in the real-RAM model, where a comparison or an addition of
  two reals costs one unit.
- *In Lean* (`EFX.K3.algoOrdC`, `EFX.K3.algoOrd`): the program computes w itself with a comparison oracle
  `le : V → V → Bool` over any `EFX.OrderedValue` type V (e.g. ℝ≥0) and then runs `EFX.K3.algoC` on w. Per agent it
  asks v_i(g) ≤ 0 for every good (its relevant goods, in index order), then the twelve basic comparisons of the
  values of its first three relevant goods (`EFX.Pat`), and takes the first row of the 31-row table `EFX.Pat.reps`
  with that pattern (`EFX.K3.surrogate`; L12 made constructive, `EFX.K3.agree_surrogate`). Correctness,
  `EFX.K3.algoOrd_efx0`: for a correct oracle, nonnegative values and |R_i| ≤ 3, the output is EFX₀ for v. Cost,
  `EFX.K3.surrogateC_cost` and `EFX.K3.algoOrdC_cost`: n(m + 12) oracle calls and at most
  n(m + 12) + 10nm + 971n + 400(n + m + 1)⁴ counted operations in all (with the finer bound,
  `EFX.K3.algoOrdC_cost_fine`). w is stored as an n × m table, read at unit cost as the input is. The statement that
  the run on v itself makes the same decisions as the run on w (the first two points) is not formalized.

## 4. The owner test (the known issue), resolved

**The issue.** LB⁺ gives the large bundle to r if r is a *valid owner* (Lemma 1 of `proofs/lb_last_step.md`):
- some set H of junk goods with |H| ≤ S − cap(r) meets π_x = {b_x, c_x} ∩ J for every exposed agent x ∈ E_r;
- no pair {b_x, c_x} lies in r's base, which always holds for r (§4 of that file).

In general, deciding whether such an H exists is a minimum-vertex-cover question on the graph whose vertices are the
junk goods and whose edges are the sets π_x, each of at most two goods. Vertex cover is NP-hard in general.
Remark 2 of `proofs/lb_last_step.md` calls the minimum "easy here" without an argument. `src/lbplus.c` computes it
by brute force.

**Resolution.** For the owner r of LB⁺ the test is exact and needs no minimum.

**Proposition O.** Let the state be LB⁺'s state after Phase 1 (any order with R1 priority) and the upgrades (any
order), with ω = |J| − S ≥ 1, and let r and E = E_r be as in §2. Then r is a valid owner iff

  |E| ≤ S − cap(r),  or some two agents x ≠ y of E have π_x ∩ π_y ≠ ∅.

In either case `HITSET(J, E)` is a witness. Checking the condition takes O(|E|² + m) steps with a junk flag per good
(O(|E|²·m) as formalized, where `meet` tests membership in J; §5), or O(|E| + |J|) with an index from goods to
agents (`k3/k3algo.py`, `fast`).

*Proof.*
- (a) *Theorem A's counting.* S − cap(r) ≥ |E ∖ B*| ≥ |E| − 1, where B* is r's block. The first inequality is shown
  in the proof of Theorem A (`proofs/lb_last_step.md` §4):
  - by (A3), the exposed agents are leaders of distinct blocks;
  - for x ∈ E ∖ B*, the ends τ(x) of need chains are distinct terminals outside B*, so distinct from r, each with
    cap ≥ 1.

  The second holds because, by (A3), at most one exposed agent (k*) lies in B*.
- (b) *Hitting sets of E's pairs.* Every π_x is nonempty: at most one of b_x, c_x is r's pick (the pair would
  otherwise lie in r's base). Let τ be the smallest size of a set of junk goods meeting every π_x.
  - τ ≤ |E|: take one good per set.
  - τ ≤ |E| − 1 iff two of the sets meet. If g ∈ π_x ∩ π_y, then g together with one good of each other π_z hits
    everything. Conversely, if the sets are pairwise disjoint, a hitting set contains a different good of each set.
- (c) r is valid iff τ ≤ S − cap(r).
  - Both disjuncts suffice:
    - |E| ≤ S − cap(r) gives τ ≤ |E| ≤ S − cap(r);
    - two meeting sets give τ ≤ |E| − 1 ≤ S − cap(r), by (b) and (a).
  - Conversely, if no two sets meet, then τ = |E| by (b), so τ ≤ S − cap(r) gives the first disjunct.
- (d) In both cases `HITSET(J, E)` has exactly the size used above: |E| − 1 goods if a pair meets, |E| otherwise. ∎

Lean: `EFX.LB.validOwner_iff` (`lean/EFX/OwnerR.lean`, PR #18) is Proposition O with
`ValidOwner w := ∃ H, OwnerOK … w H` (Lemma 1's condition for *some* H) and the test `|hitSet| ≤ S − cap(r)`. The
counting (a) is `EFX.LB.hitSet_fits`. So `lbPlus` already used the exact test, and `algo` inherits it.

After the rotation no test is needed. By Theorem B (g), every agent exposed for k* has a junk good in its pair, and
one good per exposed agent fits the slots. So `HITSET` fits (`EFX.LB.theoremB`).

What stays open is only the general question, which LB⁺ never asks: for an *arbitrary* owner o, as in LB's owner
search, the test is a vertex-cover question on the π-graph, and we do not know whether it is hard on the graphs that
occur. `k3/k3algo.py` asserts inequality (a) on every run in which LB⁺ reaches the owner test (EVIDENCE for the
implementation; the inequality itself is proved).

**The simpler test is not enough** (`attempts/k3-owner-test-no-shared-good.md`). Testing only |E| ≤ S − cap(r),
one junk good per exposed pair without sharing, rejects valid owners outside Theorem A's bad case. LB⁺ would then
rotate outside the bad case, where Theorem B does not apply. That file records the smallest configuration found.

## 5. Running time

**Theorem (Lean, `EFX.K3.algoC_cost`).** For every instance with n ≥ 1 agents and m goods, `algoC` performs at most
400·(n + m + 1)⁴ counted operations. No hypothesis on |R_i| is needed.

The proof bounds every counted step with one number N = n + m + 1 that exceeds the length of every list the program
builds. The facts used:
- the agents left, the upgraded agents (plus k*), the exposed agents, the need chain and the order have at most
  n + 1 elements;
- the goods left, the junk and the pools have at most m;
- the placement list H ++ (J − H) has at most n + m.

The degree-4 term comes from one loop:

| step | counted cost (Lean bound, N = n + m + 1) | finer (per step written; the total is `EFX.K3.algoC_cost_fine`) |
|---|---|---|
| Stage R: ≤ n rounds, each testing R1 for every agent (favourite, erase, value over M) | 15·N² per round | O(n²m) |
| rankings (table over agents: relevant goods, `sort3`) | 14·N² | O(nm) |
| R1ORDER: ≤ n steps, each scanning the agents for one with ≤ 2 goods left (3 membership tests in the pool) | 15·N³ | O(n²m) |
| Phase 1's picks (table: each entry replays Phase 1 up to the agent) | 17·N³ | O(n²m) |
| **upgrades**: ≤ n rounds × n agents × (NA of one good: n agents × membership in U) | **36·N⁴** | **O(n⁴ + n²m)** |
| junk, slots (table: n × NA), sums | 8·N² + 21·N³ + … | O(nm + n³) |
| owner test: exposed agents, `meet` (pairs of E × membership in J), `hitSet` | 20·N² + 24·N³ | O(n²m) |
| blocks (table), k*, need chain (≤ n agents × frozen test O(n²)), rotated picks | 31·N³ + 34·N³ + … | O(n²m + n³) |
| rotated state, second owner test (`meet` again), completion (≤ m goods × (picker, upgraded, `fill`)) | 21·N³ + 24·N³ + 19·N² + … | O(n²m + n³) (earlier written as O(n³ + nm); corrected below) |
| output table (m goods × lookup among ≤ n peeled goods) | 4·N² | O(nm) |

Summing the finer column gives O(n⁴ + n²m) for the formalized program.

**Theorem (Lean, `EFX.K3.algoC_cost_fine`, `lean/EFX/K3CostFine.lean`).** For every instance with n ≥ 1 agents and m
goods, `algoC` performs at most n⁴ + 20n³ + 25n²m + 124n² + 47nm + 119n + 22m + 3 counted operations; hence at most
145n⁴ + 72n²m + 119n + 22m + 3 (`algoC_cost_fine'`) and at most 270(n⁴ + n²m) (`algoC_cost_fine''`).

The proof re-bounds every stage with a bound a = n on the lists of agents (a + 1 for the upgraded agents after the
rotation) and b = m on the lists of goods. The upgrade loop gives n⁴ + 17n³ + n²m + … (`EFX.K3.lbUpC_cost_fine`). One
row of the table above is corrected by the formalization: in "rotated state, second owner test, completion" the
second owner test runs `hitSet`, hence `meet` (pairs of exposed agents × membership in the junk), which the program's
loops bound by 2n²m, as in the first owner test's row; that row is O(n²m + n³), not O(n³ + nm). The total is
unaffected.

*A faster implementation (written; EVIDENCE for its speed).* `fast` in `k3/k3algo.py` computes the same allocation
(checked against the Lean `#eval` and the transcription `mirror`, §7) with worklists and counters:
- Stage R keeps a heap of the agents R1 applies to. Under the hypothesis, R1 keeps applying once it applies:
  removing a good other than the favourite lowers the rest; removing the favourite leaves at most two goods. So only
  the valuers of a removed good need a new test.
- R1ORDER keeps a heap of the non-full agents.
- The upgrades keep the counts |{i ∉ U : g ranked above i's pick}| per good and a heap of candidates.
- `meet` uses an index from junk goods to the exposed agents.

After reading the input (the goods each agent values), this takes O((n + m) log n) operations. Reading a dense
input takes O(nm), a sparse one O(n + m). This analysis is written, not machine-checked.

## 6. The cost model (what is counted, what is abstracted)

`EFX.Timed` (`lean/EFX/Timed.lean`) is the cost monad:
- `Timed α` pairs a value with a natural number;
- `tick k` adds k;
- `bind` adds the costs of the steps actually evaluated.

Programs are written in this monad, and each has a *value lemma* saying that it computes the existing definition.
Examples:
- `EFX.K3.hitSetC_val : (hitSetC P J E).val = hitSet P J E`;
- `EFX.K3.lbPlusC_val : (lbPlusC …).val = lbPlus …`;
- `EFX.K3.algo_eq_spec`.

The cost lemmas bound `cost`. The cost is therefore the cost of the very program whose value is the allocation, not
of a separately written cost function.

**Counted, one unit each:**
- one step of a list traversal (a cell visited by map, filter, any, find, a sum, length, append, take, drop, or by
  the recursions of Phase 1, the blocks, the chain, the rotation, `fill`, `lastOut`), together with the comparison
  done there (membership, erase);
- one comparison of two agents or two goods;
- one read of the input v_i(g);
- one comparison or addition of two natural numbers (values, counters);
- one read of a *table*: the rankings a_i, b_i, c_i, the picks, the blocks, the slots.

**Tables.** A table is an array filled once (`EFX.Timed.mkTable`, `Array.ofFn`). Filling it costs its entries'
evaluations plus one unit per entry, and each read is one unit (the RAM model; Lean's runtime reads arrays in
constant time).

**Straight-line code.** Code with a bounded number of the above operations is charged by one `tick k`, with k at
least that number. Each such tick is annotated in `lean/EFX/K3CostLB.lean` and `lean/EFX/K3Cost.lean`; for example,
a rank costs 6 (three table reads and three comparisons).

**Abstracted (not counted):**
- building pairs, options and list cells that a counted step produces, and pattern matching on them;
- Boolean connectives on computed Booleans: at most a constant number per counted step;
- building closures;
- the size of numbers: an addition or comparison of arbitrary natural numbers counts as one unit. In a bit model,
  multiply by the bit length of the largest sum, at most b + log₂ m for b-bit values.

**The input.** The model's instance is a function v : Fin n → Fin m → ℕ, and each value read costs one unit (the
input as an n × m matrix).

The bound 400·(n + m + 1)⁴ is not tight. For random instances the count of `algoC` is below 0.4·(n + m + 1)⁴
(`results/k3_lean_crosscheck.log`: the ratio falls from 0.38 at n = 2 to 0.002 at n = 30).

## 7. Computations (evidence, not proof)

All logs are under `results/`, with their commands.

| log | what | result |
|---|---|---|
| `k3_cross.log` | 200,000 random instances (n ≤ 9): balanced three-good instances, arbitrary instances with ≤ 3 relevant goods, few-level values; `mirror` (literal transcription of the Lean definitions) vs `fast` | identical outputs; every output EFX₀ by two raw checks |
| `k3_lean_crosscheck.log` | 675 instances, including 62 on which LB⁺ rotates and random cores with n up to 30; Lean `#eval` of `EFX.K3.algo` vs `mirror` vs `fast` | identical outputs; every Lean output raw EFX₀; every operation count ≤ 400·(n + m + 1)⁴ |
| `k3_certs_5_6.log` | every ranking profile of every certified core of `certs_5_6` (251 cores, 11,127,456 profiles, 3 balanced realizations each) | 0 failures; 5,474 rotations; the three realizations always give the same allocation (the algorithm is ordinal on cores) |
| `k3_certs_2_6.log` | every ranking profile of every core with n ≤ 6, connected or not (`certs_lb_2_6`, `certs_lb_disconnected_4_6`: 3,567 cores, 152,071,632 profiles) | 0 failures; 395,038 rotations; `mirror` = `fast` on every 1,000th profile |
| `k3_certs_7_sample.log`, `k3_certs_8_sample.log` | 100 (n = 7) and 30 (n = 8) random ranking profiles of every certified connected core (41,170 and 12,763 cores) | 0 failures; 3,625 and 84 rotations |
| `k3_timing.log` | `fast` on random instances with n up to 10⁵ agents (three families), `mirror` up to n = 80 | every output raw EFX₀; `fast` = `mirror` wherever both ran; times in §7.1 |

Every output in these runs is checked against the raw EFX₀ definition. For i ≠ j, the largest v_i(X_j ∖ {g}) over
g ∈ X_j is v_i(X_j) minus i's smallest value in X_j (0 if X_j holds a good i does not value). A literal
triple-loop check runs on the random instances as well.

### 7.1 Timings

`results/k3_timing.log` (`python3 k3/timing.py --max-n=100000 --mirror-max-n=80 --reps=3 --seed=1`): median seconds
of three instances, Python 3.11, one CPU. The three families:
- core: m = 1.5n, LB⁺ does the work and usually needs no owner;
- core2m: m = 2n, LB⁺ usually gives an owner;
- general: 0–3 goods per agent, and Stage R peels most agents.

| n | core | core2m | general | `mirror` (core2m) |
|---|---|---|---|---|
| 80 | 0.0006 | 0.0007 | 0.0004 | 0.30 |
| 1,000 | 0.0073 | 0.0074 | 0.0051 | – |
| 10,000 | 0.082 | 0.089 | 0.062 | – |
| 100,000 | 1.53 | 1.58 | 0.84 | – |

- `fast` grows about linearly: the log-log slopes between consecutive sizes are 1.0–1.4, consistent with
  O((n + m) log n).
- The literal transcription `mirror` of the Lean definitions grows with slopes 2–3 on these instances, below its
  worst case O(n⁴ + n²m).
- An earlier version of `fast` was quadratic on the core2m and general families (40 s at n = 10⁵). It rebuilt a set
  for every junk good in `complete` and prepended to a list at every upgrade. The fix does not change any output
  (`k3algo.py --cross`, `k3/lean_crosscheck.py`).

This is evidence about the implementations, not part of any theorem.

## 8. Comparison with the local search LS2 (Track B)

The coordinator asked, for the owner, to explore both algorithms: LB⁺ (this file) and the local search LS2 of
`proofs/local_search.md` §4. The review of LS2 is `proofs/ls2_referee.md`.

| | K3ALG (LB⁺) | LS2 |
|---|---|---|
| proof of correctness | Theorems 1′, A, B, C of `proofs/lb_last_step.md`: two written reviews, machine-checked (PR #18), plus this file's reduction (R1 only) | Theorem C of `proofs/local_search.md`: one written review (`proofs/ls2_referee.md`, no error found), brute force (`k3/ls2_referee.py`), not machine-checked (ledger LS3 CONJECTURE) |
| what it needs from the instance | every agent values three goods and is balanced; goods nobody values allowed; any number of private goods; so only R1 in front | a core: L4's m ≤ 2n is used in Claim 2 (g), so the full CORE reduction (L3 with envy-cycle elimination, R1, R2) in front |
| hardest step | the owner test, polynomial by Proposition O (`hitSet`; no vertex cover) | the augmented envy cycle (Claim 3) and Phase 2's maximum matching (Claim 4) |
| number of main steps | one pass (Phase 1, upgrades, ≤ 1 rotation) | ≤ 7n Phase-1 steps (Σℓ rises) |
| running time | formalized program: ≤ 400·(n + m + 1)⁴ (Lean); O(n⁴ + n²m) (written); `fast`: O((n + m) log n) after the input (written) | O(n²(n + m)) per core (written, `proofs/ls2_referee.md` remark 1, `k3/ls2.py`) |
| measured on the same random cores (`results/k3_ls2_compare.log`, Python, `fast` vs `k3/ls2.py`) | 0.0072 s at n = 1,000, 0.040 s at n = 5,000 (slope ≈ 1) | 2.9 s at n = 1,000, 90 s at n = 5,000 (slope ≈ 2; about 2.1n Phase-1 steps, each O(n + m) here) |
| output shape | EFX₀, ≤ 1 bundle of > 2 goods (on the core part) | EFX₀, ≤ 1 bundle of > 2 goods |
| Lean | done: `EFX.K3.algo`, `algo_efx0`, `algoC_cost` | not started; handed to a second session (PR #54 comment, with a plan) |

*Which is simpler to formalize.* K3ALG was: its correctness reused the existing Lean proof of LB⁺ unchanged. The new
work was a counted program with value lemmas, computable rankings and the peeling loop, and the cost bounds.

LS2 would need a new development:
- partial allocations with a pool;
- the envy graph and its paths;
- the closed walk of Claim 3;
- maximum matchings with the no-augmenting-path argument of Claim 4;
- a computable CORE reduction with L3's envy-cycle elimination (its rotations are bounded by the sum of levels,
  ≤ 7n);
- R2.

Its arguments are local and elementary, and its termination measure (Σℓ ≤ 7n) is simple. So it is a reasonable
second target, and an independent machine-checked route to D and TARGET.

LS2's Phase 2 does use a maximum matching, which is polynomial for sure. But K3ALG's owner test is polynomial too
(Proposition O), so the vertex-cover concern does not separate the two algorithms.

## 9. Summary for the ledger

- **K3.ALG** (PROVED, Lean `EFX.K3.algo_efx0`, `EFX.K3.algo_eq_spec`, `EFX.K3.algoSpec_efx0`): K3ALG returns an
  EFX₀ allocation of every instance with n ≥ 1 agents and |R_i| ≤ 3 (natural-number values).
- **K3.ALG.TIME** (PROVED, Lean `EFX.K3.algoC_cost`): K3ALG performs at most 400·(n + m + 1)⁴ counted operations,
  in the cost model of §6.
- **K3.ALG.FINE** (PROVED, Lean `EFX.K3.algoC_cost_fine`): at most n⁴ + 20n³ + 25n²m + 124n² + 47nm + 119n + 22m + 3
  counted operations, O(n⁴ + n²m) (§5).
- **K3.ALG.REAL** (PROVED, Lean `EFX.K3.algoOrd_efx0`, `EFX.K3.algoOrdC_cost`): K3ALG on real values (any
  `EFX.OrderedValue`) in the comparison model, via L12's surrogate computed with n(m + 12) oracle calls (§3).
- **K3.OWNER** (PROVED; Lean `EFX.LB.validOwner_iff`, `EFX.LB.hitSet_fits`): Proposition O. The owner test of LB⁺ is
  exact with `hitSet` and needs no minimum vertex cover.
- **K3.ALG.RUN** (EVIDENCE): the computations of §7.
- **K3.LS2** (CONJECTURE): LS2 runs in polynomial time, O(n²(n + m)) per core (written). Its correctness is LS3
  (CONJECTURE), refereed in `proofs/ls2_referee.md` with no error found, but not machine-checked.
- **K3.LS2.RUN** (EVIDENCE): the brute-force referee of LS2 (`k3/ls2_referee.py`).
- Not claimed:
  - the O((n + m) log n) implementation (written, §5);
  - the part of the real-value remark of §3 that the run on v itself makes the same decisions as the run on w;
  - the complexity of the owner test for arbitrary owners (open, not needed).
