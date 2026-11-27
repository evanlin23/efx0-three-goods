# Splicing a REC-S repair into one round: the exception occurs (workstream `proof/kgen-rounds`)

**Idea.** Theorem REC-S (`k4/oc1max_multi.md` §12) repairs a start with two sequential moves:
1. the earliest-wanter chain E(k), in which k takes a pool pair T;
2. a Theorem S chain P₂ in the reduced instance.

On all REC-S witnesses of the n = 4 export, the final allocation is a round of OC₁′ moves from the picks. So the hope
was a lemma saying that every REC-S repair is one round of OC₁′ moves. Then a proof of REC-S existence would prove
ROUND-P (`kgen/rounds.md` §4.10).

**What survives: Lemma SPLICE** (§4.10; proof written here, not refereed). A REC-S repair is a round of OC₁′ moves,
except in configuration (EX).
- In (EX), the agent q that holds no pick in X (k, or P₂'s start u₀) has its pick in the bundle of an agent v that also
  keeps its own pick.
- And v needs its own pick: v_v(X_v ∖ {Y_v}) ≤ v_v(Y_v).

**Where the exception breaks it.** (EX) occurs: 49 of 4,616 REC-S repairs on random strict connected n = 4, 5 cores
(`splice_search_random_*.log`). All 49 are in an (EX) configuration: 48 of form EX-b and 1 of form EX-c. No failure lies
outside (EX), as the proof predicts.
- Every exception is at a start where OC₁ already holds, so ROUND-P holds there anyway, through other allocations.
- At the starts that matter, those with no one-move repair, there is no exception: 265,549 REC-S repairs at n = 4
  (112,880 starts) and n = 5 (280 + 23,943 starts).

**Smallest configuration** (n = 4, m = 7, EX-b; `kgen/rounds/splice_ex.py`, `results/kgen_rounds/splice_ex.log`):

| agent | g0 | g1 | g2 | g3 | g4 | g5 | g6 |
|---|---|---|---|---|---|---|---|
| 0 | 0 | 2289 | 1831 | 2530 | 0 | 1934 | 0 |
| 1 | 0 | 836 | 0 | 2963 | 0 | 2033 | 642 |
| 2 | 0 | 1387 | 1223 | 2254 | 0 | 0 | 1149 |
| 3 | 1362 | 0 | 271 | 0 | 72 | 1386 | 0 |

- Order (2, 0, 3, 1) gives picks (1, 6, 3, 5); the junk is {0, 2, 4}.
- The REC-S witness, accepted by `check_recs.py`:
  - E(3) = (3, 1), with agent 3 taking T = {0, 4}; this releases Y₁ = 6;
  - P₂ = (2, 1), with agent 2 taking {2, 6} and agent 1 receiving 3;
  - the head's good 5 = Y₃ is the kept-out h, and it goes to agent 0;
  - X = ({1, 5}, {3}, {2, 6}, {0, 4}), which is raw EFX₀.
- Why X is not a one-round witness:
  - Agent 3 holds no pick, and its pick 5 lies with agent 0, which keeps its pick 1.
  - So 3 → 0 is forced, and agent 0 is a chain end whose own pick stays outside.
  - Its gain would need v₀(5) = 1934 > v₀(1) = 2289, which fails.
  - Two rounds do reach X: the hand-off 3 → 1 releases Y₁, then the swap.

**Reproduce.**
```
python3 kgen/rounds/splice_ex.py
python3 kgen/rounds/splice_search.py random 4,7,3000,2 1 200 3      # 26 exceptions, all at starts where OC1 holds
```
