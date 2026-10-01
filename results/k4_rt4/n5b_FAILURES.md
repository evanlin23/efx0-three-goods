# DL_RT4 failures on the n = 5 cores with four 4-good agents (compute/k4-rt4-n5b)

EVIDENCE: the output of `k4/dlrt4_run.py` (dlrt4.c sha256 `fcde494a3161279d47a7b80e614f69c58894ebc7b40d00e461f677b8810d7cae`), every
failing state confirmed with the Python reference `k4/dlrt4_ref.py`. Conjecture DL_RT4: at f ≥ 1, every min-frozen P with def(P) > 0 has a
min-frozen neighbour P′ with def(P′) < def(P) under RT4 = T1 ∪ T2 ∪ T3 ∪ T4 (`k4/dlrt4.c`'s header, `k4/dl2.md` §3,
`results/k4_dl13/n4_FAILURES.md`). The ledger is not edited here; what follows is for the coordinator of compute/k4-rt4 and the proof
workstream to weigh.

**Status: written while run n5b_4 was still running** (`k4_certs_5_n4_4`, 16,000 random profiles per core, seed 1). The counts below cover the
failures found up to then; `n5b_SUMMARY.md` gives the final counts of the whole slice.

## The failures

| run | core (file, pos, idx, m) | sets | profile | values | failing state P | f | def(P) | nearest k |
|---|---|---|---|---|---|---:|---:|---:|
| n5b_4 | `k4_certs_5_n4_4`, 3206, 364, 9 | [[0,2,4,7],[1,4,7,8],[3,6,8],[5,6,7,8],[5,6,7,8]] | 108,86,1,108,27 | [[6,3,5,7],[4,2,8,7],[2,4,3],[4,8,1,6],[2,7,8,4]] | ({7}, {8}, {3}, {5}, {6}) | 3 | 1 | 3 |
| n5b_4 | `k4_certs_5_n4_4`, 3521, 679, 9 | [[0,2,3,7],[1,6,8],[3,5,7,8],[4,5,6,8],[4,6,7,8]] | 98,1,16,17,15 | [[5,6,4,8],[2,4,3],[2,4,8,7],[2,4,10,7],[2,4,8,5]] | ({7}, {1}, {8}, {5}, {6}) | 3 | 1 | 3 |
| n5b_4 | `k4_certs_5_n4_4`, 3521, 679, 9 | (same) | (same) | (same) | ({7}, {1}, {8}, {4,5}, {6}) | 3 | 1 | 3 |

The profile is given as indices into `check4.core_domains(sets, m, False)` (as in the dump), and the values agent by agent in the order of
its set. The same lines are in `n5b_failures.tsv`, and the dump `dump_n5b_4.jsonl.gz` holds each failing state as a dlrt4.c "D" record
(`"br": "none"`) with every better min-frozen state.

## The shape of the nearest better states

`k4/dlrt4_failures.py` (new, log `n5b_failures_shapes.log`) recomputes each failing state with the suite's model (`k4/suite/model.py`), lists
every better min-frozen state, checks that this set equals dlrt4.c's "better" list in the dump (it does for all three), and gives the shape
of each nearest move with `k4/dl2_relations.py`'s `shape` (U: frozen → free, Z: free → frozen, W: frozen → frozen, Y: free → free).

All three failing states have f = 3, def(P) = 1, NA = {6, 7, 8}, no better state at distance 1 or 2, and 16 better states at distance 3.
**Every one of these 48 nearest moves has the same shape: a chain of frozen goods through one frozen intermediary**, |U| = |Z| = |W| = 1,
Y = ∅, NA unchanged:

- x (frozen in P, U) gives up its frozen good g₁ and becomes free (taking one or two goods of J);
- w (frozen in P and P′, W) takes g₁ and gives up its own frozen good g₂;
- z (free in P, Z) takes g₂ and becomes frozen.

So z does not take x's good itself (the role swap T3 needs P′(z) = P(x) and W = ∅), and x and z change roles (T4 needs every changed agent
frozen in P and in P′). In dl2_relations.py's terms the move satisfies RC ("a chain of frozen goods, |U| = |Z| = 1, plus pure releases") and
R3; no other relation of `dl2_relations.RELATIONS` holds for any better move of these states. It reads as a T3 role swap composed with a
T4 transposition (x → z, then z ↔ w), where the intermediate state is not a better min-frozen state (there is none at distance ≤ 2).

The smallest example, core pos 3206 (idx 364, m = 9) of `k4_certs_5_n4_4`, profile (108, 86, 1, 108, 27):

- agent 0 on goods {0, 2, 4, 7} with values (6, 3, 5, 7); agent 1 on {1, 4, 7, 8}: (4, 2, 8, 7); agent 2 on {3, 6, 8}: (2, 4, 3);
  agents 3 and 4 on {5, 6, 7, 8}: (4, 8, 1, 6) and (2, 7, 8, 4);
- P = ({7}, {8}, {3}, {5}, {6}): min-frozen with f = 3 (agents 0, 1, 4 frozen), NA = {6, 7, 8}, def(P) = 1;
- a nearest better state: P′ = ({0}, {8}, {3}, {6}, {7}), def(P′) = −1: agent 0 gives up 7 for {0} (x), agent 4 moves from 6 to 7 (w), agent 3
  moves from 5 to 6 (z); NA stays {6, 7, 8}. The other 15 nearest states vary x's new base ({0}, {0,2}, {0,4}, {2,4}), the intermediary
  (agent 4 passing 6, or agent 1 passing 8) and z (agent 3, or agent 2 taking 8 or 6).

Core pos 3521 (idx 679) has the same pattern with x = agent 0 (good 7), w = agent 2 (good 8) or agent 4 (good 6), z = agent 3 or agent 1; its
two failing states differ only in agent 3's free base ({5} or {4, 5}).

## Confirmation

`python3 k4/dlrt4_ref.py inst results/k4_rt4/n5b_failures_inst.json` (log `ref_n5b_failures.log`; the inst list is written by
`k4/dlrt4_failures.py --inst`): the reference (model.py + dl2_relations.py + its own T4 test) re-derives all 26 def > 0 states of the two
profiles, agrees with dlrt4.c on every field of every state (0 mismatches, 0 assertions; dl13.c and the -DBIGPP=0 build agree too), and finds
**3 DL_RT4 failures at f ≥ 1**, the three states above.
