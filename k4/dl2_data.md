# DL₂ on data: k* against n, and the shape of the trapped repairs

Workstream `compute/k4-dl2` (PR #70). Ledger rows K4.DL2.KN, K4.DL2.SHAPE (EVIDENCE). EVIDENCE only (PROMPT.md §5
rule 3), except where a short argument is given, and that argument is not refereed. Conjecture DL₂ (K4.STRAT.DL2) is
refuted by the proof workstream's `dl2-n3m7` (K4.DL2.X3, `attempts/k4-dl2-three-agents.md` on `proof/k4-dl2-k1`,
which owns the status change) and independently, at f = 0, by `dl2-rot-n3m7` here (`attempts/k4-dl2-rotation.md`).
This file answers the follow-up questions: does k* stay bounded as n grows, and what do the trapped repairs look like?
The proof workstream (`k4/dl2.md`, `k4/dl2_classify.py`) reads the dumps listed in §6.

## Summary

1. **k* is not bounded: k* = n occurs for every n tested.**
   - n = 2: 8,912 of the 105,120 profiles with ω ≥ 1, exhaustive.
   - n = 3: 52,928 of the 119,640,516 profiles with ω ≥ 1, exhaustive (k* ≤ n always).
   - n = 4: 1,072 profiles of 4 cyclic cores (16 of the 46 cyclic cores run, §3.1), including C_4. In the classes
     run exhaustively, k* ≤ 2: with one 4-good agent (102,434 profiles with ω ≥ 1) and with two (54,488,316). So at
     n = 4 the traps need three or four 4-good agents. In #53's n = 4 and n = 5 gap catalogues (f ≥ 1), k* ≤ 3 and
     k* ≤ 2.
   - The family C_n (§4): one strict profile of one core for each n. k* = n is checked by `k4/dl2.c` for 3 ≤ n ≤ 12,
     and by `k4/suite/model.py` as well for n ≤ 7. A short argument (§4, not refereed) gives it for every n.

   So DL_k fails for every fixed k. In C_n the only repairs of the trap P_n change all n bases: they rotate goods
   around the n-cycle of exposures. A neighbourhood relation R for `EFX.C4min.target4_of_defLocal` (PR #68) must
   therefore contain rotations along exposure cycles of every length as single moves.
2. **The traps (k(P) ≥ 3) come in two shapes**, on every one of the 87,056 traps at n ≤ 3 and the 1,074 found at
   n = 4 (§5):
   - **ROT** (every f = 0 trap; also the two f = 1 traps of the n = 4 catalogues, among their free agents): every
     least-distance repair rotates goods along a cycle of the exposure relation. Each agent takes a good from the base
     of the owner it is exposed to, so transfers follow the exposure edges.
   - **SWAP+FREE** (f ≥ 1): a frozen agent unfreezes and an agent that needed its good takes it (a role swap along a
     need edge). The third agent gives up a good that a role-swap agent values. In some repairs this is a pure
     single-good release (SWAP+REL), in others a swap with the pool or a hand-over to the unfreezing agent.
3. **Pareto-maximal P.** The setting of Lemmas H3 and H7 still has traps: 8,736 Pareto-maximal P at n = 3 need three
   agents. All have a local frozen exposure (H7's class L), and all are role-swap traps. None of the f = 0 rotation
   traps is Pareto-maximal (in `dl2-rot-n3m7` and C_n the rotation is a Pareto-improvement). The 377,832
   Pareto-maximal P with def > 0 at n ≤ 3 equal `k4/hall.md`'s count of not removal-only completable Pareto-maxima
   (`hall.c`, independent code).

## 1. Objects

For a strict profile of a connected k = 4 core with ω ≥ 1 (definitions of `k4/c4x.md` §1, `k4/strategy.md` §3):
- 𝒫, the min-frozen class, and def(P) (removal-only deficit; +∞ only when every agent is frozen);
- the distance between two P: the number of agents whose bases differ;
- k(P) for def(P) > 0: the least distance to a min-frozen P′ with def(P′) < def(P); k* is its maximum over the
  profile, and 0 when no P has def > 0. DL_k is "k* ≤ k";
- nn(P): the distance to the nearest other min-frozen P of any deficit. A P with k(P) ≥ 3 is a **trap**. It is
  **isolated** if nn(P) ≥ 3 (no min-frozen P′ at all within two changes), and **non-isolated** otherwise (neighbours
  exist, none better; `dl2.c`'s counters `ktrap`, `ptrap`);
- the signature of P: the exposure classes w.r.t. its best owners. Free x: H3's e1, e2, e3, or fO when none of them
  fits (possible off Pareto-maxima). Frozen x: H7's G, G1, L, or O. Plus D2 if a frozen agent is exposed w.r.t. two
  free owners (Lemma D(ii)), and PM if P is Pareto-maximal;
- a repair: per changed agent, T (trades a good with another agent), G (grows), S (shrinks) or W (swaps with the
  pool), with base sizes before > after (`k4/dl2.c` header).

## 2. Implementations and checks

- `k4/dl2.c`: everything above, per profile. It copies `k4/gap.c`'s input format and profile loop.
- `k4/suite/deficit_local.py` with `k4/suite/model.py`: the strategy workstream's independent k*.
- `k4/dl2_check.py` compares the two **per P**: bases, deficit, distance, nearest neighbour and the Pareto flag.
  `model.py`'s Pareto flag is computed over all of 𝒫; `dl2.c` scans the min-frozen class.
  - Scope: 34,964 instances, 603,858 min-frozen P, **0 disagreements**.
  - Sources: the suite (148 instances); #53's catalogues at 245040b (every 1st–40th record, n = 2–5, hard hunt);
    random strict profiles of every certified core list with n ≤ 4, and of n = 5 with one 4-good agent.
  - Logs: `results/k4_dl2/check_*.log`.
- `k4/dl2_selftest.py`: the 64-bit build and the hashed neighbour search give output identical to the plain build
  (`selftest.log`).
- `attempts/k4_dl2_rotation.py`: a third, raw re-derivation, used on `dl2-rot-n3m7`.
- Every trap in §5 is re-derived from scratch with `model.py` by `k4/dl2_shapes.py`, which reports 0 mismatches.

## 3. k* against n

| scope | profiles with ω ≥ 1 | k* = 0 | 1 | 2 | 3 | ≥ 4 | k* = n | P with def > 0 | traps: P at distance ≥ 3 (isolated / non-isolated) | log |
|---|---|---|---|---|---|---|---|---|---|---|
| n = 2, every profile (5 cores) | 105,120 | 44,192 | 52,016 | 8,912 | — | — | 8,912 | 171,432 | — | `n3.log` |
| n = 3, every profile (51 cores) | 119,640,516 | 106,103,948 | 13,033,872 | 449,768 | 52,928 | — | 52,928 | 36,739,800 | 87,056 (29,952 / 57,104) | `n3.log`, `n3_part1.log` |
| n = 4, one 4-good agent, every profile (135 cores) | 102,434 | 102,258 | 0 | 176 | 0 | 0 | 0 | 286 | 0 | `n4_1.log` |
| n = 4, two 4-good agents, every profile (309 cores) | 54,488,316 | 54,284,364 | 171,340 | 32,612 | 0 | 0 | 0 | 324,658 | 0 | `n4_2.log` |
| n = 4, cyclic cores (§3.1), 16 of the 46, every profile with top t_i and second x_i | 5,308,416 | 5,221,489 | 80,905 | 4,950 | 0 | 1,072 | 1,072 | | 1,072 (all isolated) | `cycle_n4_part.log` |
| n = 4, #53's catalogues with three or four 4-good agents (every 1st record) and hunts (gap profiles, f ≥ 1) | 245,963 | 227,413 | 18,109 | 439 | 2 | 0 | 0 | 70,333 | 2 (2 / 0) | `n4cat_*.log` |
| n = 5, #53's catalogues and hunts (every record; gap profiles, f ≥ 1) | 134,587 | 128,663 | 5,879 | 45 | 0 | 0 | 0 | 26,632 | 0 | `n5cat_*.log` |
| H₂ of `k4/c4.md` §7 (n = 9, m = 23), §7's values | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 4,939 | 0 | `h2.log` |
| H₂, 100 random strict profiles | 100 | 46 | 54 | 0 | 0 | 0 | 0 | 23,858 | 0 | `h2_rand.log` |
| C_n, 3 ≤ n ≤ 12 (one profile each) | 10 | 0 | 0 | 0 | 1 (n = 3) | 9 | 10 | 10 | 10 (10 / 0) | `cn.log` |

The cyclic n = 4 run was stopped after 16 of its 46 cores to free the CPU for the exhaustive rows (its per-core lines
are in the log; the tables were not written). #53's catalogues hold only gap profiles (f ≥ 1, no frozen-robust key),
so they contain no f = 0 profile, where the rotation traps live.

The largest least deficit over all profiles is 0 in every row, so C₄ᵐⁱⁿ (removal-only) holds on all of them.

### 3.1 Cyclic cores

`k4/dl2_cycle.py N` builds the cores that generalize `dl2-rot-n3m7`. Agents i = 0..n−1 sit on a cycle, and agent i
values {t_i, x_i, t_{i+1}, y_i}, with y_i the shared junk good j or some x_k. There are 7 such cores at n = 3 and 46 at
n = 4 (up to rotation). The script runs every profile whose top is t_i and second good x_i. At n = 3 this finds 294
profiles with k* = 3; the n = 4 results are in the table.

## 4. The family C_n: k* = n for every n

C_n (n ≥ 3) has goods t_0..t_{n−1}, x_0..x_{n−1}, j (m = 2n + 1). Agent i values t_i : 8, x_i : 5, t_{i+1} : 4,
j : 2 (indices mod n), so all agents have the same values. C_n is a connected k = 4 core with strict values: x_i is
agent i's only private good, 8 < 5 + 4 + 2, and the 15 subset sums of 8, 5, 4, 2 are distinct. σ = −1.

**Claim.** f = 0 and ω = 1. P_n = (agent i holds {x_i, t_{i+1}})_i has def(P_n) = 1, and every other min-frozen P
differs from P_n in all n bases. Hence k*(C_n) = n.

*Argument (not refereed).*
- A base is need-free iff no good of R_i outside it is worth more than it. For agent i, a base containing t_i is
  need-free (8 is the top). A base without t_i is need-free iff it is worth more than 8. Among the bases of at most
  two goods, only the pair {x_i, t_{i+1}} (5 + 4 = 9) is; {x_i, j} = 7, {t_{i+1}, j} = 6 and the singletons are not.
- The bases {t_i} form a valid P without needs, so f = 0, the min-frozen P are exactly the P whose bases are all
  need-free, and ω = 0 − σ = 1.
- If agent i holds {x_i, t_{i+1}}, agent i + 1 cannot hold t_{i+1}, so it must hold {x_{i+1}, t_{i+2}}. Around the
  cycle, every agent holds its pair, and the P is P_n. Every other min-frozen P gives every agent a base containing its
  own top, so it differs from P_n in all n bases.
- In P_n, J = {j} and S = 0. An owner bundle must have ω + 2 = 3 goods, so it is B_o ∪ {j}. That bundle threatens
  agent o + 1, which holds 9 and sees t_{o+1} + j = 10 (x_o ∉ R_{o+1}, so nothing is removed). Removing j leaves 2
  goods, so def(P_n) = 3 − 2 = 1 (u = 0, nobody is frozen).
- A P′ with def(P′) ≤ 0: every agent holds {t_i}, J = {x_0, …, x_{n−1}, j}, and owner o takes X = {t_o, x_o, j}.
  Agent o − 1 sees t_o + j = 6 ≤ 8, and agent i sees at most j = 2. So X is safe, |X| = 3 = ω + 2, and def(P′) ≤ 0.
- Every exposure in P_n is H3's e2 with the same label j: a label collision in a cycle of length n. P_n is not
  Pareto-maximal; the rotation in which every agent takes its top improves everyone.

The min-frozen class has 2ⁿ + n·2ⁿ⁻¹ + 1 elements (each agent holds {t_i} or {t_i, x_i}, at most one also holds
{t_i, j}, plus P_n). `k4/dl2_cn.py` confirms the claim with `dl2.c` for n = 3..12, and with `model.py` for n ≤ 7
(`cn.log`). C_4 is core 0 of the cyclic hunt.

## 5. The trapped repairs (k(P) ≥ 3)

`k4/dl2_shapes.py` takes every dumped profile with k* ≥ 3. For each P at distance ≥ 3 it re-derives the min-frozen
class and every deficit with `model.py`, then enumerates all repairs at the least distance. Each repair gets flows,
per-agent labels and a shape:
- **ROT**: no frozen agent among the changed ones, and the goods taken from other changed agents form one directed
  cycle through all of them;
- **SWAP+REL / SWAP+FREE**: a frozen agent unfreezes and an agent that needed its good takes it. Every other changed
  agent only releases goods (REL), or gives up some good valued by a role-swap agent (FREE);
- **OTHER**: anything else.

| data | traps (k) | shapes of the least-distance repairs | log |
|---|---|---|---|
| n = 3, f = 0, every profile | 57,984 (k = 3) | **every** repair is ROT: 1,525,248 repairs, each a 3-cycle with every transfer j → i along an exposure edge (i exposed w.r.t. owner j in P) | `shapes_n3.log` |
| n = 3, f = 1, every profile | 29,072 (k = 3) | **every P has a SWAP+FREE repair** (a role swap along a need edge, chain length 1, plus a third free agent giving up a good a swap agent values); 17,904 also have SWAP+REL (a single-good release); 304 also have OTHER repairs (the third agent trades one of its goods for a good the receiver released) | `shapes_n3.log` |
| n = 4 cyclic cores, f = 0 | 1,072 (k = 4) | every repair is ROT: 94,764 repairs, 4-cycles along exposure edges | `shapes_cycle_n4.log` |
| n = 4 catalogues, f = 1 | 2 (k = 3, isolated) | both have ROT repairs among three free agents (the frozen agent does not change); one also has a SWAP+FREE repair | `shapes_n4cat.log` |
| C_n | 1 per n (k = n) | rotation of the whole n-cycle (§4) | `cn.log` |

Every trap was re-derived by `model.py` with 0 mismatches against `dl2.c` (def and k).

**On the proof workstream's question** (is a trapped repair a role swap of a frozen agent with an agent that needs
its good, propagated along a need chain or threat walk, plus single-good releases by agents next to the chain?):
- With frozen agents, at n = 3, yes in the weak form. Every trap has a role swap of chain length 1 plus one more
  agent that gives up a good the swap agents value. That agent's change is a pure single-good release in 17,904 of
  the 29,072 P; otherwise it swaps with the pool, or hands the good to the unfreezing agent.
- Without frozen agents (f = 0, Theorem Z's case), no. There is nothing to swap. The repair is a rotation along a
  cycle of the exposure relation (a threat walk that closes up), and C_n makes that cycle as long as n.
- Rotations also occur at f = 1 (the two n = 4 catalogue traps), among the free agents.

So a relation R that makes DL_R true must contain at least (i) rotations along exposure cycles of every length and
(ii) role swaps along a need edge together with one freeing change of an adjacent agent. Whether (i) and (ii)
suffice is untested here beyond n = 4.

**All P with def > 0** (`k4/dl2_table.py results/k4_dl2/tables_n3.json`; n ≤ 3, 36,911,232 P, canonical repair):
- 96.4% have a one-agent repair (S shrink 19.4M, W swap with the pool 12.4M, G grow 3.9M), and 3.4% need two agents.
  87,056 need three.
- The 1,237,720 two-agent repairs (canonical witness, roles table (3)) split three ways:
  - a role swap (a frozen agent unfreezes and a free one freezes): 580,534;
  - two free agents: 457,136;
  - two frozen agents exchanging their frozen goods, which changes the key: 200,050.
- At the 377,832 Pareto-maximal P with def > 0 (the same number as `k4/hall.md`'s count of not removal-only
  completable Pareto-maxima with frozen agents at n ≤ 3), the signature contains G for 196,956, L for 113,136, G1 for
  67,740 and e2 for 39,936 of them (a P counts under each of its classes). 8,736 of them need three agents; every one
  has L (H7's local class) in its signature.

## 6. Data for the proof workstream

- `results/k4_dl2/repairs_*.jsonl.gz`: `dl2.c`'s records. They hold every profile with k* ≥ 3, with all its P with
  def > 0, and a sample of k* = 1 and k* = 2 profiles (rates in each log's command). Each P carries:
  - its bases, def, best owners, exposures with classes, signature, Pareto flag, k, nn;
  - the canonical witness (bases, deficit, repair type, roles) and every repair type available at the least distance.
- `results/k4_dl2/trapped_*.jsonl.gz`: one line per trap. It has every least-distance repair, with flows ([good,
  from, to]), per-agent labels (unfreeze, freeze, takeN, release, frees, rot), shape, need edges and exposures.
- `results/k4_dl2/tables_*.json`: the aggregated repair tables over every P with def > 0 (`k4/dl2_table.py`).

## 7. Reproduce

```
sh k4/dl2_runs.sh check        # cross-checks (about 20 min, 2 processes)
sh k4/dl2_runs.sh n3           # n <= 3, every profile (about 40 min, 2 processes; resumes from the checkpoint)
sh k4/dl2_runs.sh n4_1; sh k4/dl2_runs.sh n4_2     # n = 4 with one / two 4-good agents (n4_2: hours; checkpointed)
sh k4/dl2_runs.sh n4cat; sh k4/dl2_runs.sh n5cat   # #53's catalogues and hunts (minutes)
sh k4/dl2_runs.sh cycle 4      # cyclic n = 4 cores (about 1 h; the log here covers the first 16 cores)
python3 k4/dl2_cn.py 3,4,5,6,7,8,9,10,11,12 --py=7
python3 k4/dl2_shapes.py results/k4_dl2/trapped_n3.jsonl.gz results/k4_dl2/repairs_n3.jsonl.gz
python3 k4/dl2_shapes.py results/k4_dl2/trapped_cycle_n4.jsonl.gz results/k4_dl2/repairs_cycle.jsonl.gz
python3 k4/dl2_shapes.py results/k4_dl2/trapped_n4cat.jsonl.gz results/k4_dl2/repairs_n4cat.jsonl.gz
python3 k4/dl2_table.py results/k4_dl2/tables_n3.json
python3 k4/dl2_dumpfix.py results/k4_dl2/repairs_n3.jsonl.gz --ckpt=results/k4_dl2/ckpt_n3.jsonl   # after a killed run
```
