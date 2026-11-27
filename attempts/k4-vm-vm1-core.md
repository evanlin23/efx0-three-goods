# Conjecture VM1 on connected k = 4 cores: refuted (smallest n = 4, m = 7)

Workstream proof/k4-vm (`k4/vm.md` §7.3, §7.7). Conjecture VM1 says: from some V-M matching, at most one move (a pool
upgrade or an unrestricted two-agent exchange), then EFX₀-safe placements with envy-cycle rotation, give a complete
EFX₀ allocation.

`attempts/k4-vm-vm1-noncore.md` refuted VM1 outside the cores and restricted it to connected k = 4 cores, the
instances that matter for TARGET₄ (K4.CORE). **It fails on cores too.**

## The smallest: P34, n = 4, m = 7 (found by the exhaustive certifier)

The exhaustive certifier `k4/vm/vm1chain_cert.py` (`k4/vm.md` §7.9) runs over every strict profile of every n ≤ 4 core.
It found that VM1 already fails at **n = 4**, on the core `4_pure` idx 34 (m = 7, every agent values 4 goods). Every
failing profile there is completed by VM1-chain (`vm1_cert_n4_pure.log`). The first failing profile:

| agent | goods (value) | ranking |
|---|---|---|
| 0 | 0 (4), 2 (3), 4 (2), 5 (8) | 5 > 0 > 2 > 4 |
| 1 | 0 (4), 2 (3), 4 (2), 6 (8) | 6 > 0 > 2 > 4 |
| 2 | 1 (4), 3 (2), 5 (8), 6 (5) | 5 > 6 > 1 > 3 |
| 3 | 1 (4), 3 (2), 5 (8), 6 (5) | 5 > 6 > 1 > 3 |

Checked by hand:
1. **V-M.** Agents 0 and 1 are strong (8 > 4 + 3) and take goods 5 and 6 in Phase I. Agents 2 and 3 tie on good 1
   at rank 3, and the loser takes good 3 at rank 4. So Y = ({5}, {6}, {1}, {3}) or ({5}, {6}, {3}, {1}). The pool is
   {0, 2, 4}, valued only by agents 0 and 1 (4, 3, 2 each).
2. **Frozen agents.** Agents 2 and 3 want goods 5 and 6, and the loser wants good 1 too. So only the loser, say agent 3
   holding good 3, is unfrozen, and it values no pool good.
3. **Zero moves fail.** Agent 3 can take at most two pool goods: all three are worth 9 > 8 to agents 0 and 1, who do
   not value good 3. The third pool good has no place.
4. **The one move fails.** The only legal moves are agent 0's or agent 1's upgrade to {0, 2, 4} (9 > 8).
   - After agent 0's upgrade, good 5 is in the pool, and agents 0, 2 and 3 value it at 8. Every placement breaks EFX₀:
     - on agents 2 or 3, the other sees 5 alone (8 > 4 or 8 > 2);
     - on agent 1, agent 2 sees 6 + 5;
     - on agent 0, agent 1 sees {0, 2, 4} (9 > 8).
   - No envy cycle exists, since agent 0 envies nobody.
   - The exchange that would send good 5 to agent 2 and park agent 2's good 1 on agent 0 breaks EFX₀: agent 3 values 1
     (4 > 2) but not 0, 2 or 4.
5. **Two moves complete:** ({0, 2, 4}, {6}, {5}, {3, 1}). Agent 0 upgrades, agent 2 takes the released 5, and the
   released 1 goes to agent 3.

That is a **DE chain of length 1** whose released good returns to the pool. VM1's exchange with a worthless z parks
that good on x instead, which here breaks EFX₀. So the dictionary entry "worthless-z exchange = chain of length 1" of
`k4/vm.md` §7.8 is only an approximation. The chain is the real move.

Checked uncapped by `vm1_verify.py` (`results/k4_vm/vm1_verify_pure34.log`) and by the replay
`attempts/k4_vm_vm1_core.py` (instance P34, with its own core check; `replay_core.log`).

## The first ones found (n = 5): how they were found

`k4/vm/vm1_core_repair.py` starts from the near-core failure K4-cut, which fails `is_core4` only by one agent's
strict balance. It mutates the instance, keeps only mutations under which VM1 still fails, and accepts a mutation
when the number of `is_core4` violations does not grow. In 16 walks of 300 steps it reached **5 failing cores**,
C0–C4 (`results/k4_vm/vm1_core_repair.log`; JSON in `vm1_core_failures.jsonl`).

Each was checked three ways:
- `is_core4` passes;
- `vm1_verify.py`, uncapped (`vm1_verify_core_cands.log`): there is exactly one V-M matching and exactly one state one
  move away, and neither can be completed by placements and rotations. Two moves suffice;
- the independent replay `attempts/k4_vm_vm1_core.py` (`replay_core.log`). It shares no code with `k4/vm/` or
  `k4/c4_verify_H/`, and has its own check of IsCore4 (C1)–(C5), strictness and connectivity.

Earlier searches missed these:
- the core-checked climbs (`vm1f_climb{3,4,5}.log`) started from random cores;
- these instances are reached by walking from a failure toward the cores, and the failing region seems small.

## C0, n = 5, m = 8 (the first failing core found)

| agent | goods (value) | ranking |
|---|---|---|
| 0 | 3 (25), 6 (5), 2 (15), 4 (26) | 4 > 3 > 2 > 6 |
| 1 | 7 (17), 0 (30), 4 (23) | 0 > 4 > 7 |
| 2 | 1 (6), 3 (15), 2 (30), 0 (25) | 2 > 0 > 3 > 1 |
| 3 | 7 (14), 4 (9), 2 (24), 3 (3) | 2 > 7 > 4 > 3 |
| 4 | 7 (11), 6 (15), 5 (8), 4 (30) | 4 > 6 > 7 > 5 |

Checked by hand:
1. **V-M.** In Phase I, agents 3 and 4 have strong tops (24 > 14 + 9 and 30 > 15 + 11) and get goods 2 and 4. In
   Phase II:
   - agent 1 gets its top 0 at rank 1;
   - agent 0 gets its second good 3 at rank 2;
   - agent 2 gets its fourth good 1 at rank 4.

   So Y = ({3}, {0}, {1}, {2}, {4}), and the pool is {5, 6, 7}.
2. **Frozen agents.** Agent 0 wants good 4, so agent 4 is frozen. Agent 2 wants goods 2, 0 and 3, so agents 3, 1 and
   0 are frozen. Only agent 2 is unfrozen, and frozen agents can receive nothing (Lemma P1′).
3. **Zero moves fail.** Agent 2 values no pool good. Agent 4 values all three, together worth 34 > 30 = v₄(4), and
   does not value good 1. So by EFX₀ agent 2 can hold at most two of them, and the third has no place.
   - No envy cycle exists: agent 0 envies agent 4, agent 4 envies nobody, and nobody may envy agent 2.
4. **The one move fails.** The only legal move is agent 4's upgrade to {5, 6, 7}.
   - No other agent has a pool set worth more than its pick.
   - Every exchange fails because a side does not gain, or because EFX₀ breaks. Agent 4 taking agent 0's good 3 plus
     {5, 6, 7} leaves a bundle that agent 2 envies but does not fully value.
   - After the upgrade, good 4 has no safe place. On agents 0, 1 and 3, agent 2 sees their goods (15, 25, 30 > 6). On
     agents 2 and 4, agent 0 sees good 4 alone (26 > 25), or 4 + 6 = 31 > 25.
   - Again no envy cycle exists.
5. **Two moves complete:** ({4}, {0}, {1, 3}, {2}, {5, 6, 7}).

## The completion is one DE chain

The two moves are **a chain of DE's Lemma chain** (`paper/k3-simple/long.tex`), of length 2:
- x = agent 4 takes its pool set {5, 6, 7};
- j₁ = agent 0 takes x's good 4, which it wants;
- j₂ = agent 2 takes j₁'s good 3, which it wants, keeping its good 1.

C1–C4 complete the same way. **VM1-chain** (`k4/vm/vm1_chain.py`) allows one such chain in place of the one VM1 move,
and it completes all five cores (`vm1_chain_cores.log`).

**What survives:**
- VMX₂ (any number of moves) completes all five;
- **Conjecture VM1-chain on cores** (one VM1 move or one DE chain, then placement with rotation) is unrefuted. It also
  completes every non-core and k ≤ 7 VM1 failure found (`k4/vm.md` §7.7);
- Theorem VM (ordinary EFX) and the proved lemmas are unaffected.

Reproduce:
- `python3 attempts/k4_vm_vm1_core.py` (P34 and C0–C4, under a second);
- `python3 k4/vm/vm1_verify.py '<JSON>' --maxd=3` with a line of `results/k4_vm/vm1_core_failures.jsonl`;
- `python3 k4/vm/vm1_core_repair.py '<K4-cut JSON>' 16 300 77`: the search.
