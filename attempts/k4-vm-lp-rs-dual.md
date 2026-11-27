# RS dual prices as a completion certificate at RS-optimal starts: refuted (n = 4, m = 6)

Workstream proof/k4-vm, LP/duality angle on RKMAX's min-rank-sum form (`k4/vm_lp/rs_dual.md`).

**The idea.** At an RS-optimal maximum matching Y (least rank sum), the dual prices β of the RS LP form a potential:
- they rise along the wants digraph;
- they are capped at every agent that values a junk good (Lemma RSD).

The candidate certificate:
- (D1) if every dangerous agent has slack in its junk cap, the picks complete with one absorber;
- (D2) otherwise a chain read off the tight dual constraints repairs.

**It fails.**
- On the certifier's n = 4 failure export, D1, D2 and the widened D2 fail on 160 of the 10,840 RS-optimal starts that
  need a move.
- On random n = 4 cores they fail too.
- Both danger notions were tried: rklib's *truly dangerous* agents, and frozen agents whose junk is worth more than
  their pick. The logs are in `results/k4_vm_lp/`.

## Smallest failing configuration: n = 4, m = 6

A random strict connected k = 4 core (`cores:4:3000:301` #2548; `is_core4` passes):

| agent | goods (value) | ranking |
|---|---|---|
| 0 | 0 (4), 2 (6), 3 (3), 4 (8) | 4 > 2 > 0 > 3 |
| 1 | 1 (6), 2 (7), 3 (10), 5 (2) | 3 > 2 > 1 > 5 |
| 2 | 2 (3), 4 (4), 5 (2) | 4 > 2 > 5 |
| 3 | 3 (4), 4 (3), 5 (2) | 3 > 4 > 5 |

1. **Y is RS-optimal.** Y = (4, 2, 5, 3) has rank sum 1 + 2 + 3 + 1 = 7, the least over the 38 perfect-agent
   matchings.
2. **The duals.** The least dual prices are β(2) = 1, β(3) = 2, β(4) = 2, and 0 elsewhere. The junk is {0, 1}.
   - Agents 0, 1 and 3 are frozen; agent 2, the receiver, wants goods 4 and 2.
   - No frozen agent values the junk above its pick: v₀({0, 1}) = 4 < 8 and v₁({0, 1}) = 6 < 7.
   - So no agent is dangerous, and D1's hypothesis holds vacuously.
3. **The picks have no one-absorber completion.** Every absorber is envied:
   - on agent 2, agent 1 sees {5, 0, 1}, worth 2 + 6 = 8 > 7;
   - on agent 0, agent 2 does;
   - on agent 1, agents 0 and 2 do;
   - on agent 3, agent 1 does.

   Spreading the junk does not help either: the replay checks every assignment.
4. **One ring repairs it:** ({0, 2}, {1, 5}, {4}, {3}).
   - Agent 2 takes agent 0's pick 4, which it wants.
   - Agent 0 takes agent 1's pick 2 (worth 6 to it) and junk 0.
   - Agent 1 takes the receiver's pick 5 and junk 1.

   None of these is on a tight chain from a dangerous agent, because there is none.

**Why it fails.** The threat that blocks the completion is cardinal: the absorber's pick plus junk, against the
observer's pick. The RS LP compares only ranks, so its duals cannot see the threat.

**What survives:**
- Lemma RSD (proved);
- OC₁ at every RS-optimal start tested, as in proof/k4-rkmax;
- the canonical tight chain repairs 10,680 of the 10,840 hard RS-optimal starts on the export.

A usable LP certificate would need cardinal coefficients (`k4/vm_lp/rs_dual.md` §3).

Reproduce: `python3 attempts/k4_vm_lp_rs_dual.py`. It is an independent replay from the definitions (no repository code,
no rklib): rank-sum optimality, the least prices, the absence of dangerous agents, no one-absorber completion, and the
repairing ring.
