# Does Lemma M^c's infeasibility certificate name the repairing chain's head? (PARTIAL, stopped)

Workstream proof/k4-vm, the optional timeboxed step of the LP/duality angle (`k4/vm_lp/rs_dual.md`). It was stopped
at the coordinator's wind-down request, so this is partial evidence only. Script: `k4/vm_lp/mc_head.py`. Log:
`results/k4_vm_lp/mc_head_cores_4_800_311.log`.

**Question.** Take a start Y of single picks with no wanted junk good ((G2), which holds at Pareto-optimal starts)
where the picks fail. Lemma M^c (`k4/oc1max_multi.md` §9) is exact there, so every triple (owner o, kept-out junk H,
frozen slots F_s) violates (C1), (C2) or (C3). Does the violated condition name the head x₀ of a repairing chain?

**Method.**
- M^c is re-implemented from the §9 text.
- It agrees with rklib's brute-force one-absorber search on all 2,203 (G2) maximum-matching starts of 800 random n = 4
  cores. There are 0 mismatches; non-(G2) starts are skipped.
- *Named* agents: the owner for (C2), the needy non-eligible agents for (C1), and the uncovered needy agents for (C3).
  For each owner, the triples with the fewest named agents are kept.
- *Heads*: the takers of junk in rklib's repairing official moves.

**Partial result** (313 starts on random cores where the picks fail and one move repairs):

| statement | holds |
|---|---|
| some head is named for every owner | 193 / 313 |
| some head is named for some owner | 299 / 313 |
| some repairing move changes an agent named for every owner | 282 / 313 |
| some repairing move changes an agent named for some owner | 313 / 313, but near-trivial: at 171 starts all 4 agents are named for some owner |

At 26 starts no agent is named for every owner.

**Reading.** The certificate usually points at an agent of the repair: the owner-independent named set meets a
repairing move at 90 % of starts. It does not reliably name the chain's head (62 %). Often it names the threatened
agent, while a different agent leads the chain. As a rule, "the violated (C)-condition names x₀" fails on this sample.
The run on the certifier's export was stopped before it finished; its partial log was not kept.
