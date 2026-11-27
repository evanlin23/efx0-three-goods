# Breaking one round of disjoint chains with wanter rankings: fails

Workstream `proof/k4-ksens` (`k4/ksens.md` §6). Idea: in PW (`k4/ksens.md` §1) a round of disjoint chains repairs
every frozen agent at once, each with its own wanter. With one or two wanters ranking the frozen picks so that a
wanter must trade up several times (an agent moving twice), a round should be unable to perform the repairs, which
only a sequence of chains could.

**Test** (`k4/ksens/round_gadgets.py`, `results/k4_ksens/round_gadgets.log`). Instances:
- PW(f, W, r) with clean values, for (f, W, r) = (3, 1, 4), (3, 1, 5), (4, 1, 5), (3, 2, 4), (4, 2, 5), (4, 2, 6);
- every combination of the wanters' rankings over the frozen picks;
- 1,224 configurations in all, tested from the natural order.

**Result.**
- In 612 of them one chain fails and two sequential chains succeed.
- One round fails in none.
- Whenever a wanter would have to move twice, a different wanter, or a single longer chain inside the round, does the
  same job. The merged chain x₂ → w → x₁ repairs both frozen agents in one move: x₁ receives w's old pick and a pair.

**Smallest failing configuration of the idea:** PW(3, 1, 4) with any ranking. One round repairs it.

**What does break one round** is a different mechanism: an agent whose repair needs two other agents' picks, which a
chain's head (taking from its own end only) cannot collect. See RD5 (`k4/ksens.md` §6, `k4/ksens/refute_rd_k5.py`):
n = 4, m = 7, k = 5.

Reproduce: `python3 k4/ksens/round_gadgets.py`.
