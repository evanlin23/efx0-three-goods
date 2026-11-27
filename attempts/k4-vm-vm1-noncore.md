# Conjecture VM1 for all 4-limited instances: refuted outside the cores (and at k = 5)

Workstream proof/k4-vm (`k4/vm.md` §7.3, §7.7). Conjecture VM1 was stated in §7.3 "for every 4-limited instance":
from some V-M matching, at most one move (a pool upgrade or an unrestricted two-agent exchange), then EFX₀-safe
placements with envy-cycle rotation, give a complete EFX₀ allocation.

**That form is false, already at k = 4.** The counterexamples in this file lie outside the k = 4 cores, which are the
instances that matter for TARGET₄ (K4.CORE, LEDGER.md, PROVED in Lean).

**Update:** walking from K4-cut toward the cores found failing *cores* too (`attempts/k4-vm-vm1-core.md`). VM1 is
refuted on connected k = 4 cores as well. This file keeps the non-core instances, which came first.

## How it was found

The k = 6 general climb `k4/vm/vm1_climb_k.py 5 6 16 200 56` (`results/k4_vm/vm1_climb_k6_n5_long.log`) has no core
requirement. It reached margin (0, 0.0) on **K5**, an instance with n = 5, m = 9 in which three agents value 5 goods,
so k = 5.

`k4/vm/vm1_shrink.py` (`results/k4_vm/vm1_shrink_k5.log`) then cut goods from agents' sets while VM1 kept failing:
- **K4-min** (n = 5, m = 8, k = 4) is reached by single cuts. Two of its agents value a single good.
- Of the 125 ways to cut K5's three 5-good agents down to 4 goods, **3 still fail**. One is **K4-cut** (n = 5, m = 9,
  sizes 4, 3, 4, 3, 4). It fails `is_core4` only through agent 3, which is not strictly balanced (17 ≥ 10 + 4). So K4-cut
  is one condition away from a core, and rule R1 would peel agent 3.

All three were checked uncapped by `vm1_verify.py` (`vm1_verify_climb_k5.log` for K5, `vm1_verify_k4_shrunk.log` for
K4-min) and by the independent replay `attempts/k4_vm_vm1_noncore.py` (`results/k4_vm/replay_noncore.log`). Each has
a single V-M matching and a single state one move away. Neither the matching nor that state can be completed by
placements and rotations. **Two moves suffice** in each.

## The smallest failing configuration found: K4-min (n = 5, m = 8, k = 4)

| agent | ranking (good: value) |
|---|---|
| 0 | 5: 26 > 4: 25 > 0: 15 |
| 1 | 0: 27 |
| 2 | 2: 30 > 0: 29 > 4: 25 > 1: 20 |
| 3 | 2: 17 |
| 4 | 5: 30 > 7: 15 > 3: 11 > 6: 8 |

Checked by hand:
1. **V-M.** In Phase I, agents 1, 3 and 4 hold strong tops (a > b + c) and get goods 0, 2 and 5. In Phase II, agent 0
   gets its second good 4 and agent 2 its fourth good 1. So Y = ({4}, {0}, {1}, {2}, {5}), with pool {3, 6, 7}, which
   only agent 4 values.
2. **Frozen agents.** Agent 0 wants good 5, so agent 4 is frozen. Agent 2 wants goods 2, 0 and 4, so agents 3, 1 and 0
   are frozen. Only agent 2 is unfrozen, and by Lemma P1′ frozen agents can receive nothing.
3. **Zero moves fail.** Agent 2 can take at most two of the pool goods: all three are worth 34 > 30 to agent 4, who
   does not value good 1, so EFX₀ would fail. The third pool good has no safe place. No envy cycle exists: nobody can
   envy agent 2's bundle under EFX₀, and agent 4 envies nobody.
4. **The one move fails.** The only legal move is agent 4's upgrade to {3, 6, 7} (34 > 30), which puts good 5 back in
   the pool.
   - Good 5 has no safe place. On agent 0, agent 2 sees good 4 (25 > 20) after removing 5. On agents 1 and 3, agent 2
     sees their goods. On agents 2 and 4, agent 0 sees 5 alone (26 > 25).
   - No envy cycle exists.
   - Every exchange fails a test: neither side gains, or the result breaks EFX₀.
5. **Two moves complete:** ({5}, {0}, {1, 4}, {2}, {3, 6, 7}). Agent 4 upgrades to {3, 6, 7}, agent 0 takes the
   released good 5 (it wants it), and agent 2 takes the released good 4 (it wants it, and keeps good 1).

## What is missing from VM1's moves: DE's chains

The completion in step 5 is **a chain of DE's Lemma chain** (`paper/k3-simple/long.tex`), of length 2:
- x = agent 4 takes its "pair" {3, 6, 7} from the pool;
- j₁ = agent 0 takes x's good 5, which it wants;
- j₂ = agent 2 takes j₁'s good 4, which it wants.

K5 and K4-cut complete the same way: agent 4 upgrades, agent 0 takes good 6 and agent 2 takes good 5. VM1's moves are
DE's chains of length 0 (an upgrade), chains of length 1 (a worthless-z exchange) and 2-rings (a valued-z exchange),
as in the dictionary of `k4/vm.md` §7.8. **A chain of length 2 is not one VM1 move.**

Agents 1 and 3 here, and agent 3 of K4-cut (which is not strictly balanced), are what rules R1 and R2 peel. The
chain still arises in cores, though: see `attempts/k4-vm-vm1-core.md`.

**What survives:**
- VMX₂ (any number of moves) completes all three instances (two moves);
- the natural general form allows one DE trade, chains of any length included. That is Conjecture VM1-chain
  (`k4/vm.md` §7.7), and it completes all three, and the failing cores of `attempts/k4-vm-vm1-core.md`.

At k = 5, K5 refutes VM1 for general instances: it is a random instance, not from the PW family.

Reproduce:
- `python3 attempts/k4_vm_vm1_noncore.py` (all three instances, under a second);
- `python3 k4/vm/vm1_verify.py '<JSON>' --maxd=3` with the JSON in the first line of `vm1_verify_k4_shrunk.log` or
  `vm1_verify_climb_k5.log`;
- `python3 k4/vm/vm1_shrink.py '<K5 JSON>'`.
