# β = 3: Q-plans with a restricted toolbox

Workstream `proof/beta3`. Intermediate hypotheses on the way to Theorem D3 (`proofs/beta3.md`). A Q-plan (§3 there)
gives every agent without a private good (Q-agent) a role: its top alone (a-pin), its b alone under a 1-holder of its
top (b-pin), or two of its goods (2-holder); spare goods go to the collector, or, when no component of K is active,
to a dump target (a 2-holder's bundle or a P-agent's head). Theorem 5 turns any Q-plan into an EFX₀ allocation with at
most one large bundle. Each restriction below looked sufficient on the first cores tried and is not.

**What survived.** The full toolbox has a Q-plan for every β = 3 core and every order of its Q-agents (Lemma 7,
certified on all reduced cores with n ≤ 10). Cores with q ≤ 1 need only a-pins, spares and collectors; q = 2 needs
b-pins and 2-holders, but never a dump target (Lemma 6, by hand).

**Where each restriction breaks** (smallest n; counts are Q-orders without a plan among all β = 3 cores with that n):

| toolbox | fails first at | smallest failing configuration (core; Q-orders a, b, c) |
|---|---|---|
| a-pins only | n = 3, q = 2 (12 of 36) | [[1,2,3],[0,1,2],[0,1,2]]; agents 1, 2 both (0, 1, 2): equal tops, one must be a b-pin |
| a-pins, b-pins (with or without dump) | n = 3, q = 3 (216 of 216) | [[0,1,3],[0,2,3],[1,2,3]]; (0,1,3), (0,2,3), (1,2,3): no P-agents, so K is four isolated goods; three 1-holders mark three of them, and the fourth needs a spare with neither a collector nor a dump target |
| a-pins, 2-holders, dump | n = 3, q = 2 (12 of 36) | as for a-pins only |
| all roles, no dump target | n = 4, q = 3 (4 of 864) | [[0,1,5],[0,1,4],[2,3,4],[2,3,4]]; agent 1 (4,0,1), agents 2, 3 (2,4,3) |

In the last configuration every Q-plan needs a dump target. One is: agent 2 an a-pin at 2, agent 3 a b-pin at 4 (its
top 2 is held by agent 2), agent 1 a b-pin at 0 (its top 4 is held by agent 3), spare 3, no active component, and the
spare dumped on agent 0's head 1. It gives the EFX₀ allocation {1, 3, 5}, {0}, {2}, {4} (`proofs/beta3.md` §6).
With n = 5 the same restriction fails on 6 of 3,672 q = 3 orders; with n = 6 on 64 q = 3 and 8 q = 4 orders.

Reproduce: `python attempts/beta3_restricted_qplans.py 3 4 5` (about a minute; exact search, every plan re-checked with
`beta3.check_plan`).
