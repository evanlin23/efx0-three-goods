# Reductions to solved cases, and combinatorial formulations (exploration, branch proof/k3-simplify)

Question: is there an algorithm simpler than K3S (`proofs/k3_simple.md`) for EFX₀ when every agent values at most
three goods, ideally with no repair (rotation) step? Topic of this note: reductions to solved cases (two goods per
agent, multigraphs) and combinatorial / optimisation formulations. Everything here is EVIDENCE unless marked
*proved*; the proofs are sketches and have not been refereed.

Files (all in this folder; run from here, one process, no pools):
- `engine.py`: K3S steps 1–3 (draft with peel priority, upgrade loop, HitSet + one absorber), rank-based, with a
  pluggable leader rule (`top` or `pair`) and absorber choice (`r` or `any`), **no rotation**. Validated equal to
  `k3s.k3s(..., rotate=False)` on all 18,666 profiles with n = 2, m ≤ 5 and n = 3, m ≤ 6 (`python3 engine.py`).
- `candidates.py`: the rotation-free candidates of ideas 1, 2 and pair leaders (`python3 candidates.py NAME...`).
- `po_states.py`, `po_fast.py`: idea 3, Pareto-optimal valid states (Conjecture PO below).
- `power.py`: how many valid states are not completable (shows the PO test has power).
- Logs: `candidates.log`, `po_fast_small.log`, `po_fast_larger.log`, `power.log`.

Test protocol: every ranking profile (`gen_small`: agent 0 ranks 0 ≻ 1 ≻ 2, unranked goods worthless, values 4, 3, 2,
raw EFX₀ check `k3s.efx0`) for (n, m) ∈ {(2, 3..6), (3, 4..7), (4, 5..6)}, then cores (`lbx.core_profiles`), then
random profiles. "First" = first failing profile in that enumeration order, smallest (n, m) first.

## Summary

| idea | candidate | smallest failure | counts |
|---|---|---|---|
| 1. drop a good | every agent ignores c; serial dictatorship; last agent absorbs (L2c verbatim) | n = 2, m = 4 | 24 / 24 at n = 2, m = 4 |
| 1. drop a good | ignore the more-valued of b, c; L2c | n = 2, m = 4 | 24 / 24 |
| 1. drop a good | ignore c; L2c; repair: holder of nothing takes c, free top-holder takes its c, last free agent absorbs | n = 2, m = 4 | 18 / 24 |
| 2. hubs first | K3S 1–3, leader = agent whose top has most valuers; absorber r / any | n = 3, m = 4 | 52 / 44 of 576 |
| (baseline) | K3S 1–3, index leader (no rotation); absorber r / any | n = 3, m = 4 | 28 / 20 of 576 |
| pair leaders | K3S 1–3, a leader takes {b, c} instead of a | n = 2, m = 3 | 4 / 6 |
| pair leaders | ... only if b, c are no other unprocessed agent's top | n = 3, m = 4 | 72 / 576 |
| pair leaders | ... only if b, c are the c of every other unprocessed valuer | n = 3, m = 4 | 12 / 8 of 576 |
| 3. formulation | **Conjecture PO**: every Pareto-optimal valid state is completable | none found | see below |
| 4. relaxation | not pursued beyond the remark below | | |


## Idea 1: reduce to two goods per agent

**Fact (proved, one line).** Serial dictatorship on the true 3-good instance with the last agent absorbing everything
fails only in one way: an agent holding its top a whose b and c both lie in the absorber's bundle of ≥ 3 goods (case
T). Every agent that lost a good holds its best remaining good and the goods it ranks higher are earlier picks,
hence singletons (the absorber is last). So which good an agent ignores does not matter for the failure mode: ignoring
c reproduces serial dictatorship except that an agent holding nothing may leave its c in the big bundle (case E), and
ignoring a or b makes case B or C fail as well. No choice of the ignored good protects a top-holder, because the
2-good instance never sees the pair {b, c}.

**Smallest failure**, all three variants: n = 2, m = 4, both agents rank 0 ≻ 1 ≻ 2, good 3 worthless. Agent 0 takes
0, agent 1 takes 1, and the leftovers {2, 3} go to agent 1: agent 0 holds only its top while its b, c sit in
{1, 2, 3} (v₀({1,2,3} ∖ {3}) = 5 > 4). The repair "a top-holder whose b, c are left over takes its c" does not apply:
agent 1 needs 0 alone, so agent 0 is not free. The EFX₀ allocation {0, 3}, {1, 2} is K3S's upgrade (agent 1 holds
its b, its c is left over, nobody needs b alone). So any repair of the 2-good reduction must contain the upgrade
step and HitSet, and is K3S without the rotation (which fails, baseline row).

## Idea 2: reduce to a multigraph core

Not simpler, for three reasons.
- Theorem M's construction (`proofs/multigraph_extension.md`: popular matching, moves Up, U1, R1 with a potential,
  dump lemma) is itself longer than K3S, so a reduction to it cannot shorten the algorithm.
- It does not extend past class 𝒰 (ledger MX.X, MX.O; `attempts/multigraph_u1_mixed_top.md`): core H3 has no popular
  matching at all, and a mixed-top hub breaks invariant I3 at n = 4, m = 5.
- "Pre-assign the goods with ≥ 3 valuers" is, inside K3S's draft, a leader rule: a hub given to one valuer makes its
  other valuers peelable, and the draft continues. Rule `hub` (leader = agent whose top has the most unprocessed
  valuers) fails like the other leader rules (`attempts/k3s-leader-rules.md`):

  Smallest failure, n = 3, m = 4, rankings (0, 1, 2), (0, 1, 2), (1, 2, 3). Good 1 has three valuers, so agent 2
  leads and takes 1; agent 0 takes 0; agent 1 takes 2 (its c, needs 0 and 1 alone); good 3 is left over. Agent 1 is
  the only free agent, so r = 1, and agent 2 (holds its top 1; b = 2 is r's good, c = 3 left over) is exposed with no
  slot for its protecting good. Choosing any other absorber does not help (absorber `any`: 44 of 576 still fail).

**Pair leaders** (a related reduction: a leader takes {b, c}, which is always safe for it, instead of a, so that
its valuers become peelable). Fails at n = 2, m = 3, rankings (0, 1, 2), (1, 0, 2): agent 0 takes {1, 2}, agent 1
loses its top 1 and holds its b = 0, but 1 is not alone. Restricting pair leaders to agents whose b, c are no other
agent's top fails at n = 3, m = 4 with three agents ranking 0 ≻ 1 ≻ 2 (agent 0 takes {1, 2}, agent 1 takes 0, agent 2
gets nothing and needs 1, 2 alone). Restricting further to b, c that are only ever someone's c fails at n = 3,
m = 4, rankings (0, 1, 2), (0, 3, 1), (3, 1, 0) (no pair leader qualifies; it is K3S's index draft, agent 0 exposed
to r = 2, no slot).

## Idea 3: a combinatorial formulation, Pareto-optimal valid states (the best candidate)

**Observation.** The K3S rotation is a *Pareto improvement*. Since a < b + c, every agent prefers its own pair
{b, c} to its top. In the rotation, k goes from a to {b, c}; every other agent of the need chain, r included, moves to
a good it needs, i.e. ranks higher. So the bad case of K3S is a state that is not Pareto optimal.

**Definitions.** A *state* gives each agent i nothing, one of its own goods, or its pair {b_i, c_i} (i ∈ U), all
goods distinct. Utility order: pair ≻ a ≻ b ≻ c ≻ nothing. NA = goods some non-U agent ranks above its holding
("needed alone"). The state is *valid* if (V1) every good of NA is the single held good of another non-U agent and
(V2) no pair good is in NA. (These are exactly the conditions K3S's states satisfy: Lemma `upgrades` (V1, V2) for the
draft + upgrades, Theorem B after the rotation.) A valid state is *completable* if some *free* agent o (in U, holding
nothing, or holding a good not in NA) passes K3S's HitSet test (`engine.absorb`): one protecting good per exposed agent
into distinct free agents other than o, the rest to o. §3.3 of `proofs/k3_simple.md` (soundness) uses only
validity, so a completable state yields an EFX₀ allocation; the code also checks every output against the raw
definition (0 failures).

> **Conjecture PO.** In every profile (balanced agents, three goods each, worthless goods allowed), every valid state
> that is Pareto optimal among valid states is completable.

If true, this gives an order-free algorithm with no rotation and no draft: *take any valid state that no valid state
Pareto-dominates; let the first free agent that passes the HitSet test absorb the leftovers.* A Pareto-optimal valid
state can be obtained, for instance, as a maximiser of Σ u_i (u = 4, 3, 2, 1, 0), or by serial dictatorship over
valid states (each agent in turn fixes its best option for which a valid state still exists), or by repeated Pareto
improvement from K3S's draft state (Σ u_i ≤ 4n increases each time). **Honest assessment:** none of these is simpler
to *execute* than K3S (each needs a search or an oracle for valid states; the improving step K3S needs is exactly one
rotation, Theorem B). What Conjecture PO would simplify is the *statement and proof*: one order-free invariant replaces
blocks, Lemma T and the bad-case analysis.

**Evidence** (`po_states.py`, `po_fast.py`; enumerate all valid states, keep the Pareto-optimal ones, test each):

| set | profiles | profiles with a non-completable PO valid state |
|---|---|---|
| every profile n = 2, m = 3..6 | 210 | 0 |
| every profile n = 3, m = 4..7 | 62,676 | 0 |
| every profile n = 4, m = 5 | 216,000 | 0 |
| 50,000 random profiles n = 4, m = 6 | 50,000 | 0 |
| 200 random profiles of every certified core, n = 5 | 61,400 | 0 |
| random profiles, n = 2..8, m = max(3, n)..2n + 2 (up to 350 valid states each) | 6,000 | 0 |

The test has power: 1,248 of the 3,600 profiles with n = 3, m = 5 (and 3,308 of 14,400 with m = 6) have a valid
state that is *not* completable (2,060 and 5,464 such states, among them K3S's draft states that need the rotation);
none of them is Pareto optimal (`power.py`, `power.log`). Logs: `po_fast_small.log`, `po_fast_larger.log`.

The exhaustive n = 4, m = 6 set (1,728,000 profiles, about 25 minutes single-core) was not run, for time.
`po_states.py` also found, at n ≤ 3 (m ≤ 7): every maximiser of Σ u_i and every leximin-optimal valid state is
completable, and every profile has a completable valid state (as it must: K3S's output is one).

**Partial proof (sketch, not refereed).** Fix a Pareto-optimal valid state; J = unheld goods; F = free agents;
D = need digraph (arc j → j′ when non-U j′ ranks Y_j above its holding).
- (P1) D is acyclic: rotating the goods around a cycle moves every agent of it up and keeps validity.
- (P2) Every non-U agent x holding a_x has at most one of b_x, c_x in J. Otherwise let x take {b_x, c_x} and pass a_x
  along a path of D from x; the path ends at a free agent f (every non-free agent has an out-arc, D is acyclic), whose
  old good is released into J. Every agent on the path moves up, NA can only shrink, the released good is in no one's
  NA, and b_x, c_x ∈ J ∉ NA, so the new state is valid and Pareto-dominates.
- (P3) If x is exposed for a free absorber o (so Y_o ∈ {b_x, c_x} and the other good is in J, by P2), then x does not
  reach o in D: otherwise the same move ending at f = o hands Y_o to x.
- (P4) **If |F| = 1, Conjecture PO holds.** A free agent exists unless every agent is in U (then any absorber has no
  exposed agent). If F = {o}, an exposed x ≠ o is non-free, so its path in D ends at the only free agent o,
  contradicting P3. So o has no exposed agent and absorbs everything.
- Open: |F| ≥ 2. Counting alone does not finish it. A configuration where every free absorber fails needs, e.g., free
  o₁, o₂, each exposing two non-free top-holders that reach the other. One such configuration (n = 6, m = 10) is
  not Pareto optimal, but the dominating state upgrades two agents at once (o₂ takes a_{x1}, x₁ takes {Y_{o1}, g₁},
  o₁ takes a_{x2}, x₂ takes {Y_{o2}, g₂}). So a proof needs a Hall-type lemma that produces such multi-upgrade
  exchange cycles from a failing HitSet count.

## Idea 4: LP / fractional relaxations

Not tested, for time. One remark: maximum Nash welfare and max Σ u are natural "formulations", but the values here
are only ordinal (L5), and the conditions that matter (goods *alone*, pairs not together in a big bundle) are not
monotone in any welfare function. The one optimisation formulation that tested clean is Conjecture PO's (any
Pareto-optimal valid state, in the ordinal sense above), and it is a statement about K3S's own state space.

## What to try next

1. Prove Conjecture PO for |F| ≥ 2 (P1–P4 are the start; the missing piece is the exchange-cycle lemma).
2. Find a direct, oracle-free rule that outputs a Pareto-optimal valid state (e.g. a serial dictatorship in which an
   agent's options are pair, a, b, c, with a validity look-ahead that is local). With Conjecture PO it would give a
   rotation-free algorithm.
3. Run `python3 po_fast.py small 4 6` (25 min) and larger random samples.
