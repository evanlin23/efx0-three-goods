# Attempt: after the chain, its head x_t is the owner (Conjectures OC₁-H and OC₁-HD, k = 4)

Workstream `proof/k4-ttc` (`k4/ttc.md` §8, §10). Status: **refuted** at n = 6, m = 10. The counterexample was found by
an adversarial climb and is replayed independently: chains enumerated from the definition, completions brute-forced
against the raw EFX₀ definition, no SAT and no shared code. Plain OC₁ holds there. The endpoint form OC₁-E survives
(below).

## The idea

In Abdulkadiroğlu–Sönmez's TTC with an ordering, a request chain ending at a vacant house executes only when its
head is the top-priority agent, so the pool behaves as the head's endowment (`k4/ttc.md` §1). The translation was
two conjectures:
- *OC₁-H.* From every order, the picks have a one-absorber completion, or some improving chain x₀, …, x_t (t ≥ 1)
  has a one-absorber completion whose absorber is the head x_t, the agent whose pick is vacated.
- *OC₁-HD.* The same with the chain's shape fixed: x₀ dangerous, and the middle agents taking exactly their
  predecessor's pick.

Both held on all 2,310 distinct hard starts with n ≤ 5 and on 103 hard starts with n = 6–9 (`k4/ttc.md` §8, §10).
One of those 2,310 starts is dich3, the instance on which x₀ cannot own (`attempts/k4-ttc-x0-owner.md`).

## The counterexample

Found by `k4/ttc/head_bign_climb.py` (n = 6–8, climbing on values and incidences; `results/k4_ttc/head_bign_climb_6_8.log`).
- Instance (case 0): sets [[0, 2, 3, 1], [1, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]], values
  [[2, 7, 8, 5], [2, 9, 5, 10], [10, 2, 6, 5], [8, 7, 1, 5], [10, 1, 2], [10, 9, 3, 1]], m = 10.
- Order (0, 1, 2, 3, 4, 5).
- Picks (3, 9, 1, 6, none, none): agents 4 and 5 find all their goods taken. Junk {0, 2, 4, 5, 7, 8}.

`python3 k4/ttc/refute_head.py 0` (log `results/k4_ttc/refute_head.log`):
- the picks have no one-absorber completion;
- there are 10 improving chains with t ≥ 1, and none has a completion in which its head absorbs (every other agent at
  most one junk good);
- 4 chains have a one-absorber completion with another absorber:
  - (0, 4): agent 0 takes {0, 2}, agent 4 takes 3; absorbers 0 or 5;
  - (0, 5): absorbers 0 or 4;
  - (1, 4): agent 1 takes {4, 5}, agent 4 takes 9; absorbers 1 or 5;
  - (1, 5): absorbers 1 or 4.

A second instance from the same climb (case 1, `refute_head.py 1`) behaves the same way. There 43 chains exist, none
with the head absorbing, and in chain (0, 4) only the other pickless agent can absorb.

**Why the head fails.** The head is a pickless agent, and it receives a pick that the other pickless agent values. If
the head also absorbed the junk, the other pickless agent would remove a junk good and still see that pick, worth more
than its own empty bundle. The absorber has to be an agent whose bundle nobody envies after removing one good: x₀ (now
holding junk only) or the other pickless agent.

**Why n ≤ 5 missed it.** The k = 4 cores with n ≤ 5 rarely leave two agents without a pick. The counterexample needs
two pickless agents with overlapping goods, one of which heads the chain.

## What survives

**Conjecture OC₁-E (the absorber is an endpoint of the chain).** From every order, the picks have a one-absorber
completion, or some improving chain x₀, …, x_t (t ≥ 1) has a one-absorber completion whose absorber is x₀ or x_t.
- It holds on everything above: here x₀ absorbs, and on every earlier start the head does.
- Neither endpoint alone suffices: the head fails here, and x₀ fails on dich3 (n = 3, m = 7).
- These are LB⁺'s two owners at k = 3: Theorem A's r (the chain's end) and Theorem B's k (the chain's start).

The shape form **OC₁-ED** (OC₁-HD's shape, the absorber an endpoint) holds on both instances here: the chains (0, 4)
and (1, 4) have t = 1 and x₀ dangerous. Climbs against OC₁-E / OC₁-ED: `k4/ttc.md` §10.
