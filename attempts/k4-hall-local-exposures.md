# Theorem K3 at k = 4 when every frozen exposure is local: false

Workstream `proof/k4-hall` (`k4/hall.md` §5).

**Approach.** Theorem K3 (`k4/c4x.md` §3) proves that every Pareto-maximal P ∈ 𝒫 of a k = 3 core is completable. At
k = 3 every exposure of a frozen agent is *local*: it goes through a good of the owner's base, and the owner is not a
chain end of the agent (Lemma E there). At k = 4, Lemma H7 of `k4/hall.md` §5 shows that a frozen exposure is local
unless the agent is a *big-top* agent (four goods, holding its top a with a > b + c) whose other goods lie in J, or in
J ∪ B_o for a chain end o. The hope was: if no frozen exposure is of the big-top kinds (G) or (G1), a Pareto-maximum is
completable, as at k = 3 (with Theorem H0's counting for the free exposed agents).

**Why it fails.** A big-top agent can block every owner through local exposures alone. The repair makes it the owner
through an exchange cycle that is not a Pareto-improvement in 𝒫: the big-top agent's value drops as a base but rises as
an owner's bundle.

## Smallest failing configuration found

n = 3, m = 7 (core 33 of `results/k4_certs_3.json.gz`), `k4/hall_instances/local3.inst`:

| agent | goods and values | base in P |
|---|---|---|
| 0 | 0:3 1:2 2:10 3:6 (a = 10 > b + c = 9: big-top) | {2}, frozen (agent 1 needs 2) |
| 1 | 2:8 4:2 5:3 6:4 | {5, 6} (needs 2) |
| 2 | 3:7 4:3 5:5 6:6 | {3, 4} |

J = {0, 1}, the number of slots S is 0, ω = 2, and the fewest frozen agents is 1. P is Pareto-maximal among all 22 valid
pre-allocations. It is not completable:
- Owner 1 leaves agent 2 threatened. Agent 2 values 1's base {5, 6} at 11 > 10, shape e3 of Lemma H3, unhittable.
- Owner 2 leaves agent 0 threatened. B_2 ∪ J ∋ 3, 0, 1, worth 11 > 10 to agent 0. This is a local exposure with one
  label, and there is no slot.

Agent 0's chain end is agent 1, not agent 2, so the exposure w.r.t. owner 2 is local, not (G1). The completable repair
is the cycle below, with deficit −1:
- agent 0 gives 2 to agent 1;
- agent 1 gives {5, 6} to agent 2;
- agent 2 gives 3 to agent 0;
- agent 0 becomes the owner of {3, 0, 1, 4}.

(Two other min-frozen repairs lower agent 1 instead.)

## Replay

`python3 attempts/k4_hall_attempts.py` checks P with both implementations and prints "ALL CONFIRMED":
- `k4/hall.c`: this P is a Pareto-maximum in the min-frozen class with deficit 1;
- `k4/hall_check.py`: P is valid and Pareto-maximal, and every completion fails the raw EFX₀ re-check.

## What survives

Conjecture K4.HALL.BT (`k4/hall.md` §5). Every non-completable Pareto-maximum with frozen agents that was found has a
frozen big-top agent. In every sampled profile with such a maximum, some min-frozen pre-allocation is completable with
a big-top agent as the owner. So the k = 4 argument must let a big-top agent become the owner, and Pareto-maximality
cannot be the extremal principle for it.
