# First agent by fewest frozen agents (k4/adaptive.md §4, the bridge to Theorem Z)

**Idea** (the coordinator's suggested next step after the #44 review). PR #41's Theorem Z (machine-checked on main,
K4.C4MIN.Z.LEAN) proves C₄ᵐⁱⁿ on every profile where some valid pre-allocation of `k4/c4x.md`'s space 𝒫 has no frozen
agent: some pre-allocation with the fewest frozen agents is completable. If rule F's first agent were the one whose
run of Phase 1 leaves the fewest frozen agents, and that number were the fewest over 𝒫, Theorem Z would say why rule F
works, at least where that number is 0. Two rules test this (`k4/adaptive.c`):
- `-A28`: the first agent a whose run τ_a = (a, then index order) leaves the fewest frozen agents after need-shrinking
  upgrades (ties by index), then index order;
- `-A29`: rule F restricted to those first agents (for each bound 0, 1, …, each of them in index order).

**Where it breaks.** With at most one rotation both fail at n = 3 (with two, LB₄ʳ succeeds): `-A28` on 11,520
profiles, with the same histogram as `-A4` (least ω after need-shrinking upgrades); `-A29` also on 11,520. So on
these profiles every first agent with the fewest frozen agents needs two rotations, and rule F succeeds with one from a
first agent whose run leaves *more* frozen agents. At n = 4 with one or two 4-good agents neither needs two rotations,
but `-A29` needs one on 207,248 profiles with two 4-good agents, where rule F needs one on 206,880
(`results/k4_adaptive_frozen.log`).

On every one of the 96 leaves (weight 11,520) where `-A29` needs two rotations, the fewest frozen agents over 𝒫 is
**0** (`k4/c4x.c -1s`, PR #36), so Theorem Z applies, but the fewest over *every* run of Phase 1 (every insertion
sequence) and every upgrade policy is **1** (PR #33's independent model; checked on each leaf's representative).
Theorem Z's pre-allocation is not a state that Phase 1 and the upgrades reach; LB₄ʳ gets to an allocation only
through a rotation. So the bridge cannot go through the Phase 1 state: it needs either a statement about the state
after rotations or an existence theorem for the reachable states.

**Smallest failing configuration** (n = 3, m = 6): the profile of `attempts/k4-adaptive-greedy-omega.md`, agents
{0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8), (2, 3, 4, 8), (2, 7, 8, 4).
- After need-shrinking upgrades, the first agents 0, 1, 2 (then index order) leave 1, 2, 1 frozen agents; agents 0
  and 2 need two rotations, agent 1 needs one (rule F's choice).
- Fewest frozen agents over 𝒫: 0; over every run of Phase 1 and every policy: 1.
- Brute force: K4.D holds there.

Reproduce:
- `python3 attempts/k4_adaptive_attempts.py`: rules 28 and 29 on this profile, with `k4/adaptive.c` and in PR #33's
  model, plus the frozen counts (`results/k4_adaptive_attempts.log`).
- `python3 k4/adaptive_frozen.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz results/k4_certs_4_n4_1.json.gz results/k4_certs_4_n4_2.json.gz`:
  the counts and the 96 leaves (`results/k4_adaptive_frozen.log`).
