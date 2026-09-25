# The big-top obstruction: exposed frozen agents and the big-top owner step

Workstream `proof/k4-hall-bt`. It builds on `k4/hall.md` (PR #46: Lemmas H3, H6, H7, conjecture BT) and on
`k4/c4min.md` (PR #41: configurations, Theorems Z and F, the exchange digraph). Ledger rows K4.HALL.BT*
(CONJECTURE / EVIDENCE only). What is left of C₄ᵐⁱⁿ after Theorems Z and F is the case of an **exposed frozen agent**:
- every profile with f = 1;
- 7.28M of the 119.6M n = 3 profiles with ω ≥ 1;
- a large share at n = 4 and 5.

This file attacks it from the side of the *big-top* agents: four goods, holding the top a, with a > b + c.

**Status.** Nothing here changes K4.D or K4.T. What is here:
- **§1 BT in #41's language** (conjecture, with exhaustive evidence for n ≤ 3 and the n = 4 one-4-good class).
  Let P ∈ 𝒫 be Pareto-maximal at the fewest frozen agents, with ω ≥ 1 and no valid owner. Then some *exposed* frozen
  agent is a big-top agent. The part that is proved (`k4/hall.md` Lemmas H6, H7) is that a frozen agent that is not
  big-top is exposed only *locally*: through a good of the owner's base, w.r.t. an owner that does not need its good.
- **§2 The big-top owner step** (conjecture K4.HALL.BTOWN, with exhaustive evidence, and a proved monotonicity lemma).
  At every such P, some cycle of #41's exchange digraph through a frozen big-top agent x, with x becoming the owner,
  gives a completable configuration.
  - The cycle move lets every receiver of a threat edge keep part of its own holding. #41's move, where each vertex
    gives away everything, is not enough on one sampled n = 3 profile.
  - Lemma BT1 (proved) handles the plainest cycle, a need chain closed by one threat edge (LB⁺'s rotation). The new
    owner x faces exactly the old owner's set B_τ ∪ J. Its threatened agents are among the old ones, minus x, plus
    possibly τ. The other agents' slots are unchanged.
- **§3 Evidence**, §4 reproduce.

## 1. BT at the fewest frozen agents

Notation of `k4/c4x.md` §1 and `k4/hall.md`. P ∈ 𝒫 is Pareto-maximal among the pre-allocations with the fewest
frozen agents; a Pareto-improvement never adds a frozen agent (NA only shrinks), so these are the Pareto-maxima of 𝒫 in
the min-frozen class. In #41's terms P is a configuration at the needed set 𝒩 = NA(P) whose free agents hold their bases
(plus slot goods). An agent x is *exposed* w.r.t. a free owner o if B_o ∪ J threatens x holding its base. A frozen x is
exposed in #41's sense (v_x(U_x) > v_x(φ(x))) whenever it is exposed w.r.t. some owner.

**Conjecture K4.HALL.BT (restated).** If P has ω ≥ 1 and no removal-only owner, and has frozen agents, then some
frozen big-top agent is exposed w.r.t. some free owner.

What is proved toward it:
- Lemma H6: along a need chain, a frozen agent has no better set of one or two goods.
- Lemma H7 (both in `k4/hall.md` §5): a frozen exposure is one of three kinds.
  - Global: a big-top agent whose three lower goods are junk.
  - A big-top agent exposed w.r.t. one of its chain ends.
  - Local: through a good of B_o, with o not a chain end.

So a non-big-top frozen agent is exposed only locally: w.r.t. owners holding one of its lower goods. For such an agent
the repairing move is the exchange cycle through the owner: the agent it blocks takes the goods it wants from B_o, and
o is compensated along the cycle. At k = 3 this is Theorem K3's cycle move. What is missing is the proof that a
suitable cycle exists when no big-top agent is exposed (§3: never violated).

## 2. The big-top owner step

**The move.** #41's exchange digraph of a configuration without a valid owner has:
- threat edges o → y (o free, y exposed w.r.t. o);
- need edges x → z (x frozen, z needs φ(x)).

Take a simple cycle through a frozen big-top agent x. Its in-edge is a threat edge, since x holds its top, needs
nothing, and so receives no need edge. Move holdings along the cycle:
- a receiver of a need edge takes the frozen good;
- a receiver w of a threat edge u → w takes an *admissible* set (at most two goods, its needs inside 𝒩) from B_u, its
  own base and the junk, each good used once.

x becomes free, with an admissible set of its lower goods; it needs a, which is now a one-good base. x is then taken
as the owner, with its needs from its bundle: once the bundle holds enough lower goods it needs nothing, which may
unfreeze the agent now holding a. Admissibility keeps NA inside 𝒩, so the result is a valid pre-allocation with the
fewest frozen agents (rigidity, `k4/c4min.md` §1).

**Conjecture K4.HALL.BTOWN.** At every P as in §1, some such cycle through some frozen big-top agent x makes x a
removal-only owner.

Evidence (§3), in every profile tested with a non-completable Pareto-maximum with frozen agents:
- the cycle exists;
- `k4/hall.md` §5 found, in all 320,124 such profiles with n ≤ 3, a completable min-frozen pre-allocation owned by
  a big-top agent.

#41's plain move (each vertex gives away all it holds) is not enough (core 44 of `results/k4_certs_3.json.gz`):
- agents 0: 0:2 2:6 4:3 6:10 (big-top, frozen on 6), 1: 1:3 3:2 5:6 6:10 (base {1, 5}), 2: 2:2 3:4 4:7 5:10 (base
  {3, 4}), J = {0, 2};
- on the cycle 0 → 1 → 2 → 0, agent 2 must keep its good 3 and take 5, leaving 2 for agent 0, who then owns
  {2, 4, 0, 1}.

**Lemma BT1 (the rotation of LB⁺ at k = 4: monotonicity).** Let P be Pareto-maximal at the fewest frozen agents, x a
frozen big-top agent on its top a, τ a chain end of x, and suppose b_x, c_x ∈ J ∪ B_τ. Let P′ be the rotation:
- every agent of a simple need chain x = x₀ → … → x_s = τ takes its predecessor's good;
- x takes {b_x, c_x};
- B_τ ∖ {b_x, c_x} becomes junk.

Then:
- (a) P′ ∈ 𝒫 with NA(P′) = NA(P), so it has the same frozen agents except that x is free and τ is frozen.
- (b) x's owner set in P′ equals τ's in P: {b_x, c_x} ∪ J′ = B_τ ∪ J.
- (c) The slots of the agents other than the owner are the same (S′ − cap′(x) = S − cap(τ)). The agents exposed
  w.r.t. x in P′ are among those exposed w.r.t. τ in P, other than x, plus possibly τ.

*Proof.*
- (a) {b_x, c_x} is admissible: every good of R_x outside it is d_x < b_x + c_x, or a_x, which is needed and is x₁'s
  one-good base. Each chain agent and τ takes a good it needed, so its needs shrink. So NA(P′) ⊆ NA(P), with equality
  by minimality. B_τ misses NA because τ is free. So the new junk and {b_x, c_x} miss NA′, and P′ is valid. Every good
  of NA is again a one-good base, now of the next agent on the chain. So x₁, …, x_{s−1} and τ are frozen, and x is
  free with cap 0.
- (b) J′ = (J ∪ B_τ) ∖ {b_x, c_x}.
- (c) Only x, the chain agents and τ change: x from frozen to cap 0, τ from cap(τ) to frozen, the chain agents frozen
  before and after. So S′ = S − cap(τ). An agent y ∉ {x, τ} holds a base worth at least as much as before, and is
  threatened by the same set B_τ ∪ J, so it was exposed w.r.t. τ. ∎

Also, x's needs from a bundle containing b_x, c_x and d_x are empty (b_x + c_x + d_x > a_x by balance). So if no
agent other than x needs a_x, the owner's bundle unfreezes x₁ and adds one slot: the "u" of `k4/hall.md` Lemma H1.
τ can become exposed only if its base in P was a pair: with one good or none, R_τ ∩ J = ∅ by (U), and B_τ ∪ J meets
R_τ in at most one good.

What Lemma BT1 does not give is that x's demand, removed, was the whole excess of τ's. That is the analogue of LB⁺'s
bad case. The data says a suitable cycle always exists; it is not always this one.

## 3. Evidence

(Filled in from `results/k4_hall_bt_n3.log`, `results/k4_hall_bt_n4_1.log` and `results/k4_hall_bt_samples.log` when the
runs finish.)

## 4. Reproduce

```
python3 k4/hall_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -Bx 5   # results/k4_hall_bt_n3.log
python3 k4/hall_run.py results/k4_certs_4_n4_1.json.gz -Bx 5                        # results/k4_hall_bt_n4_1.log
# samples: results/k4_hall_bt_samples.log lists every command
```
`k4/hall.c -B` computes the Pareto-maxima inside the min-frozen set. At each one with frozen agents, ω ≥ 1 and no
removal-only owner it counts:
- a frozen big-top agent;
- an exposed one;
- a cycle of the exchange digraph through a frozen big-top agent x after which x is a valid owner (every choice of
  the receivers' admissible sets, by backtracking);
- a cycle after which some owner is valid.
