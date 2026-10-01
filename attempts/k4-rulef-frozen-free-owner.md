# "No frozen agent after need-shrinking upgrades gives a valid owner" (k4/rulef.md §6)

**Idea.** Proposition H′ (K4.AD.H) proves rule F on H_t in two steps: the right first agent leaves no frozen agent
after need-shrinking upgrades, and then the owner r is valid by a count. The second step as a general lemma for
LB₄ʳ's states — an analogue of #41's Theorem Z (fewest frozen agents 0, K4.C4MIN.Z), which is stated over a different
space of pre-allocations — would reduce Lemma M (k4/rulef.md §4) to choosing a first agent whose run leaves no frozen
agent: *if the state after Phase 1(τ) and need-shrinking upgrades has no frozen agent and ω ≥ 1, some owner is valid
without rotation.*

**Where it breaks.** Already at n = 2. A free agent holding its top can be threatened by goods that sit in an
upgraded agent's two-good base: those goods are not junk, so they cannot be kept out of the owner's bundle, and the
upgraded agent cannot be the owner without handing them over. On the profile below, first agent 0: agent 0 takes 4,
agent 1 takes 3 and upgrades with 2 (need-shrinking: 5 + 4 > 8), so nobody is frozen and ω = 1. Owner 0's bundle
{4, 0, 1} threatens agent 1 ({4, 1} is worth 8 + 2 > 5 + 4 to it), and only the owner has a slot, so 1 cannot be kept
out; owner 1 (base {3, 2}) threatens agent 0, whose goods 3 and 2 in that base are worth 7 + 4 > 8 + 2. No completion exists; a rotation is needed. (First
agent 1 needs none: there agent 0 upgrades to {3, 2} and owner 1 is valid.) Counted on the n = 2 leaves
(`k4/rulef.c -A40 -C3 -r1 -D3`, then `k4/rulef_n2stats.py`; `results/k4_rulef/contain_n2.log`): 600 (profile, first
agent) pairs with no frozen agent after need-shrinking upgrades, ω ≥ 1 and Lemma K's deficit positive, 240 of them
with no output at all before a rotation.

**Smallest failing configuration** (n = 2, m = 5): agents {0, 2, 3, 4}, {1, 2, 3, 4} with values (2, 4, 7, 8),
(2, 4, 5, 8), first agent 0. Confirmed in PR #33's independent model of LB₄ʳ: the state after Phase 1([0]) and
need-shrinking upgrades has no frozen agent, ω = 1, and no `Output` (no owner and every owner, both owner-needs
conventions); brute force finds EFX₀ allocations with at most one large bundle.

Reproduce: `python3 attempts/k4_rulef_attempts.py` (part 2; `results/k4_rulef/attempts.log`).
