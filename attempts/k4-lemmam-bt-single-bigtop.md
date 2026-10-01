# The unique big-top agent first (step (a) of the big-top programme, `k4/rulef.md` §6)

**Idea.** `k4/rulef.md` §5.2 found, exhaustively on every certified core with n ≤ 4 and at most three 4-good agents,
that when exactly one agent q is *big-top* (four goods, a > b + c) the run of τ_q = (q, then index order) is in class
K0 or K1 of rule RK. A big-top agent that does not hold its top keeps needing it, so the holder of its top stays frozen
until a rotation; inserted first, q holds its top and needs nothing. Step (a) of the programme for Lemma M: with exactly
one big-top agent, τ_q satisfies M1 (|σ_F| ≤ κ₀) or Lemma KR's hypotheses.

**Where it breaks.** Being inserted first only helps where q's insertion reaches. If q's top is private, q's insertion
changes nothing for the other agents, and the rest of the run is index order. On H_t (`k4/c4.md` §7) plus such a q,
the rest is H_t's index run, which Proposition H's count (K4.C4.R) shows needs about 2t/3 rotations; q adds one slot
place. For t ≥ 3 one rotation is not enough: Proposition Q of `k4/lemmam_bt.md` §2 (written proof).

**Smallest failing configuration** (smallest of this family; at n ≤ 4 with at most three 4-good agents the statement
holds on every strict profile, `k4/rulef.md` §5.2): H_3 + q, n = 14, m = 34. Agents (goods, values in the same order):
ℓ {0, 3, 4, 5} (8, 6, 5, 4); for gadget j = 1, 2, 3 the x's {a, b, c, g_j} (8, 6, 4, 3) and y_j {a_{j,1}, a_{j,2}, a_{j,3},
e_j} (8, 6, 4, 3) as built by `k4/adaptive_H.py` (t = 3); q = agent 13 {33, 9, 12, 4} (8, 4, 3, 2): good 33 is private,
9 and 12 are b_{1,1} and c_{1,1}, 4 is u. A connected k = 4 core with a strict profile; q is its only big-top agent.
- Lemma K (`k4/lemmam_bt.py`): least deficit 5 at q's run under each policy, at least 2 after every single RotStep (18
  of them): q is in neither K0 nor K1 (`results/k4_lemmam_bt/classes_Hq3.log`); `k4/rulef.c -A42 -Q0` (first big-top
  agent) puts q in no class (`results/k4_lemmam_bt/rk_Hq3.log` has every first agent's class).
- LB₄ʳ(τ_q) with at most one rotation has no output, by PR #33's two encodings of Lean's `Output`
  (`results/k4_lemmam_bt/exactA_Hq3.log`, `exactB_Hq3.log`); `k4/rulef.c` agrees (`-A42 -Q0 -r1 -T1`: fail).
- Rule RK takes agent 1 (x_{1,1}, gadget 1) in K0, as Proposition H″ predicts: the first agent has to be where the run
  is decided, not where the big-top agent is.

Reproduce: `python3 attempts/k4_lemmam_bt_attempts.py` (part 1), or `bash k4/lemmam_bt_runs.sh core classes exactA
exactB`.
