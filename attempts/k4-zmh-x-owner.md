# Failed: ZMOVE with the unfrozen agent as the new owner (ZX)

Workstream `proof/k4-zmove-hall` (`k4/zmove_hall.md` §1). REFUTED (a candidate uniform form of ZMOVE, not a ledger
claim).

**Statement tried (ZX).** At some Z′-maximum Q of every key κ with def*(κ) > 0, some (T3⁺) move with at most one helper
from P_Q reaches a state P′ with def(P′) ≤ 0 *in which the unfrozen agent x is a best owner*: x has a safe bundle Z in
P′ with |Z| + u′_x(Z) ≥ ω + 2 (Lemma H1).

It would replace the case lists by one shape: every lemma of `k4/sx.md` and `k4/f2.md` whose owner is x (A, B, B′, A⁺,
B⁺, C′ and C′⁺ with o = x, C⁺ₕ) is an instance, and a proof would only have to find x's bundle. On the first inputs
(PR #80's small n = 4 hunts, compute/k4-rc's cores, compute/k4-cover's two COVER⁺ failures) it held at every Z′-maximum.

**Smallest failure found** (n = 3, m = 8, f = 1, ω = 3):
`{"sets": [[0,2,5,7],[1,4,6,7],[3,5,6,7]], "vals": [[3,4,2,8],[2,3,4,8],[3,5,6,7]], "m": 8}`
- key κ = (7, agent 2), def* > 0; its unique Z′-maximum is Q = {0: {0,2}, 1: {4,6}}, L = {1,3,5};
- both free agents are terminals (top 7), both are robust leaves, and both are θ-b (big-top on 7 with their three lower
  goods in their bundles): `k4/sx.md` §5 case (2), the case of Lemmas C and C′;
- each of the 16 (T3) moves from P_Q that reach deficit ≤ 0 has the *other leaf* as its only best owner (4 moves without
  helper, where it does not move: Lemma C's shape; 12 with that leaf as the helper): a θ-b terminal τ takes 7, and a
  bundle of x would keep τ's three lower goods, which threaten τ holding 7 (`k4/zmh_roles.py`).

**Extent** (`k4/zmh_zx.py`, `results/k4_zmove_hall/zx_forms.log`): 42 of 3,119 f = 1 keys in every 20th profile of
compute/k4-cover's n = 3 screen; it held at every f ≥ 2 key of the samples there (compute/k4-rc's cores, every 40th
f ≥ 2 profile of compute/k4-cover's dumps with n ≤ 5). The forms without helper fail more often (n = 3: 45 keys for
ZMOVE without helper, 203 for ZX without helper), and the forms with W = ∅ fail at f ≥ 2 (33 of 536 f = 2 keys and 805
of 3,550 f = 3 keys of the dump sample need a frozen agent passing its good on).

**Reproduce:** `python3 k4/zmh_zx.py INST.json` with INST.json = [the profile above]; the second implementation
`python3 k4/zmh_xcheck.py INST.json` confirms def*, the Z′-maximum and the number of repairing moves (it does not
classify owners).
