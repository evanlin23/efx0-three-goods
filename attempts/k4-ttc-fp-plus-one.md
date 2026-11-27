# Failed: the pointer rule FP+1^max (a minimal pointer fixed point, then at most one move) at n = 5 outside K4.MC2

Workstream `proof/k4-ttc` (`k4/ttc.md` §14.3). **Status:** refuted on a strict connected k = 4 core with ν = n = 5,
in which one agent has two private goods. Not refuted in the K4.MC2 class: every MC2-class OC₁^max failure tested
satisfies it (the 11 n = 4 instances of `compute/k4-oc1max-cert` and the walks around them).

## The rule

At a maximum-matching serial-dictatorship start Y, with junk J:
- either one improving move gives a one-absorber completion (OC₁^max); or
- some *minimal pointer fixed point* exists, and after it the bases have a one-absorber completion, or one more move
  gives one.

A minimal pointer fixed point is the fixed point of the pointer map of `k4/ttc.md` §11, with minimality added. It is a
chain (x₀, …, x_t) with:
- x₀ dangerous (frozen and valuing junk), taking as its new base an inclusion-minimal improving set H ⊆ J and nothing
  from any base;
- each x_i (i ≥ 1) taking exactly x_{i−1}'s pick, so the chain follows a pure want path;
- x_t a receiver (unfrozen).

It is a TTC-style rule: every pointer is a single demand. The rule implies OC₂^max.

## Smallest failing configuration (n = 5, m = 9)

`results/k4_ttc/oc1max_cex_n5_two_private.json`, instance 0.

| agent | goods (value) | pick |
|---|---|---|
| 0 | g0 (3), g4 (2), g5 (10), g6 (6) | g4 |
| 1 | g2 (4), g3 (1), g4 (6), g6 (8) | g6 |
| 2 | g0 (2), g1 (8), g5 (5), g6 (4) | g0 |
| 3 | g2 (5), g4 (4), g5 (8), g6 (2) | g5 |
| 4 | g0 (7), g1 (8), g7 (2), g8 (4) | g1 |

**The start.** Order (1, 3, 4, 2, 0), picks (g4, g6, g0, g5, g1), a perfect matching (ν = 5), junk
{g2, g3, g7, g8}.

**Core conditions.**
- `is_core4` returns [].
- Agent 4's private goods g7 and g8 satisfy 2 + 4 < 7 + 8.
- Agent 4 has two private goods, so the core is **not** in the K4.MC2 class.

**OC₁^max fails** (the free form too). `refute_oc1.py`, by brute force with no SAT (`refute_oc1max_cex_n5.log`),
finds no completion, free or one-absorber, at the picks or after any of the 37 moves (7 additions, 21 chains,
9 rings). SAT agrees (`oc1max_cex_n5_ttc.log`).

**No minimal pointer fixed point exists.**
- The frozen agents are 1, 2, 3 and 4; the receiver is 0. The dangerous agents are:
  - agent 1, valuing g2 at 4 and g3 at 1;
  - agent 3, valuing g2 at 5;
  - agent 4, valuing g7 at 2 and g8 at 4.
- None of them improves with junk alone: 5, 5 and 6 against picks worth 8.

**OC₂^max holds.**
- *Agent 4 first:* in (2, 4), agent 4 takes g0 plus its private pair {g7, g8} (13 > 8), and agent 2 takes g1. Then
  (0, 1) or (0, 3).
- *Or agent 1 first:* in (0, 1), agent 1 takes g4 plus g2 (10 > 8). Then a chain through agent 4.

In both cases the first move absorbs danger: a dangerous agent takes junk it values into its new base, but as an
*internal* member of the chain, not as x₀.

## Reproduce

```
python3 k4/ttc/oc1max_cex_n4.py results/k4_ttc/oc1max_cex_n5_two_private.json      # SAT + brute force, the moves
(cd k4/ttc && python3 refute_oc1.py ../../results/k4_ttc/oc1max_cex_n5_two_private.json 0)   # independent replay
python3 k4/ttc/oc2max_fp.py grow FILE.json 200 1 1   # FILE: compute/k4-oc1max-cert's results/k4_oc1max/oc1max_cex_n4.json
```

The last command finds 17 such starts among 1,895 grown instances. With `mc2` (no agent with two private goods),
`grow FILE.json 200 3 1 1 mc2` finds no OC₁^max failure at all among 1,819 instances.

## What this says

- In the MC2 class at n = 4, the pointer rule is exactly right: every minimal fixed point is a good first move.
- Outside it, the danger can sit in junk that its dangerous agent values below its pick. Then the agent can absorb it
  only together with a predecessor's pick, inside a chain.
- *A rule covering both:* "first move: some dangerous agent takes danger junk into its new base". This is necessary on
  every OC₁^max failure tested (97 at n = 4, 17 at n = 5), but not sufficient: some danger-absorbing first move is bad
  at every one of them.
- Whether the MC2 class at n ≥ 5 needs the internal form is open. K4.MC2 makes this the relevant question.
