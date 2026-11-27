# Attempt: RKMAX with no move (proof/k4-rkmax)

**Idea.** Strengthen Conjecture RKMAX (`k4/rkmax.md`, `k4/sdc.md` §31 end) to "the picks of every σ-maximal
maximum-matching start have a one-absorber completion", so that a proof needs only the slot criterion (Lemma 1 of
`k4/oc1_hall.md` §1) and no move. A weaker variant: some receiver z of the σ-maximal start has Θ(z) = ∅ (Prop. T0's
completion, owned by a receiver).

**Result: false, already at n = 4.**
- On the 111,600 profiles of the certifier's n = 4 export, 10,840 of the 198,400 σ-optimal vectors need one move
  (`results/k4_rkmax/rk_check_n4.log`).
- No other rank potential tested (RS, leximin, the number of receivers first, fewest frozen, fewest dangerous or truly
  dangerous agents first, the best worst-receiver rank first) has only zero-move optima. On a 1-in-20 sample of the
  export, the best one ("RS then |U|", "fewest frozen then σ" and "σ then |U|" tie) still needs a move at 15 of 5,580
  profiles (`k4/rkmax/rk_potentials.py`).
- The T0 variant fails much more often: on that sample, every RM-optimum satisfies T0 at only 169 of 5,580 profiles,
  and some Pareto-optimal maximum matching does so at 5,519.
- Some Pareto-optimal maximum matching completes at the picks at every sampled profile (5,580 of 5,580). So
  "OC₁^∃max with zero moves" is not refuted, but no rank-extremal rule found picks such a vector.

**Smallest failing configuration** (n = 2; `python3 k4/rkmax/rk_zero_move.py replay`, log
`results/k4_rkmax/rk_zero_move_replay.log`):
- sets [[0,1,2,3],[0,1,2]], vals [[14,9,25,3],[25,30,35]] (a strict balanced MC2-class core: agent 0 has the private
  good 3);
- σ-max is (1, 1, 0, 0), reached by the picks (0, 2) (ranks 2, 1) and (2, 1) (ranks 1, 2);
- at (0, 2) the junk is {1, 3}, and no one-absorber completion exists. Agent 1 absorbing both is envied by agent 0
  (25 + 9 + 3 − 3 > 14), agent 0 absorbing both is envied by agent 1 (25 + 30 > 35), and in each split of the junk
  agent 0 envies agent 1's two-good bundle. One move repairs, so OC₁ holds;
- the other σ-optimal vector (2, 1) completes at the picks.

So "every σ-optimal vector completes at the picks" fails at n = 2, while "some σ-optimal vector completes at the
picks" holds here. The n = 4 example of the same log has two σ-optimal vectors that need a move (the RF-B
configuration: receiver 0, two truly dangerous agents 2 and 3 sharing the junk goods {3, 4}).

Search: `rk_zero_move.py 2000 2 1` finds three n = 2 examples among the first 197 random MC2-class cores, and
`rk_zero_move.py 3000 3 1` finds three n = 3 examples among the first 148.

**Lesson.** At a σ-maximal start the move cannot be avoided. A proof has to go through the repairs of `k4/rkmax.md` §5
(Prop. T0, Lemma S′, Lemma RF-B), which is Conjecture HS-MAX.

Reproduce: `python3 k4/rkmax/rk_zero_move.py replay`; `python3 k4/rkmax/rk_potentials.py 20`.
