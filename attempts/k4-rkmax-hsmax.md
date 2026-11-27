# Attempt: HS-MAX, RKMAX through three named repairs (proof/k4-rkmax)

**Idea** (`k4/rkmax.md` §5). Reduce RKMAX to a static statement about the picks. At a σ-maximal maximum-matching start
whose picks do not complete, one of three refereed or proved repairs should apply:
- Prop. T0: a receiver whose Θ is empty;
- Lemma S′: Theorem S with the kept-out good at any holder;
- Lemma RF-B.

Each is a finite list of inequalities between one agent's subset sums. HS-MAX would then turn RKMAX, and with it
TARGET₄, into a combinatorial statement with no moves.

**Evidence before the refutation.** 0 gaps on every σ-optimal vector of every profile of the n = 4 export (198,400),
of the n = 5 exports (sel2 1,004,160; partial6 1,305,032), and of random MC2-class cores (n = 5: 4,709; n = 6: 2,349).
Logs: `results/k4_rkmax/rk_hsmax_*.log`. The Theorem U/S-only version had 880 gaps on partial6; Lemma S′ closed them.

**Result: false at n = 4** (`k4/rkmax/rk_climb.py`, log `results/k4_rkmax/rk_climb_n4.log`, 45 s).
- *Seeds.* 200 *residue* starts: hard Pareto-optimal maximum matchings with no T0 / S′ / RF-B case. They come from
  the n = 4 export profiles, where every residue start is σ-dominated.
- *Climb.* Change one agent's value at a time, keeping the values strict and balanced and the start a residue start,
  and minimize the number of maximum matchings with a larger σ.
- *Outcome.* 44 climbs reach 0, i.e. a σ-maximal residue start. OC₁ holds at every one by one move, so RKMAX is not
  refuted.
- *Replay.* `python3 k4/rkmax/rk_hsmax_cex.py` (log `results/k4_rkmax/rk_hsmax_cex.log`) checks all 44: strict and
  balanced; σ-maximal maximum matching, Pareto optimal, SD; hard by rklib and by `mmlib.oa_absorbers`; no T0, S′ or
  RF-B case, by exhaustive enumeration; OC₁ by one move; Lemma SINK₁ applies.

**Smallest failing configuration** (n = 4, m = 7; one of the 44, `results/k4_rkmax/hsmax_cex_n4.jsonl`):
- sets [[0,1,2,6],[1,2,5,6],[3,4,5,6],[3,4,5,6]], vals [[1,8,23,18],[24,28,15,26],[5,3,7,6],[7,3,9,8]], picks (2, 1, 6, 5).
- ranks (1, 3, 2, 1); the single receiver is 1; agents 2 and 3 are truly dangerous and share the junk pair S = {3, 4};
  agent 0 is pick-dangerous; Θ(1) = {2, 3}.
- *Why RF-B fails.* Its chain "2 takes S, 1 takes Y_2 = 6" is official, but (B5) fails: agent 0 values all of
  Z = {6, 1, 0}, and 18 + 8 + 1 − 1 = 26 > 23.
- *The repair.* This is the RF-B″ shape of `k4/oc1_hall.md` §24.11. After the chain, agent 3 is unfrozen, since 2 no
  longer wants Y_3. Then 1 absorbs Z ∖ {1}, and agent 3 takes the good 1.

**Lesson.** The repair lemmas must allow the absorber's bundle to lose one good to a holder that the chain unfreezes.
That is Lemma SINK₁ (`k4/rkmax.md` §7), and the surviving form is HS-MAX′ (K4.RKMAX.HSMAX2). The 44 starts lie
outside the export profiles: every residue start inside them is σ-dominated. Random profiles never produced one.
Only the targeted climb did, so HS-MAX′ needs the same adversarial testing before any proof attempt.

Reproduce: `python3 k4/rkmax/rk_hsmax_cex.py`; `python3 k4/rkmax/rk_climb.py 200 3000 2`.
