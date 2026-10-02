# Failed: S1c in local form (big-top x with two terminals ⇒ P_Q completable)

Workstream `proof/k4-zmove-hall` (`k4/zmove_hall.md` §3). REFUTED (a candidate statement, not a ledger claim).

**Statement tried (S1c⁺).** f = 1, ω ≥ 1, κ = (g, x) any key, Q a Z′-maximum at κ. If x is big-top on g and Q has at
least two terminals, then def(P_Q) ≤ 0.

It would prove Proposition S1c (K4.TB.S1C: at a *non-completable* key, two terminals at a Z′-maximum force x not
big-top) by a local argument at P_Q alone, without using that every other configuration of κ fails too.

**Why it was plausible.** On random profiles (`k4/zmh_s1c.py`, 146,430 random strict profiles of the n = 3 and n = 4
cores, 4,418 with f = 1) there are 127 Z′-maxima with a big-top x and two terminals (all at completable keys, as S1c
predicts); at 126 of them P_Q itself already has deficit ≤ 0, through the parking exchange of `k4/zmove_hall.md` §3.

**Smallest failure found** (n = 3, m = 8, ω = 3):
`{"sets": [[0,2,5,7],[1,4,6,7],[3,5,6,7]], "vals": [[6,2,3,10],[4,2,3,8],[3,2,4,8]], "m": 8}`
- all three agents have top 7; agent 0 is big-top on 7 (10 > 6 + 3), and so are agents 1 and 2;
- key κ = (7, agent 0): its unique Z′-maximum is Q = {1: {1,4}, 2: {3,6}}, L = {0,2,5} = U_x, potential (2, 11);
  both free agents are terminals and both are leaves; def(P_Q) = 1;
- def*(κ) = 0: agent 2 re-bases from {3,6} to {3,5} (it parks x's lower good 5, its own smallest good), 6 goes to the
  pool, and agent 1 owns {1,4,0,2,6}. That configuration has the lower potential (2, 10).

So S1c is a statement about the key, not about its maximum: the parking that protects x lowers the potential, and only
non-completability of κ (every configuration fails) excludes it. The n = 3 proof of S1c in `k4/zmove_hall.md` §3 uses
exactly that.

**Reproduce** (both implementations; seconds): `python3 attempts/k4_zmh_attempts.py`.
