# ZMOVE at one frozen agent (f = 1)

Workstream `proof/k4-zmove-f1`. Target: Theorem ZMOVE (`k4/f2.md` §7.2) at f = 1, i.e. Conjecture K4.SX.COVER's
conclusion in its weaker, move form: for every strict profile of every connected k = 4 core with f = 1 and ω ≥ 1, and
every key κ = (g, x) with def*(κ) > 0, at some (better: every) Z′-maximum Q of κ one (T3) move with at most one helper
(who gives up a good) from P_Q reaches a state of deficit ≤ 0. Nothing here changes K4.D or K4.T. Written proofs here
are CONJECTURE rows until refereed ("written proof in `k4/zmove_f1.md` §x, not yet refereed"); data rows are EVIDENCE.

Milestones: (1) Conjecture S1c (K4.TB.S1C) at every n; (2) the open cases of K4.SX.COVER; (3) ZMOVE at f = 1.

**Status.** Work in progress.

## 0. Setting

Notation of `k4/c4x.md` §1, `k4/c4min.md` §1, `k4/c4min_reduce.md` §1–§2, `k4/c4min_f1.md` §1–§2 and `k4/sx.md`
§1–§3. Tool: `k4/zf1_lib.py` (configurations at an f = 1 key, written from the definitions; no repository imports).
