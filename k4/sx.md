# DL on the key graph and Conjecture SX (proof/k4-sx)

Workstream `proof/k4-sx`, `k4/dl13.md` §6 item 1 (on branch `proof/k4-dl13`, PR #75). Work in progress; this file is
being written. Nothing here changes K4.D or K4.T.

**Target.** DL on the key graph (`k4/dl13.md` §2.3, Remark): every key κ with least deficit def*(κ) > 0 has a key κ′,
reached by one (T3) or (T4) move from some state of κ (at f ≥ 2: one (T3⁺) or (T4) move, after the coordinator's
refutation of the T3/T4 form at n = 5, f = 3), with def*(κ′) < def*(κ). Route: Theorem Z′ (`k4/c4min_reduce.md` §2,
K4.C4MIN.RED.Z).

Tool: `k4/sx_keygraph.py` (keys, least deficits, key-level neighbours for the edge sets T3, T3⁺, T3 ∪ T4, T3⁺ ∪ T4).
