# Refuted: Conjecture D1-LONG and Sub-lemma D1-H(ii) in canonical form (workstream proof/k4-oc1-hall)

**Claims** (`k4/oc1_hall.md` §21).
- *D1-LONG:* at a one-absorber-hard start with one dangerous agent k, some longest *canonical* chain from k, with a
  minimal improving H₀, leaves an S\* completion owned by k. A canonical chain is one in which every chain agent takes
  its predecessor's pick alone, with no head junk.
- *D1-H(ii):* a longest canonical chain with HEAD, or the chain through a second wanter, repairs with owner k.

**Evidence that looked good.**
- 197 of 197 starts with n ≤ 5, every order.
- 309 of 309 sampled hard starts at n = 6–8.
- Adversarial climbs at n = 4, 5 bottomed out at one repairing pair.

**Counterexample D1H-X** (found by `proof/k4-d1`, `k4/d1/verify_cex.py` on that branch; re-verified here).
- n = 3, m = 8. Sets [[0,1,5,7],[3,4,6,7],[0,2,5,7]], values [[26,3,25,27],[19,17,25,30],[9,14,7,29]], order (0, 1, 2),
  picks (7, 6, 2).
- J = {0, 1, 3, 4, 5}, F = D = {0}, and agents 1 and 2 both want good 7.
- It is hard: `ohlib.absorb_brute` and the SAT test agree.
- It is **not a core**: `hcore.is_core4` on the dense value matrix says agent 1 has 3 private goods of 4
  (`k4/oc1_hall/d1h2_tests.py`). Whether canonical D1-LONG fails on a strict core is therefore not known from this
  instance.
- Both canonical chains, (0, 1) and (0, 2), have HEAD for every improving H₀, and no owner k or head works after
  either. After (0, 2) the off-chain second wanter 1 can own.
- The ED chain (0, 2), in which the head takes 7 together with junk good 0 (or 5), with H₀ = {1, 5} (or {0, 1}),
  repairs with owner k: [[1,5,2,4],[6,3],[7,0]]. So the ED-MIN form of §15, which allows head junk, survives.

**Smallest failing configuration:** D1H-X itself (n = 3, m = 8). The §21 data have no instance of it, because their
n = 3 profiles have m ≤ 7.

**Lesson.** HEAD is not always cured by the other wanter, or by a longer chain. The head itself may need one junk
good of its own danger set. The open sub-lemma becomes D1-HJ (`proof/k4-d1`): at a hard start where every canonical
chain from k has HEAD, some chain whose head adds at most one junk good, with a minimal H₀, repairs with owner k.

**Repro:** `python3 k4/oc1_hall/d1long_cex.py` (log `results/k4_oc1_hall/d1long_cex.log`).
