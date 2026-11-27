# "OC₁ holds at every rank-maximal maximum-matching start": false at k = 5 (n = 3) and k = 6 (n = 3, 4)

Workstream `proof/kgen-n3` (coordinator's request, 2026-11-27); context in `kgen/rf.md`.

**The approach** (coordinator's extremal variant). Define rank_i(Y) = 1 + the number of i's relevant goods valued
above Y_i. Among the maximum-matching SD pick vectors (the picks of some serial-dictatorship order that match ν
agents), call a vector RM-optimal if it lexicographically maximizes (#rank 1, #rank 2, …). The hope was that OC₁
holds at *every* RM-optimal vector. Moves follow the official rule of `k4/sdc.md` §29: additions, chains and rings,
with no empty hand-on, a one-absorber completion, and raw EFX₀.

**Why it seemed right.** It holds on the coordinator's n = 4 and n = 5 data at k = 4
(`k4/sdc/extremal_rank_check.py` on `claude/kind-lamport-y8fdme`, not read here).

**Why it fails at n = 3.** With three agents, every maximum-matching SD vector found has the same signature
(1, 1, 1): the first picker gets rank 1, the second rank 2, the third rank 3. So RM-optimality selects nothing, and
every failing start is RM-optimal. This is the case on all 13 of ksens's n = 3, k = 5 one-chain failures
(`results/k4_ksens/kcegar_k5_n3_D1.log` on main).

**Smallest failing configuration** (n = 3, m = 6, k = 5, strict and balanced; ksens's witness n3_m6_93).
- agent 0 values goods 0, 2, 3, 4, 5 at 3, 33, 39, 35, 43;
- agent 1 values goods 1, 2, 3, 4, 5 at 16, 20, 32, 26, 43;
- agent 2 values goods 1, 3, 4, 5 at 3, 6, 2, 10.
- The order (1, 0, 2) gives the picks (3, 5, 1), a perfect start. OC₁ fails there, and its signature (1, 1, 1) is
  shared by all six maximum-matching vectors.

**With n = 4** (k = 6, m = 7, strict and balanced; found by `kgen/rf/rf_run.py climb 6 4 …`, seed 164000326).
- sets [[0,1,2,3,5],[0,1,2,3,4,6],[0,1,2,3,4,5],[0,1,2,3,4,5]];
- vals [[58,29,57,10,17],[32,47,53,23,31,4],[49,55,57,21,38,3],[59,58,46,2,37,4]].
- The failing start (5, 1, 2, 0) has signature (2, 1, 0, 1, 0, 0), the maximum, which 6 vectors share.
- No n = 4, k = 5 instance found so far has a failing RM-optimal vector (the 3 climb-found k = 5 failures and RD5 do
  not).

**Checks.**
- OC₁ failure: by this workstream's checker (`kgen/rf/rf_lib.py`) and by k4/sdc's `oc1_mc2_rand.Inst.check` on main.
- RM signatures: by two codes, `rf_rm.py`, and `rf_rm_xcheck.py` with brute-force ν.

**Reproduce:**
- `MAINWT=<checkout of main> python3 kgen/rf/rf_rm.py known` (`results/kgen_rf/rf_rm_known.log`);
- `MAINWT=<checkout of main> python3 kgen/rf/rf_rm_xcheck.py` (`results/kgen_rf/rf_rm_xcheck.log`).

**What survives:** the ∃-form. On all 28 instances, some RM-optimal vector satisfies OC₁. RF (receiver first) also
holds on all of them.
