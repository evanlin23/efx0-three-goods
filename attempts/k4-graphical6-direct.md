# The 6 graphical all-P4 cores of K4.MC7, certified directly: out of reach here (2026-11-28)

**Target.** K4.MC7 (TARGET₄ for β ≤ 4) covers 6 cores only through the multigraph theorem of Afshinmehr et al.:
graphical all-P4 cores with n = 6, m = 15 and 288⁶ ≈ 5.7·10¹⁴ profiles each, listed in
`results/k4_min_cex_cores_4.json.gz`. Certifying them directly would make K4.MC7 independent of that paper.

**Attempt.** `k4/frontier/graphical6.py` runs the frontier CEGAR (`k4/frontier/search.py`, scanner `scan2.c`,
`--tries=2`) on all 6, one process per core on 4 CPUs.

**Result.** It was stopped by the 2-hour background-job limit (14:17–16:17 UTC) with **no core finished**. The earlier
MINCEX run (old scanner) timed out too, at 120–3600 s per core. The CEGAR keeps no checkpoint inside a core, so a
core that needs more than 2 h cannot finish under this environment's job limit, and reruns start over. The line is
dropped under the kill rule.

**What would close it.** A run without the 2-hour limit (the user's machine: `python3 k4/frontier/graphical6.py OUT.jsonl`),
symmetry reduction (all six are 4-regular-like graphical cores with large automorphism groups), or a direct k = 4
proof of the multigraph theorem for cores.

**Smallest failing configuration:** core 0, sets [[0,1,2,9],[0,2,8,10],[1,4,7,11],[3,5,6,12],[3,6,8,13],[4,5,7,14]]
(n = 6, m = 15, all P4).

    python3 k4/frontier/graphical6.py OUT.jsonl 0
