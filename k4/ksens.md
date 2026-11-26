# k-sensitivity: where SD-C, MD, OC and OC₁ break as k grows

Angle `proof/k4-ksens` of the TARGET₄ campaign (`k4/attack_log.md`), branch `claude/k4-ksens`. Code `k4/ksens/`, logs
`results/k4_ksens/`. Definitions as in `k4/sdc.md` §2 (SD-C), §28 (MD), §29 (OC, OC₁). Random and climbed instances
are evidence only (PROMPT.md §5 rule 3).

## Status (burst 1, in progress)

- Tool: `k4/ksens/ocsat.py` decides SD-C, MD, OC and OC₁ for one start with one SAT call each (the chain is encoded
  in SAT, no set-size bounds), any k. It agrees with k4/sdc's enumerative implementation on 1,758 starts at k = 4–6,
  including the exact number of repairing states (`results/k4_ksens/xcheck_ocsat_*.log`, 0 mismatches).
- Random junk-rich surveys at k = 5, 6, 8 (n = 4, 4,800 instances): no failure of any of the four.
- Climbs: running.

## Why

If OC₁ (or SD-C) held for every k it would prove EFX₀ existence for all additive instances, so a proof of OC₁ at
k = 4 must use k ≤ 4 somewhere. This note looks for the smallest k at which each conjecture fails and for the property
of k ≤ 4 that the failing configuration violates.
