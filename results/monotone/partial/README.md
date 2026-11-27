# Partial results (PARTIAL: runs stopped at wind-down, 2026-11-27)

- `n3_m8_k7_only.partial.jsonl`: n = 3, k = 7, m = 8, hypergraphs with a 7-good agent. 97 of 99 records:
  96 UNSAT, 1 TIMEOUT, (1,6,7,7,7,7,7,7). Not run to the end: (3,3,5,6,7,7,7,7) and (3,5,6,7,7,7,7,7).
- `n3_m9_k7_only.partial.jsonl`: m = 9, 186 of 188 records: 185 UNSAT, 1 TIMEOUT, (1,2,5,6,7,7,7,7,7).
  Not run to the end: (1,3,5,6,6,7,7,7,7) and (3,3,5,5,6,6,7,7,7).

The UNSAT records here come from the search alone. The independent checker (`monotone/check_cert.py`) was
started on them and stopped before it finished, so they are single-implementation results, not certified.
