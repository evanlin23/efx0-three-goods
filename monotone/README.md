# Monotone valuations with bounded relevance (workstream proof/monotone-k)

Question: for normalized monotone valuations in which every agent has at most k relevant goods, what is the
smallest k at which EFX₀ can fail? Start with `threshold.md`, the results and the method.

| file | what it is |
|---|---|
| `threshold.md` | the question, the reductions that prune the search (§2), the method and its trust chain (§3), results (§4–5) |
| `k3.md` | Theorem M3: monotone EFX₀ for k ≤ 3, via additive surrogates (Lemma S3) and TARGET |
| `k3_check.py` | exhaustive check of Lemma S3 on all nondegenerate monotone orders of ≤ 3 goods; the r = 4 failure |
| `types4.py` | disjoint-comparison types of a 4-good agent: 912 monotone (exact) against ≥ 336 additive |
| `amm_check.py` | the counterexample of arXiv 2604.18216v4 §3.1 from the raw definition: k = 8, no EFX₀; deletions and merges |
| `amm_modify.py` | can that instance be thinned (agents ignoring goods) with some agents fixed? (`attempts/monotone-lower-relevance-of-amm.md`) |
| `mono_lib.py` | raw definitions: monotonicity, relevance, EFX₀ by brute force |
| `hypergraphs.py` | relevance hypergraphs up to isomorphism, with the pruning of `threshold.md` §2 |
| `check_enum.py` | independent re-enumeration (different method, no shared code), n ≤ 4 |
| `check_enum5.py` | second independent re-enumeration (labeled count vectors, numpy canonical forms), fast enough for n = 5 |
| `synth.py` | SAT encodings (`order`, `rank`), allocation clauses, inner EFX₀ searches (Python; C in `efx0search.c`) |
| `run_search.py` | CEGAR driver per family (n, m, k); writes `results/monotone/n{n}_m{m}_k{k}.jsonl` |
| `check_cert.py` | independent certificate checker (own clause generation, own symmetry breaking, Glucose) |
| `validate.py` | encoding validation on the pinned counterexample; random-profile evidence for certificates |
| `summarize.py` | coverage table; `--recount` checks every result file against a fresh enumeration |

Reproduce a family, e.g. n = 4, k = 4:
```
for m in 8 9 10 11 12; do python3 monotone/run_search.py 4 $m 4 results/monotone/n4_m${m}_k4.jsonl --jobs 4; done
python3 monotone/check_cert.py results/monotone/n4_m*_k4.jsonl
python3 monotone/summarize.py --recount
```
