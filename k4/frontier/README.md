# k4/frontier: pushing the k = 4 certification (workstream compute/k4-frontier)

Tools for LEDGER open item 15 (computation part): certify k = 4 cores beyond `k4/SCOUT.md` §3, hunt for
counterexamples beyond the certified range, and test constructions from the proof sessions against every certified
core and profile.

## Search: `search.py`, `scan2.c`
`search.py` runs the CEGAR of `k4/search4.py` unchanged in everything that matters for soundness: the same cores
(`search4.cores`, nauty's `genbg`), type domains, inner SAT model (at most one bundle of more than 2 goods, D2) and
safety masks (`search4.Core`), and the same certificate format, so `k4/check4.py` checks its output as it checks
search4's. Only the proposal step changes. `scan2.c` returns a profile that no allocation found so far covers, or
proves there is none. Three prunings, each sound because coverage is monotone:
1. per agent, only the inclusion-minimal rows count (row = the set of allocations under which a type is safe);
2. a prefix set that meets F (allocations safe for all later agents with every type) covers its subtree;
3. a store of prefix sets already proved covered, at levels 1..n-3. Rows only gain bits as allocations are added,
   so the store stays valid from one call to the next.

The last two levels are checked together through columns (for each allocation, the last agent's minimal types it
makes safe). `test_scan2.py` compares `find` with brute force: random rows, one context kept across calls
(13,640 calls, all agree).

Measured runs (no profile without a D2 allocation anywhere):

| cores | count | command | time | allocations |
|---|---|---|---|---|
| n = 5, three 4-good agents | 9,861 | `k4/search4.py 5 --n4=3` (the old scanner) | 56 min on 3 CPUs | 923,281 |
| n = 5, four 4-good agents | 9,846 | `search.py 5 --n4=4` | 95 min on 2 CPUs | 1,566,025 |
| n = 5, pure (288⁵ ≈ 2·10¹² profiles per core) | 4,674 | `search.py 5 --pure --part=0/2`, then `--part=1/2` | 2 × 75 min on 2 CPUs | 1,386,132 |
| n = 6, one 4-good agent | 26,866 | `search.py 6 --n4=1 --tries=2` | 85 min on 2 CPUs | 2,022,655 |

With the old scanner (`k4/scan.c`), a core with four 4-good agents took ~35 s instead of ~1 s (4-core sample). Its
walk grows with the product of the domains, so a fifth 288-type agent multiplies it by up to 48 more; that is why
`k4/SCOUT.md` left pure n = 5 open. It took ~5 CPU-hours here. No symmetry reduction or type lemma was needed: the minimal-row
reduction adapts to the allocations found, and the store carries covered regions from one call to the next.
Next (not run): n = 6 with two 4-good agents, 119,283 cores at ~0.7 s each with `--tries=2`, ≈ 24 CPU-hours plus
checking.

Runs are split into parts with checkpoints:
- `--part=i/k` takes every k-th core; `--m=` restricts m.
- Each part appends to its own `checkpoint_*.jsonl` here. Rerunning resumes from all checkpoints of the same (n, mode).
- The certificate is written only once every core is done.

## Checker changes (`k4/check4.py`)
check4.py's coverage loop was a plain depth-first walk over every type. It was far too slow for n = 5 cores with
four or five 4-good agents (≈ 15 s per core for four 4-good agents, minutes for pure ones). It now uses the same
kind of sound reductions:
- minimal types per agent;
- a memo of covered prefix sets;
- smallest children first;
- the last two agents by columns.

These are written independently of `scan2.c`, in check4's own C string. Everything else in check4 is unchanged:
- type enumeration, raw EFX₀ masks;
- completeness by orbit counting;
- `--expect` and the D2 test.

Evidence that the change is sound:
- `test_check4_fast.py` compares the new coverage answer with main's version (`git show 2039ab7:k4/check4.py`) on
  random allocation subsets of the committed certificates: 240 cores (72 covered, 168 not), all agree
  (`results/k4_frontier_test_check4_fast.log`);
- `k4/test_check4.py` still rejects every corruption (`results/k4_frontier_test_check4.log`);
- every committed k = 4 certificate passes the new version (`results/k4_frontier_recheck.log`);
- a third check, independent of both: `tester.py --oracle` walks every profile of every n ≤ 3 core by brute force
  and finds a certificate allocation that is EFX₀ and D2 for each (3.0·10⁸ profiles).

## Tester for construction candidates: `tester.py`, `tester.c`, `k4plugin.h`
Checks a construction's outputs on every strict profile of every certified core (n ≤ 3 by default: 56 cores,
3.0·10⁸ profiles), or on a random sample (`--sample=N`) for n = 4, 5. Every output is checked with the raw EFX₀
definition and explicit integer values; `--d2` also requires at most one bundle of more than 2 goods. Types are
enumerated in tester.c from scratch (6 and 288; `--ties`: 13 and 1,271). Failures are reported smallest first
(n, then m), each with a certificate allocation that works for the same profile. The construction can be:
- a C plugin: implement `int k4_construct(const k4_inst *I, int *owner)` from `k4plugin.h`,
  `gcc -O2 -shared -fPIC -Ik4/frontier -o my.so my.c`, then `python3 k4/frontier/tester.py --plugin=my.so`;
- any program, over a pipe: `--pipe='python3 mine.py'`, one instance per line (protocol in `tester.py`);
- the certificate itself: `--oracle`, a brute-force re-check of coverage.

`plugins/sd.c` and `plugins/sd_pipe.py` are examples (serial dictatorship, which fails at once). Measured: the
oracle run over n ≤ 3 takes 4 min on one CPU.

## Counterexample hunt: `hunt.py` (EVIDENCE only)
Random and structured k = 4 cores with n = 6–8. The generator draws private goods per agent, then shared goods
with degree ≥ 2 and hub weights (`--skew`). Every output passes `check4.is_core`. For each core, random profiles
are solved in the D2 model. Then hill-climbing on the profile minimizes a score: for each choice of the large
bundle's owner (or none), the number of D2 EFX₀ allocations, capped and summed. Any profile with no D2 allocation
is written out, and it counts only after an independent brute-force check from the raw definition.

Runs (`results/k4_hunt_{6_mixed,6_pure,7_mixed,8_mixed}.log`): 130 cores with n = 6–8, 26,000 random profiles plus
hill-climbing, no profile without a D2 allocation. The climbing barely lowers the score: with cap 2, most owner choices
keep at least two D2 allocations. So these runs are weak evidence. Exhaustive certification (above) is the real test.

## Reproduce
```
python3 k4/frontier/test_scan2.py 300                       # scanner vs brute force
python3 k4/frontier/test_check4_fast.py 40                  # new check4 coverage vs main's
python3 k4/search4.py 5 --n4=3 --jobs=3 --out=results/k4_certs_5_n4_3.json.gz        # ≈ 1 h on 3 CPUs
python3 k4/frontier/search.py 5 --n4=4 --jobs=2 --out=results/k4_certs_5_n4_4.json.gz
python3 k4/frontier/search.py 5 --pure --part=0/2 --jobs=2 --out=results/k4_certs_5_pure.json.gz   # then --part=1/2
python3 k4/frontier/search.py 6 --n4=1 --tries=2 --jobs=2 --out=results/k4_certs_6_n4_1.json.gz
python3 k4/check4.py results/k4_certs_5_n4_3.json.gz --expect 5:3:9861         # likewise 5:4:9846, 5:pure:4674, 6:1:26866
python3 k4/frontier/hunt.py --n=7 --p4=0.6 --skew=1 --cores=30 --climb=40 --seed=13   # EVIDENCE
python3 k4/frontier/tester.py --oracle --n=2,3 --d2         # brute-force re-check of the n <= 3 certificates
```
