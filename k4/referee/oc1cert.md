# Referee re-check (evidence): the certifier's n = 4 results (`k4/oc1cert.md`, branch `compute/k4-oc1max-cert`)

Referee: `proof/k4-referee`, 2026-11-27.
- The brief: "as a check rather than a proof", re-verify a random sample of the OC₂^max witnesses at n = 4 with my
  own code, and re-verify the 11 n = 4 OC₁^max counterexamples.
- Read: `k4/oc1cert.md` at `fa8e971` in full. Also LEDGER.md rows K4.CORE and K4.OT (the profile domain), and the
  move rules of `k4/oc1cert/brute_verify.py`. The latter was read only to pin down which moves count as official; it
  was not run, and no code was reused.
- Data read: `results/k4_oc1max/oc1max_cex_n4.json` and `results/k4_oc1max/cert_4_depth2.json.gz` (1,002 cores,
  407,454 witnesses: 133,910 picks, 269,082 chains, 4,411 additions, 51 two-move "seq").
- Check: `k4/referee/cert_ref.py`, run by `cert_ref_runs.sh`, log `results/k4_referee/cert_ref.log`. It contains:
  - my own official moves (`k4/sdc.md` §29): additions; chains with t ≥ 1, nonempty passed bases, sets inside the
    receivers' relevant goods and the current junk, strict gains;
  - optionally, the certifier's extra "ring" kind;
  - one-absorber and free completions by brute force;
  - raw EFX₀;
  - my own simulation of each witness.

## Verdict: CONFIRMED (evidence)

### The 11 OC₁^max counterexamples (all confirmed)

For each of the 11 (4_n4_3 #58, #77; 4_pure #20, #21, #23, #24, #26, #29, #36, #38, #45), my code finds:
- the printed picks are an SD outcome (1 or 3 orders), the profile is strict and balanced, ν = 4, and the start is
  perfect;
- no one-absorber completion, and no free completion, at the picks or after any official move;
  - 15–32 distinct one-move states;
  - with the certifier's extra rings the state sets are the same, and still none completes;
- two moves repair: 4–7 first moves have a repairing second move;
- the stated pattern: exactly one unfrozen agent, two frozen agents sharing a single junk danger pair, 3 or 4 junk
  goods, and no agent with two private goods;
- EFX₀ allocation counts 14, 24, 18, 21, 19, 20, 19, 24, 18, 62, 54 (#58 has 14, as stated);
- only 1–3 of the 24 orders fail OC₁;
- **ordinality:** 20 random order-preserving perturbations of each profile (×1000 plus noise below 1/4 per good)
  give the same picks, still fail OC₁, and still need exactly two moves (220 of 220);
- the certificate's own two-move witnesses: exactly one "seq" witness of the core validates at each counterexample
  start under my simulation, and no other witness does.

**Wording point.** The note says "neither the picks nor any of the 20–51 states one official move reaches has any EFX₀
completion". In its own log (`brute_verify_cex_n4.log`), 20–51 counts move *descriptions*: the distinct-state counter
was added after that log was written. I count 15–32 distinct states. The claim itself (no completion) is confirmed.

### Random sample of the depth-2 certificate (OC₂^max at n = 4)

Setup:
- 5,000 random core draws among the 1,002 cores, 3 random strict core profiles each, giving 15,000 profiles;
- the profiles are inside the certificate's domain: strict (no two disjoint subsets with equal sums), strictly
  balanced (2v(g) < v(R_i)), and (C4) for two-private agents;
- every SD order whose picks form a maximum matching: 35,858 starts.

At each start:
- (a) OC₂^max decided by my forward search;
- (b) the certificate's witnesses for that core are simulated, and one counts as covering the start if my
  simulation accepts it.

| run | starts | picks complete | one move | two moves | OC₂ fails | covered by a validated witness | uncovered |
|---|---|---|---|---|---|---|---|
| sample, seed 1 | 18,208 | 16,633 | 1,575 | 0 | 0 | 18,208 | 0 |
| sample, seed 2 | 17,650 | 16,122 | 1,528 | 0 | 0 | 17,650 | 0 |

**Two-move witnesses**, near the 11 counterexamples:
- one or two agents of each counterexample profile are re-drawn with strict core values;
- 8,000 profiles, 30,222 starts.

| run | starts | two moves needed | covered, by a validated "seq" witness | uncovered | OC₂ fails | distinct seq witnesses exercised |
|---|---|---|---|---|---|---|
| near, seed 3 | 15,048 | 100 | 100 | 0 | 0 | 13 |
| near, seed 4 | 15,174 | 113 | 113 | 0 | 0 | 11 |

Every witness that validated is a genuine repair under my own definitions:
- its moves are legal official moves from the start;
- its bases lie inside X;
- at most one agent holds two or more goods outside its base;
- X is EFX₀.

No start was found that the certificate fails to cover, and none where my search and the witnesses disagree.

**My own sampling bug, for the record.** My first sampler drew values without the core conditions. It produced a
top-heavy agent (54 > 33 + 17), and the start was "uncovered". That profile is outside the certified domain (K4.CORE's
strict balance). With the domain enforced, no uncovered start remains.

## For the coordinator

- The 11 n = 4 OC₁^max counterexamples are confirmed by an independent brute force, including ordinality under
  perturbation. Each is repaired by two moves, and the certificate's own two-move witness validates there.
- On 35,858 sampled starts and 30,222 starts near the counterexamples (213 of them needing two moves), OC₂^max holds,
  and the depth-2 certificate's witnesses validate under my code. This is evidence for K4.SDC.OC2MAX.N4, not a second
  certificate check: the certifier's own `check.py` remains the proof artifact.
- Wording: "20–51 states" should read "20–51 moves (15–32 distinct states)".
