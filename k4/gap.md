# The exposed-frozen gap of C₄ᵐⁱⁿ: catalog, hard instances, lemma bench (compute/k4-gap)

EVIDENCE only (PROMPT.md §5 rule 3); ledger rows K4.GAP.*. This file maps the one case of conjecture C₄ᵐⁱⁿ that
Theorems Z and F of `k4/c4min.md` (PR #41) leave open, and describes a test bench for the lemmas proposed to close it.
Definitions are those of `k4/c4min.md` §1, §3.6 and §4, `k4/c4x.md` §1 (PR #36) and `k4/hall.md` §5 (PR #46).

## 0. The gap

Fix a strict profile of a k = 4 core. f is the fewest frozen agents over 𝒫, and ω = f − (2n − m). A *key* is the pair
(F, φ) of a min-frozen P ∈ 𝒫: its frozen agents and their one-good bases. 𝒩 = φ(F) is the needed set, and U_i = R_i ∖ 𝒩.
A configuration of a key gives every free agent a pair Q_y ⊆ M ∖ 𝒩, with Q_y ∩ U_y admissible; the rest is the pool L.
A frozen agent x is *exposed* if v_x(U_x) > v_x(φ(x)).

The profile is **in the gap** if f ≥ 1, ω ≥ 1 and every key has an exposed frozen agent. Frozen robustness depends
only on the key, so this is the same as "no configuration at the fewest frozen agents is frozen-robust". The other
profiles with ω ≥ 1 are covered by Theorem Z (f = 0) or Theorem F. Every profile with f = 1 is in the gap.

For each configuration the catalog records:
- **valid owners** (`k4/c4min.md` §1): a free o and a set C ⊆ X = Q_o ∪ L such that
  - X ∖ C contains an admissible set of o;
  - |C| is at most the number of frozen agents that o's bundle unfreezes;
  - no x ≠ o strongly envies X ∖ C while holding H_x.

  For each valid owner the catalog keeps the least |C|. A configuration is **simple** if some owner is valid with
  C = ∅: nothing is withheld and nothing is unfrozen.
- **Φ′** = (−t, r, Λ, −p) and **pool-optimality** (`k4/c4min.md` §3.1, §4).
- **Threat edges** o → x, with C = ∅.
- **The class of Lemma H7** (`k4/hall.md` §5) of each threatened frozen agent. The configuration corresponds to the
  pre-allocation of Lemma 1(a): B_y = Q_y ∩ U_y, with junk J_P = M ∖ 𝒩 ∖ ⋃ B_y. A big-top agent has four goods,
  holds its top a, and has a > b + c. The classes are:
  - **G**: x is big-top and R_x ∖ {a} ⊆ J_P.
  - **G1**: not G; o is a chain end of x (a free agent reached from x by need edges through frozen agents); x is
    big-top and R_x ∖ {a} ⊆ J_P ∪ B_o.
  - **L**: not G or G1; o is not a chain end, and the goods of R_x in X ∖ B_o are worth at most v_x(φ(x)), so the
    threat uses a good of B_o.
  - **O**: none of these. Lemma H7 says this cannot happen at a Pareto-maximum.
- **needers** of each φ(x).
- **threat multiplicity**: the number of owners that threaten a frozen agent.

## 1. Tools

- **`k4/gap.c`.** Written from the definitions; it shares no code with `k4/c4min.c`, `k4/hall.c` or `k4/c4x.c`. It
  enumerates 𝒫 (early exit when some P has no need), f, ω, the keys and the class. For every gap profile it enumerates
  every configuration of every key and tests every owner and every C. `-D` adds the removal-only deficit of every
  min-frozen P (`k4/c4x.md` §1) and compares "some P has deficit ≤ 0" with "some configuration has a valid owner"
  (Lemma 1 of `k4/c4min.md`). `-C` dumps every configuration as JSON.
- **`k4/gap_run.py`.** The driver over the certificate files (`check4.core_domains`: every strict balanced type,
  smallest integer representative). It runs every profile or a seeded sample per core, prints the counters with the
  command and the SHA-256 of gap.c, and writes the catalogs `results/k4_gap/*.json.gz`.
- **`k4/gap_model.py`.** A Python model of the same objects: Profile, Config, owners, Φ′, kinds, H7, and the moves of
  `k4/c4min.md` §4 (pool moves; one step along a cycle of the exchange digraph). It shares no code with gap.c.
- **`k4/gap_bench.py`.** The lemma bench (§4).
- **`k4/gap_hard.py`.** The smallest instances per hardness category (§3).

**Cross-checks.**
- Every class count equals #41's table (`k4/c4min.md` §4), computed by different code. The rows that match are n = 2,
  n = 3 and n = 4 with one 4-good agent, where both runs cover every profile.
- The deficit test and the configuration test agree on every gap profile of every run with `-D`: n ≤ 3, all 7,285,840
  profiles; n = 4 with one 4-good agent, all 44,388.
- gap.c and gap_model agree configuration by configuration on the key set, f, ω, Φ′, pool-optimality, the valid owners
  with their least |C|, the threat edges and the H7 classes: every n = 2 gap profile, and 2,971 n = 3 gap profiles
  (every 25th catalog record) (`results/k4_gap_selftest.log`).
- Every counterexample the bench reports is re-derived from scratch by gap_model (its own 𝒫, keys and configurations).

## 2. The catalog

(filled in below)

## 3. The smallest hard instances

(filled in below)

## 4. The lemma bench

(filled in below)

## Reproduce
```
python3 k4/gap_run.py results/k4_certs_2.json.gz -D --rec=1 --out=results/k4_gap/gap_n2.json.gz     # seconds
python3 k4/gap_run.py results/k4_certs_3.json.gz -D --rec=100 --out=results/k4_gap/gap_n3.json.gz   # 91 s on 4 CPUs
python3 k4/gap_run.py results/k4_certs_4_n4_1.json.gz -D --rec=1 --out=results/k4_gap/gap_n4_1.json.gz
python3 k4/gap_run.py results/k4_certs_4_n4_2.json.gz --sample=4000 --seed=4 --rec=1 --out=results/k4_gap/gap_n4_2_s4000.json.gz
python3 k4/gap_bench.py --selftest --catalog=results/k4_gap/gap_n2.json.gz
python3 k4/gap_bench.py --catalog=results/k4_gap/gap_n2.json.gz,results/k4_gap/gap_n3.json.gz
python3 k4/gap_hard.py results/k4_gap/*.json.gz --show=2
```
Every log under `results/k4_gap_*.log` starts with its command.
