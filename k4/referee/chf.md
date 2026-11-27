# Referee report: Proposition CH-F (W(3, 1) and W(4, 1) are false) and Proposition DU (`kgen/charity.md`, branch `claude/kgen-charity`)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `kgen/charity.md` at `8862555` (CH-F, §6; DU, §3) and `attempts/kgen-charity-welfare-maxima.md`.
- Data: the two instances' values are taken from those texts, and for the k = 3 instance from the table in
  `kgen/charity/w_counterexample.py`. They were read as data; the script was not run.
- Check: `k4/referee/chf_ref.py`, log `results/k4_referee/chf_ref.log`. It uses no SAT and no MILP, so it is
  independent of both methods the session used.

## Verdicts

| item | verdict |
|---|---|
| CH-F, k = 4 instance (S′(3, 4)'s hypergraph, n = 9, m = 14) | **CORRECT**: the stranded state (goods 6, 7 out, total 198) is the unique welfare maximum; every EFX₀ allocation with ≤ 1 good out has total ≤ 197, and 197 is attained |
| CH-F, k = 3 instance (S′(3, 3) with relays, n = 12, m = 17) | **CORRECT**: the same with 484 against ≤ 483, and 483 is attained |
| Proposition DU (disjoint unions are completable) | **CORRECT** (written proof re-derived; see `charity.md` §5) |

## 1. Method (exact, from the raw definition)

**Reduction.** Let X be a partial EFX₀ allocation, and let X^v keep only the goods held by one of their valuers. Then
X^v is EFX₀ with the same welfare:
- removing a good its holder values at 0 changes no agent's own value;
- it only shrinks the other bundles, and threats are monotone in the bundle.

So every partial EFX₀ allocation of welfare ≥ T arises from an EFX₀ *orientation* of welfare ≥ T, with the other
goods set aside and then placed on non-valuers or left out.

**Search.**
1. A depth-first search enumerates every EFX₀ orientation with welfare ≥ T. Each good goes to one of its valuers or
   is set aside. Two prunes, both sound:
   - the welfare bound (current welfare + each remaining good at its best valuer);
   - a strong-envy violation that persists even if the envier receives every good it values among those left.
2. For each orientation found, an exhaustive search over the placements of its set-aside goods on non-valuers, with
   at most one good left out, tests raw EFX₀. The prune: a bundle already strongly envied stays so.

The claim "every EFX₀ allocation with ≤ 1 good out has total ≤ T − 1" holds iff no orientation of step 1 admits such
a placement.

## 2. Results

| instance | stranded state EFX₀, total | EFX₀ orientations with welfare ≥ total | completable with ≤ 1 out | best with ≤ 1 out (sanity run at total − 1) |
|---|---|---|---|---|
| k = 4 (n = 9, m = 14) | yes, 198 (goods 6, 7 out) | 1 (the stranded state) | 0 | **197**, e.g. agent s₂ keeps only good 4 and goods 5, 6, 7 are placed or left out (one) |
| k = 3 (n = 12, m = 17) | yes, 484 (goods 6, 7 out) | 1 (the stranded state) | 0 | **483**, the analogous state |

So in both instances the welfare maximum over partial EFX₀ allocations is unique and leaves two goods out, and the
statements W(4, 1) and W(3, 1) are false. The sanity runs show that the placement search is not vacuous.

Single implementation on my side, but independent of the session's two (SAT and MILP), and it agrees with both.
