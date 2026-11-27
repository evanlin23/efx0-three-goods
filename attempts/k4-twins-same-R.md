# Attempt: reduce twins (two agents with the same relevant set) in a minimal counterexample to TARGET₄

Workstream `proof/k4-twins` (`k4/TWINS.md`). Failed except where the twins share two goods that nobody else values (the
closed double edges of K4.MC8, which are reduced). Generator only (`k4/twins4.py` on `k4/reduce4.py`); the reductions
tried are DEL, the copy gadgets KEEP-e / KEEP-f (one twin kept on the same goods, the other deleted), and every
one-agent gadget h on the boundary goods plus 0, 1 or 2 gadget goods (menu of reduce4's valuation classes, at most 4
goods). All use the unenvied bundle (Lemma M1(b)).

**Why try it.** Twins (identical relevant sets, possibly identical types) are the local form of "few valuation types",
under which EFX is known globally (identical valuations; `proofs/citations.md`, Akrami et al. 2608.08864, read; the
Plaut–Roughgarden original is [unverified] here). In the β = 5, n = 6 candidate list (`claude/k4-hunt-cegar`), 782 of
30,337 cores have twins.

**Results** (pair profiles; 6 types per 3-good agent, 288 per 4-good agent):

| configuration | goods | profiles | reduced |
|---|---|---|---|
| twins-Q3-0 | e, f on (a, b, c), all boundary | 36 | 0 |
| twins-Q3-1 | e, f on (g0, a, b), g0 of degree 2 | 36 | 26 |
| twins-Q3-2 = dbl-Q3-Q3-c1 | e, f on (g0, g1, a) | 36 | 36 (certified, K4.MC8) |
| twins-P3 | e on (G1, G2, p_e), f on (G1, G2, p_f) | 36 | 26 |

- twins-Q3-0 (and every configuration with I = ∅ and two agents): **no reduction under Lemma M1/M1(b) exists, for any
  gadget.** Proof in `k4/TWINS.md` §3: a smaller gadget has one agent h; the state "h holds its favourite good b of R and
  all its gadget goods, a and c each lie in an outside bundle with outside goods, h's bundle unenvied" is admissible for
  every valuation of h, and the extension can hand only b to e and f.
- twins-Q3-1: the 10 profiles left include both identical-type ones in which g0 is ranked last (e = f = (g0: 2, a: 4,
  b: 3) and e = f = (g0: 2, a: 3, b: 4)). So "identical types" does not rescue it.
- twins-P3: two gadget goods and the copy gadgets add nothing to the 26 of `attempts/k4-mincex-twins.md`.

**Smallest failing configuration.** twins-Q3-1 with e on (g0, a, b) = (3, 4, 2) and f on (g0, a, b) = (3, 2, 4) (each
ranks its own boundary good first, g0 second):
- DEL fails at the state where a and b lie together in one outside bundle without outside goods, unenvied: one of e, f
  gets nothing but g0 is the only interior good, and the other is threatened by {a, b} (θ = 4 > 3 for e).
- The best one-agent gadget, h = (a: 1, b: 2) (it reduces 14 profiles), fails at the state h holds {b, z′}, a lies in
  an outside bundle with outside goods, h's bundle unenvied.

Reproduce: `cd k4 && python3 twins4.py why twins-Q3-0 twins-Q3-1 --zs=0,1,2` (coverage and the failing states),
`python3 twins4.py explore twins-P3 --copies` (twins-P3 with the copy gadgets).
