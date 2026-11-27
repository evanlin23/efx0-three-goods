# Hardness by "profiles covered by few certificate allocations" (k4-hunt; failed as a proxy)

Workstream proof/k4-hunt (`k4/hunt.md`). Idea: in a certified core, the profiles under which at most one allocation of
the CEGAR certificate is EFX₀ should be the hardest (fewest EFX₀ allocations overall), so they would point the hunt
toward near-counterexamples without enumerating profiles.

Method (`k4/hunt/hardest.py`): the ordinal outer encoding of `k4/hunt/cegar.py` with each certificate clause relaxed
by an indicator e_k and at most c = 1 of the e_k true; for each such profile, all EFX₀ allocations are counted by SAT
enumeration (search4's inner encoding with blocking clauses, each one re-checked with the raw definition), up to a cap.

Why it fails: the certificate is tiny compared with the set of EFX₀ allocations, so "covered by one certificate
allocation" says nothing about the total. Smallest failing configuration: the core MC7-1 of `k4/MINCEX.md` §8
(n = 6, m = 15, six P4 agents, [[0,1,2,9],[0,4,8,10],[1,5,7,11],[2,6,8,12],[3,4,6,13],[3,5,7,14]]): the profiles
with at most one of the 770 certificate allocations EFX₀ (e.g. types (3,8,2,4), (2,3,8,4), (6,8,4,3), (3,6,10,2),
(3,2,10,6), (3,10,6,2) on the agents' goods in order) all have at least 5,000 EFX₀ allocations (the cap). On MC7-2,
MC7-3 and MC7-5 no profile is covered by at most one certificate allocation at all.

What is used instead: the certificate size itself (the number of allocations the CEGAR needs to cover a core) as a
per-core hardness measure (`k4/hunt.md` §3–§4).

Reproduce (about 30 s):
```
python3 k4/hunt/hardest.py results/k4_hunt/named_mc7.json.gz --profiles=3
```
