# Failures of `bt1:W (M_bt1)`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `hunt1_failprofiles` | 2 | 2 |
| `n4_3_7cores` | 32 | 273,715,200 |
| `hunt1` (hunt) | 1 annealing walks ended in a failure | – |

## Smallest failure (dataset `hunt1_failprofiles`, n = 4, m = 8)

```
PFAIL cand=bt1:W w=1 n=4 m=8 sets=[[0,3,4,6],[1,3,6,7],[2,5,6,7],[4,5,7]] vals=[[3,10,2,6],[2,8,4,5],[2,8,5,4],[2,4,3]] fa=0:K0=0,K1=0,bt=1,sh=1,c40=0,g2=0,N[om=2,r=2,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=1,x3=2],E[om=2,r=2,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=1,x3=2];1:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=1,r=2,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=1,r=2,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];2:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=1,r=0,rfz=0,ks=2,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=1,r=0,rfz=0,ks=2,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];3:K0=0,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=2,r=1,rfz=0,ks=3,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=1,rfz=0,ks=3,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=1; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 2: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 3: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 3, 4, 6], [1, 3, 6, 7], [2, 5, 6, 7], [4, 5, 7]], "vals": [[3, 10, 2, 6], [2, 8, 4, 5], [2, 8, 5, 4], [2, 4, 3]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_M_bt1.md   # second implementation
```

## Notes

- The profile: core 202 of `results/k4_certs_4_n4_3.json.gz` (n = 4, m = 8, three 4-good agents),
  `sets=[[0,3,4,6],[1,3,6,7],[2,5,6,7],[4,5,7]] vals=[[3,10,2,6],[2,8,4,5],[2,8,5,4],[2,4,3]]`. Agent 0 is the only
  big-top agent (10 > 6 + 3; agents 1 and 2 have 8 < 5 + 4). Found by the annealing hunt (`hunt1.log`, walk from a random
  start, step 48,881).
- **rulef.c itself** (unchanged, `/tmp/k4_rulef_5721abf3bc9e25b1`, single profile): `-A41 -E1 -D5 -Y1` gives agent 0
  Lemma K deficits 1 (need-shrinking) and 1 (envy-free), not C40, no single rotation (`k1 = 0`), also with `-N1` (no
  upgrades); `-A40` gives LB₄ʳ(τ₀) more than one rotation; `-A42 -Q2` ("the first big-top agent") puts it in the open
  class. Agents 1 and 2 are in K0, so **Lemma M holds** on this profile.
- **Exact, in the second implementation** (PR #33's model, `lb4r.reach` + `lb4r.any_output`, Lean's `Output` with
  the owner's needs from the bundle): LB₄ʳ(τ₀) has no output with 0 or 1 rotations under each of the three policies
  (need-shrinking, envy-free, none) and has one with 2. So even the exact classes (Lemma K′, all policies) do not
  contain the unique big-top agent: "exactly one big-top agent q ⇒ τ_q needs at most one rotation" is false.
- **Why `k4/rulef.md` §5.2 reports it as true** ("if exactly one agent is big-top, that agent is in class K0 or K1",
  from `rulef.c -A42 -Q2`, `results/k4_rulef/btrk_n4_n4_3.log`): mode 42 evaluates `bigtop_agent(a)` only up to the
  first big-top agent, so the lazy type splitting never separates the profiles where agents 1 and 2 are big-top from
  those where they are not. The leaf that contains this profile has a representative with three big-top agents (the
  log's FAIL line `sets=[[0,3,4,6],[1,3,6,7],[2,5,6,7],[4,5,7]] vals=[[3,10,2,6],[2,8,3,4],[2,8,4,3],[2,4,3]]`), and
  the "every uncertified profile has two or three big-top agents" count was read off the representatives. The class
  counts of rulef.md (weights) are right; the big-top attribution of the leaves is not. `k4/lemmam_portfolio.c`
  compares big-top for every agent, so its leaves are split on it.
- Consequence for the provers: route (a) of rulef.md §6 ("with exactly one big-top agent q, the run of τ_q satisfies
  M1 or Lemma KR's hypotheses") is false as stated, already for K0 ∪ K1 and for the exact LB₄ʳ.
