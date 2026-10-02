# Failures of `nobt:K0|KRo|Rwo`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n4_s2000` | 1 | 797,184 |

## Smallest failure (dataset `n4_s2000`, n = 4, m = 11)

```
PFAIL cand=nobt:K0|KRo|Rwo w=1 n=4 m=11 sets=[[0,2,8,10],[1,5,8,10],[3,6,9,10],[4,7,9,10]] vals=[[3,8,10,4],[2,6,7,10],[5,3,7,6],[5,3,7,6]] fa=0:K0=1,K1=0,bt=0,sh=0,c40=0,g2=0,N[om=3,r=2,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=5,r=3,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=4,x3=8];1:K0=1,K1=0,bt=0,sh=0,c40=0,g2=0,N[om=3,r=2,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=5,r=3,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=4,x3=8];2:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=5,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=c,x3=2],E[om=6,r=1,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=d,x3=2];3:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=5,r=0,rfz=0,ks=3,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=c,x3=2],E[om=6,r=1,rfz=0,ks=3,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=d,x3=2]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=1 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=1 KRb=1 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=0; agent 2: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 3: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 8, 10], [1, 5, 8, 10], [3, 6, 9, 10], [4, 7, 9, 10]], "vals": [[3, 8, 10, 4], [2, 6, 7, 10], [5, 3, 7, 6], [5, 3, 7, 6]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_nobt_K0orKRoorRwo.md   # second implementation
```

