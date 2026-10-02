# Failures of `shp:W`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n4_2_all` | 4 | 317,568,000 |
| `n4_3_7cores` | 48 | 248,616,000 |

## Smallest failure (dataset `n4_2_all`, n = 4, m = 7)

```
PFAIL cand=shp:W w=4 n=4 m=7 sets=[[0,2,5,6],[1,4,5,6],[2,3,5],[3,4,6]] vals=[[2,8,4,5],[2,8,5,4],[4,2,3],[2,4,3]] fa=0:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=0,r=3,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=3,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=0,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];2:K0=0,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=1,r=1,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=1,r=1,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];3:K0=0,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=3,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=1,r=0,rfz=0,ks=3,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 2: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 3: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 5, 6], [1, 4, 5, 6], [2, 3, 5], [3, 4, 6]], "vals": [[2, 8, 4, 5], [2, 8, 5, 4], [4, 2, 3], [2, 4, 3]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_shp_W.md   # second implementation
```

