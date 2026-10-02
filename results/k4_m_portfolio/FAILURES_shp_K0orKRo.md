# Failures of `shp:K0|KRo`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n3` | 125,688 | 78,475,400 |
| `n4_1_all` | 96 | 4,009,200 |
| `n4_2_all` | 53,704 | 317,568,000 |
| `n4_3_7cores` | 31,104 | 248,616,000 |
| `n4_s2000` | 199 | 797,184 |
| `n4_s50` | 3 | 20,036 |
| `n5_s20` | 16 | 265,270 |
| `n5_s200` | 147 | 2,651,140 |

## Smallest failure (dataset `n3`, n = 3, m = 5)

```
PFAIL cand=shp:K0|KRo w=2 n=3 m=5 sets=[[0,3,4],[1,2,3,4],[1,2,4]] vals=[[2,3,4],[3,5,7,6],[2,3,4]] fa=0:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=-1,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=-1,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=0,sh=0,c40=1,g2=0,N[om=-1,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=-1,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];2:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=2,x3=1],E[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=2,x3=1]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 2: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=1 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 3, 4], [1, 2, 3, 4], [1, 2, 4]], "vals": [[2, 3, 4], [3, 5, 7, 6], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_shp_K0orKRo.md   # second implementation
```

