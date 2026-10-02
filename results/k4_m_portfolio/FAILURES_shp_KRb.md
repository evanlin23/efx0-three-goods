# Failures of `shp:KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `H` | 20 | 20 |
| `n2` | 9,996 | 30,760 |
| `n3` | 59,495,276 | 78,475,400 |
| `n4_1_all` | 3,861,260 | 4,009,200 |
| `n4_2_all` | 291,485,705 | 317,568,000 |
| `n4_3_7cores` | 215,254,722 | 248,616,000 |
| `n4_3_every12` | 865,316,990 | 994,816,000 |
| `n4_s2000` | 701,597 | 797,184 |
| `n4_s50` | 17,599 | 20,036 |
| `n5_s20` | 238,416 | 265,270 |
| `n5_s200` | 2,382,932 | 2,651,140 |
| `suite` | 37 | 50 |

## Smallest failure (dataset `n2`, n = 2, m = 4)

```
PFAIL cand=shp:KRb w=5 n=2 m=4 sets=[[0,1,2,3],[1,2,3]] vals=[[1,4,6,8],[2,3,4]] fa=0:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=0,r=1,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=1,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 2, 3], [1, 2, 3]], "vals": [[1, 4, 6, 8], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_shp_KRb.md   # second implementation
```

