# Failures of `shp:M1`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n2` | 4,620 | 30,760 |
| `n3` | 2,465,400 | 78,475,400 |
| `n4_1_all` | 17,120 | 4,009,200 |
| `n4_2_all` | 3,168,116 | 317,568,000 |
| `n4_3_7cores` | 4,480,798 | 248,616,000 |
| `n4_s2000` | 11,671 | 797,184 |
| `n4_s50` | 266 | 20,036 |
| `n5_s20` | 1,680 | 265,270 |
| `n5_s200` | 17,531 | 2,651,140 |
| `suite` | 5 | 50 |

## Smallest failure (dataset `n2`, n = 2, m = 5)

```
PFAIL cand=shp:M1 w=2 n=2 m=5 sets=[[0,1,3,4],[2,3,4]] vals=[[2,4,5,8],[2,3,4]] fa=0:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=1,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=1,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=0,sh=1,c40=0,g2=1,N[om=1,r=1,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=0 KRb=1 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 3, 4], [2, 3, 4]], "vals": [[2, 4, 5, 8], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_shp_M1.md   # second implementation
```

