# Failures of `bt2:K0|KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n4_2_all` | 4 | 20,134,656 |
| `n4_3_7cores` | 96 | 58,392,576 |
| `n4_s2000` | 1 | 125,234 |
| `n5_s20` | 3 | 62,154 |
| `n5_s200` | 25 | 619,541 |

## Smallest failure (dataset `n4_2_all`, n = 4, m = 8)

```
PFAIL cand=bt2:K0|KRb w=1 n=4 m=8 sets=[[0,2,4,6],[1,3,5,7],[4,6,7],[5,6,7]] vals=[[2,3,4,8],[2,3,4,8],[2,3,4],[2,4,3]] fa=0:K0=0,K1=1,bt=1,sh=1,c40=0,g2=0,N[om=3,r=3,rfz=0,ks=0,M1=0,KRb=0,KRa=1,KRo=1,Rw=0,Rwo=0,x1=3,x3=8],E[om=3,r=3,rfz=0,ks=0,M1=0,KRb=0,KRa=1,KRo=1,Rw=0,Rwo=0,x1=3,x3=8];1:K0=0,K1=1,bt=1,sh=1,c40=0,g2=0,N[om=3,r=2,rfz=0,ks=1,M1=0,KRb=0,KRa=1,KRo=1,Rw=0,Rwo=0,x1=3,x3=4],E[om=3,r=2,rfz=0,ks=1,M1=0,KRb=0,KRa=1,KRo=1,Rw=0,Rwo=0,x1=3,x3=4];2:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=2,r=1,rfz=0,ks=2,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=1,rfz=0,ks=2,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];3:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=2,r=1,rfz=0,ks=3,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=1,rfz=0,ks=3,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=0 K1=1 M1=0 KRb=0 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=1; agent 1: K0=0 K1=1 M1=0 KRb=0 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=1; agent 2: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 3: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 4, 6], [1, 3, 5, 7], [4, 6, 7], [5, 6, 7]], "vals": [[2, 3, 4, 8], [2, 3, 4, 8], [2, 3, 4], [2, 4, 3]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_bt2_K0orKRb.md   # second implementation
```

