# Failures of `bt2:K0`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n3` | 11,728 | 21,873,024 |
| `n4_2_all` | 1,928 | 20,134,656 |
| `n4_3_7cores` | 636 | 58,392,576 |
| `n4_s2000` | 85 | 125,234 |
| `n4_s50` | 3 | 3,085 |
| `n5_s20` | 36 | 62,154 |
| `n5_s200` | 342 | 619,541 |

## Smallest failure (dataset `n3`, n = 3, m = 5)

```
PFAIL cand=bt2:K0 w=4 n=3 m=5 sets=[[0,1,3,4],[0,2,3,4],[1,2,3,4]] vals=[[2,3,4,8],[2,3,4,8],[1,4,6,8]] fa=0:K0=0,K1=1,bt=1,sh=1,c40=0,g2=0,N[om=1,r=2,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=2,x3=4],E[om=1,r=2,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=2,x3=4];1:K0=0,K1=1,bt=1,sh=1,c40=0,g2=0,N[om=1,r=2,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=4],E[om=1,r=2,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=4];2:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=0,r=0,rfz=0,ks=2,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=1,r=1,rfz=0,ks=2,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=2]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=1; agent 1: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=1; agent 2: K0=1 K1=0 M1=1 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4]], "vals": [[2, 3, 4, 8], [2, 3, 4, 8], [1, 4, 6, 8]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_bt2_K0.md   # second implementation
```

