# Failures of `sh:M1`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n2` | 8,820 | 44,656 |
| `n3` | 1,802,062 | 135,892,280 |
| `n4_1_all` | 2,576 | 4,820,688 |
| `n4_2_all` | 754,873 | 458,728,992 |
| `n4_3_7cores` | 949,968 | 431,039,232 |
| `n4_s2000` | 3,824 | 1,272,852 |
| `n4_s50` | 88 | 31,881 |
| `n5_s20` | 396 | 475,674 |
| `n5_s200` | 4,490 | 4,763,575 |
| `suite` | 18 | 144 |

## Smallest failure (dataset `suite`, n = 2, m = 5)

```
PFAIL cand=sh:M1 w=1 n=2 m=5 sets=[[0,2,3,4],[1,2,3,4]] vals=[[2,3,4,8],[2,3,4,8]] fa=0:K0=1,K1=0,bt=1,sh=1,c40=0,g2=0,N[om=2,r=1,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=1,x3=2],E[om=2,r=1,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=1,x3=2];1:K0=1,K1=0,bt=1,sh=1,c40=0,g2=0,N[om=2,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=2,x3=1],E[om=2,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=2,x3=1]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=0 KRb=1 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=1; agent 1: K0=1 K1=0 M1=0 KRb=1 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=1.

## Reproduce

```
echo '{"sets": [[0, 2, 3, 4], [1, 2, 3, 4]], "vals": [[2, 3, 4, 8], [2, 3, 4, 8]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_sh_M1.md   # second implementation
```

