# Failures of `sh:K0`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n3` | 299,112 | 135,892,280 |
| `n4_1_all` | 2,176 | 4,820,688 |
| `n4_2_all` | 423,576 | 458,728,992 |
| `n4_3_7cores` | 24,624 | 431,039,232 |
| `n4_s2000` | 1,324 | 1,272,852 |
| `n4_s50` | 34 | 31,881 |
| `n5_s20` | 126 | 475,674 |
| `n5_s200` | 1,234 | 4,763,575 |
| `suite` | 7 | 144 |

## Smallest failure (dataset `n3`, n = 3, m = 5)

```
PFAIL cand=sh:K0 w=2 n=3 m=5 sets=[[0,1,3,4],[2,3,4],[2,3,4]] vals=[[3,5,7,6],[2,3,4],[2,3,4]] fa=0:K0=0,K1=1,bt=0,sh=0,c40=0,g2=0,N[om=1,r=2,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=4],E[om=1,r=2,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=4];1:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=1,r=2,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=4],E[om=1,r=2,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=4];2:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=1,r=1,rfz=0,ks=2,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=2],E[om=1,r=1,rfz=0,ks=2,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=1,x3=2]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0; agent 1: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0; agent 2: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]], "vals": [[3, 5, 7, 6], [2, 3, 4], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_sh_K0.md   # second implementation
```

