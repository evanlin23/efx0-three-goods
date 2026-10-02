# Failures of `sh:K0|KRo`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n3` | 2,880 | 135,892,280 |
| `n4_2_all` | 1,696 | 458,728,992 |
| `n4_3_7cores` | 5,760 | 431,039,232 |
| `n4_s2000` | 16 | 1,272,852 |
| `n5_s20` | 1 | 475,674 |
| `n5_s200` | 23 | 4,763,575 |

## Smallest failure (dataset `n3`, n = 3, m = 5)

```
PFAIL cand=sh:K0|KRo w=4 n=3 m=5 sets=[[0,2,3,4],[1,2,3,4],[1,2,3,4]] vals=[[4,2,3,8],[7,3,5,6],[7,3,5,6]] fa=0:K0=1,K1=0,bt=1,sh=0,c40=0,g2=0,N[om=-1,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=1,r=2,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=2,x3=4];1:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=6,x3=1],E[om=1,r=0,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=6,x3=1];2:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=6,x3=1],E[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=6,x3=1]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=1; agent 1: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=1 Rwo=1 big-top=0; agent 2: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=1 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4]], "vals": [[4, 2, 3, 8], [7, 3, 5, 6], [7, 3, 5, 6]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_sh_K0orKRo.md   # second implementation
```

