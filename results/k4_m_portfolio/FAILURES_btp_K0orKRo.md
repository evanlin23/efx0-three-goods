# Failures of `btp:K0|KRo`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `hunt1_failprofiles` | 2 | 2 |
| `n3` | 23,856 | 125,469,216 |
| `n4_3_7cores` | 37,056 | 332,107,776 |
| `n4_s2000` | 79 | 746,407 |
| `n4_s50` | 1 | 18,510 |
| `n5_s20` | 30 | 279,622 |
| `n5_s200` | 219 | 2,800,996 |

## Smallest failure (dataset `n3`, n = 3, m = 6)

```
PFAIL cand=btp:K0|KRo w=4 n=3 m=6 sets=[[0,2,4,5],[1,3,4,5],[2,3,4,5]] vals=[[2,8,4,5],[2,8,3,4],[6,7,3,5]] fa=0:K0=1,K1=0,bt=0,sh=0,c40=0,g2=0,N[om=1,r=1,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=4,x3=2],E[om=1,r=1,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=4,x3=2];1:K0=0,K1=1,bt=1,sh=1,c40=0,g2=0,N[om=1,r=2,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=0,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=6,x3=1];2:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=1,x1=4,x3=2],E[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=1,x1=4,x3=2]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0; agent 1: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=1 Rwo=1 big-top=1; agent 2: K0=1 K1=0 M1=0 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5]], "vals": [[2, 8, 4, 5], [2, 8, 3, 4], [6, 7, 3, 5]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_btp_K0orKRo.md   # second implementation
```

