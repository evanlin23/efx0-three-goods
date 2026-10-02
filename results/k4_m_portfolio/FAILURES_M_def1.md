# Failures of `all:KRb (M_def1)`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `H` | 20 | 20 |
| `hunt1_failprofiles` | 2 | 2 |
| `n2` | 155,436 | 189,216 |
| `n3` | 239,320,255 | 299,837,376 |
| `n4_1_all` | 6,743,610 | 7,247,232 |
| `n4_2_all` | 633,898,968 | 724,847,616 |
| `n4_3_7cores` | 614,252,348 | 788,299,776 |
| `n4_s2000` | 1,610,202 | 2,004,000 |
| `n4_s50` | 40,327 | 50,100 |
| `n5_s20` | 506,763 | 631,680 |
| `n5_s200` | 5,063,124 | 6,316,800 |
| `suite` | 84 | 152 |

## Smallest failure (dataset `n2`, n = 2, m = 4)

```
PFAIL cand=all:KRb w=2 n=2 m=4 sets=[[0,1,2,3],[1,2,3]] vals=[[2,3,8,4],[2,3,4]] fa=0:K0=1,K1=0,bt=1,sh=0,c40=1,g2=0,N[om=0,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=0,sh=0,c40=1,g2=0,N[om=0,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=1; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 2, 3], [1, 2, 3]], "vals": [[2, 3, 8, 4], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_M_def1.md   # second implementation
```

