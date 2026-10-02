# Failures of `gapn:KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `H` | 20 | 20 |
| `hunt1_failprofiles` | 2 | 2 |
| `n2` | 175,396 | 189,216 |
| `n3` | 275,569,444 | 299,837,376 |
| `n4_1_all` | 7,060,316 | 7,247,232 |
| `n4_2_all` | 697,838,228 | 724,847,616 |
| `n4_3_7cores` | 741,349,630 | 788,299,776 |
| `n4_s2000` | 1,863,967 | 2,004,000 |
| `n4_s50` | 46,724 | 50,100 |
| `n5_s20` | 589,264 | 631,680 |
| `n5_s200` | 5,891,419 | 6,316,800 |
| `suite` | 109 | 152 |

## Smallest failure (dataset `n2`, n = 2, m = 4)

```
PFAIL cand=gapn:KRb w=1 agent=0 n=2 m=4 sets=[[0,1,2,3],[1,2,3]] vals=[[2,3,4,8],[2,3,4]] fa=0:K0=1,K1=0,bt=1,sh=1,c40=1,g2=0,N[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=0,K1=1,bt=0,sh=1,c40=1,g2=0,N[om=1,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=0,x3=0],E[om=1,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=1; agent 1: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 2, 3], [1, 2, 3]], "vals": [[2, 3, 4, 8], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_gapn_KRb.md   # second implementation
```

