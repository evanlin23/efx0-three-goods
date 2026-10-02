# Failures of `gap:K0|KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `hunt1_failprofiles` | 2 | 2 |
| `n3` | 1,674,584 | 299,837,376 |
| `n4_1_all` | 7,844 | 7,247,232 |
| `n4_2_all` | 1,637,976 | 724,847,616 |
| `n4_3_7cores` | 2,862,076 | 788,299,776 |
| `n4_3_every12` | 7,879,720 | 2,705,301,504 |
| `n4_s2000` | 7,557 | 2,004,000 |
| `n4_s50` | 184 | 50,100 |
| `n5_s20` | 1,439 | 631,680 |
| `n5_s200` | 14,277 | 6,316,800 |
| `suite` | 2 | 152 |

## Smallest failure (dataset `n3`, n = 3, m = 5)

```
PFAIL cand=gap:K0|KRb w=1 agent=2 n=3 m=5 sets=[[0,2,3,4],[1,2,3,4],[1,3,4]] vals=[[4,6,1,8],[3,7,5,6],[2,3,4]] fa=0:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=-1,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=-1,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=0,sh=0,c40=1,g2=0,N[om=-1,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=-1,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];2:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=2,x3=1],E[om=1,r=0,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=1,Rwo=1,x1=2,x3=1]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 2: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=1 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 3, 4], [1, 2, 3, 4], [1, 3, 4]], "vals": [[4, 6, 1, 8], [3, 7, 5, 6], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_gap_K0orKRb.md   # second implementation
```

