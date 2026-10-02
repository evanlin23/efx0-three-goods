# Failures of `gapn:K0|KRo|Rwo`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `hunt1_failprofiles` | 2 | 2 |
| `n3` | 145,778 | 299,837,376 |
| `n4_2_all` | 6,704 | 724,847,616 |
| `n4_3_7cores` | 59,872 | 788,299,776 |
| `n4_3_every12` | 147,928 | 2,705,301,504 |
| `n4_s2000` | 269 | 2,004,000 |
| `n4_s50` | 9 | 50,100 |
| `n5_s20` | 62 | 631,680 |
| `n5_s200` | 481 | 6,316,800 |

## Smallest failure (dataset `n3`, n = 3, m = 6)

```
PFAIL cand=gapn:K0|KRo|Rwo w=1 agent=0 n=3 m=6 sets=[[0,2,4,5],[1,3,5],[2,3,4,5]] vals=[[1,4,6,8],[2,4,3],[2,10,6,7]] fa=0:K0=0,K1=0,bt=0,sh=0,c40=0,g2=0,N[om=1,r=1,rfz=1,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=2,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=1,x3=4];1:K0=0,K1=1,bt=0,sh=1,c40=1,g2=0,N[om=1,r=2,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=0,x3=0],E[om=1,r=2,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=0,x3=0];2:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=0,r=2,rfz=0,ks=2,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=2,rfz=0,ks=2,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0; agent 2: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 4, 5], [1, 3, 5], [2, 3, 4, 5]], "vals": [[1, 4, 6, 8], [2, 4, 3], [2, 10, 6, 7]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_gapn_K0orKRoorRwo.md   # second implementation
```

