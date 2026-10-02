# Failures of `btsh:M1|KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n2` | 436 | 88,216 |
| `n3` | 437,131 | 203,944,616 |
| `n4_1_all` | 96 | 5,217,072 |
| `n4_2_all` | 75,690 | 539,049,216 |
| `n4_3_7cores` | 262,233 | 580,723,776 |
| `n4_3_every12` | 458,039 | 2,134,549,504 |
| `n4_s2000` | 602 | 1,543,591 |
| `n4_s50` | 17 | 38,546 |
| `n5_s20` | 42 | 544,892 |
| `n5_s200` | 569 | 5,452,136 |
| `suite` | 7 | 146 |

## Smallest failure (dataset `n2`, n = 2, m = 5)

```
PFAIL cand=btsh:M1|KRb w=1 n=2 m=5 sets=[[0,2,3,4],[1,2,3,4]] vals=[[4,5,6,8],[4,5,6,8]] fa=0:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=1,rfz=0,ks=0,M1=0,KRb=0,KRa=1,KRo=1,Rw=0,Rwo=0,x1=1,x3=2];1:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=1,r=1,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=0,rfz=0,ks=1,M1=0,KRb=0,KRa=1,KRo=1,Rw=0,Rwo=0,x1=2,x3=1]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=0 KRb=0 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=0 KRb=0 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 3, 4], [1, 2, 3, 4]], "vals": [[4, 5, 6, 8], [4, 5, 6, 8]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_btsh_M1orKRb.md   # second implementation
```

