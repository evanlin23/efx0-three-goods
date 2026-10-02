# Failures of `bt1:M1`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `hunt1_failprofiles` | 2 | 2 |
| `n2` | 3,600 | 52,272 |
| `n3` | 2,870,352 | 103,596,192 |
| `n4_1_all` | 3,540 | 1,207,872 |
| `n4_2_all` | 2,440,776 | 201,346,560 |
| `n4_3_7cores` | 4,972,104 | 273,715,200 |
| `n4_3_every12` | 17,490,372 | 939,340,800 |
| `n4_s2000` | 13,400 | 621,173 |
| `n4_s50` | 311 | 15,425 |
| `n5_s20` | 3,200 | 217,468 |
| `n5_s200` | 30,765 | 2,181,455 |
| `suite` | 15 | 47 |

## Smallest failure (dataset `n2`, n = 2, m = 5)

```
PFAIL cand=bt1:M1 w=1 n=2 m=5 sets=[[0,2,3,4],[1,2,3,4]] vals=[[2,3,6,10],[2,4,5,8]] fa=0:K0=1,K1=0,bt=1,sh=1,c40=0,g2=0,N[om=1,r=0,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=2,r=1,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=1,x3=2];1:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=2,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=2,x3=1],E[om=2,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=0,Rwo=0,x1=2,x3=1]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=0 KRb=1 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=1; agent 1: K0=1 K1=0 M1=0 KRb=1 KRa=1 KRo=1 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 2, 3, 4], [1, 2, 3, 4]], "vals": [[2, 3, 6, 10], [2, 4, 5, 8]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_bt1_M1.md   # second implementation
```

