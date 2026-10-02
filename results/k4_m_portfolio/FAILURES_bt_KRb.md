# Failures of `bt:KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `hunt1_failprofiles` | 2 | 2 |
| `n2` | 52,560 | 57,456 |
| `n3` | 114,016,892 | 125,469,216 |
| `n4_1_all` | 1,192,116 | 1,207,872 |
| `n4_2_all` | 215,111,380 | 221,481,216 |
| `n4_3_7cores` | 310,943,876 | 332,107,776 |
| `n4_s2000` | 686,947 | 746,407 |
| `n4_s50` | 17,092 | 18,510 |
| `n5_s20` | 257,564 | 279,622 |
| `n5_s200` | 2,580,465 | 2,800,996 |
| `suite` | 61 | 96 |

## Smallest failure (dataset `n2`, n = 2, m = 4)

```
PFAIL cand=bt:KRb w=2 n=2 m=4 sets=[[0,1,2,3],[1,2,3]] vals=[[2,3,4,8],[2,3,4]] fa=0:K0=1,K1=0,bt=1,sh=1,c40=1,g2=0,N[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=0,K1=1,bt=0,sh=1,c40=1,g2=0,N[om=1,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=0,x3=0],E[om=1,r=0,rfz=0,ks=1,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=1; agent 1: K0=0 K1=1 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 2, 3], [1, 2, 3]], "vals": [[2, 3, 4, 8], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_bt_KRb.md   # second implementation
```

