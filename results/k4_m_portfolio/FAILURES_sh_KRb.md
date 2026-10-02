# Failures of `sh:KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `H` | 20 | 20 |
| `hunt1_failprofiles` | 2 | 2 |
| `n2` | 10,876 | 44,656 |
| `n3` | 90,715,767 | 135,892,280 |
| `n4_1_all` | 4,400,526 | 4,820,688 |
| `n4_2_all` | 387,575,806 | 458,728,992 |
| `n4_3_7cores` | 325,956,496 | 431,039,232 |
| `n4_s2000` | 976,986 | 1,272,852 |
| `n4_s50` | 24,523 | 31,881 |
| `n5_s20` | 381,679 | 475,674 |
| `n5_s200` | 3,821,706 | 4,763,575 |
| `suite` | 86 | 144 |

## Smallest failure (dataset `n2`, n = 2, m = 4)

```
PFAIL cand=sh:KRb w=5 n=2 m=4 sets=[[0,1,2,3],[1,2,3]] vals=[[1,4,6,8],[2,3,4]] fa=0:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=0,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=0,sh=1,c40=1,g2=0,N[om=0,r=1,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=1,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0.

## Reproduce

```
echo '{"sets": [[0, 1, 2, 3], [1, 2, 3]], "vals": [[1, 4, 6, 8], [2, 3, 4]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_sh_KRb.md   # second implementation
```

