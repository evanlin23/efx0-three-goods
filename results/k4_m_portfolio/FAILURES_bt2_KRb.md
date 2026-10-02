# Failures of `bt2:KRb`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | failures (profiles) | applicable |
|---|---|---|
| `n2` | 3,888 | 5,184 |
| `n3` | 18,638,264 | 21,873,024 |
| `n4_2_all` | 19,318,528 | 20,134,656 |
| `n4_3_7cores` | 52,405,916 | 58,392,576 |
| `n4_s2000` | 107,731 | 125,234 |
| `n4_s50` | 2,670 | 3,085 |
| `n5_s20` | 54,254 | 62,154 |
| `n5_s200` | 541,512 | 619,541 |
| `suite` | 31 | 49 |

## Smallest failure (dataset `n2`, n = 2, m = 4)

```
PFAIL cand=bt2:KRb w=4 n=2 m=4 sets=[[0,1,2,3],[0,1,2,3]] vals=[[2,3,8,4],[2,3,4,8]] fa=0:K0=1,K1=0,bt=1,sh=0,c40=1,g2=0,N[om=0,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=1,rfz=0,ks=0,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0];1:K0=1,K1=0,bt=1,sh=0,c40=1,g2=0,N[om=0,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=0,r=0,rfz=0,ks=1,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=1; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=1.

## Reproduce

```
echo '{"sets": [[0, 1, 2, 3], [0, 1, 2, 3]], "vals": [[2, 3, 8, 4], [2, 3, 4, 8]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_bt2_KRb.md   # second implementation
```

