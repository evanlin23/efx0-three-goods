# Failures of `partner:x1N`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | (profile, first agent) pairs: a partner exists, none in K0 ∪ K1 | pairs with a not in K0 ∪ K1 |
|---|---|---|
| `n4_3_every12` | 2,592 | 10,096 |
| `hunt2_aborted` (hunt) | 1 annealing walks ended in a failure | – |

## Smallest failure (dataset `n4_3_every12`, n = 4, m = 7)

```
XFAIL var=x1N a=1 partners=4 w=2 n=4 m=7 sets=[[0,1,2,3],[0,2,6],[1,4,5,6],[3,4,5,6]] vals=[[2,8,4,3],[2,3,4],[7,3,5,6],[2,3,4,8]] fa=0:K0=1,K1=0,bt=1,sh=1,c40=0,g2=0,N[om=1,r=3,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=4,x3=8],E[om=1,r=3,rfz=0,ks=0,M1=0,KRb=1,KRa=1,KRo=1,Rw=1,Rwo=1,x1=4,x3=8];1:K0=0,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=1,r=3,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=4,x3=1],E[om=1,r=3,rfz=0,ks=1,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=4,x3=1];2:K0=0,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=1,r=3,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=4,x3=1],E[om=1,r=3,rfz=0,ks=2,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=4,x3=1];3:K0=1,K1=0,bt=1,sh=1,c40=0,g2=0,N[om=1,r=1,rfz=0,ks=3,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=1,x1=4,x3=1],E[om=2,r=0,rfz=0,ks=3,M1=0,KRb=0,KRa=1,KRo=1,Rw=1,Rwo=1,x1=c,x3=1]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=1 K1=0 M1=0 KRb=1 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=1; agent 1: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 2: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 3: K0=1 K1=0 M1=0 KRb=0 KRa=1 KRo=1 Rw=1 Rwo=1 big-top=1; first agent 1 not in K0 ∪ K1, partners [2] not in K0 ∪ K1 either.

## Reproduce

```
echo '{"sets": [[0, 1, 2, 3], [0, 2, 6], [1, 4, 5, 6], [3, 4, 5, 6]], "vals": [[2, 8, 4, 3], [2, 3, 4], [7, 3, 5, 6], [2, 3, 4, 8]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_partner_x1N.md   # second implementation
```

