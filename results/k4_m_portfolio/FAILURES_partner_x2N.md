# Failures of `partner:x2N`

Lemma M portfolio (`k4/lemmam_portfolio.c`, workstream compute/k4-m-portfolio). EVIDENCE: found by the first implementation (classes K0, K1 of `k4/rulef.c`, included unchanged; `-Y1`), confirmed below by the second (`k4/lemmam_xcheck.py`, PR #33's independent model `k4/c4_verify_H/lb4r.py` with Lemma K of `k4/rulef_model.py`, M1 and Lemma KR written from the text of `k4/rulef.md`).

## Where it fails

| dataset | (profile, first agent) pairs: a partner exists, none in K0 ∪ K1 | pairs with a not in K0 ∪ K1 |
|---|---|---|
| `H` | 15 | 22 |
| `suite` | 9 | 21 |

## Smallest failure (dataset `H`, n = 13, m = 33)

```
XFAIL var=x2N a=9 partners=1 w=1 n=13 m=33 sets=[[0,3,4,5],[6,9,12,0],[7,10,13,0],[8,11,14,0],[6,7,8,1],[15,18,21,1],[16,19,22,1],[17,20,23,1],[15,16,17,2],[24,27,30,2],[25,28,31,2],[26,29,32,2],[24,25,26,3]] vals=[[8,6,5,4],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3],[8,6,4,3]] fa=0:K0=0,K1=0,bt=0,sh=0,c40=0,g2=0,N[om=16,r=12,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=eee,x3=1110],E[om=16,r=12,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=eee,x3=1110];1:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=7,r=11,rfz=0,ks=11,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=13,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=0,x1=1222,x3=444];2:K0=1,K1=0,bt=0,sh=0,c40=0,g2=0,N[om=7,r=11,rfz=0,ks=11,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=12,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=0,x1=1220,x3=440];3:K0=1,K1=0,bt=0,sh=0,c40=0,g2=0,N[om=7,r=11,rfz=0,ks=11,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=12,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=0,x1=1220,x3=440];4:K0=1,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=7,r=11,rfz=0,ks=11,M1=1,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=0,x3=0],E[om=12,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=0,x1=1220,x3=440];5:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=10,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=e,x3=10],E[om=14,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=122e,x3=450];6:K0=0,K1=1,bt=0,sh=0,c40=0,g2=0,N[om=10,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=0,x1=e,x3=10],E[om=13,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=120e,x3=410];7:K0=0,K1=1,bt=0,sh=0,c40=0,g2=0,N[om=10,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=0,x1=e,x3=10],E[om=13,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=120e,x3=410];8:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=10,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=1,Rw=0,Rwo=0,x1=e,x3=10],E[om=13,r=11,rfz=0,ks=11,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=120e,x3=410];9:K0=0,K1=0,bt=0,sh=1,c40=0,g2=0,N[om=13,r=11,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=ee,x3=110],E[om=15,r=11,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=12ee,x3=510];10:K0=0,K1=1,bt=0,sh=0,c40=0,g2=0,N[om=13,r=11,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=ee,x3=110],E[om=14,r=11,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=ee,x3=110];11:K0=0,K1=1,bt=0,sh=0,c40=0,g2=0,N[om=13,r=10,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=ee,x3=110],E[om=14,r=10,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=10ee,x3=310];12:K0=0,K1=1,bt=0,sh=1,c40=0,g2=0,N[om=13,r=11,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=ee,x3=110],E[om=14,r=11,rfz=0,ks=0,M1=0,KRb=0,KRa=0,KRo=0,Rw=0,Rwo=0,x1=ee,x3=110]
```

Second implementation: **CONFIRMED**. Per first agent (some policy): agent 0: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 1: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=0 big-top=0; agent 2: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=0 big-top=0; agent 3: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=0 big-top=0; agent 4: K0=1 K1=0 M1=1 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=0 big-top=0; agent 5: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 6: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=0 big-top=0; agent 7: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=0 big-top=0; agent 8: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=1 Rw=0 Rwo=0 big-top=0; agent 9: K0=0 K1=0 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 10: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 11: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; agent 12: K0=0 K1=1 M1=0 KRb=0 KRa=0 KRo=0 Rw=0 Rwo=0 big-top=0; first agent 9 not in K0 ∪ K1, partners [0] not in K0 ∪ K1 either.

## Reproduce

```
echo '{"sets": [[0, 3, 4, 5], [6, 9, 12, 0], [7, 10, 13, 0], [8, 11, 14, 0], [6, 7, 8, 1], [15, 18, 21, 1], [16, 19, 22, 1], [17, 20, 23, 1], [15, 16, 17, 2], [24, 27, 30, 2], [25, 28, 31, 2], [26, 29, 32, 2], [24, 25, 26, 3]], "vals": [[8, 6, 5, 4], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3], [8, 6, 4, 3]]}' > /tmp/p.jsonl
python3 k4/lemmam_portfolio.py --profiles=/tmp/p.jsonl -Y1 --jobs=1     # first implementation
python3 k4/lemmam_xcheck.py --fails=results/k4_m_portfolio/FAILURES_partner_x2N.md   # second implementation
```

