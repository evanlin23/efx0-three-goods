"""Probe of Observation S2 (k4/d1.md §7.1): add a fourth agent o (unfrozen, wanting nothing, picking last a new good)
to every hard all-HEAD three-agent start recorded by head_hunt.py; report when the start stays hard and all-HEAD (S2
fails) and which completion appears otherwise.  Evidence generator.

    python3 k4/d1/s2_probe.py
"""
import sys, json, random, collections, itertools
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from d1lib import *
from head_hunt import all_head
rng=random.Random(5)
C=collections.Counter(); bases=[]; seen=set()
for rec in [r for fn in ['results/k4_d1/allhead_h1.jsonl.gz','results/k4_d1/allhead_hc1.jsonl'] for r in open_records(fn)]:
    if len(rec['sets'])!=3: continue
    key=json.dumps((rec['sets'],rec['vals']))
    if key in seen: continue
    seen.add(key); bases.append(rec)
print('bases',len(bases))
ex=[]
for rec in bases:
    sets,vals,m=rec['sets'],rec['vals'],rec['m']; od=rec['order']
    I0=Inst(sets,vals,m); S0=Start(I0,tuple(rec['picks']))
    for trial in range(25):
        # new agent o: pick = new good m; values 1-3 goods among J + picks, all below its pick
        cand=list(S0.J)+[y for y in S0.Y if y is not None]
        r=rng.randint(1,3); goods=rng.sample(cand,r)
        top=rng.randint(10,40)
        ov=[top]+rng.sample(range(1,top),len(goods))
        sets2=[list(s) for s in sets]+[[m]+goods]; vals2=[list(v) for v in vals]+[ov]
        I=Inst(sets2,vals2,m+1); Y=sd_picks(I,list(od)+[3]); S=Start(I,Y)
        if Y[:3]!=tuple(rec['picks']) or Y[3]!=m: continue
        if 3 in S.F or len(S.D)!=1: continue
        if any(3 in S.W[j] for j in range(4)): continue   # o wants nothing
        k=S.D[0]
        if not all_head(S,k): C['adding o breaks all-HEAD']+=1; continue
        oa=one_absorber(I,S.B,witness=True)
        if not oa: C['still hard (S2 FAILS)']+=1; print('S2 FAILS', json.dumps((sets2,vals2)), Y, 'MC2' if all(sum(1 for g in sets2[i] if all(g not in sets2[j] for j in range(4) if j!=i))<=1 for i in range(4)) else 'notMC2'); continue
        o,X=oa
        valj = any(g in I.R[3] for g in S.J)
        C[('completes', 'absorber=%s'%('o' if o==3 else ('k' if o==k else 'wanter')), 'o values junk' if valj else 'o no junk', 'o takes junk' if len(X[3])>1 else 'o takes none')]+=1
for kk,c in sorted(C.items(), key=lambda t:-t[1]): print(c,kk)
