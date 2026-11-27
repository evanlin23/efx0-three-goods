"""Slot use at the SLOT starts (k4/oc1max_multi.md §7): at every start whose first repairing mechanism is an obstructed
canonical chain with owner k (regimes.py's CAN-k), the fewest junk goods given to holders in an S* completion owned by k
after some canonical chain, and which holders take them (the head, an agent unfrozen at the picks, an agent unfrozen
by the chain) and what (the head's old pick Y_z, a junk good of another truly dangerous agent, of another dangerous
agent, other junk).

    python3 k4/oc1max_multi/slot_stats.py FILE.jsonl[.gz] [...]
"""
import json, sys, os, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collect import records
from mmlib import *
from dred import canonical_chains, improving_sets, obstacles
from lemma_b import truly_dangerous
from regimes import mechanism
C=collections.Counter(); ex={}
def witnesses(I,nb,o):
    J=junk(I,nb); hs=holders(I,nb,o)
    for r in range(min(len(J),len(hs))+1):
        for K in itertools.combinations(J,r):
            rest=[g for g in J if g not in K]
            for who in itertools.permutations(hs,r):
                X=[list(b) for b in nb]
                for g,i in zip(K,who): X[i].append(g)
                X[o]+=rest
                if I.efx0(X): yield dict(zip(who,K))
for fn in sys.argv[1:]:
  for r in records(fn):
    I=Inst(r['inst']['sets'],r['inst']['vals'],r['inst']['m'])
    mech,DT=mechanism(I,r)
    if mech!='CAN-k': continue
    Y=tuple(r['picks']); b=base_from_picks(Y); J=junk(I,b); D=r['D']
    best=None
    for k in D:
        for path in canonical_chains(I,b,k):
            z=path[-1]
            for H0 in improving_sets(I,b,k,J+list(b[z]),False):
                nb,ob=obstacles(I,b,path,H0)
                for slots in witnesses(I,nb,k):
                    # describe: number of slot goods; does head take a slot; what
                    desc=[]
                    for u,g in sorted(slots.items()):
                        who='head' if u==z else ('unfrozen-at-picks' if u not in r['F'] else 'unfrozen-by-chain')
                        what='Y_z' if g==b[z][0] else ('junk of D_T' if any(g in I.R[d] for d in DT if d!=k) else ('junk of D' if any(g in I.R[d] for d in D if d!=k) else 'other junk'))
                        desc.append(who+':'+what)
                    key=(len(slots),tuple(sorted(desc)))
                    if best is None or key<best: best=key
                    break
    C[best]+=1
for k in sorted(C,key=lambda k:-C[k])[:25]: print(C[k],k)
A=collections.Counter()
for k,c in C.items():
    A["slots=%d"%k[0]]+=c
    if k[0]==1: A["one slot, head" if k[1][0].startswith("head") else "one slot, other holder"]+=c
    if any(x.startswith("head") for x in k[1]): A["head used"]+=c
print(dict(A), sum(C.values()))
