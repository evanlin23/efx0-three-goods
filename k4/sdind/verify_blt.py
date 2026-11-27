"""Independent check of the OC1 core counterexample B< reported by the coordinator (k4/oc1_hall.md §16 on another
branch): picks of the order 0..5, one-absorber completions (numpy brute force, raw EFX0), and every state after one
improving chain or ring (rings from de_free.moves; chains from both de_free and sdilib.chains).

    python3 k4/sdind/verify_blt.py"""
import sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _paths
from sdilib import Inst, sd, completions, picks_base, chains, wanted_by
import de_free as DF
from sdclib import Enc
sets=[[0,2,3,1],[6,4,5,9],[1,2,3,9],[1,6,7,8],[3,6,9],[1,3,6,9]]
vals=[[6,14,16,12],[4,18,12,28],[28,4,16,21],[16,14,12,6],[28,8,24],[20,30,8,4]]
m=10; I=Inst(sets,vals,m)
Y,J=sd(I,range(6)); print('picks',Y,'junk',J,'wanted by',wanted_by(I,Y),flush=True)
pb=picks_base(I,Y)
_,A1=completions(I,pb,1); _,Af=completions(I,pb,None)
print('one-absorber completions',len(A1),'free completions',len(Af),flush=True)
E=Enc(sets,vals,m)
base=[-1]*m
for i,g in enumerate(Y):
    if g is not None: base[g]=i
DF.CHAIN_ONLY=False; states=DF.moves(E,tuple(base))
DF.CHAIN_ONLY=True; chainstates=set(DF.moves(E,tuple(base)))
mine=set()
for nb,p,H in chains(I,pb):
    b=[-1]*m
    for i,bb in enumerate(nb):
        for g in bb: b[g]=i
    mine.add(tuple(b))
print('states: chains+rings',len(states),'chains (de_free)',len(chainstates),'chains (sdilib)',len(mine),'agree',mine==chainstates,flush=True)
ok=0; t0=time.time()
for k,st in enumerate(states):
    bases=[[g for g in range(m) if st[g]==i] for i in range(6)]
    _,A=completions(I,bases,1)
    if len(A): ok+=1; print('REPAIRING STATE',bases,flush=True)
print('states with a one-absorber completion:',ok,'of',len(states),'time %.0f s'%(time.time()-t0),flush=True)
