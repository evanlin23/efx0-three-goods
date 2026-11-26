"""The shape of the LIFT-EX two-move repairs at the n = 4 failures (k4/matching.md §6; evidence only).
For every start of results/k4_matching/data/oc1max_cex_n4.json and results/k4_matching/n4_failing_walk.jsonl, over
the LIFT pairs (P1 from a dangerous agent to the lone holder z with an H0 that also improves a second dangerous agent;
P2 ending at z and giving z its favourite good; owner P2's head h, Lemma EX* holding): which features some LIFT pair
has -- H0 sizes, whether h is inert at Y (its junk is worth at most its pick), whether h's H0 contains z's good after
P1, the sizes of the other multi-good bundles, and whether h can take all the junk (the allocation is then raw EFX0).

    python3 k4/matching/lift_oblig.py"""
import sys, os, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _mpaths  # noqa: F401
from mlib import M
from lift_shapes import chain_moves
from exchange import ex_value_general
import multiprocessing as mp
def job(row):
    I=M(row['sets'],row['vals']); Y=row['picks']; base=[[g] for g in Y]; D=I.dangerous(base); hold=I.holders(base)
    z=hold[0]; C=collections.Counter(); found=False
    for P1,H01,Hs1,B1 in chain_moves(I,base,D):
        if P1[-1]!=z: continue
        if not any(q!=P1[0] and I.V(q,[g for g in H01 if g in I.R[q]])>I.V(q,base[q]) for q in D): continue
        for P2,H02,Hs2,B2 in chain_moves(I,B1):
            if P2[-1]!=z or not B2[z] or I.V(z,B2[z])<max(I.v[z].values()): continue
            h=P2[0]; d,_,_=ex_value_general(I,B1,P2,B2,h)
            if d>0: continue
            found=True
            X=[list(b) for b in B2]; X[h]=X[h]+I.junk(B2)
            C['owner takes all junk: EFX0 %s'%I.efx0(X)]+=1
            C['max size of other multi-good bundles %d'%max([len(B2[j]) for j in range(I.n) if j!=h]+[0])]+=1
            C['P1 H0 size %d, P2 H0 size %d'%(len(H01),len(H02))]+=1
            C['z frozen at B1 %s'%(z in I.frozen(B1))]+=1
            C['P2 head = P1 head %s'%(h==P1[0])]+=1
            C['P2 head valued no junk at Y (inert) %s'%(not (I.R[h]&set(I.junk(base))) or I.V(h,[g for g in I.junk(base) if g in I.R[h]])<=I.V(h,base[h]))]+=1
            C['P2 H0 contains z base at B1 %s'%(B1[z][0] in H02)]+=1
    return C, found
R=os.path.join(_mpaths.ROOT, 'results', 'k4_matching')
rows=[dict(sets=d['sets'],vals=d['vals'],picks=d['picks']) for d in json.load(open(R+'/data/oc1max_cex_n4.json'))['instances']]
rows+=[json.loads(l) for l in open(R+'/n4_failing_walk.jsonl')]
T=collections.Counter(); S=collections.Counter()
if __name__ == '__main__':
  with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as p:
    for C,f in p.imap_unordered(job,rows,chunksize=8):
        for k in C: S[k]+=1
        T['starts with a LIFT pair %s'%f]+=1
  for k in sorted(T): print(k,T[k])
  print('--- starts where some LIFT pair has the feature:')
  for k in sorted(S): print(k,S[k])
