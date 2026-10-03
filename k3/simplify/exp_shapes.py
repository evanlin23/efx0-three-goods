# Moved from a scratch script: simple shapes of Section 4 of proofs/k3_simple.md ("2 goods each", "2 absorbers").
"""Test simple algorithm shapes for EFX0 with 3 relevant goods per agent.
Profiles: each agent ranks 3 distinct goods a>b>c with values 4,3,2 (strictly balanced);
goods nobody ranks are worthless. By Lemma L5, EFX0 then depends only on the rankings."""
import itertools, random, sys
from collections import defaultdict

def vals(rank):
    return [{r[0]:4, r[1]:3, r[2]:2} for r in rank]

def efx0(v, X):
    n=len(v)
    for i in range(n):
        vi=sum(v[i].get(g,0) for g in X[i])
        for j in range(n):
            if i==j or not X[j]: continue
            s=sum(v[i].get(g,0) for g in X[j]); mn=min(v[i].get(g,0) for g in X[j])
            if s-mn > vi: return False
    return True

def turns_take(rank, turns, m):
    """agents take turns in the given sequence; each takes its favourite remaining relevant good."""
    free=set(range(m)); X=[[] for _ in rank]
    for i in turns:
        for g in rank[i]:
            if g in free: X[i].append(g); free.discard(g); break
    return X, sorted(free)

def r1_order(rank, m):
    """serial dictatorship with R1 priority: an agent that lost a good goes first; else smallest index."""
    free=set(range(m)); rem=list(range(len(rank))); order=[]
    while rem:
        cand=[i for i in rem if sum(g in free for g in rank[i])<=2]
        i=cand[0] if cand else rem[0]
        order.append(i); rem.remove(i)
        for g in rank[i]:
            if g in free: free.discard(g); break
    return order

def with_absorber(X, Z, s):
    Y=[list(b) for b in X]; Y[s]+=Z; return Y

# ---------- candidates ----------
def one_each_absorber(rank, m, order):           # your algorithm, verbatim
    X,Z=turns_take(rank, order, m); return efx0(vals(rank), with_absorber(X,Z,order[-1]))

def one_each_best_absorber(rank, m, order):      # same, but the absorber may be ANY agent (best case)
    X,Z=turns_take(rank, order, m); v=vals(rank)
    return any(efx0(v, with_absorber(X,Z,s)) for s in range(len(rank)))

def one_each_two_absorbers_last(rank, m, order): # leftovers split between the last two agents, ANY split (best case)
    X,Z=turns_take(rank, order, m); v=vals(rank)
    if len(rank)<2: return True
    s1,s2=order[-2],order[-1]
    for mask in range(1<<len(Z)):
        Y=[list(b) for b in X]
        for k,g in enumerate(Z): Y[s1 if mask>>k&1 else s2].append(g)
        if efx0(v,Y): return True
    return False

def one_each_two_absorbers_any(rank, m, order):  # ANY two agents, ANY split (best case of the whole shape for this order)
    X,Z=turns_take(rank, order, m); v=vals(rank); n=len(rank)
    for s1,s2 in itertools.combinations(range(n),2):
        for mask in range(1<<len(Z)):
            Y=[list(b) for b in X]
            for k,g in enumerate(Z): Y[s1 if mask>>k&1 else s2].append(g)
            if efx0(v,Y): return True
    return False

def two_rounds(rank, m, order, snake, best):     # two-round draft, then the leftovers to the last picker (or best agent)
    seq=list(order)+(list(reversed(order)) if snake else list(order))
    X,Z=turns_take(rank, seq, m); v=vals(rank)
    if best: return any(efx0(v, with_absorber(X,Z,s)) for s in range(len(rank)))
    return efx0(v, with_absorber(X,Z,seq[-1]))

def top_two(rank, m, order):                     # each agent takes its two favourite remaining goods at once
    free=set(range(m)); X=[[] for _ in rank]
    for i in order:
        for g in rank[i]:
            if g in free and len(X[i])<2: X[i].append(g); free.discard(g)
    return efx0(vals(rank), with_absorber(X,sorted(free),order[-1]))

CANDS = {
 "1 each + absorber (your alg)":            lambda r,m,o: one_each_absorber(r,m,o),
 "1 each + best single absorber":           lambda r,m,o: one_each_best_absorber(r,m,o),
 "1 each + last 2 absorbers, best split":   lambda r,m,o: one_each_two_absorbers_last(r,m,o),
 "1 each + ANY 2 absorbers, best split":    lambda r,m,o: one_each_two_absorbers_any(r,m,o),
 "2 rounds (1..n,1..n) + last absorbs":     lambda r,m,o: two_rounds(r,m,o,False,False),
 "2 rounds snake (1..n,n..1) + last absorbs": lambda r,m,o: two_rounds(r,m,o,True,False),
 "2 rounds snake + best absorber":          lambda r,m,o: two_rounds(r,m,o,True,True),
 "take top 2 at once + last absorbs":       lambda r,m,o: top_two(r,m,o),
}

def profiles(n, m):
    triples=list(itertools.permutations(range(m),3))
    first=[(0,1,2)]          # symmetry: relabel goods so agent 0 ranks 0>1>2
    for rest in itertools.product(triples, repeat=n-1):
        yield first+list(rest)

if __name__=="__main__":
    mode=sys.argv[1]   # index | r1
    sizes=[(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(3,7)]
    smallest={}; tallies=defaultdict(dict)
    for n,m in sizes:
        tot=0; fail=defaultdict(int)
        for rank in profiles(n,m):
            tot+=1
            order=list(range(n)) if mode=="index" else r1_order(rank,m)
            for name,f in CANDS.items():
                if not f(rank,m,order):
                    fail[name]+=1
                    smallest.setdefault(name,(n,m,rank,order))
        for name in CANDS: tallies[name][(n,m)]=(fail[name],tot)
    for name in CANDS:
        row="  ".join(f"n{n}m{m}:{tallies[name][(n,m)][0]}" for n,m in sizes)
        print(f"{name:45s} {row}")
        if name in smallest: print("    smallest failure:", smallest[name])
    print("totals per size:", {f"n{n}m{m}":tallies[next(iter(CANDS))][(n,m)][1] for n,m in sizes})
