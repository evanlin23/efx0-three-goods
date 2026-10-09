# Does an EFX0 allocation with at most two bundles of >= 2 goods always exist? (attempts/k3s-two-absorbers.md)
# Does an EFX0 allocation with at most 2 bundles of >= 2 goods always exist? (shape only, no algorithm)
import itertools, random, sys, time
from exp_shapes import vals, efx0, profiles
def has_shape(rank, m, k=2):
    v=vals(rank); n=len(rank)
    for big in itertools.combinations(range(n), min(k,n)):
        small=[i for i in range(n) if i not in big]
        # each small agent gets nothing or one good (distinct)
        for pick in itertools.product(range(-1,m), repeat=len(small)):
            used=[g for g in pick if g>=0]
            if len(set(used))<len(used): continue
            rest=[g for g in range(m) if g not in used]
            for asg in itertools.product(range(len(big)), repeat=len(rest)):
                X=[[] for _ in range(n)]
                for i,g in zip(small,pick):
                    if g>=0: X[i]=[g]
                for g,b in zip(rest,asg): X[big[b]].append(g)
                if efx0(v,X): return True
    return False
t=time.time()
for n,m in [(3,4),(3,5),(3,6)]:
    bad=[r for r in profiles(n,m) if not has_shape(r,m)]
    print(f"n={n} m={m}: profiles with no EFX0 allocation of the 2-absorber shape: {len(bad)}", bad[:2], f"{time.time()-t:.0f}s", flush=True)
random.seed(1)
for n,m,reps in [(4,6,300),(4,7,300),(4,8,200),(5,8,60)]:
    bad=0
    for _ in range(reps):
        rank=[tuple(random.sample(range(m),3)) for _ in range(n)]
        if not has_shape(rank,m): bad+=1; ex=rank
    print(f"n={n} m={m} random {reps}: {bad} without the shape", ex if bad else "", f"{time.time()-t:.0f}s", flush=True)
