"""Independent brute-force replay: P1 (every Pareto-maximal partial EFX0 allocation, most goods for its value vector,
is complete) fails on GM4-D, a k = 4 core in which every good has at most 3 valuers. Prints the valuer counts and
every Pareto-maximal value vector with the most goods allocated and one witness (owner per good, 4 = unallocated).
    python3 k4/p3/p1_gm4d.py   (about 2 s)"""
import itertools
sets=[[0,2,4,5],[0,3,4,6],[1,2,5,6],[1,3,5,6]]; vals=[[10,7,2,6],[8,4,1,6],[1,4,8,6],[3,6,10,2]]
n,m=4,7
v=[[0]*m for _ in range(n)]
for i,(S,V) in enumerate(zip(sets,vals)):
    for g,x in zip(S,V): v[i][g]=x
print('valuers per good',[sum(v[i][g]>0 for i in range(n)) for g in range(m)])
def ok(B):
    for i in range(n):
        own=sum(v[i][g] for g in B[i])
        for j in range(n):
            if i==j or not B[j]: continue
            s=sum(v[i][g] for g in B[j]); mn=min(v[i][g] for g in B[j])
            if s-mn>own: return False
    return True
best={}
for a in itertools.product(range(n+1),repeat=m):
    B=[[g for g in range(m) if a[g]==i] for i in range(n)]
    if not ok(B): continue
    u=tuple(sum(v[i][g] for g in B[i]) for i in range(n)); na=sum(x<n for x in a)
    if best.get(u,(-1,))[0]<na: best[u]=(na,a)
U=list(best)
pm=[u for u in U if not any(w!=u and all(x>=y for x,y in zip(w,u)) for w in U)]
for u in pm: print(u, best[u])
