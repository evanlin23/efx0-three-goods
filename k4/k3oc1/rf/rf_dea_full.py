"""Does receiver-first restore (DE-a)?  Exact form: at every RF start of girth's build (DEMOTE-0 and (1, 3) at n = 5)
that has no one-absorber completion at its picks, enumerate every official improving chain (k4/sdc.md §29 rule, as in
attempts/k4_k3oc1_rf_dea.py) and test the one-absorber completion after it by brute force; classify the start by
whether some repairing chain satisfies (DE-a) (every agent that takes a junk good held its top good before the
chain).  Raw EFX0, own code.
    python3 k4/k3oc1/rf/rf_dea_full.py RESIDUE.jsonl.gz SHARD NSHARDS"""
import sys, gzip, json, itertools, collections

def analyse(SETS, VALS, Y2):
    n = len(SETS); m = 1 + max(max(s) for s in SETS)
    v = [dict(zip(s, x)) for s, x in zip(SETS, VALS)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    top = [max(s, key=lambda g: v[i][g]) for i, s in enumerate(SETS)]
    def efx0(X):
        for i in range(n):
            own = val(i, X[i])
            for j in range(n):
                if i == j or len(X[j]) < 2: continue
                vs = [v[i].get(g, 0) for g in X[j]]
                if sum(vs) - min(vs) > own: return False
        return True
    def completes(base):
        B = [[g for g in range(m) if base[g] == a] for a in range(n)]
        J = [g for g in range(m) if base[g] < 0]
        for asg in itertools.product(range(n), repeat=len(J)):
            if sum(1 for a in range(n) if asg.count(a) >= 2) > 1: continue
            if efx0([B[a] + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]): return True
        return False
    base = tuple(next((a for a in range(n) if Y2[a] == g), -1) for g in range(m))
    if completes(base): return 'completes at the picks'
    B = [[g for g in range(m) if base[g] == a] for a in range(n)]; J = [g for g in range(m) if base[g] < 0]
    subsets = lambda xs: [S for r in range(len(xs) + 1) for S in itertools.combinations(xs, r)]
    rep_dea = rep_other = 0
    for t in range(n):
        for path in itertools.permutations(range(n), t + 1):
            x0, xt = path[0], path[-1]
            if any(not B[a] for a in path[:-1]): continue
            for Hs in itertools.product(*[subsets([g for g in J if g in v[a]]) for a in path]):
                if len(set(g for H in Hs for g in H)) != sum(len(H) for H in Hs): continue
                for Hx in (subsets([g for g in B[xt] if g in v[x0]]) if t > 0 else [()]):
                    new0 = (B[x0] if t == 0 else []) + list(Hs[0]) + list(Hx)
                    if not Hs[0] and not Hx: continue
                    if val(x0, new0) <= val(x0, B[x0]): continue
                    nb = list(base)
                    if t > 0:
                        for g in B[xt]: nb[g] = -1
                    ok = True
                    for s in range(1, t + 1):
                        new = B[path[s - 1]] + list(Hs[s])
                        if val(path[s], new) <= val(path[s], B[path[s]]): ok = False; break
                        for g in new: nb[g] = path[s]
                    if not ok: continue
                    for g in new0: nb[g] = x0
                    if completes(tuple(nb)):
                        if all(B[a] == [top[a]] for a, H in zip(path, Hs) if H): rep_dea += 1
                        else: rep_other += 1
    if rep_dea: return 'needs a move; some repairing chain satisfies (DE-a)'
    if rep_other: return 'needs a move; every repairing chain violates (DE-a)'
    return 'needs a move; NO repairing chain'

if __name__ == '__main__':
    shard, nsh = int(sys.argv[2]), int(sys.argv[3])
    C = collections.Counter(); ex = {}
    for k, line in enumerate(gzip.open(sys.argv[1], 'rt')):
        if k % nsh != shard: continue
        r = json.loads(line)
        res = analyse(r['sets'], r['vals'], r['Y2'])
        C[r['cls'] + ': ' + res] += 1
        if 'violates' in res or 'NO' in res: print('EX', r['cls'], res, json.dumps(r), flush=True)
    for k in sorted(C): print(C[k], k)
