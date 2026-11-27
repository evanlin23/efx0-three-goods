"""When a fact of RF-A1* is broken by perturbing one agent (a1_perturb.py), Y becomes repairable by one move.  Which
moves?  For each broken instance, every repairing official chain at Y (rf_dea_full's enumeration), described by the
roles (u, w, d, k2, o) of its agents and the junk it takes; tallied by shape, per broken fact.
    python3 k4/k3oc1/rf/a1_repairs.py RESIDUE.jsonl.gz STEP TRIES SEED"""
import sys, gzip, json, itertools, random, collections
from a1_contra import sd
from a1_perturb import shape_and_facts

def repairing_chains(SETS, VALS, Y):
    n = len(SETS); m = 1 + max(max(s) for s in SETS); v = [dict(zip(s, x)) for s, x in zip(SETS, VALS)]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    def efx0(X):
        for i in range(n):
            own = val(i, X[i])
            for j in range(n):
                if i != j and len(X[j]) >= 2:
                    vs = [v[i].get(g, 0) for g in X[j]]
                    if sum(vs) - min(vs) > own: return False
        return True
    def completes(base):
        B = [[g for g in range(m) if base[g] == a] for a in range(n)]; J = [g for g in range(m) if base[g] < 0]
        for asg in itertools.product(range(n), repeat=len(J)):
            if sum(1 for a in range(n) if asg.count(a) >= 2) > 1: continue
            if efx0([B[a] + [g for g, a2 in zip(J, asg) if a2 == a] for a in range(n)]): return True
        return False
    base = tuple(next((a for a in range(n) if Y[a] == g), -1) for g in range(m))
    B = [[g for g in range(m) if base[g] == a] for a in range(n)]; J = [g for g in range(m) if base[g] < 0]
    subsets = lambda xs: [S for r in range(len(xs) + 1) for S in itertools.combinations(xs, r)]
    out = []
    for t in range(n):
        for path in itertools.permutations(range(n), t + 1):
            x0, xt = path[0], path[-1]
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
                    if completes(tuple(nb)): out.append((path, Hs, Hx))
    return out

if __name__ == '__main__':
    path_, STEP, TRIES, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed); C = collections.Counter()
    for k, line in enumerate(gzip.open(path_, 'rt')):
        r = json.loads(line)
        if r['cls'] != 'DEMOTE-0' or len(r['path']) != 3 or k % STEP: continue
        sets, vals, Y = r['sets'], r['vals'], r['Y']; n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
        o = next((o for o in itertools.permutations(range(n)) if sd(sets, v, o) == Y and o[-1] == r['u']
                  and sd(sets, v, (r['u'],) + tuple(a for a in o if a != r['u'])) == r['Y2']), None)
        if o is None: continue
        base = shape_and_facts(sets, vals, o)
        for role in ('d', 'k2', 'u'):
            a = base[role]
            for _ in range(TRIES):
                nv = [list(x) for x in vals]; nv[a] = rng.sample(range(1, 31), len(sets[a]))
                res = shape_and_facts(sets, nv, o)
                if res is None or all(res['facts']): continue
                lab = {res['u']: 'u', res['w']: 'w', res['d']: 'd'}
                if res['k2'] is not None: lab[res['k2']] = 'k2'
                Jy = set(x for x in range(1 + max(max(s) for s in sets)) if x not in res['Y'])
                names = lambda H: tuple(sorted('junk' for _ in H))
                forms = set()
                for pth, Hs, Hx in repairing_chains(sets, nv, res['Y']):
                    forms.add(tuple('%s%s' % (lab.get(x, 'o'), '+%dj' % len(H) if H else '') for x, H in zip(pth, Hs)) + (('+head', ) if Hx else ()))
                C['%s broken: repairing chain forms %s' % (role, sorted(forms))] += 1
    for k, c in sorted(C.items(), key=lambda kv: -kv[1]): print(c, k)
