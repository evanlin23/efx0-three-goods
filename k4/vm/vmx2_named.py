"""VMX2 on named hard instances (coordinator's request, k4/vm.md section 7.2): B< and B> (the OC1 counterexample on a
strict connected n = 6 core, k4/oc1_hall.md section 16 on another branch), SPECIAL (T3, Q2, r4253, r3943),
lb4-owner-needs-from-base-n4m8, the 84 OC1 counterexamples of the TTC session (results/k4_ttc/oc1_counterexamples.json
on claude/k4-ttc) plus its n = 5 counterexample and core candidate.  For each instance and each of K relabellings
(agents and goods permuted): DFS over VMX2's choices until the first run that ends EFX0 (up to --cap runs, then
--samples random runs).  Every output is checked against the raw EFX0 definition by an inline checker that shares
no code with vmlib.  EVIDENCE only.
    python3 k4/vm/vmx2_named.py EXTDIR [--relabel=K] [--cap=N] [--samples=N]
EXTDIR holds oc1_counterexamples.json, oc1_counterexample_n5.json, oc1_core_candidate.json (git show from the TTC
branch)."""
import sys, os, json, random, zlib, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import data

B_SETS = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
B_LT = [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]
B_GT = [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 19], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]


def raw_efx0(sets, vals, m, X):
    """independent checker: complete partition, and for all i != j, g in X_j: v_i(X_i) >= v_i(X_j - g)"""
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    if sorted(g for b in X for g in b) != list(range(m)):
        return False
    for i in range(len(X)):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(len(X)):
            if i != j and any(sum(v[i].get(h, 0) for h in X[j] if h != g) > own for g in X[j]):
                return False
    return True


def relabel(sets, vals, m, rng):
    n = len(sets); pa = list(range(n)); rng.shuffle(pa); pg = list(range(m)); rng.shuffle(pg)
    S = [None] * n; W = [None] * n
    for i in range(n):
        S[pa[i]] = [pg[g] for g in sets[i]]; W[pa[i]] = list(vals[i])
    return S, W


def one(args):
    name, sets, vals, m, cap, samples = args
    I = V.Inst(sets, vals, m); t0 = time.time(); k = 0
    for ch, r in V.all_runs(V.vm6x_run, I, limit=cap, mode='choice', phase3=False):
        k += 1
        if not isinstance(r, V.Stuck):
            ok = raw_efx0(sets, vals, m, r[0])
            return name, I.n, I.m, 'found', k, ok, time.time() - t0
    rng = random.Random(zlib.crc32(name.encode()))
    for t in range(samples):
        c = V.Chooser((), rng=rng)
        try:
            X, _ = V.vm6x_run(I, c, mode='choice', phase3=False)
            return name, I.n, I.m, 'found (sampled)', k + t + 1, raw_efx0(sets, vals, m, X), time.time() - t0
        except V.Stuck:
            pass
    return name, I.n, I.m, 'NONE' if k < cap else 'none within cap', k + samples, None, time.time() - t0


if __name__ == '__main__':
    ext = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    K = int(opt.get('relabel', 3)); cap = int(opt.get('cap', 20000)); samples = int(opt.get('samples', 2000))
    print('$ python3 k4/vm/vmx2_named.py EXTDIR', ' '.join(sys.argv[2:]))
    items = [('B<', B_SETS, B_LT, 10), ('B>', B_SETS, B_GT, 10)]
    items += [(nm, s, v, m) for nm, s, v, m in data.special()]
    d = json.load(open(os.path.join(data.ROOT, 'k4/suite/instances/lb4-owner-needs-from-base-n4m8.json')))
    items.append(('lb4-owner-needs-from-base-n4m8', d['sets'], d['vals'], d.get('m') or 1 + max(max(x) for x in d['sets'])))
    for t, x in enumerate(json.load(open(os.path.join(ext, 'oc1_counterexamples.json')))):
        items.append(('ttc84:%d' % t, x['sets'], x['vals'], x['m']))
    for fn in ('oc1_counterexample_n5.json', 'oc1_core_candidate.json'):
        x = json.load(open(os.path.join(ext, fn)))
        x = x[0] if isinstance(x, list) else x
        items.append((fn[:-5], x['sets'], x['vals'], x.get('m') or 1 + max(max(s) for s in x['sets'])))
    allitems = []
    for nm, s, v, m in items:
        allitems.append((nm, s, v, m, cap, samples))
        rng = random.Random(zlib.crc32(nm.encode()))
        for k in range(K):
            S, W = relabel(s, v, m, rng); allitems.append(('%s~%d' % (nm, k), S, W, m, cap, samples))
    res = []
    with mp.Pool(os.cpu_count()) as pool:
        for r in pool.imap_unordered(one, allitems):
            res.append(r)
    res.sort(key=lambda r: r[0])
    bad = [r for r in res if not r[3].startswith('found') or not r[5]]
    for r in res:
        if not r[0].startswith('ttc84') or r in bad:
            print('  %-40s n=%d m=%d %-16s runs %6d raw-EFX0 %s  %.1fs' % r)
    nt = [r for r in res if r[0].startswith('ttc84')]
    print('ttc84 (with relabellings): %d items, found %d, raw-EFX0 confirmed %d' % (len(nt), sum(r[3].startswith('found') for r in nt), sum(bool(r[5]) for r in nt)))
    print('items', len(res), 'without an EFX0 run:', len(bad))
