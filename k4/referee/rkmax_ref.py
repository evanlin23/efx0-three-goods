#!/usr/bin/env python3
"""Referee check of Conjecture RKMAX at n = 4 (k4/sdc.md §31 end, claude/kind-lamport-y8fdme at c1b2756b). Own code:
SD, nu, raw EFX0, official moves (additions, chains with nonempty passed bases, rings: the coordinator's OC1 move set)
and one-absorber completions come from k4/referee/cert_ref.py; nothing from k4/sdc/ is run or imported. The certifier's
complete n = 4 failure export (two_move_starts_n4.json.gz, compute/k4-oc1max-cert) is read as data.

Per profile (sets, vals) of the export: all 24 orders, SD vectors, nu, the maximum-matching (MM) vectors; rank_i(Y) =
1 + #{g in R_i : v_i(g) > v_i(Y_i)} (5 if pickless), sigma(Y) = (#rank 1, ..., #rank 4).
  sigma : OC1 at every sigma-maximal MM vector; also leximin on ranks (LMR), min rank sum (RS), max #rank-1 (TOP).
  all   : OC1 at every distinct MM vector; the failing vectors must equal the export's picks for that profile; then
          the optimum claims for sigma, LMR, RS and TOP (every optimum OC1 / some optimum OC1) are read off, and at
          every failing start Y some MM vector has sigma > sigma(Y). Also the RF/sigma claims (rm_path_check): at every
          failing (Y, u), some u-first MM order raises sigma; per listed order o, whether SD(u, o - u) raises sigma.

    python3 rkmax_ref.py sigma|all EXPORT [JOBS] [STRIDE OFFSET]
"""
import sys, gzip, json, itertools
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import sd, nu, complete, moves, mk, rel

def oc1(v, Y, rings=True):
    B = [({y} if y is not None else set()) for y in Y]
    if complete(v, B):
        return 0
    for b in moves(v, B, rings=rings):
        if complete(v, b):
            return 1
    return None

def ranks(v, Y):
    out = []
    for i, y in enumerate(Y):
        if y is None:
            out.append(5)
        else:
            out.append(1 + sum(1 for g in rel(v, i) if v[i][g] > v[i][y]))
    return out

def sigma(rk):
    return tuple(sum(1 for r in rk if r == k) for k in (1, 2, 3, 4))

def profile_job(task):
    mode, sets, vals, fails = task
    v = mk(sets, vals); n = len(v); c = Counter()
    nuv = nu(v)
    vecs = {}
    for o in itertools.permutations(range(n)):
        Y = tuple(sd(v, list(o)))
        if sum(1 for y in Y if y is not None) == nuv:
            vecs.setdefault(Y, []).append(o)
    c['profiles'] += 1; c['MM vectors'] += len(vecs)
    rk = {Y: ranks(v, Y) for Y in vecs}
    pots = {'sigma': lambda Y: sigma(rk[Y]),
            'LMR': lambda Y: tuple(-r for r in sorted(rk[Y], reverse=True)),
            'RS': lambda Y: -sum(rk[Y]),
            'TOP': lambda Y: sum(1 for r in rk[Y] if r == 1)}
    status = {}
    def st(Y):
        if Y not in status:
            status[Y] = oc1(v, Y)
        return status[Y]
    if mode == 'all':
        for Y in vecs:
            st(Y)
        myfail = sorted(Y for Y in vecs if status[Y] is None)
        c['MM vectors failing OC1 (mine)'] += len(myfail)
        c['failing set == export picks' if myfail == sorted(tuple(f) for f in fails) else 'FAILING SET DIFFERS'] += 1
        best = max(sigma(rk[Y]) for Y in vecs)
        for Y in myfail:
            c['failing Y has a sigma-larger MM vector' if sigma(rk[Y]) < best else 'FAILING Y IS SIGMA-MAXIMAL'] += 1
    for name, f in pots.items():
        b = max(f(Y) for Y in vecs)
        opt = [Y for Y in vecs if f(Y) == b]
        c['%s: optima' % name] += len(opt)
        if mode == 'sigma' and name != 'sigma':
            continue
        good = [Y for Y in opt if st(Y) is not None]
        c['%s: every optimum OC1' % name] += (len(good) == len(opt))
        c['%s: some optimum OC1' % name] += (len(good) > 0)
        if name == 'sigma':
            c['sigma: optima needing one move'] += sum(1 for Y in opt if st(Y) == 1)
            c['sigma: optima completing at the picks'] += sum(1 for Y in opt if st(Y) == 0)
    return c

def rf_job(task):
    sets, starts = task
    c = Counter()
    for s in starts:
        v = mk(sets, s['vals']); n = len(v); nuv = nu(v); Y = list(s['picks'])
        recv = [a for a in range(n) if Y[a] is not None and not any(
            i != a and v[i][Y[a]] > (v[i][Y[i]] if Y[i] is not None else 0) for i in range(n))]
        sY = sigma(ranks(v, Y))
        c['failing starts'] += 1; c['receivers %d' % len(recv)] += 1
        for u in recv:
            c['failing pairs (Y, u)'] += 1
            ok = False
            for rest in itertools.permutations([a for a in range(n) if a != u]):
                Z = sd(v, [u] + list(rest))
                if sum(1 for z in Z if z is not None) == nuv and sigma(ranks(v, Z)) > sY:
                    ok = True
            c['  some u-first MM order raises sigma' if ok else '  NO u-first MM order raises sigma'] += 1
            anyo = False
            for o in s['orders']:
                Z = sd(v, [u] + [a for a in o if a != u])
                mm = sum(1 for z in Z if z is not None) == nuv
                up = mm and sigma(ranks(v, Z)) > sY
                anyo |= up
                c['  rotations (u, o - u) of listed orders'] += 1
                c['    rotation MM and raises sigma' if up else ('    rotation MM, sigma not raised' if mm else '    rotation not MM')] += 1
            c['  some listed rotation raises sigma'] += anyo
    return c

def main():
    mode, path = sys.argv[1], sys.argv[2]
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    stride, off = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (1, 0)
    print('$ python3 rkmax_ref.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(path))
    prof = {}
    rf_tasks = []
    for h in d['hypergraphs']:
        for i in range(0, len(h['starts']), 500):
            rf_tasks.append((h['sets'], h['starts'][i:i + 500]))
        for s in h['starts']:
            k = json.dumps([h['sets'], s['vals']])
            prof.setdefault(k, (h['sets'], s['vals'], []))[2].append(s['picks'])
    keys = sorted(prof)[off::stride]
    tasks = [(mode,) + prof[k] for k in keys]
    print('profiles in export %d, this run %d' % (len(prof), len(tasks)), flush=True)
    C = Counter()
    with Pool(jobs) as pool:
        for t, c in enumerate(pool.imap_unordered(profile_job, tasks, chunksize=50)):
            C.update(c)
            if (t + 1) % 10000 == 0:
                print('  ... %d profiles' % (t + 1), flush=True)
        if mode == 'all' and stride == 1:
            for c in pool.imap_unordered(rf_job, rf_tasks):
                C.update(c)
    for k in sorted(C):
        print('  %-50s %d' % (k, C[k]))

if __name__ == '__main__':
    main()
