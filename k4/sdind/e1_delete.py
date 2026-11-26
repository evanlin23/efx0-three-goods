"""E1: delete one agent u together with its pick Y_u (B-form along the serial-dictatorship order).

Fact used (k4/sd_induct.md §1): for every agent u, the picks of SD(pi) restricted to the other agents are exactly the
picks of SD(pi minus u) on I - u - Y_u, and the junk is the same set of goods.  So every one-absorber completion X of
I in which u receives no junk restricts to a one-absorber completion of I - u - Y_u, and a completion X' of
I - u - Y_u extends with u holding {Y_u} alone iff no bundle of X' threatens u.

For every distinct SD outcome Y and every agent u (classified: 'last' = nobody wants Y_u, so u can be last in an
order giving Y; 'first' = Y_u is u's top, so u can be first; 'both'; 'mid'), compute
  A  = one-absorber EFX0 completions of Y in I,
  A' = one-absorber EFX0 completions of Y minus u in I' = I - u - Y_u,
and for each X' in A' the Hamming distance (junk goods whose holder changes) to the nearest X in A, and whether some X
in A is reached by moving junk goods to u only ('u absorbs', distance counted the same way).
Reported per u-class: starts with A nonempty; with A' empty (the hypothesis gives nothing without a chain); with
EVERY X' at distance 0 / <= 1 / <= 2; with every X' reaching A by moves to u only; with SOME X' at distance 0.

    python3 k4/sdind/e1_delete.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, os, itertools, collections, json, gzip, random, time
import numpy as np
import _paths
from sdilib import Inst, sd, completions, delete, picks_base, wanted_by


def load(src):
    if src == 'special':
        from nof_var import SPECIAL
        return list(SPECIAL)
    if src.startswith('cores:'):
        _, files, N, seed = src.split(':')
        rng = random.Random(int(seed)); cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in files.split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        out = []
        for t in range(int(N)):
            sets = rng.choice(cores)
            out.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
        return out
    if src == 'logs':
        import re, glob
        seen = set(); out = []
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try: sets, vals = json.loads(mt.group(1))
                    except Exception: continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4: continue
                    key = json.dumps((sets, vals))
                    if key in seen: continue
                    seen.add(key); out.append(('log%d' % len(out), sets, vals, 1 + max(max(a) for a in sets)))
        return out
    from sdc_need import instances
    return instances(src)


def outcomes(I):
    seen = {}
    for o in itertools.permutations(range(I.n)):
        Y, J = sd(I, o)
        seen.setdefault(tuple(Y), o)
    return seen


def uclass(I, Y, u, W):
    last = not W[u]
    top = Y[u] is not None and Y[u] == max(I.R[u], key=lambda h: (I.V[u, h], -h)) if I.R[u] else True
    return 'both' if (last and top) else 'last' if last else 'first' if top else 'mid'


def dist_table(A, A2map, u):
    """for each X' (rows of A2map, already in I's agent labels): (nearest Hamming distance, nearest distance using
    moves to u only, or None)"""
    out = []
    for xp in A2map:
        if len(A) == 0:
            out.append((None, None)); continue
        diff = (A != xp[None, :])
        d = diff.sum(axis=1).min()
        uonly = ~(diff & (A != u)).any(axis=1)
        du = diff[uonly].sum(axis=1).min() if uonly.any() else None
        out.append((int(d), None if du is None else int(du)))
    return out


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); ex = collections.defaultdict(list)
    print('$ python3 k4/sdind/e1_delete.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        for Y, o in outcomes(I).items():
            Y = list(Y)
            try:
                J, A = completions(I, picks_base(I, Y), 1)
            except ValueError:
                C['skipped (too big)'] += 1; continue
            if len(A) == 0: continue
            C['starts with a one-absorber completion'] += 1
            W = wanted_by(I, Y)
            for u in range(I.n):
                cl = uclass(I, Y, u, W)
                gone = [Y[u]] if Y[u] is not None else []
                I2, amap, gmap = delete(I, [u], gone)
                inv = {b: a for a, b in amap.items()}
                Y2 = [None] * I2.n
                for a, b in amap.items():
                    Y2[b] = gmap[Y[a]] if Y[a] is not None else None
                J2, A2 = completions(I2, picks_base(I2, Y2), 1)
                assert [gmap[g] for g in J] == J2
                A2map = np.vectorize(lambda b: inv[b])(A2) if len(A2) else A2
                key = cl
                C[key + ': cases'] += 1
                if len(A2) == 0:
                    C[key + ': A\' empty'] += 1; continue
                dt = dist_table(A, A2map, u)
                ds = [d for d, _ in dt]; dus = [du for _, du in dt]
                C[key + ': some X\' at distance 0'] += (min(ds) == 0)
                for k in (0, 1, 2):
                    C[key + ': every X\' at distance <= %d' % k] += (max(ds) <= k)
                C[key + ': every X\' reaches A by moves to u'] += all(du is not None for du in dus)
                C[key + ': fraction of X\' at distance 0 (sum)'] += 0  # placeholder for alignment
                if max(ds) > 2 and len(ex[key]) < 3:
                    ex[key].append((name, json.dumps((sets, vals)), 'picks', Y, 'u', u, 'max dist', max(ds)))
    for k in sorted(C): print(k, C[k])
    for k, v in ex.items():
        for e in v: print('example', k, *e)
    print('time %.0f s' % (time.time() - t0))
