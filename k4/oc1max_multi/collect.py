"""Collect every one-absorber-hard perfect start with |D| >= 2 (k4/oc1max_multi.md §1).

For every instance of a data set and every order: the serial-dictatorship picks; keep them if they form a maximum
matching; if some agent with a relevant good is pickless, apply Lemma RED (k4/sdc.md §31) to get a perfect start of
the reduced instance (pickless agents become null agents).  Keep the perfect start if its picks have no one-absorber
completion (raw enumeration, mmlib.oa_absorbers) and it has at least two dangerous agents.  For each kept start, every
official move (mmlib.moves) is tried, and the repairing ones are recorded with their absorbers and S* owners.

Output: one JSON line per distinct kept start (instance, order, picks) appended to the file OUT (SLIM=0: with the
start's structure and every repairing move); the summary goes to stdout.

    python3 k4/oc1max_multi/collect.py SRC [args]
SRC: special | screen | suite | logs | cores:FILES N SEED   (the data sets of k4/oc1_hall.md, via k4/sdc's loader)
     n5:LISTS R SEED [STRIDE]                                 (random profiles of the n = 5 core lists, as in
                                                               k4/sdc/oc1max_n5_lists.py)
"""
import sys, os, json, gzip, random, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from mmlib import (Inst, base_from_picks, junk, frozen, wanters, dangerous, oa_absorbers, sstar_owners, moves,
                   is_ed, is_canonical, nu, red, is_perfect)

NMAX = int(os.environ.get('NMAX', '5'))
SLIM = os.environ.get('SLIM', '1') == '1'     # write the starts only (the analyses recompute the repairs)


def load(src, argv):
    if src.startswith('n5:'):
        from oc1max_n5_lists import profile
        lists = src[3:].split(','); R = int(argv[2]); seed = int(argv[3]); stride = int(argv[4]) if len(argv) > 4 else 1
        items = []; t = 0
        for lst in lists:
            d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_5_%s.json.gz' % lst)))
            for c in d['cores'][::stride]:
                rng = random.Random(seed * 1000003 + t); t += 1
                for r in range(R):
                    vals, _ = profile(c['sets'], rng)
                    items.append(('%s#%d.%d' % (lst, c['idx'], r), c['sets'], vals, 1 + max(max(s) for s in c['sets'])))
        return items
    from min_frozen import load as L
    return L(src, argv)


def add_repairs(rec):
    """the start's structure (J, F, D, wanters, junk sets) and every repairing move, with absorbers and S* owners"""
    I2 = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m']); base = base_from_picks(tuple(rec['picks']))
    J = junk(I2, base); F = frozen(I2, base); D = dangerous(I2, base)
    rec.update({'J': J, 'F': F, 'D': D, 'W': {j: wanters(I2, base, j) for j in F},
                'Jd': {d: [g for g in J if g in I2.R[d]] for d in D}, 'repairs': []})
    for nb, ds in moves(I2, base).items():
        oa = oa_absorbers(I2, nb)
        if not oa: continue
        ss = sstar_owners(I2, nb)
        for kind, path, Hs in ds:
            rec['repairs'].append({'kind': kind, 'path': path, 'H': {str(k): list(v) for k, v in Hs.items() if v},
                                   'base': nb, 'oa': sorted(oa), 'ss': sorted(ss),
                                   'ed': is_ed(I2, base, (kind, path, Hs), D),
                                   'canon': is_canonical(I2, base, (kind, path, Hs), D)})
    return rec


def records(fn):
    """read a file of kept starts (.jsonl or .jsonl.gz, full or slim); slim records get their repairs recomputed
    (in parallel)"""
    f = gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)
    recs = [json.loads(line) for line in f]
    todo = [r for r in recs if 'repairs' not in r]
    if todo:
        with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
            done = pool.map(add_repairs, todo, chunksize=8)
        it = iter(done); recs = [r if 'repairs' in r else next(it) for r in recs]
    yield from recs


def study(item):
    name, sets, vals, m = item
    I = Inst(sets, vals, m, name)
    if I.n > NMAX: return name, collections.Counter(), []
    C = collections.Counter(); out = []; seen = set(); N = nu(I)
    for od in itertools.permutations(range(I.n)):
        Y = I.sd(od)
        if Y in seen: continue
        seen.add(Y)
        if sum(y is not None for y in Y) != N: C['non-max'] += 1; continue
        C['max'] += 1
        if is_perfect(I, Y): I2, Y2, keep, S, U = I, Y, list(range(I.n)), [], []
        else: I2, Y2, keep, S, U = red(I, Y); C['max, reduced by RED'] += 1
        base = base_from_picks(Y2)
        if oa_absorbers(I2, base, owners=None):
            C['complete at the picks'] += 1; continue
        D = dangerous(I2, base)
        C['hard, |D| = %d' % len(D)] += 1
        if len(D) < 2: continue
        rec = {'name': name, 'inst': I2.to_json(), 'orig_sets': sets, 'orig_vals': vals, 'order': od,
               'picks': Y2, 'keep': keep, 'S': S, 'U': U}
        add_repairs(rec)
        C['hard, |D| >= 2, repaired' if rec['repairs'] else 'hard, |D| >= 2, NOT REPAIRED'] += 1
        out.append(rec)
    return name, C, out


if __name__ == '__main__':
    src = sys.argv[1]; t0 = time.time()
    items = load(src, sys.argv)
    outf = open(os.environ['OUT'], 'a') if os.environ.get('OUT') else None
    print('$ python3 k4/oc1max_multi/collect.py', *sys.argv[1:], '(NMAX=%d)' % NMAX, 'instances', len(items), flush=True)
    T = collections.Counter(); keyseen = set()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for name, C, out in pool.imap_unordered(study, items, chunksize=4):
            T.update(C)
            for rec in out:
                k = json.dumps((rec['inst']['sets'], rec['inst']['vals'], rec['picks']))
                if k in keyseen: T['duplicate kept starts'] += 1; continue
                keyseen.add(k); T['distinct kept starts'] += 1
                if not rec['repairs']: print('NOT REPAIRED', json.dumps(rec), flush=True)
                if outf:
                    slim = {k: rec[k] for k in ('name', 'inst', 'orig_sets', 'orig_vals', 'order', 'picks', 'keep', 'S', 'U')}
                    slim['src'] = src
                    outf.write(json.dumps(slim if SLIM else rec) + '\n')
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
