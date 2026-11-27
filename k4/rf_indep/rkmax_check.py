"""Independent check of Conjecture RKMAX (k4/sdc.md section 31 end on claude/kind-lamport-y8fdme, ledger K4.SDC.RKMAX)
on the certifier's complete n = 5 failure lists (5_pure #38, #419, #447: two_move_starts_n5_sel2.json.gz).
Workstream compute/k4-rf-indep; written from the statement, without reading k4/sdc/extremal_rank_check.py,
extremal_rank_n5.py or oc1_mc2_rand.

Ranks: at a pick vector Y, rank_i(Y) = 1 + #{g in R_i : v_i(g) > v_i(Y_i)}; an agent with no pick has rank 5.
Signature sigma(Y) = (#rank 1, #rank 2, #rank 3, #rank 4).  RKMAX: every maximum-matching SD pick vector whose sigma is
lexicographically maximal among the profile's maximum-matching SD pick vectors (over all n! orders) satisfies OC1.

For every profile of the lists: SD picks of all n! orders (own SD of rf_check.py), keep the maximum matchings (own nu),
take the sigma-maximal ones, and test OC1 at each distinct one with rf_oc1.c; every witness is re-checked by
rf_check.verify_shard (k4/d1/d1lib.py raw EFX0), every F answer by the pure-Python search rf_check.py_oc1.

    python3 k4/rf_indep/rkmax_check.py --data DIR [--groups sel2] [--procs 4]
"""
import sys, os, gzip, json, itertools, collections, time, argparse, tempfile, subprocess
import gc as gc_mod
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rf_check as R

FILES = {'sel2': 'two_move_starts_n5_sel2.json.gz', 'partial6': 'two_move_starts_n5_partial6.json.gz'}
G = {}


def init_worker(hyps):
    G['hyps'] = hyps
    G['perms'] = {n: list(itertools.permutations(range(n))) for n in set(h['n'] for h in hyps.values())}


def sigma(sets, vals, Y):
    s = [0, 0, 0, 0]
    for i, (gs, vv) in enumerate(zip(sets, vals)):
        if Y[i] is None: continue                    # rank 5: not counted
        v = dict(zip(gs, vv)); p = v[Y[i]]
        r = 1 + sum(1 for g in gs if v[g] > p)
        s[r - 1] += 1
    return tuple(s)


def work(job):
    hid, profs = job
    h = G['hyps'][hid]; sets, n, nu = h['sets'], h['n'], h['nu']
    perms = G['perms'][n]
    C = collections.Counter(); keys = []
    for pk, Ys in profs:                             # Ys: the export's failing pick vectors of this profile
        vals = R.unprof(pk, h)
        if any(len(set(vv)) != len(vv) for vv in vals): C['profiles with a tie between single goods'] += 1
        pref = R.prefs(sets, vals)
        vecs = set(R.sd(pref, o) for o in perms)
        mm = [Y for Y in vecs if sum(1 for y in Y if y is not None) == nu]
        C['profiles'] += 1
        C['distinct SD vectors'] += len(vecs); C['distinct maximum-matching SD vectors'] += len(mm)
        if not mm: C['PROFILES WITHOUT A MAXIMUM-MATCHING SD VECTOR'] += 1; continue
        sig = {Y: sigma(sets, vals, Y) for Y in mm}
        best = max(sig.values())
        top = [Y for Y in mm if sig[Y] == best]
        C['sigma-maximal vectors'] += len(top)
        C['profiles with %d sigma-maximal vector(s)' % len(top)] += 1
        C['max signature %s' % (best,)] += 1
        for Y in Ys:
            C['export failing starts'] += 1
            C['export failing starts that are sigma-maximal'] += sig.get(Y) == best
            C['export failing starts with a maximum-matching SD vector of larger sigma'] += Y in sig and sig[Y] < best
        for Y in top: keys.append(pk + R.ybytes(Y))
    return hid, C, keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', required=True); ap.add_argument('--groups', default='sel2')
    ap.add_argument('--procs', type=int, default=os.cpu_count() or 4); ap.add_argument('--bin', default=None)
    args = ap.parse_args(); t0 = time.time()
    print('$ python3 k4/rf_indep/rkmax_check.py --data DIR --groups %s --procs %d' % (args.groups, args.procs))
    binpath = args.bin or os.path.join(tempfile.gettempdir(), 'rf_oc1_bin')
    subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    hyps = {}; meta = {}; jobs = []
    for group in args.groups.split(','):
        fn = os.path.join(args.data, FILES[group]); print('input %-8s %s sha256 %s' % (group, FILES[group], R.sha(fn)))
        d = json.load(gzip.open(fn))
        for h in d['hypergraphs']:
            hid = len(hyps); sets = h['sets']; m = 1 + max(max(s) for s in sets)
            hyps[hid] = dict(sets=sets, n=len(sets), m=m, nu=R.nu_kuhn(sets), nu_brute=R.nu_brute(sets), nu_export=h['nu'])
            meta[hid] = dict(name='%s#%d' % (h['list'], h['idx']), complete=h['complete'], group=group)
            profs = collections.defaultdict(list)
            for st in h['starts']: profs[R.prof_key(st['vals'])].append(tuple(st['picks']))
            items = list(profs.items())
            for i in range(0, len(items), 3000): jobs.append((hid, items[i:i + 3000]))
        del d
    for hid, h in hyps.items():
        print('%-12s m %2d nu %d (brute %d, export %d) complete=%s' % (meta[hid]['name'], h['m'], h['nu'], h['nu_brute'],
                                                                     h['nu_export'], meta[hid]['complete']))
    perh = collections.defaultdict(collections.Counter); tops = collections.defaultdict(list)
    gc_mod.collect(); gc_mod.freeze()
    with Pool(args.procs, initializer=init_worker, initargs=(hyps,)) as pool:
        for hid, C, keys in pool.imap(work, jobs):
            perh[hid].update(C); tops[hid].extend(keys)
    gc_mod.unfreeze()
    print('orders and signatures done %.0f s' % (time.time() - t0), flush=True)

    def gen():
        for hid, keys in tops.items():
            h = hyps[hid]; n = h['n']
            for j, key in enumerate(keys):
                B = [[y] if y != 255 else [] for y in key[-n:]]
                yield R.task_line('rk:%d:%d' % (hid, j), h['sets'], R.unprof(key[:-n], h), h['m'], B)
    shards, ntasks = R.run_shards(gen(), args.procs, binpath, 'rk')
    print('OC1 search on %d sigma-maximal vectors done %.0f s' % (ntasks, time.time() - t0), flush=True)
    ver = collections.defaultdict(collections.Counter); fails = []
    gc_mod.collect(); gc_mod.freeze()
    with Pool(args.procs) as pool:
        for out, F in pool.imap(R.verify_shard, shards):
            for (gcl, hid), C in out.items(): ver[hid].update(C)
            fails += F
        second = collections.Counter(pool.map(R.py_from_line, fails)) if fails else collections.Counter()
    gc_mod.unfreeze()
    print('witnesses verified %.0f s' % (time.time() - t0), flush=True)

    print()
    T = collections.Counter()
    for hid in sorted(perh):
        print('--', meta[hid]['name'], '(%s, complete=%s)' % (meta[hid]['group'], meta[hid]['complete']))
        C = perh[hid] + collections.Counter({'OC1 at sigma-maximal vectors: ' + k: v for k, v in ver[hid].items()})
        for k in sorted(C): print('   %-80s %d' % (k, C[k]))
        T.update(C)
    print('-- total')
    for k in sorted(T): print('   %-80s %d' % (k, T[k]))
    print()
    print('second implementation on F answers:', dict(second) if second else 'no F answers')
    bad = sum(v for k, v in T.items() if 'INVALID' in k)
    failprof = set()
    for l in fails:
        _, hid, j = l.split(None, 1)[0].split(':'); hid, j = int(hid), int(j)
        failprof.add((hid, tops[hid][j][:-hyps[hid]['n']]))
    print('profiles with an OC1-failing sigma-maximal vector: %d' % len(failprof))
    print('RESULT RKMAX: %d profiles, %d sigma-maximal maximum-matching vectors, OC1 F answers %d, invalid witnesses %d'
          % (T['profiles'], T['sigma-maximal vectors'], T['OC1 at sigma-maximal vectors: F'], bad))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
