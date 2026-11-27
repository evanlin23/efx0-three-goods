"""Conjecture RF off the certifier's exports: random strict profiles of every pure n = 5 core (or of a plain core list,
e.g. the n = 6 cores of K).  Workstream compute/k4-rf-offexport; same own code as rf_check.py / rkmax_rand.py (SD, nu,
receivers, OC1 search rf_oc1.c with witnesses re-checked by k4/d1/d1lib.py).

For every profile: the SD picks of all n! orders; OC1 at every distinct maximum-matching SD vector.  A *failing start*
is a maximum-matching SD vector Y where OC1 fails.  At each failing start and each receiver u of Y (an agent with a pick
that no other agent prefers to its own pick):
- (a) RF, every form (K4.SDC.RF as amended): every u-first order that gives a maximum matching satisfies OC1;
- (b) RF-rot-exists (k4/oc1_hall.md 24.15): some order o giving Y has the rotation (u, o - u), or, when that leaves an
  agent pickless, (u, d, o - u - d) with d the RF path's end (the agent that held a pick at Y and has none at the
  rotation's picks), whose picks are a maximum matching satisfying OC1;
- (c) RF-exists: some u-first order gives a maximum matching satisfying OC1.
Also: (a') some receiver meets (a), (c') some receiver meets (c), and RF's existence clause (some u-first maximum
matching).  Every u-first vector and every rotation vector is an SD vector of the profile, so its OC1 answer is already
known.  OC1 holding at a vector used here is witness-checked in Python; any (b) or (c) failure is re-checked by the
pure-Python exhaustive search (rf_check.py_oc1, raw EFX0 by enumeration) at every vector it relies on.

    python3 k4/rf_indep/rf_rand.py --per-core 600 --vmax 20 --seed 1 [--cores FILE --any-n --min4 2] [--dump FILE]
"""
import sys, os, gzip, json, itertools, collections, time, argparse, tempfile, subprocess, random
import gc as gc_mod
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import rf_check as R
import d1lib as L
from rkmax_rand import strict_vals

G = {}


def init_worker(cores, args, binpath):
    G['cores'] = cores; G['args'] = args
    G['perms'] = {n: list(itertools.permutations(range(n))) for n in set(len(c['sets']) for c in cores)}
    G['p'] = subprocess.Popen([binpath, 'line'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)


def oc1_batch(sets, vals, m, vecs):
    lines = [R.task_line('v%d' % j, sets, vals, m, [[y] if y is not None else [] for y in Y]) for j, Y in enumerate(vecs)]
    G['p'].stdin.write('\n'.join(lines) + '\n'); G['p'].stdin.flush()
    out = {}
    for j, Y in enumerate(vecs):
        a = G['p'].stdout.readline().split()
        if a[0] != 'v%d' % j: raise SystemExit('coprocess out of step')
        out[Y] = a[1:]
    return out


def witness_ok(sets, vals, m, Y, a):
    I = L.Inst(sets, vals, m); n = I.n; B = [[y] if y is not None else [] for y in Y]
    if a[0] == 'P':
        return R.check_completion(I, B, int(a[1]), [R.bits(int(x)) for x in a[2:2 + n]])
    t = int(a[1]); seq = [int(x) for x in a[2:3 + t]]; Hs = [R.bits(int(x)) for x in a[3 + t:4 + 2 * t]]
    o = int(a[4 + 2 * t]); X = [R.bits(int(x)) for x in a[5 + 2 * t:5 + 2 * t + n]]
    NB = R.check_chain(I, B, seq, Hs)
    return NB is not None and R.check_completion(I, NB, o, X)


def work(cid):
    c = G['cores'][cid]; a = G['args']
    rnd = random.Random('rf/%d/%d/%d/%d' % (a['vmax'], a['seed'], c['m'], c['idx']))
    C = collections.Counter(); recs = []
    for _ in range(a['per_core']):
        vals = [strict_vals(rnd, a['vmax'], len(s)) for s in c['sets']]
        analyze(c, vals, C, recs)
    return cid, C, recs


def analyze(c, vals, C, recs, only=None):
    """OC1 at every maximum-matching SD vector of the profile; (a)-(c) at each failing start (only those in `only`,
    if given).  Updates the Counter C and appends one row per failing start to recs."""
    sets, m, nu = c['sets'], c['m'], c['nu']; n = len(sets); perms = G['perms'][n]
    if True:
        pref = R.prefs(sets, vals)
        allp = {o: R.sd(pref, o) for o in perms}
        ismm = lambda Y: sum(1 for y in Y if y is not None) == nu
        M = sorted(set(Y for Y in allp.values() if ismm(Y)), key=str)
        C['profiles'] += 1; C['distinct maximum-matching SD vectors'] += len(M)
        ans = oc1_batch(sets, vals, m, M)
        ok = {Y: ans[Y][0] != 'F' for Y in M}
        for Y in M: C['OC1 at maximum-matching vectors: ' + ('F' if not ok[Y] else ans[Y][0] if ans[Y][0] == 'P' else 'C')] += 1
        fails = [Y for Y in M if not ok[Y] and (only is None or Y in only)]
        if not fails: return
        C['profiles with a failing start'] += 1
        checked = set()
        def good(Y):                       # OC1 holds at Y, witness re-checked
            if not ok[Y]: return False
            if Y not in checked:
                if not witness_ok(sets, vals, m, Y, ans[Y]): raise SystemExit('invalid witness %s %s' % (Y, ans[Y]))
                checked.add(Y)
            return True
        for Y in fails:
            C['failing starts'] += 1
            giving = [o for o in perms if allp[o] == Y]
            rec = R.receivers(sets, vals, Y)
            C['failing starts with %d receiver(s)' % len(rec)] += 1
            row = dict(core_m=c['m'], core_idx=c['idx'], sets=sets, vals=vals, picks=list(Y), orders=len(giving),
                       receivers=rec, per_receiver={})
            anyA = anyC = anyB = False
            for u in rec:
                uf = [o for o in perms if o[0] == u]
                ufmm = sorted(set(allp[o] for o in uf if ismm(allp[o])), key=str)
                A = bool(ufmm) and all(good(Yp) for Yp in ufmm)
                Cx = any(good(Yp) for Yp in ufmm)
                # (b): rotations of the orders giving Y
                Bx = False; kinds = collections.Counter()
                for o in giving:
                    rot = (u,) + tuple(x for x in o if x != u); Yp = allp[rot]
                    if ismm(Yp):
                        kinds['rotation maximum'] += 1
                        if good(Yp): Bx = True; kinds['rotation OC1'] += 1
                    else:
                        ds = [i for i in range(n) if Y[i] is not None and Yp[i] is None]
                        kinds['rotation pickless (%d candidate d)' % len(ds)] += 1
                        for d in ds:
                            rot2 = (u, d) + tuple(x for x in o if x not in (u, d)); Y2 = allp[rot2]
                            if ismm(Y2):
                                kinds['d-second maximum'] += 1
                                if good(Y2): Bx = True; kinds['d-second OC1'] += 1
                C['(start, receiver) pairs'] += 1
                C['  some u-first maximum matching (RF existence clause)'] += bool(ufmm)
                C['  (a) every u-first maximum-matching order satisfies OC1'] += A
                C['  (b) RF-rot-exists'] += Bx
                C['  (c) RF-exists'] += Cx
                for k, v in kinds.items(): C['  rotations: ' + k] += v
                row['per_receiver'][u] = dict(a=A, b=Bx, c=Cx, u_first_mm=len(ufmm),
                                              u_first_mm_oc1=sum(1 for Yp in ufmm if ok[Yp]), rotations=dict(kinds))
                anyA |= A; anyB |= Bx; anyC |= Cx
            C["  (a') some receiver meets (a)"] += anyA
            C["  (b') some receiver meets (b)"] += anyB
            C["  (c') some receiver meets (c)"] += anyC
            row['some_receiver'] = dict(a=anyA, b=anyB, c=anyC)
            bad_bc = any(not (r['b'] and r['c']) for r in row['per_receiver'].values()) or not rec
            if bad_bc:
                # re-check every vector this relies on with the pure-Python search
                vec = set([Y])
                for u in rec:
                    vec |= set(allp[o] for o in perms if o[0] == u and ismm(allp[o]))
                row['second_implementation'] = {str(V): R.py_oc1(sets, vals, m, [[y] if y is not None else [] for y in V])
                                                for V in sorted(vec, key=str)}
                row['flag'] = 'b or c fails'
            recs.append(row)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--per-core', type=int, default=600); ap.add_argument('--vmax', type=int, default=20)
    ap.add_argument('--seed', type=int, default=1); ap.add_argument('--procs', type=int, default=os.cpu_count() or 4)
    ap.add_argument('--cores', default=os.path.join(ROOT, 'results', 'k4_certs_5_pure.json.gz'))
    ap.add_argument('--any-n', action='store_true'); ap.add_argument('--min4', type=int, default=0)
    ap.add_argument('--bin', default=None); ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--dump', default=None, help='write every failing start with its (a)-(c) results (JSONL, gzip)')
    args = ap.parse_args(); t0 = time.time()
    print('$ python3 k4/rf_indep/rf_rand.py --per-core %d --vmax %d --seed %d --procs %d --cores %s%s%s'
          % (args.per_core, args.vmax, args.seed, args.procs, os.path.basename(args.cores),
             ' --any-n' if args.any_n else '', ' --min4 %d' % args.min4 if args.min4 else ''))
    binpath = args.bin or os.path.join(tempfile.gettempdir(), 'rf_oc1_bin')
    subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    raw = json.load(gzip.open(args.cores))
    raw = raw['cores'] if isinstance(raw, dict) else [dict(c, idx=i) for i, c in enumerate(raw)]
    if args.min4: raw = [c for c in raw if sum(1 for s in c['sets'] if len(s) == 4) >= args.min4]
    if args.limit: raw = raw[:args.limit]
    cores = [dict(sets=c['sets'], m=c['m'], idx=c['idx'], nu=R.nu_kuhn(c['sets'])) for c in raw]
    if not args.any_n and any(len(c['sets']) != 5 or any(len(s) != 4 for s in c['sets']) for c in cores):
        raise SystemExit('not a pure n = 5 list')
    print('cores %d from %s (sha256 %s); agents %s; nu %s' % (len(cores), os.path.basename(args.cores), R.sha(args.cores),
          dict(collections.Counter(len(c['sets']) for c in cores)), dict(collections.Counter(c['nu'] for c in cores))), flush=True)
    T = collections.Counter(); rows = []
    a = dict(vmax=args.vmax, seed=args.seed, per_core=args.per_core)
    gc_mod.collect(); gc_mod.freeze()
    with Pool(args.procs, initializer=init_worker, initargs=(cores, a, binpath)) as pool:
        for cid, C, recs in pool.imap_unordered(work, range(len(cores)), chunksize=4):
            T.update(C); rows += recs
            for r in recs:
                if r.get('flag'): print('FLAG', json.dumps(r), flush=True)
    gc_mod.unfreeze()
    print('done %.0f s' % (time.time() - t0))
    print()
    for k in sorted(T, key=lambda k: (k.startswith(' '), k)): print('   %-72s %d' % (k, T[k]))
    cores_with = len(set((r['core_m'], r['core_idx']) for r in rows))
    print('cores with a failing start: %d' % cores_with)
    if args.dump:
        with gzip.open(args.dump, 'wt') as f:
            for r in rows: f.write(json.dumps(r) + '\n')
        print('dumped %d failing starts to %s' % (len(rows), os.path.relpath(args.dump, ROOT)))
    flags = [r for r in rows if r.get('flag')]
    P = T['(start, receiver) pairs']
    print('RESULT RF off the exports: %d profiles, %d failing starts, %d (start, receiver) pairs; (a) %d, (b) %d, (c) %d of %d; '
          'starts with a (b) or (c) failure: %d' % (T['profiles'], T['failing starts'], P,
          T['  (a) every u-first maximum-matching order satisfies OC1'], T['  (b) RF-rot-exists'], T['  (c) RF-exists'], P, len(flags)))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
