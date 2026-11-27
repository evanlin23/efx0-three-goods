"""Independent check of Conjecture RF (k4/sdc.md section 31 end, K4.SDC.RF as amended 2026-11-27 04:22 UTC) on the
certifier's n = 5 failure exports.  Workstream compute/k4-rf-indep; see k4/rf_indep/README.md.

Written from the statements only, without reading any other RF / OC1 / de_free / certifier code.  Own code:
- serial dictatorship (SD): each agent in turn takes its best remaining relevant good, ties by lower good index
  (k4/d1/d1lib.py convention); an agent with no relevant good left gets nothing;
- maximum matching size nu of the agent-good relevance graph (augmenting paths, cross-checked by brute force);
- receivers: agents u with a pick such that no other agent j has v_j(Y_u) > v_j(Y_j);
- OC1 (k4/sdc.md section 29): a one-absorber completion of the picks, or one improving chain after which the bases
  have one.  The search is k4/rf_indep/rf_oc1.c; every positive answer comes with a witness (the chain and the final
  allocation), which this script re-checks with k4/d1/d1lib.py's raw EFX0 test and its own chain test.  A negative
  answer at an RF start would be re-checked by a pure-Python exhaustive search (second implementation).

RF, amended: for every failing start Y and every receiver u of Y, (a) some order with u first gives a maximum matching
and (b) every order with u first that gives a maximum matching satisfies OC1.  Here (b) is checked at the pick vector
Y' of every one of the (n-1)! u-first orders; distinct (profile, Y') pairs are tested once.  For comparison with
k4/oc1_hall.md section 24.10 the script also counts the rotations (u, o - u) of the listed failing orders o.

Optionally (--orig) it runs the same OC1 search at the failing starts Y themselves: it should answer F everywhere.

    python3 k4/rf_indep/rf_check.py --data DIR [--orig all|N] [--procs 4]

DIR holds, from branch compute/k4-oc1max-cert (commit d830b54a or later), results/k4_oc1max/n5/:
two_move_starts_n5_sel2.json.gz, two_move_starts_n5_partial6.json.gz, 5_pure_s5o0_summary.jsonl.gz,
5_pure_s5o1_summary.jsonl.gz.
"""
import sys, os, gzip, json, itertools, collections, hashlib, subprocess, time, argparse, tempfile, random
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'd1'))
import d1lib as L

HALL = {'export_rf_starts': 1530083, 'export_mm': 1526623, 'export_pickless_rot': 3460,
        'export_pickless_uf_mm': 26524, 'stored_mm': 650, 'stored_pickless_rot': 16,
        'export_failing_starts': 1285930, 'export_failing_orders': 7608052, 'stored_starts': 568}


# ---------------------------------------------------------------- matching, SD, receivers
def nu_kuhn(sets):
    match = {}
    def aug(i, seen):
        for g in sets[i]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = i; return True
        return False
    return sum(1 for i in range(len(sets)) if aug(i, set()))


def nu_brute(sets):
    best = 0
    for choice in itertools.product(*[list(s) + [None] for s in sets]):
        gs = [g for g in choice if g is not None]
        if len(gs) == len(set(gs)): best = max(best, len(gs))
    return best


def prefs(sets, vals):
    return [[g for _, g in sorted(((-v, g) for g, v in zip(s, vv)))] for s, vv in zip(sets, vals)]


def sd(pref, order):
    taken = set(); Y = [None] * len(pref)
    for i in order:
        for g in pref[i]:
            if g not in taken: Y[i] = g; taken.add(g); break
    return tuple(Y)


def receivers(sets, vals, Y):
    v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
    n = len(sets); out = []
    for u in range(n):
        if Y[u] is None: continue
        if all(not (v[j].get(Y[u], 0) > (v[j].get(Y[j], 0) if Y[j] is not None else 0)) for j in range(n) if j != u):
            out.append(u)
    return out


# ---------------------------------------------------------------- per-start work (pool)
G = {}


def init_worker(hyps):
    G['hyps'] = hyps
    G['perms'] = {n: list(itertools.permutations(range(n))) for n in set(h['n'] for h in hyps.values())}


def prof_key(vals):
    assert all(0 < x < 256 for vv in vals for x in vv)
    return bytes(x for vv in vals for x in vv)


def work(job):
    hid, starts = job
    h = G['hyps'][hid]; sets, n, nu = h['sets'], h['n'], h['nu']
    perms = G['perms'][n]
    C = collections.Counter(); keys = {}
    for st in starts:
        vals, Y = st['vals'], tuple(st['picks'])
        pref = prefs(sets, vals)
        allp = {o: sd(pref, o) for o in perms}
        listed = [tuple(o) for o in st['orders']] if st.get('orders') is not None else None
        giving = [o for o in perms if allp[o] == Y]
        C['starts'] += 1
        C['orders giving Y (all n! orders)'] += len(giving)
        if listed is not None:
            C['listed orders'] += len(listed)
            C['listed orders whose SD picks are Y'] += sum(1 for o in listed if allp[o] == Y)
            C['starts whose listed orders are exactly the orders giving Y'] += set(listed) == set(giving)
        else:
            listed = giving
        C['starts with |Y| = nu'] += sum(1 for y in Y if y is not None) == nu
        rec = receivers(sets, vals, Y)
        C['receivers per start %d' % len(rec)] += 1
        if st.get('receivers') is not None:
            C['starts whose receivers agree with the export'] += sorted(rec) == sorted(st['receivers'])
        pk = prof_key(vals)
        for u in rec:
            C['(start, receiver) pairs'] += 1
            uf = [o for o in perms if o[0] == u]
            mm = set(o for o in uf if sum(1 for y in allp[o] if y is not None) == nu)
            C['u-first orders'] += len(uf); C['u-first orders giving a maximum matching'] += len(mm)
            C['(start, receiver) pairs with some u-first maximum-matching order (RF a)'] += bool(mm)
            for o in uf:
                keys[(pk, allp[o], 0)] = 1 if o in mm else 0
            for o in listed:
                rot = (u,) + tuple(a for a in o if a != u)
                Yp = allp[rot]
                keys[(pk, Yp, 1)] = 1 if sum(1 for y in Yp if y is not None) == nu else 0
    return hid, C, list(keys.items())


# ---------------------------------------------------------------- C search and witness checks
def task_line(tid, sets, vals, m, B):
    parts = [tid, str(len(sets)), str(m)]
    for s, vv in zip(sets, vals):
        parts.append(str(len(s)))
        for g, v in zip(s, vv): parts += [str(g), str(v)]
    for b in B: parts.append(str(sum(1 << g for g in b)))
    return ' '.join(parts)


def run_c(lines, procs, binpath, tag):
    tmp = tempfile.mkdtemp(prefix='rf_' + tag + '_')
    shards = [lines[i::procs] for i in range(procs)]
    ps = []
    for i, sh in enumerate(shards):
        fi = os.path.join(tmp, 'in%d' % i); fo = os.path.join(tmp, 'out%d' % i)
        with open(fi, 'w') as f: f.write('\n'.join(sh) + ('\n' if sh else ''))
        ps.append((subprocess.Popen([binpath], stdin=open(fi), stdout=open(fo, 'w')), fo))
    out = {}
    for p, fo in ps:
        if p.wait() != 0: raise SystemExit('rf_oc1 failed')
        for line in open(fo):
            a = line.split(); out[a[0]] = a[1:]
    if len(out) != len(lines): raise SystemExit('missing answers: %d of %d' % (len(out), len(lines)))
    return out


def bits(x):
    return [g for g in range(32) if x >> g & 1]


def check_completion(I, B, o, X):
    """X: lists.  A one-absorber completion of bases B with absorber o, raw EFX0?"""
    allg = sorted(g for x in X for g in x)
    if allg != list(range(I.m)): return False
    for i in range(I.n):
        if not set(B[i]) <= set(X[i]): return False
        if i != o and len(set(X[i]) - set(B[i])) > 1: return False
    return L.efx0(I, X)


def check_chain(I, B, seq, Hs):
    """the improving-chain conditions of k4/sdc.md section 29; returns the new bases or None"""
    t = len(seq) - 1
    if t < 1 or len(set(seq)) != len(seq): return None
    held = set(g for b in B for g in b); J = set(range(I.m)) - held
    allH = [g for h in Hs for g in h]
    if len(allH) != len(set(allH)): return None
    if not set(Hs[0]) <= (J | set(B[seq[t]])) & I.R[seq[0]]: return None
    for i in range(1, t + 1):
        if not set(Hs[i]) <= J & I.R[seq[i]]: return None
    if not I.val(seq[0], Hs[0]) > I.val(seq[0], B[seq[0]]): return None
    for i in range(1, t + 1):
        if not I.val(seq[i], list(B[seq[i - 1]]) + list(Hs[i])) > I.val(seq[i], B[seq[i]]): return None
    NB = [list(b) for b in B]
    NB[seq[0]] = sorted(Hs[0])
    for i in range(1, t + 1): NB[seq[i]] = sorted(list(B[seq[i - 1]]) + list(Hs[i]))
    return NB


def verify(job):
    """job: list of (sets, vals, m, B, answer tokens).  Returns Counter."""
    C = collections.Counter()
    for sets, vals, m, B, a in job:
        I = L.Inst(sets, vals, m); n = I.n
        if a[0] == 'P':
            o = int(a[1]); X = [bits(int(x)) for x in a[2:2 + n]]
            C['P verified' if check_completion(I, B, o, X) else 'P WITNESS INVALID'] += 1
        elif a[0] == 'C':
            t = int(a[1]); seq = [int(x) for x in a[2:3 + t]]
            Hs = [bits(int(x)) for x in a[3 + t:4 + 2 * t]]
            o = int(a[4 + 2 * t]); X = [bits(int(x)) for x in a[5 + 2 * t:5 + 2 * t + n]]
            NB = check_chain(I, B, seq, Hs)
            ok = NB is not None and check_completion(I, NB, o, X)
            C[('C verified, t = %d' % t) if ok else 'C WITNESS INVALID'] += 1
        else:
            C['F'] += 1
    return C


def py_oc1(sets, vals, m, B):
    """second implementation (pure Python, exhaustive): OC1 at bases B?"""
    I = L.Inst(sets, vals, m); n = I.n
    if L.one_absorber(I, B, witness=True): return 'P'
    held = set(g for b in B for g in b); J = [g for g in range(m) if g not in held]
    def subsets(xs):
        for r in range(len(xs) + 1):
            for c in itertools.combinations(xs, r): yield list(c)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            c0 = [g for g in sorted(set(J) | set(B[seq[t]])) if g in I.R[seq[0]]]
            for H0 in subsets(c0):
                if not I.val(seq[0], H0) > I.val(seq[0], B[seq[0]]): continue
                def rec(i, used, Hs):
                    if i > t:
                        NB = check_chain(I, B, seq, Hs)
                        return NB is not None and bool(L.one_absorber(I, NB, witness=True))
                    ci = [g for g in J if g in I.R[seq[i]] and g not in used]
                    for Hi in subsets(ci):
                        if I.val(seq[i], list(B[seq[i - 1]]) + Hi) > I.val(seq[i], B[seq[i]]):
                            if rec(i + 1, used | set(Hi), Hs + [Hi]): return True
                    return False
                if rec(1, set(H0), [H0]): return 'C'
    return 'F'


# ---------------------------------------------------------------- main
def sha(fn):
    return hashlib.sha256(open(fn, 'rb').read()).hexdigest()[:16]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', required=True); ap.add_argument('--procs', type=int, default=os.cpu_count() or 4)
    ap.add_argument('--orig', default='0', help="OC1 search at the failing starts Y too: 'all' or a sample size per hypergraph")
    ap.add_argument('--bin', default=None)
    ap.add_argument('--limit', type=int, default=0, help='testing: only the first N starts of each hypergraph')
    ap.add_argument('--orig-py', type=int, default=0, help='re-check N of the --orig F answers per hypergraph in pure Python')
    args = ap.parse_args()
    t0 = time.time()
    print('$ python3 k4/rf_indep/rf_check.py --data DIR --orig %s --procs %d' % (args.orig, args.procs))
    binpath = args.bin or os.path.join(tempfile.gettempdir(), 'rf_oc1_bin')
    subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    files = {'sel2': 'two_move_starts_n5_sel2.json.gz', 'partial6': 'two_move_starts_n5_partial6.json.gz',
             's5o0': '5_pure_s5o0_summary.jsonl.gz', 's5o1': '5_pure_s5o1_summary.jsonl.gz'}
    for k, fn in files.items(): print('input %-8s %s sha256 %s' % (k, fn, sha(os.path.join(args.data, fn))))

    hyps = {}; jobs = []; meta = {}
    def add_hyp(group, lst, idx, sets, m, nu_export, complete, starts):
        key = (lst, idx, json.dumps(sets))
        hid = len(hyps)
        for h2, hh in hyps.items():
            if hh['key'] == key: hid = h2
        if hid == len(hyps):
            nu = nu_kuhn(sets); nb = nu_brute(sets)
            hyps[hid] = dict(key=key, sets=sets, n=len(sets), m=m, nu=nu, nu_brute=nb, nu_export=nu_export)
            meta[hid] = dict(group=set(), complete=complete, list=lst, idx=idx)
        meta[hid]['group'].add(group)
        if args.limit: starts = starts[:args.limit]
        for i in range(0, len(starts), 4000): jobs.append((hid, group, starts[i:i + 4000]))

    for group in ('sel2', 'partial6'):
        d = json.load(gzip.open(os.path.join(args.data, files[group])))
        for h in d['hypergraphs']:
            m = 1 + max(max(s) for s in h['sets'])
            add_hyp(group, h['list'], h['idx'], h['sets'], m, h['nu'], h['complete'], h['starts'])
    for group in ('s5o0', 's5o1'):
        for line in gzip.open(os.path.join(args.data, files[group]), 'rt'):
            r = json.loads(line)
            if not r.get('oc1_fails'): continue
            starts = [dict(vals=f['vals'], picks=f['picks']) for f in r['oc1_fails']]
            add_hyp('stored', r['list'], r['idx'], r['sets'], r['m'], r['nu'], None, starts)

    for hid, h in hyps.items():
        if not (h['nu'] == h['nu_brute'] == h['nu_export']): print('NU MISMATCH', h['key'], h['nu'], h['nu_brute'], h['nu_export'])
    # cross-check the fast SD with d1lib.sd_picks on a sample
    rnd = random.Random(1); bad = 0; tested = 0
    for hid, group, starts in jobs[::7]:
        h = hyps[hid]
        for st in starts[:20]:
            I = L.Inst(h['sets'], st['vals'], h['m']); pref = prefs(h['sets'], st['vals'])
            for o in rnd.sample(list(itertools.permutations(range(h['n']))), 10):
                tested += 1; bad += sd(pref, o) != L.sd_picks(I, o)
    print('fast SD vs d1lib.sd_picks: %d orders compared, %d differ' % (tested, bad))

    # ---- stage A: orders, receivers, u-first pick vectors
    perg = collections.defaultdict(collections.Counter)
    uf = collections.defaultdict(dict)       # (group class, hid) -> {(prof, Y'): mm}
    rot = collections.defaultdict(dict)
    gclass = lambda g: 'stored' if g == 'stored' else 'export'
    with Pool(args.procs, initializer=init_worker, initargs=(hyps,)) as pool:
        for (hid, C, keys), (_, group, _) in zip(pool.imap(work, [(h, s) for h, g, s in jobs]), jobs):
            perg[(group, hid)].update(C)
            gc = gclass(group)
            for (pk, Yp, isrot), mm in keys:
                (rot if isrot else uf)[(gc, hid)][(pk, Yp)] = mm
    print('stage A done %.0f s' % (time.time() - t0))

    # ---- stage B: OC1 at every distinct u-first maximum-matching pick vector
    tasks = []; tinfo = {}
    for (gc, hid), dct in sorted(uf.items()):
        h = hyps[hid]
        for j, ((pk, Yp), mm) in enumerate(dct.items()):
            if not mm: continue
            vals = unprof(pk, h)
            B = [[y] if y is not None else [] for y in Yp]
            tid = '%s:%d:%d' % (gc, hid, j)
            tasks.append(task_line(tid, h['sets'], vals, h['m'], B)); tinfo[tid] = (h['sets'], vals, h['m'], B, gc, hid)
    print('stage B: %d OC1 tasks' % len(tasks), flush=True)
    ans = run_c(tasks, args.procs, binpath, 'rf')
    print('stage B done %.0f s' % (time.time() - t0), flush=True)

    # ---- stage C: verify every witness in Python
    vjobs = collections.defaultdict(list)
    for tid, a in ans.items():
        s, v, m, B, gc, hid = tinfo[tid]
        vjobs[(gc, hid)].append((s, v, m, B, a))
    ver = collections.defaultdict(collections.Counter)
    flat = [(k, lst[i:i + 5000]) for k, lst in vjobs.items() for i in range(0, len(lst), 5000)]
    with Pool(args.procs) as pool:
        for (k, _), C in zip(flat, pool.imap(verify, [j for _, j in flat])): ver[k].update(C)
    fails = [(tid, tinfo[tid]) for tid, a in ans.items() if a[0] == 'F']
    second = collections.Counter(py_oc1(*info[:4]) for tid, info in fails)
    print('stage C done %.0f s' % (time.time() - t0), flush=True)

    # ---- optional: OC1 at the failing starts themselves
    orig = None
    if args.orig != '0':
        olines = []; rnd = random.Random(2)
        byh = collections.defaultdict(list)
        for hid, group, starts in jobs:
            if group == 'stored': continue
            byh[hid].extend(starts)
        for hid, sts in byh.items():
            pick = sts if args.orig == 'all' else rnd.sample(sts, min(len(sts), int(args.orig)))
            h = hyps[hid]
            for j, st in enumerate(pick):
                B = [[y] if y is not None else [] for y in st['picks']]
                olines.append(task_line('orig:%d:%d' % (hid, j), h['sets'], st['vals'], h['m'], B))
        oans = run_c(olines, args.procs, binpath, 'orig')
        orig = collections.defaultdict(collections.Counter)
        for tid, a in oans.items(): orig[int(tid.split(':')[1])][a[0]] += 1
        if args.orig_py:
            pj = []; per = collections.Counter(); oinfo = {}
            for line in olines:
                tok = line.split(); tid = tok[0]; hid = int(tid.split(':')[1])
                if oans[tid][0] == 'F' and per[hid] < args.orig_py:
                    per[hid] += 1; pj.append((hid, line))
            with Pool(args.procs) as pool:
                for hid, r in zip([h for h, _ in pj], pool.imap(py_from_line, [l for _, l in pj])):
                    orig[hid]['second implementation (Python) on F: ' + r] += 1
        print('orig done %.0f s' % (time.time() - t0), flush=True)

    report(hyps, meta, perg, uf, rot, ver, second, orig, args)
    print('time %.0f s' % (time.time() - t0))


def py_from_line(line):
    tok = line.split(); n, m = int(tok[1]), int(tok[2]); p = 3; sets = []; vals = []
    for i in range(n):
        k = int(tok[p]); p += 1
        sets.append([int(tok[p + 2 * q]) for q in range(k)]); vals.append([int(tok[p + 2 * q + 1]) for q in range(k)]); p += 2 * k
    B = [bits(int(tok[p + i])) for i in range(n)]
    return py_oc1(sets, vals, m, B)


def unprof(pk, h):
    flat = list(pk); out = []; p = 0
    for s in h['sets']: out.append(flat[p:p + len(s)]); p += len(s)
    return out


def report(hyps, meta, perg, uf, rot, ver, second, orig, args):
    def hname(hid): return '%s#%d' % (meta[hid]['list'], meta[hid]['idx'])
    print()
    print('== hypergraphs')
    for hid, h in sorted(hyps.items()):
        mt = meta[hid]
        print('%-12s m %2d nu %d (brute %d, export %d)  groups %s  export flag complete=%s' % (
            hname(hid), h['m'], h['nu'], h['nu_brute'], h['nu_export'], ','.join(sorted(mt['group'])), mt['complete']))
    print()
    print('== stage A per (group, hypergraph)')
    for (group, hid), C in sorted(perg.items(), key=lambda x: (x[0][0], hname(x[0][1]))):
        print('--', group, hname(hid))
        for k in sorted(C): print('   %-75s %d' % (k, C[k]))
    print()
    print('== RF at the u-first maximum-matching pick vectors (distinct (profile, Y\') pairs)')
    S = collections.defaultdict(collections.Counter)
    for (gc, hid), dct in sorted(uf.items()):
        cls = gc if gc == 'stored' else ('export-complete' if meta[hid]['complete'] else 'export-partial')
        C = collections.Counter()
        C['distinct u-first pick vectors'] = len(dct)
        C['  maximum matchings (RF tests these)'] = sum(dct.values())
        C['  not maximum matchings (excluded by RF)'] = len(dct) - sum(dct.values())
        for k, c in ver[(gc, hid)].items(): C['  OC1: ' + k] += c
        r = rot[(gc, hid)]
        C['distinct rotation (u, o - u) pick vectors'] = len(r)
        C['  rotation vectors that are maximum matchings'] = sum(r.values())
        C['  rotation vectors with a pickless agent'] = len(r) - sum(r.values())
        print('--', gc, hname(hid), '(%s)' % cls)
        for k in C: print('   %-75s %d' % (k, C[k]))
        S[cls].update(C); S['ALL ' + gc].update(C)
    for cls in sorted(S):
        print('-- total', cls)
        for k in S[cls]: print('   %-75s %d' % (k, S[cls][k]))
    print()
    print('== second implementation on F answers:', dict(second) if second else 'no F answers')
    print()
    print('== comparison with k4/oc1_hall.md section 24.10 (Hall)')
    E, St = S['ALL export'], S['ALL stored']
    A = collections.defaultdict(collections.Counter)
    for (g, hid), C in perg.items():
        A['stored' if g == 'stored' else 'export'].update(C)
    rows = [
        ('export failing starts', A['export']['starts'], HALL['export_failing_starts']),
        ('export listed failing orders', A['export']['listed orders'], HALL['export_failing_orders']),
        ('export distinct rotation RF starts (incl. pickless)', E['distinct rotation (u, o - u) pick vectors'], HALL['export_rf_starts']),
        ('export rotation RF starts that are maximum matchings', E['  rotation vectors that are maximum matchings'], HALL['export_mm']),
        ('export rotation vectors with a pickless agent', E['  rotation vectors with a pickless agent'], HALL['export_pickless_rot']),
        ('stored failing starts', A['stored']['starts'], HALL['stored_starts']),
        ('stored rotation RF starts that are maximum matchings', St['  rotation vectors that are maximum matchings'], HALL['stored_mm']),
        ('stored rotation vectors with a pickless agent', St['  rotation vectors with a pickless agent'], HALL['stored_pickless_rot']),
    ]
    for name, mine, hall in rows:
        print('   %-60s mine %9d  Hall %9d  %s' % (name, mine, hall, 'agree' if mine == hall else 'DIFFER'))
    if orig is not None:
        print()
        print('== OC1 search at the failing starts Y themselves (--orig %s); expected: F everywhere' % args.orig)
        for hid in sorted(orig): print('   %-12s %s' % (hname(hid), dict(orig[hid])))
    bad = sum(c for C in ver.values() for k, c in C.items() if 'INVALID' in k)
    nF = sum(C['F'] for C in ver.values())
    nmm = sum(C['  maximum matchings (RF tests these)'] for k, C in S.items() if k.startswith('ALL'))
    rfa_fail = sum(C['(start, receiver) pairs'] - C['(start, receiver) pairs with some u-first maximum-matching order (RF a)']
                   for C in perg.values())
    print()
    print('RESULT RF (a) fails at %d (start, receiver) pairs; RF (b): %d distinct maximum-matching u-first pick vectors, '
          'OC1 F answers %d, invalid witnesses %d' % (rfa_fail, nmm, nF, bad))


if __name__ == '__main__':
    main()
