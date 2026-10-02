#!/usr/bin/env python3
"""Independent Python check of k4/dlrc.c (compute/k4-rc): Conjecture DL_RC (R_C = T1 + T2 + T3+ + T4) and its key-graph
form. EVIDENCE tooling.

Built on k4/dl134_xcheck.py's model, which is main's k4/c4x_check.py enumeration (every base map good -> agent or junk,
(V1), (V2) literally, its own removal-only deficit `rodef`); dl134_xcheck.Prof gives the min-frozen class, the needs,
NA, the frozen flags and the T1 / T2 / T3p / T3h / T4 kinds of a move. It uses neither k4/suite/model.py nor any code of
k4/dlrc.c. (c4x_check.analyse also decides completability, which nothing here reads; it is replaced by a stub for speed
unless --full is given.) The T3+ test is the coordinator's `t3plus` (compute/k4-rc brief, xverify2.py), extended to
return |W|:
  NA' = NA; ch = the changed agents; exactly one x in ch frozen in P and free in P'; exactly one z free in P and frozen
  in P'; W = the agents of ch frozen in both; Y = those free in both, |Y| <= 1, each giving up a good; the sorted bases
  of W + {z} in P' equal those of W + {x} in P. Value 2 (T3+) if z needs its new good in P, else 1 (weak, T3w).
Per state (min-frozen P with def(P) > 0, profiles with omega >= 1) it computes, from the definitions in k4/dlrc.c's
header: f, def, t1 t2 t3p t3h t4 (dl134_xcheck's kinds), t3c (an improving T3+ move with W nonempty), s3c (its least
|ch|), wmin, t3w, wminw, rdc, nrc, bestrc, the key (NA, the frozen agents' bases), dstar = def*(key), kmin / kminw (the
least def* over the keys reached by one T3+ (resp. T3+ or T3w) or T4 move from some state of the key, for keys with
def* > 0 at f >= 1; 999998 elsewhere; 999999 if there is none), keyok; and per profile the -H line of dlrc.c. It runs
dlrc.c (-s -H) on the same profiles and requires exact agreement on every field, and checks besides:
  - dlrc.c's "K" and "L" lines and its B, G, M, Z, C, Y tables equal k4/dlrt4.c's (unchanged) on the same input, and every
    "S" line of dlrc.c starts with dlrt4.c's "S" line;
  - dlrc.c built with -DBIGPP=0 (large-class code path everywhere) prints exactly the default build's output;
  - dlrc.c's internal counters rcnokey and anomc are 0.

usage:
  python3 k4/dlrc_ref.py inst FILE.json ...                   JSON lists of {"id", "sets", "vals", "m"}
  python3 k4/dlrc_ref.py tsv FILE.tsv ...                     the profiles of results/k4_dl13/n4_failures_*.tsv
  python3 k4/dlrc_ref.py suite [--maxprod=P]                  the suite's complete instances (base-map count <= P)
  python3 k4/dlrc_ref.py random FILE ... --want=N [--neg=K] [--seed=S]
      random (core, profile) draws from the certificate files (in turn), screened with dlrc.c: N profiles with an f >= 1
      def > 0 state and K without one
options: --jobs=J, --full (keep c4x_check's completability test), --expect-rt4fail=N --expect-rcfail=N (assert totals)"""
import collections, gzip, hashlib, json, os, random, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import c4x_check as CX
import dl134_xcheck as X

if '--full' not in sys.argv:
    CX.completable = lambda *a, **k: None          # not read by dl134_xcheck.Prof; the enumeration and rodef are kept

TMP = tempfile.gettempdir()
INF = 999999
NC = 999998                                        # kmin not computed (key with def* <= 0, or f = 0)


def cdef(x):
    return INF if x >= 1 << 20 else x


# ------------------------------------------------------------------ the T3+ test (the coordinator's t3plus, with |W|)
def t3plus(n, P, Q, IP, IQ):
    """(0, None) / (1, |W|) weak / (2, |W|) T3+"""
    (N1, NA1, fz1), (N2, NA2, fz2) = IP, IQ
    if NA1 != NA2: return 0, None
    ch = [i for i in range(n) if P[i] != Q[i]]
    xs = [i for i in ch if fz1[i] and not fz2[i]]; zs = [i for i in ch if fz2[i] and not fz1[i]]
    ws = [i for i in ch if fz1[i] and fz2[i]]; ys = [i for i in ch if not fz1[i] and not fz2[i]]
    if len(xs) != 1 or len(zs) != 1 or len(ys) > 1: return 0, None
    if not all(P[y] - Q[y] for y in ys): return 0, None
    if sorted(map(sorted, [Q[i] for i in ws + zs])) != sorted(map(sorted, [P[i] for i in ws + xs])): return 0, None
    return (2 if Q[zs[0]] <= N1[zs[0]] else 1), len(ws)


def is_t4(k): return k['t4']


def ref_profile(d):
    """{bases: fields} for the def > 0 states, and the H-line fields, of one profile"""
    sets, vals, m = d['sets'], d['vals'], d['m']
    n = len(sets)
    Pr = X.Prof(sets, vals, m)
    omega = Pr.f - (2 * n - m)
    if omega <= 0:
        return {}, [-1, 0, 0, 0, 0, 0, 0, INF, 0, INF, 0, 0, 0]
    f = Pr.f
    mp = [(P, cdef(dv)) for P, dv in Pr.mp]
    info = {P: Pr.info(P) for P, _ in mp}
    D = dict(mp)

    def key(P):
        N, NA, fz = info[P]
        return (NA, tuple(P[i] if fz[i] else None for i in range(n)))
    K = collections.defaultdict(list)
    for P, _ in mp: K[key(P)].append(P)
    dstar = {k: min(D[P] for P in Ps) for k, Ps in K.items()}
    kmin, kminw = {}, {}
    for k, Ps in K.items():
        if f < 1 or dstar[k] <= 0: kmin[k] = kminw[k] = NC; continue
        a = b = INF
        for P in Ps:
            for Q, _ in mp:
                kq = key(Q)
                if kq == k: continue
                kinds, _ = Pr.move(P, Q, info[P], info[Q])
                t, _w = t3plus(n, P, Q, info[P], info[Q])
                if t == 2 or kinds['t4']: a = min(a, dstar[kq]); b = min(b, dstar[kq])
                elif t == 1: b = min(b, dstar[kq])
        kmin[k], kminw[k] = a, b
    out = {}
    h = dict(st1=0, rt4f=0, rcf=0, ch=0, ch3=0, chw2=0, gap=INF, c3=0, mv=INF, kf=0, maxw=0)
    for P, dP in mp:
        if dP <= 0: continue
        fl = dict(t1=0, t2=0, t3p=0, t3h=0, t4=0)
        t3c = 0; s3c = 99; wmin = 99; t3w = 0; wminw = 99; rdc = 99; nrc = 0; bestrc = INF
        for Q, dQ in mp:
            if dQ >= dP: continue
            kinds, c = Pr.move(P, Q, info[P], info[Q])
            t, w = t3plus(n, P, Q, info[P], info[Q])
            rt4 = False
            for x in fl:
                if kinds[x]: fl[x] = 1; rt4 = True
            if t >= 1: t3w = 1; wminw = min(wminw, w)
            if t == 2:
                wmin = min(wmin, w)
                if w > 0: t3c = 1; s3c = min(s3c, c)
            if rt4 or t == 2:
                nrc += 1; rdc = min(rdc, c); bestrc = min(bestrc, dQ)
        ok = any(fl.values()); okrc = ok or bool(t3c)
        k = key(P)
        keyok = int(dstar[k] < dP or kmin[k] < dP)
        Bs = tuple(tuple(sorted(B)) for B in P)
        out[Bs] = dict(f=f, d=dP, **fl, t3c=t3c, s3c=s3c, wmin=wmin, t3w=t3w, wminw=wminw, rdc=rdc, nrc=nrc, bestrc=bestrc,
                       dstar=dstar[k], kmin=kmin[k], kminw=kminw[k], keyok=keyok)
        if f >= 1:
            h['st1'] += 1
            if not ok: h['rt4f'] += 1
            if not okrc: h['rcf'] += 1
            if not ok and okrc:
                h['ch'] += 1
                if f >= 3: h['ch3'] += 1
                if wmin >= 2: h['chw2'] += 1
                h['maxw'] = max(h['maxw'], wmin)
            h['gap'] = min(h['gap'], dP - bestrc if okrc else 0)
            h['mv'] = min(h['mv'], nrc)
            if rdc >= 3: h['c3'] += 1
            if not keyok: h['kf'] += 1
    kfk = sum(1 for k in K if f >= 1 and dstar[k] > 0 and kmin[k] >= dstar[k])
    H = [f, h['st1'], h['rt4f'], h['rcf'], h['ch'], h['ch3'], h['chw2'], h['gap'], h['c3'], h['mv'], h['kf'], kfk, h['maxw']]
    return out, H


# ------------------------------------------------------------------ the C side
def build(src, extra=()):
    sha = hashlib.sha256(open(src, 'rb').read()).hexdigest()
    b = os.path.join(TMP, 'k4rcref_' + os.path.basename(src).replace('.c', '') + '_' + sha[:16] + ''.join(e.replace('=', '') for e in extra))
    if not os.path.exists(b):
        subprocess.run(['gcc', '-O2'] + list(extra) + ['-o', b + '.tmp', src], check=True); os.replace(b + '.tmp', b)
    return b, sha


def block(d, tag):
    out = [f"{len(d['sets'])} {d['m']} {tag}"] + [f"{len(S)} {' '.join(map(str, S))}" for S in d['sets']]
    out.append(' '.join('1' for _ in d['sets']))
    out += [' '.join(map(str, V)) for V in d['vals']]
    out.append('0')
    return '\n'.join(out) + '\n'


CF = 'f d t1 t2 t3p t3h t4 t3c s3c wmin t3w wminw rdc nrc bestrc dstar kmin kminw keyok'.split()


def c_parse(out, sets_list):
    """dlrc.c -s -H output -> per block {'S': {bases: fields}, 'Sraw': {bases: line}, 'H': [...], 'K', 'L', 'LC', 'tab'}"""
    res, cur, raw, H = [], {}, {}, None
    for l in out.splitlines():
        w = l.split()
        if not w: continue
        if w[0] == 'S':
            n = len(sets_list[len(res)])
            Bs = tuple(tuple(g for g in range(64) if int(b) >> g & 1) for b in w[2:2 + n])
            x = w[2 + n:]
            y = list(map(int, x[20:32]))           # x[0:20]: dlrt4.c's fields (def .. sig)
            cur[Bs] = dict(f=int(w[1]), d=int(x[0]), t1=int(x[3]), t2=int(x[4]), t3p=int(x[5]), t3h=int(x[6]), t4=int(x[7]),
                           t3c=y[0], s3c=y[1], wmin=y[2], t3w=y[3], wminw=y[4], rdc=y[5], nrc=y[6], bestrc=y[7], dstar=y[8],
                           kmin=y[9], kminw=y[10], keyok=y[11])
            raw[Bs] = ' '.join(w[:2 + n + 20])
        elif w[0] == 'H': H = list(map(int, w[2 + len(sets_list[len(res)]):]))
        elif w[0] == 'K': res.append({'S': cur, 'Sraw': raw, 'H': H, 'K': l, 'tab': {}}); cur = {}; raw = {}; H = None
        elif w[0] == 'L': res[-1]['L'] = l
        elif w[0] == 'LC': res[-1]['LC'] = {k: int(v) for k, v in zip(w[2::2], w[3::2])}
        elif w[0] in ('B', 'G', 'M', 'Z', 'C', 'Y', 'W') and res: res[-1]['tab'][l.rsplit(' ', 1)[0]] = int(w[-1])
    return res


def rt4_parse(out, sets_list):
    res, raw = [], {}
    for l in out.splitlines():
        w = l.split()
        if not w: continue
        if w[0] == 'S':
            n = len(sets_list[len(res)])
            Bs = tuple(tuple(g for g in range(64) if int(b) >> g & 1) for b in w[2:2 + n])
            raw[Bs] = l
        elif w[0] == 'K': res.append({'Sraw': raw, 'K': l, 'tab': {}}); raw = {}
        elif w[0] == 'L': res[-1]['L'] = l
        elif w[0] in ('B', 'G', 'M', 'Z', 'C', 'Y') and res: res[-1]['tab'][l.rsplit(' ', 1)[0]] = int(w[-1])
    return res


def compare(insts, opt, stats, log):
    brc, sha = build(os.path.join(HERE, 'dlrc.c'))
    brc0, _ = build(os.path.join(HERE, 'dlrc.c'), ('-DBIGPP=0',))
    brt, shart = build(os.path.join(HERE, 'dlrt4.c'))
    jobs = int(opt.get('jobs', 1))
    pool = Pool(jobs) if jobs > 1 else None
    CH = 200
    for c0 in range(0, len(insts), CH):
        chunk = insts[c0:c0 + CH]
        inp = ''.join(block(d, k) for k, d in enumerate(chunk))
        orc = subprocess.run([brc, '-s', '-H', '-r1', '-o1'], input=inp, capture_output=True, text=True, check=True).stdout
        orc0 = subprocess.run([brc0, '-s', '-H', '-r1', '-o1'], input=inp, capture_output=True, text=True, check=True).stdout
        ort = subprocess.run([brt, '-s'], input=inp, capture_output=True, text=True, check=True).stdout
        if orc != orc0: stats['mm_bigpp'] += 1; log('MISMATCH -DBIGPP=0 build, chunk at %d' % c0)
        sl = [d['sets'] for d in chunk]
        C = c_parse(orc, sl); R4 = rt4_parse(ort, sl)
        if len(C) != len(chunk) or len(R4) != len(chunk):
            stats['mm_blocks'] += 1; log('MISMATCH number of blocks, chunk at %d' % c0); continue
        for cb, rb in zip(C, R4):
            if cb['K'] != rb['K'] or cb['L'] != rb['L'] or {k: v for k, v in cb['tab'].items() if k[0] != 'W'} != rb['tab']:
                stats['mm_rt4'] += 1; log('MISMATCH dlrt4.c K / L / tables, chunk at %d block %s' % (c0, cb['K'].split()[1]))
            if set(cb['Sraw']) != set(rb['Sraw']) or any(rb['Sraw'][Bs] != cb['Sraw'][Bs] for Bs in cb['Sraw']):
                stats['mm_rt4S'] += 1; log('MISMATCH dlrt4.c S lines, chunk at %d block %s' % (c0, cb['K'].split()[1]))
            stats['rcnokey'] += cb['LC']['rcnokey']; stats['anomc'] += cb['LC']['anomc']
        it = pool.imap(ref_profile, chunk, chunksize=1) if pool else map(ref_profile, chunk)
        for d, (R, H), cb in zip(chunk, it, C):
            stats['prof'] += 1
            Cs = cb['S']
            if cb['H'] != H:
                stats['mm_H'] += 1; log('MISMATCH H line %s C %s ref %s' % (d['id'], cb['H'], H))
            if set(R) != set(Cs):
                stats['mm_states'] += 1; log('MISMATCH states %s %s' % (d['id'], sorted(set(R) ^ set(Cs))[:3])); continue
            if any(s['f'] >= 1 for s in Cs.values()): stats['prof_f1'] += 1
            for Bs, s in Cs.items():
                a = R[Bs]
                bad = [fn for fn in CF if a[fn] != s[fn]]
                if bad:
                    stats['mm_fields'] += 1; log('MISMATCH %s %s fields %s C %s ref %s' % (d['id'], Bs, bad, s, a))
                stats['st'] += 1
                if s['f'] < 1: stats['st_f0'] += 1; continue
                stats['st_f1'] += 1
                ok = s['t1'] or s['t2'] or s['t3p'] or s['t3h'] or s['t4']
                if not ok: stats['rt4fail'] += 1
                if not (ok or s['t3c']): stats['rcfail'] += 1
                if not ok and s['t3c']: stats['chain'] += 1
                if s['t3c']: stats['t3c'] += 1
                if not s['keyok']: stats['keyfail'] += 1
                if s['d'] == s['dstar']: stats['keymin_states'] += 1
        log('#  %d / %d profiles: %s' % (min(c0 + CH, len(insts)), len(insts), dict(stats)))
    if pool: pool.close()
    return sha, shart


# ------------------------------------------------------------------ inputs
def tsv_items(files):
    out = []
    for fn in files:
        for l in open(fn):
            w = l.rstrip('\n').split('\t')
            if w[0] == 'file': continue
            out.append({'sets': json.loads(w[4]), 'm': int(w[3]), 'vals': json.loads(w[6]), 'id': '%s#%s:%s' % (w[0], w[1], w[5])})
    return out


def suite_items(opt):
    import glob
    maxprod = int(opt.get('maxprod', 2000000))
    out = []
    for fn in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
        d = json.load(open(fn))
        if 'kind' in d or 'vals' not in d: continue
        d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
        if d['m'] > 32: continue
        prod = 1
        for g in range(d['m']): prod *= 1 + sum(g in S for S in d['sets'])
        if prod > maxprod: continue
        out.append({'id': d['id'], 'sets': d['sets'], 'm': d['m'], 'vals': d['vals']})
    return out


def random_items(files, opt, log):
    rng = random.Random(int(opt.get('seed', 1)))
    want = int(opt.get('want', 1000)); neg = int(opt.get('neg', 0))
    brc, _ = build(os.path.join(HERE, 'dlrc.c'))
    data = [(os.path.basename(f).replace('.json.gz', ''), json.load(gzip.open(f, 'rt'))['cores']) for f in files]
    doms = {}; pos, negs, drawn, fi = [], [], 0, 0
    while len(pos) < want or len(negs) < neg:
        batch = []
        for _ in range(2000):
            base, cores = data[fi % len(data)]; fi += 1
            k = rng.randrange(len(cores)); c = cores[k]
            if (base, k) not in doms: doms[(base, k)] = check4.core_domains(c['sets'], c['m'], False)
            Dm = doms[(base, k)]
            ts = [rng.randrange(len(x)) for x in Dm]
            batch.append({'sets': c['sets'], 'm': c['m'], 'vals': [[Dm[i][ts[i]][g] for g in c['sets'][i]] for i in range(len(c['sets']))],
                          'id': '%s#%d[m=%d,idx=%d]:%s' % (base, k, c['m'], c.get('idx', k), ','.join(map(str, ts)))})
        drawn += len(batch)
        out = subprocess.run([brc, '-H'], input=''.join(block(d, j) for j, d in enumerate(batch)), capture_output=True,
                             text=True, check=True).stdout
        Hs = [list(map(int, l.split()[1:])) for l in out.splitlines() if l.startswith('H ')]
        for d, h in zip(batch, Hs):
            st1 = h[1 + len(d['sets']) + 1]
            if st1 and len(pos) < want: pos.append(d)
            elif not st1 and len(negs) < neg: negs.append(d)
    log('# random: %d profiles drawn, %d with an f >= 1 def > 0 state kept, %d without one kept' % (drawn, len(pos), len(negs)))
    return pos + negs


def main(argv):
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    log = lambda s: print(s, flush=True)
    log('# command: python3 k4/dlrc_ref.py ' + ' '.join(argv))
    t0 = time.time()
    if mode == 'inst':
        insts = [d for fn in rest for d in json.load(open(fn))]
        for d in insts: d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
    elif mode == 'tsv': insts = tsv_items(rest)
    elif mode == 'suite': insts = suite_items(opt)
    elif mode == 'random': insts = random_items(rest, opt, log)
    else: print(__doc__); return
    log('# %d profiles' % len(insts))
    stats = collections.Counter()
    sha, shart = compare(insts, opt, stats, log)
    log('# dlrc.c sha256 %s; dlrt4.c sha256 %s' % (sha, shart))
    log('profiles %d (with an f >= 1 def > 0 state %d); states %d (f = 0: %d, f >= 1: %d); f >= 1: DL_RT4 fails at %d, '
        'DL_RC fails at %d, chain states %d, with an improving T3c move %d, key form fails at %d; states with def = def* '
        '%d' % (stats['prof'], stats['prof_f1'], stats['st'], stats['st_f0'], stats['st_f1'], stats['rt4fail'],
                stats['rcfail'], stats['chain'], stats['t3c'], stats['keyfail'], stats['keymin_states']))
    nmm = sum(stats[k] for k in ('mm_bigpp', 'mm_blocks', 'mm_rt4', 'mm_rt4S', 'mm_H', 'mm_states', 'mm_fields'))
    log('mismatches: reference vs dlrc.c: states %d, fields %d, H lines %d; dlrc.c vs dlrt4.c: K/L/tables %d, S lines %d; '
        '-DBIGPP=0 build %d; blocks %d; dlrc.c rcnokey %d, anomc %d; TOTAL %d [%.0f s]'
        % (stats['mm_states'], stats['mm_fields'], stats['mm_H'], stats['mm_rt4'], stats['mm_rt4S'], stats['mm_bigpp'],
           stats['mm_blocks'], stats['rcnokey'], stats['anomc'], nmm + stats['rcnokey'] + stats['anomc'], time.time() - t0))
    if 'expect-rt4fail' in opt: assert stats['rt4fail'] == int(opt['expect-rt4fail']), 'rt4fail'
    if 'expect-rcfail' in opt: assert stats['rcfail'] == int(opt['expect-rcfail']), 'rcfail'


if __name__ == '__main__':
    main(sys.argv[1:])
