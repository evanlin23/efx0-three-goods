#!/usr/bin/env python3
"""Python reference for k4/dlrt4.c (compute/k4-rt4): Conjecture DL_RT4, RT4 = T1 + T2 + T3 + T4. EVIDENCE tooling.

The reference uses k4/suite/model.py (the suite's own model: 𝒫, the min-frozen class, the removal-only deficit) and
k4/dl2_relations.py (the shape of a move P -> P' and its relation predicates; RTr is R_T = T1 + T2 + T3 of k4/dl2.md
§3) as libraries, and adds its own T4 test, written here from the definition and sharing no code with k4/dlrt4.c:
  (T4) the agents whose base changes are frozen in P and in P' (PA.frozen of k4/dl2_classify.py: a one-good base inside
       the needed set), they hold in P' exactly the goods they held in P (a permutation of their singleton bases), and
       NA(P') = NA(P). Its cycle type is read off the permutation ("2", "3", "2+2", ...).
T1, T2, T3 are dl2_relations.py's: T1 = _one(s, nt_ok=False); T2 = the rotation clause of RTr (|ch| >= 2, every changed
agent free in P and in P', no need transfer); T3 = _swap(s, 1, gives=True) (T3p without, T3h with the helper). For every
improving move the reference asserts that RTr holds iff T1, T2 or T3 does, that R13 holds iff T1 or T3 does, and that at
most one kind holds.

Per state (min-frozen P with def(P) > 0) it computes what dlrt4.c's "S" line holds (k4/dlrt4.c's header): f, def, the
nearest distance, rd, the flags t1 t2 t3p t3h t4, the least sizes s2 s3p s3h s4, the T1 / T2 / T3 type masks, the T4
cycle types (all, and at the least T4 size), the least deficit dW over the improving RT4 moves, and the Pareto flag;
and compares them, with exact agreement, with dlrt4.c -s. It also checks:
  - dlrt4.c's "K" line equals k4/dl13.c's on the same input (the shared first pass);
  - per state, dlrt4.c's t1, t3p, t3h, T1 and T3 type masks equal dl13.c's (the T1 and T3 code is dl13.c's);
  - dlrt4.c built with -DBIGPP=0 (every class hashed, candidates generated) prints exactly the default build's output;
  - with --x (n <= 4): the flags t1 t2 t3 t4 and the least T4 size against k4/dl134_xcheck.py (main's c4x_check.py with
    its own move kinds, written in compute/k4-dl13 without model.py).

usage:
  python3 k4/dlrt4_ref.py suite [IDS...] [--maxn=N]                      the suite's core instances (n <= 6), or those named
  python3 k4/dlrt4_ref.py tsv FILE.tsv ...                               the profiles of results/k4_dl13/n4_failures_*.tsv
                                                                         (and checks that every listed failing state is a state)
  python3 k4/dlrt4_ref.py random FILE ... --states=N [--seed=S] [--neg=K] random (core, profile) draws from the certificate
      files (one file after the other in turn), screened with dlrt4.c until N states with f >= 1 are found; those profiles
      and K screened profiles without such a state are compared
  python3 k4/dlrt4_ref.py inst FILE.json                                 a JSON list of {"id", "sets", "vals", "m"}
  python3 k4/dlrt4_ref.py records DUMP.jsonl.gz ... [--allrec]           the profiles of the dump records of states
      without a T1 or T3 move (needing T2 or T4, or failing); --allrec: of every record
  python3 k4/dlrt4_ref.py write-tsv-inst OUT.json FILE.tsv ...           write the TSV profiles as an inst list (for dlrt4_run.py)
options: --x (also k4/dl134_xcheck.py, n <= 4), --jobs=J, --every=E (every E-th profile)"""
import collections, gzip, hashlib, json, os, random, subprocess, sys, tempfile
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import dl2_relations as DR
from dl2_classify import PA, M, bits, pc

TMP = tempfile.gettempdir()
CINF = 999999


def build(src, extra=()):
    sha = hashlib.sha256(open(src, 'rb').read()).hexdigest()
    b = os.path.join(TMP, 'k4ref_' + os.path.basename(src).replace('.c', '') + '_' + sha[:16] + ''.join(e.replace('=', '') for e in extra))
    if not os.path.exists(b):
        subprocess.run(['gcc', '-O2'] + list(extra) + ['-o', b + '.tmp', src], check=True); os.replace(b + '.tmp', b)
    return b, sha


def block(d, tag):
    out = [f"{len(d['sets'])} {d['m']} {tag}"] + [f"{len(S)} {' '.join(map(str, S))}" for S in d['sets']]
    out.append(' '.join('1' for _ in d['sets']))
    out += [' '.join(map(str, V)) for V in d['vals']]
    out.append('0')
    return '\n'.join(out) + '\n'


# ------------------------------------------------------------------ the reference
def t4_move(P, P2, ch):
    """own T4 test: (True, cycle type string) if P -> P2 permutes the singleton bases of frozen agents, NA kept"""
    if len(ch) < 2: return False, None
    if not all(P.frozen[i] and P2.frozen[i] for i in ch): return False, None
    if P.NA != P2.NA: return False, None
    old = sorted(P.Bs[i] for i in ch); new = sorted(P2.Bs[i] for i in ch)
    if old != new or any(pc(B) != 1 for B in old): return False, None
    holder = {P.Bs[i]: i for i in ch}                  # good (as a one-bit mask) -> its holder in P
    to = {i: holder[P2.Bs[i]] for i in ch}             # agent i holds in P2 the good agent to[i] held in P
    seen, lens = set(), []
    for i in ch:
        if i in seen: continue
        l, j = 0, i
        while j not in seen: seen.add(j); l += 1; j = to[j]
        lens.append(l)
    return True, '+'.join(str(x) for x in sorted(lens, reverse=True))


XS = {'J': 0, 'JZ': 1, 'other': 2}
HK = {'rel1': 1, 'rel': 1, 'junk': 2, 'trade': 3}
T2pred = lambda s: s['k'] >= 2 and len(s['Y']) == s['k'] and not s['nt']


def ref_states(d):
    """{bases (tuple of sorted tuples): fields} for every min-frozen P with def(P) > 0 (model.py, dl2_relations.py)"""
    I = M.Inst(d['sets'], d['vals'], d.get('m'))
    I.preallocs()
    if I.omega <= 0: return {}
    mp = [Bs for Bs, NA in I.minP]
    PAs = {Bs: PA(I, Bs) for Bs in mp}
    D = {}
    for Bs in mp:
        x = I.deficit(Bs); D[Bs] = CINF if x is None else x
    vv = {Bs: [I.val(i, Bs[i]) for i in range(I.n)] for Bs in mp}
    out = {}
    for Bs in mp:
        if D[Bs] <= 0: continue
        P = PAs[Bs]
        fl = dict(t1=0, t2=0, t3p=0, t3h=0, t4=0); sz = dict(t2=99, t3p=99, t3h=99, t4=99)
        t1m = t2m = t3m = 0; cy = set(); cmin = {}; rd = 99; k = 99; dW = CINF
        for B2 in mp:
            if D[B2] >= D[Bs]: continue
            P2 = PAs[B2]
            ch = [i for i in range(I.n) if Bs[i] != B2[i]]
            k = min(k, len(ch))
            s = DR.shape(P, P2)
            t1 = DR._one(s, nt_ok=False); t2 = T2pred(s); t3 = DR._swap(s, 1, gives=True)
            t4, cyc = t4_move(P, P2, ch)
            kinds = [x for x, h in (('t1', t1), ('t2', t2), ('t3', t3), ('t4', t4)) if h]
            assert len(kinds) <= 1, ('kinds overlap', kinds, Bs, B2)
            assert DR.RELATIONS['RTr'][1](s) == bool(t1 or t2 or t3), ('RTr', Bs, B2)
            assert DR.RELATIONS['R13'][1](s) == bool(t1 or t3), ('R13', Bs, B2)
            if not kinds: continue
            rd = min(rd, len(ch)); dW = min(dW, D[B2])
            if t1:
                fl['t1'] = 1
                y = ch[0]; B, Bn = Bs[y], B2[y]
                t1m |= 1 << (0 if not (Bn & ~B) else 1 if not (B & ~Bn) else 2)
            elif t2:
                fl['t2'] = 1; sz['t2'] = min(sz['t2'], len(ch)); t2m |= 1 << len(ch)
            elif t3:
                kk = 't3h' if s['Y'] else 't3p'
                fl[kk] = 1; sz[kk] = min(sz[kk], len(ch))
                t3m |= 1 << (4 * XS[s['xsrc']] + (HK[s['Y'][0]] if s['Y'] else 0))
            else:
                fl['t4'] = 1; sz['t4'] = min(sz['t4'], len(ch)); cy.add(cyc)
                cmin.setdefault(len(ch), set()).add(cyc)
        pm = int(not any(B2 != Bs and all(a >= b for a, b in zip(vv[B2], vv[Bs])) and vv[B2] != vv[Bs] for B2 in mp))
        out[tuple(tuple(sorted(bits(B))) for B in Bs)] = dict(
            f=I.f, d=D[Bs], k=k, rd=rd, **fl, s2=sz['t2'], s3p=sz['t3p'], s3h=sz['t3h'], s4=sz['t4'], t1m=t1m, t2m=t2m,
            t3m=t3m, cyc=frozenset(cy), cycmin=frozenset(cmin[sz['t4']]) if cy else frozenset(), dW=dW, pm=pm)
    return out


# ------------------------------------------------------------------ the C side
def c_parse(out, sets_list):
    """dlrt4.c -s output -> per block: (K line, L line, {bases: fields})"""
    res, cur = [], {}
    for l in out.splitlines():
        w = l.split()
        if not w: continue
        if w[0] == 'S':
            n = len(sets_list[len(res)])
            Bs = tuple(tuple(g for g in range(64) if int(b) >> g & 1) for b in w[2:2 + n])
            x = w[2 + n:]
            st = lambda z: frozenset() if z == '-' else frozenset(z.split(','))
            cur[Bs] = dict(f=int(w[1]), d=int(x[0]), k=int(x[1]), rd=int(x[2]), t1=int(x[3]), t2=int(x[4]), t3p=int(x[5]),
                           t3h=int(x[6]), t4=int(x[7]), s2=int(x[8]), s3p=int(x[9]), s3h=int(x[10]), s4=int(x[11]),
                           t1m=int(x[12]), t2m=int(x[13]), t3m=int(x[14]), cyc=st(x[15]), cycmin=st(x[16]), dW=int(x[17]),
                           pm=int(x[18]))
        elif w[0] == 'K': res.append([l, None, cur]); cur = {}
        elif w[0] == 'L': res[-1][1] = l
    return res


def c13_parse(out, sets_list):
    """dl13.c -s output -> per block: (K line, {bases: (t1, t3p, t3h, t1mask, t3mask)})"""
    res, cur = [], {}
    for l in out.splitlines():
        w = l.split()
        if not w: continue
        if w[0] == 'S':
            n = len(sets_list[len(res)])
            Bs = tuple(tuple(g for g in range(64) if int(b) >> g & 1) for b in w[2:2 + n])
            x = list(map(int, w[2 + n:2 + n + 11]))
            cur[Bs] = (x[3], x[4], x[5], x[6], x[7])
        elif w[0] == 'K': res.append([l, cur]); cur = {}
    return res


def x_states(d):
    """k4/dl134_xcheck.py (c4x_check.py): {bases: (t1, t2, t3, t4, least T4 size)} for the def > 0 states (n <= 4)"""
    import dl134_xcheck as X
    Pr = X.Prof(d['sets'], d['vals'], d['m'])
    out = {}
    if Pr.f < 0: return out
    for P, dP in Pr.mp:
        if dP <= 0: continue
        flags, holds, t4min, dist, ok = Pr.state(P, dP)
        out[tuple(tuple(sorted(B)) for B in P)] = (int(flags['t1']), int(flags['t2']), int(flags['t3p'] or flags['t3h']),
                                                    int(flags['t4']), t4min if flags['t4'] else 99, ok)
    return out


def one(args):
    d, want_x = args
    try:
        r = ref_states(d)
    except AssertionError as e:
        return d, None, str(e), None
    xs = x_states(d) if want_x and len(d['sets']) <= 4 else None
    return d, r, None, xs


FIELDS = 'f d k rd t1 t2 t3p t3h t4 s2 s3p s3h s4 t1m t2m t3m cyc cycmin dW pm'.split()


def compare(insts, opt, stats, log):
    """run the C builds on insts (chunks of 200) and compare with the reference"""
    brt, shrt = build(os.path.join(HERE, 'dlrt4.c'))
    brth, _ = build(os.path.join(HERE, 'dlrt4.c'), ('-DBIGPP=0',))
    b13, _ = build(os.path.join(HERE, 'dl13.c'))
    jobs = int(opt.get('jobs', 1)); want_x = 'x' in opt
    pool = Pool(jobs) if jobs > 1 else None
    CH = 200
    for c0 in range(0, len(insts), CH):
        chunk = insts[c0:c0 + CH]
        inp = ''.join(block(d, k) for k, d in enumerate(chunk))
        ort = subprocess.run([brt, '-s', '-r1', '-o1'], input=inp, capture_output=True, text=True, check=True).stdout
        orth = subprocess.run([brth, '-s', '-r1', '-o1'], input=inp, capture_output=True, text=True, check=True).stdout
        o13 = subprocess.run([b13, '-s'], input=inp, capture_output=True, text=True, check=True).stdout
        if ort != orth:
            stats['mm_hash'] += 1; log('MISMATCH -DBIGPP=0 build, chunk at %d' % c0)
        sl = [d['sets'] for d in chunk]
        C = c_parse(ort, sl); C13 = c13_parse(o13, sl)
        if len(C) != len(chunk) or [c[0] for c in C] != [c[0] for c in C13]:
            stats['mm_K'] += 1; log('MISMATCH K lines vs dl13.c, chunk at %d' % c0)
        it = (pool.imap(one, [(d, want_x) for d in chunk], chunksize=2) if pool else map(one, [(d, want_x) for d in chunk]))
        for (d, R, err, X), (_, Lline, Cs), (_, C13s) in zip(it, C, C13):
            stats['prof'] += 1
            if err:
                stats['assert'] += 1; log('ASSERTION in the reference %s: %s' % (d['id'], err)); continue
            if Cs: stats['prof_pos'] += 1
            if any(s['f'] >= 1 for s in Cs.values()): stats['prof_f1'] += 1
            for Bs, s in Cs.items():
                stats['st'] += 1; stats['st_f0' if s['f'] == 0 else 'st_f1'] += 1
                ok = s['t1'] or s['t2'] or s['t3p'] or s['t3h'] or s['t4']
                if not ok: stats['fail_f0' if s['f'] == 0 else 'fail_f1'] += 1
                if s['f'] >= 1:
                    for kk in ('t1', 't2', 't3p', 't3h', 't4'):
                        if s[kk]: stats['f1_' + kk] += 1
                    if s['t4'] and not (s['t1'] or s['t2'] or s['t3p'] or s['t3h']): stats['f1_t4only'] += 1
                    if s['t2'] and not (s['t1'] or s['t4'] or s['t3p'] or s['t3h']): stats['f1_t2only'] += 1
                c13 = C13s.get(Bs)
                if c13 is None or c13 != (s['t1'], s['t3p'], s['t3h'], s['t1m'], s['t3m']):
                    stats['mm_13'] += 1; log('MISMATCH vs dl13.c %s %s %s %s' % (d['id'], Bs, c13, s))
            if set(R) != set(Cs):
                stats['mm_ref'] += 1; log('MISMATCH reference states %s %s' % (d['id'], sorted(set(R) ^ set(Cs))[:3]))
            else:
                for Bs, s in Cs.items():
                    a = R[Bs]
                    bad = [fn for fn in FIELDS if a[fn] != s[fn]]
                    if bad:
                        stats['mm_ref'] += 1
                        log('MISMATCH reference %s %s fields %s C %s ref %s' % (d['id'], Bs, bad, s, a))
            if X is not None:
                if set(X) != set(Cs):
                    stats['mm_x'] += 1; log('MISMATCH xcheck states %s %s' % (d['id'], sorted(set(X) ^ set(Cs))[:3]))
                else:
                    for Bs, s in Cs.items():
                        stats['st_x'] += 1
                        x = X[Bs]
                        mine = (s['t1'], s['t2'], int(bool(s['t3p'] or s['t3h'])), s['t4'], s['s4'], True)
                        if x != mine:
                            stats['mm_x'] += 1; log('MISMATCH xcheck %s %s C %s x %s' % (d['id'], Bs, mine, x))
        log('#  %d / %d profiles: %s' % (min(c0 + CH, len(insts)), len(insts), dict(stats)))
    if pool: pool.close()
    return shrt


# ------------------------------------------------------------------ inputs
def tsv_items(files):
    out, fails = [], []
    for fn in files:
        for l in open(fn):
            w = l.rstrip('\n').split('\t')
            if w[0] == 'file': continue
            sets, vals = json.loads(w[4]), json.loads(w[6])
            d = {'sets': sets, 'm': int(w[3]), 'vals': vals, 'id': '%s#%s:%s' % (w[0], w[1], w[5])}
            out.append(d)
            for B in json.loads(w[8]): fails.append((len(out) - 1, tuple(tuple(sorted(b)) for b in B)))
    return out, fails


def random_items(files, opt, log):
    """random (core, profile) draws from the files in turn, screened by dlrt4.c: profiles with an f >= 1 state (until
    --states=N states) and --neg=K profiles without one"""
    rng = random.Random(int(opt.get('seed', 1)))
    want = int(opt.get('states', 2000)); neg = int(opt.get('neg', 300))
    brt, _ = build(os.path.join(HERE, 'dlrt4.c'))
    data = [(os.path.basename(f).replace('.json.gz', ''), json.load(gzip.open(f, 'rt'))['cores']) for f in files]
    doms = {}
    pos, negs, nst, drawn = [], [], 0, 0
    fi = 0
    while nst < want:
        batch = []
        for _ in range(2000):
            base, cores = data[fi % len(data)]; fi += 1
            k = rng.randrange(len(cores)); c = cores[k]
            if (base, k) not in doms: doms[(base, k)] = check4.core_domains(c['sets'], c['m'], False)
            D = doms[(base, k)]
            ts = [rng.randrange(len(x)) for x in D]
            batch.append({'sets': c['sets'], 'm': c['m'], 'vals': [[D[i][ts[i]][g] for g in c['sets'][i]] for i in range(len(c['sets']))],
                          'id': '%s#%d[m=%d,idx=%d]:%s' % (base, k, c['m'], c.get('idx', k), ','.join(map(str, ts)))})
        drawn += len(batch)
        out = subprocess.run([brt, '-s'], input=''.join(block(d, j) for j, d in enumerate(batch)), capture_output=True,
                             text=True, check=True).stdout
        for d, (_, _, Cs) in zip(batch, c_parse(out, [d['sets'] for d in batch])):
            n1 = sum(1 for s in Cs.values() if s['f'] >= 1)
            if n1 and nst < want: pos.append(d); nst += n1
            elif not n1 and len(negs) < neg: negs.append(d)
    log('# random: %d profiles drawn, %d with an f >= 1 state (%d such states), %d without one kept' % (drawn, len(pos), nst, len(negs)))
    return pos + negs


def records_items(files, opt):
    """the distinct profiles of dlrt4_run.py / dlrt4_nbhd.py dump records whose state has no T1 or T3 move (DL_RT4 needs
    T2 or T4 there, or fails); with --allrec, of every record"""
    seen = collections.OrderedDict()
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            if 'core' not in r or 'vals' not in r: continue
            brs = r['br'].split('+')
            if 'allrec' not in opt and any(b in ('T1', 'T3p', 'T3h') for b in brs): continue
            c = r['core']
            key = json.dumps([c['sets'], r['vals']])
            if key not in seen:
                seen[key] = {'sets': c['sets'], 'm': c['m'], 'vals': r['vals'],
                             'id': '%s#%s:%s' % (c.get('file', c.get('id')), c.get('pos', ''), ','.join(map(str, r.get('prof', []))))}
    return list(seen.values())


def main(argv):
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    log = lambda s: print(s, flush=True)
    log('# command: python3 k4/dlrt4_ref.py ' + ' '.join(argv))
    if mode == 'write-tsv-inst':
        items, fails = tsv_items(rest[1:])
        json.dump(items, open(rest[0], 'w'))
        log('# wrote %d profiles (%d failing states) to %s' % (len(items), len(fails), rest[0])); return
    fails = []
    if mode == 'suite':
        insts = [dict(d, id=src) for d, src in DR.items_of('suite', [], {'nmax': opt.get('maxn', 6)}) if not rest or src in rest]
    elif mode == 'tsv':
        insts, fails = tsv_items(rest)
    elif mode == 'random':
        insts = random_items(rest, opt, log)
    elif mode == 'records':
        insts = records_items(rest, opt)
    elif mode == 'inst':
        insts = json.load(open(rest[0]))
        for d in insts: d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
    else:
        print(__doc__); return
    if 'every' in opt: insts = insts[::int(opt['every'])]
    stats = collections.Counter()
    sha = compare(insts, opt, stats, log)
    log('# dlrt4.c sha256 %s' % sha)
    if fails:                         # every listed failing state is a state of its profile (dlrt4.c, -s)
        brt, _ = build(os.path.join(HERE, 'dlrt4.c'))
        found = 0
        for c0 in range(0, len(insts), 200):
            chunk = insts[c0:c0 + 200]
            out = subprocess.run([brt, '-s'], input=''.join(block(d, k) for k, d in enumerate(chunk)), capture_output=True,
                                 text=True, check=True).stdout
            C = c_parse(out, [d['sets'] for d in chunk])
            for j, Bs in fails:
                if c0 <= j < c0 + 200:
                    s = C[j - c0][2].get(Bs)
                    if s is None: stats['fails_missing'] += 1; log('MISSING listed failing state %s %s' % (insts[j]['id'], Bs))
                    else:
                        found += 1
                        if not (s['t1'] or s['t3p'] or s['t3h']): stats['fails_r13_confirmed'] += 1
                        if not (s['t1'] or s['t2'] or s['t3p'] or s['t3h'] or s['t4']): stats['fails_rt4'] += 1
        log('# listed failing states: %d, found as states %d, R_13 fails there (dlrt4.c) %d, DL_RT4 fails there %d'
            % (len(fails), found, stats['fails_r13_confirmed'], stats['fails_rt4']))
    log('profiles %d (with a def > 0 state %d, with an f >= 1 state %d); states %d (f = 0: %d, f >= 1: %d); DL_RT4 '
        'failures f >= 1: %d, RT4 failures f = 0: %d' % (stats['prof'], stats['prof_pos'], stats['prof_f1'], stats['st'],
                                                         stats['st_f0'], stats['st_f1'], stats['fail_f1'], stats['fail_f0']))
    log('f >= 1 states with an improving move: T1 %d, T2 %d, T3p %d, T3h %d, T4 %d; only T4 %d, only T2 %d'
        % (stats['f1_t1'], stats['f1_t2'], stats['f1_t3p'], stats['f1_t3h'], stats['f1_t4'], stats['f1_t4only'],
           stats['f1_t2only']))
    log('mismatches: reference (model.py + dl2_relations.py + own T4) %d, reference assertions %d, dl13.c (K line and '
        'T1/T3 per state) %d + %d, -DBIGPP=0 build %d, xcheck (dl134_xcheck.py, %d states) %s'
        % (stats['mm_ref'], stats['assert'], stats['mm_K'], stats['mm_13'], stats['mm_hash'], stats['st_x'],
           stats['mm_x'] if 'x' in opt else '-'))


if __name__ == '__main__':
    main(sys.argv[1:])
