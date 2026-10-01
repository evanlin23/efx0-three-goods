#!/usr/bin/env python3
"""Cross-checks of k4/dl13.c (compute/k4-dl13; Conjecture DL13, k4/dl2.md §3, ledger K4.DL2.T13). EVIDENCE tooling.

For a list of single profiles, compares per state (min-frozen P with def(P) > 0):
  (a) k4/dl13.c against k4/dl2_relations.py on k4/suite/model.py (the proof workstream's implementation): the set of
      states (bases), def, the nearest distance k, DL13 at P (relation R13), and the branches t1 / t3p / t3h, with the
      move types where the shapes of dl2_relations.py determine them (T1: release or not; T3: x's source and the
      helper's kind);
  (b) for n <= 4, k4/dl13.c against main's k4/c4x_check.py (its own 𝒫 and deficit `rodef`) with the membership tests
      of k4/dl2_relations_xcheck.py (rel_B; t1 = one agent changes and NA is kept, t3p / t3h = rel_B 'R13' with two /
      three agents changed): the states, def, k, DL13, t1, t3p, t3h;
  (c) dl13.c's "K" line against k4/dl2.c's on the same input (dl13.c keeps dl2.c's code for these counters);
  (d) dl13.c built with -DBIGPP=0 (candidates by hashing, R_13 moves generated) against the default build (every P
      scanned): the whole output must be identical.

usage: python3 k4/dl13_check.py suite [--maxn=N]
       python3 k4/dl13_check.py certs FILE [--rand=K] [--seed=S] [--cores=A:B]    (K random profiles per core)
       python3 k4/dl13_check.py catalog FILE [--every=E] [--max=N]
options: --no-model (skip (a)), --no-x (skip (b)), --fge1 (count only profiles with f >= 1 towards --want), --want=W
(stop after W profiles with a def > 0 state, after the shuffle of --rand)"""
import gzip, hashlib, json, os, random, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import dl2_relations as DR
from dl2_relations_xcheck import rel_B, states_B

TMP = tempfile.gettempdir()


def build(src, extra=()):
    sha = hashlib.sha256(open(src, 'rb').read()).hexdigest()
    b = os.path.join(TMP, 'k4chk_' + os.path.basename(src).replace('.c', '') + '_' + sha[:16] + ''.join(e.replace('=', '') for e in extra))
    if not os.path.exists(b):
        subprocess.run(['gcc', '-O2'] + list(extra) + ['-o', b + '.tmp', src], check=True); os.replace(b + '.tmp', b)
    return b, sha


def block(d, tag):
    out = [f"{len(d['sets'])} {d['m']} {tag}"] + [f"{len(S)} {' '.join(map(str, S))}" for S in d['sets']]
    out.append(' '.join('1' for _ in d['sets']))
    out += [' '.join(map(str, V)) for V in d['vals']]
    out.append('0')
    return '\n'.join(out) + '\n'


def c_states(out, sets):
    """dl13.c -s output -> per block: (K line, L line, {bases: state})"""
    res, cur = [], {}
    for l in out.splitlines():
        w = l.split()
        if w[0] == 'S':
            n = len(sets[len(res)])
            f = int(w[1]); Bs = tuple(tuple(g for g in range(64) if int(b) >> g & 1) for b in w[2:2 + n])
            x = list(map(int, w[2 + n:2 + n + 11]))
            cur[Bs] = {'f': f, 'def': x[0], 'k': None if x[1] == 99 else x[1], 'rd': x[2], 't1': x[3], 't3p': x[4],
                       't3h': x[5], 't1m': x[6], 't3m': x[7], 'sig': w[-1]}
        elif w[0] == 'K': res.append([l, None, cur]); cur = {}
        elif w[0] == 'L': res[-1][1] = l
    return res


XS = {'J': 0, 'JZ': 1, 'other': 2}
HK = {'rel1': 1, 'rel': 1, 'junk': 2, 'trade': 3}


def model_states(d):
    """dl2_relations.py (model.py): per state def, k, R13, t1, t3p, t3h, T1 release-type flag, T3 type mask"""
    out = {}
    for r in DR.profile(d):
        sh = r['shapes']
        t1 = [s for s in sh if DR._one(s, nt_ok=False)]
        t3 = [s for s in sh if DR._swap(s, 1, gives=True)]
        t3m = 0
        for s in t3: t3m |= 1 << (4 * XS[s['xsrc']] + (HK[s['Y'][0]] if s['Y'] else 0))
        out[tuple(tuple(B) for B in r['Bs'])] = {
            'def': 999999 if r['def'] == DR.INF else r['def'], 'k': r['k'], 'R13': r['holds']['R13'], 't1': int(bool(t1)),
            't3p': int(any(not s['Y'] for s in t3)), 't3h': int(any(s['Y'] for s in t3)),
            't1rel': int(any(s['Y'][0] in ('rel', 'rel1') for s in t1)), 't3m': t3m, 'f': r['f']}
    return out


def x_states(d):
    """main's c4x_check.py + dl2_relations_xcheck.rel_B: per state def, k, R13, t1, t3p, t3h"""
    sets, vals, m = d['sets'], d['vals'], d['m']
    import c4x_check as CX
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    res = CX.analyse(sets, m, vl)
    mf = max(r[2]['-frozen'] for r in res)
    mp = [(tuple(frozenset(B) for B in r[0]), r[2]['rodef']) for r in res if r[2]['-frozen'] == mf]
    val = lambda i, B: sum(vl[i].get(g, 0) for g in B)
    nd = lambda i, B: frozenset(g for g in vl[i] if g not in B and vl[i][g] > val(i, B))
    out = {}
    for P, dv in mp:
        if dv <= 0: continue
        better = [P2 for P2, d2 in mp if d2 < dv]
        k = min((sum(1 for a, b in zip(P, P2) if a != b) for P2 in better), default=None)
        t1 = t3p = t3h = 0
        for P2 in better:
            ch = [i for i in range(len(P)) if P[i] != P2[i]]
            if len(ch) == 1:
                NA1 = frozenset().union(*[nd(i, P[i]) for i in range(len(P))])
                NA2 = frozenset().union(*[nd(i, P2[i]) for i in range(len(P))])
                if NA1 == NA2: t1 = 1
            elif rel_B('R13', sets, vals, P, P2):
                if len(ch) == 2: t3p = 1
                else: t3h = 1
        out[tuple(tuple(sorted(B)) for B in P)] = {'def': 999999 if dv == float('inf') else dv, 'k': k,
                                                   'R13': bool(t1 or t3p or t3h), 't1': t1, 't3p': t3p, 't3h': t3h}
    return out


def items(mode, rest, opt):
    if mode == 'suite':
        out = []
        for d, src in DR.items_of('suite', [], {'nmax': opt.get('maxn', 6)}):
            out.append(dict(d, id=src))
        return out
    if mode == 'certs':
        data = json.load(gzip.open(rest[0], 'rt'))
        rng = random.Random(int(opt.get('seed', 1)))
        base = os.path.basename(rest[0]).replace('.json.gz', '')
        cores = data['cores']
        lo, hi = 0, len(cores)
        if 'cores' in opt: a, b = opt['cores'].split(':'); lo, hi = int(a or 0), int(b or len(cores))
        out = []
        for core in cores[lo:hi]:
            sets, m = core['sets'], core['m']
            doms = check4.core_domains(sets, m, False)
            for _ in range(int(opt.get('rand', 10))):
                ts = [rng.randrange(len(D)) for D in doms]
                out.append({'sets': sets, 'm': m, 'vals': [[doms[i][ts[i]][g] for g in sets[i]] for i in range(len(sets))],
                            'id': '%s[m=%d,idx=%d]:%s' % (base, m, core['idx'], ','.join(map(str, ts)))})
        return out
    out = []
    for d, src in DR.items_of('catalog', rest, opt):
        out.append(dict(d, id=src))
    return out


def main(argv):
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/dl13_check.py ' + ' '.join(argv), flush=True)
    b13, sha13 = build(os.path.join(HERE, 'dl13.c'))
    b13h, _ = build(os.path.join(HERE, 'dl13.c'), ('-DBIGPP=0',))
    b2, sha2 = build(os.path.join(HERE, 'dl2.c'))
    print(f'# dl13.c sha256 {sha13}; dl2.c sha256 {sha2}', flush=True)
    insts = items(mode, rest, opt)
    want = int(opt.get('want', 0))
    stats = dict(prof=0, prof_pos=0, prof_f1=0, st=0, st_f0=0, st_f1=0, st_x=0, mm_model=0, mm_x=0, mm_K=0, mm_hash=0,
                 fail_f1=0, fail_f0=0)
    CH = 200
    for c0 in range(0, len(insts), CH):
        chunk = insts[c0:c0 + CH]
        inp = ''.join(block(d, k) for k, d in enumerate(chunk))
        o13 = subprocess.run([b13, '-s'], input=inp, capture_output=True, text=True, check=True).stdout
        o13h = subprocess.run([b13h, '-s'], input=inp, capture_output=True, text=True, check=True).stdout
        o2 = subprocess.run([b2], input=inp, capture_output=True, text=True, check=True).stdout
        if o13 != o13h:
            stats['mm_hash'] += 1; print('MISMATCH hash build, chunk at', c0, flush=True)
        K2 = [l for l in o2.splitlines() if l.startswith('K ')]
        res = c_states(o13, [d['sets'] for d in chunk])
        if len(res) != len(chunk) or [r[0] for r in res] != K2:
            stats['mm_K'] += 1; print('MISMATCH K lines vs dl2.c, chunk at', c0, flush=True)
        for d, (_, _, C) in zip(chunk, res):
            stats['prof'] += 1
            if C: stats['prof_pos'] += 1
            if C and next(iter(C.values()))['f'] >= 1: stats['prof_f1'] += 1
            for Bs, s in C.items():
                stats['st'] += 1; stats['st_f0' if s['f'] == 0 else 'st_f1'] += 1
                if not (s['t1'] or s['t3p'] or s['t3h']): stats['fail_f0' if s['f'] == 0 else 'fail_f1'] += 1
            if 'no-model' not in opt:
                M = model_states(d)
                if set(M) != set(C):
                    stats['mm_model'] += 1; print('MISMATCH model states', d['id'], sorted(set(M) ^ set(C))[:3], flush=True)
                else:
                    for Bs, s in C.items():
                        a = M[Bs]
                        t1rel = int(bool(s['t1m'] & 1))
                        if (a['def'] != s['def'] or a['k'] != s['k'] or a['R13'] != bool(s['t1'] or s['t3p'] or s['t3h'])
                                or (a['t1'], a['t3p'], a['t3h']) != (s['t1'], s['t3p'], s['t3h']) or a['t1rel'] != t1rel
                                or a['t3m'] != s['t3m'] or a['f'] != s['f']):
                            stats['mm_model'] += 1
                            print('MISMATCH model', d['id'], Bs, 'C', s, 'model', a, flush=True)
            if 'no-x' not in opt and len(d['sets']) <= 4:
                X = x_states(d)
                if set(X) != set(C):
                    stats['mm_x'] += 1; print('MISMATCH xcheck states', d['id'], sorted(set(X) ^ set(C))[:3], flush=True)
                else:
                    for Bs, s in C.items():
                        stats['st_x'] += 1
                        a = X[Bs]
                        if (a['def'] != s['def'] or a['k'] != s['k'] or a['R13'] != bool(s['t1'] or s['t3p'] or s['t3h'])
                                or (a['t1'], a['t3p'], a['t3h']) != (s['t1'], s['t3p'], s['t3h'])):
                            stats['mm_x'] += 1
                            print('MISMATCH xcheck', d['id'], Bs, 'C', s, 'x', a, flush=True)
        print('#  %d / %d profiles: %s' % (min(c0 + CH, len(insts)), len(insts), stats), flush=True)
        if want and stats['prof_f1' if 'fge1' in opt else 'prof_pos'] >= want: break
    print('profiles %d (with a def > 0 state %d, with f >= 1 and a def > 0 state %d); states %d (f = 0: %d, f >= 1: %d); '
          'DL13 failures f >= 1: %d, R_13 failures f = 0: %d' % (stats['prof'], stats['prof_pos'], stats['prof_f1'],
                                                               stats['st'], stats['st_f0'], stats['st_f1'],
                                                               stats['fail_f1'], stats['fail_f0']))
    print('mismatches: model (dl2_relations.py) %s, xcheck (c4x_check.py, %d states with n <= 4) %s, K line vs dl2.c %d, '
          'hash build %d' % ('-' if 'no-model' in opt else stats['mm_model'], stats['st_x'],
                             '-' if 'no-x' in opt else stats['mm_x'], stats['mm_K'], stats['mm_hash']), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
