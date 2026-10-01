#!/usr/bin/env python3
"""An independent Python reference for k4/dl134.c (compute/k4-dl134; Conjecture DL134 = DL13 of k4/dl2.md §3 with the
frozen permutations T4 added), and its comparison with dl134.c. EVIDENCE tooling.

The reference (ref_states) shares no code with dl134.c:
  - 𝒫, the min-frozen class and def(P): k4/suite/model.py (Inst.preallocs, Inst.deficit);
  - T1 and T3: k4/dl2_relations.py as a library (shape(); T1 = _one(s, nt_ok=False), T3 = _swap(s, 1, gives=True),
    i.e. its relation "R13"); the T3 type from the shape (x's source, the helper's kind), as k4/dl13_check.py does;
  - T4: t4_cycle below, written here from the definition of the brief: a permutation pi of the frozen agents' singleton
    bases among the frozen agents; each frozen agent i takes the base of pi(i); every one of them stays frozen in P'
    (its singleton base lies in NA'); NA' = NA; all other bases are unchanged; any cycle structure (pi is not the
    identity, since P' != P).
Per state (min-frozen P with def(P) > 0) it gives f, def, the nearest distance k of a better min-frozen P', the nearest
distance of an improving R_13 move and of an improving R_134 move, the flags t1 / t3p / t3h / t4, the T1 type mask (rel,
grow, pool: computed here from the bases), the T3 type mask, the set of T4 cycle types, and the least def(P') reached by
each kind (dT1, dT3, dT4).

The comparison (main) runs, on a list of single profiles, chunk by chunk:
  (a) dl134.c -s -q1 against the reference: the set of states and every field above, per state;
  (b) dl134.c against dl134.c built with -DBIGPP=0 (candidates generated and looked up in a hash, T4 by the bijections
      of the frozen agents onto their goods): the whole output must be identical;
  (c) dl134.c's "K" line against k4/dl2.c's and its "L" line against k4/dl13.c's on the same input (both unchanged).

usage: python3 k4/dl134_ref.py suite [--maxn=N]
       python3 k4/dl134_ref.py tsv FILE.tsv...                      (results/k4_dl13/n4_failures_*.tsv; also checks
                                                                     that every listed state is there and fails R_13)
       python3 k4/dl134_ref.py rand FILE... --want=W [--seed=S] [--per=R] [--plain=U]
                (cores of certificate files: R random profiles per core (default 400) are screened with dl134.c, and
                 profiles with an f >= 1 state with def > 0 are taken in a seeded random order until W such states
                 are compared; also U profiles drawn without screening (default 300), compared whole)
common: [--jobs=J]"""
import csv, gzip, hashlib, json, os, random, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc
import dl2_relations as DR

TMP = tempfile.gettempdir()
INF = 999999
CYCNAME = ["2", "3", "4", "2+2", "5", "3+2", "6", "4+2", "3+3", "2+2+2", "7", "5+2", "4+3", "3+2+2", "8", "6+2", "5+3",
           "4+4", "4+2+2", "3+3+2", "2+2+2+2"]                 # the names dl134.c gives (anything else: "other")
XS = {'J': 0, 'JZ': 1, 'other': 2}
HK = {'rel1': 1, 'rel': 1, 'junk': 2, 'trade': 3}


# ------------------------------------------------------------------------------------------------ the reference
def t4_cycle(I, Bs, Bs2):
    """(T4) from its definition: None, or the cycle type of pi (cycle lengths >= 2, decreasing, joined by '+')"""
    n = I.n
    NA = 0; NA2 = 0
    for i in range(n):
        NA |= I.needs(i, Bs[i]); NA2 |= I.needs(i, Bs2[i])
    if NA != NA2: return None                                       # NA' = NA
    frozen = [i for i in range(n) if pc(Bs[i]) == 1 and Bs[i] & NA]
    if any(Bs2[i] != Bs[i] for i in range(n) if i not in frozen): return None    # all other bases unchanged
    pi = {}
    for i in frozen:                                                # B'_i = B_{pi(i)} with pi(i) frozen
        js = [j for j in frozen if Bs[j] == Bs2[i]]
        if len(js) != 1: return None
        pi[i] = js[0]
    if sorted(pi.values()) != sorted(frozen): return None          # pi is a permutation of the frozen agents
    if any(not (pc(Bs2[i]) == 1 and Bs2[i] & NA2) for i in frozen): return None   # every one stays frozen
    if all(pi[i] == i for i in frozen): return None                # P' = P
    lens, seen = [], set()
    for i in frozen:
        if i in seen: continue
        l, j = 0, i
        while j not in seen: seen.add(j); l += 1; j = pi[j]
        if l >= 2: lens.append(l)
    nm = '+'.join(map(str, sorted(lens, reverse=True)))
    return nm if nm in CYCNAME else 'other'


def t1_type(B, B2):
    """dl134.c's T1 types: 0 rel (B' strictly inside B), 1 grow (B strictly inside B'), 2 pool (otherwise)"""
    if B2 != B and B2 & B == B2: return 0
    if B2 != B and B2 & B == B: return 1
    return 2


def ref_states(d):
    """{bases (tuple of sorted tuples): fields} for every min-frozen P with def(P) > 0 of the profile d"""
    I = M.Inst(d['sets'], d['vals'], d.get('m'))
    I.preallocs()
    if I.omega <= 0: return {}
    mp = [Bs for Bs, NA in I.minP]
    D = {}
    for Bs in mp:
        x = I.deficit(Bs); D[Bs] = INF if x is None else x
    PAs = {Bs: DR.PA(I, Bs) for Bs in mp}
    out = {}
    for Bs in mp:
        if D[Bs] <= 0: continue
        r = {'f': I.f, 'def': D[Bs], 'k': 99, 'r13d': 99, 'rd': 99, 't1': 0, 't3p': 0, 't3h': 0, 't4': 0, 't1m': 0,
             't3m': 0, 't4types': set(), 'dT1': INF, 'dT3': INF, 'dT4': INF, 'overlap': 0}
        for B2 in mp:
            if D[B2] >= D[Bs]: continue
            dist = sum(1 for a, b in zip(Bs, B2) if a != b)
            r['k'] = min(r['k'], dist)
            s = DR.shape(PAs[Bs], PAs[B2])
            is1, is3, cy = DR._one(s, nt_ok=False), DR._swap(s, 1, gives=True), t4_cycle(I, Bs, B2)
            if is1 + is3 + (cy is not None) > 1: r['overlap'] += 1          # the kinds are disjoint (dl134.c's header)
            if is1:
                y = next(i for i in range(I.n) if Bs[i] != B2[i])
                r['t1'] = 1; r['t1m'] |= 1 << t1_type(Bs[y], B2[y]); r['dT1'] = min(r['dT1'], D[B2])
                r['r13d'] = min(r['r13d'], dist); r['rd'] = min(r['rd'], dist)
            elif is3:
                r['t3h' if s['Y'] else 't3p'] = 1
                r['t3m'] |= 1 << (4 * XS[s['xsrc']] + (HK[s['Y'][0]] if s['Y'] else 0))
                r['dT3'] = min(r['dT3'], D[B2]); r['r13d'] = min(r['r13d'], dist); r['rd'] = min(r['rd'], dist)
            elif cy is not None:
                r['t4'] = 1; r['t4types'].add(cy); r['dT4'] = min(r['dT4'], D[B2]); r['rd'] = min(r['rd'], dist)
        out[tuple(tuple(sorted(bits(B))) for B in Bs)] = r
    return out


def ref_one(d):
    return ref_states(d)


# ------------------------------------------------------------------------------------------------ dl134.c
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


SF = 'def k r13d rd t1 t3p t3h t4 t1m t3m t4m dT1 dT3 dT4 pm'.split()


def c_states(out, sets):
    """dl134.c -s output -> per block: [K line, L line, M line, {bases: state}]"""
    res, cur = [], {}
    for l in out.splitlines():
        w = l.split()
        if w[0] == 'S':
            n = len(sets[len(res)])
            Bs = tuple(tuple(g for g in range(64) if int(b) >> g & 1) for b in w[2:2 + n])
            r = {'f': int(w[1])}
            r.update(zip(SF, map(int, w[2 + n:2 + n + len(SF)])))
            nm = CYCNAME + ['other']
            r['t4types'] = {nm[c] for c in range(len(nm)) if r['t4m'] >> c & 1}
            cur[Bs] = r
        elif w[0] == 'K': res.append([l, None, None, cur]); cur = {}
        elif w[0] == 'L': res[-1][1] = l
        elif w[0] == 'M': res[-1][2] = l
    return res


CMP = ['f', 'def', 'k', 'r13d', 'rd', 't1', 't3p', 't3h', 't4', 't1m', 't3m', 't4types', 'dT1', 'dT3', 'dT4']


def compare(insts, jobs, tag, listed=None):
    """the comparisons (a), (b), (c) on single profiles; listed: {inst index: [failing bases]} (tsv mode)"""
    b134, sha134 = build(os.path.join(HERE, 'dl134.c'))
    b134h, _ = build(os.path.join(HERE, 'dl134.c'), ('-DBIGPP=0',))
    b13, sha13 = build(os.path.join(HERE, 'dl13.c'))
    b2, sha2 = build(os.path.join(HERE, 'dl2.c'))
    print(f'# {tag}: dl134.c sha256 {sha134}; dl13.c sha256 {sha13}; dl2.c sha256 {sha2}', flush=True)
    st = dict(prof=0, prof_pos=0, prof_f1=0, st=0, st_f0=0, st_f1=0, fail134_f1=0, fail13_f1=0, t4only=0, t4only2=0,
              st_t4=0, st_t4long=0,
              mm_ref=0, mm_K=0, mm_L=0, mm_hash=0, listed=0, listed_bad=0)
    t0 = time.time()
    CH = 200
    pool = Pool(jobs) if jobs > 1 else None
    for c0 in range(0, len(insts), CH):
        chunk = insts[c0:c0 + CH]
        inp = ''.join(block(d, k) for k, d in enumerate(chunk))
        o134 = subprocess.run([b134, '-s', '-q1'], input=inp, capture_output=True, text=True, check=True).stdout
        o134h = subprocess.run([b134h, '-s', '-q1'], input=inp, capture_output=True, text=True, check=True).stdout
        o13 = subprocess.run([b13], input=inp, capture_output=True, text=True, check=True).stdout
        o2 = subprocess.run([b2], input=inp, capture_output=True, text=True, check=True).stdout
        if o134 != o134h:
            st['mm_hash'] += 1; print('MISMATCH hash build, chunk at', c0, flush=True)
        res = c_states(o134, [d['sets'] for d in chunk])
        K2 = [l for l in o2.splitlines() if l.startswith('K ')]
        L13 = [l for l in o13.splitlines() if l.startswith('L ')]
        if len(res) != len(chunk) or [r[0] for r in res] != K2:
            st['mm_K'] += 1; print('MISMATCH K lines vs dl2.c, chunk at', c0, flush=True)
        if [r[1] for r in res] != L13:
            st['mm_L'] += 1; print('MISMATCH L lines vs dl13.c, chunk at', c0, flush=True)
        refs = pool.map(ref_one, chunk, chunksize=2) if pool else list(map(ref_one, chunk))
        for k, (d, (_, _, _, C), R) in enumerate(zip(chunk, res, refs)):
            st['prof'] += 1
            if C: st['prof_pos'] += 1
            if C and next(iter(C.values()))['f'] >= 1: st['prof_f1'] += 1
            for Bs, s in C.items():
                st['st'] += 1; st['st_f0' if s['f'] == 0 else 'st_f1'] += 1
                st['st_t4'] += s['t4']; st['st_t4long'] += bool(s['t4types'] - {'2'})
                if s['f'] >= 1:
                    ok13 = s['t1'] or s['t3p'] or s['t3h']
                    if not ok13: st['fail13_f1'] += 1
                    if not (ok13 or s['t4']): st['fail134_f1'] += 1
                    if s['t4'] and not ok13: st['t4only'] += 1; st['t4only2'] += '2' in s['t4types']
            if set(R) != set(C):
                st['mm_ref'] += 1; print('MISMATCH ref states', d['id'], sorted(set(R) ^ set(C))[:3], flush=True)
            else:
                for Bs, s in C.items():
                    a = R[Bs]
                    if any(a[x] != s[x] for x in CMP) or a['overlap']:
                        st['mm_ref'] += 1
                        print('MISMATCH ref', d['id'], Bs, {x: (s[x], a[x]) for x in CMP if a[x] != s[x]}, 'overlap',
                              a['overlap'], flush=True)
            if listed is not None:
                for B in listed[c0 + k]:
                    st['listed'] += 1
                    Bt = tuple(tuple(sorted(x)) for x in B)
                    s, a = C.get(Bt), R.get(Bt)
                    if s is None or a is None or s['f'] < 1 or s['t1'] or s['t3p'] or s['t3h'] or a['t1'] or a['t3p'] or a['t3h']:
                        st['listed_bad'] += 1; print('LISTED STATE NOT A DL13 FAILURE', d['id'], B, flush=True)
        print('#  %d / %d profiles [%.0f s]: %s' % (min(c0 + CH, len(insts)), len(insts), time.time() - t0, st), flush=True)
    if pool: pool.close()
    print(f'{tag}: profiles {st["prof"]} (with a def > 0 state {st["prof_pos"]}, with f >= 1 and a def > 0 state '
          f'{st["prof_f1"]}); states {st["st"]} (f = 0: {st["st_f0"]}, f >= 1: {st["st_f1"]}); DL13 fails at '
          f'{st["fail13_f1"]} f >= 1 states, DL134 at {st["fail134_f1"]}; repaired by T4 only {st["t4only"]} (with a '
          f'2-swap {st["t4only2"]}); states with an improving T4 move {st["st_t4"]} (with one that is not a single '
          f'2-swap {st["st_t4long"]})' + (f'; listed failing states {st["listed"]}, not DL13 failures {st["listed_bad"]}'
                                       if listed is not None else ''), flush=True)
    print(f'{tag}: mismatches: reference {st["mm_ref"]}, K line vs dl2.c {st["mm_K"]}, L line vs dl13.c {st["mm_L"]}, '
          f'hash build {st["mm_hash"]} [{time.time() - t0:.0f} s]', flush=True)
    return st


# ------------------------------------------------------------------------------------------------ inputs
def screen(files, per, seed):
    """R random profiles per core of each file (repeats dropped), screened with dl134.c: [(instance, f >= 1 states)] for
    the profiles with an f >= 1 state"""
    import check4
    b134, _ = build(os.path.join(HERE, 'dl134.c'))
    rng = random.Random(seed)
    out = []
    for f in files:
        cores = json.load(gzip.open(f, 'rt'))['cores']
        base = os.path.basename(f).replace('.json.gz', '')
        for pos, c in enumerate(cores):
            sets, m = c['sets'], c['m']
            doms = check4.core_domains(sets, m, False)
            profs = sorted(set(tuple(rng.randrange(len(D)) for D in doms) for _ in range(per)))
            inp = [f"{len(sets)} {m} {pos}"] + [f"{len(S)} {' '.join(map(str, S))}" for S in sets]
            inp.append(' '.join(str(len(D)) for D in doms))
            for S, D in zip(sets, doms): inp += [' '.join(str(dd[g]) for g in S) for dd in D]
            inp.append(str(-len(profs))); inp += [' '.join(map(str, p)) for p in profs]
            o = subprocess.run([b134, '-s'], input='\n'.join(inp) + '\n', capture_output=True, text=True, check=True).stdout
            cur, cnt = None, 0

            def flush():
                if cur is not None and cnt:
                    vals = [[doms[i][cur[i]][g] for g in sets[i]] for i in range(len(sets))]
                    out.append(({'sets': sets, 'm': m, 'vals': vals,
                                 'id': '%s#%d[m=%d,idx=%d]:%s' % (base, pos, m, c['idx'], ','.join(map(str, cur)))}, cnt))
            for l in o.splitlines():
                if l.startswith('V '):
                    flush(); cur, cnt = list(map(int, l.split()[2:2 + len(sets)])), 0
                elif l.startswith('S ') and int(l.split()[1]) >= 1: cnt += 1
            flush()
    return out


def plain(files, U, seed):
    """U profiles: a random core of a random file, a random profile"""
    import check4
    rng = random.Random(seed + 1000)
    data = [(os.path.basename(f).replace('.json.gz', ''), json.load(gzip.open(f, 'rt'))['cores']) for f in files]
    out = []
    for _ in range(U):
        base, cores = data[rng.randrange(len(data))]
        pos = rng.randrange(len(cores)); c = cores[pos]
        doms = check4.core_domains(c['sets'], c['m'], False)
        p = [rng.randrange(len(D)) for D in doms]
        out.append({'sets': c['sets'], 'm': c['m'], 'vals': [[doms[i][p[i]][g] for g in c['sets'][i]] for i in range(len(p))],
                    'id': '%s#%d[m=%d,idx=%d]:%s' % (base, pos, c['m'], c['idx'], ','.join(map(str, p)))})
    return out


def main(argv):
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[1:] if a.startswith('--'))
    print('# command: python3 k4/dl134_ref.py ' + ' '.join(argv), flush=True)
    jobs = int(opt.get('jobs', 1))
    if mode == 'suite':
        insts = [dict(d, id=src) for d, src in DR.items_of('suite', [], {'nmax': opt.get('maxn', 6)})]
        compare(insts, jobs, 'suite')
    elif mode == 'tsv':
        insts, listed = [], {}
        for fn in rest:
            for row in csv.DictReader(open(fn), delimiter='\t'):
                listed[len(insts)] = json.loads(row['bases'])
                insts.append({'sets': json.loads(row['sets']), 'm': int(row['m']), 'vals': json.loads(row['vals']),
                              'id': f"{row['file']}#{row['pos']}:{row['profile']}"})
        compare(insts, jobs, 'tsv', listed)
    elif mode == 'rand':
        want, seed = int(opt['want']), int(opt.get('seed', 1))
        t0 = time.time()
        cand = screen(rest, int(opt.get('per', 400)), seed)
        random.Random(seed).shuffle(cand)
        insts, tot = [], 0
        for d, c in cand:
            if tot >= want: break
            insts.append(d); tot += c
        print(f'# screened: {len(cand)} profiles with an f >= 1 state with def > 0; taken {len(insts)} with {tot} such '
              f'states [{time.time() - t0:.0f} s]', flush=True)
        if tot < want: print(f'# WARNING: only {tot} states available, fewer than --want={want}', flush=True)
        compare(insts, jobs, 'rand (screened, f >= 1)')
        U = int(opt.get('plain', 300))
        if U: compare(plain(rest, U, seed), jobs, 'rand (plain)')
    else:
        print(__doc__)


if __name__ == '__main__':
    main(sys.argv[1:])
