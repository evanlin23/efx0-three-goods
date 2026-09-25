"""Independent re-check of the k = 4 reduction certificates (k4/MINCEX.md; written by k4/mincex4.py with k4/reduce4.py).

Shares no code with reduce4.py / mincex4.py:
  1. types are re-enumerated here from the grid [1, 16]^d: a type is the sign vector of v(S) - v(T) over unordered
     pairs of disjoint nonempty S, T; strict = no zero sign, balanced = top < sum of the others (288 for d = 4, 6 for
     d = 3). Each type is represented by its LAST grid point (the generator uses small representatives), so agreement
     also tests that safety depends only on the type;
  2. local states of Y are enumerated as maps from the local goods to labels (gadget agents, outside blocks 0..k-1),
     reduced to restricted-growth form, then given marker flags and (with 'source') the unenvied bundle;
  3. safety is the raw EFX0 definition written as v(own) >= v(B) - v(g) for every other bundle B and every g in B;
  4. the gadget must be a legal reduction: smaller (fewer agents, or as many and fewer goods), each gadget agent values
     at most 4 goods, all in I' + D, and H' stays in the class C_k whenever H does (every way the rest of the
     instance can connect the boundary goods, as in tools/check_reductions.py);
  5. every stored extension is checked against Lemma M1 / M1(b): goods conserved, outside bundles keep their goods
     outside I', moved items (boundary goods and outside goods of gadget agents) go to agents of S or to outside
     bundles made of gadget goods only, every new or modified bundle dominated (or, with 'source', made outside I and
     I' of goods of the unenvied bundle).
A profile of a record is covered when every state admissible for it (gadget agents safe, none envying the unenvied
bundle) has a stored extension under which every agent of S is safe. Per configuration the covered profiles of its
records are united.
Usage: check_reductions4.py certs.json.gz [--jobs=J] [--expect=CONFIG:COUNT ...] [--fail-out=fail.json]
       check_reductions4.py certs.json.gz --selftest     (corrupted copies must be rejected)"""
import sys, json, gzip, itertools, collections
import numpy as np
from multiprocessing import Pool


# ----- 1. types -----
def enumerate_types(d, top=16):
    pairs = [(S, T) for S in range(1, 1 << d) for T in range(S + 1, 1 << d) if not S & T]
    pts = np.array(list(itertools.product(range(1, top + 1), repeat=d)), dtype=np.int64)
    sub = np.array([[S >> i & 1 for i in range(d)] for S in range(1 << d)], dtype=np.int64)
    sums = pts @ sub.T
    sig = np.stack([np.sign(sums[:, S] - sums[:, T]) for S, T in pairs], axis=1)
    rev = sig[::-1]
    _, idx = np.unique(rev, axis=0, return_index=True)
    reps = pts[::-1][idx]
    sigs = rev[idx]
    strict = (sigs != 0).all(1)
    bal = reps.max(1) * 2 < reps.sum(1)
    return [tuple(int(x) for x in r) for r in reps[strict & bal]]


TY = {d: enumerate_types(d) for d in (3, 4)}
assert len(TY[3]) == 6 and len(TY[4]) == 288, (len(TY[3]), len(TY[4]))


def domain(R, priv):
    out = []
    for t in TY[len(R)]:
        v = dict(zip(R, t))
        if len(priv) == 2 and v[priv[0]] + v[priv[1]] >= sum(v.values()) - v[priv[0]] - v[priv[1]]: continue
        out.append(v)
    return out


def safe(v, own, others):
    mine = sum(v.get(g, 0) for g in own)
    for B in others:
        tot = sum(v.get(g, 0) for g in B)
        if any(tot - v.get(g, 0) > mine for g in B): return False
    return True


def is_marker(x):
    return x[:2] in ('w:', 'W:')


# ----- 2. states -----
def states(L, sps, source):
    seen = set()
    for lab in itertools.product(list(sps) + list(range(len(L))), repeat=len(L)):
        ren, blk = {}, []
        for x in lab:
            if isinstance(x, int):
                if x not in ren: ren[x] = len(ren)
                blk.append(ren[x])
            else: blk.append(x)
        blk = tuple(blk)
        if blk in seen or any(isinstance(x, int) and x not in ren.values() for x in blk): continue
        seen.add(blk)
        nb = len(ren)
        base = {s: [g for g, x in zip(L, blk) if x == s] for s in sps}
        blocks = [[g for g, x in zip(L, blk) if x == k] for k in range(nb)]
        for wf in itertools.product((False, True), repeat=len(sps)):
            Yb = {s: base[s] + (['w:' + s] if f else []) for s, f in zip(sps, wf)}
            for Wf in itertools.product((False, True), repeat=nb):
                Ob = [b + (['W'] if f else []) for b, f in zip(blocks, Wf)]
                if not source:
                    yield Yb, Ob, None; continue
                for s in sps: yield Yb, Ob, ('sp', s)
                for k in range(nb): yield Yb, Ob, ('O', k)
                yield Yb, Ob + [[]], ('O', nb)
                yield Yb, Ob + [['W']], ('O', nb)


def canonical(Yb, Ob, src):
    """(key, blocks with markers renamed 'W:<position>', unenvied bundle in canonical form)."""
    order = sorted(range(len(Ob)), key=lambda k: sorted(Ob[k]))
    pos = {k: i for i, k in enumerate(order)}
    blocks = [sorted(('W:%d' % i) if x == 'W' else x for x in Ob[k]) for i, k in enumerate(order)]
    sd = None if src is None else (['sp', src[1]] if src[0] == 'sp' else ['O', pos[src[1]]])
    return json.dumps([[sorted(Yb[s]) for s in sorted(Yb)], blocks, sd]), blocks, sd


# ----- 4. gadget legality -----
def partitions(items):
    if not items: yield []; return
    for p in partitions(items[1:]):
        for k in range(len(p)): yield p[:k] + [[items[0]] + p[k]] + p[k + 1:]
        yield [[items[0]]] + p


def comps(edges, verts):
    par = {v: v for v in verts}
    def f(v):
        while par[v] != v: par[v] = par[par[v]]; v = par[v]
        return v
    for a, b in edges: par[f(a)] = f(b)
    out = collections.defaultdict(set)
    for v in verts: out[f(v)].add(v)
    return list(out.values())


def gadget_problems(S, I, D, Ip, supp):
    out = []
    if not (len(supp) < len(S) or (len(supp) == len(S) and len(Ip) < len(I))): out.append('gadget not smaller')
    if Ip & D: out.append("I' meets D")
    for a, G in supp.items():
        if len(G) > 4: out.append('gadget agent %s values more than 4 goods' % a)
        if not G <= Ip | D: out.append("gadget agent %s values a good outside I' + D" % a)
    EH = [(('a', a), ('g', g)) for a, R in S.items() for g in R]
    EHp = [(('b', a), ('g', g)) for a, G in supp.items() for g in G]
    for P in partitions(sorted(D)):
        star = [(('r', k), ('g', g)) for k, blk in enumerate(P) for g in blk]
        def graph(E):
            V = {v for e in E + star for v in e} | {('g', g) for g in D} | {('r', k) for k in range(len(P))}
            return [(C, sum(1 for e in E + star if e[0] in C) - len(C) + 1) for C in comps(E + star, V)]
        GH, GHp = graph(EH), graph(EHp)
        for C, b in GHp:
            roots = {v for v in C if v[0] == 'r'}
            if not roots:
                if b > 0: out.append('gadget component with a cycle and no boundary good')
                continue
            host = [b2 for C2, b2 in GH if roots <= C2]
            if not host: out.append("H' joins parts that H keeps apart")
            elif b > host[0]: out.append("H' has a component with a larger cyclomatic number")
    return sorted(set(out))


# ----- 3 and 5. one record -----
def check_record(rec):
    S = {s: list(R) for s, R in rec['S'].items()}
    agents = sorted(S)
    I, D, Ip = set(rec['I']), set(rec['D']), set(rec['Ip'])
    priv = {s: [g for g in R if g in I and sum(g in R2 for R2 in S.values()) == 1] for s, R in S.items()}
    dom = {s: domain(R, priv[s]) for s, R in S.items()}
    shape = tuple(len(dom[s]) for s in agents)
    # gadget agents: list of valuations, one per type of the agent copied (or a single one)
    gv, dep, supp = {}, {}, {}
    for sp, spec in rec['Sp'].items():
        if 'fix' in spec:
            gv[sp] = [{g: x for g, x in spec['fix'].items()}]; dep[sp] = None
            supp[sp] = {g for g, x in spec['fix'].items() if x > 0}
        else:
            s, mp = spec['copy'], spec['map']
            gv[sp] = [{mp[g]: x for g, x in v.items()} for v in dom[s]]; dep[sp] = s
            supp[sp] = set(mp[g] for g in S[s])
    problems = gadget_problems(S, I, D, Ip, supp)
    wit = dict((k, X) for k, X in rec['states'])
    U = lambda B: frozenset(x for x in B if x in D or is_marker(x))
    inner = lambda B: any(x in I or x in Ip for x in B)
    L = sorted(Ip | D)
    sps = sorted(rec['Sp'])
    bad = np.zeros(shape, dtype=bool)
    seen_keys, n_adm, n_bad_x = set(), 0, 0
    for Yb, Ob, src in states(L, sps, rec['source']):
        key, blocks, sd = canonical(Yb, Ob, src)
        if key in seen_keys: continue
        seen_keys.add(key)
        Ysrc = None if sd is None else (Yb[sd[1]] if sd[0] == 'sp' else blocks[sd[1]])
        Yall = list(Yb.values()) + blocks
        adm = np.ones(shape, dtype=bool)
        for sp in sps:
            others = [B for t, B in Yb.items() if t != sp] + blocks
            ok = [safe(v, Yb[sp], others) and (Ysrc is None or sum(v.get(g, 0) for g in Ysrc) <=
                                                sum(v.get(g, 0) for g in Yb[sp])) for v in gv[sp]]
            if dep[sp] is None:
                if not ok[0]: adm[...] = False
            else:
                sh = [1] * len(shape); sh[agents.index(dep[sp])] = len(ok)
                adm &= np.array(ok).reshape(sh)
        if not adm.any(): continue
        n_adm += 1
        cov = np.zeros(shape, dtype=bool)
        moved = collections.Counter(x for s in sps for x in Yb[s] if x not in Ip)
        free = [k for k, b in enumerate(blocks) if b and all(x in Ip for x in b)]
        for X in wit.get(key, []):
            Xs, Ox = X['S'], X['O']
            ok = sorted(Xs) == agents and len(Ox) == len(blocks)
            if ok:
                allg = [x for B in Xs.values() for x in B] + [x for B in Ox for x in B]
                want = [x for B in Yall for x in B if x not in Ip] + sorted(I)
                ok = sorted(allg) == sorted(want)
            if ok:
                for k, (B, B0) in enumerate(zip(Ox, blocks)):
                    keep = [x for x in B0 if x not in Ip]
                    extra = collections.Counter(B) - collections.Counter(keep)
                    if collections.Counter(keep) - collections.Counter(B): ok = False; break
                    for x in extra:
                        if x in I: continue
                        if not (x in moved and k in free): ok = False
                    if not ok: break
            if ok:
                mod = [B for B in Xs.values()] + [B for B, B0 in zip(Ox, blocks) if sorted(B) != sorted(B0)]
                for B in mod:
                    if len(B) <= 1 or not U(B): continue
                    if Ysrc is not None and U(B) <= U(Ysrc): continue
                    if any(U(B) <= U(B2) and (not inner(B) or inner(B2) or U(B) != U(B2)) for B2 in Yall): continue
                    ok = False; break
            if not ok: n_bad_x += 1; continue
            masks = []
            for s in agents:
                others = [B for t, B in Xs.items() if t != s] + Ox
                masks.append(np.array([safe(v, Xs[s], others) for v in dom[s]]))
            arr = masks[0]
            for mk in masks[1:]: arr = np.logical_and.outer(arr, mk)
            cov |= arr
        bad |= adm & ~cov
    unknown = [k for k in wit if k not in seen_keys]
    if unknown: problems.append('%d stored states are not local states' % len(unknown))
    if n_bad_x: problems.append('%d stored extensions violate Lemma M1' % n_bad_x)
    covered = ~bad if not problems else np.zeros(shape, dtype=bool)
    return rec['config'], rec['name'], problems, n_adm, covered, [[dict(v) for v in dom[s]] for s in agents], agents


def run(recs, jobs):
    with Pool(jobs) as pool: return pool.map(check_record, recs)


def summarize(res, expect, fail_out=None):
    by = collections.OrderedDict()
    nprob = 0
    for cfg, name, problems, n_adm, covered, doms, agents in res:
        if problems:
            nprob += 1
            print('  PROBLEM %s / %s: %s' % (cfg, name, '; '.join(problems)))
        if cfg not in by: by[cfg] = [np.zeros(covered.shape, dtype=bool), doms, agents, 0, 0]
        by[cfg][0] |= covered
        by[cfg][3] += 1; by[cfg][4] += n_adm
    fails = {}
    for cfg, (cov, doms, agents, nrec, nadm) in by.items():
        print('  %-16s %3d records, %6d admissible states: %d of %d profiles covered' % (cfg, nrec, nadm, cov.sum(),
                                                                                       cov.size))
        fails[cfg] = [{s: doms[i][k] for i, (s, k) in enumerate(zip(agents, idx))} for idx in zip(*np.nonzero(~cov))]
    ok = nprob == 0
    for e in expect:
        c, n = e.rsplit(':', 1)
        got = int(by[c][0].sum()) if c in by else None
        if got != int(n): print('  EXPECT FAILED: %s covered %s, expected %s' % (c, got, n)); ok = False
    if fail_out:
        json.dump(fails, open(fail_out, 'w'), indent=0)
        print('  profiles not covered written to %s' % fail_out)
    return ok


def selftest(recs, jobs):
    """Corrupted copies must lose coverage or be flagged."""
    import copy
    base = {r['config'] + '/' + r['name']: r for r in recs}
    pick = next(r for r in recs if r['config'] == 'pair-P3-P3' and r['name'] == 'CON-e')
    res0 = check_record(pick)
    tests = []
    r = copy.deepcopy(pick); r['states'] = r['states'][1:]; tests.append(('a state deleted', r))
    r = copy.deepcopy(pick)
    for k, X in r['states']:
        for s in X[0]['S']:
            if X[0]['S'][s]: X[0]['S'][s] = X[0]['S'][s][1:]; break
        break
    tests.append(('a good dropped from an extension', r))
    r = copy.deepcopy(pick); r['Sp'] = dict(r['Sp']); r['Sp']['x'] = {'fix': {'gl': 1}}; tests.append(('an extra gadget agent', r))
    r = copy.deepcopy(pick); r['source'] = False; tests.append(('unenvied bundle dropped', r))
    sp = next(iter(pick['Sp']))
    r = copy.deepcopy(pick); r['Sp'] = {sp: {'fix': {g: 1 for g in pick['D'] + pick['Ip'] + ['u1', 'u2', 'u3']}}}
    tests.append(('gadget agent with too many goods', r))
    gad = next(r for r in recs if r['config'] == 'px-Q3')
    r = copy.deepcopy(gad); r['Ip'] = []; tests.append(("gadget good not declared in I'", r))
    # an extension that breaks domination: an interior good added to an outside bundle holding a boundary good and
    # outside goods (not the unenvied one)
    r = copy.deepcopy(pick)
    hit = False
    for k, Xl in r['states']:
        _, blocks, sd = json.loads(k)
        for i, b in enumerate(blocks):
            if len([x for x in b if x in pick['D']]) >= 1 and any(x.startswith('W:') for x in b) and sd != ['O', i]:
                for X in Xl:
                    g = next((x for B in X['S'].values() for x in B if x in pick['I']), None)
                    if g is None: continue
                    for B in X['S'].values():
                        if g in B: B.remove(g)
                    X['O'][i].append(g); hit = True
                if hit: break
        if hit: break
    tests.append(('interior good into a W bundle (domination)', r))
    good = True
    for what, args, want in (('smaller: 2 agents -> 2 agents, same goods', ({'e': ['a'], 'f': ['b']}, {'p'}, set(), {'q'}, {'x': set(), 'y': set()}), 'gadget not smaller'),
                             ('class: gadget closes a new cycle', ({'e': ['a', 'b'], 'f': ['c', 'p']}, {'p'}, {'a', 'b', 'c'}, set(), {'h': {'a', 'c'}}), "H' has a component with a larger cyclomatic number")):
        pr = gadget_problems(*args)
        print('  selftest %-44s -> %s' % (what, 'rejected' if want in pr else 'NOT REJECTED %s' % pr))
        good &= want in pr
    print('  selftest base record %s/%s: covered %d, problems %s' % (pick['config'], pick['name'], res0[4].sum(), res0[2]))
    for what, r in tests:
        res = check_record(r)
        rejected = bool(res[2]) or res[4].sum() < (res0[4].sum() if r['config'] == pick['config'] else 1e9)
        print('  selftest %-44s -> %s (problems: %s, covered %d)' % (what, 'rejected' if rejected else 'NOT REJECTED',
                                                                     res[2], res[4].sum()))
        good &= rejected
    return good


def main():
    path = sys.argv[1]
    opts = [a for a in sys.argv[2:]]
    jobs = next((int(a.split('=')[1]) for a in opts if a.startswith('--jobs=')), 4)
    expect = [a.split('=', 1)[1] for a in opts if a.startswith('--expect=')]
    fail_out = next((a.split('=', 1)[1] for a in opts if a.startswith('--fail-out=')), None)
    recs = json.load(gzip.open(path, 'rt'))
    print('check_reductions4.py %s: %d records; types re-enumerated: %d (3 goods), %d (4 goods)' % (
        path, len(recs), len(TY[3]), len(TY[4])))
    if '--selftest' in opts:
        ok = selftest(recs, jobs)
    else:
        ok = summarize(run(recs, jobs), expect, fail_out)
    print('RESULT: %s' % ('OK' if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
