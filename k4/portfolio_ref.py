#!/usr/bin/env python3
"""Reference implementation (b) of the portfolio predicates (compute/k4-portfolio). EVIDENCE tooling.

Model: k4/dl134_xcheck.py's `Prof` on main's k4/c4x_check.py (its own enumeration of every base map, (V1), (V2)
literally, its own removal-only deficit `rodef`), loaded as k4/rt4_n5_xcheck.py loads it: an empty stub stands in for
k4/dl2_relations.py during the import, so k4/suite/model.py is never loaded (asserted at the end of a run). Nothing
here calls k4/portfolio_dump.c, k4/dlrt4.c or k4/portfolio_preds.py's move descriptor: every predicate below is
written again from its definition (k4/dl2.md §3, k4/dlrt4.c's header, the ledger row K4.DL2.RC and the job's list),
with bases as frozensets, the needs from c4x_check's model (`Prof.info`), and U, Z, W, Y as explicit sets.

  python3 k4/portfolio_ref.py compare INST.json ... [--every=E] [--maxm=M] [--maxn=N]
      For each profile (JSON lists of {"id", "sets", "vals", "m"}), computes the min-frozen class and the deficits
      here, and the same with the fast path (k4/portfolio_dump.c + k4/portfolio_preds.py), and compares: the class
      and the deficits of the states, then for every predicate of the registry the verdict AND the number of
      repairs at every state (single-step forms) and at every key with def* > 0 (key-graph forms).
  python3 k4/portfolio_ref.py confirm FAILS.jsonl.gz [--pred=NAME] [--max=K]
      Re-derives failures written by k4/portfolio.py or k4/portfolio_hunt.py with this implementation alone.
  python3 k4/portfolio_ref.py sample OUT.json CERTS.json.gz P SEED [--maxm=M] [--every=E] [--fmin=F]
      Writes the profiles with f >= F and a state among P random profiles per core (every E-th core) of a certificate
      file, as an instance list for `compare` (the selection uses the fast path; the comparison does not depend on it)."""
import collections, gzip, json, os, sys, time, types
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
_STUB = 'dl2_relations' not in sys.modules
if _STUB: sys.modules['dl2_relations'] = types.ModuleType('dl2_relations')
try:
    import dl134_xcheck as X
finally:
    if _STUB: del sys.modules['dl2_relations']

BIG = 1 << 20         # c4x_check.rodef's "no free owner" value (+inf)


class Ref:
    def __init__(self, sets, vals, m):
        self.Pr = X.Prof(sets, vals, m)
        self.n = self.Pr.n
        self.f = self.Pr.f
        self.cls = [(P, (float('inf') if d >= BIG else d)) for P, d in self.Pr.mp]
        self.dd = dict(self.cls)
        self.inf = {P: self.Pr.info(P) for P, _ in self.cls}

    def needs(self, P): return self.inf[P][0]
    def NA(self, P): return self.inf[P][1]
    def frozen(self, P): return {i for i in range(self.n) if self.inf[P][2][i]}

    def key(self, P):
        fz = self.frozen(P)
        return (self.NA(P), tuple(P[i] if i in fz else None for i in range(self.n)))

    def parts(self, P, Q):
        ch = {i for i in range(self.n) if P[i] != Q[i]}
        FP, FQ = self.frozen(P), self.frozen(Q)
        U = FP - FQ                       # over all agents
        Z = FQ - FP
        W = {i for i in ch if i in FP and i in FQ}
        Y = {i for i in ch if i not in FP and i not in FQ}
        return ch, U, Z, W, Y, self.NA(P) == self.NA(Q)

    # ---- the moves, from their definitions ----
    def t1(self, P, Q):
        ch, U, Z, W, Y, keep = self.parts(P, Q)
        return len(ch) == 1 and keep

    def t2(self, P, Q):
        ch, U, Z, W, Y, keep = self.parts(P, Q)
        FP, FQ = self.frozen(P), self.frozen(Q)
        return len(ch) >= 2 and keep and all(i not in FP and i not in FQ for i in ch) and FP == FQ

    def t3(self, P, Q):
        ch, U, Z, W, Y, keep = self.parts(P, Q)
        if not keep or len(U) != 1 or len(Z) != 1 or W or len(Y) > 1: return False
        (x,), (z,) = U, Z
        if x not in ch or z not in ch: return False
        if Q[z] != P[x] or not P[x] <= self.needs(P)[z]: return False
        return all(P[h] - Q[h] for h in Y)

    def t4(self, P, Q):
        ch, U, Z, W, Y, keep = self.parts(P, Q)
        if not ch or not keep or U or Z or Y: return False
        return sorted(sorted(Q[i]) for i in ch) == sorted(sorted(P[i]) for i in ch)

    def t3plus(self, P, Q, wmax=None, ymax=1, need=True, give=True):
        ch, U, Z, W, Y, keep = self.parts(P, Q)
        if not keep or len(U) != 1 or len(Z) != 1: return False
        if wmax is not None and len(W) > wmax: return False
        if ymax is not None and len(Y) > ymax: return False
        (x,), (z,) = U, Z
        if give and not all(P[y] - Q[y] for y in Y): return False
        if need and not Q[z] <= self.needs(P)[z]: return False
        return sorted(sorted(Q[i]) for i in W | {z}) == sorted(sorted(P[i]) for i in W | {x})

    def gen(self, P, Q, kind):
        ch, U, Z, W, Y, keep = self.parts(P, Q)
        if kind == 'NA1': return keep and len(U) <= 1 and len(Z) <= 1
        if kind == 'NAbal': return keep and len(U) == len(Z)
        if kind == 'NAall': return keep
        if kind == 'U1Z1': return len(U) <= 1 and len(Z) <= 1
        if kind == 'D2': return len(ch) <= 2
        if kind == 'D3': return len(ch) <= 3
        if kind == 'D4': return len(ch) <= 4
        if kind == 'FR3': return len(U) + len(Z) + len(W) <= 3
        if kind == 'U0': return keep and not U
        if kind == 'KU1': return len(U) <= 1
        raise KeyError(kind)

    def single(self, name, P, Q):
        t1, t2, t4 = (lambda: self.t1(P, Q)), (lambda: self.t2(P, Q)), (lambda: self.t4(P, Q))
        base = lambda: t1() or t2() or t4()
        if name == 'RT4': return base() or self.t3(P, Q)
        if name == 'RC3':
            if sum(1 for i in range(self.n) if P[i] != Q[i]) > 3: return False
            return base() or self.t3plus(P, Q, wmax=1)
        if name == 'RC3_noT4':
            if sum(1 for i in range(self.n) if P[i] != Q[i]) > 3: return False
            return self.t1(P, Q) or self.t2(P, Q) or self.t3plus(P, Q, wmax=1)
        if name == 'NA3': return self.NA(P) == self.NA(Q) and sum(1 for i in range(self.n) if P[i] != Q[i]) <= 3
        if name == 'RC_W1': return base() or self.t3plus(P, Q, wmax=1)
        if name == 'RC': return base() or self.t3plus(P, Q)
        if name == 'RC_noneed': return base() or self.t3plus(P, Q, need=False)
        if name == 'RC_Yfree': return base() or self.t3plus(P, Q, give=False)
        if name == 'RC_Yany': return base() or self.t3plus(P, Q, ymax=None)
        if name == 'RC_U0': return self.gen(P, Q, 'U0') or self.t3plus(P, Q)
        return self.gen(P, Q, name)

    def keyedge(self, name, P, Q):
        if name == 'K1': return self.t3(P, Q) or self.t4(P, Q)
        if name == 'K3b_noT4': return sum(1 for i in range(self.n) if P[i] != Q[i]) <= 3 and self.t3plus(P, Q, wmax=1)
        if name == 'K3b': return sum(1 for i in range(self.n) if P[i] != Q[i]) <= 3 and (self.t3plus(P, Q, wmax=1) or self.t4(P, Q))
        if name == 'K3': return self.t3plus(P, Q, wmax=1) or self.t4(P, Q)
        if name == 'K2': return self.t3plus(P, Q) or self.t4(P, Q)
        if name == 'K2_noneed': return self.t3plus(P, Q, need=False) or self.t4(P, Q)
        if name == 'K2_Yany': return self.t3plus(P, Q, ymax=None) or self.t4(P, Q)
        if name == 'K4': return self.gen(P, Q, 'NA1')
        if name == 'K5': return self.gen(P, Q, 'NAall')
        if name == 'KU1': return self.gen(P, Q, 'KU1')
        raise KeyError(name)

    def evaluate(self, snames, knames):
        """{state P: {name: number of repairs}}, {key: {name: number of edges to better keys}}, def*"""
        sres = {}
        for P, dP in self.cls:
            if not dP > 0: continue
            better = [Q for Q, dQ in self.cls if dQ < dP]
            sres[P] = {nm: sum(1 for Q in better if self.single(nm, P, Q)) for nm in snames}
        K = collections.defaultdict(list)
        for P, _ in self.cls: K[self.key(P)].append(P)
        dstar = {k: min(self.dd[P] for P in v) for k, v in K.items()}
        kres = {}
        for k, Ps in K.items():
            if not dstar[k] > 0: continue
            tq = [Q for Q, _ in self.cls if self.key(Q) != k and dstar[self.key(Q)] < dstar[k]]
            kres[k] = {nm: sum(1 for P in Ps for Q in tq if self.keyedge(nm, P, Q)) for nm in knames}
        return sres, kres, dstar


def fast(d):
    """the fast path on one profile: (f, {state: {name: nrep}}, {key: {name: nedges}}, {P: def}) with frozenset bases"""
    import portfolio as PF, portfolio_preds as PR
    blk = PF.block(d['sets'], d['m'], [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])], 0, 0)
    A, _ = PF.run_c(blk, ['-f0', '-a'], wide=d['m'] > 32)
    if not A: return None
    a = A[0]
    pd = PR.ProfData(d['sets'], d['vals'], d['m'], [(B, (float('inf') if x >= PF.INF else x)) for B, x in a['cls']])
    r = PR.evaluate(pd)
    fs = lambda B: tuple(frozenset(g for g in range(64) if b >> g & 1) for b in B)
    st = [p for p in range(len(pd.P)) if pd.d[p] > 0]
    sres = {fs(pd.P[p]): {nm: r['single'][nm]['nrep'][i] for nm in PR.SNAMES} for i, p in enumerate(st)}
    K = collections.defaultdict(list)
    for p in range(len(pd.P)): K[pd.key[p]].append(p)
    pos = [k for k in K if r['dstar'][k] > 0]
    kres = {}
    for i, k in enumerate(pos):
        NA, fz = k
        kk = (frozenset(g for g in range(64) if NA >> g & 1), tuple(frozenset(g for g in range(64) if b >> g & 1) if b >= 0 else None for b in fz))
        kres[kk] = {nm: r['keyg'][nm]['nrep'][i] for nm in PR.KNAMES}
    defs = {fs(B): x for B, x in zip(pd.P, pd.d)}
    return a['f'], sres, kres, defs


def compare(argv):
    import portfolio_preds as PR
    files = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    insts = [d for f in files for d in json.load(open(f))][::int(opt.get('every', 1))]
    insts = [d for d in insts if (d.get('m') or 0) <= int(opt.get('maxm', 99)) and len(d['sets']) <= int(opt.get('maxn', 99))]
    print(f'# {len(insts)} profiles', flush=True)
    tot = collections.Counter(); t0 = time.time()
    for d in insts:
        d['m'] = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
        R = Ref(d['sets'], d['vals'], d['m'])
        om = R.f - (2 * R.n - d['m'])
        F = fast(d)
        if om <= 0:
            tot['omega<=0'] += 1
            if F is not None: tot['MISMATCH omega'] += 1; print('MISMATCH omega', d['id'])
            continue
        if R.f < 1: tot['f=0'] += 1; continue
        sres, kres, dstar = R.evaluate(PR.SNAMES, PR.KNAMES)
        f2, s2, k2, defs2 = F
        bad = []
        if f2 != R.f: bad.append('f')
        if {P: x for P, x in R.cls} != defs2: bad.append('class/deficits')
        if set(sres) != set(s2): bad.append('states')
        if set(kres) != set(k2): bad.append('keys')
        for P in set(sres) & set(s2):
            for nm in PR.SNAMES:
                tot['state verdicts'] += 1
                if sres[P][nm] != s2[P][nm]: bad.append(f'{nm} at {[sorted(b) for b in P]}: ref {sres[P][nm]} fast {s2[P][nm]}')
        for k in set(kres) & set(k2):
            for nm in PR.KNAMES:
                tot['key verdicts'] += 1
                if kres[k][nm] != k2[k][nm]: bad.append(f'{nm} at key {sorted(k[0])}: ref {kres[k][nm]} fast {k2[k][nm]}')
        tot['profiles'] += 1; tot['states'] += len(sres); tot['keys'] += len(kres)
        for P in sres:
            for nm in PR.SNAMES: tot['fail ' + nm] += sres[P][nm] == 0
        for k in kres:
            for nm in PR.KNAMES: tot['fail ' + nm] += kres[k][nm] == 0
        if bad:
            tot['MISMATCH profiles'] += 1
            print('MISMATCH', d['id'], bad[:6], flush=True)
    print('compared: profiles %d (f >= 1, omega >= 1), states %d, keys def* > 0 %d; %d state-predicate and %d key-predicate '
          'repair counts compared; mismatching profiles %d; skipped: f = 0 %d, omega <= 0 %d [%.0f s]' % (
              tot['profiles'], tot['states'], tot['keys'], tot['state verdicts'], tot['key verdicts'],
              tot['MISMATCH profiles'], tot['f=0'], tot['omega<=0'], time.time() - t0))
    print('failures (reference): ' + ', '.join('%s %d' % (nm, tot['fail ' + nm]) for nm in PR.SNAMES + PR.KNAMES))
    done()
    return 1 if tot['MISMATCH profiles'] or tot['MISMATCH omega'] else 0


def confirm(argv):
    import portfolio_preds as PR
    files = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    recs = [json.loads(l) for f in files for l in gzip.open(f, 'rt')]
    if 'pred' in opt: recs = [r for r in recs if r['pred'] == opt['pred']]
    seen = collections.Counter(); ok = bad = 0
    cache = {}
    for r in recs:
        if seen[r['pred']] >= int(opt.get('max', 10 ** 9)): continue
        seen[r['pred']] += 1
        ck = json.dumps([r['sets'], r['vals']])
        if ck not in cache:
            R = Ref(r['sets'], r['vals'], r['m'])
            cache[ck] = (R, R.evaluate(PR.SNAMES, PR.KNAMES))
        R, (sres, kres, dstar) = cache[ck]
        if r['kind'] == 'single':
            P = tuple(frozenset(b) for b in r['B'])
            v = sres.get(P, {}).get(r['pred'])
            good = v == 0 and (R.dd[P] if R.dd[P] != float('inf') else None) == r['def']
            print(('CONFIRMED' if good else 'NOT CONFIRMED'), r['pred'], r['id'], r['B'], 'def', r['def'], '| ref repairs', v, flush=True)
        else:
            k = (frozenset(r['NA']), tuple(frozenset(r['frozen'][str(i)]) if str(i) in r['frozen'] else None for i in range(len(r['sets']))))
            v = kres.get(k, {}).get(r['pred'])
            good = v == 0
            print(('CONFIRMED' if good else 'NOT CONFIRMED'), r['pred'], r['id'], 'key NA', r['NA'], r['frozen'], 'def*', r['def'],
                  '| ref edges', v, flush=True)
        ok += good; bad += not good
    print(f'confirmed {ok}, not confirmed {bad}; by predicate {dict(seen)}')
    done()
    return 1 if bad else 0


def sample(argv):
    import portfolio as PF, check4
    out, certs, P, seed = argv[0], argv[1], int(argv[2]), int(argv[3])
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv[4:] if a.startswith('--'))
    cores = json.load(gzip.open(certs, 'rt'))['cores']
    res = []
    for pos in range(0, len(cores), int(opt.get('every', 1))):
        c = cores[pos]
        if c['m'] > int(opt.get('maxm', 99)): continue
        doms = check4.core_domains(c['sets'], c['m'], False)
        A, _ = PF.run_c(PF.block(c['sets'], c['m'], doms, pos, P), [f'-S{seed}', f"-f{opt.get('fmin', 1)}"])
        for a in A:
            res.append({'id': f"{os.path.basename(certs)}#{pos}:{','.join(map(str, a['prof']))}", 'sets': c['sets'], 'm': c['m'],
                        'vals': [[doms[i][p][g] for g in S] for i, (S, p) in enumerate(zip(c['sets'], a['prof']))]})
    json.dump(res, open(out, 'w'))
    print(f'{len(res)} profiles -> {out}')


def done():
    loaded = sorted(m for m in ('model', 'dl2_classify', 'dl2_relations') if m in sys.modules)
    print('# modules of the model.py side loaded: %s' % (loaded or 'none'), flush=True)
    assert not loaded, loaded


if __name__ == '__main__':
    print('# command: python3 k4/portfolio_ref.py ' + ' '.join(sys.argv[1:]), flush=True)
    cmd = sys.argv[1]
    sys.exit({'compare': compare, 'confirm': confirm, 'sample': sample}[cmd](sys.argv[2:]))
