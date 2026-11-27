"""The ∃-order form OC1^∃max (LEDGER K4.SDC.OC1EXMAX) for every strict profile of a k = 4 core hypergraph, by ordinal
CEGAR (workstream compute/k4-oc1max-cert; notes in k4/oc1cert.md).

OC1^∃max: under every strict type profile tau, SOME SD order pi has maximum-matching picks Y = SD(pi, tau) that satisfy
OC1: a one-absorber completion at the picks, or after one official move.

Loop, "exists tau forall (pi, repair): fails":
- Outer SAT: one-hot types and comparison bits (as in cegar.py), with no pick variables.  Every entry found so far must
  fail.  An entry is (pi, Y, W) with W a witness of cegar.py for the fixed picks Y.  It blocks the profiles under which
  (1) SD(pi, tau) = Y, and (2) W repairs (tau, Y).
  - (1) is a conjunction of comparisons: agent i, at its turn in pi, prefers Y_i to each relevant good not picked
    before it.  A pickless agent's goods are all picked before it, which is combinatorial.
  - (2) is W's improving comparisons and EFX0 of X.  Its combinatorial conditions are fixed once Y is.
  So the negation is one clause over comparison bits.
- Inner: for the integer representative of tau, take the distinct SD outcomes over all orders that are maximum
  matchings.  For each, cegar.Cert.inner gives repairs.  The entry kept is the one whose profile box is largest; the
  order is chosen per Y, as the one with the largest SD region.
- If no maximum-matching outcome has a repair, tau is a counterexample to OC1^∃max.  It is re-checked with Inst.

    python3 k4/oc1cert/exists.py LIST[,LIST...] --out=CERT.json.gz [--jobs=4] [--only-fail=CERT_DEPTH1.json.gz]
(--only-fail: only the hypergraphs that are not certified in that OC1^max certificate.)"""
import sys, os, gzip, json, itertools, collections, time, math, multiprocessing as mp
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from cegar import Cert, TRUE, FALSE, neg
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


class ExCert(Cert):
    def _build_outer(self, solver):
        vp = IDPool(); self.vp = vp; self.bits = {}
        self.out = Solver(name=solver)
        self.z = [[vp.id(('z', i, t)) for t in range(len(D))] for i, D in enumerate(self.dom)]
        for zi in self.z:
            for c in CardEnc.equals(zi, 1, vpool=vp, encoding=EncType.seqcounter if len(zi) > 8 else EncType.pairwise).clauses:
                self.out.add_clause(c)

    def sd(self, vals, order):
        taken = set(); Y = [None] * self.n
        for i in order:
            av = [g for g in self.sets[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: vals[i][h]); Y[i] = g; taken.add(g)
        return tuple(Y)

    def region(self, Y, order):
        """[(agent, A, B)] with v_i(A) > v_i(B) required for SD(order, .) = Y (A, B position masks), or None if
        impossible (a pickless agent with a relevant good not picked before it)."""
        taken = set(); req = []
        for i in order:
            rest = [g for g in self.sets[i] if g not in taken]
            if Y[i] is None:
                if rest: return None
            else:
                if Y[i] not in rest: return None
                req += [(i, self.mask(i, [Y[i]]), self.mask(i, [g])) for g in rest if g != Y[i]]
                taken.add(Y[i])
        return req

    def region_volume(self, req):
        ok = [np.ones(len(D), dtype=bool) for D in self.dom]
        for i, A, B in req: ok[i] &= self.ss[i][:, A] > self.ss[i][:, B]
        return ok

    def entry_clause(self, order, Y, W):
        req = self.region(Y, order)
        lits = [neg(self.cmp(i, A, B)) for i, A, B in req]
        for x, new, old in W.imp:
            lits.append(neg(self.cmp(x, self.mask(x, set(new) - set(old)), self.mask(x, set(old) - set(new)))))
        for i in range(self.n):
            O, Ts = self.threats(i, W.X)
            lits += [self.cmp(i, T, O) for T in Ts]
        return self._clause(lits)

    def entry_volume(self, order, Y, W):
        ok = self.region_volume(self.region(Y, order))
        for i in range(self.n):
            O, Ts = self.threats(i, W.X)
            for T in Ts: ok[i] &= self.ss[i][:, T] < self.ss[i][:, O]
            for x, new, old in W.imp:
                if x == i:
                    ok[i] &= self.ss[i][:, self.mask(i, set(new) - set(old))] > self.ss[i][:, self.mask(i, set(old) - set(new))]
        return sum(math.log(max(1, o.sum())) for o in ok), ok

    def run_exists(self, time_limit=None):
        t0 = time.time(); self.iters = 0; self.entries = []; self.ex_fails = []
        orders = list(itertools.permutations(range(self.n)))
        while True:
            if time_limit and time.time() - t0 > time_limit: return 'timeout'
            if not self.out.solve(): return 'certified' if not self.ex_fails else 'FAIL'
            mod = set(l for l in self.out.get_model() if l > 0)
            prof = [next(t for t, v in enumerate(zi) if v in mod) for zi in self.z]
            vals = self.vals_of(prof); self.iters += 1
            byY = collections.defaultdict(list)
            for o in orders:
                Y = self.sd(vals, o)
                if sum(y is not None for y in Y) == self.nu: byY[Y].append(o)
            best = None
            for Y, os_ in byY.items():
                Ws = self.inner(prof, Y)
                for W in Ws:
                    for o in os_:
                        vol, _ = self.entry_volume(o, Y, W)
                        if best is None or vol > best[0]: best = (vol, o, Y, W)
                if best is not None and not best[3].moves: break          # a completion at the picks: good enough
            if best is None:
                self.ex_fails.append(prof)
                self.out.add_clause([-self.z[i][t] for i, t in enumerate(prof)])
                continue
            _, o, Y, W = best
            for ma, mg in self.auts:
                inv = {ma[i]: i for i in range(self.n)}
                o2 = tuple(ma[i] for i in o)
                Y2 = [None] * self.n
                for i, y in enumerate(Y): Y2[ma[i]] = None if y is None else mg[y]
                W2 = W.image(ma, mg)
                cl = self.entry_clause(o2, tuple(Y2), W2)
                if cl is None: continue
                self.entries.append((o2, tuple(Y2), W2)); self.out.add_clause(cl)


def compact_entries(C):
    """An UNSAT core of the entry clauses (a fresh outer with one selector per entry)."""
    B = ExCert.__new__(ExCert)
    B.__dict__.update({k: v for k, v in C.__dict__.items() if k in ('sets', 'n', 'm', 'R', 'pos', 'dom', 'ss', 'nu')})
    B._build_outer('cd15')
    sel = []
    for k, (o, Y, W) in enumerate(C.entries):
        s_ = B.vp.id(('sel', k)); sel.append(s_)
        B.out.add_clause(B.entry_clause(o, Y, W) + [-s_])
    assert not B.out.solve(assumptions=sel)
    core = set(B.out.get_core() or [])
    keep = [e for e, s_ in zip(C.entries, sel) if s_ in core]
    B.out.delete()
    return keep


def job(task):
    lst, idx, sets = task
    t0 = time.time()
    C = ExCert(sets)
    r = C.run_exists()
    rec = {'list': lst, 'idx': idx, 'sets': sets, 'nu': C.nu, 'result': r, 'iters': C.iters, 'entries_added': len(C.entries),
           'time': round(time.time() - t0, 3)}
    if r == 'certified':
        keep = compact_entries(C)
        rec['entries_before_compaction'] = len(C.entries)
        rec['entries'] = [{'order': list(o), 'picks': list(Y), 'witness': W.to_json()} for o, Y, W in keep]
    else:
        from oc1_mc2_rand import Inst
        rec['fails'] = []
        for prof in C.ex_fails[:3]:
            vals = [list(C.dom[i][t]) for i, t in enumerate(prof)]
            I = Inst(sets, vals)
            outs = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
            raw = {str(Y): I.check(Y) for Y in outs if sum(y is not None for y in Y) == C.nu}
            rec['fails'].append({'vals': vals, 'raw_max_orders': raw})
    return rec


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    print('$ python3 k4/oc1cert/exists.py', *sys.argv[1:], flush=True)
    only = None
    if 'only-fail' in opt:
        only = {(r['list'], r['idx'], json.dumps(r['sets'])) for r in json.load(gzip.open(opt['only-fail']))['cores'] if r['result'] != 'certified'}
    tasks = []
    for lst in args[0].split(','):
        for c in json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_%s.json.gz' % lst)))['cores']:
            if only is not None and (lst, c['idx'], json.dumps(c['sets'])) not in only: continue
            tasks.append((lst, c['idx'], c['sets']))
    print('hypergraphs', len(tasks), flush=True)
    T = collections.Counter(); recs = []; t0 = time.time()
    with mp.Pool(int(opt.get('jobs', mp.cpu_count()))) as pool:
        for rec in pool.imap_unordered(job, tasks):
            recs.append(rec); T['result %s' % rec['result']] += 1; T['iterations'] += rec['iters']
            T['entries kept'] += len(rec.get('entries', []))
            if rec['result'] != 'certified':
                print('OC1EXMAX FAILS', json.dumps({k: rec[k] for k in rec if k != 'entries'}), flush=True)
            if len(recs) % 200 == 0: print('... %d, %.0f s' % (len(recs), time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
    if 'out' in opt:
        with gzip.open(opt['out'], 'wt') as f:
            json.dump({'statement': 'OC1^exists-max (K4.SDC.OC1EXMAX) for every strict profile: some SD order has '
                                    'maximum-matching picks with a one-absorber completion at the picks or after one move',
                       'generator': 'k4/oc1cert/exists.py', 'cores': sorted(recs, key=lambda r: (r['list'], r['idx']))}, f)
        print('wrote', opt['out'])


if __name__ == '__main__':
    main()
