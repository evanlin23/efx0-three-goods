"""Independent checker for the OC1^max certificates of k4/oc1cert/run.py (workstream compute/k4-oc1max-cert).

Written separately from cegar.py; it shares no code with it or with the repository's other k = 4 tools.
- Types: its own enumeration.  The integer grid [1, 16]^d is keyed by the signs of v(A) - v(B) over disjoint
  nonempty A, B.  Strict means no sign is zero, balanced means 2 max < sum.  An agent with two private goods p, q also
  needs v(p) + v(q) < v(rest) ((C4)).  Expect 6 and 288 types (K4.OT).
- Maximum matchings: brute force over pick vectors (one relevant good or nothing per agent, goods distinct).
- For every maximum matching Y separately, the SAT question is: is there a type profile tau and an order pi such that
  SD(pi, tau) = Y and no certificate witness repairs (tau, Y)?
  - The SD condition is encoded through the order itself.  pi is a strict total order on the agents (variables
    before[a][b], antisymmetric, total, transitive).  Under type t, agent i needs every good it prefers to Y_i (every
    relevant good, if Y_i is none) to be picked by an agent before it.  A type for which such a good is unpicked is
    excluded.
  - A witness repairs (tau, Y) when its move is legal from the concrete Y by the raw rules of k4/sdc.md §29 and
    k4/sdc/oc1_mc2_rand.py Inst.moves:
    - an addition is H ⊆ J ∩ R_x;
    - a chain hands on only nonempty bases, adds junk inside the receivers' relevant goods, and lets x_0 take
      H_0 ⊆ J ∪ B_{x_t};
    - a ring hands on nonempty bases.
    Its X must contain the moved bases and give at most one agent two or more goods outside the bases.  The improving
    comparisons and EFX0 of X (v_i(X_i) >= v_i(X_j) - v_i(h) for every j != i and h in X_j) must hold for every
    agent's type.  These are raw integer evaluations, one mask over the types per agent.
  - Solver: Glucose 4 (the CEGAR uses CaDiCaL).  UNSAT for every Y: the hypergraph is covered.  Per Y, the types of an
  agent that the SD constraints and every witness mask treat alike are merged into one variable (an exact reduction:
  the formula depends on a type only through these memberships).
- The witnesses' recorded picks are used only to skip witnesses that do not match Y (skipping only weakens
  coverage, so this is sound).

    python3 k4/oc1cert/check.py CERT.json.gz [--lists=LIST,...]   (with --lists, also check that the certificate has
                                                                   every hypergraph of results/k4_certs_<LIST>.json.gz)"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import numpy as np
from pysat.solvers import Glucose4

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def own_types(d):
    grid = np.array(list(itertools.product(range(1, 17), repeat=d)), dtype=np.int64)
    masks = list(range(1, 1 << d))
    sums = np.stack([grid[:, [p for p in range(d) if M >> p & 1]].sum(1) for M in masks], 1)   # column M-1
    pairs = [(A, B) for A in masks for B in masks if A < B and not A & B]
    sig = np.stack([np.sign(sums[:, A - 1] - sums[:, B - 1]) for A, B in pairs], 1)
    ok = (sig != 0).all(1) & (2 * grid.max(1) < grid.sum(1))
    reps = {}
    for v, s in zip(grid[ok], sig[ok]):
        reps.setdefault(s.tobytes(), tuple(int(a) for a in v))
    return list(reps.values())


TYPES = {d: own_types(d) for d in (3, 4)}
assert len(TYPES[3]) == 6 and len(TYPES[4]) == 288, (len(TYPES[3]), len(TYPES[4]))


class Hyper:
    def __init__(self, sets):
        self.sets = [list(S) for S in sets]; self.n = len(sets)
        self.m = 1 + max(g for S in sets for g in S)
        self.R = [set(S) for S in sets]
        deg = collections.Counter(g for S in sets for g in S)
        self.types = []
        for S in self.sets:
            priv = [p for p, g in enumerate(S) if deg[g] == 1]
            T = TYPES[len(S)]
            if len(priv) == 2:
                T = [v for v in T if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
            self.types.append([dict(zip(S, v)) for v in T])
        self.V = [np.array([[v[g] if g in v else 0 for g in range(self.m)] for v in T], dtype=np.int64)
                  for T in self.types]                     # V[i][t, g] = value of good g under type t of agent i

    def picks_all(self):
        out = []
        def rec(i, used, cur):
            if i == self.n: out.append(tuple(cur)); return
            rec(i + 1, used, cur + [None])
            for g in self.sets[i]:
                if g not in used: rec(i + 1, used | {g}, cur + [g])
        rec(0, frozenset(), [])
        nu = max(sum(y is not None for y in Y) for Y in out)
        return nu, [Y for Y in out if sum(y is not None for y in Y) == nu]

    def val(self, i, S):
        """values of the set S for every type of agent i (vector)"""
        S = list(S)
        return self.V[i][:, S].sum(1) if S else np.zeros(len(self.types[i]), dtype=np.int64)

    def efx0_masks(self, X):
        B = [[g for g in range(self.m) if X[g] == a] for a in range(self.n)]
        out = []
        for i in range(self.n):
            own = self.val(i, B[i]); ok = np.ones(len(self.types[i]), dtype=bool)
            for j in range(self.n):
                if j == i or not B[j]: continue
                tot = self.val(i, B[j])
                for h in B[j]: ok &= own >= tot - self.V[i][:, h]
            out.append(ok)
        return out

    def apply(self, Y, w):
        """(new bases, improving conditions [(agent, new, old)]) if w's move (or sequence of moves, applied in turn)
        is legal from the picks Y by the raw rules, else None"""
        base = [[y] if y is not None else [] for y in Y]
        if w['kind'] != 'seq': return self.apply_move(base, w)
        imps = []
        for mv in w['moves']:
            if mv['kind'] in ('picks', 'seq'): return None
            r = self.apply_move(base, mv)
            if r is None: return None
            base, imp = r; imps += imp
        return base, imps

    def apply_move(self, base, w):
        n, R = self.n, self.R
        held = {g for b in base for g in b}
        if len(held) != sum(len(b) for b in base): return None
        J = set(range(self.m)) - held
        kind, path, H = w['kind'], list(w['path']), [list(h) for h in w['H']]
        nb = [list(b) for b in base]; imp = []
        if kind == 'picks':
            if path or H: return None
            return nb, imp
        if len(set(path)) != len(path) or not all(0 <= a < n for a in path) or len(H) != len(path): return None
        allH = [g for h in H for g in h]
        if len(set(allH)) != len(allH): return None
        if kind == 'add':
            if len(path) != 1: return None
            x = path[0]
            if not H[0] or not set(H[0]) <= (J & R[x]): return None
            nb[x] = base[x] + H[0]; imp.append((x, nb[x], base[x]))
            return nb, imp
        if kind == 'chain':
            t = len(path) - 1
            if t < 1: return None
            if any(not base[path[i]] for i in range(t)): return None
            for i in range(1, t + 1):
                if not set(H[i]) <= (J & R[path[i]]): return None
            x0 = path[0]
            if not H[0] or not set(H[0]) <= ((J | set(base[path[t]])) & R[x0]): return None
            if set(H[0]) & set(g for i in range(1, t + 1) for g in H[i]): return None
            nb[x0] = list(H[0]); imp.append((x0, nb[x0], base[x0]))
            for i in range(1, t + 1):
                nb[path[i]] = base[path[i - 1]] + H[i]; imp.append((path[i], nb[path[i]], base[path[i]]))
            return nb, imp
        if kind == 'ring':
            r = len(path)
            if r < 2: return None
            for i in range(r):
                if not base[path[i - 1]]: return None
                if not set(H[i]) <= (J & R[path[i]]): return None
            for i in range(r):
                nb[path[i]] = base[path[i - 1]] + H[i]; imp.append((path[i], nb[path[i]], base[path[i]]))
            return nb, imp
        return None

    def shape_ok(self, nb, X):
        if len(X) != self.m or not all(0 <= a < self.n for a in X): return False
        inb = {}
        for a, b in enumerate(nb):
            for g in b:
                if g in inb: return False          # bases must be disjoint
                inb[g] = a
        if any(X[g] != a for g, a in inb.items()): return False
        cnt = collections.Counter(X[g] for g in range(self.m) if g not in inb)
        return sum(c >= 2 for c in cnt.values()) <= 1


def read_records(path):
    """(header, iterator over records) of a certificate: a .json.gz with 'cores', or a .jsonl.gz with a header line
    and one record per line."""
    if path.endswith('.jsonl.gz'):
        f = gzip.open(path, 'rt'); head = json.loads(f.readline())
        return head, (json.loads(l) for l in f if l.strip())
    D = json.load(gzip.open(path))
    return D, iter(D.pop('cores'))


def check_core(rec):
    t0 = time.time()
    H = Hyper(rec['sets']); n = H.n
    nu, Ys = H.picks_all()
    if nu != rec['nu']: return rec['list'], rec['idx'], False, 'nu mismatch %d %d' % (nu, rec['nu']), 0, 0
    Ws = rec['witnesses']
    for w in Ws: w['_X'] = [int(c) for c in w['X']]
    efx = {}
    stats = collections.Counter()
    for Y in Ys:
        holder = {y: i for i, y in enumerate(Y) if y is not None}
        # per agent and type: excluded (a preferred good is unpicked), or the agents that must come before it
        sdreq = []
        for i in range(n):
            row = []
            for t, v in enumerate(H.types[i]):
                better = H.sets[i] if Y[i] is None else [g for g in H.sets[i] if v[g] > v[Y[i]]]
                row.append(None if any(g not in holder for g in better) else frozenset(holder[g] for g in better))
            sdreq.append(row)
        boxes = []
        for w in Ws:
            pk = w['picks']
            if any(Y[int(a)] != y for a, y in pk.items()): continue
            r = H.apply(Y, w)
            if r is None: continue
            nb, imp = r
            if not H.shape_ok(nb, w['_X']): continue
            key = w['X']
            if key not in efx: efx[key] = H.efx0_masks(w['_X'])
            masks = [mk.copy() for mk in efx[key]]
            for x, new_, old in imp:
                masks[x] &= H.val(x, new_) > H.val(x, old)
            boxes.append(masks)
        stats['witnesses applicable (sum over matchings)'] += len(boxes)
        # Types of agent i that the SD constraints and every box treat alike are interchangeable: one variable per
        # class (exact; a class's representative is its first type).
        cls = []
        for i in range(n):
            sig = {}
            for t in range(len(H.types[i])):
                if sdreq[i][t] is None: continue
                k = (sdreq[i][t], tuple(bool(b[i][t]) for b in boxes))
                sig.setdefault(k, []).append(t)
            cls.append(list(sig.items()))
        stats['type classes (sum over matchings and agents)'] += sum(len(c) for c in cls)
        if any(not c for c in cls): continue                 # Y is no SD outcome under any profile
        solver = Glucose4()
        top = [0]
        def new():
            top[0] += 1; return top[0]
        z = [[new() for _ in cls[i]] for i in range(n)]
        for zi in z:
            solver.add_clause(zi)
            for a, b in itertools.combinations(zi, 2): solver.add_clause([-a, -b])
        bef = {(a, b): new() for a in range(n) for b in range(n) if a != b}
        for a, b in itertools.combinations(range(n), 2):
            solver.add_clause([bef[(a, b)], bef[(b, a)]]); solver.add_clause([-bef[(a, b)], -bef[(b, a)]])
        for a, b, c in itertools.permutations(range(n), 3):
            solver.add_clause([-bef[(a, b)], -bef[(b, c)], bef[(a, c)]])
        for i in range(n):
            for k, ((req, _), ts) in enumerate(cls[i]):
                for j in req: solver.add_clause([-z[i][k], bef[(j, i)]])
        for bi, b in enumerate(boxes):
            solver.add_clause([z[i][k] for i in range(n) for k, (sg, ts) in enumerate(cls[i]) if not sg[1][bi]])
        if solver.solve():
            mod = set(l for l in solver.get_model() if l > 0)
            prof = [cls[i][next(k for k, v in enumerate(zi) if v in mod)][1][0] for i, zi in enumerate(z)]
            order = sorted(range(n), key=lambda a: sum(bef[(b, a)] in mod for b in range(n) if b != a))
            vals = [[H.types[i][t][g] for g in H.sets[i]] for i, t in enumerate(prof)]
            solver.delete()
            return rec['list'], rec['idx'], False, json.dumps({'uncovered': True, 'picks': Y, 'vals': vals, 'order': order}), len(Ys), time.time() - t0
        solver.delete()
    return rec['list'], rec['idx'], True, dict(stats), len(Ys), time.time() - t0


def main():
    path = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--') and '=' in a)
    print('$ python3 k4/oc1cert/check.py', *sys.argv[1:], flush=True)
    print('own types:', {d: len(T) for d, T in TYPES.items()}, flush=True)
    D, recs = read_records(path)
    T = collections.Counter(); t0 = time.time(); tmax = 0; ok_all = True
    seen = {}                                       # (list, m, idx) -> sets, for the completeness check
    mm = lambda S: 1 + max(g for U in S for g in U)  # idx counts within each m

    def certified():
        for r in recs:
            seen[(r['list'], mm(r['sets']), r['idx'])] = r['sets']
            if r['result'] != 'certified':
                T['not certified (failures found by the CEGAR, not checked here)'] += 1; continue
            yield r

    def batches(it, size=1000):
        b = []
        for r in it:
            b.append(r)
            if len(b) == size: yield b; b = []
        if b: yield b
    results = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for batch in batches(certified()):
            results.extend(pool.imap_unordered(check_core, batch, chunksize=4))
            for lst, idx, ok, info, nY, dt in results:
                T['covered' if ok else 'NOT COVERED'] += 1
                T['maximum matchings checked'] += nY
                tmax = max(tmax, dt)
                if ok:
                    for a, c in info.items(): T[a] += c
                else:
                    ok_all = False
                    print('NOT COVERED', lst, idx, info, flush=True)
            results = []
            print('... %d checked, %.0f s' % (T['covered'] + T['NOT COVERED'], time.time() - t0), flush=True)
    print('certificate', path, 'hypergraphs', len(seen), flush=True)
    if 'lists' in opt:
        for lst in opt['lists'].split(','):
            src = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_%s.json.gz' % lst)))['cores']
            miss = [c['idx'] for c in src if seen.get((lst, mm(c['sets']), c['idx'])) != c['sets']]
            print('list', lst, 'source hypergraphs', len(src), 'missing or different', len(miss), flush=True)
            ok_all &= not miss
    for a in sorted(T): print(a, T[a])
    print('slowest hypergraph %.2f s' % tmax)
    print('time %.0f s' % (time.time() - t0))
    print('RESULT', ('every certified hypergraph (%d) covered for every type profile and every maximum-matching SD order'
                     % T['covered']) if ok_all else 'FAILED')
    sys.exit(0 if ok_all else 1)


if __name__ == '__main__':
    main()
