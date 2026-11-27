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
- With OC1_SSTAR=1 every completion must have the S* shape of k4/oc1_hall.md §2 (claude/k4-oc1-hall), with the
  witness's declared owner.  Every other junk receiver must hold at most one base good and one junk good, and
  no other agent may prefer that base good to its own base (a type mask).
- With OC1_R2=m, star, o or c it checks TTC's R2-M, R2*, R2-O or R2-C (k4/ttc.md §14.6), at perfect starts only.
  - R2-O (o): the one-absorber owner is a receiver off the chain.  og: or no owner at all (nobody takes two junk
    goods).  op (R2-O'): the owner, if any, is a receiver other than the chain's end, on or off the chain.
  - R2-C: any one-absorber completion.
  - (S) / (L) / either (s, l, sl): (S) is a canonical chain without junk for x_1..x_t.  (L) is one in which a middle
    agent that was dangerous at the start takes junk and another middle agent is a receiver; the witness names those
    agents.  The completion has one absorber.
  - R2-E (e, e2, eo): the chain is the earliest-wanter chain E(x0) of the witness's recorded SD order (whose SD
    region is checked).  x0 takes an improving T and nobody else takes junk.  Variants: e2, |T| = 2; eo, the owner
    is a receiver.
  - Only profiles with at least two receivers count (a receiver is an agent whose pick no other agent prefers to its
    own).
  - Witnesses are completions of the picks (one absorber) or single canonical chains: x0 values a junk good, x1
    prefers x0's pick to its own, and the end is a receiver.  Their completion gives nobody two junk goods; for R2-M,
    holders of two or more base goods other than x0 get none.
  - The canonical and receiver conditions are type masks.
- With OC1_PRIME=1 it also accepts OC1' chains (kind 'chainp', kgen/rounds.md §4.6 on proof/kgen-rounds).  A non-end
  agent may then also take goods of the end's base; the end takes junk only.  Without the flag such witnesses are
  invalid.
- A record may list 'excluded' (type profile, picks) pairs, the known failures of export_fails.py.  These may stay
  uncovered, and every other pair must be covered; so the list of failures is complete.

    python3 k4/oc1cert/check.py CERT.json.gz [--lists=LIST,...]   (with --lists, also check that the certificate has
                                                                   every hypergraph of results/k4_certs_<LIST>.json.gz)"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import numpy as np
from pysat.solvers import Glucose4

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PRIME = os.environ.get('OC1_PRIME') == '1'      # accept OC1' chains (kgen/rounds.md §4.6) only when asked
SSTAR = os.environ.get('OC1_SSTAR') == '1'      # require S*-shaped completions (k4/oc1_hall.md §2)
R2 = os.environ.get('OC1_R2')                   # 'm' or 'star': TTC's R2-M / R2* (k4/ttc.md §14.6)


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

    def sig(self, i, v):
        """the order type of the values v (dict good -> value) of agent i: signs over disjoint nonempty pairs"""
        S = self.sets[i]; d = len(S); out = []
        for A in range(1, 1 << d):
            for B in range(A + 1, 1 << d):
                if A & B: continue
                a = sum(v[S[p]] for p in range(d) if A >> p & 1); b = sum(v[S[p]] for p in range(d) if B >> p & 1)
                out.append((a > b) - (a < b))
        return tuple(out)

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
        if kind == 'chain' or (kind == 'chainp' and PRIME):
            # chainp (OC1', only with --prime): non-end agents may also take goods of the end's base
            t = len(path) - 1
            if t < 1: return None
            if any(not base[path[i]] for i in range(t)): return None
            endb = set(base[path[t]]) if kind == 'chainp' else set()
            for i in range(1, t + 1):
                if not set(H[i]) <= ((J | (endb if i < t else set())) & R[path[i]]): return None
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
    if R2 and nu < n: return rec['list'], rec['idx'], True, {'R2: no perfect start (vacuous)': 1}, 0, time.time() - t0
    Ws = rec['witnesses']
    for w in Ws: w['_X'] = [int(c) for c in w['X']]
    # optional excluded (type profile, picks) pairs (known failures, e.g. export_fails.py): they may stay uncovered
    excl = collections.defaultdict(list)
    if rec.get('excluded'):
        tix = [{H.sig(i, v): t for t, v in enumerate(H.types[i])} for i in range(n)]     # H.types[i][t]: good -> value
        for e in rec['excluded']:
            excl[tuple(e['picks'])].append(tuple(tix[i][H.sig(i, dict(zip(H.sets[i], e['vals'][i])))] for i in range(n)))
    efx = {}
    stats = collections.Counter()
    # Prefilter (exact for validity): a witness can apply at Y only if every agent outside its recorded picks keeps
    # its pick inside its X bundle (H.shape_ok needs X to contain the bases), and every recorded pick matches Y.
    # allow[i][g]: bitset of the witnesses that allow Y_i = g (g = None: no pick).
    allow = [collections.defaultdict(int) for _ in range(n)]
    for k, w in enumerate(Ws):
        bit = 1 << k; fixed = {int(a): y for a, y in w['picks'].items()}; X = w['_X']
        for i in range(n):
            if i in fixed: allow[i][fixed[i]] |= bit
            else:
                allow[i][None] |= bit
                for g in H.sets[i]:
                    if X[g] == i: allow[i][g] |= bit
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
        cand = -1
        for i in range(n): cand &= allow[i].get(Y[i], 0)
        for k in range(len(Ws)) if cand else ():
            if not cand >> k & 1: continue
            w = Ws[k]
            pk = w['picks']
            if any(Y[int(a)] != y for a, y in pk.items()): continue
            if R2 and w['kind'] not in ('picks', 'chain'): continue
            r = H.apply(Y, w)
            if r is None: continue
            nb, imp = r
            if not H.shape_ok(nb, w['_X']): continue
            key = w['X']
            if key not in efx: efx[key] = H.efx0_masks(w['_X'])
            masks = [mk.copy() for mk in efx[key]]
            for x, new_, old in imp:
                masks[x] &= H.val(x, new_) > H.val(x, old)
            if R2 and w['kind'] == 'chain':
                # a canonical chain: x0 frozen and valuing a junk good, x1 preferring x0's pick to its own (so x0 is
                # frozen), the end a receiver (nobody prefers its pick); then the R2 completion shape
                path = w['path']; x0, x1, zz = path[0], path[1], path[-1]
                held = {y for y in Y if y is not None}
                if not any(g not in held for g in H.R[x0]): continue
                masks[x1] &= H.V[x1][:, Y[x0]] > H.V[x1][:, Y[x1]]
                for i in range(n):
                    if i != zz: masks[i] &= H.V[i][:, Y[zz]] <= H.V[i][:, Y[i]]
                X = w['_X']; inb = {g for b in nb for g in b}
                cnt = collections.Counter(X[g] for g in range(H.m) if g not in inb)
                if R2 in ('s', 'l', 'sl'):
                    # (S): no junk for x_1..x_t.  (L): the witness's tags (a, wn, rj): a a middle agent taking junk,
                    # wn preferring a's pick to its own (so a is frozen; it values junk since it takes some), rj a
                    # middle receiver.  The completion: one absorber (shape_ok).
                    is_s = all(not w['H'][l] for l in range(1, len(path)))
                    tg = w.get('tags')
                    if R2 == 's' and not is_s: continue
                    if not is_s:
                        if R2 == 's' or tg is None: continue
                        a, wn, rj = tg
                        mid = path[1:-1]
                        if a not in mid or rj not in mid or wn == a or not w['H'][path.index(a)]: continue
                        masks[wn] &= H.V[wn][:, Y[a]] > H.V[wn][:, Y[wn]]
                        for i in range(n):
                            if i != rj: masks[i] &= H.V[i][:, Y[rj]] <= H.V[i][:, Y[i]]
                elif R2 in ('e', 'e2', 'eo'):
                    # R2-E: the chain is E(x0) for the recorded SD order sigma (which must give Y), with no junk for
                    # x_1..x_t, x0 taking an improving T (apply's comparison) within (J + {Y_z})
                    sigma = w.get('order')
                    if sigma is None or sorted(sigma) != list(range(n)) or any(w['H'][l] for l in range(1, len(path))): continue
                    if R2 == 'e2' and len(w['H'][0]) != 2: continue
                    taken = set()
                    for a in sigma:
                        rest = [g for g in H.sets[a] if g not in taken]
                        masks[a] &= np.array([(max(rest, key=lambda g: v[g]) if rest else None) == Y[a] for v in H.types[a]])
                        if Y[a] is not None: taken.add(Y[a])
                    pos = {a: q for q, a in enumerate(sigma)}
                    for l in range(1, len(path)):
                        prev = path[l - 1]
                        for i in sigma[:pos[path[l]]]:
                            if i != prev: masks[i] &= H.V[i][:, Y[prev]] <= H.V[i][:, Y[i]]
                    if R2 == 'eo':
                        u = w.get('owner')
                        if u is None:
                            if any(c >= 2 for c in cnt.values()): continue
                        else:
                            if any(c >= 2 for a, c in cnt.items() if a != u): continue
                            for i in range(n):
                                if i != u: masks[i] &= H.V[i][:, Y[u]] <= H.V[i][:, Y[i]]
                elif R2 in ('m', 'star'):
                    if any(c >= 2 for c in cnt.values()): continue
                    if R2 == 'm' and any(a != x0 and len(nb[a]) >= 2 for a in cnt): continue
                elif R2 in ('o', 'og', 'op'):     # the declared owner: a receiver at the picks, off the chain
                    u = w.get('owner')                # ('op': any receiver other than the chain's end)
                    if u is None:              # 'og', 'op': no owner, nobody takes two junk goods
                        if R2 == 'o' or any(c >= 2 for c in cnt.values()): continue
                    else:
                        if (u in path if R2 != 'op' else u == path[-1]) or any(c >= 2 for a, c in cnt.items() if a != u): continue
                        for i in range(n):
                            if i != u: masks[i] &= H.V[i][:, Y[u]] <= H.V[i][:, Y[i]]
                # R2 == 'c': the one-absorber shape, already checked by shape_ok
            if SSTAR:
                # S*: every junk receiver other than the declared owner holds at most one base good and one junk
                # good, and no other agent prefers its base good to its own base
                o = w.get('owner'); X = w['_X']
                inb = {g for b in nb for g in b}
                cnt = collections.Counter(X[g] for g in range(H.m) if g not in inb)
                if o is None or any(c >= 2 for a, c in cnt.items() if a != o) or any(len(nb[a]) >= 2 for a in cnt if a != o):
                    continue
                for j in cnt:
                    if j == o or not nb[j]: continue
                    g = nb[j][0]
                    for i in range(n):
                        if i != j: masks[i] &= H.val(i, nb[i]) >= H.V[i][:, g]
            boxes.append(masks)
        stats['witnesses applicable (sum over matchings)'] += len(boxes)
        # Types of agent i that the SD constraints and every box treat alike are interchangeable: one variable per
        # class (exact; a class's representative is its first type).
        if R2:      # nw[j][i]: the types of agent i under which it does not prefer Y_j to its own pick
            nw = [[(H.V[i][:, Y[j]] <= H.V[i][:, Y[i]]) if i != j else np.ones(len(H.types[i]), dtype=bool)
                   for i in range(n)] for j in range(n)]
        cls = []
        for i in range(n):
            sig = {}
            for t in range(len(H.types[i])):
                if sdreq[i][t] is None: continue
                k = (sdreq[i][t], tuple(bool(b[i][t]) for b in boxes), tuple(e[i] == t for e in excl[Y]),
                     tuple(bool(nw[j][i][t]) for j in range(n)) if R2 else ())
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
            for k, ((req, *_), ts) in enumerate(cls[i]):
                for j in req: solver.add_clause([-z[i][k], bef[(j, i)]])
        # one literal per distinct agent mask (yl <-> the agent's class lies in the mask): each box is the clause
        # "some agent's yl is false", and learned clauses speak about masks
        ylit = {}
        def yl(i, bi):
            key = (i, tuple(k for k, (sg, ts) in enumerate(cls[i]) if sg[1][bi]))
            if key not in ylit:
                v = ylit[key] = new()
                solver.add_clause([-v] + [z[i][k] for k in key[1]])
                for k in key[1]: solver.add_clause([-z[i][k], v])
            return ylit[key]
        for bi, b in enumerate(boxes):
            solver.add_clause([-yl(i, bi) for i in range(n)])
        if R2:      # at least two receivers: rec_j -> every other agent's class lies in nw[j]
            rcv = [new() for _ in range(n)]
            for j in range(n):
                for i in range(n):
                    if i == j: continue
                    for k, (sg, ts) in enumerate(cls[i]):
                        if not sg[3][j]: solver.add_clause([-rcv[j], -z[i][k]])
            for a in range(n):    # at least two receivers: for every agent a, some receiver other than a
                solver.add_clause([r_ for b, r_ in enumerate(rcv) if b != a])
        cidx = [{t: k for k, (sg, ts) in enumerate(cls[i]) for t in ts} for i in range(n)]
        for e in excl[Y]:        # the excluded profile's types are singleton classes (their signature bit)
            if all(e[i] in cidx[i] for i in range(n)):
                solver.add_clause([-z[i][cidx[i][e[i]]] for i in range(n)])
        stats['excluded pairs'] += len(excl[Y])
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
    what = ('every perfect SD start with at least two receivers (R2-%s)' % R2) if R2 else 'every maximum-matching SD order'
    print('RESULT', ('every certified hypergraph (%d) covered for every type profile and %s' % (T['covered'], what))
          if ok_all else 'FAILED')
    sys.exit(0 if ok_all else 1)


if __name__ == '__main__':
    main()
