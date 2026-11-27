"""What do the three-move steps look like at the known two-move failures?  (k4/haxell.md §6, "Anatomy of the
three-move steps".)  Pure Python from the raw EFX0 definition, no code shared with gstar_measure.c.

Input: logs whose lines name a failing instance and a state, in either format written by this workstream:
  COUNTEREXAMPLE <instance> | <gstar_measure output with example_phiK <state>>     (ht_wclimb.py)
  STUCK <tag> <instance> | <gstar_measure output with example_phiK <state>>          (ht_n4core.py, ht_n3grid.py)
For each (instance, state) the script
  1. re-checks that the state is partial EFX0 with a nonempty pool and has no P^sub step within two moves (Pareto:
     the pool smaller, or the same pool with no agent worse and some agent strictly better), and no step for welfare
     and leximin either where the log's measure is welfare (phi1) or leximin (phi2);
  2. lists every composite of three moves reaching a partial EFX0 allocation with a smaller pool or a Pareto
     improvement (moves of k4/haxell.md §6: set transfers from one holder to one agent, swaps of two goods' holders
     with the pool as a holder, rotations of bundles along a cycle of agents);
  3. names each composite by a pattern (agents relabelled A, B, C, ... in order of appearance) and reports, per
     instance, the patterns and the properties below.

Properties of a three-move composite X -> X1 -> X2 -> Y:
  chain:  a Haxell-type alternating path.  Move 1 brings pooled goods to an agent a1 (a transfer from the pool, or a
          swap of a pooled good with one of a1's goods); move t >= 2 is a transfer of a set of goods, or a swap of two
          goods, from a_{t-1} to an agent a_t (for a swap: between a_{t-1} and a_t).  So goods flow along a path
          pool -> a1 -> a2 -> a3.
  sideways: X1 is partial EFX0 with the same pool (so the composite is one EFX0 move followed by a two-move step
          from X1).
  through-EFX0: X1 and X2 both partial EFX0.

    python3 k4/haxell/ht_rescue.py LOG [LOG ...] [SHOW=4]"""
import sys, itertools, collections

POOL = -1


def parse_inst(ws):
    w = list(map(int, ws)); n, m = w[0], w[1]; t = 2; val = [[0] * m for _ in range(n)]; rel = [set() for _ in range(n)]
    for i in range(n):
        d = w[t]; t += 1
        for _ in range(d):
            val[i][w[t]] = w[t + 1]; rel[i].add(w[t]); t += 2
    assert t == len(w), ws
    return n, m, val, rel


def read_logs(paths):
    out = []
    for p in paths:
        for ln in open(p):
            if not (ln.startswith('COUNTEREXAMPLE') or ln.startswith('STUCK')) or '|' not in ln:
                continue
            left, right = ln.split('|', 1); lw = left.split()
            inst = lw[1:] if lw[0] == 'COUNTEREXAMPLE' else lw[2:]
            rw = right.split(); key = next(x for x in rw if x.startswith('example_phi'))
            j = rw.index(key); K = int(key[len('example_phi'):]); m = int(inst[1])
            state = tuple(int(x) for x in rw[j + 1:j + 1 + m])
            out.append((p.split('/')[-1], ' '.join(inst), state, K))
    return out


class Inst:
    def __init__(self, n, m, val):
        self.n, self.m, self.val = n, m, val
        self.cache = {}

    def bundles(self, o):
        X = [[] for _ in range(self.n)]
        for g, h in enumerate(o):
            if h >= 0:
                X[h].append(g)
        return X

    def vals(self, o):
        return tuple(sum(self.val[i][g] for g in B) for i, B in enumerate(self.bundles(o)))

    def efx0(self, o):
        r = self.cache.get(o)
        if r is None:
            X = self.bundles(o); v = self.val; r = True
            for i in range(self.n):
                mine = sum(v[i][g] for g in X[i])
                for j in range(self.n):
                    if j != i and len(X[j]) >= 2 and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > mine:
                        r = False; break
                if not r:
                    break
            self.cache[o] = r
        return r

    def moves(self, o):
        """yields (name, new state); name = (kind, data) with agents as numbers, the pool as -1"""
        n, m = self.n, self.m
        for h in list(range(n)) + [POOL]:
            G = [g for g in range(m) if o[g] == h]
            for r in range(1, len(G) + 1):
                for S in itertools.combinations(G, r):
                    for b in range(n):
                        if b != h:
                            t = list(o)
                            for g in S:
                                t[g] = b
                            yield ('T', h, b, S), tuple(t)
        for g, h in itertools.combinations(range(m), 2):
            if o[g] != o[h]:
                t = list(o); t[g], t[h] = o[h], o[g]
                yield ('S', o[g], o[h], (g, h)), tuple(t)
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] == min(cyc):
                    to = {cyc[s]: cyc[(s + 1) % L] for s in range(L)}
                    yield ('R', cyc), tuple(to.get(x, x) if x >= 0 else x for x in o)


def improving(I, o, t, measure):
    p, q = o.count(POOL), t.count(POOL)
    if q > p or not I.efx0(t):
        return False
    if q < p:
        return True
    a, b = I.vals(o), I.vals(t)
    if measure == 19:
        return all(y >= x for x, y in zip(a, b)) and any(y > x for x, y in zip(a, b))
    if measure == 1:
        return sum(b) > sum(a)
    if measure == 2:
        return sorted(b) > sorted(a)
    raise ValueError(measure)


def pattern(path):
    """agents relabelled A, B, ... in order of appearance; the pool is P; sets keep their sizes"""
    lab = {POOL: 'P'}

    def L(x):
        if x not in lab:
            lab[x] = 'ABCDEFGH'[len(lab) - 1]
        return lab[x]
    out = []
    for mv in path:
        if mv[0] == 'T':
            out.append('%s>%s%s' % (L(mv[1]), L(mv[2]), '' if len(mv[3]) == 1 else '[%d]' % len(mv[3])))
        elif mv[0] == 'S':
            a, b = L(mv[1]), L(mv[2])
            out.append('%s<>%s' % tuple(sorted((a, b), key=lambda s: (s != 'P', s))))
        else:
            out.append('R(%s)' % ''.join(L(x) for x in mv[1]))
    return ' ; '.join(out)


def is_chain(path):
    prev = None
    for t, mv in enumerate(path):
        if t == 0:
            if mv[0] == 'T' and mv[1] == POOL:
                prev = mv[2]
            elif mv[0] == 'S' and POOL in (mv[1], mv[2]):
                prev = mv[2] if mv[1] == POOL else mv[1]
            else:
                return False
        else:
            if mv[0] == 'T' and mv[1] == prev:
                prev = mv[2]
            elif mv[0] == 'S' and prev in (mv[1], mv[2]) and POOL not in (mv[1], mv[2]):
                prev = mv[2] if mv[1] == prev else mv[1]
            else:
                return False
    return True


def flow(X, Y, n):
    """the flow graph of X -> Y: for every good that changes holder, an edge (old holder, new holder); returned as
    (canonical signature with agents relabelled, shape) where shape is 'path' (the support is a directed path starting
    at the pool), 'cycle' (a directed cycle through the pool), or 'other'"""
    E = collections.Counter((a, b) for a, b in zip(X, Y) if a != b)
    best = None
    for perm in itertools.permutations(range(n)):
        f = lambda x: 'P' if x == POOL else 'ABCDEFGH'[perm[x]]
        sig = tuple(sorted((f(a) + '>' + f(b), c) for (a, b), c in E.items()))
        best = sig if best is None or sig < best else best
    sup = set(E); out = collections.defaultdict(list)
    for a, b in sup:
        out[a].append(b)
    shape = 'other'
    if all(len(v) == 1 for v in out.values()) and all(sum(1 for e in sup if e[1] == x) <= 1 for x in set(out) | {e[1] for e in sup}):
        cur, seen = POOL, []
        while cur in out and cur not in seen:
            seen.append(cur); cur = out[cur][0]
        if len(seen) == len(out):
            shape = 'cycle' if cur == POOL else 'path' if cur not in out else 'other'
    return ', '.join('%s%s' % (e, '' if c == 1 else 'x%d' % c) for e, c in best), shape


def analyse(n, m, val, X, measure):
    I = Inst(n, m, val)
    assert I.efx0(X) and POOL in X, 'not a partial EFX0 state with a nonempty pool'
    meas = sorted({19, measure})
    L1 = collections.defaultdict(list)
    for mv, t in I.moves(X):
        if t != X:
            L1[t].append(mv)
    for K in meas:
        assert not any(improving(I, X, t, K) for t in L1), ('one-move step', K)
    L2 = collections.defaultdict(list)
    for t1 in L1:
        for mv, t2 in I.moves(t1):
            if t2 != X:
                L2[t2].append((t1, mv))
    for K in meas:
        assert not any(improving(I, X, t, K) for t in L2), ('two-move step', K)
    paths = []; ends = collections.Counter()
    for t2, preds in L2.items():
        for mv3, y in I.moves(t2):
            if y == X or not improving(I, X, y, 19):
                continue
            for t1, mv2 in preds:
                for mv1 in L1[t1]:
                    paths.append(((mv1, mv2, mv3), (t1, t2, y)))
            ends[y] += 1
    return I, paths, ends


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if '=' not in a]
    kw = dict(a.split('=') for a in sys.argv[1:] if '=' in a); SHOW = int(kw.get('SHOW', '4'))
    print('$ python3 k4/haxell/ht_rescue.py', *sys.argv[1:], flush=True)
    seen = set(); tot = collections.Counter(); allpat = collections.Counter(); allflow = collections.Counter()
    for src, inst, X, K in read_logs(args):
        if (inst, X) in seen:
            continue
        seen.add((inst, X)); n, m, val, rel = parse_inst(inst.split())
        I, paths, ends = analyse(n, m, val, X, K)
        chain = [p for p in paths if is_chain(p[0])]
        side = [p for p in paths if I.efx0(p[1][0]) and p[1][0].count(POOL) == X.count(POOL)]
        thru = [p for p in paths if I.efx0(p[1][0]) and I.efx0(p[1][1])]
        shrink = [p for p in paths if p[1][2].count(POOL) < X.count(POOL)]
        pats = collections.Counter(pattern(p[0]) for p in paths)
        fl = collections.Counter(flow(X, y, n) for y in ends)
        tot['with a path end state'] += any(sh == 'path' for _, sh in fl)
        tot['with a path or pool-cycle end state'] += any(sh in ('path', 'cycle') for _, sh in fl)
        for (sig, sh) in fl:
            allflow[(sig, sh)] += 1
        chainpats = collections.Counter(pattern(p[0]) for p in chain)
        tot['failures'] += 1; tot['with a chain'] += bool(chain); tot['with a sideways start'] += bool(side)
        tot['with a composite through EFX0 states'] += bool(thru); tot['with a pool-shrinking composite'] += bool(shrink)
        for pt in pats:
            allpat[pt] += 1
        print('%s n=%d m=%d phi%d state %s pool %d | rescuing 3-move composites %d, end states %d, chains %d, '
              'sideways %d, through EFX0 %d, pool-shrinking %d' % (src, n, m, K, X, X.count(POOL), len(paths), len(ends),
                                                                  len(chain), len(side), len(thru), len(shrink)))
        print('   instance', inst)
        for (sig, sh), c in sorted(fl.items(), key=lambda x: (x[0][1] != 'path', x[0][1] != 'cycle', x[0][0]))[:SHOW]:
            print('   end state flow %-40s %s%s' % (sig, sh, '' if c == 1 else '  (%d end states)' % c))
        for pt, c in pats.most_common(SHOW):
            print('   pattern %-40s %d%s' % (pt, c, '  (chain)' if pt in chainpats else ''))
        for pt, c in chainpats.most_common(2):
            if pt not in dict(pats.most_common(SHOW)):
                print('   chain   %-40s %d' % (pt, c))
    print('TOTAL', dict(tot))
    print('end-state flows occurring at the most failures:')
    for (sig, sh), c in allflow.most_common(12):
        print('   %-40s %-6s at %d failures' % (sig, sh, c))
    print('patterns occurring at the most failures:')
    for pt, c in allpat.most_common(12):
        print('   %-40s at %d failures' % (pt, c))
