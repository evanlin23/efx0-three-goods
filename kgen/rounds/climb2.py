"""Climb toward starts that need THREE rounds at strictly positive values (RD2+ test, kgen/rounds.md §4).

One-round failures are found by rnd.c (fast); for each such start the number of complete EFX allocations reachable
by at most two rounds of vertex-disjoint chains is counted (capped) with k4/ksens/ocseq.py's c-round encoding
(multi=True; branch claude/k4-ksens at 63089336, path $KSENS), blocking each found allocation.  Objective (minimized):
  (-#starts failing two rounds, min over one-round-failing starts of the two-round count, -#one-round-failing starts,
   min RND1 count over all starts, its margin sum)

    python3 kgen/rounds/climb2.py SEEDFILE.jsonl STEPS ROUNDS SEED [A=1|free]
Every candidate (a start failing two rounds) is printed as CAND3 and must be confirmed (bruter.py two rounds).
"""
import sys, os, json, random, time, itertools, zlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rndlib
KS = os.environ.get('KSENS', '/tmp/claude-0/-home-user-efx0-three-goods/1bef8951-d60e-5a6c-a841-d862b0933832/scratchpad/ksens')
sys.path.insert(0, os.path.join(KS, 'k4', 'ksens')); sys.path.insert(0, os.path.join(KS, 'k4', 'sdc'))
import ocsat, ocseq

VMAX = int(os.environ.get('VMAX', '6000'))
CAP = int(os.environ.get('CAP2', '25'))


class Seq2(ocseq.Seq):
    def count(self, base, c, A=None, cap=CAP, multi=True):
        """number of distinct complete EFX allocations X reachable by <= c rounds then a completion (<= cap)"""
        act = self.new(); cl = []
        add = lambda c_: cl.append(c_ + [-act])
        owner = {}
        for i, b in enumerate(base):
            for g in b: owner[g] = i
        own = lambda g, i, _o=owner: (_o.get(g) == i)
        for t in range(c): own = self.layer(add, own, multi)
        E = self.E
        for g in range(self.m):
            for i in range(self.n):
                l = own(g, i)
                if l is True: add([E.x[g][i]])
                elif l is not False: add([-l, E.x[g][i]])
        if A is not None:
            bigs = []
            for i in range(self.n):
                b = self.new(); bigs.append(b)
                for g, h in itertools.combinations(range(self.m), 2):
                    c1 = [-E.x[g][i], -E.x[h][i], b]
                    for q in (g, h):
                        l = own(q, i)
                        if l is True: c1 = None; break
                        if l is not False: c1.append(l)
                    if c1: add(c1)
            for comb in itertools.combinations(bigs, A + 1): add([-x for x in comb])
        for c_ in cl: self.S.add_clause(c_)
        k = 0
        while k < cap and self.S.solve(assumptions=[act]):
            mdl = set(l for l in self.S.get_model() if l > 0)
            blk = [-act]
            for g in range(self.m):
                for i in range(self.n):
                    if E.x[g][i] in mdl: blk.append(-E.x[g][i])
            self.S.add_clause(blk); k += 1
        self.S.add_clause([-act])
        return k


def evaluate(V, A):
    res, ne = rndlib.analyze(V)
    n, m = len(V), len(V[0])
    fail1 = [r for r in res if r['counts']['RND1'] == 0]
    h = min(res, key=lambda r: (r['counts']['RND1'], r['msum']))
    c2 = []
    if fail1:
        sets = [list(range(m)) for _ in range(n)]
        Q = Seq2(sets, V, m)
        for r in fail1:
            c2.append(Q.count(ocsat.bases_of(list(r['picks']), n), 2, A))
        Q.close()
    f2 = sum(1 for c in c2 if c == 0)
    key = (-f2, min(c2) if c2 else CAP + 1, -len(fail1), h['counts']['RND1'], round(h['msum'], 9))
    return key, fail1, c2


def main():
    seedfile, steps, rounds = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    seed = int(sys.argv[4]) if sys.argv[4].isdigit() else zlib.crc32(sys.argv[4].encode())
    A = None if 'free' in sys.argv[5:] else 1
    rng = random.Random(seed); t0 = time.time()
    seeds = [json.loads(l) for l in open(seedfile)]
    print('$ python3 kgen/rounds/climb2.py', *sys.argv[1:], '| seeds', len(seeds), 'A', A, flush=True)
    for r in range(rounds):
        V = [list(x) for x in rng.choice(seeds)['vals']]
        n, m = len(V), len(V[0])
        c, f1, c2 = evaluate(V, A)
        for s in range(steps):
            V2 = [list(x) for x in V]; i = rng.randrange(n); g = rng.randrange(m); u = rng.random()
            if u < 0.6: V2[i][g] = max(1, min(VMAX, V2[i][g] + rng.choice([-100, -30, -10, -3, -1, 1, 3, 10, 30, 100])))
            elif u < 0.85:
                h = rng.randrange(m); V2[i][g], V2[i][h] = V2[i][h], V2[i][g]
            else: V2[i][g] = rng.randint(1, VMAX)
            c2_, f1_, cc_ = evaluate(V2, A)
            if c2_ <= c:
                V, c, f1, c2 = V2, c2_, f1_, cc_
                if c[0] < 0:
                    for x, k in zip(f1, c2):
                        if k == 0:
                            print('CAND3 vals', json.dumps(V), 'picks', list(x['picks']), 'order', list(x['order']), flush=True)
                    break
        print('round', r, 'final', c, 'one-round failing starts', [list(x['order']) for x in f1], 'two-round counts', c2,
              'vals', json.dumps(V), 'time %.0f' % (time.time() - t0), flush=True)
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
