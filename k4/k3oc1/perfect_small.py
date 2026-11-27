"""Statement (P) of k4/k3_oc1.md §11 on its whole class: agents valuing one, two or three goods (strictly balanced
when three), at perfect starts (every agent picks).  Null agents are left out: a null agent can always receive
nothing, so instances without them are the hardest case.  Exhaustive over hypergraph classes (sets of sizes 1-3, up
to relabelling), every ranking, every order's draft; brute-force one-absorber completion; every improving move
(k3lib.chains, official rule: no pass through an empty-handed agent).
    python3 k4/k3oc1/perfect_small.py N [DEAD [SHARD NSHARDS]]"""
import sys, os, itertools, collections, time, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, completion, chains, vals
from oc1_fast import drafts

def gen_mixed(n):
    out = []
    def rec(sets, m):
        if len(sets) == n: out.append(([list(s) for s in sets], m)); return
        for size in (1, 2, 3):
            for k_new in range(0, size + 1):
                for old in itertools.combinations(range(m), size - k_new):
                    s = tuple(sorted(old + tuple(range(m, m + k_new))))
                    if sets and (len(s), s) < (len(sets[-1]), sets[-1]): continue
                    rec(sets + [s], m + k_new)
    rec([], 0); return out

def canon(sets, n):
    m = 1 + max(max(s) for s in sets)
    inc = [[a for a in range(n) if g in sets[a]] for g in range(m)]
    return min((tuple(sorted(len(sets[p.index(a)]) for a in range(n))), tuple(sorted(tuple(sorted(p[a] for a in I)) for I in inc)))
               for p in itertools.permutations(range(n)))

if __name__ == '__main__':
    n = int(sys.argv[1]); dead = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    shard, nsh = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 1)
    reps = {}
    for sets, m in gen_mixed(n): reps.setdefault(canon(sets, n), (sets, m))
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/k3oc1/perfect_small.py', *sys.argv[1:], '(%d classes)' % len(reps), flush=True)
    for ci, key in enumerate(sorted(reps)):
        if ci % nsh != shard: continue
        sets, m = reps[key]; m2 = m + dead; C['hypergraphs'] += 1
        for rk in itertools.product(*[list(itertools.permutations(s)) for s in sets]):
            V = vals(rk); C['profiles'] += 1
            for Y in drafts(rk, n):
                if any(g is None for g in Y): continue
                C['perfect drafts'] += 1; b = base_of(Y, m2)
                if completion(rk, m2, b, 1, V) is not None: continue
                C['hard'] += 1
                if any(completion(rk, m2, nb, 1, V) is not None for nb, d in chains(rk, m2, b, V)): continue
                C['ONE MOVE FAILS'] += 1
                print('FAIL', json.dumps([list(r) for r in rk]), m2, 'picks', Y, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
