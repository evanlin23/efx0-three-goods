"""Finding D1 with at most one junk good at the head (k4/d1.md §5, Conjecture D1-HJ), on every one-absorber-hard start
with D = {k} recorded in the given JSONL files (and, with ALL=1, on every such start of the recorded instances' orders):
some canonical chain P from k, with the head taking a = Y_{x_{t-1}} plus at most one junk good h (h = none: the
canonical chain), and some inclusion-minimal improving H0 inside (Pi - h) & R_k, leaves an S* completion owned by k.
Reports separately the all-HEAD starts (every canonical chain has HEAD), where Theorem D1-C does not apply.

    python3 k4/d1/headjunk_check.py FILE.jsonl ...
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from d1lib import open_records, Inst, Start, canonical_chains, pool, sstar, obstacles, minimal_improving, one_absorber


def hj_repairs(S, k):
    I = S.I; Y = S.Y; out = []
    for path in canonical_chains(S, k):
        z = path[-1]; a = Y[path[-2]]
        for h in [None] + list(S.J):
            Pi = [g for g in pool(S, path) if g != h]; Pk = [g for g in Pi if g in I.R[k]]
            imp = [frozenset(H) for r in range(1, len(Pk) + 1) for H in itertools.combinations(Pk, r) if I.val(k, H) > S.p[k]]
            for H0 in [H for H in imp if not any(K < H for K in imp)]:
                B = [list(b) for b in S.B]
                for i in range(1, len(path)): B[path[i]] = [Y[path[i - 1]]]
                if h is not None: B[z] = [a, h]
                B[k] = sorted(H0)
                if sstar(I, B, k): out.append((path, h, sorted(H0)))
    return out


if __name__ == '__main__':
    C = collections.Counter(); seen = set()
    print('$ python3 k4/d1/headjunk_check.py', *sys.argv[1:], flush=True)
    for fn in sys.argv[1:]:
        for rec in open_records(fn):
            key = json.dumps((rec['sets'], rec['vals'], rec['picks']))
            if key in seen: continue
            seen.add(key)
            I = Inst(rec['sets'], rec['vals'], rec['m']); S = Start(I, tuple(rec['picks']))
            if len(S.D) != 1 or one_absorber(I, S.B): continue
            k = S.D[0]; ch = canonical_chains(S, k)
            allhead = all(obstacles(S, p, minimal_improving(S, k, pool(S, p))[0])[0] for p in ch)
            tag = 'all-HEAD' if allhead else 'some chain without HEAD'
            reps = hj_repairs(S, k)
            C['%s hard starts' % tag] += 1
            C['%s   repaired by a canonical chain' % tag] += any(h is None for p, h, H0 in reps)
            C['%s   repaired with head junk only' % tag] += bool(reps) and not any(h is None for p, h, H0 in reps)
            if not reps:
                C['%s   NOT REPAIRED (D1-HJ fails)' % tag] += 1
                print('D1-HJ FAILS', json.dumps((rec['sets'], rec['vals'])), rec['picks'], flush=True)
    for kk in sorted(C): print(kk, C[kk])
