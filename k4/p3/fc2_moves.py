"""Forest chains (k4/p3/fc2cert.py, Conjecture FC2) by my own enumeration, for replays: an official chain in which a
receiver x_i that adds junk (H_i nonempty) takes the base of an agent unfrozen at the current bases; additions are
listed too. Shares no code with k4/oc1cert/.
    python3 k4/p3/fc2_moves.py FILE [FILE ...]    (as k4/p3/fk2.py: hard-start jsonl[.gz] or a certificate's failures)
reports, for every hard start, whether some addition or forest chain leaves bases with a one-absorber completion (SAT,
k4/p3/oc1max.Checker.complete, models re-checked raw).
"""
import sys, os, itertools, collections, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker
from fk2 import starts, subsets


def frozen(I, base, x):
    return any(j != x and I.val(j, base[x]) > I.val(j, base[j]) for j in range(I.n))


def fc_moves(I, base):
    """{state: (kind, length)} for every addition and forest chain from base"""
    n = I.n; V = I.val
    held = set().union(*base); J = [g for g in range(I.m) if g not in held]
    out = {}
    def add(nb, tag):
        key = tuple(frozenset(b) for b in nb)
        if key not in out or tag < out[key]: out[key] = tag
    for x in range(n):
        for H in subsets([g for g in J if g in I.R[x]], 1):
            nb = list(base); nb[x] = base[x] | set(H); add(nb, ('addition', 1))
    fr = [frozen(I, base, x) for x in range(n)]
    def ext(path, used, take):
        xt = path[-1]
        if len(path) >= 2:
            x0 = path[0]
            pool = [g for g in J if g not in used and g in I.R[x0]] + [g for g in base[xt] if g in I.R[x0]]
            for H0 in subsets(pool, 1):
                if V(x0, H0) > V(x0, base[x0]):
                    nb = list(base); nb[x0] = frozenset(H0)
                    for i in range(1, len(path)): nb[path[i]] = base[path[i - 1]] | take[i]
                    add(nb, ('forest chain', len(path)))
        if not base[xt] or len(path) >= n: return
        for y in range(n):
            if y in path: continue
            for H in subsets([g for g in J if g not in used and g in I.R[y]]):
                if H and fr[xt]: continue                     # junk only on top of an unfrozen agent's base
                if V(y, base[xt] | set(H)) > V(y, base[y]):
                    ext(path + [y], used | set(H), {**take, len(path): frozenset(H)})
    for x in range(n): ext([x], frozenset(), {})
    return out


if __name__ == '__main__':
    cnt = collections.Counter()
    print('$ python3 k4/p3/fc2_moves.py ' + ' '.join(sys.argv[1:]))
    for path in sys.argv[1:]:
        for sets, vals, m, Y in starts(path):
            I = Inst(sets, vals, m); K = Checker(I)
            base = tuple(frozenset([y]) for y in Y)
            if K.complete(base) is not None: K.close(); cnt['not hard (skipped)'] += 1; continue
            cnt['hard starts'] += 1
            best = None
            for st, tag in fc_moves(I, base).items():
                if K.complete(st) is not None and (best is None or tag < best): best = tag
            cnt['repaired by: ' + ('%s of %d' % best if best else 'NO FOREST CHAIN OR ADDITION')] += 1
            if best is None: print('FC2 FAILS', json.dumps({'sets': sets, 'vals': vals, 'picks': Y}))
            K.close()
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
