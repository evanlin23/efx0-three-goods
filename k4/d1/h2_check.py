"""Conjecture D1-H2 (k4/d1.md §7) on recorded hard starts: at a one-absorber-hard start with D = {k} at which every
canonical chain from k has HEAD, some canonical chain P = (x_0, ..., x_{t-1}, u) from k, or its extension
(x_0, ..., x_{t-1}, u, u2) by another wanter u2 of a = Y_{x_{t-1}} that takes Y_u plus junk S (improving for u2), with an
inclusion-minimal improving H0 for k, leaves an S* completion owned by k (raw EFX0).

    python3 k4/d1/h2_check.py FILE.jsonl[.gz] ...
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from d1lib import open_records, Inst, Start, canonical_chains, pool, sstar, obstacles, minimal_improving, one_absorber


def mins(S, k, Pi):
    I = S.I; Pk = [g for g in Pi if g in I.R[k]]
    imp = [frozenset(H) for r in range(1, len(Pk) + 1) for H in itertools.combinations(Pk, r) if I.val(k, H) > S.p[k]]
    return [H for H in imp if not any(K < H for K in imp)]


def h2_repairs(S, k):
    I = S.I; Y = S.Y; out = []
    for path in canonical_chains(S, k):
        u = path[-1]; a = Y[path[-2]]
        B = [list(b) for b in S.B]
        for i in range(1, len(path)): B[path[i]] = [Y[path[i - 1]]]
        for H0 in mins(S, k, pool(S, path)):
            B2 = [list(b) for b in B]; B2[k] = sorted(H0)
            if sstar(I, B2, k): out.append(('canonical', path, sorted(H0)))
        for u2 in S.W[path[-2]]:
            if u2 in path or u2 in S.F: continue
            for r in range(0, 3):
                for Sj in itertools.combinations([g for g in S.J if g in I.R[u2]], r):
                    if I.val(u2, [Y[u]] + list(Sj)) <= S.p[u2]: continue
                    Pi = [g for g in S.J if g not in Sj] + [Y[u2]]
                    for H0 in mins(S, k, Pi):
                        B2 = [list(b) for b in B]; B2[u2] = [Y[u]] + list(Sj); B2[k] = sorted(H0)
                        if sstar(I, B2, k): out.append(('double', path + (u2,), list(Sj), sorted(H0)))
    return out


if __name__ == '__main__':
    C = collections.Counter(); seen = set()
    print('$ python3 k4/d1/h2_check.py', *sys.argv[1:], flush=True)
    for fn in sys.argv[1:]:
        for rec in open_records(fn):
            key = json.dumps((rec['sets'], rec['vals'], rec['picks']))
            if key in seen: continue
            seen.add(key)
            I = Inst(rec['sets'], rec['vals'], rec['m']); S = Start(I, tuple(rec['picks']))
            if len(S.D) != 1: continue
            k = S.D[0]; ch = canonical_chains(S, k)
            if not ch or not all(obstacles(S, p, minimal_improving(S, k, pool(S, p))[0])[0] for p in ch): continue
            if one_absorber(I, S.B): continue
            reps = h2_repairs(S, k)
            C['all-HEAD hard starts'] += 1
            C['  repaired by a canonical chain'] += any(r[0] == 'canonical' for r in reps)
            C['  repaired only by a double chain'] += bool(reps) and not any(r[0] == 'canonical' for r in reps)
            if not reps:
                C['  D1-H2 FAILS'] += 1; print('D1-H2 FAILS', json.dumps((rec['sets'], rec['vals'])), rec['picks'], flush=True)
    for kk in sorted(C): print(kk, C[kk])
