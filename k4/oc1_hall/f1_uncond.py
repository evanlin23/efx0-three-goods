"""Unconditional forms of Finding F1 (k4/oc1_hall.md §5).  Over EVERY start with exactly one frozen agent x (hard or
not), with W the wanters of Y_x and an improving set of x a set H_0 of (J + {Y_w}) inside R_x with v_x(H_0) > p_x:
  T1: if some w has an improving set, then for some w and some inclusion-minimal improving H_0, the swap has an S*
      completion with owner x;
  T2: if no w has an improving set, the picks have an S* completion (and with which owners);
  rules by case (|W|, smallest |H_0|): every/some minimal H_0 with owner x; with an owner outside {x, w}; with owner w.

    python3 k4/oc1_hall/f1_uncond.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of
from chain_shapes import s_star_owners
from min_frozen import load


def swaps(I, P, base, x, w):
    Y = P.Y
    pool = [g for g in P.J if g in I.R[x]] + ([Y[w]] if Y[w] is not None and Y[w] in I.R[x] else [])
    imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if I.val(x, H) > P.pv[x]]
    minimal = [H for H in imp if not any(set(K) < set(H) for K in imp)]
    out = []
    for H0 in minimal:
        nb = list(base); nb[Y[x]] = w
        if Y[w] is not None: nb[Y[w]] = -1
        for g in H0: nb[g] = x
        out.append((H0, tuple(nb)))
    return out


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/f1_uncond.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.F) != 1: continue
            x = P.F[0]; W = P.W[x]; base = base_of_picks(I, Y)
            allsw = {w: swaps(I, P, base, x, w) for w in W}
            if not any(allsw.values()):
                C['T2 starts (no improving set)'] += 1
                ow = s_star_owners(I, base)
                C['T2 picks complete'] += bool(ow)
                C['T2 picks complete with a wanter as owner'] += any(o in W for o in ow)
                if not ow: print('T2 FAILS', name, json.dumps((sets, vals)), 'picks', Y, 'x', x, flush=True)
                continue
            hmin = min(len(H) for sw in allsw.values() for H, _ in sw)
            key = '|W|=%d min|H0|=%d n=%d' % (len(W), hmin, n)
            C['T1 starts'] += 1; C[key + ': starts'] += 1
            res = {(w, H0): s_star_owners(I, nb) for w, sw in allsw.items() for H0, nb in sw}
            okx = any(x in o for o in res.values())
            C['T1 holds (some minimal swap, owner x)'] += okx
            C[key + ': some minimal swap, owner x'] += okx
            C[key + ': every minimal swap, owner x'] += all(x in o for o in res.values())
            C[key + ': some minimal swap, some owner'] += any(res.values())
            C[key + ': some minimal swap, owner outside {x, w}'] += any(set(o) - {x, w} for (w, H0), o in res.items())
            C[key + ': some minimal swap, owner w'] += any(w in o for (w, H0), o in res.items())
            C[key + ': picks complete'] += bool(s_star_owners(I, base))
            if not okx and C['shown'] < 6:
                C['shown'] += 1
                print('T1 FAILS', name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'W', W,
                      {k: v for k, v in res.items()}, 'picks complete', s_star_owners(I, base), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
