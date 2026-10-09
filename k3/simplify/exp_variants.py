"""Simplifications that keep the rotation. Options (all combinations tested against raw EFX0):
  up      : run the upgrade loop (K3ALG) or skip it
  take_all: the absorber takes every leftover good except HitSet (which goes into slots), and is used whenever HitSet
            fits, even if all leftovers would fit in slots (K3ALG: no-owner completion when |J| <= S)
  klast   : k* = the last exposed agent in processing order (K3ALG: the exposed agent of r's block)"""
import sys, os, collections, multiprocessing, itertools
sys.path.insert(0, os.path.dirname(__file__))
from lbx import State, LEADERS, core_profiles, efx0

def complete_take_all(st, Y, U, o, H):
    X = [None] * st.m
    for i in range(st.n):
        if Y[i] is not None: X[Y[i]] = i
    for u in U: X[st.rank[u][2]] = u
    cap = st.caps(Y, U); L = list(dict.fromkeys(H))
    for i in range(st.n):
        if i == o: continue
        for g in L[:cap[i]]:
            if X[g] is None: X[g] = i
        L = L[cap[i]:]
    for g in st.junk(Y, U):
        if X[g] is None: X[g] = o
    return X

def run(rank, m, up=True, take_all=False, klast=False):
    st = State(rank, m)
    order, Y, blk, _ = st.phase1(LEADERS['index'])
    U = st.upgrades(Y, []) if up else []
    def finish(Y, U, o):
        J = st.junk(Y, U); cap = st.caps(Y, U)
        if not take_all and len(J) <= sum(cap): return st.complete(Y, U, None, []), 'noowner'
        E = st.exposed(o, Y, U)
        if any(st.rank[z][1] not in J and st.rank[z][2] not in J for z in E): return None, 'unprotectable'
        H = st.hitset(E, Y, U)
        if len(H) > sum(cap) - cap[o]: return None, 'H too big'
        return (complete_take_all(st, Y, U, o, H) if take_all else st.complete(Y, U, o, H)), 'owner'
    r = [i for i in order if i not in U][-1]
    X, tag = finish(Y, U, r)
    if X is not None: return X, tag
    E = st.exposed(r, Y, U)
    if klast: k = max(E, key=order.index)
    else:
        cand = [x for x in E if blk[x] == blk[r]]
        if not cand: return None, 'no k*'
        k = cand[0]
    na = st.NA(Y, U); chain = [k]
    for j in order[order.index(k) + 1:]:
        cur = chain[-1]
        if st.frozen(cur, Y, U, na) and j not in U and st.pos[j].get(Y[cur], 3) < (3 if Y[j] is None else st.pos[j][Y[j]]):
            chain.append(j)
    if chain[-1] != r and not klast: return None, 'chain does not end at r'
    Y2 = list(Y)
    for s in range(1, len(chain)): Y2[chain[s]] = Y[chain[s - 1]]
    Y2[k] = st.rank[k][1]; U2 = [k] + U
    if take_all:
        X, tag = finish(Y2, U2, k)
    else:
        J2 = st.junk(Y2, U2); cap2 = st.caps(Y2, U2)
        X, tag = finish(Y2, U2, k)
    return X, 'rot_' + tag

OPTS = [dict(up=u, take_all=t, klast=k) for u in (True, False) for t in (False, True) for k in (False, True)]
if os.environ.get('SURVIVORS'): OPTS = [dict(up=True, take_all=True, klast=True), dict(up=False, take_all=False, klast=True), dict(up=True, take_all=False, klast=False)]
def name(o): return f"up={'Y' if o['up'] else 'N'} take_all={'Y' if o['take_all'] else 'N'} klast={'Y' if o['klast'] else 'N'}"

def work(args):
    n, m, rank = args
    res = []
    for o in OPTS:
        X, tag = run(rank, m, **o)
        res.append(X is not None and efx0(rank, m, X))
    return n, res, (rank, m)

if __name__ == '__main__':
    maxn = int(sys.argv[1]); sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0; minn = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    tot = collections.Counter(); fails = collections.Counter(); first = {}
    with multiprocessing.Pool(4) as pool:
        for n, res, inst in pool.imap_unordered(work, core_profiles(maxn, sample=sample, minn=minn), chunksize=500):
            tot[n] += 1
            for t, ok in enumerate(res):
                if not ok: fails[(t, n)] += 1; first.setdefault(t, inst)
    ns = sorted(tot)
    print(f"profiles {dict(tot)} ({'every profile' if not sample else f'{sample} random per core'})")
    for t, o in enumerate(OPTS):
        print(f"  {name(o):32s} failures: " + "  ".join(f"n={n}: {fails[(t, n)]}" for n in ns) + (f"   first {first[t]}" if t in first else ""))
