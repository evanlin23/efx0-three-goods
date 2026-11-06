"""Brute-force checks of the proof steps of k4/de4.md §10 (the robust order: (V1)-(V3), robust upper sets at level 6),
and of Claim T. EVIDENCE for the written proofs.
  python3 k4/de4/verify_robust.py SOURCE PER JOBS SEED   (SOURCE: hyper | rand | core files under results/)
Checks on every valid state of every profile drawn:
  (A) Theorem A': every non-completable state in which every agent holds an upper set: the construction (Lemma 4'
      or the rotation of the threat permutation) gives a better (V3)-valid state;
  (B) at the largest level sum, every agent threatened by the leftover goods alone is free;
  (C) Corollary 10 in the robust order: every non-completable (V3)-valid (H) state with no free agent holding two or
      more goods: the walk closes and its trade is (V3)-valid and better;
  (D) the walk, whenever it closes on a non-completable (V3)-valid (H) state, gives a (V3)-valid better state;
  (T) Claim T: every non-completable (V3)-valid state of the largest level sum is all-upper."""
import sys, random, collections, json, multiprocessing as mp
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import ss_screen as S
from de4lib import Inst, random_profile, load_cores, chain_move, wanted_goods, leftover, subsets
from cycle import walk
from dead import random_r1
_types = S.types
def types2(I, i, A):
    t = _types(I, i, A)
    if t == 'U' and I.val(i, A) >= I.val(i, [g for g in I.sets[i] if g not in A]): return 'UR'
    return t
S.types = types2; S.BASE_LEV['UR'] = 5
ROB = S.Variant('rob', {'LP': 3, 'UR': 6}, ['v3'])
def lev(I, i, A): return ROB.level(I, i, A)
def phi(I, Y): return sum(lev(I, i, Y[i]) for i in range(I.n))
def v3ok(I, Y):
    held = set(g for A in Y for g in A)
    return all(not (S.types(I, i, Y[i]) == 'LP' and I.ranked(i)[1] not in held) for i in range(I.n))
def vals(I, Y): return [I.val(i, Y[i]) for i in range(I.n)]
def better(I, Z, Y):
    a, b = phi(I, Z), phi(I, Y)
    if a != b: return a > b
    x, y = vals(I, Z), vals(I, Y); return all(p >= q for p, q in zip(x, y)) and x != y
def isupper(I, i, A): return S.types(I, i, A) in ('U', 'UR')
def thmA(I, Y):
    """Theorem A': Lemma 4' or the rotation; returns (kind, Z)"""
    J = set(leftover(I, Y)); n = I.n
    for x in range(n):
        for N in subsets([g for g in set(Y[x]) | J if g in I.v[x]]):
            if len(N) >= 2 and isupper(I, x, N) and I.val(x, N) > I.val(x, Y[x]):
                Z = [tuple(A) for A in Y]; Z[x] = tuple(sorted(N)); return 'lemma4prime', Z
    thr = {}
    for o in range(n):
        B = set(Y[o]) | J
        t = [i for i in range(n) if i != o and I.theta(i, B) > I.val(i, Y[i])]
        if not t: return 'VALID OWNER (completable?)', None
        thr[o] = t[0]
    if len(set(thr.values())) != n: return 'NOT A PERMUTATION', None
    cyc, x = [], 0
    while x not in cyc: cyc.append(x); x = thr[x]
    cyc = cyc[cyc.index(x):]
    pred = {thr[o]: o for o in cyc}
    def kind(i):
        r = I.ranked(i)
        if len(r) != 4: return '3'
        return 'D' if set(Y[i]) == {r[0], r[3]} else 'R'
    need = {}
    for i in cyc:
        o = pred[i]; r = I.ranked(i)
        if kind(i) == 'D': need[o] = {r[1], r[2]}
        elif kind(i) == 'R':
            s_ = [g for g in r if g not in Y[i] and g != r[0]][0]
            need[o] = {r[0]} | ({s_} if s_ in Y[o] else set())
        else: return 'THREATENED 3-GOOD', None
    Z = [tuple(A) for A in Y]; used = set()
    for i in cyc:
        o = pred[i]; r = I.ranked(i); a = r[0]
        if kind(i) == 'D':
            if not {r[1], r[2]} <= set(Y[o]): return 'D NEED MISSING', None
            Z[i] = (r[1], r[2])
        else:
            if a not in Y[o]: return 'R WITHOUT a', None
            s_ = [g for g in r if g not in Y[i] and g != a][0]
            spare = [g for g in Y[i] if g not in need[i]]
            if s_ in Y[o]: Z[i] = (a, s_)
            elif s_ in J and s_ not in used: used.add(s_); Z[i] = (a, s_)
            elif spare: Z[i] = (a, spare[0])
            else: Z[i] = (a,)
    Z = [tuple(sorted(A)) for A in Z]
    held = [g for A in Z for g in A]
    if len(held) != len(set(held)): return 'NOT DISJOINT', None
    ok = S.valid(ROB, I, Z) and v3ok(I, Z) and phi(I, Z) > phi(I, Y)
    return ('rotation raises Phi' if ok else 'ROTATION FAILS'), Z
def job(args):
    src, per, seed = args
    rng = random.Random(seed); C = collections.Counter(); ex = []
    if src == 'rand': cores = None
    elif src == 'hyper':
        cores = json.load(open(os.path.join(ROOT, 'results/k4_de4/stuck_hypergraphs.json')))['hypergraphs'] + [[[0,1,6,8],[0,1,2,3],[2,4,5,8],[4,5,6,7]]]
    else:
        cores = []
        for f in src.split(','): cores += load_cores(os.path.join(ROOT, 'results', f))
    for _ in range(per):
        I = random_r1(rng) if cores is None else (lambda s: Inst(s, random_profile(s, rng)))(rng.choice(cores))
        Cm = S.Comp(I)
        St = S.all_states(ROB, I)
        if not St: continue
        C['profiles'] += 1
        P = max(phi(I, Y) for Y in St)
        for Y in St:
            allup = all(isupper(I, i, Y[i]) for i in range(I.n))
            J = leftover(I, Y); W = wanted_goods(I, Y)
            free = [i for i in range(I.n) if not set(Y[i]) & W]
            if phi(I, Y) == P:
                for x in range(I.n):
                    if I.val(x, J) > I.val(x, Y[x]):
                        ok = x in free
                        C['(B) top level, agent threatened by J alone is free: %s' % ok] += 1
                        if not ok: ex.append(('B', I.sets, I.v, Y, x))
            if Cm.ok(Y): continue
            if allup:
                k, Z = thmA(I, Y)
                ok = Z is not None and better(I, Z, Y) and v3ok(I, Z)
                C["(A) Theorem A': %s" % ok] += 1
                if not ok: ex.append(('A', I.sets, I.v, Y, k))
            H = all(Y) and all(I.val(i, J) <= I.val(i, Y[i]) for i in range(I.n)) and chain_move(I, Y) is None
            if H:
                ws, Zw, _ = walk(I, Y)
                F2 = [i for i in free if len(Y[i]) >= 2]
                if not F2:
                    ok = ws == 'ok' and v3ok(I, Zw) and better(I, Zw, Y)
                    C['(C) Corollary 10, robust order: %s' % ok] += 1
                    if not ok: ex.append(('C', I.sets, I.v, Y, ws))
                elif ws == 'ok':
                    ok = v3ok(I, Zw) and better(I, Zw, Y)
                    C['(D) the walk closes: trade (V3)-valid and better: %s' % ok] += 1
                    if not ok: ex.append(('D', I.sets, I.v, Y))
            if phi(I, Y) == P:
                C['(T) Claim T: non-completable top state is all-upper: %s' % allup] += 1
                if not allup: ex.append(('T', I.sets, I.v, Y))
    return C, ex
if __name__ == '__main__':
    src, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    tot, EX = collections.Counter(), []
    with mp.Pool(2) as p:
        for C, ex in p.imap_unordered(job, [(src, per, seed + k) for k in range(jobs)]):
            tot.update(C); EX += ex
    for k in sorted(tot): print('%8d  %s' % (tot[k], k))
    for e in EX[:5]: print('EX', json.dumps(e)[:500])
