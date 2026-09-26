"""Independent Python check of the local improvement lemma (k4/c4min_reduce.md §5.3, Conjecture K4.C4MIN.RED.LIL),
with k4/red_lib.py only (no code shared with k4/red.c -L).
For every configuration at every key of every f = 1 profile of a seeded sample that is not completable (exact owner test
with unfreezing), look for a move that raises the potential: (-t, r', Lam) by default, (r', -t, Lam) with RFIRST=1;
Lam = free agents' levels over R plus the frozen agent's level of its good. BIGTOP=1 restricts to big-top keys of
big-top profiles (§5.1). Catalogue:
  M1: one free agent y re-pairs inside Q_y ∪ L (any pair S whose part in U_y is admissible)
  M4: rotation along a threat cycle of free agents (plain; and the modified variant for (R) receivers)
  M5: path move from any terminal tau along any simple threat path tau -> ... -> x (x takes any admissible pair in
      (Q_{p_k} ∪ L) ∩ U_x; the modified (R) variant allowed)
NARROW=1 restricts the catalogue as in attempts/k4-c4min-reduce-lil.md (red.c -Ln): the modified receiver only as
in Lemma R(iii) of k4/c4min.md / #50 (a receiver z of kind (R) with a_z in its received pair and s_z in L, in M5 in
L \ P_x, takes {a_z, s_z}), and in M5 x takes only its best pair inside (Q_{p_k} ∪ L) ∩ U_x; RECYCLE=1 adds #50's
recycling rule (the last receiver of kind (R) takes a with its better good of Q_{p_k} \ P_x); ANYPX=1 (with NARROW)
lets x take any pair of Q_{p_k} ∪ L, as in the broad M5 (red.c -Lx).
Reports non-completable configurations with no improving move ('STUCK'), classified.
Usage: [RFIRST=1] [M2=1] [BIGTOP=1] [NARROW=1 [RECYCLE=1] [ANYPX=1]] python3 k4/red_lil.py results/k4_certs_3.json.gz R SEED
(R = 0: every profile)"""
import sys, os, random, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_lib import Prof, Key, fewest_frozen_le1, bits, pc, load_cores, profiles


def lvl(P, i, S):
    R = list(P.vals[i]); w = P.v(i, S)
    return sum(1 for k in range(len(R) + 1) for c in itertools.combinations(R, k) if sum(P.vals[i][h] for h in c) < w)


def xtype(P, x, g):
    vs = sorted((P.vals[x][h] for h in P.vals[x] if h != g), reverse=True)
    a = P.vals[x][g]
    if len(vs) == 2: return '3'
    b, c, d = vs
    return '4big' if a > b + c else '4bc' if a > b + d else '4bcbd' if a > c + d else '4flat'


def phi(P, K, Q, L):
    t = int(P.v(K.x, L & K.Ux) > P.vals[K.x][K.g])
    r = sum(K.robust(y, Q[y]) for y in K.free)
    lam = sum(lvl(P, y, Q[y] & P.R[y]) for y in K.free) + lvl(P, K.x, 1 << K.g)
    return (r, -t, lam) if os.environ.get('RFIRST') == '1' else (-t, r, lam)


def is_config(P, K, Q, L):
    used = 0
    for y in K.free:
        S = Q.get(y)
        if S is None or pc(S) != 2 or (S >> K.g) & 1 or S & used: return False
        used |= S
        if not P.admissible(y, S & K.U[y], K.U[y]): return False
    return used | L == K.Mp and not used & L


NARROW = os.environ.get('NARROW') == '1'
RECYCLE = os.environ.get('RECYCLE') == '1'
ANYPX = os.environ.get('ANYPX') == '1'


def kind_R(P, K, y, Qy):
    """kind (R) at the key K: four goods, g not relevant, Q_y ⊆ R_y \\ {a_y}, not robust; returns s_y or None"""
    if len(P.vals[y]) != 4 or (P.R[y] >> K.g) & 1: return None
    if Qy & ~P.R[y] or (Qy >> P.top[y]) & 1 or K.robust(y, Qy): return None
    return next(h for h in P.vals[y] if h != P.top[y] and not (Qy >> h) & 1)


def moves(P, Ks, K, Q, L):
    """yield (key, Q', L') for the catalogue"""
    x, g = K.x, K.g
    # M1
    for y in K.free:
        W = list(bits(Q[y] | L))
        for a, b in itertools.combinations(W, 2):
            S = (1 << a) | (1 << b)
            if S == Q[y]: continue
            Q2 = dict(Q); Q2[y] = S; L2 = (Q[y] | L) & ~S
            yield K, Q2, L2
    # M2: two free agents re-pair inside Q_y ∪ Q_z ∪ L (only if M2 enabled)
    if os.environ.get('M2') == '1':
        for y, z in itertools.combinations(K.free, 2):
            W = list(bits(Q[y] | Q[z] | L))
            for a, b in itertools.combinations(W, 2):
                S = (1 << a) | (1 << b)
                if not P.admissible(y, S & K.U[y], K.U[y]): continue
                rest = [h for h in W if not (S >> h) & 1]
                for c, d in itertools.combinations(rest, 2):
                    T = (1 << c) | (1 << d)
                    if S == Q[y] and T == Q[z]: continue
                    Q2 = dict(Q); Q2[y] = S; Q2[z] = T
                    yield K, Q2, (Q[y] | Q[z] | L) & ~S & ~T
    thr = {o: [y for y in K.free if y != o and P.threat(y, Q[o] | L, Q[y])] for o in K.free}
    xthr = [o for o in K.free if P.threat(x, Q[o] | L, 1 << g)]
    # M4: cycles
    def cycles():
        seen = set()
        for s0 in K.free:
            stack = [(s0, [s0])]
            while stack:
                v, path = stack.pop()
                for y in thr[v]:
                    if y == s0 and len(path) >= 2:
                        key = frozenset(path)
                        if key not in seen: seen.add(key); yield list(path)
                    elif y not in path and y > s0: stack.append((y, path + [y]))
    for cyc in cycles():
        k = len(cyc)
        Q2 = dict(Q)
        for j in range(k): Q2[cyc[(j + 1) % k]] = Q[cyc[j]]
        yield K, Q2, L
        if NARROW:           # Lemma R(iii): one (R) receiver with s in L takes {a, s}
            for j in range(k):
                z = cyc[(j + 1) % k]; S = Q[cyc[j]]; s = kind_R(P, K, z, Q[z]); a = P.top[z]
                if s is None or not (L >> s) & 1 or not (S >> a) & 1: continue
                Q3 = dict(Q2); Q3[z] = (1 << a) | (1 << s); L3 = (L & ~(1 << s)) | (S & ~(1 << a))
                yield K, Q3, L3
            continue
        for j in range(k):   # modified: receiver cyc[j+1] takes {a, s} with s in L
            z = cyc[(j + 1) % k]; S = Q[cyc[j]]
            for a in bits(S):
                for s in bits(L):
                    Q3 = dict(Q2); Q3[z] = (1 << a) | (1 << s); L3 = (L & ~(1 << s)) | (S & ~(1 << a))
                    yield K, Q3, L3
    # M5: path moves
    def paths(start):
        out = []
        def rec(path):
            last = path[-1]
            if last in xthr: out.append(list(path))
            for y in thr[last]:
                if y not in path: rec(path + [y])
        rec([start]); return out
    for tau in K.free:
        if not K.needs_g(tau, Q[tau]) or tau not in Ks: continue
        Kt = Ks[tau]
        for path in paths(tau):
            base = {y: Q[y] for y in K.free if y not in path}
            for i in range(len(path) - 1): base[path[i + 1]] = Q[path[i]]
            last = Q[path[-1]]
            if NARROW:       # #50's path move: P_x = x's best pair inside (Q_{p_k} ∪ L) ∩ U_x (ANYPX: any pair)
                if ANYPX:
                    cands = [(1 << a) | (1 << b) for a, b in itertools.combinations(list(bits(last | L)), 2)]
                else:
                    WU = list(bits((last | L) & Kt.U[x]))
                    cands = [max(((1 << a) | (1 << b) for a, b in itertools.combinations(WU, 2)),
                                 key=lambda S: P.v(x, S))] if len(WU) >= 2 else []
                for Px in cands:
                    Q2 = dict(base); Q2[x] = Px; L2 = (last | L) & ~Px
                    yield Kt, Q2, L2
                    for i in range(len(path) - 1):   # modification: s in L \ P_x
                        z = path[i + 1]; S = Q[path[i]]; s = kind_R(P, K, z, Q[z]); a = P.top[z]
                        if s is None or not ((L & ~Px) >> s) & 1 or not (S >> a) & 1: continue
                        Q3 = dict(Q2); Q3[z] = (1 << a) | (1 << s)
                        yield Kt, Q3, (L2 & ~(1 << s)) | (S & ~(1 << a))
                    if RECYCLE and len(path) >= 2:     # recycling at the last receiver
                        z = path[-1]; S = Q[path[-2]]; E = Q[z] & ~Px; a = P.top[z]
                        if kind_R(P, K, z, Q[z]) is not None and (S >> a) & 1 and E:
                            e = max(bits(E), key=lambda h: P.vals[z][h])
                            Q3 = dict(Q2); Q3[z] = (1 << a) | (1 << e)
                            yield Kt, Q3, (L2 & ~(1 << e)) | (S & ~(1 << a))
                continue
            W = list(bits((last | L) & ~0))
            for a, b in itertools.combinations(W, 2):
                Px = (1 << a) | (1 << b)
                Q2 = dict(base); Q2[x] = Px; L2 = (last | L) & ~Px
                yield Kt, Q2, L2
                for i in range(len(path) - 1):   # modified receiver
                    z = path[i + 1]; S = Q[path[i]]
                    for a2 in bits(S):
                        for s in bits(L2):
                            Q3 = dict(Q2); Q3[z] = (1 << a2) | (1 << s); L3 = (L2 & ~(1 << s)) | (S & ~(1 << a2))
                            yield Kt, Q3, L3


def main():
    path, rand, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed); cnt = collections.Counter(); ex = []
    for n, m, sets in load_cores(path):
        if m < 2 * n: continue
        for vals in profiles(sets, m, rand or None, rng):
            P = Prof(vals, m)
            f, keys = fewest_frozen_le1(P)
            if f != 1: continue
            Ks = {x: Key(P, g, x) for g, x in keys}
            # big-top profile?
            allc = []
            for x, K in Ks.items():
                for Q, L in K.configs():
                    r = sum(K.robust(y, Q[y]) for y in K.free)
                    lam = sum(lvl(P, y, Q[y] & P.R[y]) for y in K.free) + lvl(P, x, 1 << K.g)
                    allc.append(((r, lam), x))
            b = max(c[0] for c in allc)
            GLOBAL = os.environ.get('BIGTOP') != '1'
            if not GLOBAL and not all(xtype(P, x, Ks[x].g) == '4big' for c, x in allc if c == b): continue
            cnt['profiles considered'] += 1
            bigK = Ks if GLOBAL else {x: K for x, K in Ks.items() if xtype(P, x, K.g) == '4big'}
            for x, K in bigK.items():
                for Q, L in K.configs():
                    if any(K.owner_status(Q, L, o)[2] for o in K.free): continue
                    cnt['non-completable configurations'] += 1
                    p0 = phi(P, K, Q, L)
                    ok = False
                    for K2, Q2, L2 in moves(P, Ks, K, Q, L):
                        if K2.x not in bigK: continue
                        if not is_config(P, K2, Q2, L2): continue
                        if phi(P, K2, Q2, L2) > p0: ok = True; break
                    if not ok:
                        cnt['STUCK'] += 1
                        t = -p0[1] if os.environ.get('RFIRST') == '1' else -p0[0]
                        cnt[('stuck', 't=%d' % t, xtype(P, x, K.g))] += 1
                        if len(ex) < 8: ex.append((vals, x, {y: sorted(bits(q)) for y, q in Q.items()}, sorted(bits(L)), p0))
    for k, v in sorted(cnt.items(), key=str): print(k, v)
    for e in ex: print('example', e)


if __name__ == '__main__':
    main()
