"""Brute-force check of Lemma PM of k4/c4min_reduce.md §5.2 (the path move at a threatened terminal keeps t = 0 and
raises r'), with k4/red_lib.py (Python, from the definitions).

For every configuration c at every key of every f = 1 profile of a seeded random sample such that
  - t(c) = 0,
  - every free agent that is not robust is pool-optimal (no pair S ⊆ Q_y ∪ L worth more than Q_y),
  - no owner is valid with C = ∅,
(the first and the last hypotheses are not used by the proof; they are kept so that the checked scope is the lemma's)
and for every simple threat path tau = p_0 -> p_1 -> ... -> p_k -> x through free agents (each threatened by the
previous one, x by p_k) whose start tau is a terminal threatened by some owner that is not on the path, and for EVERY
robust admissible pair P_x of x inside (Q_{p_k} ∪ L) ∩ U_x, the path move gives:
  - p_{i+1} the pair Q_{p_i} (i = 0..k-1) (plain move), or, for exactly one receiver z = p_{i+1} of kind (R) (four goods,
    g not relevant, holding a non-robust pair of R_z \ {a_z}) with a_z ∈ Q_{p_i} and s_z ∈ L \ P_x, the pair {a_z, s_z},
    the other good of Q_{p_i} going to the pool (every such single modification is tested, with or without a receiver
    that is robust after the plain move);
  - x the pair P_x; tau the good g (frozen); the rest of Q_{p_k} ∪ L to the pool.
Checked: the result is a configuration at the key (g, tau), t = 0 there, and r' rises by at least 1.
Usage: python3 k4/red_pathmove.py results/k4_certs_3.json.gz 3000 5   (R = 0: every profile)"""
import os, sys, random, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from red_lib import Prof, Key, fewest_frozen_le1, bits, pc, load_cores, profiles


def check_profile(P, cnt, bad):
    f, keys = fewest_frozen_le1(P)
    if f != 1: return
    Ks = {x: Key(P, g, x) for g, x in keys}
    for g, x in keys:
        K = Ks[x]
        for Q, L in K.configs():
            if P.v(x, L & K.Ux) > P.vals[x][g]: continue                        # t = 0
            rob = {y: K.robust(y, Q[y]) for y in K.free}
            def poolopt(y):
                vq = P.v(y, Q[y]); W = list(bits(Q[y] | L))
                return all(P.v(y, (1 << a) | (1 << b)) <= vq for a, b in itertools.combinations(W, 2))
            if not all(rob[y] or poolopt(y) for y in K.free): continue
            if any(K.owner_status(Q, L, o)[0] and not K.owner_status(Q, L, o)[1] for o in K.free): continue
            cnt['configurations (t = 0, non-robust pool-optimal, no valid owner)'] += 1
            thr = {o: [y for y in K.free if y != o and P.threat(y, Q[o] | L, Q[y])] for o in K.free}
            xthr = [o for o in K.free if P.threat(x, Q[o] | L, 1 << g)]
            threatened = {y for o in K.free for y in thr[o]}
            # simple threat paths ending at x, started by a threatened terminal
            def paths_to_x(start):
                out = []
                def rec(path):
                    last = path[-1]
                    if last in xthr: out.append(list(path))
                    for y in thr[last]:
                        if y not in path: path.append(y); rec(path); path.pop()
                rec([start]); return out
            r0 = sum(rob.values())
            for tau in K.free:
                if not (K.needs_g(tau, Q[tau]) and tau in threatened): continue
                tthr = [o for o in K.free if tau in thr[o]]
                for path in paths_to_x(tau):
                    if any(o in path[1:] for o in tthr): cnt['skipped: a threatener of tau on the path'] += 1; continue
                    if tau not in Ks: cnt['FAIL terminal with a path is not a key'] += 1; continue
                    cnt['paths'] += 1
                    for why in apply_moves(P, K, Ks[tau], Q, L, path, r0, cnt):
                        cnt['FAIL ' + why] += 1
                        if len(bad) < 5: bad.append((P.vals, (g, x), {y: sorted(bits(q)) for y, q in Q.items()}, sorted(bits(L)), path, why))


def kind_R(P, K, y, Qy):
    """kind (R) at the key K: four goods, g not relevant, Q_y ⊆ R_y \\ {a_y}, not robust; returns s_y or None"""
    if len(P.vals[y]) != 4 or (P.R[y] >> K.g) & 1: return None
    if Qy & ~P.R[y] or (Qy >> P.top[y]) & 1 or K.robust(y, Qy): return None
    return next(h for h in P.vals[y] if h != P.top[y] and not (Qy >> h) & 1)


def apply_moves(P, K, Kt, Q, L, path, r0, cnt):
    """every robust admissible P_x, the plain move and every single modification; yields failure reasons"""
    x, g = K.x, K.g
    tau = path[0]
    recv = [(path[i + 1], Q[path[i]]) for i in range(len(path) - 1)]
    base = {y: Q[y] for y in K.free if y not in path}
    for y, S in recv: base[y] = S
    last = Q[path[-1]]
    Wx = (last | L) & Kt.U[x]
    cands = [(1 << a) | (1 << b) for a, b in itertools.combinations(list(bits(Wx)), 2)]
    cands = [S for S in cands if P.admissible(x, S, Kt.U[x]) and P.v(x, S) >= P.v(x, Kt.U[x] & ~S)]
    if not cands: yield 'no robust admissible pair for x in its threatening set'; return
    for Px in cands:
        newQ = dict(base); newQ[x] = Px
        newL = (last | L) & ~Px
        variants = [('plain', newQ, newL)]
        for y, S in recv:
            s = kind_R(P, K, y, Q[y]); a = P.top[y]
            if s is None or not ((L & ~Px) >> s) & 1 or not (S >> a) & 1: continue
            Q3 = dict(newQ); Q3[y] = (1 << a) | (1 << s)
            variants.append(('modified', Q3, (newL & ~(1 << s)) | (S & ~(1 << a))))
        for kind, Q2, L2 in variants:
            cnt['path moves (%s)' % kind] += 1
            why = check_result(P, Kt, Q2, L2, tau, g, r0)
            if why: yield why + ' (%s)' % kind


def check_result(P, Kt, newQ, newL, tau, g, r0):
    used = 0
    for y, S in newQ.items():
        if S & used or pc(S) != 2 or (S >> g) & 1: return 'pairs not disjoint'
        used |= S
        if not P.admissible(y, S & Kt.U[y], Kt.U[y]): return 'not admissible'
    if set(newQ) != set(Kt.free): return 'wrong agents'
    if pc(newL) != Kt.omega or newL & used: return 'pool size'
    if P.v(tau, newL & Kt.Ux) > P.vals[tau][g]: return 't = 1 after the move'
    if sum(Kt.robust(y, newQ[y]) for y in Kt.free) < r0 + 1: return "r' does not rise"
    return ''


def main():
    path, rand, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed); cnt = collections.Counter(); bad = []
    for n, m, sets in load_cores(path):
        if m < 2 * n: continue
        for vals in profiles(sets, m, rand or None, rng):
            check_profile(Prof(vals, m), cnt, bad)
    for k, v in sorted(cnt.items()): print('%-70s %d' % (k, v))
    if not cnt['paths']: print('(no path move in this scope: the check is vacuous here)')
    for b in bad: print('example', b)
    print('ALL PATH MOVES OK' if not any(k.startswith('FAIL') for k in cnt) else 'FAILURES')


if __name__ == '__main__':
    main()
