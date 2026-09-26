"""Brute-force check of Lemma PM of k4/c4min_reduce.md §5.2 (the path move at a threatened terminal keeps t = 0 and
raises r'), with k4/red_lib.py (Python, from the definitions).

For every configuration c at every key of every f = 1 profile of a seeded random sample such that
  - t(c) = 0,
  - every free agent that is not robust is pool-optimal (no pair S ⊆ Q_y ∪ L worth more than Q_y),
  - no owner is valid with C = ∅,
and for every threat path tau = p_j -> p_{j+1} -> ... -> p_k -> x through free agents (each threatened by the previous
one, x by p_k) whose start tau is a terminal threatened by some owner that is not on the path (so tau is not robust,
and its threatener keeps its pair), the path move gives:
  - p_{i+1} the pair Q_{p_i} (i = j..k-1), or, for a receiver of kind (R) whose fourth good s lies in the pool, the pair
    {a, s} with the other good of Q_{p_i} going to the pool (only if no receiver becomes robust by the plain move);
  - x a robust admissible pair P_x inside (Q_{p_k} ∪ L) ∩ U_x (it exists by Lemma PM (i));
  - tau the good g (frozen); the rest of Q_{p_k} ∪ L to the pool.
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
                    cnt['path moves'] += 1
                    ok, why = apply_move(P, K, Ks[tau], Q, L, path, r0)
                    if not ok:
                        cnt['FAIL ' + why] += 1
                        if len(bad) < 5: bad.append((P.vals, (g, x), {y: sorted(bits(q)) for y, q in Q.items()}, sorted(bits(L)), path, why))


def apply_move(P, K, Kt, Q, L, path, r0):
    x, g = K.x, K.g
    tau = path[0]
    newQ = {y: Q[y] for y in K.free if y not in path}
    pool = L
    # receivers p_{i+1} get Q_{p_i}
    recv = [(path[i + 1], Q[path[i]]) for i in range(len(path) - 1)]
    plain_robust = any(Kt.robust(y, S) for y, S in recv if y in Kt.U)
    for y, S in recv: newQ[y] = S
    last = Q[path[-1]]
    # x's robust admissible pair inside (Q_{p_k} ∪ L) ∩ U_x (as a free agent at the key (g, tau))
    Wx = (last | pool) & Kt.U[x]
    cands = [(1 << a) | (1 << b) for a, b in itertools.combinations(list(bits(Wx)), 2)]
    cands = [S for S in cands if P.admissible(x, S, Kt.U[x]) and P.v(x, S) >= P.v(x, Kt.U[x] & ~S)]
    if not cands: return False, 'no robust admissible pair for x in its threatening set'
    Px = max(cands, key=lambda S: P.v(x, S))
    newQ[x] = Px
    newL = (last | pool) & ~Px
    # modified (R) receiver, only if no receiver is robust after the plain move
    if not plain_robust:
        for i, (y, S) in enumerate(recv):
            if len(P.vals[y]) != 4 or (P.R[y] >> g) & 1: continue
            a = P.top[y]
            if not (S >> a) & 1: continue
            others = [h for h in P.vals[y] if h != a]
            held = Q[y] & P.R[y]
            if pc(held) != 2 or (held >> a) & 1: continue
            s = [h for h in others if not (held >> h) & 1][0]
            if (newL >> s) & 1:
                ybar = S & ~(1 << a)
                newQ[y] = (1 << a) | (1 << s)
                newL = (newL & ~(1 << s)) | ybar
                break
    # validity at the key (g, tau)
    used = 0
    for y, S in newQ.items():
        if S & used or pc(S) != 2 or (S >> g) & 1: return False, 'pairs not disjoint'
        used |= S
        if not P.admissible(y, S & Kt.U[y], Kt.U[y]): return False, 'not admissible'
    if set(newQ) != set(Kt.free): return False, 'wrong agents'
    if pc(newL) != Kt.omega: return False, 'pool size'
    t1 = P.v(tau, newL & Kt.Ux) > P.vals[tau][g]
    if t1: return False, 't = 1 after the move'
    r1 = sum(Kt.robust(y, newQ[y]) for y in Kt.free)
    if r1 < r0 + 1: return False, "r' does not rise"
    return True, ''


def main():
    path, rand, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed); cnt = collections.Counter(); bad = []
    for n, m, sets in load_cores(path):
        if m < 2 * n: continue
        for vals in profiles(sets, m, rand or None, rng):
            check_profile(Prof(vals, m), cnt, bad)
    for k, v in sorted(cnt.items()): print('%-70s %d' % (k, v))
    for b in bad: print('example', b)
    print('ALL PATH MOVES OK' if not any(k.startswith('FAIL') for k in cnt) else 'FAILURES')


if __name__ == '__main__':
    main()
