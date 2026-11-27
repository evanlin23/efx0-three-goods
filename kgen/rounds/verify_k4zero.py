"""Verify OC1 / one-round failures of k-limited instances WITH ZEROS (EFX0; kgen/rounds.md §4.3) by two independent
programs:
  (a) k4/sdc's own pipeline: sdclib.Enc, sdc_orders.sd, de_free.moves (chains and rings, DF_HMAX = DF_BMAX = 4, which
      covers every set at k <= 4), oc_absorb.extends_A (one absorber) -- the campaign's OC1 test (k4/sdc.md §29);
  (b) a pure-Python brute force written here from the definitions: serial dictatorship over relevant goods, every chain
      (t >= 0, sets H inside the receiver's relevant goods, x_0 may take goods of the end's base: rings), every round of
      vertex-disjoint chains, every completion, raw EFX0 (v_i(X_i) >= v_i(X_j - g) for every g in X_j, worthless g
      included), at most one absorber.
Reports for the order: picks extend (one absorber), OC1 (one chain or ring), one round, two rounds (b only), MD.

    python3 kgen/rounds/verify_k4zero.py '<rows json, zeros allowed>' ORDER...
"""
import sys, os, json, itertools, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))


# ---------------- (b) brute force from the definitions ----------------
def sd(V, order):
    m = len(V[0]); left = set(range(m)); y = [None] * len(V)
    for a in order:
        best = None
        for g in sorted(left):
            if V[a][g] > 0 and (best is None or V[a][g] > V[a][best]): best = g
        y[a] = best
        if best is not None: left.discard(best)
    return y


def val(V, i, S): return sum(V[i][g] for g in S)


def efx0(V, X):
    for i in range(len(X)):
        o = val(V, i, X[i])
        for j in range(len(X)):
            if i != j:
                t = val(V, i, X[j])
                for g in X[j]:
                    if t - V[i][g] > o: return False
    return True


def completion(V, bases, A):
    n, m = len(V), len(V[0]); used = set(g for b in bases for g in b)
    rest = [g for g in range(m) if g not in used]
    for asg in itertools.product(range(n), repeat=len(rest)):
        if A is not None:
            c = [0] * n
            for a in asg: c[a] += 1
            if sum(1 for x in c if x >= 2) > A: continue
        X = [sorted(b) for b in bases]
        for g, a in zip(rest, asg): X[a].append(g)
        if efx0(V, X): return X
    return None


def one_round(V, bases, single):
    """states after one round (single: at most one chain); H inside relevant goods"""
    n, m = len(V), len(V[0]); used = set(g for b in bases for g in b)
    J = frozenset(g for g in range(m) if g not in used); out = set()

    def rec(free, fj, cur, last, k):
        out.add(tuple(frozenset(b) for b in cur))
        if single and k: return
        for L in range(1, len(free) + 1):
            for seq in itertools.permutations(sorted(free), L):
                if seq[0] < last: continue
                if any(not cur[seq[i]] for i in range(L - 1)): continue
                jl = sorted(fj); endb = sorted(cur[seq[-1]]) if L > 1 else []
                for asg in itertools.product(range(L + 1), repeat=len(jl)):
                    if any(a < L and V[seq[a]][g] <= 0 for g, a in zip(jl, asg)): continue
                    H = [set() for _ in seq]
                    for g, a in zip(jl, asg):
                        if a < L: H[a].add(g)
                    for take in itertools.product((0, 1), repeat=len(endb)):
                        T = {g for g, t in zip(endb, take) if t}
                        if any(V[seq[0]][g] <= 0 for g in T): continue
                        new = list(cur); ok = True
                        if L == 1:
                            nb = set(cur[seq[0]]) | H[0]; ok = bool(H[0]) and val(V, seq[0], nb) > val(V, seq[0], cur[seq[0]])
                            new[seq[0]] = nb
                        else:
                            new[seq[0]] = H[0] | T; ok = val(V, seq[0], new[seq[0]]) > val(V, seq[0], cur[seq[0]])
                            for i in range(1, L):
                                new[seq[i]] = set(cur[seq[i - 1]]) | H[i]
                                ok = ok and val(V, seq[i], new[seq[i]]) > val(V, seq[i], cur[seq[i]])
                        if ok: rec(free - set(seq), fj - set().union(*H), new, seq[0], k + 1)
    rec(set(range(n)), J, [set(b) for b in bases], -1, 0)
    return out


def brute(V, order):
    n, m = len(V), len(V[0]); y = sd(V, order)
    b0 = [frozenset([g]) if g is not None else frozenset() for g in y]
    r = {'picks': y, 'ext_1': completion(V, b0, 1) is not None}
    S1 = one_round(V, b0, True); r['oc1'] = any(completion(V, list(s), 1) is not None for s in S1)
    SR = one_round(V, b0, False); r['round_1'] = any(completion(V, list(s), 1) is not None for s in SR)
    r['round_free'] = any(completion(V, list(s), None) is not None for s in SR)
    if not r['round_1']:
        ok2 = False; seen = set()
        for s in SR:
            for s2 in one_round(V, list(s), False):
                if s2 in seen: continue
                seen.add(s2)
                if completion(V, list(s2), 1) is not None: ok2 = True; break
            if ok2: break
        r['two_rounds_1'] = ok2
    md = False
    for own in itertools.product(range(n), repeat=m):
        X = [[g for g in range(m) if own[g] == i] for i in range(n)]
        if all(val(V, i, X[i]) >= (V[i][y[i]] if y[i] is not None else 0) for i in range(n)) and efx0(V, X): md = True; break
    r['md'] = md
    return r


# ---------------- (a) k4/sdc's pipeline ----------------
def sdc_pipeline(V, order):
    import de_free as DF
    from sdclib import Enc
    from sdc_orders import sd as sdc_sd
    import oc_absorb
    n, m = len(V), len(V[0])
    sets = [[g for g in range(m) if V[i][g] > 0] for i in range(n)]
    vals = [[V[i][g] for g in sets[i]] for i in range(n)]
    E = Enc(sets, vals, m)
    Y, _left = sdc_sd(E, order)
    base = [-1] * m
    for a, g in enumerate(Y):
        if g is not None: base[g] = a
    r = {'picks': Y, 'ext_1': oc_absorb.extends_A(E, base, 1)}
    DF.CHAIN_ONLY = False
    states = DF.moves(E, tuple(base))
    r['oc1'] = r['ext_1'] or any(oc_absorb.extends_A(E, list(s), 1) for s in states)
    r['n_states'] = len(states)
    return r


if __name__ == '__main__':
    V = json.loads(sys.argv[1]); order = tuple(map(int, sys.argv[2:])); t0 = time.time()
    print('instance', json.dumps(V), 'order', order, 'k =', max(sum(1 for x in r if x > 0) for r in V))
    print('[k4/sdc pipeline]', sdc_pipeline(V, order), '%.0fs' % (time.time() - t0), flush=True)
    print('[brute force]    ', brute(V, order), '%.0fs' % (time.time() - t0), flush=True)


def one_chain_prime(V, bases):
    """OC1' (kgen/rounds.md §4.6): ONE chain x_0..x_t (t >= 0, or none); every NON-END agent x_i (i < t) may take,
    besides junk it values, goods of the end's base B_{x_t} that it values (the start x_0 as in a ring; a middle agent
    in addition to the base it receives); the end x_t takes B_{x_{t-1}} plus junk; the rest of B_{x_t} becomes junk;
    every chain agent strictly gains.  Written from that definition, independent of rnd.c."""
    n, m = len(V), len(V[0]); used = set(g for b in bases for g in b)
    J = sorted(g for g in range(m) if g not in used); out = {tuple(frozenset(b) for b in bases)}
    for L in range(1, n + 1):
        for seq in itertools.permutations(range(n), L):
            if any(not bases[seq[i]] for i in range(L - 1)): continue
            endb = sorted(bases[seq[-1]]) if L > 1 else []
            # each junk good: to one chain agent that values it, or nowhere; each end good: to a non-end agent that
            # values it, or released
            optsJ = [[None] + [k for k in range(L) if V[seq[k]][g] > 0] for g in J]
            optsE = [[None] + [k for k in range(L - 1) if V[seq[k]][g] > 0] for g in endb]
            for aJ in itertools.product(*optsJ):
                for aE in itertools.product(*optsE):
                    H = [set() for _ in seq]
                    for g, k in zip(J, aJ):
                        if k is not None: H[k].add(g)
                    for g, k in zip(endb, aE):
                        if k is not None: H[k].add(g)
                    new = [set(b) for b in bases]
                    if L == 1:
                        if not H[0]: continue
                        new[seq[0]] = set(bases[seq[0]]) | H[0]
                    else:
                        new[seq[0]] = set(H[0])
                        for i in range(1, L): new[seq[i]] = set(bases[seq[i - 1]]) | H[i]
                    if all(val(V, a, new[a]) > val(V, a, bases[a]) for a in seq):
                        out.add(tuple(frozenset(b) for b in new))
    return out


def oc1_prime(V, order):
    y = sd(V, order); b0 = [frozenset([g]) if g is not None else frozenset() for g in y]
    return any(completion(V, list(s), 1) is not None for s in one_chain_prime(V, b0))
