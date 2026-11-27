"""Literal check of Theorem D1-C (k4/d1.md §3) in its contrapositive form, on every start (hard or not).

Statement checked.  Let Y = SD(pi) with D = {k}, every good relevant to some agent, and let P = (k, ..., x_t = z) be a
canonical chain without HEAD.  Then at least one of:
  (R)  some inclusion-minimal improving H0 inside P_k = (J + B_z) & R_k is a singleton, or its crowded holders at B'
       (the state after P with H0) can be given distinct *robust* compensation goods: u gets e in (Pi - H0) & R_u with
       v_u(B'_u) + v_u(e) >= v_u((Pi & R_u) - e);
  (T)  Tool T: for some owner o unfrozen at the picks (o = z, or o off the chain) and some H inside J & P_k, W_o - H
       does not threaten k (raw test) and H has a system of distinct robust helpers among the unfrozen agents other
       than o (h robust for i: v_i(Y_i) + v_i(h) >= v_i((W_o & R_i) - h));
  (A)  the absorber completion of Lemma HC: x_{t-1} absorbs {a} + (J - g), the head z holds {Y_z, g}, all other
       agents keep their picks (g a junk good of H0 & R_z for some H0 in M with Y_z in H0 crowding z);
  (E)  the edge completion: owner z takes the whole pool Pi, which lies inside R_k.

Each outcome is verified by the raw EFX0 test: (R) by the S* completion test at B' with owner k, (T) by the S*
completion test at the picks with owner o, (A) and (E) by efx0 on the explicit allocation.  At a hard start (no
one-absorber completion of the picks) only (R) can occur, so (R) holds there: that is Theorem D1-C.

    python3 k4/d1/d1c_check.py SRC [loader args]          (data sets of k4/sdc/min_frozen.py)
    python3 k4/d1/d1c_check.py random SEED SECONDS        (random instances, every order)
    python3 k4/d1/d1c_check.py jsonl FILE...              (hunt records: their starts only)
"""
import sys, os, itertools, collections, json, random, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from d1lib import (open_records, Inst, sd_picks, Start, one_absorber, canonical_chains, pool, minimal_improving, apply_chain,
                   obstacles, sstar, threat, efx0, frozen)


def robust(I, i, base_val, h, Q):
    """{B_i, h} robust inside B_i + Q (Q = the relevant goods of the comparison bundle's universe)"""
    return base_val + I.v[i].get(h, 0) >= I.val(i, [g for g in Q if g != h])


def try_R(S, path, M):
    """(R): a singleton, or a minimal H0 whose crowded holders have distinct robust options"""
    I = S.I; k = path[0]; Pi = pool(S, path)
    for H0 in M:
        if len(H0) == 1: return ('R', H0, 'singleton')
    for H0 in M:
        head, crowded, F2 = obstacles(S, path, H0)
        if head: return None   # HEAD is a property of the chain; caller excludes it
        B2 = apply_chain(S, path, H0)
        opts = []
        for u in crowded:
            Q = [g for g in Pi if g in I.R[u]]
            bv = I.val(u, B2[u])
            opts.append([e for e in Q if e not in H0 and robust(I, u, bv, e, Q)])
        # distinct representatives (each holder has at most one option, but search generally)
        def match(idx, used):
            if idx == len(opts): return True
            return any(match(idx + 1, used | {e}) for e in opts[idx] if e not in used)
        if match(0, frozenset()): return ('R', H0, 'crowded %s' % crowded)
    return None


def try_T(S, path):
    """(T): owner o unfrozen at the picks, H inside J & P_k (|H| <= 2), robust helpers, k safe (raw)"""
    I = S.I; k = path[0]; z = path[-1]; Y = S.Y
    unfrozen = [i for i in range(I.n) if i not in S.F]
    owners = [z] + [o for o in unfrozen if o not in path]
    Pk_J = [g for g in S.J if g in I.R[k]]
    for o in owners:
        Wo = S.J + ([Y[o]] if Y[o] is not None else [])
        holders = [i for i in unfrozen if i != o and Y[i] is not None]
        for r in range(0, min(2, len(Pk_J)) + 1):
            for H in itertools.combinations(Pk_J, r):
                rest = [g for g in Wo if g not in H]
                if threat(I, k, S.p[k], rest): continue
                # helpers
                def helps(i, h):
                    if h not in I.R[i]: return False
                    Q = [g for g in Wo if g in I.R[i]]
                    return robust(I, i, S.p[i], h, Q)
                def match(idx, used):
                    if idx == len(H): return {}
                    for i in holders:
                        if i not in used and helps(i, H[idx]):
                            rest_ = match(idx + 1, used | {i})
                            if rest_ is not None: rest_[H[idx]] = i; return rest_
                    return None
                sdr = match(0, frozenset())
                if sdr is not None: return ('T', o, H, sdr)
    return None


def try_A(S, path, M):
    I = S.I; z = path[-1]; Y = S.Y
    if len(path) < 2: return None
    x = path[-2]; a = Y[x]
    for H0 in M:
        if Y[z] not in H0: continue
        head, crowded, F2 = obstacles(S, path, H0)
        if z not in crowded: continue
        for g in H0:
            if g == Y[z] or g not in I.R[z]: continue
            X = [list(b) for b in S.B]
            X[z] = [Y[z], g]
            X[x] = [a] + [h for h in S.J if h != g]
            if efx0(I, X): return ('A', H0, g, X)
    return None


def try_E(S, path):
    I = S.I; k = path[0]; z = path[-1]; Pi = pool(S, path)
    if all(g in I.R[k] for g in Pi):
        X = [list(b) for b in S.B]; X[z] = list(Pi)
        if efx0(I, X): return ('E', X)
    return None


def check_start(I, S, C, hard, tag, extra=''):
    k = S.D[0]
    for path in canonical_chains(S, k):
        Pi = pool(S, path); M = minimal_improving(S, k, Pi)
        if not M:
            C['%s chains with no improving set (Prop. 3\')' % tag] += 1
            t = try_T(S, path)
            if t is None: C['%s   ... and no Tool T (ERROR)' % tag] += 1
            continue
        head, _, _ = obstacles(S, path, M[0])
        if head: continue
        C['%s no-HEAD chains' % tag] += 1
        out = try_R(S, path, M)
        if out is not None:
            B2 = apply_chain(S, path, out[1])
            if not sstar(I, B2, k):
                C['%s (R) FAILS RAW (ERROR)' % tag] += 1
                print('ERROR R', extra, json.dumps((I.sets, I.vals)), S.Y, path, sorted(out[1]), flush=True)
            C['%s   (R) %s' % (tag, 'singleton' if out[2] == 'singleton' else ('crowded' if out[2] != 'crowded []' else 'no crowding'))] += 1
            continue
        if hard:
            C['%s HARD START WITHOUT (R): D1-C counterexample?' % tag] += 1
            print('NO R AT HARD START', extra, json.dumps((I.sets, I.vals)), S.Y, path, flush=True)
        res = try_T(S, path) or try_A(S, path, M) or try_E(S, path)
        if res is None:
            C['%s NONE of R/T/A/E (proof gap)' % tag] += 1
            print('GAP', extra, json.dumps((I.sets, I.vals)), S.Y, path, flush=True)
            continue
        C['%s   (%s)' % (tag, res[0])] += 1
        if res[0] == 'T':
            o = res[1]
            if not sstar(I, S.B, o):
                C['%s (T) FAILS RAW (ERROR)' % tag] += 1
                print('ERROR T', extra, json.dumps((I.sets, I.vals)), S.Y, path, res, flush=True)


def run_instance(sets, vals, m, C, name=''):
    I = Inst(sets, vals, m); seen = set()
    if len(set(g for s in sets for g in s)) != I.m: return   # every good relevant to some agent
    for od in itertools.permutations(range(I.n)):
        Y = sd_picks(I, od)
        if Y in seen: continue
        seen.add(Y); S = Start(I, Y)
        if len(S.D) != 1: continue
        hard = not one_absorber(I, S.B)
        C['starts with D = {k}'] += 1; C['  hard'] += hard
        check_start(I, S, C, hard, 'hard' if hard else 'easy', name)


if __name__ == '__main__':
    print('$ python3 k4/d1/d1c_check.py', *sys.argv[1:], flush=True)
    C = collections.Counter(); t0 = time.time()
    src = sys.argv[1]
    if src == 'random':
        sys.path.insert(0, HERE)
        from crowd_hunt import rand_inst
        rng = random.Random(int(sys.argv[2])); secs = float(sys.argv[3])
        while time.time() - t0 < secs:
            sets, vals, m = rand_inst(rng); C['instances'] += 1
            run_instance(sets, vals, m, C)
    elif src == 'jsonl':
        seen = set()
        for fn in sys.argv[2:]:
            for rec in open_records(fn):
                key = json.dumps((rec['sets'], rec['vals']))
                if key in seen: continue
                seen.add(key); C['instances'] += 1
                run_instance(rec['sets'], rec['vals'], rec['m'], C)
    else:
        sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
        from min_frozen import load
        for name, sets, vals, m in load(src, sys.argv):
            if len(sets) > 5: continue
            C['instances'] += 1
            run_instance(sets, vals, m, C, name)
    for key in sorted(C): print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
