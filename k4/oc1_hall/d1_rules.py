"""One dangerous agent (k4/oc1_hall.md §15; coordinator's proof plan step 1).  At every one-absorber-hard start (no
one-absorber completion at the picks, SAT) with exactly one dangerous agent k, fixed rules for the ED chain:
  SWAP-ALL : t = 1, k -> a wanter w of Y_k; H_0 = every good of J + {Y_w} that k values (if improving); owner k;
  SWAP-MIN : t = 1; some inclusion-minimal improving H_0 inside J + {Y_w}; owner k;
  ED-ALL   : any ED chain (middle agents take exactly their predecessor's pick, which they want; the head may add
             junk); H_0 = every good of J + B_{x_t} that k values; owner k;
  ED-MIN   : any ED chain, H_0 an inclusion-minimal improving set, owner k;  ED-MIN-OR-ALL: either;
  ED-ANY   : any ED chain, any improving H_0, owner k or x_t (Conjecture OC1-ED* (b)).
Prints, for each rule, the starts where it fails although ED-ANY works (the list the proof must justify).

    python3 k4/oc1_hall/d1_rules.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of
from chain_shapes import s_star_owners
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load


def ed_paths(I, P, k, n):
    """ED skeletons k = x_0, ..., x_t (t >= 1): x_i wants Y_{x_{i-1}} for i < t; the head x_t may not want it"""
    out = []
    def ext(path):
        last = path[-1]
        for y in range(n):
            if y in path or P.Y[last] is None: continue
            out.append(tuple(path + [y]))                      # y as head (may take junk)
            if I.v[y].get(P.Y[last], 0) > P.pv[y]: ext(path + [y])   # y as a middle agent: must want the pick
    ext([k]); return out


def apply(I, P, base, path, H0, Ht):
    nb = list(base); Y = P.Y; xt = path[-1]
    if Y[xt] is not None: nb[Y[xt]] = -1
    for i in range(len(path) - 1, 0, -1): nb[Y[path[i - 1]]] = path[i]
    for g in Ht: nb[g] = xt
    for g in H0: nb[g] = path[0]
    return tuple(nb)


def subsets(xs):
    for r in range(len(xs) + 1): yield from itertools.combinations(xs, r)


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/d1_rules.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.D) != 1: continue
            base = base_of_picks(I, Y)
            if extends_A(E, base, 1): continue
            k = P.D[0]; key = '|F|=%d |W_k|=%d' % (len(P.F), len(P.W[k]))
            C['one-absorber-hard starts with |D| = 1'] += 1; C['  ' + key] += 1
            ok = collections.Counter()
            for path in ed_paths(I, P, k, n):
                xt = path[-1]; t = len(path) - 1
                headwants = I.v[xt].get(Y[path[-2]], 0) > P.pv[xt]
                pool0 = [g for g in P.J if g in I.R[k]] + ([Y[xt]] if Y[xt] is not None and Y[xt] in I.R[k] else [])
                for H0 in subsets(pool0):
                    if not H0 or I.val(k, H0) <= P.pv[k]: continue
                    rest = [g for g in P.J if g not in H0 and g in I.R[xt]]
                    for Ht in subsets(rest):
                        if I.val(xt, [Y[path[-2]]] + list(Ht)) <= P.pv[xt]: continue
                        if not Ht and not headwants: continue
                        ow = s_star_owners(I, apply(I, P, base, path, H0, Ht))
                        if not (k in ow or xt in ow): continue
                        ok['ED-ANY'] += 1
                        allk = tuple(pool0)
                        if k in ow and set(H0) == set(allk):
                            ok['ED-ALL'] += 1
                            if t == 1 and not Ht: ok['SWAP-ALL'] += 1
                        imp = [K for K in subsets(pool0) if K and I.val(k, K) > P.pv[k]]
                        minimal = not any(set(K) < set(H0) for K in imp)
                        if k in ow and t == 1 and not Ht and minimal: ok['SWAP-MIN'] += 1
                        if k in ow and minimal: ok['ED-MIN'] += 1
                        if k in ow and (minimal or set(H0) == set(pool0)): ok['ED-MIN-OR-ALL'] += 1
            for r in ('SWAP-ALL', 'SWAP-MIN', 'ED-ALL', 'ED-MIN', 'ED-MIN-OR-ALL', 'ED-ANY'):
                C['rule %s works' % r] += bool(ok[r])
                C['  %s: rule %s works' % (key, r)] += bool(ok[r])
                if not ok[r] and ok['ED-ANY'] and r in ('ED-ALL', 'ED-MIN', 'ED-MIN-OR-ALL') and C['shown ' + r] < 4:
                    C['shown ' + r] += 1
                    print('RULE %s FAILS (ED-ANY works)' % r, name, json.dumps((sets, vals)), 'picks', Y, 'k', k, key, flush=True)
            if not ok['ED-ANY']: print('ED-ANY FAILS', name, json.dumps((sets, vals)), 'picks', Y, flush=True)
            if ok['ED-MIN'] and not ok['SWAP-MIN']:
                print('SWAPMIN-FAILS-EDMIN-WORKS', json.dumps({'name': name, 'sets': sets, 'vals': vals, 'm': m, 'order': list(od),
                      'picks': list(Y), 'k': k, 'frozen': P.F, 'wanters of k': P.W[k]}), flush=True)
    for k_ in sorted(C, key=str): print(k_, C[k_])
    print('time %.0f s' % (time.time() - t0))
