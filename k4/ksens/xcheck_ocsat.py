"""Cross-check of ocsat.py (one SAT call per question) against k4/sdc's enumerative implementation (de_free.moves lists
every improving chain, oc_absorb.extends_A / de_free.extends test each resulting state).  Random instances with up to K
relevant goods per agent; every order; per start compare ext, ext1, oc, oc1.  de_free bounds set sizes (set to 99
here) and forbids passing an empty base, so ocsat runs with EMPTY_PASS = False.

    python3 k4/ksens/xcheck_ocsat.py SEED T n mmax K"""
import sys, random, itertools, collections, time
import _paths
import ocsat
import de_free as DF
from sdclib import Enc
from oc_absorb import extends_A

ocsat.EMPTY_PASS = False
DF.CHAIN_ONLY = True; DF.HMAX = 99; DF.BMAX = 99


def rand_inst(rng, n, mmax, K):
    while True:
        m = rng.randint(n + 1, mmax)
        sets = [sorted(rng.sample(range(m), rng.randint(2, min(K, m)))) for _ in range(n)]
        if len(set().union(*map(set, sets))) == m: break
    vals = [rng.sample(range(1, 30), len(s)) for s in sets]
    return sets, vals, m


if __name__ == '__main__':
    seed, T, n, mmax, K = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/ksens/xcheck_ocsat.py', *sys.argv[1:], flush=True)
    for t in range(T):
        sets, vals, m = rand_inst(rng, n, mmax, K)
        E = Enc(sets, vals, m); O = ocsat.OC(sets, vals, m)
        for Y, o in ocsat.starts(sets, vals, m).items():
            b = ocsat.bases_of(Y, n)
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            base = tuple(base)
            mv = list(DF.moves(E, base))
            ref = {'ext': DF.extends(E, base), 'ext1': extends_A(E, base, 1)}
            ref['oc'] = ref['ext'] or any(DF.extends(E, b2) for b2 in mv)
            ref['oc1'] = ref['ext1'] or any(extends_A(E, b2, 1) for b2 in mv)
            mine = {'ext': O.holds(b, chain='none'), 'ext1': O.holds(b, chain='none', A=1)}
            mine['oc'] = mine['ext'] or O.holds(b, chain='need')
            mine['oc1'] = mine['ext1'] or O.holds(b, chain='need', A=1)
            # exact count of states one chain reaches with a one-absorber completion
            c_ref = sum(1 for b2 in set(mv) if extends_A(E, b2, 1))
            c_mine = O.count(b, chain='need', A=1, cap=10 ** 6)
            C['starts'] += 1
            for k in ref:
                C['%s %s' % (k, ref[k])] += 1
                if ref[k] != mine[k]:
                    C['MISMATCH ' + k] += 1; print('MISMATCH', k, sets, vals, Y, ref[k], mine[k], flush=True)
            if c_ref != c_mine:
                C['MISMATCH count'] += 1; print('MISMATCH count', sets, vals, Y, c_ref, c_mine, flush=True)
        O.close()
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
