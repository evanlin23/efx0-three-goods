"""Falsification search for Conjecture REC-LOW (k4/sdc.md §31, ledger K4.SDC.RECLOW): on random strict connected k = 4
cores of the K4.MC2 class (generator oc1_mc2_rand.gen), at every maximum-matching SD pick vector that ESCAPES REC-LOW's
failure shape (no pick-holding receiver, or a receiver at rank <= 2), OC1 must hold (raw checker oc1_mc2_rand.Inst.check).
A failure there refutes REC-LOW (or, with no receiver, Lemma REC-exists).  Also run on the named strict core B< / B>
(k4/sdc/oc1_core_cex_verify.py), whose failing orders are outside the MC2 class.  Random testing is EVIDENCE only.
Mode 'perturb': near known failures.  Take every STRIDE-th failing start of d1's off-export walk dump, and NP times
scale its values by 10 and multiply each by a random factor in [0.6, 1.4]; keep the result if strict (no balance
condition: the walk's own profiles need not satisfy 2 v_i(g) < v_i(R_i)); test it as above.
    python3 k4/sdc/rec_low_rand.py N_INST SEED NMIN NMAX   |   python3 k4/sdc/rec_low_rand.py named
    python3 k4/sdc/rec_low_rand.py perturb STRIDE NP SEED"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst, gen
from oc1_max_orders import nu
from extremal_rank_check import ranks


def recs(I, Y):
    n = I.n; p = [I.v[i].get(Y[i], 0) if Y[i] is not None else 0 for i in range(n)]
    return [u for u in range(n) if Y[u] is not None and all(I.v[i].get(Y[u], 0) <= p[i] for i in range(n) if i != u)]


def run(sets, vals):
    I = Inst(sets, vals); n = I.n; N = nu(I)
    vec = set(I.sd(o) for o in itertools.permutations(range(n)))
    C = collections.Counter(); bad = []
    for Y in vec:
        if sum(x is not None for x in Y) != N: continue
        rz = recs(I, Y); rk = ranks(I, Y)
        esc = (not rz) or min(rk[u] for u in rz) <= 2
        res = I.check(Y)
        C['max vectors: escape=%s -> %s' % (esc, res)] += 1
        if res == 'OC1 fails':
            C['failing max vectors: receiver ranks %s' % sorted(rk[u] for u in rz)] += 1
        if esc and res == 'OC1 fails': bad.append(Y)
    return C, bad


def strict_ok(x):
    seen = {}
    for r in range(1, len(x) + 1):
        for T in itertools.combinations(range(len(x)), r):
            s_ = sum(x[k] for k in T)
            if any(not (set(T) & U) for U in seen.get(s_, [])): return False
            seen.setdefault(s_, []).append(set(T))
    return True


def pjob(a):
    sets, vals, seed, NP = a; rng = random.Random(seed); C = collections.Counter(); out = None
    for _ in range(NP):
        nv = []
        for x in vals:
            while True:
                y = [max(1, round(10 * g * rng.uniform(0.6, 1.4))) for g in x]
                if strict_ok(y): break
            nv.append(y)
        C1, bad = run(sets, nv); C.update(C1); C['perturbed profiles'] += 1
        if bad and out is None: out = (sets, nv, bad)
    return C, out


def job(a):
    n, seed = a; rng = random.Random(seed); sets, vals = gen(n, rng)
    C, bad = run(sets, vals); C['instances n=%d' % n] += 1
    return C, (n, seed, sets, vals, bad) if bad else None


if __name__ == '__main__':
    print('$ python3 k4/sdc/rec_low_rand.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'named':
        sys.argv[1] = 'B<'  # the module reads its instance name from sys.argv[1] at import
        from oc1_core_cex_verify import SETS, VALS  # noqa: E402
        for name in ('B<', 'B>'):
            C, bad = run(SETS, VALS[name]); print(name, dict(C), 'REC-LOW counterexamples:', bad)
        sys.exit()
    if sys.argv[1] == 'perturb':
        import gzip
        F = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_rf_offexport',
                         'rf_walk_n5_stored_fails.jsonl.gz')
        ST, NP, SEED = map(int, sys.argv[2:5]); t0 = time.time(); T = collections.Counter()
        rows = [json.loads(l) for i, l in enumerate(gzip.open(F, 'rt')) if i % ST == 0]
        tasks = [(r['sets'], r['vals'], SEED * 1000003 + t, NP) for t, r in enumerate(rows)]
        print('base starts', len(tasks), flush=True)
        with mp.Pool() as pool:
            for C, ex in pool.imap_unordered(pjob, tasks, chunksize=4):
                T.update(C)
                if ex: print('REC-LOW FAILS', json.dumps(ex), flush=True)
        for k in sorted(T): print(k, T[k])
        print('time %.0f s' % (time.time() - t0)); sys.exit()
    NI, SEED, NMIN, NMAX = map(int, sys.argv[1:5]); t0 = time.time(); T = collections.Counter()
    tasks = [(NMIN + t % (NMAX - NMIN + 1), SEED * 1000003 + t) for t in range(NI)]
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks, chunksize=4):
            T.update(C)
            if ex: print('REC-LOW FAILS', json.dumps(ex), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
