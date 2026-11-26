"""Conjecture CM (k4/matching.md §3) at larger n, sampled orders (evidence only).

Instances: random strict profiles of the n = 6 cores with one 4-good agent (results/k4_certs_6_n4_1.json.gz,
de4lib.random_profile, as k4/sdc/min_frozen.load 'cores:'), or random strict connected cores from
k4/sdc/oc1_mc2_rand.gen (n = NMIN..NMAX, the K4.MC2 class).  For each instance, R random orders; for every distinct
perfect start whose picks have no one-absorber completion (raw): search for a CM witness (exchange.ex_value: chain from
a dangerous agent, improving H0, owner o with d_o <= s_o; the witness allocation is rebuilt and checked with raw
EFX0).  A start with no witness is printed, with its OC1 status (raw, every official move).

    python3 k4/matching/cm_big.py cores6 N R SEED | gen N R SEED NMIN NMAX"""
import sys, os, json, gzip, random, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, subsets
from exchange import general_chains, apply_chain, ex_value


def witness(I, base):
    J = I.junk(base); fz = set(I.frozen(base)); Y = [b[0] if b else None for b in base]
    for P, Hs in general_chains(I, base):
        k, xt = P[0], P[-1]; used = set(g for h in Hs.values() for g in h)
        Pi = [g for g in J if g not in used] + [Y[xt]]
        for H0 in subsets([g for g in Pi if g in I.R[k]], 1):
            if I.V(k, H0) <= I.V(k, base[k]) or (xt in fz and Y[xt] not in H0): continue
            Bp = apply_chain(I, base, P, list(H0), Hs)
            for o in [k, xt] + [j for j in range(I.n) if j not in (k, xt)]:
                d, s, _, X = ex_value(I, base, P, Bp, o, build=True)
                if d <= s:
                    assert X is not None and I.efx0(X), ('EX witness fails', I.sets, I.vals, base, P, H0, Hs, o)
                    return (P, list(H0), o, 'k' if o == k else 'end' if o == xt else 'off')
    return None


def job(args):
    name, sets, vals, R, seed = args
    rng = random.Random(seed); I = M(sets, vals, None, name); C = collections.Counter(); out = []
    orders = [tuple(rng.sample(range(I.n), I.n)) for _ in range(R)]
    for Y in sorted(set(I.sd(o) for o in orders), key=str):
        if any(Y[i] is None for i in range(I.n) if I.sets[i]): C['non-perfect starts'] += 1; continue
        C['perfect starts'] += 1
        base = [[g] if g is not None else [] for g in Y]
        if I.complete(base, 0, 'oa') is not None: continue
        C['hard perfect starts'] += 1
        w = witness(I, base)
        if w: C['CM holds, owner %s' % w[3]] += 1; continue
        oc1 = any(I.complete(b, 0, 'oa') is not None for b in I.moves(base))
        C['CM FAILS, OC1 %s' % ('holds' if oc1 else 'FAILS')] += 1
        out.append((Y, oc1))
    return name, sets, vals, C, out


if __name__ == '__main__':
    mode = sys.argv[1]; N, R, SEED = map(int, sys.argv[2:5]); rng = random.Random(SEED); tasks = []
    print('$ python3 k4/matching/cm_big.py', *sys.argv[1:], flush=True)
    if mode == 'cores6':
        cwd = os.getcwd(); os.chdir(os.path.join(_mpaths.ROOT, 'k4', 'de4'))
        from de4lib import random_profile
        os.chdir(cwd)
        cores = [c['sets'] for c in json.load(gzip.open(os.path.join(_mpaths.ROOT, 'results', 'k4_certs_6_n4_1.json.gz')))['cores']]
        for t in range(N):
            sets = rng.choice(cores); tasks.append(('c6-%d' % t, sets, random_profile(sets, rng), R, SEED * 100003 + t))
    else:
        from oc1_mc2_rand import gen
        NMIN, NMAX = map(int, sys.argv[5:7])
        for t in range(N):
            n = NMIN + t % (NMAX - NMIN + 1)
            while True:
                try: sets, vals = gen(n, rng); break
                except ValueError: continue
            tasks.append(('g%d-%d' % (n, t), sets, vals, R, SEED * 100003 + t))
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for name, sets, vals, C, out in pool.imap_unordered(job, tasks, chunksize=2):
            T['instances'] += 1; T.update(C)
            for Y, oc1 in out:
                print('CM FAILS', name, json.dumps({'sets': sets, 'vals': vals, 'picks': Y, 'OC1': oc1}), flush=True)
            if T['instances'] % 100 == 0: print('...', T['instances'], 'instances, %.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
