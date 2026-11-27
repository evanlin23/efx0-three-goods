"""OC1^max at n = 6 (k4/ttc.md §13): a strided sweep of the connected k = 4 core hypergraphs with n = 6, a given number
n4 of 4-good agents and nu = 6, enumerated with nauty's genbg (k4/search4.cores, one per isomorphism class).  For each
hypergraph, R random strict profiles drawn from k4/search4.domain (strict balanced types; two private goods only with
p + q < s + t), then every one of the 720 orders.  For every distinct serial-dictatorship outcome that is a maximum
matching (all 6 agents matched): a one-absorber completion at the picks (oc_absorb.extends_A), else the number of
improving moves (de_free chains and additions) after which one exists, capped at CAP.  A count of 0 is an OC1^max
failure and is printed.  The hardest starts (fewest repairing moves) are printed with their structure: frozen agents,
dangerous agents (frozen and valuing junk), receivers (unfrozen agents), and whether two dangerous agents' junk sets
meet.

    python3 k4/ttc/oc1max_n6.py N4[,N4..] STRIDE R SEED [mc2]   (mc2: skip hypergraphs with an agent holding two
    private goods, the K4.MC2 class)"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
import ttclib as T
sys.path.insert(0, os.path.join(T.ROOT, 'k4'))
import search4 as S4
import core_climb as CC

CAP = 30
N = 6


def profile(sets, rng):
    m = 1 + max(max(s) for s in sets)
    deg = [sum(g in S for S in sets) for g in range(m)]
    return [list(rng.choice(S4.domain(S, deg))) for S in sets]


def structure(E, base):
    F = T.frozen_set(E, base); D = T.dangerous_set(E, base)
    J = set(g for g in range(E.m) if base[g] < 0)
    js = {x: set(g for g in J if E.v[x].get(g, 0) > 0) for x in D}
    meet = any(js[a] & js[b] for a, b in itertools.combinations(sorted(D), 2))
    return {'frozen': len(F), 'dangerous': len(D), 'receivers': E.n - len(F), 'junk': len(J), 'danger sets meet': meet}


def job(args):
    m, sets, R, seed = args
    rng = random.Random(seed); C = collections.Counter(); hardest = None; bad = []
    for _ in range(R):
        vals = profile(sets, rng); E = T.Enc(sets, vals, m); seen = set()
        for pi in itertools.permutations(range(N)):
            Y = tuple(T.sd(E, list(pi))[0])
            if Y in seen:
                continue
            seen.add(Y)
            if any(y is None for y in Y):
                C['non-maximum outcomes'] += 1; continue
            C['maximum outcomes'] += 1
            b = T.base_of(E, Y)
            if T.extends_A(E, b, 1):
                continue
            C['maximum outcomes needing a move'] += 1
            c = 0; s2 = set()
            for b2 in T.DF.iter_chains(E, b):
                if b2 in s2:
                    continue
                s2.add(b2)
                if T.extends_A(E, b2, 1):
                    c += 1
                    if c >= CAP:
                        break
            C['repairing moves %s' % (c if c < 5 else '5+')] += 1
            if c == 0:
                bad.append((vals, Y))
            if hardest is None or c < hardest[0]:
                hardest = (c, vals, Y, structure(E, b))
    return m, sets, C, hardest, bad


def main(argv):
    n4s = [int(x) for x in argv[0].split(',')]; stride = int(argv[1]); R = int(argv[2]); seed = int(argv[3])
    mc2 = 'mc2' in argv[4:]
    print('$ python3 k4/ttc/oc1max_n6.py', *argv, flush=True)
    t0 = time.time(); tasks = []
    for n4 in n4s:
        k = 0
        for m in range(4, 3 * N + 1):
            for sets in S4.cores(N, m, n4 == N, None if n4 == N else n4):
                k += 1
                if k % stride:
                    continue
                if CC.nu(sets) < N or (mc2 and CC.two_private(sets)):
                    continue
                tasks.append((m, sets, R, seed * 1000003 + len(tasks)))
        print('n4 = %d: %d hypergraphs enumerated, %d sampled so far (stride %d, nu = 6%s), %.0f s' % (
            n4, k, len(tasks), stride, ', MC2' if mc2 else '', time.time() - t0), flush=True)
    Ctot = collections.Counter(); hard = []; done = 0
    with mp.Pool(max(1, (os.cpu_count() or 2))) as pool:
        for m, sets, C, hardest, bad in pool.imap_unordered(job, tasks, chunksize=4):
            done += 1; Ctot.update(C)
            for vals, Y in bad:
                Ctot['OC1^max FAILURES'] += 1
                print('OC1max FAILS', json.dumps({'sets': sets, 'vals': vals, 'm': m, 'picks': Y}), flush=True)
            if hardest is not None:
                hard.append((hardest[0], m, sets, hardest[1], hardest[2], hardest[3]))
            if done % 500 == 0:
                print('...', done, 'of', len(tasks), 'hypergraphs, %.0f s' % (time.time() - t0), flush=True)
    print('hypergraphs tested', len(tasks), 'profiles each', R)
    for k in sorted(Ctot):
        print(k, Ctot[k])
    hard.sort(key=lambda h: h[0])
    print('hardest starts (fewest repairing moves):')
    for c, m, sets, vals, Y, st in hard[:8]:
        print('  %d repairing moves' % c, json.dumps({'sets': sets, 'vals': vals, 'm': m, 'picks': Y}), st)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
