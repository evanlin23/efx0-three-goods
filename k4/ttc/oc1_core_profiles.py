"""How rare is the OC1 failure on the hypergraph of the core counterexample (attempts/k4-ttc-oc1-counterexample.md)?
Random strict balanced profiles (de4lib.random_profile) of that hypergraph, kept when is_core4 accepts them; for each,
every order; counts the profiles with a start that no improving move repairs (oc_absorb.extends_A over de_free's
moves, chains and additions).

    python3 k4/ttc/oc1_core_profiles.py N SEED"""
import sys, os, random, collections, itertools, json, time
import ttclib as T
import core_climb as CC

SETS = [[0, 1, 3, 4], [1, 2, 5, 6], [2, 0, 7, 8], [0, 1, 2], [0, 1, 2]]

if __name__ == '__main__':
    N, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/ttc/oc1_core_profiles.py', *sys.argv[1:], flush=True)
    for t in range(N):
        vals = CC.random_profile(SETS, rng)
        if not CC.is_core(SETS, vals, 9):
            C['profiles rejected (not a core)'] += 1; continue
        C['core profiles'] += 1
        E = T.Enc(SETS, vals, 9); res = {}
        for pi in itertools.permutations(range(5)):
            Y = tuple(T.sd(E, list(pi))[0])
            if Y in res:
                continue
            b = T.base_of(E, Y)
            if T.extends_A(E, b, 1):
                res[Y] = 0; continue
            res[Y] = 1 if any(T.extends_A(E, b2, 1) for b2 in set(T.DF.moves(E, b))) else None
        C['profiles needing a chain somewhere'] += any(r == 1 for r in res.values())
        if any(r is None for r in res.values()):
            C['profiles where OC1 fails'] += 1
            if C['profiles where OC1 fails'] <= 3:
                print('OC1 FAILS', json.dumps(vals), [Y for Y, r in res.items() if r is None], flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
