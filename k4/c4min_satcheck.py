#!/usr/bin/env python3
"""Cross-check of the SAT encoding k4/c4min_sat.py against k4/c4min_hunt.c (k4/c4min_hunt.md §1.1): on random strict
profiles of random cores of the certificate lists (n = 3-5) and of random connected cores (n = 6-8), compare
  f*; d* (SAT: selectors; c4min_hunt.c -1: the least deficit over the min-frozen pre-allocations);
  where an owner is needed (f* > sigma): the set of owners o for which some min-frozen P has deficit <= 0 with o as
  owner (SAT: assumption own[o]; c4min_hunt.c -1o).
usage: c4min_satcheck.py [--per-core=K] [--seed=S]"""
import random, sys, time
import c4min_common as cc, c4min_sat, c4min_rigid, c4min_families as F


def main():
    per, seed = 2, 1
    for a in sys.argv[1:]:
        k, _, v = a.partition('=')
        if k == '--per-core': per = int(v)
        elif k == '--seed': seed = int(v)
    rng = random.Random(seed)
    srcs = []
    for f, K in [('k4_certs_3', 51), ('k4_certs_4_n4_2', 60), ('k4_certs_4_n4_3', 60), ('k4_certs_4_pure', 60),
                 ('k4_certs_5_n4_2', 40), ('k4_certs_5_n4_3', 40), ('k4_certs_5_n4_4', 40), ('k4_certs_5_pure', 40)]:
        cores = cc.load_cores(f'{cc.ROOT}/results/{f}.json.gz')
        for ci in rng.sample(range(len(cores)), min(K, len(cores))): srcs.append((f, cores[ci]['sets'], cores[ci]['m']))
    for n, m, n4 in [(6, 12, 4), (6, 15, 6), (7, 15, 7), (7, 17, 7), (8, 17, 8), (8, 19, 8)]:
        for r in range(10): srcs.append((f'random{n},{m},{n4}', F.random_core(rng, n, m, n4), m))
    tot = bad = own = 0
    t0 = time.time()
    for tag, sets, m in srcs:
        doms = cc.domains(sets, m)
        for _ in range(per):
            vals = [rng.choice(D) for D in doms]
            f, holds, cert, owners = c4min_sat.fstar_and_holds(sets, m, vals, per_owner=True)
            ob = c4min_sat.objective(sets, m, vals)
            h = cc.hunt_one(sets, m, vals)
            fh, sigma, D = c4min_rigid.owners(sets, m, vals)
            ok = f == fh == h['fstar'] and holds == (h['dstar'] <= 0) and ob[1] == min(h['dstar'], c4min_sat.DPOS + 1)
            if fh <= sigma: ok = ok and None in owners
            else:
                own += 1
                ok = ok and owners == [o for o, d in enumerate(D) if d <= 0] and ob[2] == len(owners)
            tot += 1
            if not ok:
                bad += 1
                print('MISMATCH', tag, sets, [[v[g] for g in S] for S, v in zip(sets, vals)], (f, holds, owners, ob), (h, D), flush=True)
    print(f'TOTAL profiles {tot} (owner needed {own}) mismatches {bad} ({time.time() - t0:.0f} s)')


if __name__ == '__main__':
    main()
