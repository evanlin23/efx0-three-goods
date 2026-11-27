"""Adversarial hill-climb against Finding B / Conjecture OC1^H (k4/oc1_hall.md §10).  Objective of a profile: over
every order whose picks have no S* completion (hard starts), the least number of (repairing chain description, owner)
pairs in which the chain starts at a dangerous frozen agent k and k or the chain end owns afterwards (S* shape); then
the number of hard starts (more is better); (99, 0) if no start is hard.  Starts: random logged profiles of
results/k4_sdc/*.log with N agents that have a hard start (or k4/sdc/sdc_climb.start if none).  Minimized; 0 = a counterexample to Finding B in its
"k or end" form, which is then re-tested with every chain and every owner (Finding S*).
Mutations and starts as in k4/sdc/sdc_climb.py.

    python3 k4/oc1_hall/climb_b.py SEED N STEPS ROUNDS
"""
import sys, os, json, random, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from chain_shapes import s_star_owners
from sdclib import Enc
import de_free as DF
from sdc_climb import mutate, start
DF.CHAIN_ONLY = True


def objective(sets, vals):
    m = 1 + max(max(s) for s in sets); I = Inst(sets, vals, m); E = Enc(sets, vals, m); res = {}
    for od in itertools.permutations(range(I.n)):
        Y = picks(I, od)
        if Y in res: continue
        base = base_of_picks(I, Y)
        if s_star_owners(I, base): res[Y] = None; continue
        P = Picks(I, Y); cnt = 0
        for b2, ds in DF.moves(E, base, describe=True, all_desc=True).items():
            fromD = [d for d in ds if d[1][0] in P.D]
            if not fromD: continue
            ow = set(s_star_owners(I, b2))
            cnt += sum(1 for d in fromD if d[1][0] in ow or d[1][-1] in ow)
        res[Y] = cnt
    hard = [c for c in res.values() if c is not None]
    if not hard: return (99, 0), None
    lo = min(hard)
    return (lo, -len(hard)), [Y for Y, c in res.items() if c == lo][0]


if __name__ == '__main__':
    seed, n, steps, rounds = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 k4/oc1_hall/climb_b.py', *sys.argv[1:], flush=True)
    from min_frozen import load
    pool = [(s_, v_) for _, s_, v_, m_ in load('logs', ['x', 'logs']) if len(s_) == n]
    rng.shuffle(pool); seeds = []
    for s_, v_ in pool:
        if objective(s_, v_)[0][0] < 99: seeds.append((s_, v_))
        if len(seeds) >= rounds: break
    print('seeds with a hard start:', len(seeds), flush=True)
    for r in range(rounds):
        sets, vals = seeds[r] if r < len(seeds) else start(rng, n); c, Y = objective(sets, vals); best = c
        for s in range(steps):
            mu = mutate(sets, vals, rng)
            if mu is None or len(mu[0]) != n or max(len(x) for x in mu[0]) > 4: continue
            c2, Y2 = objective(*mu)
            if c2 <= c or rng.random() < 0.03:
                (sets, vals), c, Y = mu, c2, Y2; best = min(best, c)
                if c[0] == 0:
                    m = 1 + max(max(x) for x in sets); I = Inst(sets, vals, m); E = Enc(sets, vals, m)
                    base = base_of_picks(I, Y)
                    anyrep = [b2 for b2 in DF.moves(E, base) if s_star_owners(I, b2)]
                    print('FINDING B FAILS', json.dumps((sets, vals)), 'picks', Y, 'S* still repaired by some chain:', bool(anyrep), flush=True)
                    break
        print('round', r, 'final', c, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
