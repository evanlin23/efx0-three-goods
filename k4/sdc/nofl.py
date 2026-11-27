"""Conjecture NOF-L (k4/sdc.md §15): with pi the plain neediest-first R1 order, its blocks (a block starts at an insertion
step: no unprocessed agent has lost a good; its first agent is the block's leader), and l* the leader of the last block
whose leader is frozen (some agent prefers the leader's pick to its own pick; if no leader is frozen, the last block's
leader), SD(pi) extends to an EFX0 allocation, or SD(pi with l* moved to the end) does.  Two explicit candidates, no
choice.  (--blast: l* = the leader of the last block, frozen or not.)

    python3 k4/sdc/nofl.py screen|suite|cores:FILES N SEED|climb SEED n STEPS ROUNDS"""
import sys, os, json, gzip, random, time, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable, sd


BLAST = '--blast' in sys.argv
if BLAST: sys.argv.remove('--blast')


def frozen_pick(E, Y, x):
    if Y[x] is None: return False
    return any(j != x and E.v[j].get(Y[x], 0) > (E.v[j][Y[j]] if Y[j] is not None else 0) for j in range(E.n))


def last_leader(E, pi, Y):
    left = set(range(E.m)); done = set(); leads = []
    for i in pi:
        rest = [j for j in range(E.n) if j not in done]
        if not any(any(g not in left for g in E.R[j]) for j in rest):
            leads.append(i)
        done.add(i)
        if Y[i] is not None: left.discard(Y[i])
    if BLAST: return leads[-1]
    fz = [l for l in leads if frozen_pick(E, Y, l)]
    return fz[-1] if fz else leads[-1]


def nofl(sets, vals, m):
    """0 = plain run extends, 1 = deferral of l* extends, None = neither"""
    E = Enc(sets, vals, m)
    Y, pi = rule_order(E, 'need2', True)
    if completable(E, Y): return 0, pi, None
    l = last_leader(E, pi, Y)
    if completable(E, sd(E, [i for i in pi if i != l] + [l])[0]): return 1, pi, l
    return None, pi, l


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/nofl.py', *sys.argv[1:], flush=True)
    if src == 'climb':
        from sdc_climb import mutate, start
        seed, n, steps, rounds = map(int, sys.argv[2:6]); rng = random.Random(seed)

        def cost(sets, vals):
            m = 1 + max(max(s) for s in sets); r, pi, l = nofl(sets, vals, m)
            if r is None: return 0
            if r == 1: return 1
            # plain works: how close is it to failing?  number of working candidates among plain + every deferral
            E = Enc(sets, vals, m); Y, pi = rule_order(E, 'need2', True)
            return 2 + sum(1 for o in pi if completable(E, sd(E, [i for i in pi if i != o] + [o])[0]))
        for r in range(rounds):
            sets, vals = start(rng, n); c = cost(sets, vals); best = c
            for st in range(steps):
                mu = mutate(sets, vals, rng)
                if mu is None or len(mu[0]) != n: continue
                c2 = cost(*mu)
                if c2 <= c or rng.random() < 0.03:
                    (sets, vals), c = mu, c2; best = min(best, c)
                    if c == 0:
                        print('COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
            C['round best %d' % best] += 1
            print('round', r, 'final', c, 'best', best, 'inst', json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
    else:
        if src in ('screen', 'suite'):
            items = instances(src)
        else:
            N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
            cwd = os.getcwd(); os.chdir(_paths.DE4)
            import sdc_rand
            from de4lib import random_profile
            os.chdir(cwd)
            cores = None
            if src.startswith('cores:'):
                cores = []
                for fn in src[6:].split(','):
                    cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
            for t in range(N):
                if cores is not None:
                    sets = rng.choice(cores); vals = random_profile(sets, rng)
                elif src.startswith('gen:'):
                    _, n, m, k = src.split(':'); n, m, k = int(n), int(m), int(k)
                    while True:
                        sets = [sorted(rng.sample(range(m), rng.randint(max(1, k - 1), k))) for _ in range(n)]
                        if len(set().union(*map(set, sets))) == m: break
                    vals = [rng.sample(range(1, 60), len(s)) for s in sets]
                else:
                    os.chdir(_paths.DE4); sets, vals = sdc_rand.gen(src, rng); os.chdir(cwd)
                items.append(('r%d' % t, sets, vals, 1 + max(max(x) for x in sets)))
        for name, sets, vals, m in items:
            r, pi, l = nofl(sets, vals, m)
            C['instances'] += 1
            C['plain run extends'] += r == 0
            C['plain fails, l* deferred extends'] += r == 1
            if r is None:
                C['NOF-L FAILS'] += 1; print('NOF-L FAILS', name, json.dumps((sets, vals)), 'pi', pi, 'l*', l, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
