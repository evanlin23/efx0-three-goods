"""NOF2 (k4/sdc.md §19): with pi the neediest-first order (--r1: with R1 priority), SD(pi) extends, or SD(pi with one or two
agents moved to the end, in either relative order) does.  By Lemma DC each deferral is one displacement chain, and by
Proposition D4 in its main class an LB4r rotation; NF's "at most two rotations" at the level of serial dictatorships.

    python3 k4/sdc/nof2.py special|screen|suite|cores:FILES N SEED [--r1] | climb SEED n STEPS ROUNDS [--r1]
    climb: adversarial hill-climb (sdc_climb's instances) minimizing the number of distinct working candidates
    (plain, one or two deferrals); 0 = counterexample to NOF2."""
import sys, os, json, gzip, random, collections, time, itertools
R1 = '--r1' in sys.argv
sys.argv = [a for a in sys.argv if a != '--r1']
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable, sd
from nof_var import SPECIAL


def nof2(sets, vals, m):
    E = Enc(sets, vals, m); Y, pi = rule_order(E, 'need2', R1)
    if completable(E, Y): return 0
    seen = {tuple(Y)}
    for o in pi:
        Yo = tuple(sd(E, [i for i in pi if i != o] + [o])[0])
        if Yo not in seen:
            seen.add(Yo)
            if completable(E, list(Yo)): return 1
    for a, b in itertools.permutations(pi, 2):
        Yo = tuple(sd(E, [i for i in pi if i not in (a, b)] + [a, b])[0])
        if Yo not in seen:
            seen.add(Yo)
            if completable(E, list(Yo)): return 2
    return None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/nof2.py', *sys.argv[1:], '--r1' if R1 else '', flush=True)
    if src == 'climb':
        from sdc_climb import mutate, start
        seed, n, steps, rounds = map(int, sys.argv[2:6]); rng = random.Random(seed)
        def cnt(sets, vals):
            m = 1 + max(max(x) for x in sets); E = Enc(sets, vals, m); Y, pi = rule_order(E, 'need2', R1)
            cands = {tuple(Y)} | {tuple(sd(E, [i for i in pi if i != o] + [o])[0]) for o in pi} | \
                {tuple(sd(E, [i for i in pi if i not in (a, b)] + [a, b])[0]) for a, b in itertools.permutations(pi, 2)}
            return sum(1 for Yc in cands if completable(E, list(Yc)))
        for r in range(rounds):
            sets, vals = start(rng, n); c = cnt(sets, vals)
            for st in range(steps):
                mu = mutate(sets, vals, rng)
                if mu is None or len(mu[0]) != n: continue
                c2 = cnt(*mu)
                if c2 <= c or rng.random() < 0.03:
                    (sets, vals), c = mu, c2
                    if c == 0: print('NOF2 COUNTEREXAMPLE', json.dumps((sets, vals)), flush=True); break
            C['round final %d' % c] += 1
            print('round', r, 'final', c, json.dumps((sets, vals)), 'time %.0f' % (time.time() - t0), flush=True)
        items = []
    elif src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        r = nof2(sets, vals, m); C['instances'] += 1; C['deferrals needed: %s' % r] += 1
        if r is None: print('NOF2 FAILS', name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
