"""Hill-climbing against K4.DE4V3R.SHED2 over values and hypergraphs. EVIDENCE only.

As shed_climb2.py (graded score: distance to the largest level sum, Pareto domination, 3 per single-agent shedding that
completes the state), but a step either perturbs one value (probability 0.85) or swaps one good of one agent's set for
another good among the m goods and redraws that agent's values (0.15), keeping strict R1-cores with 3 or 4 relevant
goods per agent. Moves are kept when the score does not grow, and with probability 0.05 when it grows but stays below
99. Score 0 that fails shed.py's full check is printed as COUNTEREXAMPLE; final scores up to 3 (one completing
single-agent shedding left) as NEAR.

    python3 k4/de4/shed_climb3.py SEED STEPS ROUNDS SOURCE      (SOURCE: json:FILE of [sets, values] instances)
With SOURCE json:FILE whose entries are NEAR lines' [sets, values, state], the climb continues from them."""
import sys, os, json, random, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine_climb as RC
import shed_climb2 as SC2
from de4lib import Inst


def mutate(sets, vals, m, rng):
    sets = [list(s) for s in sets]; vals = [list(v) for v in vals]
    if rng.random() < 0.85:
        i = rng.randrange(len(sets)); k = rng.randrange(len(sets[i]))
        vals[i][k] = max(1, vals[i][k] + rng.choice([-4, -2, -1, 1, 2, 4]))
        return sets, vals
    i = rng.randrange(len(sets)); k = rng.randrange(len(sets[i]))
    new = rng.choice([g for g in range(m) if g not in sets[i]])
    s = sorted(set(sets[i]) - {sets[i][k]} | {new})
    for _ in range(200):
        V = rng.sample(range(1, 40), len(s))
        if max(V) < sum(V) - max(V):
            sets[i], vals[i] = s, V
            return sets, vals
    return None, None


def climb(sets, vals, m, rng, steps, tag):
    I = Inst(sets, vals, m)
    g, Y = SC2.gap(I)
    for step in range(steps):
        ns, nv = mutate(sets, vals, m, rng)
        if ns is None:
            continue
        if any(sum(1 for t in ns if g_ in t) == 0 for g_ in range(m)):
            continue
        I2 = Inst(ns, nv, m)
        if not RC.ok_core(I2):
            continue
        g2, Y2 = SC2.gap(I2)
        if g2 <= g or (g2 < 99 and rng.random() < 0.05):
            sets, vals, g, Y = ns, nv, g2, Y2
            if g == 0:
                print('COUNTEREXAMPLE', tag, json.dumps((sets, vals, [list(a) for a in Y])), flush=True)
                return 0
    if g <= 3 and Y is not None:
        print('NEAR', g, tag, json.dumps((sets, vals, [list(a) for a in Y])), flush=True)
    return g


if __name__ == '__main__':
    seed, steps, rounds, src = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    print('$ python3 k4/de4/shed_climb3.py', ' '.join(sys.argv[1:]), flush=True)
    data = json.load(open(src[5:]))
    data = data['instances'] if isinstance(data, dict) else data
    C = collections.Counter(); t0 = time.time()
    for r in range(rounds):
        sets, vals0 = rng.choice(data)[:2]
        g = climb(sets, vals0, 1 + max(max(s) for s in sets), rng, steps, src)
        C[g] += 1
        print('round', r, 'final gap', g, 'time %.0f' % (time.time() - t0), flush=True)
    print('gaps', sorted(C.items()))
