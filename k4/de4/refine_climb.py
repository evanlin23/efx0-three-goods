"""Counterexample search for the lower-pair tie-break of the robust order (k4/de4.md §10.4; ledger K4.DE4V3R.LP).
EVIDENCE only. The order: the largest level sum Phi among (V3)-valid states, then the fewest lower-pair holders, then
value-Pareto (equivalently: lower pairs at level 3 - eps, then value-Pareto).

For a non-completable (V3)-valid state Y, with Phi* the largest level sum and L* the fewest lower-pair holders among
(V3)-valid states of level sum Phi*:
  gap(Y) = 10 (Phi* - Phi(Y)) + (#LP(Y) - L* if Phi(Y) = Phi*) + (1 if Y is Pareto-dominated in its class),
and gap(I) is the least gap(Y). gap 0 is a counterexample. Random values (or a seed instance), then single-value
perturbations kept when the gap does not grow. States with gap <= 2 at the end of a round are printed as NEAR.

    python3 k4/de4/refine_climb.py SEED STEPS ROUNDS SOURCE
SOURCE: advt0..advt3, advt3x, advt4x (seeded from adv_t.py / adv_t3.py / adv_t4.py), json:FILE (seeded from a list of [sets, values, ...]),
xhg, or a core file under results/ (random values)."""
import sys, os, json, random, time, collections
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import claimd as CD
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, leftover, load_cores
from dead import strict_ok


def nlp(I, Y):
    return sum(S.types(I, i, list(Y[i])) == 'LP' for i in range(I.n))


def ok_core(I):
    for i in range(I.n):
        V = [I.v[i][g] for g in I.sets[i]]
        if len(V) not in (3, 4) or max(V) >= sum(V) - max(V):
            return False
    return strict_ok(I)


def gap(I):
    All, ph, P = CT.states(I)
    v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
    if not v3:
        return 99, None
    P3 = max(p for _, p in v3)
    L = min(nlp(I, Y) for Y, p in v3 if p == P3)
    cls = collections.defaultdict(list)
    for Y, p in v3:
        cls[(p, nlp(I, Y))].append(CT.vals(I, Y))
    cand = []
    for Y, p in v3:
        if not leftover(I, Y):
            continue
        k = nlp(I, Y)
        vy = CT.vals(I, Y)
        dom = any(all(a >= b for a, b in zip(z, vy)) and z != vy for z in cls[(p, k)])
        g = 10 * (P3 - p) + (k - L if p == P3 else 0) + (1 if dom else 0)
        cand.append((g, Y))
    cand.sort(key=lambda t: t[0])
    Cm = S.Comp(I)
    for g, Y in cand:
        if g >= 20:
            break
        if not Cm.ok([list(a) for a in Y]):
            return g, Y
    return 99, None


def rand_vals(sets, rng):
    vals = []
    for s in sets:
        while True:
            V = rng.sample(range(1, 40), len(s))
            if max(V) < sum(V) - max(V):
                break
        vals.append(V)
    return vals


def climb(sets, m, rng, steps, tag, start=None):
    vals = [list(v) for v in start] if start is not None else None
    g, Y = 99, None
    if vals is not None:
        g, Y = gap(Inst(sets, vals, m))
    else:
        for _ in range(300):
            vals = rand_vals(sets, rng)
            I = Inst(sets, vals, m)
            if not ok_core(I):
                continue
            g, Y = gap(I)
            if g < 99:
                break
    if g >= 99:
        return 99
    for step in range(steps):
        i = rng.randrange(len(sets)); k = rng.randrange(len(sets[i]))
        nv = [list(v) for v in vals]
        nv[i][k] = max(1, nv[i][k] + rng.choice([-4, -2, -1, 1, 2, 4]))
        I2 = Inst(sets, nv, m)
        if not ok_core(I2):
            continue
        g2, Y2 = gap(I2)
        if g2 <= g or rng.random() < 0.02:
            vals, g, Y = nv, g2, Y2
            if g == 0:
                print('COUNTEREXAMPLE', tag, json.dumps((sets, vals, [list(a) for a in Y])), flush=True)
                return 0
    if g <= 2 and Y is not None:
        print('NEAR', g, tag, json.dumps((sets, vals, [list(a) for a in Y])), flush=True)
    return g


if __name__ == '__main__':
    seed, steps, rounds, src = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    print('$ python3 k4/de4/refine_climb.py', ' '.join(sys.argv[1:]), flush=True)
    data = json.load(open(src[5:])) if src.startswith('json:') else None
    pool = None
    if src == 'xhg':
        pool = [(s, 1 + max(max(a) for a in s)) for s in CD.XHG]
    elif not src.startswith('advt') and data is None:
        pool = [(s, 1 + max(max(a) for a in s)) for s in load_cores(os.path.join(ROOT, 'results', src))]
    C = collections.Counter(); t0 = time.time()
    for r in range(rounds):
        if data is not None:
            d = rng.choice(data)
            sets, vals0 = d[0], d[1]
            g = climb(sets, 1 + max(max(s) for s in sets), rng, steps, src, start=vals0)
        elif src.startswith('advt'):
            import adv_t, adv_t3, adv_t4
            I0 = None
            while I0 is None:
                I0 = adv_t3.make(rng) if src == 'advt3x' else adv_t4.make(rng) if src == 'advt4x' else adv_t.make(rng, int(src[4:]))
            g = climb(I0.sets, 1 + max(max(s) for s in I0.sets), rng, steps, src,
                      start=[[I0.v[i][g_] for g_ in I0.sets[i]] for i in range(I0.n)])
        else:
            sets, m = rng.choice(pool)
            g = climb(sets, m, rng, steps, src)
        C[g] += 1
        print('round', r, 'final gap', g, 'time %.0f' % (time.time() - t0), flush=True)
    print('gaps', sorted(C.items()))
