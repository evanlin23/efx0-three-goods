"""Hill-climbing against shed-completability (k4/de4.md §10.5; ledger K4.DE4V3R.SHED). EVIDENCE only.

gap(Y) = 10 (Phi* - Phi(Y)) + (1 if Y is value-Pareto-dominated among (V3)-valid states of its level sum) for (V3)-valid
states Y that are not shed-completable (shed.py; SHED=top or SHED=broad); gap(I) is the least, 99 if none lies within 5 of Phi*. gap 0 is a
maximum of the robust order that is not shed-completable: a counterexample. Climbs as refine_climb.py.

    python3 k4/de4/shed_climb.py SEED STEPS ROUNDS SOURCE      (SOURCE as in refine_climb.py)"""
import sys, os, json, random, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine_climb as RC
import shed as SH
CD = RC.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover


def gap(I):
    All, ph, P = CT.states(I)
    v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
    if not v3:
        return 99, None
    P3 = max(p for _, p in v3)
    cls = collections.defaultdict(list)
    for Y, p in v3:
        cls[p].append(CT.vals(I, Y))
    Cm = S.Comp(I)
    cand = []
    for Y, p in v3:
        if P3 - p > 5 or not leftover(I, Y):
            continue
        vy = CT.vals(I, Y)
        dom = any(all(a >= b for a, b in zip(z, vy)) and z != vy for z in cls[p])
        cand.append((10 * (P3 - p) + (1 if dom else 0), Y))
    cand.sort(key=lambda t: t[0])
    for g, Y in cand:
        if Cm.ok([list(A) for A in Y]):
            continue
        if SH.shed_ok(I, Y, Cm) is None:
            return g, Y
    return 99, None


RC.gap = gap

if __name__ == '__main__':
    seed, steps, rounds, src = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    print('$ SHED=%s python3 k4/de4/shed_climb.py %s' % (SH.MODE, ' '.join(sys.argv[1:])), flush=True)
    data = json.load(open(src[5:])) if src.startswith('json:') else None
    if isinstance(data, dict):
        data = data['instances']
    C = collections.Counter(); t0 = time.time()
    for r in range(rounds):
        if data is not None:
            d = rng.choice(data); sets, vals0 = d[0], d[1]
        else:
            import adv_t, adv_t3, adv_t4
            I0 = None
            while I0 is None:
                I0 = (adv_t3.make(rng) if src == 'advt3x' else adv_t4.make(rng) if src == 'advt4x'
                      else adv_t4.make(rng, resid=True) if src == 'advt4r' else adv_t.make(rng, int(src[4:])))
            sets, vals0 = I0.sets, [[I0.v[i][g_] for g_ in I0.sets[i]] for i in range(I0.n)]
        g = RC.climb(sets, 1 + max(max(s) for s in sets), rng, steps, src, start=vals0)
        C[g] += 1
        print('round', r, 'final gap', g, 'time %.0f' % (time.time() - t0), flush=True)
    print('gaps', sorted(C.items()))
