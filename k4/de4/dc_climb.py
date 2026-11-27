"""Search for the double clash that Corollary 28 leaves (k4/de4.md §10.4; ledger K4.DE4V3R.LP). EVIDENCE only.

Hill-climbs the values of a fixed hypergraph toward a (V3)-valid (H) state of the largest level sum with a double
clash (topswap.roles) at which no top swap of Lemma 27 applies (both frozen agents' next goods held, or a triple
threat). gap(Y) = 10 (Phi* - Phi(Y)) + (number of lower-pair holders of the clash with a valid top swap); gap 0 is
such a state, printed as FOUND (not by itself a counterexample to K4.DE4V3R.LP: check it with refine.py).

    python3 k4/de4/dc_climb.py SEED STEPS ROUNDS SOURCE      (SOURCE as in refine_climb.py)"""
import sys, os, json, random, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine_climb as RC
import topswap as TS
import refine_hx as RH
CD = RC.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, leftover, wanted_goods


def gap(I):
    All, ph, P = CT.states(I)
    v3 = [(Y, p) for Y, p in zip(All, ph) if T.v3ok(I, Y)]
    if not v3:
        return 99, None
    P3 = max(p for _, p in v3)
    best = (99, None)
    for Y, p in sorted(v3, key=lambda t: -t[1]):
        if 10 * (P3 - p) >= best[0] or P3 - p > 3:
            break
        J = set(leftover(I, Y))
        if not J:
            continue
        W = set(wanted_goods(I, Y))
        if not CD.H(I, Y, J, W):
            continue
        us = TS.roles(I, Y, J, W)
        if us is None:
            continue
        g = 10 * (P3 - p) + sum(TS.swap(I, Y, J, u)[1] is not None for u in us)
        if g < best[0]:
            best = (g, Y)
    return best


RC.gap = gap

if __name__ == '__main__':
    seed, steps, rounds, src = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    print('$ python3 k4/de4/dc_climb.py', ' '.join(sys.argv[1:]), flush=True)
    data = json.load(open(src[5:])) if src.startswith('json:') else None
    if isinstance(data, dict):
        data = data['instances']
    C = collections.Counter(); t0 = time.time()
    for r in range(rounds):
        if data is not None:
            d = rng.choice(data)
            sets, vals0 = d[0], d[1]
        else:
            import adv_t, adv_t3, adv_t4
            I0 = None
            while I0 is None:
                I0 = adv_t3.make(rng) if src == 'advt3x' else adv_t4.make(rng) if src == 'advt4x' else adv_t.make(rng, int(src[4:]))
            sets, vals0 = I0.sets, [[I0.v[i][g_] for g_ in I0.sets[i]] for i in range(I0.n)]
        g = RC.climb(sets, 1 + max(max(s) for s in sets), rng, steps, src, start=vals0, label='FOUND')
        C[g] += 1
        print('round', r, 'final gap', g, 'time %.0f' % (time.time() - t0), flush=True)
    print('gaps', sorted(C.items()))
