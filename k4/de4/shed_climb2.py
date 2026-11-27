"""Hill-climbing against broad shed-completability (K4.DE4V3R.SHED2) with a graded objective. EVIDENCE only.

For a non-completable (V3)-valid state Y within 5 of the largest level sum Phi*:
  score(Y) = 10 (Phi* - Phi(Y)) + (1 if Y is value-Pareto-dominated in its level sum) + 3 k(Y),
where k(Y) is the number of agents w holding two or more goods such that letting w alone keep one good of its holding
makes Y completable. The score of an instance is the least score; 99 if no non-completable state lies within 5 of
Phi*. Moves are kept when the score does not grow, and with probability 0.05 when it grows but stays below 99
(never to 99, so the climb does not drift into a random walk). At score 0 (a maximum with no single-agent shedding), shed.py's full check (any set of agents) decides: if Y is
not shed-completable it is a counterexample to K4.DE4V3R.SHED2, printed as COUNTEREXAMPLE.

    python3 k4/de4/shed_climb2.py SEED STEPS ROUNDS SOURCE      (SOURCE as in shed_climb.py)"""
import sys, os, json, random, time, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine_climb as RC
import shed as SH
SH.MODE = 'broad'
CD = RC.CD; CT = CD.CT; T = CD.T; S = CD.S
from de4lib import leftover


def single_sheds(I, Y, Cm):
    k = 0
    for w in range(I.n):
        if len(Y[w]) < 2:
            continue
        for g in Y[w]:
            Z = [list(A) for A in Y]; Z[w] = [g]
            if Cm.ok(Z):
                k += 1
                break
    return k


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
    best = (99, None)
    for Y, p in sorted(v3, key=lambda t: -t[1]):
        if P3 - p > 5 or 10 * (P3 - p) >= best[0]:
            break
        if not leftover(I, Y) or Cm.ok([list(A) for A in Y]):
            continue
        vy = CT.vals(I, Y)
        dom = any(all(a >= b for a, b in zip(z, vy)) and z != vy for z in cls[p])
        sc = 10 * (P3 - p) + (1 if dom else 0) + 3 * single_sheds(I, Y, Cm)
        if sc == 0 and SH.shed_ok(I, Y, Cm) is not None:
            sc = 1
        if sc < best[0]:
            best = (sc, Y)
    return best


RC.gap = gap

if __name__ == '__main__':
    seed, steps, rounds, src = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    print('$ python3 k4/de4/shed_climb2.py', ' '.join(sys.argv[1:]), flush=True)
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
        g = RC.climb(sets, 1 + max(max(s) for s in sets), rng, steps, src, start=vals0, noise=0.05, cap99=True)
        C[g] += 1
        print('round', r, 'final gap', g, 'time %.0f' % (time.time() - t0), flush=True)
    print('gaps', sorted(C.items()))
