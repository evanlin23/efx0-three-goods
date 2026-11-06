"""Counterexample search by hill-climbing the values of a fixed hypergraph (k4/de4.md §10.3; ledger K4.DE4V3R.T,
K4.DE4V3R.P1, K4.DE4V3R.C3). EVIDENCE, and the search that found the counterexample to P1 (refute_p1.py).

gap(I) = Phi* minus the largest level sum of a (V3)-valid state of the kind sought:
  MODE=claimT  non-completable, not all-upper, with leftover goods (gap 0: a counterexample to Claim T);
  MODE=p1      with (H) and an out-arc of a free lower-pair holder (gap 0: a counterexample to P1);
  MODE=p1r     the same with a non-lateral out-arc (the taker is not a free holder of its b taking its lower pair);
  MODE=hx      with (H) and an unclean F2-clash cycle (gap 0 at a maximum: a counterexample to HX);
  MODE=c3      with (H) and a cycle of G through a free agent holding two or more goods (Conjecture C3).
States within 1 of the largest level sum at the end of a round are printed as NEAR.
Random values; then single-value perturbations are kept when the gap does not grow.

    MODE=... python3 k4/de4/gapsearch.py SEED STEPS ROUNDS SOURCE     SOURCE: xhg, dnc, advt0..advt3, advt3x
(seeded from adv_t.py / adv_t3.py), unclean (seeded from the JSON list in $UNCLEAN), or a core file under results/"""
import sys, os, json, random, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import claimd as CD
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, leftover, load_cores
from dead import strict_ok

def ok_core(I):
    for i in range(I.n):
        V = [I.v[i][g] for g in I.sets[i]]
        if len(V) not in (3, 4) or max(V) >= sum(V) - max(V): return False
    return strict_ok(I)

MODE = os.environ.get('MODE', 'claimT')

def bad(I, Y):
    from de4lib import wanted_goods
    J = set(leftover(I, Y))
    if not J: return False
    W = set(wanted_goods(I, Y))
    if not CD.H(I, Y, J, W): return False
    arcs = CD.graph(I, Y, J, W)
    if MODE == 'p1':
        return any(not CT.frozen(Y, a[0], W) and S.types(I, a[0], list(Y[a[0]])) == 'LP' for a in arcs)
    if MODE == 'p1r':
        def lateral(a):
            x = a[1]; r = I.ranked(x)
            return (not CT.frozen(Y, x, W) and len(r) == 4 and list(Y[x]) == [r[1]] and set(a[2]) == {r[2], r[3]})
        return any(not CT.frozen(Y, a[0], W) and S.types(I, a[0], list(Y[a[0]])) == 'LP' and not lateral(a) for a in arcs)
    if MODE == 'c3':
        return any(any(not CT.frozen(Y, a[0], W) and len(Y[a[0]]) >= 2 for a in c) for c in CD.cycles(I, arcs, I.n))
    for c in CD.cycles(I, arcs, I.n):
        if not CD.f2_clash_only(I, Y, J, W, c): continue
        lab = [g for a in c for g in set(a[2]) & J]
        if len(lab) != len(set(lab)): return True
    return False

def gap(I):
    All, ph, P = CT.states(I)
    if MODE != 'claimT':
        best = None
        for Y, p in sorted(zip(All, ph), key=lambda t: -t[1]):
            if best is not None and p < best: break
            if T.v3ok(I, Y) and bad(I, Y):
                return P - p, Y, P
        return 99, None, P
    cand = sorted(((p, Y) for Y, p in zip(All, ph) if T.v3ok(I, Y) and leftover(I, Y) and not CT.allupper(I, Y)),
                  key=lambda t: -t[0])
    Cm = S.Comp(I)
    for p, Y in cand:
        if not Cm.ok([list(a) for a in Y]):
            return P - p, Y, P
    return 99, None, P

def climb(sets, m, rng, steps, tag, start=None):
    if start is not None:
        vals = [list(v) for v in start]
        I = Inst(sets, vals, m)
        g, Y, P = gap(I)
        if g >= 99: return 99
    for tries in range(0 if start is not None else 300):
        vals = []
        for s in sets:
            while True:
                V = rng.sample(range(1, 30), len(s))
                if max(V) < sum(V) - max(V): break
            vals.append(V)
        I = Inst(sets, vals, m)
        if not ok_core(I): continue
        g, Y, P = gap(I)
        if g < 99: break
    else:
        if start is None: return 99
    for step in range(steps):
        i = rng.randrange(len(sets)); k = rng.randrange(len(sets[i]))
        nv = [list(v) for v in vals]
        nv[i][k] = max(1, nv[i][k] + rng.choice([-4, -2, -1, 1, 2, 4]))
        I2 = Inst(sets, nv, m)
        if not ok_core(I2): continue
        g2, Y2, P2 = gap(I2)
        if g2 <= g or rng.random() < 0.02:
            vals, g, Y, P = nv, g2, Y2, P2
            if g == 0:
                print('COUNTEREXAMPLE', tag, json.dumps((sets, vals, [list(a) for a in Y])), flush=True)
                return 0
    if g <= 1 and Y is not None:
        print('NEAR', g, tag, json.dumps((sets, vals, [list(a) for a in Y])), flush=True)
    return g

if __name__ == '__main__':
    seed, steps, rounds, src = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    rng = random.Random(seed)
    if src.startswith('advt') or src == 'unclean':
        pool = None
    elif src == 'dnc':
        pool = [([[0, 2, 4, 5], [1, 3, 6, 7], [1, 4, 8, 10], [0, 7, 8, 9], [0, 2, 7, 9], [1, 3, 9, 10]], 11)]
    elif src == 'xhg':
        pool = [(s, 1 + max(max(a) for a in s)) for s in CD.XHG]
    else:
        pool = [(s, 1 + max(max(a) for a in s)) for s in load_cores(os.path.join(ROOT, 'results', src))]
    print('$ MODE=%s python3 k4/de4/gapsearch.py %s' % (MODE, ' '.join(sys.argv[1:])))
    from collections import Counter
    C = Counter(); t0 = time.time()
    for r in range(rounds):
        if src == 'unclean':
            data = json.load(open(os.environ['UNCLEAN']))
            sets, vals0, key = rng.choice(data)
            m = 1 + max(max(s_) for s_ in sets)
            g = climb(sets, m, rng, steps, src + ':' + key, start=vals0)
        elif src.startswith('advt'):
            import adv_t, adv_t3
            I0 = None
            while I0 is None:
                I0 = adv_t3.make(rng) if src == 'advt3x' else adv_t.make(rng, int(src[4:]))
            g = climb(I0.sets, I0.m if hasattr(I0, 'm') else 1 + max(max(s) for s in I0.sets), rng, steps, src,
                      start=[[I0.v[i][g_] for g_ in I0.sets[i]] for i in range(I0.n)])
        else:
            sets, m = rng.choice(pool)
            g = climb(sets, m, rng, steps, src)
        C[g] += 1
        print('round', r, 'final gap', g, 'time %.0f' % (time.time() - t0), flush=True)
    print('gaps', sorted(C.items()))
