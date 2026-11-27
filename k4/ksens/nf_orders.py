"""Neediest-first orders (k4/sdc/nof_var.order: need2 = y1 - y2 - y3 as in k4/sdc.md §9, need1 = y1 - y2, needall)
on the PW family (k4/ksens.md §4, "Which orders"): OC1 and OC from their picks.  Reproduces results/k4_ksens/
nf_orders.log (parts 1-3) and nf2r1.log (part 4).

    python3 k4/ksens/nf_orders.py [1|2|3|4]"""
import sys, json, itertools
import _paths
sys.path.insert(0, _paths.SDC)
import ocsat, fam_ladder, fam_pwr1
from sdclib import Enc
from nof_var import order as nf_order
from r1_pw import sd_r1


def pw_tuned(f, W, r, WD=()):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)]; vals = [[40] + [24 - t for t in range(r)] for j in range(f)]
    for i in range(W):
        sets.append(P + [Q[i]] + [D[t] for t in WD]); vals.append([20 - j for j in range(f)] + [2] + [3] * len(WD))
    return sets, vals, f + W + r


def pw_flat(f, W, r, WD=()):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)]; vals = [[400] + [240 - t for t in range(r)] for j in range(f)]
    for i in range(W):
        sets.append(P + [Q[i]] + [D[t] for t in WD]); vals.append([200 - j for j in range(f)] + [190] + [195] * len(WD))
    return sets, vals, f + W + r


def with_z(f, W, r, wd0=True):
    """PW (flat wanters) plus a first agent z whose pick is the pool good D[0]"""
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)]; vals = [[400] + [240 - t for t in range(r)] for j in range(f)]
    for i in range(W):
        sets.append(P + [Q[i]] + ([D[0]] if wd0 else [])); vals.append([200 - j for j in range(f)] + [190] + ([195] if wd0 else []))
    sets.append([D[0]]); vals.append([100])
    return sets, vals, f + W + r


def show(name, sets, vals, m, kinds=('need2', 'need1', 'needall'), counts=False):
    E = Enc(sets, vals, m); O = ocsat.OC(sets, vals, m); n = len(sets)
    line = '%s %s k %d' % (name, json.dumps((sets, vals)), max(map(len, sets)))
    if counts:
        allbad = sum(1 for Y in ocsat.starts(sets, vals, m) if not O.holds(ocsat.bases_of(Y, n), chain='any', A=1))
        st = {}
        for o in itertools.permutations(range(n)): st.setdefault(tuple(sd_r1(sets, vals, o, m)), o)
        r1bad = sum(1 for Y in st if not O.holds(ocsat.bases_of(Y, n), chain='any', A=1))
        line += ' | every order: OC1 fails on %d starts | R1 orders: %d of %d' % (allbad, r1bad, len(st))
    print(line, flush=True)
    for kind in kinds:
        for r1 in (False, True):
            Y, done = nf_order(E, kind, r1); b = ocsat.bases_of(Y, n)
            print('   ', kind, 'R1' if r1 else 'plain', 'order', done, 'picks', Y, 'OC1', O.holds(b, chain='any', A=1),
                  'OC', O.holds(b, chain='any'), flush=True)
    O.close()


if __name__ == '__main__':
    parts = [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4]
    if 1 in parts:
        print('$ part 1: default values')
        for name, inst in {'PW5': fam_ladder.clean(3, 2, 4), 'PWR1-6': fam_pwr1.make(3, 3, 5, [0]), 'PW436': fam_ladder.clean(4, 3, 6)}.items():
            show(name, *inst)
    if 2 in parts:
        print('$ part 2: pool goods just above half the pick')
        for name, args in {'PW5-nf': (3, 2, 4), 'PWR1-6-nf': (3, 3, 5, (0,)), 'PWR1-7-nf': (4, 3, 5, (0,))}.items():
            show(name, *pw_tuned(*args), counts=True)
    if 3 in parts:
        print('$ part 3: flat wanters (200, 199, ..., q = 190)')
        for name, args in {'PW5-flat': (3, 2, 4), 'PW6-flat': (4, 2, 4), 'PWR1-6-flat': (3, 3, 5, (0,)), 'PWR1-7-flat': (4, 3, 5, (0,))}.items():
            show(name, *pw_flat(*args), kinds=('need2', 'needall'))
    if 4 in parts:
        print('$ part 4: need2 with R1 against PW plus a first agent z on a pool good')
        for f, W, r, wd0 in [(3, 2, 5, True), (3, 3, 5, True), (3, 3, 6, True), (4, 3, 5, True), (3, 2, 4, True), (3, 3, 4, True), (3, 3, 5, False)]:
            sets, vals, m = with_z(f, W, r, wd0)
            E = Enc(sets, vals, m); O = ocsat.OC(sets, vals, m); n = len(sets)
            print('f %d W %d r %d wd0 %s: k %d n %d m %d' % (f, W, r, wd0, max(map(len, sets)), n, m), json.dumps((sets, vals)), flush=True)
            for kind in ('need2', 'need1', 'needall'):
                Y, done = nf_order(E, kind, True); b = ocsat.bases_of(Y, n)
                print('     %s-R1 order %s picks %s OC1 %s OC %s' % (kind, done, Y, O.holds(b, chain='any', A=1), O.holds(b, chain='any')), flush=True)
            O.close()
