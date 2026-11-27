"""OC1 (and OC) restricted to R1-priority or neediest-first orders fail at k = 6 and 7 (k4/ksens.md §4).
  PWR1-6 = fam_pwr1.make(3, 3, 5, [0]): n = 6, m = 11, k = 6 (the wanters value the pool good that the displaced
           frozen agent takes, so it is frozen too);
  PW436  = fam_ladder.clean(4, 3, 6): n = 7, m = 13, k = 7.
For an R1-priority order of each, two checks:
  1. SAT: ocsat.py (one chain) and ocseq.py (a separately written encoding of c chains), on sdclib's EFX0 clauses;
  2. SAT-free: brute.py enumerates every improving chain from the definition, and decides the completion of every
     resulting state by backtracking against the raw EFX0 definition (brute.Inst.completes_bt, validated against the
     full enumeration on PW5: 38,286 comparisons, 0 mismatches).

    python3 k4/ksens/refute_oc1_r1.py [PWR1-6 | PW436 | NF2-6 | NF1R1-6]
NF2-6 and NF1R1-6 (k = 6): the same failure from neediest-first orders (k4/sdc/nof_var.order)."""
import sys, json, time, itertools
import _paths
import ocsat, ocseq, brute, fam_ladder, fam_pwr1
from r1_pw import sd_r1

def pw_flat(f, W, r, WD=()):
    """PW with flat wanters (k4/ksens.md §4): pool goods just above half the pick, wanters' values nearly equal"""
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)]; vals = [[400] + [240 - t for t in range(r)] for j in range(f)]
    for i in range(W):
        sets.append(P + [Q[i]] + [D[t] for t in WD]); vals.append([200 - j for j in range(f)] + [190] + [195] * len(WD))
    return sets, vals, f + W + r


def pw_nf(f, W, r, WD=()):
    """PW with pool goods just above half the pick and steeper wanters (k4/ksens.md §4)"""
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)]; vals = [[40] + [24 - t for t in range(r)] for j in range(f)]
    for i in range(W):
        sets.append(P + [Q[i]] + [D[t] for t in WD]); vals.append([20 - j for j in range(f)] + [2] + [3] * len(WD))
    return sets, vals, f + W + r


def nf_picks(kind, r1):
    def f(sets, vals, m):
        sys.path.insert(0, _paths.SDC)
        from sdclib import Enc
        from nof_var import order as nf_order
        return tuple(nf_order(Enc(sets, vals, m), kind, r1)[0])
    return f


def r1_picks(order):
    return lambda sets, vals, m: tuple(sd_r1(sets, vals, order, m))


CASES = {'PWR1-6': (lambda: fam_pwr1.make(3, 3, 5, [0]), r1_picks((0, 3, 1, 2, 4, 5)), 'an R1-priority order'),
         'PW436': (lambda: fam_ladder.clean(4, 3, 6), r1_picks((0, 4, 1, 2, 3, 5, 6)), 'an R1-priority order'),
         'NF2-6': (lambda: pw_flat(3, 3, 5, (0,)), nf_picks('need2', False), 'the neediest-first order (need = y1 - y2 - y3)'),
         'NF1R1-6': (lambda: pw_nf(4, 3, 5, (0,)), nf_picks('need1', True), 'the R1 neediest-first order with need = y1 - y2')}


def service(sets, order, Y, m):
    left = set(range(m)); done = []; rank = {a: k for k, a in enumerate(order)}
    for _ in range(len(sets)):
        i = min([a for a in range(len(sets)) if a not in done], key=lambda a: (0 if any(g not in left for g in sets[a]) else 1, rank[a]))
        done.append(i)
        if Y[i] is not None: left.discard(Y[i])
    return done


if __name__ == '__main__':
    names = sys.argv[1:] or list(CASES)
    print('$ python3 k4/ksens/refute_oc1_r1.py', *sys.argv[1:], flush=True)
    for name in names:
        mk, picks, what = CASES[name]; sets, vals, m = mk(); n = len(sets)
        Y = picks(sets, vals, m); b = ocsat.bases_of(Y, n)
        print('%s %s\n   k %d, n %d, m %d; %s, picks %s, junk %s' % (name, json.dumps((sets, vals)),
              max(map(len, sets)), n, m, what, Y, [g for g in range(m) if g not in Y]), flush=True)
        O = ocsat.OC(sets, vals, m); Q = ocseq.Seq(sets, vals, m)
        r = {'ocsat oc': O.holds(b, chain='any'), 'ocsat oc1': O.holds(b, chain='any', A=1),
             'ocseq <=1 chain free': Q.holds(b, 1), 'ocseq <=1 chain A=1': Q.holds(b, 1, 1), 'ocseq <=2 chains free': Q.holds(b, 2)}
        print('   SAT:', r, flush=True)
        I = brute.Inst(sets, vals, m); t0 = time.time()
        base = [frozenset([g]) if g is not None else frozenset() for g in Y]
        ch = I.chains(base)
        c0 = I.completes_bt(base); free = sum(1 for s in ch if I.completes_bt(s)); one = sum(1 for s in ch if I.completes_bt(s, 1))
        print('   SAT-free: %d distinct one-chain states; picks complete (free) %s; states with a free completion %d, with a '
              'one-absorber completion %d (%.0f s)' % (len(ch), c0, free, one, time.time() - t0), flush=True)
        assert not r['ocsat oc'] and not r['ocsat oc1'] and not r['ocseq <=1 chain free'] and not r['ocseq <=1 chain A=1']
        assert r['ocseq <=2 chains free'] and not c0 and free == 0 and one == 0
        st = {}
        for o in itertools.permutations(range(n)): st.setdefault(tuple(sd_r1(sets, vals, o, m)), o)
        print('   R1-priority starts: %d, failing OC1 (ocsat): %d; every-order starts failing OC1: %d' % (len(st),
              sum(1 for y in st if not O.holds(ocsat.bases_of(y, n), chain='any', A=1)),
              sum(1 for y in ocsat.starts(sets, vals, m) if not O.holds(ocsat.bases_of(y, n), chain='any', A=1))), flush=True)
        print('   OK: OC and OC1 fail from this order; two chains suffice', flush=True)
