"""Classify the failures of one mechanism configuration (k4/ttc.md §4): for every hard start where the run ends
without a one-absorber completion, follow its trades ('rep' runs one trade at a time) and record
  - whether the start and each later state are value-dominated by a complete EFX0 allocation (ttclib.dominated);
  - the first trade after which the state is no longer dominated (the mechanism overshoots), or
  - that every state stays dominated and the run stalls (no request path closes), and whether some improving chain
    (de_free) from the stall state has a one-absorber completion.

    python3 k4/ttc/ttc_fail.py SRC [N SEED] pref=minval prio=rev [nmax=5]"""
import sys, random, collections, json, time
import ttclib as T


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a)
    pref, prio = kw.get('pref', 'minval'), kw.get('prio', 'rev'); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/ttc_fail.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); shown = 0
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m)
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
            if T.extends_A(E, b, 1):
                continue
            C['hard starts'] += 1
            states = [b]; k = 0
            while not T.extends_A(E, b, 1) and k < 4 * n:
                b2, tr = T.yrmh(E, b, pi, pref, prio, 'one')
                if not tr:
                    break
                b = b2; states.append(b); k += 1
            if T.extends_A(E, b, 1):
                C['repaired'] += 1; C['repaired after %d trades' % k] += 1
                continue
            dom = [T.dominated(E, s) for s in states]
            if all(dom):
                C['fail: stalls while dominated'] += 1
                rep = any(T.extends_A(E, b3, 1) for b3 in set(T.DF.iter_chains(E, b)))
                C['fail: stalls while dominated, a chain repairs the stall state'] += rep
                kind = 'stall'
            else:
                first = dom.index(False)
                C['fail: leaves the dominated region at trade %d' % first] += 1
                kind = 'overshoot at trade %d' % first
            if shown < 6:
                shown += 1
                print('FAIL (%s)' % kind, name, json.dumps((sets, vals)), 'order', pi, 'picks', Y,
                      'states', [T.bundles(E, s) for s in states], flush=True)
    for k_ in sorted(C):
        print(k_, C[k_])
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
