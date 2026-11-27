"""The ten n = 3 failures of TTC2 (results/k4_ttc/ttc2_data.log): does any YRMH-IGYT run (every head, the 25 head/inner
pairs of val, minval, minimal, lean, small, modes one/head/full) repair them?  And which improving chains repair
(k4/ttc.md §5)?  Log: results/k4_ttc/ttc2_failures_union.log.

    python3 k4/ttc/ttc2_fail_union.py"""
import ttclib as T

BASIC = ['val', 'minval', 'minimal', 'lean', 'small']
PREFS = [h + '/' + i for h in BASIC for i in BASIC]
FAILS = [('log59', [[0, 2, 3], [2, 4, 0], [1, 2, 3, 0]], [[36, 35, 12], [33, 18, 30], [29, 46, 19, 32]], 5, [1, 2, 0]),
         ('log69', [[0, 3, 2, 1], [1, 2, 4], [1, 2, 4, 3]], [[16, 35, 36, 13], [37, 12, 34], [27, 31, 9, 13]], 5, [0, 2, 1]),
         ('r457', [[0, 2, 4, 5], [1, 3, 4, 5], [2, 3, 5]], [[3, 6, 4, 8], [4, 5, 6, 8], [4, 2, 3]], 6, [1, 0, 2]),
         ('r1174', [[0, 2, 4, 5], [1, 4, 5], [3, 4, 5]], [[6, 3, 5, 7], [2, 4, 3], [2, 3, 4]], 6, [0, 1, 2]),
         ('r1563', [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[6, 8, 10, 3], [2, 4, 8, 3], [3, 7, 6, 5]], 6, [0, 1, 2]),
         ('r1889', [[0, 2, 3, 4], [1, 2, 3, 4], [2, 3, 4]], [[5, 6, 7, 3], [4, 1, 6, 8], [2, 3, 4]], 5, [0, 2, 1]),
         ('r2122', [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]], [[4, 3, 10, 8], [4, 3, 10, 8], [6, 8, 3, 10]], 8, [0, 2, 1]),
         ('r2249', [[0, 2, 4, 5], [1, 4, 5], [3, 4, 5]], [[4, 5, 8, 6], [2, 4, 3], [2, 3, 4]], 6, [1, 0, 2]),
         ('r2244', [[0, 2, 5, 6], [1, 4, 5, 6], [3, 5, 6]], [[3, 2, 10, 6], [8, 4, 3, 10], [2, 4, 3]], 7, [0, 1, 2]),
         ('r2254', [[0, 2, 3, 4], [1, 2, 3, 4], [1, 3, 4]], [[4, 3, 8, 10], [4, 6, 3, 8], [2, 4, 3]], 5, [1, 2, 0])]

if __name__ == '__main__':
    for name, sets, vals, m, pi in FAILS:
        E = T.Enc(sets, vals, m); Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
        states = set()
        for pref in PREFS:
            for p in range(E.n):
                prio = [p] + [i for i in pi[::-1] if i != p]
                for mode in ('one', 'head', 'full'):
                    b2, tr = T.yrmh(E, b, prio, pref, 'pi', mode)
                    if tr:
                        states.add(b2)
        rep = [T.bundles(E, s) for s in states if T.extends_A(E, s, 1)]
        chains = [T.bundles(E, s) for s in set(T.DF.iter_chains(E, b)) if T.extends_A(E, s, 1)]
        print(name, 'picks', Y, 'frozen', sorted(T.frozen_set(E, b)), 'TTC runs', len(states), 'repairing TTC runs',
              len(rep), '| repairing chains', chains[:4])
