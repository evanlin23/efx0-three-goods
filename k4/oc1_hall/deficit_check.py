"""The S* deficit (ohlib.deficit, k4/oc1_hall.md §4) against the raw S* completion test, and its values at hard
starts and after repairing chains.  For every distinct start and every unfrozen single-good owner o:
  deficit(o) <= 0  <=>  ohlib.shaped_completion(o) (S* completion with owner o)          [checked: Lemma 3]
For hard starts: the least deficit over unfrozen owners, and over all owners.  NOTE: for a frozen owner the deficit
ignores (S1) (wanters of the owner's pick), so only unfrozen owners are compared exactly.

    python3 k4/oc1_hall/deficit_check.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, shaped_completion, s_star_deficits
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/deficit_check.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y); P = Picks(I, Y)
            B = bundles_of(I, base); F = set(frozen_set(I, base))
            holders = [j for j in range(n) if len(B[j]) <= 1 and j not in F]
            U = [o for o in range(n) if o not in F]
            d = s_star_deficits(I, base, U)
            for o in U:
                ex = shaped_completion(I, base, o, holders)
                ok = d[o][0] is not None and d[o][0] <= 0
                C['owner tests'] += 1
                if ex != ok:
                    C['MISMATCH'] += 1; print('MISMATCH', name, json.dumps((sets, vals)), 'picks', Y, 'o', o, ex, d[o], flush=True)
            anyok = any(d[o][0] is not None and d[o][0] <= 0 for o in U)
            if not anyok:
                C['starts with no unfrozen owner'] += 1
                ds = [d[o][0] for o in U if d[o][0] is not None]
                C['  least unfrozen-owner deficit %s' % (min(ds) if ds else None)] += 1
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
