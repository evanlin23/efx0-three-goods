"""Least base class (base.py C0..C3) of the one-move repair at every one-move start (Phi empty), against whether pure
reduction (base_census.py form (i)) repairs the start.

    python3 k4/base_phantom/classes.py [FILES...]
"""
import sys, os, json, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bplib import Inst, start_state, load_rows, row_key
from base import base_repairs, in_class
from base_census import repairs, FORMS, DEFAULT


def job(r):
    I = Inst(r['sets'], r['vals'])
    S = start_state(I, r['picks'])
    c, w = base_repairs(I, S)
    fine = None
    if c != 'C0':
        reps = base_repairs(I, S, want_all=True)
        for cl in ('W1', 'ED'):
            if any(in_class(x[5], cl) for x in reps):
                fine = cl
                break
    return r, c, repairs(I, S, FORMS['(i)'], {}), (w[4] if w else None), fine


if __name__ == '__main__':
    files = sys.argv[1:] or DEFAULT
    rows = {}
    for fn in files:
        for r in load_rows(fn):
            rows.setdefault(row_key(r), r)
    print('$ python3 k4/base_phantom/classes.py', *[os.path.basename(f) for f in files])
    print('distinct starts:', len(rows))
    C = collections.Counter()
    with mp.Pool(4) as pool:
        for r, c, pure, f, fine in pool.imap_unordered(job, list(rows.values()), chunksize=32):
            C[('least class %s' % c, 'pure reduction repairs' if pure else 'pure reduction FAILS')] += 1
            if c != 'C0':
                C[('  beyond C0: W1 (ED with one junk good at the end) or ED', fine)] += 1
                if fine is None:
                    C[('  beyond ED', r['name'], len(r['sets']), json.dumps(r['picks']))] += 1
            if c != 'C0':
                C[('  %s repair shape' % c, 'x0 dangerous' if f['dang'] else 'x0 not dangerous',
                   'len %d' % f['len'], 'ring' if f['ring'] else 'chain')] += 1
    for k in sorted(C, key=str):
        print('  %5d  %s' % (C[k], k))
