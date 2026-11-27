"""The two-move starts with no P1-free admissible round (second implementation; primitives of check_deadends.py).

At a two-move start (no one-absorber completion, no official move followed by one), the P1-free greedy process of
rules.py has nothing to do if every admissible round settles some agent with an "l alone" constraint.  For every
start of FILE this script recomputes, independently of bplib/base/rules: hardness at the picks, the absence of a
one-move repair, and whether some admissible round has only P1-free settlements.  It lists the starts with none.

    python3 k4/base_phantom/verify_nop1_gap.py FILE
"""
import sys, os, json, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_deadends import Instance, one_absorber, admissible_rounds, official_moves
from check_rules import rows_of, p1free


def job(row):
    sets, vals, picks = row
    I = Instance(sets, vals)
    X = [{g} for g in picks]
    al = list(range(I.n))
    R = admissible_rounds(I, X, al)
    free = [c for c, Y, a2 in R if all(p1free(I, k, T) for k, P, T in c)]
    if free:
        return row, None
    hard = one_absorber(I, X, al) is None
    move = any(one_absorber(I, Y, al) is not None for P, H0, Hs, Y in official_moves(I, X, al))
    return row, (hard, move, len(R))


if __name__ == '__main__':
    fn = sys.argv[1]
    print('$ python3 k4/base_phantom/verify_nop1_gap.py', fn)
    seen = set()
    rows = []
    for r in rows_of(fn):
        k = json.dumps(r)
        if k not in seen:
            seen.add(k)
            rows.append(r)
    C = collections.Counter()
    out = []
    with mp.Pool(4) as pool:
        for row, res in pool.imap_unordered(job, rows, chunksize=8):
            if res is None:
                C['some P1-free admissible round at the start'] += 1
                continue
            hard, move, nr = res
            C['no P1-free admissible round at the start: hard %s, one-move repair %s, admissible rounds %s'
              % (hard, move, 'yes' if nr else 'none')] += 1
            out.append(row)
    for k in sorted(C):
        print('  %6d  %s' % (C[k], k))
    for row in sorted(out, key=lambda r: (len(r[0]), json.dumps(r))):
        print('  ', json.dumps({'sets': row[0], 'vals': row[1], 'picks': row[2]}))
