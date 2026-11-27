"""Cross-check of mmlib's one-absorber enumeration against the Hall session's independent ohlib.absorb_brute
(`k4/oc1_hall/ohlib.py` on branch claude/k4-oc1-hall; pass a checkout of that branch as HALL=path).

For every kept start of the given files: the set of working absorbers at the picks (both must be empty: the start is
hard), and at the state reached by every repairing move recorded by collect.add_repairs (the sets must agree).

    HALL=/path/to/hall/checkout python3 k4/oc1max_multi/xcheck_hall.py FILE.jsonl[.gz] [...]
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, oa_absorbers

sys.path.insert(0, os.path.join(os.environ['HALL'], 'k4', 'oc1_hall'))
import ohlib


def to_hall_base(I, bases):
    b = [-1] * I.m
    for i, B in enumerate(bases):
        for g in B: b[g] = i
    return tuple(b)


if __name__ == '__main__':
    T = collections.Counter(); bad = []
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            H = ohlib.Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            st = [base_from_picks(tuple(rec['picks']))] + [tuple(tuple(b) for b in r['base']) for r in rec['repairs']]
            for j, bs in enumerate(dict.fromkeys(st)):
                a = oa_absorbers(I, bs); b = ohlib.absorb_brute(H, to_hall_base(I, bs))
                T['states'] += 1
                if a != b: bad.append((rec['name'], rec['picks'], bs, sorted(a), sorted(b)))
                if j == 0 and (a or b): bad.append(('NOT HARD', rec['name'], rec['picks']))
    print('$ python3 k4/oc1max_multi/xcheck_hall.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
    print('mismatches:', len(bad), bad[:5])
