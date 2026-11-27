"""R1-priority picks versus maximum-matching picks (k4/oc1_hall.md §19).  Per instance: nu (maximum matching size);
the set of plain SD pick vectors, of R1-priority SD pick vectors, and of plain pick vectors forming a maximum matching.
Reports: R1-priority pick vectors that are not maximum matchings; maximum-matching pick vectors that no R1-priority
order produces.

    python3 k4/oc1_hall/r1_vs_max.py SRC
"""
import sys, os, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks
from max_matching import nu
from sdclib import Enc
from sdc_orders import sd
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/oc1_hall/r1_vs_max.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); N = nu(I)
        plain = set(); r1 = set()
        for od in itertools.permutations(range(n)):
            plain.add(picks(I, od)); r1.add(tuple(sd(E, list(od), True)[0]))
        size = lambda Y: sum(1 for y in Y if y is not None)
        mx = set(Y for Y in plain if size(Y) == N)
        C['instances'] += 1
        C['R1-priority pick vectors'] += len(r1); C['  of them not a maximum matching'] += sum(1 for Y in r1 if size(Y) != N)
        C['maximum-matching pick vectors'] += len(mx); C['  of them produced by no R1-priority order'] += len(mx - r1)
        C['instances where some R1-priority pick vector is not maximum'] += any(size(Y) != N for Y in r1)
        C['instances where nu < n'] += N < n
    for k in sorted(C): print(k, C[k])
