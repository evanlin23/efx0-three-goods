"""Which weaker forms of OC repair a given start?  k4/sdc's own machinery (de_free.search: BFS over improving chains,
unbounded sets; oc_absorb.extends_A: completion with at most A absorbers; de_free.extends: free completion).

    python3 kgen/weaker_n.py '<json v>' 'o0,o1,...'"""
import sys, os, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
import _paths  # noqa
import de_free as DF
from sdclib import Enc
from oc_absorb import extends_A
from sdc_orders import sd

if __name__ == '__main__':
    v = json.loads(sys.argv[1]); order = list(map(int, sys.argv[2].split(','))); n, m = len(v), len(v[0])
    DF.HMAX = m; DF.BMAX = m; DF.CAP = 200000
    sets = [[g for g in range(m) if v[i][g] > 0] for i in range(n)]
    E = Enc(sets, [[v[i][g] for g in sets[i]] for i in range(n)], m)
    Y = sd(E, order)[0]; base = [-1] * m
    for i, g in enumerate(Y):
        if g is not None: base[g] = i
    base = tuple(base)
    print('picks', Y)
    orig = DF.extends
    for label, ext, chain_only in [('free completion, chains only', orig, True), ('free completion, chains and rings', orig, False),
                                   ('one absorber, chains only', lambda E, b: extends_A(E, b, 1), True),
                                   ('two absorbers, chains only', lambda E, b: extends_A(E, b, 2), True),
                                   ('three absorbers, chains only', lambda E, b: extends_A(E, b, 3), True)]:
        DF.CHAIN_ONLY = chain_only; DF.extends = ext
        print('%-36s least number of moves: %s' % (label, DF.search(E, base, {})), flush=True)
    DF.extends = orig
