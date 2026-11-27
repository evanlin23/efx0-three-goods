"""How many k = 4 core hypergraphs (results/k4_certs_*.json.gz) are linear, and how many satisfy Theorem T1 (linear with
an agent on no 3-cycle; then every monotone profile on them has an EFX0 allocation)?  k4/girth.md section 4.

    python3 k4/girth/core_stats.py
"""
import collections

from lss import Inst, two_cycles, triangles
from sources import cores


def main():
    print('$ python3 k4/girth/core_stats.py')
    for n in (2, 3, 4, 5, 6):
        C = collections.Counter()
        for f, idx, sets, m in cores(n):
            I = Inst(sets, [[1] * len(S) for S in sets], m)
            C['cores'] += 1
            if two_cycles(I):
                continue
            C['linear'] += 1
            on = set()
            for x, y, z, w in triangles(I):
                on |= {x, y, z}
            if len(on) < I.n:
                C['linear, an agent on no 3-cycle (T1)'] += 1
            if not triangles(I):
                C['linear and triangle-free (LSS itself)'] += 1
        print('n = %d: %s' % (n, dict(C)), flush=True)


if __name__ == '__main__':
    main()
