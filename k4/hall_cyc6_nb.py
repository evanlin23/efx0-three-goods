#!/usr/bin/env python3
"""Profiles around the collision instance k4/hall_instances/cyc6.inst (k4/hall.md §3.2): change the types of the agents
in AGENTS (all strict balanced types of k4/check4.py, the others fixed as in cyc6) and compare, per profile, the
Pareto-maxima and the level-sum maxima among the pre-allocations without frozen agents (k4/hall.c -N, -N -Q1).

usage: python3 k4/hall_cyc6_nb.py AGENTS      e.g. 0 (one agent) or 03 (agents 0 and 3)"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains
from hall_run import binary

SETS = [[0, 2, 3, 12], [4, 2, 3, 5], [4, 6, 7, 13], [6, 8, 9, 12], [10, 8, 9, 11], [10, 0, 1, 14]]
BASE = [{0: 8, 2: 6, 3: 5, 12: 4}, {4: 10, 2: 8, 3: 6, 5: 3}, {4: 8, 6: 6, 7: 5, 13: 4},
        {6: 8, 8: 6, 9: 5, 12: 4}, {10: 10, 8: 8, 9: 6, 11: 3}, {10: 8, 0: 6, 1: 5, 14: 4}]

def main():
    free = {int(c) for c in sys.argv[1]}
    doms = core_domains(SETS, 15, False)
    L = ['6 15']
    for i, S in enumerate(SETS):
        D = doms[i] if i in free else [BASE[i]]
        L.append('4 ' + ' '.join(map(str, S)) + f' {len(D)}')
        for v in D: L.append(' '.join(str(v[g]) for g in S))
    L.append(f'0 {len(doms[0]) if 0 in free else 1}')
    inp = '\n'.join(L) + '\n'
    for opt, name in (([], 'Pareto-maxima'), (['-Q1'], 'level-sum maxima')):
        out = subprocess.run([binary(), '-N'] + opt, input=inp, capture_output=True, text=True, check=True).stdout
        for line in out.splitlines():
            if line.startswith('PARETO minfrozen 0'):
                w = line.split()
                print(f'agents {sys.argv[1]} free, {name} without frozen agents: profiles {w[4]}, every maximum completable {w[6]}, some {w[8]}, maxima {w[10]}')
        sys.stdout.flush()

if __name__ == '__main__':
    main()
