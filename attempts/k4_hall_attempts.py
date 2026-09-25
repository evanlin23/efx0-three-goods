#!/usr/bin/env python3
"""Replay the smallest failing configurations of attempts/k4-hall-*.md with both implementations:
k4/hall.c (enumeration of all valid pre-allocations, exact removal-only deficit) and the independent plain-Python
k4/hall_check.py (every completion literally, raw EFX0 re-check). Prints "confirmed" for each claim."""
import os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4'))
from hall_run import binary

def hall_input(path):
    vals, bases = [], None
    for line in open(path):
        w = line.split()
        if w and w[0] == 'agent': vals.append([tuple(map(int, t.split(':'))) for t in w[1:]])
    m = 1 + max(g for a in vals for g, _ in a)
    L = [f'{len(vals)} {m}']
    for a in vals:
        L.append(f'{len(a)} ' + ' '.join(str(g) for g, _ in a) + ' 1'); L.append(' '.join(str(x) for _, x in a))
    return '\n'.join(L) + '\n0 1\n'

def main():
    ok = True
    # 1. attempts/k4-hall-pareto-no-frozen.md: a Pareto-maximal valid pre-allocation without frozen agents that is not
    #    completable (pure core, n = 6, m = 15); some other one is.
    inst = os.path.join(ROOT, 'k4', 'hall_instances', 'cyc6.inst')
    out = subprocess.run([binary(), '-1', '-P', '-Px', '1'], input=hall_input(inst), capture_output=True, text=True, check=True).stdout
    c1 = 'PARETO minfrozen 0 profiles 1 every_ok 0 some_ok 1' in out and 'bases {2,3} {4,5} {6,7} {8,9} {10,11} {0,1} J {12,13,14} omega 3 def 1' in out
    out2 = subprocess.run([sys.executable, os.path.join(ROOT, 'k4', 'hall_check.py'), inst], capture_output=True, text=True, check=True).stdout
    c2 = all(s in out2 for s in ('valid True frozen []', 'fewest frozen 0, Pareto-maximal True', 'completable False', 'removal-only completable False'))
    print(f'cyc6: hall.c {"confirmed" if c1 else "NOT confirmed"}; hall_check.py {"confirmed" if c2 else "NOT confirmed"}')
    ok &= c1 and c2
    # 2. k4/hall.md §5: a Pareto-maximum with only local frozen exposures (no (G), no (G1)) that is not completable
    #    (n = 3, m = 7; core 33 of results/k4_certs_3.json.gz).
    inst = os.path.join(ROOT, 'k4', 'hall_instances', 'local3.inst')
    out = subprocess.run([binary(), '-1', '-N', '-d'], input=hall_input(inst), capture_output=True, text=True, check=True).stdout
    c1 = 'PM bases {2}F {5,6} {3,4} J {0,1} T 1 omega 2 def 1' in out
    out2 = subprocess.run([sys.executable, os.path.join(ROOT, 'k4', 'hall_check.py'), inst], capture_output=True, text=True, check=True).stdout
    c2 = all(s in out2 for s in ('valid True frozen [0]', 'fewest frozen 1, Pareto-maximal True', 'completable False', 'removal-only completable False'))
    print(f'local3: hall.c {"confirmed" if c1 else "NOT confirmed"}; hall_check.py {"confirmed" if c2 else "NOT confirmed"}')
    ok &= c1 and c2
    # 3. attempts/k4-hall-bt-n4.md: a non-completable Pareto-maximum at the fewest frozen agents without a frozen
    #    big-top agent (pure n = 4, m = 7; core 59 of results/k4_certs_4_pure.json.gz): conjecture BT is false.
    inst = os.path.join(ROOT, 'k4', 'hall_instances', 'bt4.inst')
    out = subprocess.run([binary(), '-1', '-N', '-d'], input=hall_input(inst), capture_output=True, text=True, check=True).stdout
    c1 = 'PM bases {2,5} {0,3} {4}F {6}F J {1} T 2 omega 1 def 1' in out
    out2 = subprocess.run([sys.executable, os.path.join(ROOT, 'k4', 'hall_check.py'), inst], capture_output=True, text=True, check=True).stdout
    c2 = all(s in out2 for s in ('valid True frozen [2, 3]', 'fewest frozen 2, Pareto-maximal True', 'completable False', 'removal-only completable False'))
    print(f'bt4: hall.c {"confirmed" if c1 else "NOT confirmed"}; hall_check.py {"confirmed" if c2 else "NOT confirmed"}')
    ok &= c1 and c2
    print('ALL CONFIRMED' if ok else 'SOME NOT CONFIRMED')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
