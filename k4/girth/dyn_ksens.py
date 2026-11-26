"""Conjecture DYN (k4/girth.md section 5) on the counterexamples to the k = 4 conjectures OC / OC1 / RD
(coordinator's request).  EVIDENCE only.

Instances (copied, with their sources; values as given there):
  PW5   k = 5, n = 5, m = 9   k4/ksens.md section 1, branch claude/k4-ksens (refereed CORRECT, k4/referee/ksens.md)
  RD5   k = 5, n = 4, m = 7   k4/ksens.md section 6, branch claude/k4-ksens
  KG48  k = 5, n = 4, m = 8   attempts/kgen-n4-oc1.md, branch claude/kgen-n3
  B<, B>  k = 4 cores, n = 6, m = 10   k4/sdc.md (OC1 fails on a strict core), k4/sdc/oc1_core_cex_verify.py, branch
          claude/kind-lamport-y8fdme
  TTC1..TTC39  k = 4 cores, n = 5   results/k4_sdc/ttc_core_cex_39.json on claude/kind-lamport-y8fdme (copied to
          k4/girth/data/ttc_core_cex_39.json)
For each: every labeling (vertex 0 and orders of its neighbours and of the rest); LSS's Algorithm 2 with the G1 repair,
then dynamic parking; counts the labelings that complete, and also the plain Algorithm 2 for comparison.

    python3 k4/girth/dyn_ksens.py
"""
import itertools
import json
import os

from lss import Inst, labels, lss_dyn, lss_dyn_safe, is_efx0

HERE = os.path.dirname(os.path.abspath(__file__))


def from_rows(rows):
    """rows: per agent, a dict good -> value"""
    return Inst.from_dicts(rows)


INSTANCES = []
PW5_sets = [[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]]
PW5_vals = [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]]
INSTANCES.append(('PW5 (k=5)', Inst(PW5_sets, PW5_vals)))
INSTANCES.append(('RD5 (k=5)', from_rows([{1: 57, 3: 44, 5: 33, 0: 26, 4: 24}, {1: 12, 2: 11, 3: 6},
                                           {1: 9, 2: 8, 3: 6, 4: 1}, {2: 53, 5: 47, 0: 36, 6: 4}])))
KG = [[34, 0, 0, 0, 38, 35, 37, 33], [0, 10, 5, 0, 0, 4, 2, 0], [0, 2, 0, 0, 3, 0, 1, 0], [52, 54, 53, 4, 0, 0, 0, 51]]
INSTANCES.append(('KG48 (k=5)', from_rows([{g: x for g, x in enumerate(r) if x > 0} for r in KG])))
B_sets = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
B_vals = {'B<': [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]],
          'B>': [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 19], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]}
for k, v in B_vals.items():
    INSTANCES.append((k + ' (k=4 core)', Inst(B_sets, v)))
for t, d in enumerate(json.load(open(os.path.join(HERE, 'data', 'ttc_core_cex_39.json')))):
    INSTANCES.append(('TTC%d (k=4 core)' % (t + 1), Inst(d['sets'], d['vals'])))


def all_labels(I):
    for z in range(I.n):
        nb = I.neighbours(z)
        rest = [a for a in range(I.n) if a != z and a not in nb]
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                yield labels(I, z, p, q)


def main():
    print('$ python3 k4/girth/dyn_ksens.py')
    tot_inst = tot_ok = 0
    for name, I in INSTANCES:
        L = list(all_labels(I))
        safe = plain = 0
        for lab in L:
            r, Z = lss_dyn_safe(I, lab)
            if Z is not None:
                assert is_efx0(I, Z) and sorted(g for b in Z for g in b) == list(range(I.m))
                safe += 1
            plain += lss_dyn(I, lab)[1] is not None
        tot_inst += 1
        tot_ok += safe > 0
        print('%-18s n=%d m=%2d k=%d  labelings %4d: DYN (G1 repair) completes %4d, unrepaired %4d'
              % (name, I.n, I.m, max(len(r) for r in I.R), len(L), safe, plain), flush=True)
    print('instances completed by DYN for some labeling: %d of %d' % (tot_ok, tot_inst))


if __name__ == '__main__':
    main()
