"""Lemma B2's final rounds, described.  At every GR-visited state where no admissible round is P1-free (B2), list the
final rounds (admissible rounds after which a lifted completion exists): how many settlements, how many of them carry
an "l alone" constraint, and whether some final round of a given shape exists.

    python3 k4/base_phantom/b2_shapes.py FILE [STRIDE]
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bplib import Inst, start_state, load_rows, row_key, rounds, lifted_completion
from gr import p1free, ed_repair


def shapes(I, S0, C):
    seen = set()
    stack = [S0]
    while stack:
        S = stack.pop()
        if S.key() in seen:
            continue
        seen.add(S.key())
        if lifted_completion(I, S) is not None:
            continue
        rs = list(rounds(I, S))
        fin = [combo for combo, S2 in rs if lifted_completion(I, S2) is not None]
        free = [S2 for combo, S2 in rs if all(p1free(I, k, T) for k, P, T in combo)]
        if fin or ed_repair(I, S) is not None:
            if rs and not free:
                kinds = set()
                for combo in fin:
                    nP1 = sum(1 for k, P, T in combo if not p1free(I, k, T))
                    kinds.add('%d settlement(s), %d with l alone' % (len(combo), nP1))
                C['B2 state, %d phantoms: final-round shapes available %s' % (len(S.dead), sorted(kinds))] += 1
                C['B2 state, %d phantoms: a single-settlement final round exists: %s'
                  % (len(S.dead), any(len(c) == 1 for c in fin))] += 1
            continue
        stack.extend(free)


if __name__ == '__main__':
    fn = sys.argv[1]
    stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/base_phantom/b2_shapes.py', os.path.relpath(fn), stride)
    C = collections.Counter()
    seen = set()
    for t, r in enumerate(load_rows(fn)):
        if t % stride or row_key(r) in seen:
            continue
        seen.add(row_key(r))
        I = Inst(r['sets'], r['vals'])
        shapes(I, start_state(I, r['picks']), C)
    for k in sorted(C):
        print('  %7d  %s' % (C[k], k))
