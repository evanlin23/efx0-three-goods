"""Second implementation check of Lemma K (k4/rulef.md §2).

Reads DATA lines of k4/rulef.c -A40 (one leaf representative profile each, with the C deficits kN, kE per first agent)
and, for every first agent a and both upgrade policies, recomputes the Lemma K deficit with k4/rulef_model.py (written
from the text on PR #33's independent model of LB4r). Checks:
  (1) where the Python deficit is <= 0, the completion built as in the proof of Lemma K is an Output of LB4R.lean
      (lb4r.output_check, owner's needs from the bundle) and is EFX0 by the raw definition;
  (2) the C deficit (k4/rulef.c, slot goods restricted) is never below the Python one (both count the same object;
      the C version only drops options), and agrees on the sign (<= 0 or not) unless noted as a C restriction.
Usage: rulef_check.py DATAFILE [--max=N]"""
import json, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rulef_model as RM
import lb4r as M

F = ['rot', 'cov', 'dN', 'dE', 'hN', 'hE', 'omN', 'omE', 'fz', 'e4', 'r', 'uN', 'uE', 'kN', 'kE', 'c40']


def main():
    path = sys.argv[1]
    mx = int(next((a.split('=')[1] for a in sys.argv[2:] if a.startswith('--max=')), 10 ** 9))
    nprof = nchk = nwit = bad = below = signdiff = 0
    for line in open(path):
        if not (line.startswith('DATA') or line.startswith('IDX')): continue
        if nprof >= mx: break
        nprof += 1
        sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
        vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
        names = F if line.startswith('DATA') else ['kN', 'kE', 'c40', 'omN', 'k1']
        fa = [dict(zip(names, map(int, x.split(':')[1].split(',')))) for x in line.split('fa=')[1].strip().split(';')]
        inst = RM.make_inst(sets, vals)
        for a in range(inst.n):
            for pol, key in (('shrink', 'kN'), ('envyFree', 'kE')):
                s, _ = RM.run_state(inst, a, pol)
                d = RM.deficit_K(inst, s)
                c = fa[a][key]
                c = RM.NEG if c == -100 else (RM.INF if c >= 999 else c)
                nchk += 1
                if c < d:
                    below += 1
                    print('C BELOW PYTHON', a, pol, c, d, sets, vals)
                if (c <= 0) != (d <= 0):
                    signdiff += 1
                if d <= 0:
                    w = RM.witness_K(inst, s)
                    o, X = w
                    ok = M.output_check(inst, s, o, X, 'bundle') and RM.check_efx0(inst, X)
                    nwit += 1
                    if not ok:
                        bad += 1
                        print('WITNESS FAILS', a, pol, o, X, sets, vals)
    print(f'{path}: profiles {nprof}, (first agent, policy) pairs {nchk}, witnesses checked {nwit}, '
          f'witness failures {bad}, C deficit below Python {below}, sign differences (C restriction) {signdiff}')


if __name__ == '__main__':
    main()
