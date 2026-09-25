#!/usr/bin/env python3
"""Cross-check k4/c4x.c against the independent k4/c4x_check.py, profile by profile.

usage: python3 k4/c4x_crosscheck.py FILE [--all | --rand=N] [--seed=S] [--only=I,J] [--w0]
For each core of FILE (or --only), the Python checker analyses the profiles (all, or N random ones) and c4x -v
analyses the same profiles; the lines (#valid, #completable, every/some flags of six potentials) must agree."""
import gzip, json, sys, os, subprocess, itertools, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains
import c4x_check, c4x_run

def main():
    f = sys.argv[1]
    allp, rand, seed, only, w0 = False, 50, 1, None, False
    for a in sys.argv[2:]:
        if a == '--all': allp = True
        elif a.startswith('--rand='): rand = int(a[7:])
        elif a.startswith('--seed='): seed = int(a[7:])
        elif a.startswith('--only='): only = [int(x) for x in a[7:].split(',')]
        elif a == '--w0': w0 = True
    data = json.load(gzip.open(f, 'rt'))
    b = c4x_run.binary()
    total = mism = 0
    for ci, core in enumerate(data['cores']):
        if only is not None and ci not in only: continue
        n, m, sets = core['n'], core['m'], core['sets']
        doms = core_domains(sets, m, False)
        if allp: profs = list(itertools.product(*[range(len(D)) for D in doms]))
        else:
            rng = random.Random(seed * 7919 + ci)
            profs = [tuple(rng.randrange(len(D)) for D in doms) for _ in range(rand)]
        inp, _ = c4x_run.core_input(core)
        inp += f'\n0 {len(doms[0])}\n{len(profs)}\n' + '\n'.join(' '.join(map(str, p)) for p in profs) + '\n'
        out = subprocess.run([b, '-v', '-R', '-p', c4x_check.C_POTS] + (['-w0'] if w0 else []), input=inp, capture_output=True, text=True, check=True).stdout
        cl = [l for l in out.splitlines() if l.startswith('PROF')]
        for p, cline in zip(profs, cl):
            vals_list = [doms[i][p[i]] for i in range(n)]
            res = c4x_check.analyse(sets, m, vals_list, w0)
            flags = []
            for pot in c4x_check.POTS:
                best = max(r[2][pot] for r in res)
                mx = [r for r in res if r[2][pot] == best]
                flags.append(f'{int(all(r[1] for r in mx))}{int(any(r[1] for r in mx))}')
            pline = ' '.join(['PROF', *map(str, p), str(len(res)), str(sum(r[1] for r in res)), *flags])
            total += 1
            if pline != cline:
                mism += 1
                print('MISMATCH core', ci, '\n  py:', pline, '\n  c: ', cline)
        print(f'core {ci}: {len(profs)} profiles checked', flush=True)
    print(f'CROSSCHECK {f} profiles {total} mismatches {mism}')

if __name__ == '__main__':
    main()
