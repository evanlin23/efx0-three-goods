#!/usr/bin/env python3
"""State-by-state comparison of two implementations of the R_134 / T4 test (compute/k4-dl13). EVIDENCE tooling.

  python3 k4/dl134_compare.py --tsv=STATES.tsv[,...] XCHECK.jsonl.gz ...

STATES.tsv: per-state results of compute/k4-dl134's k4/dl134.c (`k4/dl134_run.py tsv ... --out=...`; columns file, pos,
idx, m, profile, bases, found, f, def, k, r13dist, rdist, branch, t4types, dT4, sig; branch: the kinds of the improving
R_134 moves, e.g. "T4" or "T3p+T4", "none" if R_134 fails; t4types: the cycle lengths of the improving T4 moves).
XCHECK.jsonl.gz: per-state output of this workstream's k4/dl134_xcheck.py (c4x_check.py with membership tests written
separately; kinds t1, t2, t3p, t3h, t4, t4s2 and the relation verdicts).
For every state of the TSV, compares: the state is found by both; def; R_134 holds; T1, T3 (plain / with a helper) and
T4 present; a 2-swap present (t4types contains 2 / t4s2). Prints the mismatches and the totals."""
import ast, csv, gzip, json, sys


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    files = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/dl134_compare.py ' + ' '.join(argv), flush=True)
    mine = {}
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            c = r['core']
            key = (c.get('file'), int(c.get('pos', -1)), ','.join(map(str, r['prof'])), json.dumps([sorted(b) for b in r['B']]))
            mine[key] = r
    rows = []
    for t in opt['tsv'].split(','):
        with open(t) as fo:
            rows += list(csv.DictReader(fo, delimiter='\t'))
    n = bad = missing = 0; agree = {'R134': 0, 'T1': 0, 'T3': 0, 'T4': 0, 'T4s2': 0, 'def': 0}
    for row in rows:
        n += 1
        B = [sorted(b) for b in ast.literal_eval(row['bases'])]
        key = (row['file'], int(row['pos']), row['profile'], json.dumps(B))
        r = mine.get(key)
        if r is None:
            missing += 1; print('MISSING in the xcheck output:', key, flush=True); continue
        br = row['branch'].split('+') if row['branch'] != 'none' else []
        t4t = set(x for x in row['t4types'].split(',') if x and x != '-')
        cmp = {'def': int(row['def']) == r['def'],
               'R134': (row['branch'] != 'none') == bool(r['holds']['R134']),
               'T1': ('T1' in br) == bool(r['kinds']['t1']),
               'T3': (('T3p' in br) or ('T3h' in br)) == bool(r['kinds']['t3p'] or r['kinds']['t3h']),
               'T4': ('T4' in br) == bool(r['kinds']['t4']),
               'T4s2': ('2' in t4t) == bool(r['kinds']['t4s2'])}
        for k, v in cmp.items(): agree[k] += v
        if not all(cmp.values()):
            bad += 1; print('MISMATCH', key, {k: v for k, v in cmp.items() if not v}, 'tsv', dict(row), 'xcheck', r['kinds'], r['holds'], flush=True)
    print(f'states in the TSV {n}; found in the xcheck output {n - missing}; agreeing on ' +
          ', '.join(f'{k} {v}' for k, v in agree.items()) + f'; states with a mismatch {bad}, missing {missing}', flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
