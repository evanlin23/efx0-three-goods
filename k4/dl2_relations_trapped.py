#!/usr/bin/env python3
"""DL_R on the exhaustive n = 3 dump of the compute/k4-dl2 workstream (k4/dl2.md §3): every min-frozen P with def > 0
and least repair distance k* >= 3 of every strict profile of every n = 3 core, with every least-distance repair P'
(`results/k4_dl2/trapped_n3.jsonl.gz` on that branch, written by its C tool `k4/dl2.c`). At n = 3 the distance is at
most 3, so these repairs are all the min-frozen P' with a smaller deficit. For each P, tests whether some repair is a
move of R (membership written in k4/dl2_relations_xcheck.py, independent of k4/dl2_relations.py; the P' and deficits
are the compute tool's). With --model=E, every E-th profile is also recomputed with k4/dl2_relations.py on
k4/suite/model.py and compared (deficit, k*, DL_R).
usage: python3 k4/dl2_relations_trapped.py DUMP [--model=E]"""
import gzip, json, os, sys
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from dl2_relations_xcheck import rel_B, REL_B


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--'))
    E = int(opt.get('model', 0))
    print('# command: python3 k4/dl2_relations_trapped.py ' + ' '.join(argv), flush=True)
    fails = {r: Counter() for r in REL_B}; nst = Counter(); profs = {}; verdict = {}; mism = 0; nmod = 0
    for l in gzip.open(argv[0], 'rt'):
        x = json.loads(l)
        sets = x['core']['sets']; vals = x['vals']; f = x['f']
        P = tuple(frozenset(b) for b in x['P'])
        key = (x['core']['file'], x['core']['m'], x['core']['idx'], tuple(x['prof']))     # core named by (m, idx)
        profs.setdefault(key, (sets, vals, x['m'], f)); nst[f] += 1
        v = verdict[(key, tuple(tuple(sorted(b)) for b in x['P']))] = {}
        for r in REL_B:
            v[r] = any(rel_B(r, sets, vals, P, tuple(frozenset(b) for b in rp['B2'])) for rp in x['repairs']
                       if rp['def2'] < x['def'])
            if not v[r]:
                fails[r][f] += 1
                if r == 'RTr' or (r == 'R13' and f >= 1 and fails[r][f] <= 20):
                    print('%s FAILS' % r, key, 'f', f, 'P', x['P'], flush=True)
    print('states (P with k* >= 3) %d in %d profiles; by f: %s' % (sum(nst.values()), len(profs), dict(sorted(nst.items()))))
    for r in REL_B:
        print('%-6s fails at %d states, by f: %s' % (r, sum(fails[r].values()), dict(sorted(fails[r].items()))), flush=True)
    if E:
        import dl2_relations as DR
        for i, (key, (sets, vals, m, f)) in enumerate(sorted(profs.items())):
            if i % E: continue
            nmod += 1
            st = {tuple(tuple(b) for b in r['Bs']): r for r in DR.profile({'sets': sets, 'vals': vals, 'm': m})}
            got = {P for P, r in st.items() if r['k'] is not None and r['k'] >= 3}
            mine = {P for (k2, P) in verdict if k2 == key}
            if got != mine or any(st[P]['holds'][r] != verdict[(key, P)][r] for P in got for r in REL_B):
                mism += 1; print('MODEL MISMATCH', key, sorted(got ^ mine)[:3], flush=True)
        print('model recheck: %d profiles, mismatches %d (the set of P with k* >= 3, and DL_R there for %s)' % (
            nmod, mism, ', '.join(REL_B)))

if __name__ == '__main__':
    main(sys.argv[1:])
