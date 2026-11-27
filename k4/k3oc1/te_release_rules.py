"""Release lemma (k4/k3_oc1.md §12.1, Lemma 5): which simple rule picks a valid Rule E rotation with few remaining
needs, omega' <= 1 (or <= 0)?  Rules: least omega' (the target), sigma-first k, sigma-last k, longest chain, and the
same restricted to k with {b_k, c_k} inside J (rule P's class).  On GAP lines.
    python3 k4/k3oc1/te_release_rules.py gapfile:FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import read_lines
from te_rules import results
C = collections.Counter()
for a in sys.argv[1:]:
    for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]
        R = results(rk, int(mt.group(2)), ast.literal_eval(mt.group(3)), ast.literal_eval(mt.group(4)))
        if not R: continue
        tag = '|T| %s: ' % mt.group(5)
        jp = [r for r in R if not r['arrow']]
        rules = {'least omega': min(R, key=lambda r: r['om']), 'sigma-first': min(R, key=lambda r: r['pos']),
                 'sigma-last': max(R, key=lambda r: r['pos']), 'longest (sigma-first tie)': min(R, key=lambda r: (-r['len'], r['pos']))}
        if jp:
            rules.update({'junk-pair sigma-first': min(jp, key=lambda r: r['pos']), 'junk-pair sigma-last': max(jp, key=lambda r: r['pos']),
                          'junk-pair longest': min(jp, key=lambda r: (-r['len'], r['pos'])), 'junk-pair least omega': min(jp, key=lambda r: r['om'])})
        for nm, r in rules.items():
            C[tag + '%-28s omega\' <= 1 %s; completes %s' % (nm, r['om'] <= 1, r['ok'])] += 1
for k in sorted(C): print(C[k], k)
