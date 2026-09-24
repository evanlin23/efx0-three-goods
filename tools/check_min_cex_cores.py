"""Checks that a certificate file covers every core that proofs/min_counterexample.md §5 leaves open.
Given the complete list of connected cores for some (n, m) (its completeness is checked by tools/check_enum.py) and a
certificate file (checked by tools/check_certs.py), recomputes, independently of src/min_cex_cores.py, which cores have
no good of degree 2 valued by two agents that have a private good, and checks that each of them appears in the
certificate file with the same hypergraph (same list of agents' goods).
Usage: check_min_cex_cores.py full_list.json.gz certs.json.gz [certs.json.gz ...]"""
import sys, json, gzip


def keeps(sets):
    count = {}
    for S in sets:
        for x in S: count[x] = count.get(x, 0) + 1
    has_private = [any(count[x] == 1 for x in S) for S in sets]
    for x, c in count.items():
        if c == 2 and all(has_private[i] for i, S in enumerate(sets) if x in S): return False
    return True


full = json.load(gzip.open(sys.argv[1], 'rt'))
certified = {(r['n'], r['m'], json.dumps([sorted(S) for S in r['sets']])) for path in sys.argv[2:]
             for r in json.load(gzip.open(path, 'rt'))}
missing, kept = 0, {}
for r in full:
    if not keeps(r['sets']): continue
    kept[(r['n'], r['m'])] = kept.get((r['n'], r['m']), 0) + 1
    if (r['n'], r['m'], json.dumps([sorted(S) for S in r['sets']])) not in certified:
        print('no certificate for', r['n'], r['m'], r['sets']); missing += 1
print('cores in the list: %d; kept by the filter: %s; without certificate: %d' % (len(full), kept, missing))
sys.exit(1 if missing else 0)
