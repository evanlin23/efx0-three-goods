"""Write the n = 2 and n = 3 core lists of results/k4_certs_{2,3}.json.gz split by the number of 4-good agents
(results/k4_c4_split/k4_certs_{2,3}_n4eq{K}.json.gz; only the core lists, in the same format, for k4/lb4_run.py)."""
import gzip, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'results', 'k4_c4_split')
os.makedirs(OUT, exist_ok=True)
for n in (2, 3):
    d = json.load(gzip.open(os.path.join(HERE, '..', 'results', f'k4_certs_{n}.json.gz'), 'rt'))
    for k in range(1, n + 1):
        cs = [{'m': c['m'], 'sets': c['sets']} for c in d['cores'] if sum(len(s) == 4 for s in c['sets']) == k]
        if cs:
            json.dump({'ties': False, 'cores': cs}, gzip.open(os.path.join(OUT, f'k4_certs_{n}_n4eq{k}.json.gz'), 'wt'))
            print(f'k4_certs_{n}_n4eq{k}.json.gz: {len(cs)} cores')
