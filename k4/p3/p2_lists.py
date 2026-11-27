"""Write the n = 5 core lists restricted to cores in which every good has at most two valuers (the multigraph cores),
in the format of results/k4_certs_5_*.json.gz, so that k4/oc1cert/run.py (workstream compute/k4-oc1max-cert) can certify
them: results/k4_certs_5_<LIST>_p2.json.gz in the checkout given as the first argument (676 cores: n4_1 49, n4_2 136,
n4_3 221, n4_4 181, pure 89).
    python3 k4/p3/p2_lists.py CHECKOUT_OF_compute/k4-oc1max-cert
then, in that checkout:
    python3 k4/oc1cert/run.py 5_n4_1_p2,5_n4_2_p2,5_n4_3_p2,5_n4_4_p2,5_pure_p2 --out=cert_5_p2.json.gz --jobs=4   (~22 min)
    python3 k4/oc1cert/check.py cert_5_p2.json.gz --lists=5_n4_1_p2,5_n4_2_p2,5_n4_3_p2,5_n4_4_p2,5_pure_p2   (~6 min)
"""
import gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
dst = sys.argv[1]
for lst in ('n4_1', 'n4_2', 'n4_3', 'n4_4', 'pure'):
    d = json.load(gzip.open(os.path.join(ROOT, 'results', f'k4_certs_5_{lst}.json.gz'), 'rt'))
    keep = [c for c in d['cores'] if max(sum(g in S for S in c['sets']) for g in range(c['m'])) <= 2]
    o = dict(d); o['cores'] = keep
    with gzip.open(os.path.join(dst, 'results', f'k4_certs_5_{lst}_p2.json.gz'), 'wt') as f: json.dump(o, f)
    print(lst, len(d['cores']), '->', len(keep))
