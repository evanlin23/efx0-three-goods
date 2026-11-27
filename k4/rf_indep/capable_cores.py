"""The pure n = 5 cores on which the certifier met OC1^max failures, and its stored failing starts on them, from its
chunk summaries (compute/k4-oc1max-cert, results/k4_oc1max/n5/5_pure_s5o0_summary.jsonl.gz and ..._s5o1_...): a core
is failure-capable when its record has '2 moves' pairs or stored oc1_fails.  Cores are named (m, idx) as in
results/k4_certs_5_pure.json.gz (checked by their sets).  Workstream compute/k4-rf-offexport.

    python3 k4/rf_indep/capable_cores.py DIR    # DIR holds the two summaries
writes results/k4_rf_offexport/n5_failure_capable_cores.json.gz and n5_stored_fails_seeds.jsonl.gz
"""
import sys, os, gzip, json, collections
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
EXPORT = {(9, 38), (10, 419), (11, 447), (8, 164), (8, 374), (8, 379), (8, 464), (9, 778), (9, 808)}

if __name__ == '__main__':
    d = sys.argv[1]
    cert = {(c['m'], c['idx']): c for c in json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_5_pure.json.gz')))['cores']}
    cores = []; seeds = []
    for fn in ('5_pure_s5o0_summary.jsonl.gz', '5_pure_s5o1_summary.jsonl.gz'):
        for line in gzip.open(os.path.join(d, fn), 'rt'):
            r = json.loads(line)
            if not (r.get('stats', {}).get('kinds', {}).get('2 moves', 0) or r.get('oc1_fails')): continue
            if cert[(r['m'], r['idx'])]['sets'] != r['sets']: raise SystemExit('core mismatch %s' % ((r['m'], r['idx']),))
            cores.append(dict(sets=r['sets'], m=r['m'], idx=r['idx'], export=(r['m'], r['idx']) in EXPORT, chunk=fn[7:11]))
            for f in r.get('oc1_fails') or []:
                seeds.append(dict(core_m=r['m'], core_idx=r['idx'], vals=f['vals'], picks=f['picks'], chunk=fn[7:11]))
    out = os.path.join(ROOT, 'results', 'k4_rf_offexport')
    json.dump({'cores': cores}, gzip.open(os.path.join(out, 'n5_failure_capable_cores.json.gz'), 'wt'))
    with gzip.open(os.path.join(out, 'n5_stored_fails_seeds.jsonl.gz'), 'wt') as f:
        for s in seeds: f.write(json.dumps(s) + '\n')
    print('failure-capable cores %d (%d of them export hypergraphs), m %s; stored failing starts %d'
          % (len(cores), sum(c['export'] for c in cores), dict(sorted(collections.Counter(c['m'] for c in cores).items())), len(seeds)))
