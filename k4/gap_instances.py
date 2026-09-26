"""Builds the versioned instance suite of the exposed-frozen gap (compute/k4-gap; k4/gap.md section 5).

  python3 k4/gap_instances.py [--out=results/k4_gap/instances_v1.json]

The file is written once per version and never edited: a new version gets a new name (instances_v2.json, ...).
Each instance has an id, n, m, the goods of each agent (sets) and its values (vals, in the order of the goods), tags
(the categories and statements it is an instance of), its provenance, and optionally a highlighted configuration
(key: the frozen good of each agent or null; Q: the pair of each free agent). Sources:
  - #52's instance files k4/hall_instances/*.inst (on main);
  - the named counterexamples of this workstream (attempts/k4-gap-phi-prime.md, attempts/k4-gap-btcyc.md,
    results/k4_gap_bt5.log, the SAME_N configuration of k4/gap.md section 3);
  - the smallest instances of every category of k4/gap_hard.py in the final catalogs (results/k4_gap/hard_base.json.gz,
    results/k4_gap/hard_hunt_smallest.json.gz), two per category and n.
Use it with k4/gap_bench.py: gb.check_instances(pred, scope) or python3 k4/gap_bench.py --instances."""
import glob, gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')

def parse_inst(path):
    agents, bases, comment = [], None, ''
    for line in open(path):
        line = line.strip()
        if line.startswith('#'): comment += line[1:].strip() + ' '
        elif line.startswith('agent'):
            agents.append({int(g): int(v) for g, v in (t.split(':') for t in line.split()[1:])})
        elif line.startswith('bases'):
            bases = [[int(g) for g in part.split(',') if g.strip()] for part in line[5:].split('|')]
    sets = [list(a) for a in agents]
    vals = [[a[g] for g in S] for a, S in zip(agents, sets)]
    return sets, vals, bases, comment.strip()

NAMED = [
    dict(id='phi-n4-m8', tags=['PHI', 'N', 'PHI_PRIME fails'], m=8,
         sets=[[0, 2, 5, 7], [1, 4, 6, 7], [2, 3, 4, 6], [3, 5, 6, 7]], vals=[[2, 3, 6, 10], [3, 2, 6, 10], [6, 10, 3, 2], [8, 4, 5, 2]],
         config=dict(key=[7, None, None, 3], Q={'1': [1, 6], '2': [2, 4]}),
         provenance='pure core 104 (0-based position) of results/k4_certs_4_pure.json.gz; hunt results/k4_gap_hunt_n4_pure_s400k.log; '
                    'attempts/k4-gap-phi-prime.md (the unique Phi\'-maximum has no valid owner; gap.c, gap_model, #41 c4min_cfg.py)'),
    dict(id='phi-n4-m10', tags=['PHI', 'N', 'PHI_PRIME fails'], m=10,
         sets=[[0, 2, 5, 8], [1, 4, 7, 9], [3, 5, 6, 9], [6, 7, 8, 9]], vals=[[2, 6, 10, 3], [6, 3, 10, 2], [3, 10, 2, 6], [3, 8, 4, 2]],
         config=dict(key=[5, 7, None, None], Q={'2': [3, 9], '3': [6, 8]}),
         provenance='pure core 183 of results/k4_certs_4_pure.json.gz; same hunt; attempts/k4-gap-phi-prime.md'),
    dict(id='btcyc-n4-m8', tags=['BTCYC fails', 'REACH_EACH_CYC fails'], m=8,
         sets=[[0, 2, 5, 6], [0, 3, 4, 6], [1, 2, 4, 7], [1, 3, 5, 7]], vals=[[3, 10, 2, 6], [2, 10, 3, 6], [2, 10, 3, 6], [2, 8, 3, 4]],
         config=dict(key=[2, 3, None, None], Q={'2': [4, 7], '3': [1, 5]}),
         provenance='pure n = 4 hunt (results/k4_gap/hard_hunt.json.gz, category W); attempts/k4-gap-btcyc.md; results/k4_gap_btcyc.log'),
    dict(id='bt-n5-m10', tags=['BT fails'], m=10,
         sets=[[0, 2, 4, 8], [1, 3, 7, 9], [4, 6, 9], [5, 6, 7, 9], [5, 8, 9]], vals=[[2, 4, 5, 8], [3, 2, 6, 10], [2, 3, 4], [8, 6, 4, 3], [4, 3, 2]],
         config=dict(key=[None, None, 9, 5, None], Q={'0': [2, 4], '1': [1, 7], '4': [3, 8]}),
         provenance='n = 5 catalog with three 4-good agents (results/k4_gap/gap_n5_3_s100.json.gz), bench results/k4_gap_bench_n5.log; results/k4_gap_bt5.log'),
    dict(id='samen-n4-m8', tags=['SAME_N fails', 'LOCAL_ALL fails'], m=8,
         sets=[[0, 2, 4, 5], [1, 3, 6, 7], [4, 5, 6, 7], [5, 6, 7]], vals=[[6, 3, 2, 10], [2, 3, 6, 10], [4, 6, 3, 8], [2, 4, 3]],
         config=dict(key=[5, 7, None, None], Q={'2': [0, 4], '3': [1, 6]}),
         provenance='n = 4 catalogs (every 5th record), bench results/k4_gap_bench_n4.log (LOCAL_ALL, SAME_N); k4/gap.md section 3'),
]

def main():
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    out = opt.get('out', os.path.join(ROOT, 'results', 'k4_gap', 'instances_v1.json'))
    inst = []
    for p in sorted(glob.glob(os.path.join(ROOT, 'k4', 'hall_instances', '*.inst'))):
        sets, vals, bases, comment = parse_inst(p)
        name = os.path.basename(p)[:-5]
        tags = {'bt4': ['BT fails', 'REACH_EACH_CYC fails'], 'local3': ['#46 local exposures'], 'cyc6': ['#46 label collision (f = 0)']}.get(name, [])
        inst.append(dict(id=f'hall-{name}', tags=tags, n=len(sets), m=1 + max(g for S in sets for g in S), sets=sets, vals=vals,
                         bases=bases, provenance=f'k4/hall_instances/{name}.inst (#46/#52): {comment}'))
    for d in NAMED:
        d = dict(d); d['n'] = len(d['sets']); inst.append(d)
    for f in ('hard_base.json.gz', 'hard_hunt_smallest.json.gz'):
        path = os.path.join(ROOT, 'results', 'k4_gap', f)
        for cat, recs in json.load(gzip.open(path, 'rt')).items():
            for r in recs:
                c = r['core']
                iid = f"{cat.lower()}-n{len(c['sets'])}-m{c['m']}-{c['file'].replace('.json.gz', '')}-{c['pos']}-{'-'.join(map(str, r['prof']))}"
                same = [x for x in inst if x['sets'] == c['sets'] and x['vals'] == r['vals']]
                if same:                                    # the same profile: merge the tags and the provenance
                    if cat not in same[0]['tags']: same[0]['tags'].append(cat)
                    continue
                ex = r.get('ex') or {}
                inst.append(dict(id=iid, tags=[cat], n=len(c['sets']), m=c['m'], sets=c['sets'], vals=r['vals'],
                                 config=dict(key=[None if g < 0 else g for g in ex['key']],
                                             Q={str(y): q for y, q in enumerate(ex['Q']) if q is not None}) if ex else None,
                                 provenance=f"category {cat} of k4/gap_hard.py, results/k4_gap/{f}: core {c['file']} position {c['pos']} "
                                            f"(idx {c['idx']}), profile (type indices) {r['prof']}; f = {r['f']}, omega = {r['omega']}"))
    json.dump({'version': 1, 'description': 'instance suite of the exposed-frozen gap of C4min (k4/gap.md section 5); '
               'built by python3 k4/gap_instances.py; never edited (a new version gets a new file)', 'instances': inst},
              open(out, 'w'), indent=1)
    print(f"wrote {len(inst)} instances to {out}")

if __name__ == '__main__':
    main()
