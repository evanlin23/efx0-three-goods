"""Seed profiles for k4/rulef_hunt.py --seeds (one JSON object {"sets", "vals", "tag"} per line).

  rulef_hunt_seeds.py H OUT        H_1 (k4/adaptive_H.py, n = 5, m = 13) under all 120 orders of its agents, and H_2
                                   (n = 9) under 8 random agent-and-goods relabelings (k4/adaptive_H.py relabel, seed 1)
  rulef_hunt_seeds.py suite OUT    every complete, strict k = 4 core instance of k4/suite/instances with 4 <= n <= 9
  rulef_hunt_seeds.py best OUT K CK..  the best profile of every unit of the checkpoint files CK (k4/rulef_hunt.py
                                   ck/RUN.jsonl) with best_nwork <= K, least nwork first
  rulef_hunt_seeds.py tight OUT F.. the profiles of the dumps F (tight_*.jsonl.gz) with nwork <= 1, one per searched
                                   core (unit or seed tag; the one with the least key, a relabeled one possibly)
The relabeling of agents matters to rule RK (index order after the first agent); of goods it does not (strict types)."""
import glob, gzip, itertools, json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def main():
    what, out = sys.argv[1], sys.argv[2]
    rows = []
    if what == 'H':
        import adaptive_H as AH
        sets, vals, m = AH.build(1)
        for perm in itertools.permutations(range(len(sets))):     # agent i of H_1 becomes agent perm[i]
            S = [None] * len(sets); V = [None] * len(sets)
            for i in range(len(sets)):
                S[perm[i]] = sets[i]; V[perm[i]] = vals[i]
            rows.append({'sets': S, 'vals': V, 'tag': 'H_1 agents->' + ''.join(map(str, perm))})
        sets, vals, m = AH.build(2)
        rng = random.Random(1)
        rows.append({'sets': sets, 'vals': vals, 'tag': 'H_2'})
        for q in range(8):
            S, V, pa = AH.relabel(sets, vals, m, rng)
            rows.append({'sets': S, 'vals': V, 'tag': f'H_2 relabel {q + 1}'})
    elif what == 'suite':
        for f in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
            r = json.load(open(f))
            if 'kind' in r or not r.get('is_core') or not r.get('strict') or not 4 <= r['n'] <= 9: continue
            rows.append({'sets': r['sets'], 'vals': r['vals'], 'tag': 'suite ' + r['id']})
    elif what == 'best':
        K = int(sys.argv[3]); recs = []
        cache = {}
        for f in sys.argv[4:]:
            for line in open(f):
                r = json.loads(line)
                if r['best_nwork'] > K: continue
                if 'file' in r:
                    if r['file'] not in cache:
                        cache[r['file']] = json.load(gzip.open(os.path.join(HERE, '..', 'results', r['file']), 'rt'))['cores']
                    sets = cache[r['file']][r['core']]['sets']
                else:
                    sets = r['sets']
                recs.append((r['best_nwork'], r['best_key'], {'sets': sets, 'vals': r['best_vals'], 'tag': 'best ' + r['unit']}))
        recs.sort(key=lambda z: (z[0], z[1]))
        rows = [z[2] for z in recs]
    elif what == 'tight':
        best = {}
        for f in sys.argv[3:]:
            for line in gzip.open(f, 'rt'):
                o = json.loads(line)
                if o['nwork'] > 1: continue
                k = o.get('tag') or o['unit']        # one seed per searched core (relabeled profiles included)
                key = (o['nwork'], -min(o['def']), o['nK0'])
                if k not in best or key < best[k][0]:
                    best[k] = (key, {'sets': o['sets'], 'vals': o['vals'], 'tag': 'tight ' + (o.get('tag') or o['unit'])})
        rows = [v for _, v in sorted(best.values(), key=lambda z: z[0])]
    with open(out, 'w') as f:
        for r in rows: f.write(json.dumps(r) + '\n')
    print(f'{out}: {len(rows)} seeds')


if __name__ == '__main__':
    main()
