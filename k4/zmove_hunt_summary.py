#!/usr/bin/env python3
"""Table of the Phase 3 hunts of workstream compute/k4-zmove from their checkpoints (OUT.state.json of k4/zmove_hunt.py
and k4/zmove_corehunt.py): per hunt the seed (from the log), minutes run, steps, profiles screened and evaluated (with a
key of def* > 0), distinct cores (core hunts), profiles recorded, ZMOVE failures, the best score and the best margin
seen. EVIDENCE tooling.
usage: python3 k4/zmove_hunt_summary.py [DIR]          (default results/k4_zmove/hunt)"""
import glob, json, os, sys


def main(argv):
    d = argv[0] if argv else 'results/k4_zmove/hunt'
    rows = []; tot = {'evals': 0, 'cores': 0, 'fails': 0, 'minutes': 0.0}
    for st in sorted(glob.glob(os.path.join(d, '*.state.json'))):
        name = os.path.basename(st)[:-len('.jsonl.gz.state.json')]
        s = json.load(open(st)); S = s['stats']
        log = st[:-len('.jsonl.gz.state.json')] + '.log'
        seed = kind = ''
        if os.path.exists(log):
            for line in open(log):
                if line.startswith('# command'):
                    kind = 'core' if 'corehunt' in line else 'profile'
                    seed = next((a.split('=', 1)[1] for a in line.split() if a.startswith('--seedfile=')), 'inline')
                    seed = os.path.basename(seed)
                if line.startswith('# seed:'): seed += ' (' + line[8:].strip() + ')'
        nc = len(S.get('cores', [])) if kind == 'core' else '-'
        rows.append((name, kind, seed, S['elapsed'] / 60, S['steps'], S['screened'], S['evals'], nc, S['recorded'],
                     S['fails'], s['best_s'], S['best_margin']))
        tot['evals'] += S['evals']; tot['fails'] += S['fails']; tot['minutes'] += S['elapsed'] / 60
        if kind == 'core': tot['cores'] += nc
    print('| hunt | kind | seed (start) | minutes | steps | screened | evaluated | cores | recorded | failures | best score | best margin |')
    print('|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for r in rows:
        print('| %s | %s | %s | %.0f | %d | %d | %d | %s | %d | %d | %s | %s |' % r)
    print('\ntotal: %d hunts, %.0f minutes, %d profiles evaluated (core hunts: %d cores), %d ZMOVE failures' % (
        len(rows), tot['minutes'], tot['evals'], tot['cores'], tot['fails']))


if __name__ == '__main__':
    main(sys.argv[1:])
