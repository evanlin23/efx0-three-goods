#!/usr/bin/env python3
"""The profiles of the T1-stuck states of k4/dl13.md §1 (results/k4_dl13_stuck/stuck_*.jsonl.gz, PR #75), deduplicated,
as one instance list for k4/sx_keygraph.py inst, k4/sx_zprime.py and k4/sx_f2.py (workstream proof/k4-sx).
Every T3-stage state of k4/dl13.md §2.3 is T1-stuck, so its profile is among these.
usage: python3 k4/sx_t3stage.py      (writes results/k4_sx/t3stage/profiles.json.gz and profiles_f1.jsonl.gz)"""
import collections, glob, gzip, json, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    seen = {}; cnt = collections.Counter()
    for fn in sorted(glob.glob(os.path.join(ROOT, 'results/k4_dl13_stuck/stuck_*.jsonl.gz'))):
        for line in gzip.open(fn, 'rt'):
            r = json.loads(line)
            cnt['T1-stuck records'] += 1
            key = json.dumps([r['sets'], r['vals'], r['m']])
            if key not in seen:
                seen[key] = {'id': r['src'], 'sets': r['sets'], 'vals': r['vals'], 'm': r['m'], 'f': r['f']}
    out = os.path.join(ROOT, 'results/k4_sx/t3stage')
    os.makedirs(out, exist_ok=True)
    json.dump(list(seen.values()), gzip.open(os.path.join(out, 'profiles.json.gz'), 'wt'))
    with gzip.open(os.path.join(out, 'profiles_f1.jsonl.gz'), 'wt') as fo:     # the format of k4/sx_zprime.py's input
        for d in seen.values():
            if d['f'] == 1:
                fo.write(json.dumps({'src': d['id'], 'sets': d['sets'], 'vals': d['vals'], 'm': d['m'], 'f': 1}) + '\n')
    by = collections.Counter((len(d['sets']), d['f']) for d in seen.values())
    print(dict(cnt), 'distinct profiles', len(seen), 'by (n, f):', sorted(by.items()))


if __name__ == '__main__':
    main()
