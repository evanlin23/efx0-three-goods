#!/usr/bin/env python3
"""Tabulate the k4/dlrc_hunt.py checkpoints (compute/k4-rc): per run, the units (climbs), profiles evaluated, def > 0
states with f >= 1 met, distinct profiles with a chain state, the largest least |W| at a chain state, DL_RC and key-form
failures, CPU time, and the best score reached with its unit, core and profile. EVIDENCE bookkeeping.

usage: python3 k4/dlrc_hunt_summary.py results/k4_rc/ckpt_hunt_*.jsonl"""
import collections, json, os, sys


def main(files):
    print('# command: python3 k4/dlrc_hunt_summary.py ' + ' '.join(files))
    tot = collections.Counter()
    print('| run | units | n | profiles evaluated | f >= 1 states met | units reaching a chain state | distinct chain '
          'profiles | largest least \\|W\\| | DL_RC fails | key form fails | CPU s | best score (where) |')
    print('|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---|')
    for fn in files:
        S = [json.loads(l) for l in open(fn) if l.strip()]
        if not S: continue
        name = os.path.basename(fn)[len('ckpt_hunt_'):-len('.jsonl')]
        b = max(S, key=lambda s: s['best_score'])
        ns = sorted(set(s['n'] for s in S))
        row = dict(units=len(S), evals=sum(s['evals'] for s in S), states=sum(s.get('states', 0) for s in S),
                   chainunits=sum(1 for s in S if s['chain_profiles']), chainprof=sum(s['chain_profiles'] for s in S),
                   rcf=sum(s['rcfail_profiles'] for s in S), kf=sum(s['keyfail_profiles'] for s in S),
                   secs=sum(s['secs'] for s in S))
        maxw = max(s['maxw'] for s in S)
        for k, v in row.items(): tot[k] += v
        tot['maxw'] = max(tot['maxw'], maxw)
        print('| %s | %d | %s | %d | %d | %d | %d | %d | %d | %d | %.0f | %s (%s, %s, profile %s) |' % (
            name, row['units'], ','.join(map(str, ns)), row['evals'], row['states'], row['chainunits'], row['chainprof'],
            maxw, row['rcf'], row['kf'], row['secs'], b['best_score'], json.dumps(b['key']), b['label'], b['best_prof']))
    print('| total | %d | | %d | %d | %d | %d | %d | %d | %d | %.0f | |' % (
        tot['units'], tot['evals'], tot['states'], tot['chainunits'], tot['chainprof'], tot['maxw'], tot['rcf'], tot['kf'],
        tot['secs']))


if __name__ == '__main__':
    main(sys.argv[1:])
