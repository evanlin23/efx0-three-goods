#!/usr/bin/env python3
"""Count the non-completable f = 1 keys of PR #80's hunt dumps and their Z′-maxima by (x big-top, number of
terminals) (workstream proof/k4-zmove-f1; EVIDENCE tooling, k4/zf1_lib.py).

usage: python3 k4/zf1_count.py DUMP.jsonl.gz ..."""
import collections, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zf1_lib import Prof, load, f1_keys, zmax, noncompletable

cnt = collections.Counter()
t0 = time.time()
print('# command: python3 k4/zf1_count.py ' + ' '.join(sys.argv[1:]))
for path in sys.argv[1:]:
    for rec in load(path):
        pr = Prof(rec['sets'], rec['vals'], rec['m'])
        for K in f1_keys(pr):
            allc, mx = zmax(K)
            if not noncompletable(allc): continue
            cnt['non-completable keys, n = %d' % pr.n] += 1
            bt = pr.bigtop_on(K.x, K.g)
            if bt: cnt['non-completable keys with x big-top, n = %d' % pr.n] += 1
            for c in mx:
                cnt['Z′-maxima, n = %d, x %s, %s terminal(s)' % (pr.n, 'big-top' if bt else 'not big-top',
                                                                  min(len(c.term), 3))] += 1
for k in sorted(cnt): print('  %-60s %d' % (k, cnt[k]))
print('done; time %.0f s' % (time.time() - t0))
