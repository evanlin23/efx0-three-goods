"""Assemble a certificate from mincex_cert.py's checkpoint (latest record per core, in the order of the shapes file),
without the type domains (the checkers recompute them). Usage: mincex_ckpt.py shapes.json.gz checkpoint.jsonl out.json.gz"""
import sys, json, gzip
shapes, ck, out = sys.argv[1:4]
done = {}
for line in open(ck):
    r = json.loads(line); done[json.dumps([r['n'], r['m'], r['sets']])] = r
res = []
for s in json.load(gzip.open(shapes, 'rt')):
    r = dict(done.get(json.dumps([s['n'], s['m'], s['sets']]), s))
    r.pop('domains', None)
    res.append(r)
with gzip.open(out, 'wt') as f: json.dump(res, f, separators=(',', ':'))
print('%d cores, %d certified, %d not' % (len(res), sum('allocs' in r for r in res), sum('allocs' not in r for r in res)))
