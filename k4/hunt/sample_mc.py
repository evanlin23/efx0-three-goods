"""Sample minimal-counterexample candidates per (beta, m) group from mc_n.py's files, for a hunting run.
Usage: sample_mc.py OUT.json.gz FILE [FILE ...] [--per=K] [--mmin=M] [--seed=S]"""
import sys, json, gzip, random, collections
files = [a for a in sys.argv[2:] if not a.startswith('--')]
opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
rng = random.Random(int(opt.get('seed', 1)))
groups = collections.defaultdict(list)
for f in files:
    for r in json.load(gzip.open(f, 'rt')):
        if r['m'] >= int(opt.get('mmin', 0)): groups[(r['beta'], r['m'])].append(r)
out = []
for key in sorted(groups):
    g = groups[key]
    out += rng.sample(g, min(int(opt.get('per', 100)), len(g)))
    print(key, len(g), '->', min(int(opt.get('per', 100)), len(g)))
json.dump(out, gzip.open(sys.argv[1], 'wt'))
print(len(out), 'sampled')
