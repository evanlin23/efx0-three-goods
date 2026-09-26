"""DEF-LOCAL_k over #53's gap catalogs (results/k4_gap/*.json.gz on compute/k4-gap, read from k4/suite/.cache/gapbench):
for every catalog profile, k* = the largest distance (number of agents whose base changes) from a min-frozen P with
def(P) > 0 to the nearest min-frozen P' with def(P') < def(P). Prints the histogram of k* and the profiles with k* > K.
usage: python3 k4/suite/deficit_sweep.py CATALOG [--every=E] [--max=N] [--show=K] [--jobs=J]"""
import gzip, json, os, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import deficit_local as DL


def one(rec):
    d = {'sets': rec['core']['sets'], 'vals': rec['vals'], 'm': rec['core']['m']}
    k, det = DL.kstar(d)
    return k, d, det


def main(argv):
    cat = argv[0]; every = 1; mx = None; show = 2; jobs = 4
    for a in argv[1:]:
        if a.startswith('--every='): every = int(a[8:])
        elif a.startswith('--max='): mx = int(a[6:])
        elif a.startswith('--show='): show = int(a[7:])
        elif a.startswith('--jobs='): jobs = int(a[7:])
    recs = json.load(gzip.open(cat, 'rt'))['records'][::every]
    if mx: recs = recs[:mx]
    print('# command: python3 k4/suite/deficit_sweep.py ' + ' '.join(argv), flush=True)
    hist = {}; bad = []
    with Pool(jobs) as p:
        for k, d, det in p.imap_unordered(one, recs, chunksize=8):
            hist[k] = hist.get(k, 0) + 1
            if k is not None and k > show: bad.append((k, d, det))
    print('profiles', len(recs), 'k* histogram', dict(sorted(hist.items(), key=lambda x: (x[0] is None, x[0] or 0))))
    for k, d, det in sorted(bad, key=lambda x: (len(x[1]['sets']), x[1]['m']))[:10]:
        print('  k*=%d n=%d m=%d sets=%s vals=%s %s' % (k, len(d['sets']), d['m'], d['sets'], d['vals'], det))


if __name__ == '__main__':
    main(sys.argv[1:])
