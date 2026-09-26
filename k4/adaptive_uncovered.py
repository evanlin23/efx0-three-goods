"""How LB4r succeeds on the profiles that no insertion sequence's covered run reaches (k4/adaptive.md §6):
k4/adaptive.c -A23 (rule F, recording whether some insertion sequence has a run covered by the theorems of #33 and
#37) on every strict profile of every core of the given files; sums, per (covered or not, upgrade policy, rotations,
how the owner step ended), the number of profiles. Other C options replace the default '-A23 -r3', e.g.
'-A26 -C3 -r0 -w0': the fewest rotations over every insertion sequence (-i2), with the coverage by the theorems and
Theorem A4+N recorded, the owner's needs from its base, no rotation. Profiles on which LB4r fails with the options
are listed as 'fails' (the difference between the class total and its successes).
Usage: adaptive_uncovered.py FILE [FILE ...] [--jobs=J] [C options]"""
import collections, gzip, json, os, subprocess, sys
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as A

OPTS = ['-A23', '-r3']

def run(c):
    p = subprocess.run([A.BIN] + OPTS, input=A.encode_core(c['sets'], c['m']), capture_output=True, text=True)
    out = collections.Counter()
    for l in p.stdout.split('\n'):
        if l.startswith('U '):
            a, b, r, e, w = map(int, l.split()[1:]); out[(a, b, r, e)] += w
        elif l.startswith('total '):
            d = A.parse(l); out['total'] += d['total']; out['uncov'] += d['uncov']
    return out

def init(opts):
    global OPTS
    OPTS = opts

def main():
    args = sys.argv[1:]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')] or OPTS
    A.build()
    print('# adaptive_uncovered.py', ' '.join(args), '# adaptive.c sha256', A.SHA, flush=True)
    names = ['need-shrinking', 'envy-free', 'no upgrades']; st = ['no owner needed', 'owner r', 'other owner', 'rotation']
    for f in [a for a in args if not a.startswith('-')]:
        tot = collections.Counter()
        with Pool(jobs, initializer=init, initargs=(opts,)) as pool:
            for o in pool.imap_unordered(run, json.load(gzip.open(f, 'rt'))['cores']): tot.update(o)
        print(f)
        keys = sorted(k for k in tot if isinstance(k, tuple))
        for k in keys:
            print(f"  {'no covered sequence' if k[0] else 'covered':20s} policy={names[k[1]]:14s} rotations={k[2]} {st[k[3]]:16s} {tot[k]}")
        for u, lab in ((0, 'covered'), (1, 'no covered sequence')):
            cls = tot['uncov'] if u else tot['total'] - tot['uncov']
            ok = sum(tot[k] for k in keys if k[0] == u)
            if cls - ok: print(f"  {lab:20s} fails {cls - ok}")
        print(f"  total {tot['total']} no covered sequence {tot['uncov']}", flush=True)

if __name__ == '__main__':
    main()
