"""How LB4r with rule F succeeds on the profiles that no insertion sequence's covered run reaches (k4/adaptive.md §6):
k4/adaptive.c -A23 (rule F, recording whether some insertion sequence has a run covered by the theorems of #33 and
#37) on every strict profile of every core of the given files; sums, per (covered or not, upgrade policy, rotations,
how the owner step ended), the number of profiles.  Usage: adaptive_uncovered.py FILE [FILE ...] [--jobs=J]"""
import collections, gzip, json, os, subprocess, sys
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as A

def run(c):
    p = subprocess.run([A.BIN, '-A23', '-r3'], input=A.encode_core(c['sets'], c['m']), capture_output=True, text=True)
    out = collections.Counter()
    for l in p.stdout.split('\n'):
        if l.startswith('U '):
            a, b, r, e, w = map(int, l.split()[1:]); out[(a, b, r, e)] += w
    return out

def main():
    args = sys.argv[1:]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    A.build()
    print('# adaptive_uncovered.py', ' '.join(args), '# adaptive.c sha256', A.SHA, flush=True)
    names = ['need-shrinking', 'envy-free', 'no upgrades']; st = ['no owner needed', 'owner r', 'other owner', 'rotation']
    for f in [a for a in args if not a.startswith('--')]:
        tot = collections.Counter()
        with Pool(jobs) as pool:
            for o in pool.imap_unordered(run, json.load(gzip.open(f, 'rt'))['cores']): tot.update(o)
        print(f)
        for k, v in sorted(tot.items()):
            print(f"  {'no covered sequence' if k[0] else 'covered':20s} policy={names[k[1]]:14s} rotations={k[2]} {st[k[3]]:16s} {v}")

if __name__ == '__main__':
    main()
