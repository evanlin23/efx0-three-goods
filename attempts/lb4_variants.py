"""Reproduce the smallest failures of the rejected LB4 variants (attempts/lb4-*.md).

For each variant: run k4/lb4.c with the variant's options on every strict profile of the given core (lazy type
branching, as k4/lb4_run.py does), report how many profiles fail, and for the first failing profile list, by brute
force over all n^m allocations with explicit integers (k4/lb4_brute.py), the EFX0 allocations with at most one
bundle of more than 2 goods. A nonempty list shows it is the construction that fails, not conjecture K4.D.
Usage: python attempts/lb4_variants.py [NAME ...]      (default: every variant below)"""
import json, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4'))
import lb4_run, lb4_brute

VARIANTS = {
    # name: (options of k4/lb4.c, core as (m, sets), what the variant is)
    'lbplus-shape': ('-i0 -u1 -o2 -r1', (5, [[0, 2, 3, 4], [1, 2, 3, 4]]),
                     'index insertion, N-shrinking upgrades, owner r, else one rotation (any chain, any subset)'),
    'no-rotation': ('-i2 -u3 -r0 -w1', (5, [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]]),
                    'every insertion sequence, every upgrade policy, every owner, owner needs from its bundle; no rotation'),
    'fixed-insertion': ('-i0 -u3 -r3 -w1 -c1', (6, [[0, 2, 4, 5], [1, 3, 5], [2, 3, 4, 5]]),
                        'index insertion; every upgrade policy, every owner, up to 3 rotations (chains may end at '
                        'upgraded agents), owner needs from its bundle'),
    'last-block-leader': ('-i8 -u1 -r1 -w1 -c1', (8, [[0, 2, 7], [1, 2, 3, 7], [1, 4, 5, 6], [3, 4, 5, 6]]),
                          'index insertion; if it fails, every other leader of the last block (LB4 otherwise)'),
    'owner-needs-from-base': ('-i2 -u3 -r1 -w0', (8, [[0, 2, 4, 6], [0, 2, 5, 6], [1, 3, 4, 7], [1, 3, 5, 7]]),
                              'every insertion sequence, every upgrade policy, every owner, one rotation; '
                              'the owner\'s needs from its base (as at k = 3)'),
}

def run_variant(name):
    opts, (m, sets), what = VARIANTS[name]
    lb4_run.build()
    p = subprocess.run([lb4_run.BIN] + opts.split() + ['-f1'], input=lb4_run.encode(sets, m, False),
                       capture_output=True, text=True, check=True)
    kv = dict(zip(p.stdout.split()[0:22:2], map(int, p.stdout.split()[1:22:2])))
    print(f"{name}: {what}\n  options {opts}; core m={m} sets={sets}")
    print(f"  profiles {kv['total']}, failing {kv['fails']}, raw-check failures {kv['rawfails']}")
    fail = [l for l in p.stderr.split('\n') if l.startswith('FAIL')]
    if not fail:
        print('  NO FAILURE (unexpected)'); return False
    vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', fail[0]).group(1))
    print(f"  first failing profile: values {vals}\n  {fail[0]}")
    sols = [X for X in lb4_brute.all_efx0(sets, vals) if sum(len(B) > 2 for B in X) <= 1]
    print(f"  brute force: {len(sols)} EFX0 allocations with at most one bundle of > 2 goods, e.g. {sols[:2]}")
    return kv['fails'] > 0 and kv['rawfails'] == 0 and len(sols) > 0

if __name__ == '__main__':
    names = sys.argv[1:] or list(VARIANTS)
    ok = all([run_variant(nm) for nm in names])
    print('all reproduced' if ok else 'NOT all reproduced')
    sys.exit(0 if ok else 1)
