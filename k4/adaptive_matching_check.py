"""Check of k4/adaptive.c's choice_matching (rules 17, 18, 25; k4/adaptive.md §5) against brute force: on random
instances (n = 2..6, m = 4..9, agents with 3 or 4 goods), the matching of agents to their first or second choice must
have the largest size and, among those, the most first choices. Usage: python3 k4/adaptive_matching_check.py"""
import itertools, os, random, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); import adaptive_run as A; A.build()
print('# adaptive_matching_check.py', ' '.join(sys.argv[1:]), '# adaptive.c sha256', A.SHA, flush=True)
rng = random.Random(5); bad = 0
for trial in range(300):
    n = rng.randint(2, 6); m = rng.randint(4, 9)
    sets = [sorted(rng.sample(range(m), rng.choice([3, 4]))) for _ in range(n)]
    vals = [rng.sample(range(1, 20), len(S)) for S in sets]
    used = set(g for S in sets for g in S)
    if len(used) < m: continue
    out = subprocess.run([A.BIN, '-A17', '-r0', '-T1', '-vv'], input=A.encode_profile(sets, vals), capture_output=True, text=True).stdout
    cls = [int(x) for x in [l for l in out.split('\n') if 'matching classes' in l][0].split(':')[1].split()]
    top = [[g for g, _ in sorted(zip(S, V), key=lambda x: -x[1])][:2] for S, V in zip(sets, vals)]
    best = None
    for choice in itertools.product([0, 1, 2], repeat=n):
        gs = [top[i][c] for i, c in enumerate(choice) if c < 2]
        if len(gs) != len(set(gs)): continue
        key = (sum(c < 2 for c in choice), sum(c == 0 for c in choice))
        if best is None or key > best: best = key
    got = (sum(c < 2 for c in cls), sum(c == 0 for c in cls))
    gs = [top[i][c] for i, c in enumerate(cls) if c < 2]
    if got != best or len(gs) != len(set(gs)): bad += 1; print('MISMATCH', sets, vals, cls, best)
print('checked, mismatches:', bad)
