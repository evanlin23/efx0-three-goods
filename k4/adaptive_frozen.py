"""Does rule F's first agent give the pre-allocation with the fewest frozen agents? (k4/adaptive.md §4, the bridge to
PR #41's Theorem Z: C4min holds when some valid pre-allocation of k4/c4x.md's space P has no frozen agent;
attempts/k4-adaptive-fewest-frozen.md.)
  1. k4/adaptive.c -A28 (the first agent whose run leaves the fewest frozen agents after need-shrinking upgrades, then
     index order) and -A29 (rule F restricted to those first agents) on every strict profile of the given files;
  2. on every leaf where -A29 needs two rotations (its representative profile, weight w): the fewest frozen agents
     over P (k4/c4x.c -1s, PR #36) and, in PR #33's independent LB4r model (k4/c4_verify_H/lb4r.py), the fewest frozen
     agents over every run of Phase 1 (every insertion sequence) and every upgrade policy.
Usage: adaptive_frozen.py FILE [FILE ...] [--jobs=J]"""
import collections, itertools, json, os, re, subprocess, sys, tempfile, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.environ.get('C4VERIFY_DIR') or os.path.join(HERE, 'c4_verify_H'))
import adaptive_run as A
from lb4r import Inst, phase1_state, up_run, all_needs, NA_of, frozen_at

C4X_SRC = os.path.join(HERE, 'c4x.c')
C4X = os.path.join(tempfile.gettempdir(), 'k4_c4x_' + hashlib.sha256(open(C4X_SRC, 'rb').read()).hexdigest()[:16])

def dense(sets, vals):
    m = 1 + max(g for S in sets for g in S)
    v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    return v

def fewest_frozen_phase1(sets, vals):
    inst = Inst(dense(sets, vals)); n = len(sets); best = n
    for tau in itertools.product(range(n), repeat=n):
        s0, _ = phase1_state(inst, list(tau))
        for pol in ('shrink', 'envyFree', 'none'):
            s1, _ = up_run(inst, s0, pol)
            best = min(best, sum(frozen_at(inst, s1, NA_of(all_needs(inst, s1)))))
    return best

def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('--')]
    jobs = [a for a in args if a.startswith('--jobs=')]
    A.build()
    if not os.path.exists(C4X): subprocess.run(['gcc', '-O2', '-o', C4X, C4X_SRC], check=True)
    print('# adaptive_frozen.py', ' '.join(args), '# adaptive.c sha256', A.SHA, '# c4x.c', os.path.basename(C4X), flush=True)
    for r in ('-A28', '-A29'):
        p = subprocess.run([sys.executable, os.path.join(HERE, 'adaptive_run.py')] + files + [r, '-r3', '--show=0'] + jobs,
                           capture_output=True, text=True)
        print(p.stdout.strip(), flush=True)
    for f in files:
        p = subprocess.run([sys.executable, os.path.join(HERE, 'adaptive_run.py'), f, '-A29', '-r3', '-K2', '-f100000',
                            '--show=100000000'] + jobs, capture_output=True, text=True)
        st = collections.Counter(); ex = None
        for l in p.stdout.split('\n'):
            if not l.startswith('DEEP'): continue
            w = int(re.search(r' w=(\d+)', l).group(1))
            sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', l).group(1)); vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', l).group(1))
            out = subprocess.run([C4X, '-1s'], input=A.encode_profile(sets, vals), capture_output=True, text=True).stdout
            mP = int(out.split('minfrozen ')[1].split()[0])
            mR = fewest_frozen_phase1(sets, vals)
            st[(mP, mR)] += w; st[('leaves', mP, mR)] += 1
            if ex is None: ex = (sets, vals, mP, mR)
        print(f"{os.path.basename(f)}: leaves where -A29 needs two rotations, by (fewest frozen over P, fewest frozen over "
              f"every Phase 1 run and policy):", flush=True)
        for k in sorted(k for k in st if k[0] != 'leaves'):
            print(f"  P: {k[0]}, Phase 1 runs: {k[1]}: {st[('leaves',) + k]} leaves, weight {st[k]}")
        if ex: print(f"  first: sets={ex[0]} vals={ex[1]} fewest frozen over P {ex[2]}, over Phase 1 runs {ex[3]}", flush=True)

if __name__ == '__main__':
    main()
