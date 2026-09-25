"""Smallest failures of the rejected insertion rules of k4/adaptive.md §5 (attempts/k4-adaptive-*.md), reproduced.

For each recorded configuration (a rule, a profile, the insertion sequence the rule chooses):
  1. k4/adaptive.c with the rule: LB4r with at most one rotation fails (-r1), with two it succeeds (-r2); rule 16
     needs at most one rotation on the same profile;
  2. independently, the LB4r model of PR #33 (k4/c4_verify_H/lb4r.py, written from lean/EFX/LB4R.lean; folder in
     C4VERIFY_DIR, default k4/c4_verify_H): on the rule's insertion sequence, under each upgrade policy, no state
     reachable with at most one rotation has an output (no owner or any owner; the owner's needs from its bundle or
     from its base), and some state reachable with two has one;
  3. k4/lb4_brute.py: the profile has EFX0 allocations with at most one bundle of more than two goods (so the rule
     fails, not K4.D).
And for attempts/k4-adaptive-coverage-multi4.md: on the n = 2 profile recorded there, no insertion sequence has a run
covered by the theorems of k4/c4.md and k4/c4one.md (k4/adaptive.c -A22), while LB4r succeeds without rotation.
Usage: python3 attempts/k4_adaptive_attempts.py"""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import adaptive_run as A
sys.path.insert(0, os.environ.get('C4VERIFY_DIR') or os.path.join(ROOT, 'k4', 'c4_verify_H'))
from lb4r import Inst, phase1_state, up_run, reach, any_output

# (rules, sets, vals): the smallest failure (n = 3, m = 6) of each rule, from results/k4_adaptive_smallest.log
CASES = [
    ([0, 1, 2, 4, 5, 6, 8, 10, 11, 13], [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [2, 3, 4, 8], [2, 7, 8, 4]]),
    ([7], [[0, 1, 2, 5], [2, 3, 4, 5], [3, 4, 5]], [[1, 4, 8, 6], [8, 2, 3, 4], [2, 3, 4]]),
    ([9], [[0, 1, 2, 5], [1, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 8, 6], [1, 4, 6, 8], [8, 2, 3, 4]]),
]
COVER = ([[0, 1, 2, 3], [0, 1, 2, 3]], [[2, 4, 5, 8], [2, 4, 5, 8]])

def tool(sets, vals, opts):
    p = subprocess.run([A.BIN] + opts + ['-T1', '-v'], input=A.encode_profile(sets, vals), capture_output=True, text=True)
    run = [l for l in p.stdout.split('\n') if l.startswith('RUN')][0]
    single = [l for l in p.stdout.split('\n') if l.startswith('single')][0]
    tau = [int(x) for x in run.split('tau=')[1].split()[0].split(',') if x]
    order = [int(x) for x in run.split('order=')[1].split('picks=')[0].split()]
    return run.split()[1], tau, order, single

def lean_tau(tau, order):
    """agent ids at the insertion steps -> LB4R.lean's tau (position among the unprocessed agents, index order)"""
    out, done = [], set()
    it = iter(tau)
    nxt = next(it, None)
    for x in order:
        if x == nxt:
            out.append(sorted(set(range(len(order))) - done).index(x)); nxt = next(it, None)
        done.add(x)
    return out

def dense(sets, vals):
    m = 1 + max(g for S in sets for g in S)
    v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    return v

def least_rotations(v, tau, q=2):
    inst = Inst(v); s0, _ = phase1_state(inst, tau); best = None
    for pol in ('shrink', 'envyFree', 'none'):
        s1, _ = up_run(inst, s0, pol)
        for d, lev in enumerate(reach(inst, s1, q)):
            if any(any_output(inst, s, conv) for s in lev for conv in ('bundle', 'base')):
                best = d if best is None else min(best, d); break
    return best

def brute_d2(sets, vals):
    p = subprocess.run([sys.executable, os.path.join(ROOT, 'k4', 'lb4_brute.py'), json.dumps(sets), json.dumps(vals)],
                       capture_output=True, text=True)
    return p.stdout.split('\n')[0]

def main():
    A.build()
    print('# attempts/k4_adaptive_attempts.py # adaptive.c sha256', A.SHA, flush=True)
    allok = True
    for rules, sets, vals in CASES:
        print(f"profile sets={sets} vals={vals}")
        v = dense(sets, vals)
        for r in rules:
            s1 = tool(sets, vals, [f'-A{r}', '-r1'])
            s2 = tool(sets, vals, [f'-A{r}', '-r2'])
            ind = least_rotations(v, lean_tau(s1[1], s1[2]))
            ok = s1[0] == 'fail' and s2[0] == 'rot=2' and ind == 2
            allok &= ok
            print(f"  rule {r}: tau={s1[1]} adaptive.c -r1: {s1[0]}, -r2: {s2[0]}; independent model: least rotations "
                  f"{ind} -> {'OK' if ok else 'MISMATCH'}")
        s16 = tool(sets, vals, ['-A16', '-r2'])
        ind16 = least_rotations(v, lean_tau(s16[1], s16[2]))
        print(f"  rule 16: tau={s16[1]} {s16[0]}; independent model: least rotations {ind16}")
        allok &= s16[0] in ('rot=0', 'rot=1') and ind16 is not None and ind16 <= 1
        print('  brute force:', brute_d2(sets, vals))
    sets, vals = COVER
    p = subprocess.run([A.BIN, '-A22', '-r1', '-u2', '-w0', '-c0', '-T1'], input=A.encode_profile(sets, vals), capture_output=True, text=True)
    unc = 'uncov=1' in p.stdout
    r16 = tool(sets, vals, ['-A16', '-r1'])
    print(f"coverage: sets={sets} vals={vals}: no insertion sequence covered by the theorems: {unc}; rule 16: {r16[0]}")
    allok &= unc and r16[0] == 'rot=0'
    print('ALL AS RECORDED' if allok else 'MISMATCH')

if __name__ == '__main__':
    main()
