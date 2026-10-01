"""Rule RK (k4/rulef.md §4) on the cores H_t of k4/c4.md §7 and on relabeled copies (built by k4/adaptive_H.py of #44).

For each H_t (and K seeded relabelings): k4/rulef.c -A41 -r1 -T1 (and the options given, e.g. -w0, the owner's needs
from its base for LB4r's final owner search, as #44 does for H_t; a -w0 completion is a -w1 completion): RK's class
(K0, K1, C40, open), its first agent, and the rotations LB4r needed on RK's sequence.
Usage: rulef_H.py T1,T2,... [--perms=K] [--seed=S] [--timeout=SEC] [C options]"""
import os, random, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_H as AH
import adaptive_run as AR
import rulef_run as RR

CLASSES = ['K0', 'K1', 'C40', 'open']


def main():
    args = sys.argv[1:]
    ts = [int(x) for x in args[0].split(',')]
    perms = int(next((a.split('=')[1] for a in args if a.startswith('--perms=')), 0))
    seed = int(next((a.split('=')[1] for a in args if a.startswith('--seed=')), 1))
    tmo = int(next((a.split('=')[1] for a in args if a.startswith('--timeout=')), 3600))
    opts = [a for a in args[1:] if a.startswith('-') and not a.startswith('--')]
    RR.build()
    print('#', 'rulef_H.py', ' '.join(args), '# rulef.c sha256', RR.SHA, flush=True)
    for t in ts:
        sets, vals, m = AH.build(t)
        rng = random.Random(seed * 1000 + t)
        for p in range(perms + 1):
            S, V, pa = (sets, vals, None) if p == 0 else AH.relabel(sets, vals, m, rng)
            t0 = time.time()
            lab = 'H_%d' % t + ('' if p == 0 else f' relabel {p} (l -> agent {pa[0]})')
            try:
                r = subprocess.run([RR.BIN, '-A41', '-r1', '-T1', '-v'] + opts, input=AR.encode_profile(S, V),
                                   capture_output=True, text=True, timeout=tmo)
                out = r.stdout.split('\n')
                rk = next((l for l in out if l.startswith('RK41')), None)
                run = next((l for l in out if l.startswith('RUN')), '')
                single = next((l for l in out if l.startswith('single')), f'exit {r.returncode}')
                cls = '?'
                if rk:
                    t_ = rk.split()
                    for c in range(4):
                        i = t_.index('c%d' % c)
                        if sum(map(int, t_[i + 1:i + 4])): cls = CLASSES[c]
                tau = run.split('tau=')[1].split()[0] if 'tau=' in run else '?'
                print(f"{lab}: class {cls}, first agent {tau.split(',')[0]}; {single} time {time.time() - t0:.1f}s", flush=True)
            except subprocess.TimeoutExpired:
                print(f"{lab}: timeout {tmo}s", flush=True)


if __name__ == '__main__':
    main()
