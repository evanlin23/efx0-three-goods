"""TARGET4 with one 4-good agent q (k4/one4.md): list the uncovered runs to which none of the proved key-decreasing
moves of k4/c4one.md §6 (Lemma Omega with any x, its variant Omega_q, Lemma Psi / Psi_q) applies -- the residual cases
that a proof of Exchange Lemma X (or X*) still has to handle.  Same driver as k4/c4tools/c4omega1.py --any (k4/c4check.c
-X -Y -P2 -u2 -i20 -Z3 -K<class>, every insertion sequence, LB's P-step key; --general for P-steps in any order).
Prints each residual KCASE line (class, sets, profile, run) and a tally.
    python3 k4/one4_residual.py FILE [--general] [--max=N]"""
import os, sys, re, json, gzip, subprocess, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, 'c4tools')); sys.path.insert(0, HERE)
import c4omega1 as O
import lb4_run, c4check_run

GENERAL = ['-G'] if '--general' in sys.argv else []
MAX = int(next((a.split('=')[1] for a in sys.argv if a.startswith('--max=')), 20))


def residual(c):
    out = []; seen = set()
    for K in (1, 2, 3, 4, 5):
        p = subprocess.run([O.BIN, '-X', '-Y', '-P2', '-u2', '-i20', '-o0', '-r1', '-w0', '-c0', '-f3', '-Z3', '-K%d' % K,
                            '-KL100000'] + GENERAL, input=lb4_run.encode(c['sets'], c['m'], False), capture_output=True, text=True)
        for l in p.stderr.split('\n'):
            if not l.startswith('KCASE'): continue
            key = (K, l.split(' upg=')[0])
            if key in seen: continue
            seen.add(key)
            n = len(json.loads(re.search(r'sets=(\S+)', l).group(1)))
            if any(O.check(l, x).startswith('hypotheses') for x in range(n)): continue
            if any(O.check_psi(l, x).startswith('Psi hypotheses hold') for x in range(n)): continue
            out.append((O.CLS[K], l))
    return out


if __name__ == '__main__':
    c4check_run.build()
    print('$ python3 k4/one4_residual.py', *sys.argv[1:], flush=True)
    fn = sys.argv[1]
    cs = [c for c in json.load(gzip.open(fn, 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
    tally = collections.Counter(); shown = 0
    for c in cs:
        for cls, l in residual(c):
            tally[cls] += 1
            if shown < MAX: print('[%s] %s' % (cls, l[:600])); shown += 1
    print('residual cases by class:', dict(tally), 'total', sum(tally.values()))
