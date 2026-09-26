"""Self-tests of the k4/induct.md tools; writes the numbers k4/induct.md §1 and §4 quote.

  (a) SAT (k4/induct_sat.py) vs brute force (k4/induct_bf.py): EFX0 existence and PS, with and without D2, on random
      instances (n = 2..4, m = 3..7, values 0..6 with zeros);
  (b) k4/induct.c's early-exit PS search (task Q) vs its full enumeration (task P), on random instances;
  (c) k4/induct.c built with -fsanitize=address,undefined and run on every task type over random certified cores.
Usage: python3 k4/induct_selftest.py [--log=OUT]
"""
import gzip, json, os, random, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from induct_sat import exists, ps
from induct_bf import all_efx0, enviers
from induct_run import build, BIN, domain, values


def main():
    logp = next((a.split('=', 1)[1] for a in sys.argv[1:] if a.startswith('--log=')), None)
    logf = open(logp, 'w') if logp else None
    def log(s):
        print(s, flush=True)
        if logf: logf.write(s + '\n'); logf.flush()
    log('command: python3 k4/induct_selftest.py ' + ' '.join(sys.argv[1:]))
    # (a)
    rng = random.Random(3); cnt = bad = 0
    for _ in range(400):
        n = rng.randint(2, 4); m = rng.randint(3, 7)
        V = [[(0 if rng.random() < 0.4 else rng.randint(1, 6)) for g in range(m)] for i in range(n)]
        A = list(range(n)); G = list(range(m))
        E = all_efx0(V, G, A)
        for d2 in (False, True):
            Ed = [Y for Y in E if (not d2) or sum(1 for a in A if sum(1 for g in G if Y[g] == a) > 2) <= 1]
            cnt += 1; bad += (exists(V, A, G, d2) is not None) != bool(Ed)
            for w in A:
                cnt += 1
                bad += (ps(V, A, G, w, d2) is not None) != any(not enviers(V, Y, w, A) for Y in Ed)
    log(f'(a) SAT vs brute force (existence and PS, with and without D2): {cnt} checks, {bad} mismatches')
    # (b)
    build()
    rng = random.Random(9); inp = []
    for _ in range(300):
        n = rng.randint(2, 4); m = rng.randint(3, 8)
        V = [[(0 if rng.random() < 0.4 else rng.randint(1, 6)) for g in range(m)] for i in range(n)]
        inp.append(f'{n} {m}'); inp += [' '.join(map(str, r)) for r in V]
        inp.append(str(2 * n)); inp += [f'P {w}' for w in range(n)] + [f'Q {w} -1' for w in range(n)]
    out = subprocess.run([BIN], input='\n'.join(inp) + '\n', capture_output=True, text=True, check=True).stdout.split('\n')
    P = [l for l in out if l.startswith('TASK P')]; Q = [l for l in out if l.startswith('TASK Q')]
    mism = 0
    for a, b in zip(P, Q):
        f = a.split('|'); nE = int(f[1].split()[1]); me = int(f[2].split()[1]); md = int(f[2].split()[3])
        g = b.split('|')[1].split()
        mism += ((nE > 0 and me == 0), (nE > 0 and md == 0)) != (bool(int(g[1])), bool(int(g[3])))
    log(f'(b) task Q vs task P (PS and PS in D2): {len(P)} pairs, {mism} mismatches')
    # (c)
    san = os.path.join(tempfile.gettempdir(), 'k4_induct_san')
    subprocess.run(['gcc', '-O1', '-g', '-fsanitize=address,undefined', '-fno-sanitize-recover=all', '-o', san,
                    os.path.join(HERE, 'induct.c'), '-lm'], check=True)
    rng = random.Random(5); inp = []; cnt = 0
    for fn in ('k4_certs_2.json.gz', 'k4_certs_3.json.gz', 'k4_certs_4_n4_2.json.gz', 'k4_certs_4_pure.json.gz'):
        cores = json.load(gzip.open(os.path.join(HERE, '..', 'results', fn)))['cores']
        for c in rng.sample(cores, min(25, len(cores))):
            sets, m = c['sets'], c['m']
            deg = [sum(g in S for S in sets) for g in range(m)]
            V = values(sets, m, tuple(rng.choice(domain(S, deg)) for S in sets))
            T = []
            for w, S in enumerate(sets):
                if len(S) == 4:
                    for d in S:
                        T += [f'G {w} {d}', f'B {w} {d}', f'V {w} {d}', f'H {w} {d} {rng.randrange(len(sets))}', f'Q {w} {d}']
                    T.append(f'A {w}')
                T += [f'P {w}', f'Q {w} -1']
            inp.append(f'{len(sets)} {m}'); inp += [' '.join(map(str, r)) for r in V]; inp.append(str(len(T))); inp += T
            cnt += len(T)
    r = subprocess.run([san, '-r', '2'], input='\n'.join(inp) + '\n', capture_output=True, text=True)
    log(f'(c) sanitizers (address, undefined): {cnt} tasks, {r.stdout.count("TASK")} outputs, exit {r.returncode}, '
        f'stderr {"empty" if not r.stderr.strip() else r.stderr[:500]}')


if __name__ == '__main__':
    main()
