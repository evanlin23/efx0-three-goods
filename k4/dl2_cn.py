"""The cycle family C_n: k* = n for every n (compute/k4-dl2; k4/dl2_data.md §3). EVIDENCE for the n run here.

  python3 k4/dl2_cn.py N1,N2,... [--py=NMAX]

C_n (n >= 3): goods t_0..t_{n-1}, x_0..x_{n-1}, j (m = 2n + 1); agent i values t_i : 8, x_i : 5, t_{i+1} : 4, j : 2
(indices mod n). It is a connected k = 4 core with strict values (x_i is agent i's only private good; 8 < 5 + 4 + 2;
the 15 subset sums of 8, 5, 4, 2 are distinct). P_n gives agent i the pair {x_i, t_{i+1}} (worth 9, need-free), J = {j}.
For each n, k4/dl2.c computes the min-frozen class, every deficit and k*, and this script checks: f = 0, omega = 1,
def(P_n) = 1, every other min-frozen P differs from P_n in all n bases (nn(P_n) = n), and k* = n. With --py=NMAX it also
runs k4/suite/deficit_local.py (model.py) for n <= NMAX. The cyclic hunt k4/dl2_cycle.py found C_4 (its core 0)."""
import os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'suite'))
import check4
import dl2_run as DR


def build(n):
    t = list(range(n)); x = list(range(n, 2 * n)); j = 2 * n
    sets = [[t[i], x[i], t[(i + 1) % n], j] for i in range(n)]
    vals = [[8, 5, 4, 2] for _ in range(n)]
    return sets, vals, 2 * n + 1


def main():
    ns = [int(a) for a in sys.argv[1].split(',')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    print('# command: python3 k4/dl2_cn.py ' + ' '.join(sys.argv[1:]), flush=True)
    print(f'# dl2.c sha256 {DR.SHA}', flush=True)
    DR.build()
    bad = 0
    for n in ns:
        sets, vals, m = build(n)
        core = check4.is_core(n, m, sets, True)[0]
        t0 = time.time()
        doms = [[dict(zip(S, V))] for S, V in zip(sets, vals)]
        b = DR.run_blocks(DR.block(sets, m, doms, n, 0), ['-w', '-r1'])[0]
        V = b['V'][0]; ks, nmin, npos, mindef = V[n + 1], V[n + 2], V[n + 3], V[n + 4]
        Pn = tuple(sorted({i + n, (i + 1) % n}) for i in range(n))
        maskPn = [sum(1 << g for g in B) for B in Pn]
        Wn = [w for w in b['W'][0] if w[:n] == maskPn]
        D0 = b["D"][0] if b["D"] else {"f": None, "omega": None}
        ok = core and ks == n and len(Wn) == 1 and Wn[0][n] == 1 and Wn[0][n + 2] == n and npos == 1 and D0["f"] == 0 \
            and D0["omega"] == 1
        line = (f'C_{n}: m = {m}, core {core}, f = {D0["f"]}, omega = {D0["omega"]}, {nmin} min-frozen P, '
                f'{npos} with def > 0, least def {mindef}; P_n: def {Wn[0][n] if Wn else "?"}, distance to a smaller deficit '
                f'{Wn[0][n + 1] if Wn else "?"}, nearest other min-frozen P {Wn[0][n + 2] if Wn else "?"}; k* = {ks}')
        if n <= int(opt.get('py', 0)):
            import deficit_local as DL
            kp, det = DL.kstar({'sets': sets, 'vals': vals, 'm': m})
            line += f'; deficit_local.py: k* = {kp} ({det})'
            ok = ok and kp == n
        print(line + f' [{time.time() - t0:.1f} s]  {"OK" if ok else "FAILED"}', flush=True)
        bad += not ok
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
