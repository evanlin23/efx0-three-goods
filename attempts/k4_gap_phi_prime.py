"""Replay of attempts/k4-gap-phi-prime.md: Conjecture Phi' (k4/c4min.md section 4, K4.C4MIN.PHI) fails on two pure
n = 4 profiles. Three implementations re-derive, for each profile, the configurations at the fewest frozen agents,
their valid owners and Phi' = (-t, r, Lambda, -p):
  1. k4/gap.c (-C dump, via k4/gap_bench.dump);
  2. k4/gap_model.py (Python, independent of gap.c);
  3. #41's own k4/c4min_cfg.py + k4/c4min_lib.py (Phi = phi_key(), with -p appended here), read from the tree if
     present, else from branch origin/proof/k4-c4min.
Each must report a unique Phi'-maximum without a valid owner while other configurations have one.
Usage: python3 attempts/k4_gap_phi_prime.py"""
import os, subprocess, sys, tempfile
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import gap_model as gm, gap_bench as gb

CASES = [  # (core file, position, m, sets, values)
    ('k4_certs_4_pure.json.gz', 104, 8, [[0, 2, 5, 7], [1, 4, 6, 7], [2, 3, 4, 6], [3, 5, 6, 7]],
     [[2, 3, 6, 10], [3, 2, 6, 10], [6, 10, 3, 2], [8, 4, 5, 2]]),
    ('k4_certs_4_pure.json.gz', 183, 10, [[0, 2, 5, 8], [1, 4, 7, 9], [3, 5, 6, 9], [6, 7, 8, 9]],
     [[2, 6, 10, 3], [6, 3, 10, 2], [3, 10, 2, 6], [3, 8, 4, 2]]),
]

def c4min41():
    d = os.path.join(ROOT, 'k4')
    if os.path.exists(os.path.join(d, 'c4min_cfg.py')): return d, 'tree'
    t = tempfile.mkdtemp()
    for f in ('c4min_cfg.py', 'c4min_lib.py', 'check4.py'):
        src = subprocess.run(['git', '-C', ROOT, 'show', f'origin/proof/k4-c4min:k4/{f}'], capture_output=True, text=True).stdout
        open(os.path.join(t, f), 'w').write(src)
    return t, 'origin/proof/k4-c4min'

def main():
    ok = True
    path, where = c4min41()
    sys.path.insert(0, path)
    import c4min_cfg as C
    from c4min_lib import Profile as P41
    for fname, pos, m, sets, vals in CASES:
        print(f"== {fname} core {pos}: n = 4, m = {m}, sets {sets}, values {vals}")
        rec = {'core': {'sets': sets, 'm': m, 'file': fname, 'pos': pos, 'idx': pos}, 'vals': vals, 'prof': [0] * 4}
        for _, head, cl in gb.dump([rec]):
            b = max(tuple(d['phi']) for d in cl); mx = [d for d in cl if tuple(d['phi']) == b]
            print(f"  gap.c: f {head['f']}, omega {head['omega']}, {len(cl)} configurations, {sum(1 for d in cl if d['own'])} with a "
                  f"valid owner; Phi' max {b}: {len(mx)} maxima, {sum(1 for d in mx if d['own'])} with a valid owner")
            ok &= len(mx) == 1 and not mx[0]['own'] and any(d['own'] for d in cl)
        pr = gm.Profile(sets, vals, m)
        cf = pr.configs(); b = max(c.phi for c in cf); mx = [c for c in cf if c.phi == b]
        print(f"  gap_model: f {pr.f}, omega {pr.omega}, {len(cf)} configurations, {sum(c.completable for c in cf)} with a valid "
              f"owner; Phi' max {b}: {len(mx)} maxima, {sum(c.completable for c in mx)} with a valid owner: {mx[0]}; "
              f"some min-frozen P removal-only completable: {pr.deficit_ok()}")
        ok &= len(mx) == 1 and not mx[0].completable and any(c.completable for c in cf)
        p41 = P41([dict(zip(S, V)) for S, V in zip(sets, vals)], m)
        f, ks = C.keys(p41)
        cf = [c for NA, phi in ks for c in C.configs(p41, NA, phi)]
        key = lambda c: c.phi_key() + (-sum(len(c.L & c.U[x]) for x in range(p41.n) if c.phi[x] is not None),)
        b = max(key(c) for c in cf); mx = [c for c in cf if key(c) == b]
        print(f"  #41 c4min_cfg ({where}): f {f}, {len(cf)} configurations, {sum(1 for c in cf if c.owners())} with a valid owner; "
              f"Phi' max {b}: {len(mx)} maxima, {sum(1 for c in mx if c.owners())} with a valid owner")
        ok &= len(mx) == 1 and not mx[0].owners() and any(c.owners() for c in cf)
    print("all three implementations: Conjecture Phi' fails on both profiles" if ok else "MISMATCH")
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
