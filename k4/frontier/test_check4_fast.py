"""Tests of k4/check4_fast.py's coverage step against k4/check4.py (the plain checker) and against brute force.

A. Random rows: n = 2..7 agents, 1..200 allocations (1..4 words), random row bitsets, some systems with a last agent
   of more than 512 types (so check4_fast falls back from the column trick to the walk). check4_fast.coverage must
   agree with brute force over every profile (numpy) and with check4.py's C loop (plain walk, all types).
B. Certificates of every committed k = 4 class, including the four new ones (n = 5 with three or four 4-good agents,
   pure n = 5, n = 6 with one 4-good agent): random cores, each with its allocations thinned (a random fraction
   kept) or perturbed (one good moved to another agent in one allocation) or intact. check4.covered and
   check4_fast.covered must agree. check4.py's plain walk can take minutes on a covered core with 288-type agents, so
   each check4.covered call runs in a worker with a time limit (--limit, default 30 s); cases over the limit are
   counted as skipped, never as agreeing.
C. A corrupted vectorized safety table (agent 0's row negated) must be caught by check4_fast's plain-loop re-check.
D. Near-threshold corruptions of real certificates, from every class: (hole) delete every allocation covering one
   random profile; (trap) pick an agent i and types u, t with row_u strictly inside row_t, a profile P with i -> u
   that is covered, and delete every allocation covering P while the same profile with i -> t stays covered (a
   reduction that kept t instead of u would miss the hole). Both checkers must say "not covered"; check4.py calls
   over the time limit are skipped, but check4_fast must still say "not covered".
Usage: test_check4_fast.py [random_systems] [trials_per_file] [--limit=S]     exit status 1 on any disagreement"""
import ctypes, gzip, itertools, json, os, random, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.dirname(HERE))
import check4 as PLAIN
import check4_fast as FAST

def brute(rows, sizes, K):
    """rows[i]: array (sizes[i], K) of bools. Every profile has a common allocation?"""
    acc = np.ones((1, K), dtype=bool)
    for i in range(len(sizes)):
        acc = (acc[:, None, :] & rows[i][None, :, :]).reshape(-1, K)
    return bool(acc.any(axis=1).all())

def pack(rows, sizes, K):
    """ctypes M (row t of agent i at off[i] + t*W) and F, as check4 and check4_fast build them."""
    n, W = len(sizes), max(1, (K + 63) // 64)
    off = [0]
    for s in sizes: off.append(off[-1] + s * W)
    M = (ctypes.c_uint64 * off[-1])()
    for i in range(n):
        for t in range(sizes[i]):
            for a in np.flatnonzero(rows[i][t]): M[off[i] + t * W + a // 64] |= 1 << (int(a) % 64)
    F = (ctypes.c_uint64 * ((n + 1) * W))()
    full = [rows[i].all(axis=0) for i in range(n)]
    for l in range(n + 1):
        ok = np.ones(K, dtype=bool)
        for j in range(l, n): ok &= full[j]
        for a in np.flatnonzero(ok): F[l * W + a // 64] |= 1 << (int(a) % 64)
    return W, off, M, F

def part_a(systems, rng):
    lib_plain = PLAIN.load_c()
    stats = {True: 0, False: 0}
    fallback = 0
    for k in range(systems):
        n = int(rng.integers(2, 8))
        big_last = k % 5 == 4                           # a last agent with more than 512 types
        if big_last:
            sizes = [int(rng.integers(1, 3)) for _ in range(n - 1)] + [int(rng.integers(513, 700))]
            n = len(sizes)
        else:
            cap = {2: 60, 3: 30, 4: 14, 5: 8, 6: 6, 7: 5}[n]
            sizes = [int(rng.integers(1, cap + 1)) for _ in range(n)]
        K = int(rng.integers(1, 201))
        P = float(np.prod(sizes))                       # density with about 0.1..10 uncovered profiles expected
        q = np.exp(rng.uniform(np.log(0.1 / P), np.log(10 / P)))   # q = chance that a profile is uncovered
        dens = min(0.999, (1 - q ** (1.0 / K)) ** (1.0 / n))
        rows = [rng.random((s, K)) < dens for s in sizes]
        if rng.random() < 0.3:                          # plant allocations safe for everyone, or for a suffix
            a = int(rng.integers(K)); l0 = int(rng.integers(n))
            for i in range(l0, n): rows[i][:, a] = True
        W, off, M, F = pack(rows, sizes, K)
        b = brute(rows, sizes, K)
        f = FAST.coverage(n, W, sizes, off, M, F)
        pl = lib_plain.covered(n, W, (ctypes.c_int * n)(*sizes), (ctypes.c_long * n)(*off[:n]), M, F) == 1
        if not (b == f == pl):
            print(f"DISAGREE (random rows) n={n} sizes={sizes} K={K}: brute {b}, check4_fast {f}, check4 {pl}")
            return False, stats, fallback
        stats[b] += 1; fallback += big_last
    print(f"A. {systems} random row systems (n = 2..7, 1..200 allocations; {fallback} with a last agent of > 512 types): "
          f"check4_fast = check4 = brute force on all ({stats[True]} covered, {stats[False]} not)", flush=True)
    return True, stats, fallback

FILES = ['k4_certs_2.json.gz', 'k4_certs_3.json.gz', 'k4_certs_4_n4_1.json.gz', 'k4_certs_4_n4_2.json.gz',
         'k4_certs_4_n4_3.json.gz', 'k4_certs_4_pure.json.gz', 'k4_certs_5_n4_1.json.gz', 'k4_certs_5_n4_2.json.gz',
         'k4_certs_5_n4_3.json.gz', 'k4_certs_5_n4_4.json.gz', 'k4_certs_5_pure.json.gz', 'k4_certs_6_n4_1.json.gz']

def plain_covered(task):
    return PLAIN.covered(task)

def part_b(trials, rng, limit):
    from multiprocessing import Pool, TimeoutError as TE
    pool = Pool(1)
    tot = agree = cov = skipped = 0
    for fn in FILES:
        data = json.load(gzip.open(os.path.join(ROOT, 'results', fn), 'rt'))
        n, ties = data['n'], data.get('ties', False)
        kinds = {'thinned': 0, 'perturbed': 0, 'intact': 0}
        for t in range(trials):
            kind = ['thinned', 'perturbed', 'intact'][t % 3]
            r = rng.choice(data['cores'])
            A = [list(a) for a in r['allocs']]
            if kind == 'thinned':
                keep = rng.choice([0.5, 0.8, 0.95])
                A = [a for a in A if rng.random() < keep] or A[:1]
            elif kind == 'perturbed':
                a = rng.randrange(len(A)); g = rng.randrange(r['m'])
                A[a][g] = rng.choice([j for j in range(n) if j != A[a][g]])
            task = (n, r['m'], r['sets'], A, ties)
            try: p = pool.apply_async(plain_covered, (task,)).get(timeout=limit)
            except TE:
                pool.terminate(); pool = Pool(1); skipped += 1; continue
            f = FAST.covered(task)
            tot += 1; agree += p == f; cov += f; kinds[kind] += 1
            if p != f: print(f"DISAGREE {fn} m={r['m']} sets={r['sets']} ({kind}): check4 {p}, check4_fast {f}")
        print(f"  {fn}: {sum(kinds.values())} cores compared {kinds}", flush=True)
    pool.terminate()
    print(f"B. {tot} certificate cores (thinned, perturbed, intact): check4 and check4_fast agree on {agree} "
          f"({cov} covered, {tot - cov} not); {skipped} skipped (check4.py over {limit} s)", flush=True)
    return agree == tot

def part_c():
    good = FAST.safe_all_types
    FAST.safe_all_types = lambda Vi, An, i, n: ~good(Vi, An, i, n) if i == 0 else good(Vi, An, i, n)
    data = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_3.json.gz'), 'rt'))
    r = data['cores'][-1]
    caught = not FAST.covered((3, r['m'], r['sets'], r['allocs'], False))
    FAST.safe_all_types = good
    print(f"C. a corrupted safety table (agent 0 negated) is {'rejected' if caught else 'NOT rejected'}", flush=True)
    return caught

def safety_rows(n, m, sets, A_list):
    """rows[i]: bool array (|domain_i|, K), agent i's type t safe under allocation a (check4_fast's numpy table)."""
    doms = FAST.core_domains(sets, m, False)
    V = [np.array([[vals.get(g, 0) for g in range(m)] for vals in D], dtype=np.int64) for D in doms]
    rows = [np.zeros((len(D), len(A_list)), dtype=bool) for D in doms]
    for a, A in enumerate(A_list):
        An = np.array(A)
        for i in range(n): rows[i][:, a] = FAST.safe_all_types(V[i], An, i, n)
    return rows

def cover_set(rows, prof):
    acc = np.ones(rows[0].shape[1], dtype=bool)
    for i, t in enumerate(prof): acc &= rows[i][t]
    return acc

def near_threshold(n, m, sets, A_list, kind, rng):
    """A thinned allocation list with a known uncovered profile, or None if this core offers no such case."""
    rows = safety_rows(n, m, sets, A_list)
    for _ in range(50):
        if kind == 'hole':
            prof = [rng.randrange(len(r)) for r in rows]
        else:
            i = rng.randrange(n)
            R = rows[i]
            pairs = [(u, t) for u in range(len(R)) for t in range(len(R))
                     if u != t and R[u].any() and not (R[u] & ~R[t]).any() and (R[t] & ~R[u]).any()]
            if not pairs: continue
            u, t = rng.choice(pairs)
            a = rng.choice(list(np.flatnonzero(R[u])))                  # P covered by allocation a
            prof = [rng.choice(list(np.flatnonzero(rows[j][:, a]))) if j != i else u for j in range(n)]
        dead = cover_set(rows, prof)
        if not dead.any(): continue                                      # already uncovered: not near the threshold
        keep = [A for a, A in enumerate(A_list) if not dead[a]]
        if not keep: continue
        if kind == 'trap':
            alt = list(prof); alt[i] = t
            if not (cover_set(rows, alt) & ~dead).any(): continue      # the t-profile must stay covered
        return keep
    return None

def part_d(trials, rng, limit):
    from multiprocessing import Pool, TimeoutError as TE
    pool = Pool(1)
    tot = ok = skipped_plain = none = 0
    for fn in FILES:
        data = json.load(gzip.open(os.path.join(ROOT, 'results', fn), 'rt'))
        n = data['n']
        done = {'hole': 0, 'trap': 0}
        for t in range(trials):
            kind = ['hole', 'trap'][t % 2]
            r = rng.choice(data['cores'])
            keep = near_threshold(n, r['m'], r['sets'], r['allocs'], kind, rng)
            if keep is None: none += 1; continue
            task = (n, r['m'], r['sets'], keep, False)
            f = FAST.covered(task)
            try: p = pool.apply_async(plain_covered, (task,)).get(timeout=limit)
            except TE:
                pool.terminate(); pool = Pool(1); skipped_plain += 1; p = None
            tot += 1; done[kind] += 1
            good = (f is False) and (p in (False, None))
            ok += good
            if not good: print(f"WRONG {fn} m={r['m']} sets={r['sets']} ({kind}): check4 {p}, check4_fast {f} (expected not covered)")
        print(f"  {fn}: {done}", flush=True)
    pool.terminate()
    print(f"D. {tot} near-threshold corruptions (hole, trap) from every class: check4_fast says 'not covered' on {ok}; "
          f"check4.py agrees on all it finished ({skipped_plain} over {limit} s); {none} draws offered no case", flush=True)
    return ok == tot

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    limit = float(([a.split('=')[1] for a in sys.argv[1:] if a.startswith('--limit=')] or [30])[0])
    systems = int(args[0]) if len(args) > 0 else 2000
    trials = int(args[1]) if len(args) > 1 else 30
    import hashlib
    for f in ('check4.py', 'check4_fast.py'):
        print(f"k4/{f} sha256: {hashlib.sha256(open(os.path.join(os.path.dirname(HERE), f), 'rb').read()).hexdigest()}")
    ok_a = part_a(systems, np.random.default_rng(2026))[0]
    ok_b = part_b(trials, random.Random(2026), limit)
    ok_c = part_c()
    ok_d = part_d(trials, random.Random(2027), limit)
    print("ALL AGREE" if ok_a and ok_b and ok_c and ok_d else "FAILED")
    sys.exit(0 if ok_a and ok_b and ok_c and ok_d else 1)
