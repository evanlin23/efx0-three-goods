"""Exhaustive test of construction LB (construct.py; C implementation construct.c) on every connected core with n agents
and the given numbers of goods m (default: every m from 3 to 2n), under every ranking profile. Every output is checked
from the raw EFX0 definition (in construct.c, independent of the construction's T/P/B/C/E reasoning), including
"at most one bundle of >= 3 goods".
Options:
  --jobs=N         parallel C processes (default: all CPUs)
  --python=K       also run the Python reference on every K-th core and compare the hash of all its outputs with
                   the C run (K = 1: every core); the two implementations must produce identical allocations
  --disconnected   test the DISconnected cores with n agents instead: every multiset of >= 2 connected cores (each
                   with >= 2 agents) with n agents in total, goods relabelled apart
  --relabel=SEED   apply a random permutation of the agents and of the goods to every core first (seeded; LB breaks
                   ties by index, so this tests other labellings; evidence only)
  --cert=FILE      write a certificate (gzip JSON, the format of frontier.py; mode 'LB'): per core, allocations
                   output by the construction that cover every profile; check it with tools/check_certs.py and
                   construct_run.py --check-cert=FILE (every allocation has at most one bundle of >= 3 goods)
  --part=k/K       only the k-th of K contiguous slices of each core list (k = 1..K), so a long level can run in
                   pieces; the slices of one level partition its cores (merge their certificates for check_enum.py)
Usage: construct_run.py n [m ...] [options]"""
import sys, os, subprocess, time, json, gzip, itertools, multiprocessing, collections
from frontier import options
from cores_nauty import gen_cores_nauty

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, 'construct')

def compile_c():
    src = os.path.join(HERE, 'construct.c')
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O3', '-march=native', '-o', BIN, src], check=True)

def run_chunk(task):
    n, m, chunk, cert = task
    inp = f"{n} {m} {len(chunk)}\n" + "\n".join(" ".join(str(g) for S in sets for g in S) for _, sets in chunk) + "\n"
    out = subprocess.run([BIN] + (['-c'] if cert else []), input=inp, capture_output=True, text=True, check=True).stdout
    res, lines, k = [], out.split('\n'), 0
    while k < len(lines):
        t = lines[k].split(); k += 1
        if not t: continue
        if t[0] == 'core':
            d = t.index('D'); f = t.index('first')
            res.append({'fails': int(t[3]), 'large': int(t[5]), 'hash': t[7], 'D': list(map(int, t[d + 1:f])),
                        'first': None if t[f + 1] == '-' else tuple(map(int, t[f + 1:]))})
        elif t[0] == 'cert':
            c = int(t[2]); res[-1]['allocs'] = [list(map(int, lines[k + j].split())) for j in range(c)]; k += c
    return res

def py_hash(task):
    """FNV-1a over the Python reference's outputs, in the same profile order as construct.c."""
    from construct import construct, PERMS
    n, m, sets = task
    h = 1469598103934665603
    for prof in itertools.product(range(6), repeat=n):
        trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
        X = construct(n, m, trip) or [-1] * m
        for o in X: h = ((h ^ (o + 1)) * 1099511628211) & 0xffffffffffffffff
    return f"{h:016x}"

def disconnected_cores(n):
    """(m, pi, sets) for every disconnected core with n agents, up to isomorphism: multisets of >= 2 connected cores."""
    comps = {k: [(m, pi, sets) for m in range(3, 2 * k + 1) for pi, sets in gen_cores_nauty(k, m)] for k in range(2, n - 1)}
    def parts(r, mx):
        if r == 0: yield []
        for k in range(min(r, mx), 1, -1):
            for rest in parts(r - k, k): yield [k] + rest
    out = []
    for P in parts(n, n - 2):
        groups = [(k, P.count(k)) for k in sorted(set(P))]
        for choice in itertools.product(*(itertools.combinations_with_replacement(range(len(comps[k])), c) for k, c in groups)):
            m = pi = 0; sets = []
            for (k, _), idxs in zip(groups, choice):
                for i in idxs:
                    cm, cpi, cs = comps[k][i]
                    sets += [[g + m for g in S] for S in cs]; m += cm; pi += cpi
            out.append((m, pi, sets))
    return out

def check_cert(path):
    """Every allocation in the certificate has at most one bundle of >= 3 goods, and every hypergraph is a core (3
    distinct goods per agent, every good used, <= 1 private good per agent; connected or not) whose 6^n profiles are
    all covered, by tools/check_certs.py's SAT-free coverage check (check_certs.py itself also requires connectivity)."""
    sys.path.insert(0, os.path.join(HERE, '..', 'tools'))
    from check_certs import uncovered
    bad = 0; recs = json.load(gzip.open(path, 'rt'))
    for r in recs:
        for X in r['allocations']:
            if sum(v >= 3 for v in collections.Counter(X).values()) > 1: bad += 1
        deg = collections.Counter(g for S in r['sets'] for g in S)
        if (len(r['sets']) != r['n'] or any(len(set(S)) != 3 for S in r['sets']) or set(deg) != set(range(r['m']))
                or any(sum(deg[g] == 1 for g in S) > 1 for S in r['sets'])): print("not a core:", r['sets']); bad += 1
        u = uncovered(r)
        if u: print(f"UNCOVERED profiles: {u} for {r['sets']}"); bad += 1
    print(f"{path}: {len(recs)} hypergraphs, {sum(len(r['allocations']) for r in recs)} allocations; "
          f"problems (a second bundle of >= 3 goods, not a core, uncovered profiles): {bad}"); return bad

if __name__ == '__main__':
    args, opts = options(sys.argv[1:])
    if 'check-cert' in opts: sys.exit(1 if check_cert(opts['check-cert']) else 0)
    n = args[0]; ms = args[1:] or list(range(3, 2 * n + 1))
    jobs = int(opts.get('jobs', os.cpu_count())); pyk = int(opts.get('python', 0)); cert = opts.get('cert')
    compile_c(); t0 = time.time(); certs = []; allfails = 0
    log = lambda s: print(f"[{time.time() - t0:7.0f}s] {s}", flush=True)
    with multiprocessing.Pool(jobs) as pool:
        if 'disconnected' in opts:
            dis = disconnected_cores(n); ms = sorted({m for m, _, _ in dis})
        for m in ms:
            cores = gen_cores_nauty(n, m) if 'disconnected' not in opts else [(pi, s) for mm, pi, s in dis if mm == m]
            if 'part' in opts:
                k, K = map(int, opts['part'].split('/')); L = len(cores)
                cores = cores[(k - 1) * L // K:k * L // K]
            if 'relabel' in opts:
                import random
                rng = random.Random(f"{opts['relabel']}:{n}:{m}")
                def relabel(sets):
                    perm = list(range(m)); rng.shuffle(perm); sets = [[perm[g] for g in S] for S in sets]; rng.shuffle(sets)
                    return sets
                cores = [(pi, relabel(sets)) for pi, sets in cores]
            size = max(1, min(200, len(cores) // (4 * jobs) or 1))
            chunks = [cores[i:i + size] for i in range(0, len(cores), size)]
            res = [r for part in pool.map(run_chunk, [(n, m, ch, bool(cert)) for ch in chunks]) for r in part]
            fails = sum(r['fails'] for r in res); large = sum(r['large'] for r in res)
            D = collections.Counter()
            for r in res:
                for d, c in enumerate(r['D'], 3):
                    if c: D[d] += c
            first = [(sets, r['fails'], r['first']) for (_, sets), r in zip(cores, res) if r['fails']]
            part = f" (part {opts['part']})" if 'part' in opts else ''
            msg = (f"n={n} m={m}: {len(cores)} {'disconnected ' if 'disconnected' in opts else ''}cores{part}, {len(cores) * 6 ** n} hypergraph-profile pairs, construction fails on"
                   f" {fails}; outputs with a large bundle: {large} (by size {dict(sorted(D.items()))})")
            if pyk:
                idx = list(range(0, len(cores), pyk))
                ph = pool.map(py_hash, [(n, m, cores[i][1]) for i in idx])
                agree = sum(ph[j] == res[i]['hash'] for j, i in enumerate(idx))
                msg += f"; Python reference on {len(idx)} cores: identical outputs on {agree}"
                if agree != len(idx): allfails += 1
            log(msg)
            for sets, f, p in first[:10]: log(f"   FAIL {sets}: {f} profiles, first {p}")
            allfails += fails
            if cert:
                certs += [{'n': n, 'm': m, 'pi': pi, 'sets': sets, 'mode': 'LB', 'allocations': r['allocs']}
                          for (pi, sets), r in zip(cores, res)]
    if cert:
        with gzip.open(cert, 'wt') as f: json.dump(certs, f)
        log(f"certificate: {cert} ({len(certs)} hypergraphs)")
    log(f"ALL DONE; failures: {allfails}"); sys.exit(1 if allfails else 0)
