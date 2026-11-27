"""W^sub (k4/haxell.md §6) on the n = 4, k = 4 core hypergraphs (results/k4_certs_4*.json.gz, k4/search4.py), through
gstar_measure.c: every partial EFX0 allocation with a nonempty pool of every instance tested.

Types.  An agent's strict ordinal type is a strict additive order type of its relevant goods (k4/order_types.json),
realized by the type's integer representative ('rep', values in the agent's good order).  DOMAIN=cert uses the
domains of the core certificates (strict balanced types; an agent with two private goods p, q also has p + q < the
other two), which are what the cores need for TARGET_4; DOMAIN=strict uses every strict type (balanced or not), which
the one-step lemma also claims.  The domain sizes are checked against the 'domains' field of the certificates.

Welfare is not ordinal, so a type profile does not fix the instance: SCALE=1 multiplies each agent's representative
by a factor drawn from 1..4 (so the agents' welfare weights vary); SCALE=0 uses the representatives as they are.

    MODE=all:    every profile of every core with m <= MMAX and at most PMAX profiles, up to the hypergraph's
                 automorphisms (agent and good permutations preserving the relevant sets);
    MODE=sample: N random profiles (uniform over the domain product) of every core with MMIN <= m <= MMAX.

    python3 k4/haxell/ht_n4core.py MODE=all [MMAX=5] [PMAX=100000] [DOMAIN=cert] [MARGS=2,1,1,1] [PROCS=4]
    python3 k4/haxell/ht_n4core.py MODE=sample [N=100] [MMIN=4] [MMAX=8] [SEED=1] [SCALE=0] [DOMAIN=cert] ..."""
import sys, os, gzip, json, glob, itertools, random, subprocess, collections, threading, time, math
import networkx as nx
from networkx.algorithms import isomorphism
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.join(HERE, '..', '..')
args = dict(a.split('=') for a in sys.argv[1:] if '=' in a)
MODE = args.get('MODE', 'all'); MMIN = int(args.get('MMIN', '4')); MMAX = int(args.get('MMAX', '5'))
PMAX = int(args.get('PMAX', '100000')); N = int(args.get('N', '100')); SEED = int(args.get('SEED', '1'))
SCALE = int(args.get('SCALE', '0')); DOMAIN = args.get('DOMAIN', 'cert')
MARGS = args.get('MARGS', '2,1,1,1').split(','); P = int(args.get('PROCS', '4'))
ONLY = int(MARGS[2]) if len(MARGS) > 2 else -1
ONLY2 = int(MARGS[7]) if len(MARGS) > 7 else -1
OT = json.load(open(os.path.join(ROOT, 'k4', 'order_types.json')))
STRICT = {k: [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict']] for k in (3, 4)}
STRICT_BAL = {k: [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict'] and t['balanced']] for k in (3, 4)}


def load_cores():
    out = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'results', 'k4_certs_4*.json.gz'))):
        for c in json.load(gzip.open(f))['cores']:
            out.append((os.path.basename(f), c))
    return out


def domain(S, deg):
    if DOMAIN == 'strict':
        return STRICT[len(S)]
    dom = STRICT_BAL[len(S)]
    priv = [p for p, g in enumerate(S) if deg[g] == 1]
    if len(priv) == 2:
        dom = [v for v in dom if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
    return dom


def automorphisms(sets, m):
    """(agent permutation a, good permutation b) pairs: b(S_i) = S_{a(i)} for every agent i"""
    n = len(sets); G = nx.Graph()
    G.add_nodes_from(('a', i) for i in range(n)); G.add_nodes_from(('g', g) for g in range(m))
    for i, S in enumerate(sets):
        for g in S:
            G.add_edge(('a', i), ('g', g))
    nm = lambda x, y: x['kind'] == y['kind']
    for v in G.nodes:
        G.nodes[v]['kind'] = v[0]
    out = []
    for f in isomorphism.GraphMatcher(G, G, node_match=nm).isomorphisms_iter():
        out.append((tuple(f[('a', i)][1] for i in range(n)), tuple(f[('g', g)][1] for g in range(m))))
    return out


def line(sets, m, prof, scale=None):
    parts = [str(len(sets)), str(m)]
    for i, (S, v) in enumerate(zip(sets, prof)):
        c = scale[i] if scale else 1
        parts.append(str(len(S)))
        for g, x in zip(S, v):
            parts += [str(g), str(c * x)]
    return ' '.join(parts)


def profiles_all(sets, m, doms):
    autos = [(a, b) for a, b in automorphisms(sets, m) if a != tuple(range(len(sets))) or b != tuple(range(m))]
    for prof in itertools.product(*doms):
        key = tuple(prof); ok = True
        for a, b in autos:
            img = [None] * len(sets)
            for i, (S, v) in enumerate(zip(sets, prof)):
                d = {b[g]: x for g, x in zip(S, v)}
                img[a[i]] = tuple(d[g] for g in sets[a[i]])
            if tuple(img) < key:
                ok = False; break
        if ok:
            yield prof


if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_n4core.py', *sys.argv[1:], flush=True)
    t0 = time.time(); rng = random.Random(SEED)
    C = collections.Counter(); percore = collections.Counter()
    phis = ['phi0'] + (['phi%d' % ONLY] if ONLY > 0 else ['phi1', 'phi2']) + (['phi%d' % ONLY2] if ONLY2 > 0 else [])
    procs = [subprocess.Popen([os.path.join(HERE, 'gstar_measure')] + MARGS, stdin=subprocess.PIPE,
                              stdout=subprocess.PIPE, text=True, bufsize=1 << 16) for _ in range(P)]
    sent = [collections.deque() for _ in range(P)]; lock = threading.Lock(); shown = [0]

    def reader(k):
        for ln in procs[k].stdout:
            w = ln.split(); d = {w[2 * t + 4]: int(w[2 * t + 5]) for t in range(19)}
            with lock:
                tag, src = sent[k].popleft()
                C['instances'] += 1; C['partial EFX0 states'] += int(w[3])
                for key in phis:
                    C['stuck states ' + key] += d[key]; C['instances with a stuck state ' + key] += d[key] > 0
                    percore[(tag, key)] += d[key] > 0
                if any(d[key] for key in phis[1:]) and shown[0] < 30:
                    shown[0] += 1; print('STUCK', tag, src, '|', ln.strip(), flush=True)
    threads = [threading.Thread(target=reader, args=(k,)) for k in range(P)]
    for th in threads:
        th.start()
    t = 0; ncores = 0; skipped = collections.Counter()
    for fname, c in load_cores():
        sets, m = c['sets'], c['m']
        if not (MMIN <= m <= MMAX):
            continue
        deg = [sum(g in S for S in sets) for g in range(m)]
        doms = [domain(S, deg) for S in sets]
        if DOMAIN == 'cert':
            assert [len(d) for d in doms] == c['domains'], (fname, c['idx'], [len(d) for d in doms], c['domains'])
        tag = '%s:m%d:%d' % (fname.replace('.json.gz', ''), m, c['idx'])
        if MODE == 'all':
            if math.prod(len(d) for d in doms) > PMAX:
                skipped[fname] += 1; continue
            gen = profiles_all(sets, m, doms)
        else:
            gen = ([rng.choice(d) for d in doms] for _ in range(N))
        ncores += 1
        for prof in gen:
            sc = [rng.randint(1, 4) for _ in sets] if SCALE else None
            ln = line(sets, m, prof, sc); k = t % P
            with lock:
                sent[k].append((tag, ln))
            procs[k].stdin.write(ln + '\n'); t += 1
    for p in procs:
        p.stdin.close()
    for th in threads:
        th.join()
    rc = [p.wait() for p in procs]
    print('cores', ncores, 'instances sent', t, 'skipped (more than PMAX profiles)', dict(skipped), 'return codes', rc)
    for key in sorted(C):
        print(key, C[key])
    for key in phis[1:]:
        bad = sorted({tag for (tag, k2), v in percore.items() if v and k2 == key})
        print('cores with a stuck instance for %s:' % key, len(bad), bad[:20])
    print('time %.0f s' % (time.time() - t0))
