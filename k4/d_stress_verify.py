"""Checks for k4/d_stress.md added in the review of PR #42 (items N1-N4). Run from k4/; log: results/k4_dstress_verify.log.
  brute      compile d_stress_brute.c (plain enumeration, no SAT) and run it on H_1 (d_stress.chain(1)) at the paper
             values of k4/c4.md section 7 and at the three owner-climb minima of H_1 in results/k4_dstress_climbs.log:
             the number of D2 EFX0 allocations, by owner of the bundle above 2 goods; compared with the owners logged
             by the second encoding
  small      for every pure-core profile (the witness files results/k4_dstress_witnesses/pure_*.json.gz and the pure
             owner-climb minima in results/k4_dstress_climbs.log): does an EFX0 allocation with every bundle <= 2
             exist? (second encoding, d_stress_check.decide(s=2, big=0); every allocation re-checked by raw())
  corrupt    sensitivity of `d_stress_check.py FILE`: an intact copy of three records of a witness file must pass, and
             four corrupted copies (one record changed each) must be rejected
  replay     the self-test streams of results/k4_dstress_check_selftest.log replayed with d_stress.py: how many of
             their profiles have no D2 allocation
  reproduce  rerun three logged random-profile runs; compare the output (commit line and timings masked) with the
             logged block and the witnesses with the committed witness file
  iso        for t = 1..8: d_stress.chain(t) at the paper values (d_stress.paper_profile) is isomorphic to H_t as built
             by k4/c4_chain.py (agents and goods relabelled, every agent's value for every good kept; networkx)
Usage: python3 d_stress_verify.py brute|small|corrupt|replay|reproduce|iso"""
import sys, os, re, json, gzip, random, subprocess, tempfile
import d_stress as D
import d_stress_check as DC

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, '..', 'results')


def climb_minima():
    """(args, sets, logged owners, values) for every owner-climb minimum in results/k4_dstress_climbs.log."""
    out, args, sets = [], None, None
    for line in open(os.path.join(RES, 'k4_dstress_climbs.log')):
        if line.startswith('$ '):
            words = line.split()[3:]
            args = [w for w in words if not w.startswith('--')]
            seed = int(next(w for w in words if w.startswith('--seed=')).split('=')[1])
            sets = D.build(args, random.Random(seed))        # the hypergraph is fixed by the seed (run order: build first)
        m = re.match(r'\s+owners at the minimum: (\[.*?\]); profile (\[\[.*\]\])\s*$', line)
        if m: out.append((args, sets, json.loads(m.group(1)), json.loads(m.group(2))))
    return out


def brute():
    exe = os.path.join(tempfile.mkdtemp(), 'd_stress_brute')
    subprocess.run(['cc', '-O2', '-o', exe, os.path.join(HERE, 'd_stress_brute.c')], check=True)
    I = D.Inst(D.chain(1))
    cases = [('paper values', I.values(D.paper_profile(I)), None)]
    cases += [('climb minimum %d' % k, vals, own) for k, (args, sets, own, vals) in
              enumerate(x for x in climb_minima() if x[0] == ['chain', '1'])]
    print('H_1 = chain 1: %s' % json.dumps(I.sets))
    for name, vals, own in cases:
        inp = '%d %d\n' % (I.n, I.m) + ''.join('%d %s %s\n' % (len(S), ' '.join(map(str, S)), ' '.join(map(str, v)))
                                               for S, v in zip(I.sets, vals))
        res = subprocess.run([exe], input=inp, capture_output=True, text=True, check=True).stdout.strip()
        c = [int(x) for x in re.search(r'by owner ([\d ]+);', res).group(1).split()]
        none = int(re.search(r'none (\d+)', res).group(1))
        feas = list(range(I.n)) if none else [o for o in range(I.n) if c[o]]
        cmp = '' if own is None else '; logged owners %s: %s' % (own, 'agree' if own == feas else 'DISAGREE')
        print('  %s %s: D2 EFX0 allocations %s; feasible owners %s%s' % (name, json.dumps(vals), res, feas, cmp))


def small():
    bad = tot = 0
    for f in sorted(os.listdir(os.path.join(RES, 'k4_dstress_witnesses'))):
        if not f.startswith('pure_'): continue
        rec = json.load(gzip.open(os.path.join(RES, 'k4_dstress_witnesses', f), 'rt'))
        no = sum(DC.decide(rec['sets'], vals, 2, 0) is None for vals, _ in rec['witnesses'])
        print('  %s (%s): %d profiles, %d without an EFX0 allocation with every bundle <= 2' % (
            f, ' '.join(rec['args']), len(rec['witnesses']), no), flush=True)
        bad += no; tot += len(rec['witnesses'])
    mins = [x for x in climb_minima() if x[0][0] == 'pure']
    no = sum(DC.decide(sets, vals, 2, 0) is None for args, sets, own, vals in mins)
    print('  pure owner-climb minima (results/k4_dstress_climbs.log): %d profiles, %d without one' % (len(mins), no))
    print('total: %d pure-core profiles, %d without an EFX0 allocation with every bundle <= 2' % (tot + len(mins), bad + no))


def corrupt():
    src = os.path.join(RES, 'k4_dstress_witnesses', 'chain_1.json.gz')
    rec = json.load(gzip.open(src, 'rt'))
    W = [[list(map(list, v)), list(A)] for v, A in rec['witnesses'][:3]]
    n = len(rec['sets'])
    kinds = [('intact', lambda v, A: (v, A), 0),
             ('allocation shifted (every good to the next agent)', lambda v, A: (v, [(x + 1) % n for x in A]), 1),
             ('agent 0 values (9, 9, 9, 9), not a type', lambda v, A: ([[9, 9, 9, 9]] + v[1:], A), 1),
             ('every good in agent 0 bundle', lambda v, A: (v, [0] * len(A)), 1),
             ('allocation missing its last good', lambda v, A: (v, A[:-1]), 1)]
    d = tempfile.mkdtemp()
    for k, (name, f, want) in enumerate(kinds):
        ws = [list(w) for w in W]
        ws[0] = list(f(*W[0]))
        p = os.path.join(d, 'case%d.json.gz' % k)
        with gzip.open(p, 'wt') as fh: json.dump({'args': rec['args'], 'sets': rec['sets'], 'witnesses': ws}, fh)
        r = subprocess.run([sys.executable, os.path.join(HERE, 'd_stress_check.py'), p], capture_output=True, text=True)
        fails = int(re.search(r'(\d+) failures', r.stdout).group(1))
        ok = (r.returncode != 0) == bool(want) and fails == want
        print('  %s: exit %d, %d failures of 3 records: %s' % (name, r.returncode, fails,
                                                               'as expected' if ok else 'NOT AS EXPECTED'))


def replay():
    for args, N in ((['pure', '3', '5'], 150), (['pure', '4', '7'], 150), (['pure', '6', '8'], 150),
                    (['chain', '1'], 150), (['chain', '2'], 30), (['chain', '3'], 30), (['tree', '3'], 30)):
        rng = random.Random(5)                                 # the self-test's stream
        I = D.Inst(D.build(args, rng))
        bad = sum(I.shape(I.random_profile(rng)) is None for _ in range(N))
        print('  selftest %s %d: %d profiles without a D2 allocation' % (' '.join(args), N, bad), flush=True)


def reproduce():
    mask = lambda s: re.sub(r'\(\d+\.\d s\)', '(T s)', s)
    for fam, name in (('chain', 'chain_2'), ('cycle', 'cycle_3'), ('pure', 'pure_6_8')):
        log = open(os.path.join(RES, 'k4_dstress_%s.log' % fam)).read().split('\n')
        i = next(k for k, l in enumerate(log) if l.startswith('$ ') and '/%s.json.gz' % name in l)
        j = next((k for k in range(i + 1, len(log)) if log[k].startswith('$ ')), len(log))
        block = [l for l in log[i + 1:j] if l and not l.startswith('commit ')]
        cmd = log[i].split('&& ', 1)[1].split()
        out = os.path.join(tempfile.mkdtemp(), name + '.json.gz')
        cmd = [sys.executable] + cmd[1:-1] + ['--witnesses=' + out]
        r = subprocess.run(cmd, capture_output=True, text=True, cwd=HERE, check=True).stdout.split('\n')
        new = [l for l in r if l and not l.startswith('commit ')]
        new = [l.replace(out, '../results/k4_dstress_witnesses/%s.json.gz' % name) for l in new]
        same_log = list(map(mask, new)) == list(map(mask, block))
        same_w = json.load(gzip.open(out, 'rt')) == json.load(gzip.open(os.path.join(RES, 'k4_dstress_witnesses', name + '.json.gz'), 'rt'))
        print('  %s: output %s the logged block of %d lines (commit line dropped, timings masked); %d witnesses %s the '
              'committed file' % (log[i][2:], 'identical to' if same_log else 'DIFFERENT FROM', len(block),
                                  len(json.load(gzip.open(out, 'rt'))['witnesses']), 'identical to' if same_w else 'DIFFERENT FROM'),
            flush=True)


def iso():
    import networkx as nx
    import c4_chain
    def graph(sets, vals):
        G = nx.Graph()
        for i, (S, v) in enumerate(zip(sets, vals)):
            G.add_node(('a', i), kind='agent')
            for g, x in zip(S, v):
                G.add_node(('g', g), kind='good')
                G.add_edge(('a', i), ('g', g), value=x)
        return G
    for t in range(1, 9):
        I = D.Inst(D.chain(t))
        sets, vals, m = c4_chain.build(t)
        same = nx.is_isomorphic(graph(I.sets, I.values(D.paper_profile(I))), graph(sets, vals),
                                node_match=lambda a, b: a['kind'] == b['kind'],
                                edge_match=lambda a, b: a['value'] == b['value'])
        print('  t = %d (n = %d, m = %d): chain(t) at the paper values %s H_t of c4_chain.build' % (
            t, I.n, I.m, 'is isomorphic to' if same else 'is NOT isomorphic to'), flush=True)


if __name__ == '__main__':
    print('commit %s' % D.git_head(), flush=True)
    {'brute': brute, 'small': small, 'corrupt': corrupt, 'replay': replay, 'reproduce': reproduce, 'iso': iso}[sys.argv[1]]()
