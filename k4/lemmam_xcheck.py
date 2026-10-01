"""Second implementation for the Lemma M portfolio (k4/lemmam_portfolio.c), on PR #33's independent model of LB4r
(k4/c4_verify_H/lb4r.py, a transcription of lean/EFX/LB4R.lean) and k4/rulef_model.py (Lemma K written from the
text), without code from k4/rulef.c or k4/lemmam_portfolio.c.

Per first agent a (tau_a = (a, then index order)) and policy pol in (shrink, envyFree):
  K0      RM.deficit_K(state) <= 0 (omega <= 0 included), XKEEP = True (rulef.c -Y1);
  K1      not K0, and RM.rot_deficit_K(state) <= 0 (every RotStep of the model);
  M1      k4/rulef.md §6 Step 3, written here from the text: omega <= 0, or r (last-processed unmarked agent) not
          frozen and a least ∅-service of the exposed agents that are not free has size <= kappa_0 (free agents other
          than r that are not exposed); kept-out sets are ANY subsets of J (Lemma K as written), slot goods any good of J;
  KRa/KRb Lemma KR (k4/rulef.md §3) with o = r, written here from the text: the rotation is built with the model's
          rotate() and its needs with the model's needs_of; (ii) is "o not frozen in P'"; KRb is the "in particular"
          form (delta <= 1 and (eps = 0 or c_k >= 1 and eps = 1)), KRa the full bound delta - 1 - c_k + eps <= 0; every
          rotation used is also checked with the model's rot_checks (the lemma says P' is valid);
  partners  x1 (exposed frozen 4-good agents w.r.t. r), x2 (leader of r's block), x3 (ends of need chains from the x1
          agents), x3b (from r's block leader when exposed and frozen), x3c (from any exposed frozen agent), x4 (r).
Candidates as in the C header (k4/lemmam_portfolio.c).

Usage:
  lemmam_xcheck.py --sample=N FILE [FILE ...] [--seed=S] [--jobs=J] [--Copts=-Y1]
        N random (core, profile) pairs of the certificate files; k4/lemmam_portfolio.c -T1 -v on each; compares every
        per-agent field (K0, K1, M1, KRb, KRa, big-top) and every candidate verdict
  lemmam_xcheck.py --fails=LOG [LOG ...] [--max=K]
        every PFAIL / XFAIL / HFAIL line of the logs: recomputes the candidate (or partner) in this model and confirms
        the failure (prints CONFIRMED or NOT CONFIRMED with the per-agent data)"""
import itertools, json, os, random, re, subprocess, sys, gzip
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'c4_verify_H'))
import lb4r as M
import rulef_model as RM
RM.XKEEP = True
POLS = ('shrink', 'envyFree')


def val(inst, i, S): return sum(inst.v[i][g] for g in S)


def thr(inst, x, L, H): return RM.threatened(inst, x, L, H)


def run_info(inst, a, pol):
    """state after Phase 1(tau_a) and upgrades, with processing positions and blocks"""
    s, run = M.phase1_state(inst, (a,))
    s, _ = M.up_run(inst, s, pol)
    pos = {x: i for i, (x, f, k) in enumerate(run)}
    blk, b = {}, -1
    for x, f, k in run:
        if k == 'I': b += 1
        blk[x] = b
    return s, pos, blk


def minimal_protect(inst, x, W, Hx, pool):
    """all minimal D inside pool (any goods) with x not threatened by W - D holding Hx"""
    mins = []
    pool = sorted(pool)
    for r in range(len(pool) + 1):
        for D in itertools.combinations(pool, r):
            D = frozenset(D)
            if any(E <= D for E in mins): continue
            if not thr(inst, x, W - D, Hx): mins.append(D)
    return mins


def options(inst, x, W, Hx, J, capx):
    """Lemma K options with K = ∅: ('s', {g}) slot goods, ('r', D) kept-out sets (minimal)"""
    ox = []
    if capx >= 1:
        ox += [('s', frozenset([g])) for g in J if not thr(inst, x, W - {g}, list(Hx) + [g])]
    ox += [('r', D) for D in minimal_protect(inst, x, W, Hx, J)]
    return ox


def state_basics(inst, s):
    needs = M.all_needs(inst, s)
    NA = M.NA_of(needs)
    fr = M.frozen_pre(inst, s, NA)
    bases = [M.base_of(inst, s, i) for i in range(inst.n)]
    J = [g for g in range(inst.m) if s[0][g] == -1]
    cap = [0 if fr[x] else max(0, 2 - len(bases[x])) for x in range(inst.n)]
    return needs, NA, fr, bases, J, cap


def last_r(inst, s, pos):
    cand = [i for i in range(inst.n) if not s[2][i]]
    return max(cand, key=lambda i: pos[i]) if cand else None


def m1(inst, s, pos):
    needs, NA, fr, bases, J, cap = state_basics(inst, s)
    if M.omega(inst, s, needs) <= 0: return True
    r = last_r(inst, s, pos)
    if r is None or fr[r]: return False
    W = set(bases[r]) | set(J)
    kappa0 = 0; opts = []
    for x in range(inst.n):
        if x == r: continue
        free = (not s[2][x]) and (not fr[x]) and len(bases[x]) == 1
        if not thr(inst, x, W, bases[x]):
            if free: kappa0 += 1
            continue
        if free: continue
        ox = options(inst, x, W, bases[x], J, cap[x])
        if not ox: return False
        opts.append(ox)
    best = [10 ** 9]

    def dfs(i, U, G):
        if len(U) >= best[0]: return
        if i == len(opts): best[0] = len(U); return
        for kind, S in opts[i]:
            if kind == 's' and (S & G): continue
            dfs(i + 1, U | S, G | S if kind == 's' else G)
    dfs(0, frozenset(), frozenset())
    return best[0] <= kappa0


def need_chains(inst, s, needs, fr, k, o):
    """chains k = x0, .., xt = o: distinct, x0..x_{t-1} frozen, pick of x_i needed by x_{i+1}"""
    out = []
    pick = s[1]

    def ext(c):
        y = pick[c[-1]]
        if y < 0: return
        for b in range(inst.n):
            if b in c or y not in needs[b]: continue
            if b == o: out.append(c + [b])
            elif fr[b] and not s[2][b]: ext(c + [b])
    ext([k])
    return out


KR_INVALID = [0]


def kr(inst, s, o):
    """(KRa, KRb) of Lemma KR with owner o at state s"""
    needs, NA, fr, bases, J, cap = state_basics(inst, s)
    if fr[o] or len(bases[o]) > 1 or s[2][o]: return False, False
    W = frozenset(bases[o]) | frozenset(J)
    kappa = sum(cap[x] for x in range(inst.n) if x != o)
    E = [x for x in range(inst.n) if x != o and thr(inst, x, W, bases[x])]
    opts = {}
    for x in E:
        opts[x] = options(inst, x, W, bases[x], J, cap[x])
        if not opts[x]: return False, False
    ra = rb = False
    for k in range(inst.n):
        if k == o or not fr[k] or s[2][k]: continue
        yk = s[1][k]
        for c in need_chains(inst, s, needs, fr, k, o):
            y = s[1][c[-2]]
            pool = sorted(g for g in W if inst.v[k][g] > 0)
            for r in range(1, len(pool) + 1):
                for O in itertools.combinations(pool, r):
                    O = frozenset(O)
                    if not val(inst, k, O) > inst.v[k][yk]: continue
                    s2 = M.rotate(s, c, sorted(O))
                    n2 = M.all_needs(inst, s2)
                    if M.frozen_pre(inst, s2, M.NA_of(n2))[o]: continue          # (ii)
                    if not M.rot_checks(inst, s2): KR_INVALID[0] += 1          # the lemma says P' is valid
                    tho = thr(inst, o, W, [y])
                    Go = frozenset(g for g in W - O if not thr(inst, o, W - {g}, [y, g])) if tho else frozenset()
                    best = [False, False]

                    def dfs(i, Uo, G, Uk):
                        if len(Uo) > kappa + 1 or (best[0] and best[1]): return
                        if i == len(E):
                            eps = 0 if not tho else (1 if (Go - G) else None)
                            if eps is None: return
                            ck = len(Uk - Uo); delta = len(Uo | Uk) - kappa
                            if delta - 1 - ck + eps <= 0: best[0] = True
                            if delta <= 1 and (eps == 0 or (ck >= 1 and eps == 1)): best[1] = True
                            return
                        x = E[i]
                        for kind, S in opts[x]:
                            if x != k and (S & O): continue                     # (i)
                            if kind == 's' and (S & G): continue
                            G2 = G | S if kind == 's' else G
                            if x == k: dfs(i + 1, Uo, G2, Uk | S)
                            else: dfs(i + 1, Uo | S, G2, Uk)
                    dfs(0, frozenset(), frozenset(), frozenset())
                    ra |= best[0]; rb |= best[1]
                    if ra and rb: return ra, rb
    return ra, rb


def chain_ends(inst, s, needs, fr, k):
    """ends of need chains from k (inner agents frozen and unmarked; the end is the first other agent)"""
    out = set(); pick = s[1]

    def ext(c):
        y = pick[c[-1]]
        if y < 0: return
        for b in range(inst.n):
            if b in c or y not in needs[b]: continue
            if fr[b] and not s[2][b]: ext(c + [b])
            else: out.add(b)
    ext([k])
    return out


def agent_data(inst, a, want_k1=True):
    d = {'K0': False, 'K1': False, 'M1': False, 'KRa': False, 'KRb': False, 'KRo': False, 'part': {}}
    states = {}
    for pol in POLS:
        s, pos, blk = run_info(inst, a, pol)
        states[pol] = s
        if RM.deficit_K(inst, s) <= 0: d['K0'] = True
        d['M1'] |= m1(inst, s, pos)
        needs, NA, fr, bases, J, cap = state_basics(inst, s)
        P = 'N' if pol == 'shrink' else 'E'
        if M.omega(inst, s, needs) <= 0:
            for kname in ('x1', 'x2', 'x3', 'x3b', 'x3c', 'x4'): d['part'][kname + P] = set()
            continue
        r = last_r(inst, s, pos)
        ra, rb = kr(inst, s, r)
        d['KRa'] |= ra; d['KRb'] |= rb
        d['KRo'] |= ra or any(kr(inst, s, o)[0] for o in range(inst.n) if o != r)
        W = set(bases[r]) | set(J)
        E = [x for x in range(inst.n) if x != r and thr(inst, x, W, bases[x])]
        ks = min((x for x in range(inst.n) if blk[x] == blk[r]), key=lambda x: pos[x])
        x1 = {x for x in E if fr[x] and len(inst.R[x]) == 4}
        x3 = set().union(*[chain_ends(inst, s, needs, fr, x) for x in x1]) if x1 else set()
        x3c = set().union(*[chain_ends(inst, s, needs, fr, x) for x in E if fr[x]]) if any(fr[x] for x in E) else set()
        x3b = chain_ends(inst, s, needs, fr, ks) if (ks != r and ks in E and fr[ks]) else set()
        d['part'].update({'x1' + P: x1, 'x2' + P: {ks}, 'x3' + P: x3, 'x3b' + P: x3b, 'x3c' + P: x3c, 'x4' + P: {r}})
    if want_k1 and not d['K0']:
        for pol in POLS:
            if RM.rot_deficit_K(inst, states[pol])[0] <= 0: d['K1'] = True; break
    d['W'] = d['K0'] or d['K1']
    return d


def bigtop(inst, i):
    v = sorted((inst.v[i][g] for g in inst.R[i]), reverse=True)
    return len(v) == 4 and v[0] > v[1] + v[2]


def gap(inst, i, norm):
    v = sorted((inst.v[i][g] for g in inst.R[i]), reverse=True) + [0, 0, 0]
    g = v[0] - v[1] - v[2]
    return g / sum(v) if norm else g


SETS = ["all", "bt", "bt1", "nobt", "nobt0", "gap", "gapn", "btp", "shp", "bt2"]
PREDS = ["W", "K0", "M1", "KRb", "M1|KRb", "K0|KRa", "K0|KRo", "K0|KRb"]


def candidates(inst, D):
    """verdicts: 'set:pred' -> (applicable, number of allowed agents satisfying the predicate)"""
    n = inst.n
    bt = [bigtop(inst, i) for i in range(n)]
    tops = [max(inst.R[i], key=lambda g: inst.v[i][g]) for i in range(n)]
    sh = [any(j != i and tops[j] == tops[i] for j in range(n)) for i in range(n)]
    priv = [sum(1 for g in inst.R[i] if all(inst.v[j][g] == 0 for j in range(n) if j != i)) for i in range(n)]
    P = {'W': [D[a]['W'] for a in range(n)], 'K0': [D[a]['K0'] for a in range(n)], 'M1': [D[a]['M1'] for a in range(n)],
         'KRb': [D[a]['KRb'] for a in range(n)], 'M1|KRb': [D[a]['M1'] or D[a]['KRb'] for a in range(n)],
         'K0|KRa': [D[a]['K0'] or D[a]['KRa'] for a in range(n)], 'K0|KRo': [D[a]['K0'] or D[a]['KRo'] for a in range(n)],
         'K0|KRb': [D[a]['K0'] or D[a]['KRb'] for a in range(n)]}
    allag = list(range(n)); bts = [a for a in allag if bt[a]]; shs = [a for a in allag if sh[a]]
    ga = max(allag, key=lambda a: (gap(inst, a, False), -a)); gn = max(allag, key=lambda a: (gap(inst, a, True), -a))
    btp = [a for a in bts if priv[a] == min(priv[b] for b in bts)] if bts else []
    shp = [a for a in shs if priv[a] == min(priv[b] for b in shs)] if shs else []
    S = {'all': (True, allag), 'bt': (bool(bts), bts), 'bt1': (len(bts) == 1, bts), 'nobt': (not bts and bool(shs), shs),
         'nobt0': (not bts and not shs, allag), 'gap': (True, [ga]), 'gapn': (True, [gn]), 'btp': (bool(bts), btp),
         'shp': (not bts and bool(shs), shp), 'bt2': (len(bts) >= 2, bts)}
    out = {}
    for sn, (app, A) in S.items():
        for q in PREDS: out[f'{sn}:{q}'] = (app, sum(1 for a in A if P[q][a]))
    return out, bt


def parse_line(line):
    sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
    vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
    return sets, vals


def parse_fa(line):
    """per-agent C fields of a fa= block"""
    out = []
    for part in line.split(' fa=')[1].strip().split(';'):
        a, rest = part.split(':', 1)
        f = {}
        f['K0'] = int(re.search(r'K0=(\d)', rest).group(1)); f['K1'] = int(re.search(r'K1=(\d)', rest).group(1))
        f['bt'] = int(re.search(r'bt=(\d)', rest).group(1))
        f['M1'] = max(int(x) for x in re.findall(r'M1=(\d)', rest))
        f['KRb'] = max(int(x) for x in re.findall(r'KRb=(\d)', rest))
        f['KRa'] = max(int(x) for x in re.findall(r'KRa=(\d)', rest))
        out.append(f)
    return out


def check_sample(task):
    sets, vals, cline = task
    inst = RM.make_inst(sets, vals)
    D = [agent_data(inst, a) for a in range(inst.n)]
    C = parse_fa(cline)
    diffs = []
    for a in range(inst.n):
        py = {'K0': D[a]['K0'], 'W': D[a]['W'], 'M1': D[a]['M1'], 'KRb': D[a]['KRb'], 'KRa': D[a]['KRa'], 'bt': bigtop(inst, a)}
        cc = {'K0': C[a]['K0'], 'W': C[a]['K0'] or C[a]['K1'], 'M1': C[a]['M1'], 'KRb': C[a]['KRb'], 'KRa': C[a]['KRa'], 'bt': C[a]['bt']}
        for k in py:
            if bool(py[k]) != bool(cc[k]): diffs.append((a, k, bool(cc[k]), bool(py[k])))
    return sets, vals, diffs, KR_INVALID[0]


def main():
    args = sys.argv[1:]
    opt = lambda name, dflt=None: next((a.split('=', 1)[1] for a in args if a.startswith(f'--{name}=')), dflt)
    jobs = int(opt('jobs', 2))
    if opt('sample'):
        import lemmam_portfolio as LP
        import adaptive_run as AR
        import check4
        LP.build()
        N = int(opt('sample')); rng = random.Random(int(opt('seed', 1)))
        files = [a for a in args if not a.startswith('--')]
        cores = []
        for f in files:
            for c in json.load(gzip.open(f, 'rt'))['cores']: cores.append(c)
        copts = (opt('Copts', '-Y1')).split()
        tasks = []
        for _ in range(N):
            c = rng.choice(cores)
            doms = check4.core_domains(c['sets'], c['m'], False)
            vals = []
            for S, dom in zip(c['sets'], doms):
                t = rng.choice(dom); vals.append([t[g] for g in S])
            p = subprocess.run([LP.BIN] + copts + ['-T1', '-v'], input=AR.encode_profile(c['sets'], vals), capture_output=True, text=True)
            cl = next(l for l in p.stdout.split('\n') if l.startswith('PROF'))
            tasks.append((c['sets'], vals, cl))
        print(f'# lemmam_xcheck.py {" ".join(args)} # portfolio sha {LP.SHA}', flush=True)
        nd = 0; cnt = {}; inv = 0
        with Pool(jobs) as pool:
            for sets, vals, diffs, kinv in pool.imap_unordered(check_sample, tasks):
                inv += kinv
                for a, k, c, p in diffs:
                    cnt[k] = cnt.get(k, 0) + 1
                    nd += 1
                    if nd <= 30: print(f'DIFF field={k} agent={a} C={c} python={p} sets={json.dumps(sets)} vals={json.dumps(vals)}', flush=True)
        print(f'sample: {N} profiles ({len(cores)} cores from {", ".join(os.path.basename(f) for f in files)}), '
              f'per-agent field disagreements: {nd} {cnt}; KR rotations failing rot_checks (in worker processes): {inv}', flush=True)
        return
    if opt('fails') is not None:
        logs = [opt('fails')] + [a for a in args if not a.startswith('--')]
        mx = int(opt('max', 10 ** 9))
        seen = set(); lines = []
        for f in logs:
            for l in open(f):
                l = l.strip()
                mt = re.search(r'(PFAIL|XFAIL|HFAIL) ', l)
                if not mt: continue
                l = l[mt.start():]
                sets, vals = parse_line(l)
                tag = re.search(r'(cand|var)=(\S+)', l).group(0)
                if 'var=' in l and l.startswith('HFAIL'): tag = re.search(r'var=(\S+)', l).group(0)
                key = (tag, json.dumps(sets), json.dumps(vals), re.search(r' a=(\d+)', l).group(1) if ' a=' in l else '')
                if key in seen: continue
                seen.add(key); lines.append((l, tag, sets, vals))
        lines = lines[:mx]
        print(f'# lemmam_xcheck.py {" ".join(args)}: {len(lines)} distinct failure lines', flush=True)
        conf = notc = 0
        for l, tag, sets, vals in lines:
            inst = RM.make_inst(sets, vals)
            D = [agent_data(inst, a) for a in range(inst.n)]
            ver, bt = candidates(inst, D)
            if tag.startswith('cand='):
                c = tag[5:]
                import lemmam_portfolio as LP
                c = LP.ALIAS.get(c, c)
                app, nok = ver[c]
                ok = app and nok == 0
            else:
                v = tag.split('=', 1)[1]
                a = int(re.search(r' a=(\d+)', l).group(1)) if ' a=' in l else None
                agents = [a] if a is not None else range(inst.n)
                ok = False
                for b in agents:
                    if D[b]['W']: continue
                    Pset = D[b]['part'].get(v, set()) - {b}
                    if Pset and not any(D[x]['W'] for x in Pset): ok = True
            conf += ok; notc += not ok
            summ = ' '.join(f"{a}:K0={int(D[a]['K0'])},K1={int(D[a]['K1'])},M1={int(D[a]['M1'])},KRb={int(D[a]['KRb'])},KRa={int(D[a]['KRa'])},bt={int(bt[a])}" for a in range(inst.n))
            print(f"{'CONFIRMED' if ok else 'NOT CONFIRMED'} {tag} n={inst.n} m={inst.m} sets={json.dumps(sets)} vals={json.dumps(vals)} python: {summ}", flush=True)
        print(f'confirmed {conf}, not confirmed {notc}; KR rotations failing rot_checks: {KR_INVALID[0]}', flush=True)


if __name__ == '__main__':
    main()
