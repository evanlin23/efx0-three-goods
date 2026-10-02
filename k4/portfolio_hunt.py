"""Multi-target adversarial hunt over the surviving portfolio predicates (compute/k4-portfolio, Phase 3). EVIDENCE only.

Round-robin over the predicates of k4/portfolio_preds.py that are still alive (strongest first): each round gives every
alive predicate one annealing task per seed slot. A task anneals strict profiles of ONE fixed core (the hypergraph never
changes; a step replaces the type of one or two agents by another strict balanced type of check4.core_domains) to
minimize that predicate's margin, evaluating a batch of neighbours per step with the fast path (k4/portfolio_dump.c +
k4/portfolio_preds.py). Two margins (objectives, lower is better):
  count  the number of repairs (R-moves to better states; for a key-graph form, edges to better keys) at the worst state;
  edge   lexicographic (repairs by the next stronger predicate INNER[R], repairs by R) at the worst state: first drive the
         state to need R's edge (e.g. RC's T3+ with |W| >= 2 when INNER[RC] = RC_W1), then thin out those repairs.
Every evaluated profile is evaluated for EVERY alive predicate, so a task can kill any of them. A candidate failure is
re-derived with the reference implementation (k4/portfolio_ref.py, main's c4x_check; independent of portfolio_dump.c,
dlrt4.c and model.py); if confirmed, the predicate dies: results/k4_portfolio/FAILURES_<pred>.md and
FAILURES_<pred>.jsonl are written, committed and pushed (with --push), and the hunt continues with the rest.

Seeds (one fixed core each, with a starting profile):
  fail10   the 10 DL_RT4-failing n = 5 profiles (results/k4_rt4/n5b_failures_inst.json, n5c_fail_inst.json);
  hard     the profiles with the least RC3 / RC_W1 / K3b margins kept by the Phase 2 aggregates (results/k4_portfolio/*.json),
           one per core, n >= 4 (hard5: n >= 5; at n = 4 every RT4 move changes at most three agents, so RC3 contains
           RT4 there and the exhaustive n = 4 runs of K4.DL2.RT4E already cover it);
  rcores   random n = 5 cores with three or more 4-good agents and m <= 12 (k4_certs_5_n4_3, _n4_4, _pure), started at
           the hardest of 300 random profiles;
  ext      n = 6 extensions of the failing cores: a sixth agent with 3 or 4 goods, at least one of them old, the rest new
           (the core conditions of k4/suite/model.py's core_violations are checked here: degrees 3-4, at most d - 2
           private goods, connected; strict balanced types and the private-pair condition come from core_domains).
Gluings of two failing instances (n = 10) are not run: their min-frozen classes are products of two classes of ~60,
too slow for the Python predicates per annealing step (reduced coverage, said in SUMMARY.md).

  python3 k4/portfolio_hunt.py [--preds=A,B,...] [--rounds=R] [--slot=SECONDS] [--jobs=J] [--batch=B] [--push]
        [--seeds=fail10,hard,rcores,ext] [--name=LABEL]
State: results/k4_portfolio/hunt_<LABEL>.jsonl (one line per finished task; a rerun skips finished tasks and keeps the
dead predicates), log on stdout."""
import collections, gzip, json, os, random, subprocess, sys, time, zlib
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import portfolio as PF
import portfolio_preds as PR

OUT = PF.OUT
INNER = {'RC3_noT4': 'RT4', 'K3b_noT4': 'K1', 'RC3': 'RT4', 'NA3': 'RC3', 'K3b': 'K1', 'RC_W1': 'RC3', 'RC': 'RC_W1', 'RC_noneed': 'RC', 'RC_Yfree': 'RC', 'RC_Yany': 'RC', 'RC_U0': 'RC',
         'NA1': 'RC_U0', 'NAbal': 'NA1', 'NAall': 'NA1', 'U1Z1': 'NA1', 'D3': 'D2', 'D4': 'D3', 'FR3': 'D3',
         'K3': 'K3b', 'K2': 'K3', 'K2_noneed': 'K2', 'K2_Yany': 'K2', 'K4': 'K2', 'K5': 'K4', 'KU1': 'K4'}
KIND = {**{nm: 'single' for nm in PR.SNAMES}, **{nm: 'keyg' for nm in PR.KNAMES}}
ORDER = ['RC3_noT4', 'K3b_noT4', 'RC3', 'K3b', 'NA3', 'RC_W1', 'K3', 'RC', 'K2', 'RC_noneed', 'RC_Yfree', 'RC_Yany', 'K2_noneed', 'K2_Yany', 'RC_U0', 'NA1', 'K4', 'D3',
         'FR3', 'U1Z1', 'NAall', 'K5', 'KU1', 'D4']
BIG = 10 ** 6


# ---------------- seeds ----------------
def locate(doms, vals_list):
    """domain indices of a profile (values per agent aligned with sets); None if a type is not in the domain"""
    idx = []
    for D, vd in zip(doms, vals_list):
        k = next((t for t, d in enumerate(D) if d == vd), None)
        if k is None: return None
        idx.append(k)
    return tuple(idx)


def seed_from(name, sets, m, vals):
    doms = check4.core_domains(sets, m, False)
    vd = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    idx = locate(doms, vd)
    if idx is None: return None
    return {'name': name, 'sets': sets, 'm': m, 'start': idx}


def seeds_fail10():
    out = []
    for f in ('n5b_failures_inst.json', 'n5c_fail_inst.json'):
        for d in json.load(open(os.path.join(OUT, '..', 'k4_rt4', f))):
            s = seed_from('fail10:' + d['id'], d['sets'], d['m'], d['vals'])
            if s: out.append(s)
    return out


def seeds_hard(k=12, nmin=4):
    hs = []
    for fn in sorted(os.listdir(OUT)):
        if fn.endswith('.json') and not fn.startswith(('ref_', 'hunt')):
            try: d = json.load(open(os.path.join(OUT, fn)))
            except ValueError: continue
            if not isinstance(d, dict): continue
            for h in d.get('agg', {}).get('hard', []):
                if len(h['sets']) >= nmin: hs.append(h)
    hs.sort(key=lambda h: h['score'])
    out, seen = [], set()
    for h in hs:
        key = json.dumps(h['sets'])
        if key in seen: continue
        seen.add(key)
        s = seed_from('hard:' + h['id'], h['sets'], h['m'], h['vals'])
        if s: out.append(s)
        if len(out) >= k: break
    return out


def hardest_start(sets, m, rng, P=2000):
    """the hardest of P random profiles (least RC3, RC_W1 margins, larger f); None if none has a state"""
    doms = check4.core_domains(sets, m, False)
    profs = [tuple(rng.randrange(len(D)) for D in doms) for _ in range(P)]
    best = None
    for prof, res in evaluate_batch(sets, m, doms, profs):
        sc = (res['single']['RC3']['margin'], res['single']['RC_W1']['margin'], -(res['f'] or 0))
        if best is None or sc < best[0]: best = (sc, prof)
    return best[1] if best else None


def seeds_rcores(k=12, rng_seed=7):
    rng = random.Random(rng_seed)
    out = []
    for f in ('k4_certs_5_n4_3.json.gz', 'k4_certs_5_n4_4.json.gz', 'k4_certs_5_pure.json.gz'):
        cores = [c for c in json.load(gzip.open(os.path.join(OUT, '..', f), 'rt'))['cores'] if 9 <= c['m'] <= 12]
        got = 0
        for c in rng.sample(cores, 30 * k):                # cores where 2,000 random profiles give a state
            st = hardest_start(c['sets'], c['m'], rng)
            if st is None: continue
            out.append({'name': f'rcores:{f}#idx{c.get("idx")}', 'sets': c['sets'], 'm': c['m'], 'start': st})
            got += 1
            if got >= k // 3: break
    return out


def is_core(sets, m):
    n = len(sets)
    deg = [sum(g in S for S in sets) for g in range(m)]
    if any(d == 0 for d in deg): return False
    for S in sets:
        if not 3 <= len(S) <= 4: return False
        if sum(deg[g] == 1 for g in S) + 2 > len(S): return False
    seen, st = {0}, [0]                       # connected (agents through shared goods)
    while st:
        i = st.pop()
        for j in range(n):
            if j not in seen and set(sets[i]) & set(sets[j]): seen.add(j); st.append(j)
    return len(seen) == n


def seeds_ext(k=8, rng_seed=11):
    rng = random.Random(rng_seed)
    base = [d for f in ('n5b_failures_inst.json', 'n5c_fail_inst.json') for d in json.load(open(os.path.join(OUT, '..', 'k4_rt4', f)))]
    out, tries = [], 0
    while len(out) < k and tries < 2000:
        tries += 1
        d = rng.choice(base)
        m = d['m']; deg = rng.choice([3, 4]); new = rng.choice([0, 1, 1, 2]) if deg == 4 else rng.choice([0, 1])
        old = rng.sample(range(m), deg - new)
        S6 = sorted(old + list(range(m, m + new)))
        sets = [list(S) for S in d['sets']] + [S6]
        if not is_core(sets, m + new): continue
        doms = check4.core_domains(sets, m + new, False)
        base_idx = locate(doms[:5], [dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])])
        if base_idx is None: continue                 # an old agent's type is no longer admissible
        # the sixth agent's type: the hardest of 60
        cands = [base_idx + (t,) for t in rng.sample(range(len(doms[5])), min(60, len(doms[5])))]
        best = None
        for prof, res in evaluate_batch(sets, m + new, doms, cands):
            sc = (res['single']['RC3']['margin'], res['single']['RC_W1']['margin'])
            if best is None or sc < best[0]: best = (sc, prof)
        if best is None: continue
        out.append({'name': f"ext:{d['id']}+{S6}", 'sets': sets, 'm': m + new, 'start': best[1]})
    return out


# ---------------- evaluation ----------------
def evaluate_batch(sets, m, doms, profs):
    """[(prof, PR.evaluate result)] for the profiles of the batch with f >= 1, omega >= 1 and a state"""
    if not profs: return []
    A, _ = PF.run_c(PF.block(sets, m, doms, 0, 0, profs=list(profs)), ['-f1'], wide=m > 32)
    out = []
    for a in A:
        prof = tuple(a['prof'])
        vals = [[doms[i][p][g] for g in S] for i, (S, p) in enumerate(zip(sets, prof))]
        pd = PR.ProfData(sets, vals, m, [(B, (PF.INF if d >= PF.INF else d)) for B, d in a['cls']])
        r = PR.evaluate(pd)
        r['pd'] = pd
        out.append((prof, r))
    return out


def objective(r, pred, mode):
    kind = KIND[pred]
    e = r[kind][pred]
    if not e['nrep']: return (BIG, BIG)
    if mode == 'count': return (min(e['nrep']), 0)
    inner = INNER.get(pred)
    if inner is None: return (min(e['nrep']), 0)
    ei = r[kind][inner]
    return min(zip(ei['nrep'], e['nrep']))


def failures_in(r, alive, sets, m, prof, seedname):
    out = []
    pd = r['pd']
    for nm in alive:
        kind = KIND[nm]
        e = r[kind][nm]
        if not e['fail']: continue
        base = {'pred': nm, 'kind': kind, 'id': f"{seedname}|prof={','.join(map(str, prof))}", 'n': len(sets), 'm': m,
                'f': pd.f, 'sets': sets, 'vals': pd.vals}
        for x in e['fail']:
            if kind == 'single':
                out.append(dict(base, B=PF.masks_to_lists(pd.P[x]), k=PF.nearest(pd, x), frozen=[i for i in range(pd.n) if pd.F[x] >> i & 1],
                                **{'def': pd.d[x] if pd.d[x] != PF.INF else None}))
            else:
                NA, fz = x
                out.append(dict(base, NA=[g for g in range(64) if NA >> g & 1],
                                frozen={str(i): [g for g in range(64) if b >> g & 1] for i, b in enumerate(fz) if b >= 0},
                                **{'def': r['dstar'][x] if r['dstar'][x] != PF.INF else None},
                                nstates=sum(1 for q in range(len(pd.P)) if pd.key[q] == x)))
    return out


_NB = {}


def type_neighbours(D, K=12):
    """per type of a domain, the K nearest other types: Kendall distance between the orders of the subset sums"""
    gs = sorted(D[0])
    ck = tuple(tuple(d[g] for g in gs) for d in D)
    if ck not in _NB: _NB[ck] = _type_neighbours(D, gs, K)
    return _NB[ck]


def _type_neighbours(D, gs, K):
    subs = [[g for k, g in enumerate(gs) if S >> k & 1] for S in range(1, 1 << len(gs))]
    ranks = []
    for d in D:
        sums = [sum(d[g] for g in S) for S in subs]
        order = sorted(range(len(subs)), key=lambda a: sums[a])
        r = [0] * len(subs)
        for pos, a in enumerate(order): r[a] = pos
        ranks.append(r)
    L = len(subs)
    out = []
    for t, r in enumerate(ranks):
        ds = []
        for u, q in enumerate(ranks):
            if u == t: continue
            ds.append((sum(1 for a in range(L) for b in range(a + 1, L) if (r[a] < r[b]) != (q[a] < q[b])), u))
        ds.sort()
        out.append([u for _, u in ds[:K]])
    return out


def anneal(task):
    """one task: (tid, pred, mode, seed, seconds, batch, rng_seed, alive) -> result dict"""
    tid, pred, mode, seed, secs, batch, rs, alive = task
    rng = random.Random(rs)
    sets, m = seed['sets'], seed['m']
    doms = check4.core_domains(sets, m, False)
    n = len(sets)
    t0 = time.time()
    near = [type_neighbours(D) for D in doms]
    cur = tuple(seed['start'])
    res = evaluate_batch(sets, m, doms, [cur])
    cur_obj = objective(res[0][1], pred, mode) if res else (BIG, BIG)
    best, best_obj = cur, cur_obj
    steps = evals = stale = 0
    fails = []
    T = 1.0
    hist = collections.Counter()
    while time.time() - t0 < secs:
        steps += 1
        nb = set()
        while len(nb) < batch:
            p = list(cur)
            for i in rng.sample(range(n), 1 if rng.random() < 0.7 else 2):
                p[i] = rng.choice(near[i][p[i]]) if rng.random() < 0.6 else rng.randrange(len(doms[i]))
            nb.add(tuple(p))
        nb = list(nb)
        out = evaluate_batch(sets, m, doms, nb)
        evals += len(nb)
        scored = []
        for prof, r in out:
            fs = failures_in(r, alive, sets, m, prof, seed['name'])
            if fs: fails += fs
            scored.append((objective(r, pred, mode), rng.random(), prof))
        if fails: break
        if not scored:
            stale += 1
        else:
            o, _, prof = min(scored)
            if o <= cur_obj or rng.random() < T * 0.3:
                if o < cur_obj: stale = 0
                else: stale += 1
                cur, cur_obj = prof, o
            else:
                stale += 1
            if o < best_obj: best, best_obj = prof, o
        hist[cur_obj] += 1
        T *= 0.97
        if stale > 25:                                # restart: the seed, or the best so far
            cur = tuple(seed['start']) if rng.random() < 0.5 else best
            r0 = evaluate_batch(sets, m, doms, [cur])
            cur_obj = objective(r0[0][1], pred, mode) if r0 else (BIG, BIG)
            stale = 0; T = 1.0
    return {'tid': tid, 'pred': pred, 'mode': mode, 'seed': seed['name'], 'steps': steps, 'evals': evals,
            'best_obj': list(best_obj), 'best': list(best), 'fails': fails[:50], 'nfails': len(fails),
            'secs': round(time.time() - t0, 1)}


# ---------------- confirmation and reporting ----------------
def confirm(rec):
    """re-derive a failure with k4/portfolio_ref.py (c4x_check); returns (bool, text)"""
    import portfolio_ref as RF
    R = RF.Ref(rec['sets'], rec['vals'], rec['m'])
    sres, kres, dstar = R.evaluate([rec['pred']] if rec['kind'] == 'single' else [], [rec['pred']] if rec['kind'] == 'keyg' else [])
    if rec['kind'] == 'single':
        P = tuple(frozenset(b) for b in rec['B'])
        v = sres.get(P, {}).get(rec['pred'])
        d = R.dd.get(P)
        ok = v == 0 and (None if d == float('inf') else d) == rec['def']
        return ok, f"reference (c4x_check): state found {P in sres}, def {d}, {rec['pred']}-repairs {v}"
    k = (frozenset(rec['NA']), tuple(frozenset(rec['frozen'][str(i)]) if str(i) in rec['frozen'] else None for i in range(len(rec['sets']))))
    v = kres.get(k, {}).get(rec['pred'])
    return v == 0, f"reference (c4x_check): key found {k in kres}, def* {dstar.get(k)}, {rec['pred']}-edges to better keys {v}"


def write_failure(pred, recs, conf, push):
    path_md = os.path.join(OUT, f'FAILURES_{pred}.md')
    path_js = os.path.join(OUT, f'FAILURES_{pred}.jsonl')
    with open(path_js, 'w') as fo:
        for r in recs: fo.write(json.dumps(r, separators=(',', ':')) + '\n')
    r = min(recs, key=PF.fail_key)
    doc = {x[0]: x[1] for x in PR.SINGLE + PR.KEYG}
    L = [f'# {pred} fails ({"single-step form" if r["kind"] == "single" else "key-graph form"})', '',
         f'Predicate {pred}: {doc[pred]} (`k4/portfolio_preds.py`). Found by `k4/portfolio_hunt.py` (fast path: '
         '`k4/portfolio_dump.c` + `k4/portfolio_preds.py`); re-derived by `k4/portfolio_ref.py` (main\'s `k4/c4x_check.py`, '
         'independent of portfolio_dump.c, dlrt4.c and model.py). EVIDENCE: the hunt is adversarial search.', '',
         f'{len(recs)} failing {"states" if r["kind"] == "single" else "keys"} found in this batch; the smallest:', '',
         f'- instance `{r["id"]}`: n = {r["n"]}, m = {r["m"]}, f = {r["f"]}',
         f'- sets {r["sets"]}', f'- values {r["vals"]}']
    if r['kind'] == 'single':
        L.append(f'- state P = {r["B"]}, def(P) = {r["def"]}, frozen agents {r["frozen"]}, nearest distance {r["k"]}')
    else:
        L.append(f'- key NA = {r["NA"]}, frozen {r["frozen"]}, def* = {r["def"]} ({r["nstates"]} states)')
    L += ['', 'Confirmation:', ''] + [f'- `{x["id"]}`: {"CONFIRMED" if ok else "NOT CONFIRMED"} -- {t}' for x, (ok, t) in conf]
    L += ['', 'Reproduce: `python3 k4/portfolio_ref.py confirm` on the records of '
          f'`results/k4_portfolio/FAILURES_{pred}.jsonl` (gzip them first), or `python3 k4/portfolio.py inst` on '
          '{"id", "sets", "vals", "m"} built from a record.']
    open(path_md, 'w').write('\n'.join(L) + '\n')
    if push:
        subprocess.run(['git', 'add', path_md, path_js], cwd=os.path.join(HERE, '..'))
        subprocess.run(['git', 'commit', '-q', '-m', f'[compute/k4-portfolio] the hunt kills {pred}: {r["id"]} (n = {r["n"]}, m = {r["m"]}, f = {r["f"]})'
                        '\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n'
                        'Claude-Session: https://claude.ai/code/session_013o7KKdZBwSXM6r8XaRMoqF'], cwd=os.path.join(HERE, '..'))
        for k in range(4):
            if subprocess.run(['git', 'push', '-u', 'origin', 'compute/k4-portfolio'], cwd=os.path.join(HERE, '..')).returncode == 0: break
            time.sleep(2 ** (k + 1))


def report():
    """results/k4_portfolio/hunt_*.jsonl -> results/k4_portfolio/HUNT.md (per predicate and objective: tasks, profiles
    evaluated, the least objective reached, the seeds)"""
    rows = collections.defaultdict(lambda: {'tasks': 0, 'evals': 0, 'secs': 0.0, 'best': None, 'seeds': set(), 'n': set()})
    dead = {}
    files = sorted(f for f in os.listdir(OUT) if f.startswith('hunt_') and f.endswith('.jsonl'))
    for fn in files:
        for l in open(os.path.join(OUT, fn)):
            try: d = json.loads(l)
            except ValueError: continue
            if 'dead' in d: dead[d['dead']] = d['by']; continue
            e = rows[(d['pred'], d['mode'])]
            e['tasks'] += 1; e['evals'] += d['evals']; e['secs'] += d['secs']; e['seeds'].add(d['seed'].split(':')[0])
            b = tuple(d['best_obj'])
            if e['best'] is None or b < e['best']: e['best'] = b
    L = ['# The adversarial hunt (k4/portfolio_hunt.py)', '',
         'EVIDENCE only: adversarial search over strict profiles of fixed cores. Files: ' + ', '.join(f'`{f}`' for f in files) + '.',
         'Objective "count": the number of repairs (edges to better keys) at the worst state (key); "edge": (the number of '
         'repairs by the next stronger predicate INNER, the number by the predicate) at the worst state, '
         'lexicographic. 1000000 = no state (key) reached. A predicate dies when a task reaches 0 repairs; the failure is '
         're-derived by k4/portfolio_ref.py before it counts.', '',
         'Profiles generated: every neighbour is passed to portfolio_dump.c; those with an f >= 1 state are evaluated for '
         'every alive predicate.', '',
         '| predicate | objective | INNER | tasks | profiles generated | CPU s | least objective reached | seed kinds | dead |',
         '|---|---|---|---:|---:|---:|---|---|---|']
    order = {p: i for i, p in enumerate(ORDER)}
    for (p, mode), e in sorted(rows.items(), key=lambda kv: (order.get(kv[0][0], 99), kv[0][1])):
        L.append(f"| {p} | {mode} | {INNER.get(p, '-') if mode == 'edge' else '-'} | {e['tasks']} | {e['evals']:,} | {e['secs']:.0f} | "
                 f"{list(e['best'])} | {', '.join(sorted(e['seeds']))} | {dead.get(p, '')} |")
    tot = sum(e['evals'] for e in rows.values())
    L += ['', f'Total: {sum(e["tasks"] for e in rows.values())} tasks, {tot:,} profiles generated, '
          f'{sum(e["secs"] for e in rows.values()):.0f} CPU s; dead: {dead or "none"}.']
    open(os.path.join(OUT, 'HUNT.md'), 'w').write('\n'.join(L) + '\n')
    print('wrote results/k4_portfolio/HUNT.md')


def main():
    if sys.argv[1:2] == ['report']: return report()
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    name = opt.get('name', 'main')
    state = os.path.join(OUT, f'hunt_{name}.jsonl')
    print('# command: python3 k4/portfolio_hunt.py ' + ' '.join(sys.argv[1:]), flush=True)
    preds = opt['preds'].split(',') if 'preds' in opt else ORDER
    rounds, slot, jobs, batch = int(opt.get('rounds', 6)), float(opt.get('slot', 240)), int(opt.get('jobs', 2)), int(opt.get('batch', 24))
    done, dead = {}, set()
    if os.path.exists(state):
        for l in open(state):
            try: d = json.loads(l)
            except ValueError: continue
            if 'dead' in d: dead.add(d['dead'])
            else: done[d['tid']] = d
    srcs = opt.get('seeds', 'fail10,hard,rcores,ext').split(',')
    seeds = []
    for s in srcs:
        got = {'fail10': seeds_fail10, 'hard': seeds_hard, 'hard5': lambda: seeds_hard(12, 5), 'rcores': seeds_rcores,
               'ext': seeds_ext}[s]()
        print(f'# seeds {s}: {len(got)}', flush=True)
        seeds += got
    for sd in seeds:                                  # key-graph tasks only start from profiles with a key of def* > 0
        doms = check4.core_domains(sd['sets'], sd['m'], False)
        r0 = evaluate_batch(sd['sets'], sd['m'], doms, [tuple(sd['start'])])
        sd['haskeys'] = bool(r0) and r0[0][1]['keys_pos'] > 0
    kseeds = [sd for sd in seeds if sd['haskeys']] or seeds
    print(f'# {len(seeds)} seeds ({len(kseeds)} with a key of def* > 0); predicates {preds}; dead from the state file '
          f'{sorted(dead)}', flush=True)
    t0 = time.time()
    for rd in range(rounds):
        alive = [p for p in preds if p not in dead]
        if not alive: break
        tasks = []
        for j, p in enumerate(alive):
            for mode in ('count', 'edge'):
                pool = kseeds if KIND[p] == 'keyg' else seeds
                sd = pool[(rd * 7 + j * 3 + (mode == 'edge')) % len(pool)]
                tid = f'r{rd}:{p}:{mode}:{sd["name"]}'
                if tid in done: continue
                tasks.append((tid, p, mode, sd, slot, batch, zlib.crc32(tid.encode()), alive))
        print(f'# round {rd}: alive {alive}; {len(tasks)} tasks of {slot:.0f} s on {jobs} jobs [{time.time() - t0:.0f} s]', flush=True)
        with Pool(jobs) as pool:
            for res in pool.imap_unordered(anneal, tasks):
                print(f"  task {res['tid']}: steps {res['steps']} evals {res['evals']} best objective {res['best_obj']} "
                      f"fails {res['nfails']} [{res['secs']} s]", flush=True)
                newly = sorted(set(r['pred'] for r in res['fails']) - dead)
                for p in newly:
                    recs = [r for r in res['fails'] if r['pred'] == p]
                    conf = [(r, confirm(r)) for r in sorted(recs, key=PF.fail_key)[:3]]
                    ok = any(c[1][0] for c in conf)
                    print(f'  ** {p}: {len(recs)} failures, reference confirms: {[c[1] for c in conf]}', flush=True)
                    if ok:
                        dead.add(p)
                        write_failure(p, recs, [(r, c) for r, c in conf], 'push' in opt)
                        with open(state, 'a') as fo: fo.write(json.dumps({'dead': p, 'by': res['tid']}) + '\n')
                with open(state, 'a') as fo:
                    fo.write(json.dumps({k: v for k, v in res.items() if k != 'fails'}) + '\n')
    print(f'# done; dead {sorted(dead)}; alive {[p for p in preds if p not in dead]} [{time.time() - t0:.0f} s]', flush=True)


if __name__ == '__main__':
    main()
