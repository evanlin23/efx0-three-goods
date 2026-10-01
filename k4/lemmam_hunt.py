"""Phase 3 of the Lemma M portfolio: annealing hunts against the surviving candidates (k4/lemmam_portfolio.c -H).

For each candidate (round-robin, in the order given) and each core of the given certificate files (a seeded sample of
--cores of them), k4/lemmam_portfolio.c -HN -cK anneals the profile (one agent's type changed per step, sometimes two)
toward a profile where the candidate's agents are the only first agents in K0 ∪ K1 (score: number of allowed agents
satisfying the predicate, then the number of first agents in K0 ∪ K1), and stops at a failure (HFAIL). Seeds
(--seeds=FILE: profiles with sets=/vals=, mapped to the core's type indices by their order type) start the walks.
Every task is checkpointed (--checkpoint=CK) and skipped when rerun.

Usage: lemmam_hunt.py --cands=M_bt1,M_gapn,x2E,... FILE [FILE ...] [--cores=K] [--steps=N] [--restart=B] [--seed=S]
                      [--seeds=FILE] [--jobs=J] [--checkpoint=CK] [--out=JSON] [C options: -Y1]
Candidates are names of k4/lemmam_portfolio.c (CANDS) or partner variants (x1E, x2N, ...)."""
import gzip, itertools, json, os, random, re, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as AR
import check4
import lemmam_portfolio as LP


def type_key(vals):
    d = len(vals)
    sums = [sum(vals[g] for g in range(d) if S >> g & 1) for S in range(1, 1 << d)]
    order = sorted(set(sums))
    return tuple(order.index(s) for s in sums)


def seed_types(sets, m, vals):
    """type indices of the core's domains (k4/check4.core_domains, as encode_core) matching vals by order type"""
    doms = check4.core_domains(sets, m, False)
    ty = []
    for S, dom, V in zip(sets, doms, vals):
        k = type_key(V)
        idx = next((t for t, dv in enumerate(dom) if type_key([dv[g] for g in S]) == k), None)
        if idx is None: return None
        ty.append(idx)
    return ty


def cand_index(c):
    if c in LP.CANDS: return LP.CANDS.index(c)
    return 100 + LP.VARS.index(c)


def main():
    args = sys.argv[1:]
    opt = lambda name, dflt=None: next((a.split('=', 1)[1] for a in args if a.startswith(f'--{name}=')), dflt)
    cands = opt('cands').split(',')
    files = [a for a in args if not a.startswith('-')]
    ncores = int(opt('cores', 50)); steps = int(opt('steps', 20000)); rs = int(opt('restart', 3000))
    seed = int(opt('seed', 1)); jobs = int(opt('jobs', os.cpu_count())); ck = opt('checkpoint'); out = opt('out')
    copts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    LP.build()
    print('#', 'lemmam_hunt.py', ' '.join(args), '# source sha', LP.SHA, flush=True)
    rng = random.Random(seed)
    cores = []
    for f in files:
        data = json.load(gzip.open(f, 'rt'))
        idx = list(range(len(data['cores'])))
        rng.shuffle(idx)
        for i in idx[:ncores]: cores.append((os.path.basename(f), i, data['cores'][i]['sets'], data['cores'][i]['m'], None))
    if opt('seeds'):
        for j, (sets, vals) in enumerate(AR.load_profiles(opt('seeds'))):
            m = 1 + max(g for S in sets for g in S)
            ty = seed_types(sets, m, vals)
            if ty is None: print(f'# seed {j}: no matching types, skipped', flush=True); continue
            cores.append((f"seed:{os.path.basename(opt('seeds'))}", j, sets, m, ty))
    okey = ' '.join(copts) + f' H{steps} B{rs} s{seed} ' + LP.SHA
    tasks = []
    for c in cands:                                   # round-robin: every candidate on the same cores
        for name, i, sets, m, ty in cores:
            o = copts + [f'-H{steps}', f'-c{cand_index(c)}', f'-B{rs}', f'-X{seed * 7919 + i}', '-f2']
            if ty is not None: o.append('-I' + ','.join(map(str, ty)))
            tasks.append((f'hunt {c} {name} {i} {okey}', AR.encode_core(sets, m), o))
    # interleave candidates so that each gets time early (round-robin)
    per = {}
    for t in tasks: per.setdefault(t[0].split()[1], []).append(t)
    tasks = [t for grp in itertools.zip_longest(*per.values()) for t in grp if t]
    print(f'# {len(tasks)} tasks ({len(cands)} candidates x {len(cores)} cores/seeds), {jobs} workers', flush=True)
    done = LP.load_ck(ck, '')
    todo = [t for t in tasks if t[0] not in done]
    fc = open(ck, 'a') if ck else None
    res = {c: {'tasks': 0, 'fails': [], 'tight': [], 'best': None} for c in cands}

    def take(key, fl):
        c = key.split()[1]
        r = res[c]; r['tasks'] += 1
        for l in fl:
            if l.startswith('HFAIL'): r['fails'].append(l)
            elif l.startswith('HTIGHT') and len(r['tight']) < 50: r['tight'].append(l)
            elif l.startswith('HDONE'):
                b = int(re.search(r'best=(-?\d+)', l).group(1))
                r['best'] = b if r['best'] is None else min(r['best'], b)
    for t in tasks:
        if t[0] in done: take(t[0], done[t[0]]['fl'])
    t0 = time.time(); nd = 0
    with Pool(jobs) as pool:
        for key, pm, lv, fl, dt in pool.imap_unordered(LP.run, todo):
            nd += 1
            take(key, fl)
            for l in fl:
                if l.startswith('HFAIL'): print('!!', key.split()[1], l[:1500], flush=True)
            if fc: fc.write(json.dumps({'key': key, 'pm': pm, 'lv': lv, 'fl': fl, 'time': dt}) + '\n'); fc.flush()
            if nd % max(1, len(todo) // 25) == 0: print(f'# {nd}/{len(todo)} tasks, {time.time() - t0:.0f}s', flush=True)
    if fc: fc.close()
    summ = {}
    for c in cands:
        r = res[c]
        fs = sorted(r['fails'], key=LP.prof_key)
        summ[c] = {'tasks': r['tasks'], 'failures': len(fs), 'smallest': fs[0] if fs else None,
                   'best_score': r['best'], 'tight_examples': r['tight'][:5]}
        print(f"== {c}: tasks {r['tasks']}, failures {len(fs)}, best score {r['best']}" +
              (f"\n   smallest: {fs[0][:1500]}" if fs else ''), flush=True)
    if out: json.dump({'args': args, 'sha': LP.SHA, 'results': summ, 'all_fails': {c: res[c]['fails'] for c in cands}}, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
