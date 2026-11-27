"""Batch runner: OC1^max for every strict profile of every core hypergraph in a k = 4 core list (results/k4_certs_*.json.gz,
written by k4/search4.py), by the ordinal CEGAR of k4/oc1cert/cegar.py.

    python3 k4/oc1cert/run.py LIST[,LIST...] --out=results/k4_oc1max/cert_<tag>.json.gz [--jobs=4] [--stride=S --offset=O]
           [--limit=SEC] [--no-compact] [--depth=D] [--idx=I,J,...] [--summary=S.jsonl.gz]
An --out ending in .jsonl.gz is written as one JSON record per line (header line first) while the run goes.
--depth=D: up to D moves in sequence (OC_D form; default 1 = OC1^max).  --prime: OC1' moves (kgen/rounds.md §4.6).  --sstar: S*-shaped completions (k4/oc1_hall.md §2).
--r2=m|star|o|og|op|c|e|e2|eo|s|l|sl: TTC's R2-M / R2* / R2-O (strict, generous, R2-O') / R2-C / R2-E (k4/ttc.md §14.6): at every perfect start with >= 2 receivers, a one-absorber completion
of the picks, or a canonical chain to a receiver with the R2-M (owner x0, every agent <= 1 junk, multi-good holders
other than x0 none) or R2* (every agent <= 1 junk) completion.  --idx: only these core indices (within m).

LIST is a name like 2, 3, 4_n4_1, 5_pure (results/k4_certs_<LIST>.json.gz).  A hypergraph whose outer loop finds a
(profile, picks) pair with no witness is re-checked at once with the raw checker k4/sdc/oc1_mc2_rand.Inst (its SD picks
over every order, its moves, its brute-force one-absorber completion) and printed as OC1MAX CANDIDATE FAILURE."""
import sys, os, gzip, json, time, itertools, collections, multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from cegar import Cert


def raw_check(sets, vals, picks, depth=1):
    """The raw checker k4/sdc/oc1_mc2_rand.Inst on (vals, picks); with depth 2 also whether some state two moves
    away (Inst.moves twice) has a one-absorber completion (Inst.one_absorber)."""
    from oc1_mc2_rand import Inst
    I = Inst(sets, vals)
    orders = [o for o in itertools.permutations(range(I.n)) if I.sd(o) == tuple(picks)]
    res = {'orders_giving_picks': len(orders), 'raw': I.check(tuple(picks))}
    if depth >= 2 and res['raw'] == 'OC1 fails':
        base = [[p] if p is not None else [] for p in picks]
        two = set(s2 for s in I.moves(base) for s2 in I.moves([list(b) for b in s]))
        res['raw_two_moves'] = 'two moves repair' if any(I.one_absorber([list(b) for b in s]) for s in two) else 'two moves fail'
    return res


def job(task):
    lst, idx, sets, limit, compact, depth = task[:6]
    prime = len(task) > 6 and task[6]
    sstar = len(task) > 7 and task[7]
    r2 = task[8] if len(task) > 8 else None
    t0 = time.time()
    C = Cert(sets, depth=depth, prime=prime, sstar=sstar, r2=r2)
    if r2 and C.nu < C.n:     # R2 is about perfect starts
        return {'list': lst, 'idx': idx, 'sets': sets, 'm': C.m, 'nu': C.nu, 'domains': [len(D) for D in C.dom],
                'result': 'certified', 'note': 'no perfect start (nu < n): vacuous', 'stats': {'iters': 0, 'kinds': {}},
                'witnesses': [], 'time': 0}
    r = C.run(time_limit=limit)
    rec = {'list': lst, 'idx': idx, 'sets': sets, 'm': C.m, 'nu': C.nu, 'domains': [len(D) for D in C.dom],
           'result': r, 'stats': C.stats(), 'time': round(time.time() - t0, 3)}
    if C.oc1_fails:      # pairs where one move did not suffice (only with --depth >= 2): OC1^max fails there
        rec['oc1_fails'] = []
        for prof, Y in C.oc1_fails[:3]:
            vals = [list(C.dom[i][t]) for i, t in enumerate(prof)]
            rec['oc1_fails'].append({'vals': vals, 'picks': list(Y), 'raw_check': raw_check(sets, vals, Y)})
        rec['n_oc1_fail_pairs_met'] = len(C.oc1_fails)
    if r == 'certified':
        W = C.compact() if compact else C.witnesses
        rec['witnesses'] = [w.to_json() for w in W]
        rec['n_witnesses_before_compaction'] = len(C.witnesses)
    elif r == 'FAIL':
        rec['fails'] = []
        for prof, Y in C.fails:
            vals = [list(C.dom[i][t]) for i, t in enumerate(prof)]
            rec['fails'].append({'vals': vals, 'picks': list(Y), 'raw_check': raw_check(sets, vals, Y, depth)})
    rec['time'] = round(time.time() - t0, 3)
    return rec


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], '1') for a in sys.argv[1:] if a.startswith('--'))
    lists = args[0].split(',')
    out = opt.get('out'); jobs = int(opt.get('jobs', mp.cpu_count()))
    stride, offset = int(opt.get('stride', 1)), int(opt.get('offset', 0))
    limit = float(opt['limit']) if 'limit' in opt else None
    compact = 'no-compact' not in opt
    depth = int(opt.get('depth', 1))
    idxs = set(map(int, opt['idx'].split(','))) if 'idx' in opt else None
    print('$ python3 k4/oc1cert/run.py', *sys.argv[1:], flush=True)
    tasks = []
    for lst in lists:
        d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_%s.json.gz' % lst)))
        for c in d['cores'][offset::stride]:
            if idxs is not None and (lst, c['idx']) not in idxs and c['idx'] not in idxs: continue
            tasks.append((lst, c['idx'], c['sets'], limit, compact, depth, 'prime' in opt, 'sstar' in opt, opt.get('r2')))
    print('hypergraphs', len(tasks), 'jobs', jobs, flush=True)
    t0 = time.time(); T = collections.Counter(); recs = []; tmax = (0, None)
    header = {'statement': 'OC1^max (K4.SDC.OC1MAX) for every strict profile: for every type profile and every '
                           'SD order whose picks form a maximum matching, the picks have a one-absorber EFX0 '
                           'completion or at most DEPTH official moves (addition, chain, ring) give bases that '
                           'have one (DEPTH = 1 is OC1^max)', 'depth': depth,
              'generator': 'k4/oc1cert/cegar.py', 'lists': lists, 'stride': stride, 'offset': offset,
              'moves': "OC1' (kgen/rounds.md §4.6: non-end chain agents may take goods of the end's base)" if 'prime' in opt else 'official',
              'completion': 'S* (k4/oc1_hall.md §2)' if 'sstar' in opt else 'one absorber',
              'r2': opt.get('r2')}
    stream = out and out.endswith('.jsonl.gz')     # one JSON record per line (header first), not kept in memory
    summary = opt.get('summary')                   # optional: the records without witnesses, as JSON lines
    if stream:
        os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
        fout = gzip.open(out, 'wt'); fout.write(json.dumps(header) + '\n')
    fsum = gzip.open(summary, 'wt') if summary else None
    with mp.Pool(jobs) as pool:
        for k, rec in enumerate(pool.imap_unordered(job, tasks, chunksize=1 if len(tasks) < 200 else 4)):
            if stream: fout.write(json.dumps(rec) + '\n')
            else: recs.append(rec)
            if fsum: fsum.write(json.dumps({x: rec[x] for x in rec if x != 'witnesses'} | {'n_witnesses': len(rec.get('witnesses', []))}) + '\n')
            T['result %s' % rec['result']] += 1
            T['%s nu=%d n=%d' % (rec['list'], rec['nu'], len(rec['sets']))] += 1
            for kd, c in rec['stats']['kinds'].items(): T['witness kind %s (found by the inner)' % kd] += c
            T['iterations'] += rec['stats']['iters']
            T['witnesses kept'] += len(rec.get('witnesses', []))
            if rec['time'] > tmax[0]: tmax = (rec['time'], (rec['list'], rec['idx']))
            if rec['result'] != 'certified':
                print('NOT CERTIFIED', json.dumps({x: rec[x] for x in rec if x != 'witnesses'}), flush=True)
                for f in rec.get('fails', []):
                    if f['raw_check']['raw'] == 'OC1 fails' and f['raw_check']['orders_giving_picks'] > 0:
                        print('OC1MAX CANDIDATE FAILURE (raw checker agrees)', json.dumps({'sets': rec['sets'], **f}), flush=True)
            if rec.get('oc1_fails'):
                T['hypergraphs where OC1^max fails (one move not enough for some profile)'] += 1
                for f in rec['oc1_fails']:
                    T['OC1^max failures raw-checked: %s' % f['raw_check']['raw']] += 1
                print('OC1MAX FAILS (raw: %s)' % rec['oc1_fails'][0]['raw_check']['raw'],
                      json.dumps({'list': rec['list'], 'idx': rec['idx'], 'sets': rec['sets'], **rec['oc1_fails'][0]}), flush=True)
            if (k + 1) % 500 == 0:
                print('... %d hypergraphs, %.0f s' % (k + 1, time.time() - t0), flush=True)
    recs.sort(key=lambda r: (r['list'], r['idx']))
    for key in sorted(T): print(key, T[key])
    print('slowest hypergraph %.2f s %s' % tmax)
    print('time %.0f s' % (time.time() - t0))
    if fsum: fsum.close()
    if stream:
        fout.close(); print('wrote', out)
    elif out:
        os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
        with gzip.open(out, 'wt') as f:
            json.dump({**header, 'cores': recs}, f)
        print('wrote', out)


if __name__ == '__main__':
    main()
