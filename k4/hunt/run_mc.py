"""Run cegar.py on a list of candidate cores with restricted type domains (k4/hunt/mc_n.py or k4/mincex_shapes.py
output: records with n, m, sets, domains).

Usage: run_mc.py CANDIDATES.json.gz --tag=NAME [--jobs=J] [--limit=SEC] [--tries=T]
Checkpoint k4/hunt/ckpt/NAME.jsonl (resumable); certificate results/k4_hunt/NAME.json.gz (a list of records n, m,
sets, status, allocs: the format k4/check_mincex_cores4.py's check_one reads) once every candidate is done."""
import sys, os, json, gzip, time, collections
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import cegar

OPT = {}

FAIL = None

def domains_of(r):
    """The record's cut domains: stored, or recomputed with mincex_shapes.restricted_domains."""
    global FAIL
    if 'domains' in r: return r['domains']
    import pickle
    cwd = os.getcwd(); os.chdir(os.path.dirname(HERE))
    import mincex_shapes as MS
    if FAIL is None: FAIL = pickle.load(open(os.path.join(HERE, 'ckpt', 'px_uncovered.pkl'), 'rb'))
    dom, kinds, rules = MS.restricted_domains(r['sets'], r['m'], FAIL)
    os.chdir(cwd)
    assert [len(d) for d in dom] == r.get('dsizes', [len(d) for d in dom])
    return dom

def solve(task):
    k, r = task
    t0 = time.time()
    H = cegar.Hunt(r['sets'], r['m'], domains=domains_of(r), tries=int(OPT.get('tries', 2)))
    st = H.run(cap=1, time_limit=float(OPT['limit']) if 'limit' in OPT else None)
    out = {'k': k, 'n': r['n'], 'm': r['m'], 'beta': r.get('beta'), 'sets': r['sets'], 'kinds': r.get('kinds'),
           'profiles': r.get('profiles'), 'status': st, 'time': round(time.time() - t0, 2), **H.stats(), 'allocs': H.cert}
    if H.fails: out['fails'] = [[list(H.dom[i][t]) for i, t in enumerate(p)] for p in H.fails]
    return out

def main():
    src = [a for a in sys.argv[1:] if not a.startswith('--')][0]
    OPT.update(dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--')))
    cand = json.load(gzip.open(src, 'rt'))
    tag = OPT['tag']
    os.makedirs(os.path.join(HERE, 'ckpt'), exist_ok=True)
    ck = os.path.join(HERE, 'ckpt', f'{tag}.jsonl')
    done = {}
    if os.path.exists(ck):
        for line in open(ck):
            try: r = json.loads(line); done[r['k']] = r
            except json.JSONDecodeError: pass
    order = sorted(range(len(cand)), key=lambda k: cand[k].get('profiles', 0))       # small ones first
    todo = [(k, cand[k]) for k in order if k not in done]
    print(f"command: python3 k4/hunt/run_mc.py {' '.join(sys.argv[1:])}", flush=True)
    print(f"{len(cand)} candidates, {len(done)} done", flush=True)
    t0, cnt = time.time(), 0
    with Pool(int(OPT.get('jobs', os.cpu_count()))) as pool, open(ck, 'a') as f:
        for rec in pool.imap_unordered(solve, todo, chunksize=1):
            f.write(json.dumps(rec, separators=(',', ':')) + '\n'); f.flush()
            done[rec['k']] = rec; cnt += 1
            if rec['status'] != 'certified':
                print(f"  {rec['status'].upper()}: n={rec['n']} m={rec['m']} {''.join(rec['kinds'] or [])} {rec['sets']} "
                      f"{rec.get('fails', '')}", flush=True)
            if cnt % 200 == 0: print(f"  ... {cnt}/{len(todo)} [{time.time() - t0:.0f}s]", flush=True)
    recs = [done[k] for k in range(len(cand)) if k in done]
    st = collections.Counter(r['status'] for r in recs)
    print(f"  status: {dict(st)}", flush=True)
    by = collections.defaultdict(list)
    for r in recs: by[(r['beta'], r['m'])].append(r)
    for key in sorted(by, key=lambda x: (x[0] or 0, x[1])):
        rs = by[key]
        print(f"  beta={key[0]} m={key[1]}: {len(rs)} cores, {sum(r['status'] == 'certified' for r in rs)} certified, "
              f"max time {max(r['time'] for r in rs)}s, max allocs {max(r['allocs'] if isinstance(r['allocs'], int) else len(r['allocs']) for r in rs)}", flush=True)
    for r in sorted(recs, key=lambda r: -r['time'])[:5]:
        print(f"  slowest: {r['time']}s n={r['n']} m={r['m']} {''.join(r['kinds'] or [])} profiles={r['profiles']} {r['sets']}", flush=True)
    print(f"  total core time {sum(r['time'] for r in recs):.0f}s, wall {time.time() - t0:.0f}s", flush=True)
    if len(recs) == len(cand):
        path = os.path.join(ROOT, 'results', 'k4_hunt', f'cert_{tag}.json.gz')
        with gzip.open(path, 'wt') as f:
            json.dump([{'n': r['n'], 'm': r['m'], 'beta': r['beta'], 'sets': r['sets'], 'status': r['status'],
                        'allocs': r['allocs']} for r in recs], f, separators=(',', ':'))
        print(f"  wrote {path}", flush=True)

if __name__ == '__main__':
    main()
