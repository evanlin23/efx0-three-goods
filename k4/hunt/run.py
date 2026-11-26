"""Run the CEGAR of cegar.py on a class of k = 4 cores (search4.cores: genbg, one per isomorphism class).

Usage: run.py n m --n4=K [--pure] [--jobs=J] [--tries=T] [--part=i/k] [--sample=N --seed=S] [--limit=SEC] [--tag=NAME]
Writes one JSON line per core to k4/hunt/ckpt/<tag>.jsonl (resumable) and, when every core of the selection is done,
results/k4_hunt/<tag>.json.gz (the certificate: per core the sets, status and the allocations used)."""
import sys, os, json, gzip, time, random
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import search4 as S4
import cegar

OPT = {}
DIG = '0123456789abcdefghijklmnopqrstuvwxyz'

def enc(A):
    return ''.join(DIG[j] for j in A)

def solve(task):
    idx, sets, m = task
    t0 = time.time()
    H = cegar.Hunt(sets, m, tries=int(OPT.get('tries', 2)))
    st = H.run(cap=1, time_limit=float(OPT['limit']) if 'limit' in OPT else None)
    rec = {'idx': idx, 'm': m, 'sets': sets, 'status': st, 'time': round(time.time() - t0, 2), **H.stats(),
           'alloc_list': H.cert}
    if H.fails:
        rec['fails'] = [[list(H.dom[i][t]) for i, t in enumerate(p)] for p in H.fails]
    return rec

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    OPT.update(dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--')))
    n, m = int(args[0]), int(args[1])
    pure = 'pure' in OPT
    n4 = int(OPT['n4']) if 'n4' in OPT else None
    cs = S4.cores(n, m, pure, n4)
    tasks = [(idx, sets, m) for idx, sets in enumerate(cs)]
    if 'sample' in OPT:
        random.Random(int(OPT.get('seed', 1))).shuffle(tasks); tasks = sorted(tasks[:int(OPT['sample'])])
    part, parts = map(int, OPT.get('part', '0/1').split('/'))
    tasks = [t for k, t in enumerate(tasks) if k % parts == part]
    tag = OPT.get('tag', f"n{n}_m{m}_n4{n4 if n4 is not None else 'any'}{'_pure' if pure else ''}")
    os.makedirs(os.path.join(HERE, 'ckpt'), exist_ok=True)
    ck = os.path.join(HERE, 'ckpt', f'{tag}_p{part}of{parts}.jsonl')
    done = {}
    if os.path.exists(ck):
        for line in open(ck):
            try: r = json.loads(line); done[r['idx']] = r
            except json.JSONDecodeError: pass
    todo = [t for t in tasks if t[0] not in done]
    print(f"command: python3 k4/hunt/run.py {' '.join(sys.argv[1:])}", flush=True)
    print(f"n={n} m={m} n4={n4} pure={pure}: {len(cs)} cores in class, {len(tasks)} selected, {len(done)} done", flush=True)
    t0 = time.time(); cnt = 0
    with Pool(int(OPT.get('jobs', os.cpu_count()))) as pool, open(ck, 'a') as f:
        for rec in pool.imap_unordered(solve, todo, chunksize=4):
            f.write(json.dumps(rec, separators=(',', ':')) + '\n'); f.flush()
            done[rec['idx']] = rec; cnt += 1
            if rec['status'] != 'certified':
                print(f"  {rec['status'].upper()}: idx={rec['idx']} sets={rec['sets']} {rec.get('fails', '')}", flush=True)
            if cnt % 500 == 0: print(f"  ... {cnt}/{len(todo)} [{time.time() - t0:.0f}s]", flush=True)
    recs = [done[t[0]] for t in tasks]
    from collections import Counter
    print(f"  status: {dict(Counter(r['status'] for r in recs))}", flush=True)
    top = sorted(recs, key=lambda r: -r['allocs'])[:5]
    for r in top: print(f"  most allocations: {r['allocs']} idx={r['idx']} t={r['time']}s sets={r['sets']}", flush=True)
    print(f"  total core time {sum(r['time'] for r in recs):.0f}s, wall {time.time() - t0:.0f}s", flush=True)
    if len(recs) == len(tasks):
        os.makedirs(os.path.join(os.path.dirname(os.path.dirname(HERE)), 'results', 'k4_hunt'), exist_ok=True)
        path = os.path.join(os.path.dirname(os.path.dirname(HERE)), 'results', 'k4_hunt', f'{tag}_p{part}of{parts}.json.gz')
        with gzip.open(path, 'wt') as f:
            json.dump({'n': n, 'm': m, 'n4': n4, 'pure': pure, 'class_size': len(cs), 'selection': OPT.get('sample', 'all'),
                       'seed': OPT.get('seed'), 'part': [part, parts],
                       'alloc_format': 'base36 string, one character per good (its owner)',
                       'cores': [{'idx': r['idx'], 'sets': r['sets'], 'status': r['status'],
                                  'allocs': [enc(A) for A in r['alloc_list']]} for r in recs]}, f, separators=(',', ':'))
        print(f"  wrote {path}", flush=True)

if __name__ == '__main__':
    main()
