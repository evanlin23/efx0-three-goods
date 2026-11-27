"""Run cegar.py on named cores (every strict balanced profile of each), with a time limit per core.

Usage: named.py SET [--limit=SEC] [--tries=T] [--out=results/k4_hunt/named_SET.json.gz]
SET = mc7 (the 6 graphical all-P4 cores of K4.MC7, k4/MINCEX.md §8), or a JSON file with a list of
{"name", "sets"} records."""
import sys, os, json, gzip, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import cegar

MC7 = [
    [[0, 1, 2, 9], [0, 4, 8, 10], [1, 5, 7, 11], [2, 6, 8, 12], [3, 4, 6, 13], [3, 5, 7, 14]],
    [[0, 1, 2, 9], [0, 2, 8, 10], [1, 4, 7, 11], [3, 5, 6, 12], [3, 6, 8, 13], [4, 5, 7, 14]],
    [[0, 1, 6, 9], [0, 4, 7, 10], [1, 4, 7, 11], [2, 3, 6, 12], [2, 5, 8, 13], [3, 5, 8, 14]],
    [[0, 1, 6, 9], [0, 4, 7, 10], [1, 5, 7, 11], [2, 3, 6, 12], [2, 4, 8, 13], [3, 5, 8, 14]],
    [[0, 1, 6, 9], [0, 4, 8, 10], [1, 5, 7, 11], [2, 3, 6, 12], [2, 4, 7, 13], [3, 5, 8, 14]],
    [[0, 1, 6, 9], [0, 4, 6, 10], [1, 5, 7, 11], [2, 3, 8, 12], [2, 4, 7, 13], [3, 5, 8, 14]],
]

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    src = args[0]
    items = [(f'MC7-{k + 1}', s) for k, s in enumerate(MC7)] if src == 'mc7' else \
        [(r['name'], r['sets']) for r in json.load(open(src))]
    print('command: python3 k4/hunt/named.py ' + ' '.join(sys.argv[1:]), flush=True)
    out = []
    for name, sets in items:
        m = 1 + max(g for S in sets for g in S)
        t0 = time.time()
        H = cegar.Hunt(sets, m, tries=int(opt.get('tries', 2)), per_profile='per-profile' in opt)
        st = H.run(cap=1, time_limit=float(opt.get('limit', 3600)))
        rec = {'name': name, 'n': len(sets), 'm': m, 'sets': sets, 'status': st, 'time': round(time.time() - t0, 1),
               **H.stats(), 'allocs_list': H.cert}
        if H.fails: rec['fails'] = [[list(H.dom[i][t]) for i, t in enumerate(p)] for p in H.fails]
        print(f"{name}: n={len(sets)} m={m} {st} in {rec['time']}s, {H.stats()}" + (f" FAIL {rec['fails']}" if H.fails else ''), flush=True)
        out.append(rec)
    path = opt.get('out', os.path.join(ROOT, 'results', 'k4_hunt', f"named_{os.path.basename(src).split('.')[0]}.json.gz"))
    with gzip.open(path, 'wt') as f:
        json.dump({'set': src, 'cores': [{'name': r['name'], 'n': r['n'], 'm': r['m'], 'sets': r['sets'], 'status': r['status'],
                                          'allocs': r['allocs_list']} for r in out]}, f, separators=(',', ':'))
    print('wrote', path, flush=True)

if __name__ == '__main__':
    main()
