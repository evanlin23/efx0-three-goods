"""Shrink certificates: keep only the allocations in an UNSAT core of the outer formula.

For one core, the outer formula of cegar.py (one type per agent; per allocation "not EFX₀") is rebuilt from the
certificate's allocations with a selector literal per allocation clause, solved under all selectors, and the
allocations whose selectors are in the returned core are kept (repeated while the core shrinks, up to 3 rounds).
The result must be re-checked (k4/hunt/check.py); this script does not certify anything by itself.
Usage: compact.py IN.jsonl|IN.json.gz OUT.json.gz [--jobs=J]   (run.py checkpoints/certificates or run_mc.py output)"""
import sys, os, json, gzip
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import cegar
DIG = '0123456789abcdefghijklmnopqrstuvwxyz'

def shrink(task):
    sets, m, allocs, domains = task
    keep = list(allocs)
    for _ in range(3):
        H = cegar.Hunt(sets, m, domains=domains, use_aut=False)
        sel = []
        for A in keep:
            s = H.vp.id(('sel', len(sel))); sel.append(s)
            H.out.add_clause(H.clause(A) + [-s])
        if H.out.solve(assumptions=sel): return None             # not a certificate at all
        core = set(H.out.get_core() or sel)
        new = [A for A, s in zip(keep, sel) if s in core]
        if len(new) == len(keep): break
        keep = new
    return keep

def main():
    src, dst = [a for a in sys.argv[1:] if not a.startswith('--')][:2]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    if src.endswith('.jsonl'):
        recs = [json.loads(l) for l in open(src)]
        meta = None
    else:
        d = json.load(gzip.open(src, 'rt')); meta = d if isinstance(d, dict) else None
        recs = d['cores'] if isinstance(d, dict) else d
    for r in recs:
        A = r.get('alloc_list', r.get('allocs'))
        r['allocs'] = [[int(ch, 36) for ch in a] if isinstance(a, str) else a for a in A]
    tasks = [(r['sets'], r.get('m') or meta['m'], r['allocs'], r.get('domains')) for r in recs]
    with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
        res = pool.map(shrink, tasks, chunksize=16)
    before = sum(len(r['allocs']) for r in recs); after = 0
    for r, k in zip(recs, res):
        if k is None: print('NOT A CERTIFICATE', r['sets']); sys.exit(1)
        r['allocs'] = [''.join(DIG[j] for j in A) for A in k]; after += len(k)
        r.pop('alloc_list', None)
    print(f'{len(recs)} cores: {before} allocations -> {after}', flush=True)
    out = dict(meta, cores=recs) if meta else recs
    if meta: out['alloc_format'] = 'base36 string, one character per good (its owner)'
    json.dump(out, gzip.open(dst, 'wt'), separators=(',', ':'))

if __name__ == '__main__':
    main()
