"""Distinct profiles behind the neighbourhood runs of k4/gm4_run.py --around (k4/gm4.md §6).  The neighbourhoods of
different seeds overlap, so the run counts (TOTAL runs=, pfail=) count some profiles several times.
Usage: gm4_distinct.py searched SEEDFILE K [TAG]   distinct profiles among all runs of --around=SEEDFILE --vary=K
                                                   (seeds: the TAG lines, default GMFAIL, deduplicated as --around does)
       gm4_distinct.py bad LOG [LOG ...] [--tag=T]  distinct profiles among the T lines (default GMFAIL) of the logs
       gm4_distinct.py closure SEEDFILE LOG [...]  are the distinct GMFAIL profiles of the logs exactly those of SEEDFILE?
       gm4_distinct.py union SEEDFILE:K[:TAG] ...   distinct profiles in the union of several such searches
A profile is (core, type of each agent); types are indexed in k4/check4.py's core_domains order."""
import itertools, json, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains

def lines(files, tag):
    for f in files:
        for line in open(f):
            if line.startswith(tag + ' '):
                body, meta = line.split(' # ')
                vals = [tuple(map(int, t.split(','))) for t in body.split(' | ')[0].split()[1:]]
                m = int(meta.split()[0][2:]); sets = json.loads(meta.split('sets=')[1])
                yield m, sets, vals

def distinct(files, tag):
    return {(json.dumps(sets), tuple(vals)) for m, sets, vals in lines(files, tag)}

def searched(seedfile, K, tag, codes=False):
    seen, cores, chunks, runs = set(), {}, [], 0
    B = 300
    for m, sets, vals in lines([seedfile], tag):
        key = (json.dumps(sets), tuple(vals))
        if key in seen: continue
        seen.add(key)
        doms = core_domains(sets, m, False)
        dv = [[tuple(d[g] for g in S) for d in D] for S, D in zip(sets, doms)]
        idx = [dv[i].index(vals[i]) for i in range(len(sets))]
        cid = cores.setdefault(json.dumps(sets), len(cores))
        n = len(sets)
        for A in itertools.combinations(range(n), K):
            axes = [np.arange(len(dv[i]), dtype=np.int64) if i in A else np.array([idx[i]], dtype=np.int64) for i in range(n)]
            code = np.full(1, cid, dtype=np.int64)
            for ax in axes: code = (code[:, None] * B + ax[None, :]).ravel()
            chunks.append(code); runs += code.size
    allc = np.unique(np.concatenate(chunks))
    return (len(seen), runs, allc) if codes else (len(seen), runs, allc.size)

def main():
    mode = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    args = [a for a in sys.argv[2:] if not a.startswith('--')]
    if mode == 'searched':
        s, r, d = searched(args[0], int(args[1]), args[2] if len(args) > 2 else 'GMFAIL')
        print(f"searched {args[0]} K={args[1]}: seeds={s} runs={r} distinct_profiles={d}")
    elif mode == 'union':
        parts, runs = [], 0
        for spec in args:
            f, K, *t = spec.split(':')
            _, r, c = searched(f, int(K), t[0] if t else 'GMFAIL', codes=True); parts.append(c); runs += r
        print(f"union {' '.join(args)}: runs={runs} distinct_profiles={np.unique(np.concatenate(parts)).size}")
    elif mode == 'bad':
        tag = opt.get('tag', 'GMFAIL')
        print(f"bad {' '.join(args)} tag={tag}: distinct_profiles={len(distinct(args, tag))}")
    elif mode == 'closure':
        s, b = distinct([args[0]], 'GMFAIL'), distinct(args[1:], 'GMFAIL')
        print(f"closure {args[0]} vs {' '.join(args[1:])}: seeds={len(s)} found={len(b)} found_minus_seeds={len(b - s)} seeds_minus_found={len(s - b)}")

if __name__ == '__main__':
    main()
