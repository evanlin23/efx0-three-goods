#!/usr/bin/env python3
"""Chains, cycles and stars of tight gadgets (k4/c4min_hunt.md §4.3), checked with the SAT encoding k4/c4min_sat.py.

Gadgets: the profiles of a climber dump (k4/c4min_climb.py --dump) where an owner is needed and d* = 0 (no slack at
all), each a small core with its profile. A composite takes L gadgets (random, with repetition), relabels their goods
apart, and joins them along a path, a cycle or a star; each join is either a shared good (a random good of one
identified with a random good of the other; types unchanged) or a connector agent {a, b, p, q} (p, q private) with a
random strict type. Only composites that are k = 4 cores are kept. One owner must then serve every gadget: the
question is whether gadgets whose own junk leaves no slack can overload it.

usage: c4min_chains.py DUMP.jsonl [--count=N] [--lengths=2,3,4,5] [--seed=S] [--jobs=J]"""
import json, os, random, sys, time
from concurrent.futures import ProcessPoolExecutor
import c4min_common as cc
import c4min_families as F
import c4min_sat
from c4min_climb import parse_profile


def load_gadgets(dump):
    lists, out = {}, []
    for l in open(dump):
        r = json.loads(l)
        if not (r['owner'] and r['dstar'] == 0): continue
        if r['file'] not in lists: lists[r['file']] = cc.load_cores(os.path.join(cc.ROOT, 'results', r['file']))
        c = lists[r['file']][r['core']]
        out.append((c['sets'], c['m'], parse_profile(r['line'], None), f"{r['file']}#{r['core']}"))
    return out


def compose(gadgets, shape, joins, rng):
    sets, vals, off, parts = [], [], 0, []
    for gs, gm, gv, _ in gadgets:
        parts.append((off, gm))
        sets += [[g + off for g in S] for S in gs]
        vals += [{g + off: x for g, x in v.items()} for v in gv]
        off += gm
    L = len(gadgets)
    edges = [(i, i + 1) for i in range(L - 1)]
    if shape == 'cycle' and L > 2: edges.append((L - 1, 0))
    if shape == 'star': edges = [(0, i) for i in range(1, L)]
    ren = {}
    for (i, j), how in zip(edges, joins):
        a = parts[i][0] + rng.randrange(parts[i][1])
        b = parts[j][0] + rng.randrange(parts[j][1])
        if how == 'merge':
            ren[b] = a
        else:
            sets.append([a, b, off, off + 1]); vals.append(None); off += 2
    def r(g):
        while g in ren: g = ren[g]
        return g
    sets = [[r(g) for g in S] for S in sets]
    if any(len(set(S)) < len(S) for S in sets): return None
    for k, v in enumerate(vals):
        if v is not None: vals[k] = {r(g): x for g, x in v.items()}
    lab = {}
    for S in sets:
        for g in S: lab.setdefault(g, len(lab))
    sets2 = [[lab[g] for g in S] for S in sets]
    m = len(lab)
    if not F.check_core(sets2, m): return None
    doms = cc.domains(sets2, m)
    vals2 = []
    for S, v, D in zip(sets2, vals, doms):
        if v is None: vals2.append(rng.choice(D)); continue
        v2 = {lab[g]: x for g, x in v.items()}
        if tuple(v2[g] for g in S) not in {tuple(d[g] for g in S) for d in D}: return None   # type no longer allowed
        vals2.append(v2)
    return sets2, m, vals2


def work(args):
    gadgets, count, lengths, seed = args
    rng = random.Random(seed)
    lines, done, tries, hist = [], 0, 0, {}
    while done < count and tries < 50 * count:
        tries += 1
        L = rng.choice(lengths)
        shape = rng.choice(['path', 'cycle', 'star'])
        chosen = [rng.choice(gadgets) for _ in range(L)]
        joins = [rng.choice(['merge', 'link']) for _ in range(L)]
        c = compose(chosen, shape, joins, rng)
        if c is None: continue
        sets, m, vals = c
        f, holds = c4min_sat.run(sets, m, vals)
        done += 1
        hist[(L, shape)] = hist.get((L, shape), 0) + 1
        if not holds:
            lines.append(f'FAIL {shape} L={L} gadgets {[g[3] for g in chosen]} joins {joins} sets {sets} values '
                         f'{[[v[g] for g in S] for S, v in zip(sets, vals)]}')
    lines.append(f'DONE composites {done} (tries {tries}) by (length, shape) {dict(sorted(hist.items()))}')
    return lines


def main():
    dump, count, lengths, seed, jobs = None, 100, [2, 3, 4, 5], 1, 4
    for a in sys.argv[1:]:
        k, _, v = a.partition('=')
        if k == '--count': count = int(v)
        elif k == '--lengths': lengths = [int(x) for x in v.split(',')]
        elif k == '--seed': seed = int(v)
        elif k == '--jobs': jobs = int(v)
        else: dump = a
    gadgets = load_gadgets(dump)
    print(f'# {len(gadgets)} gadgets (owner needed, d* = 0) from {dump}', flush=True)
    t0, fails, tot = time.time(), 0, 0
    with ProcessPoolExecutor(jobs) as ex:
        for lines in ex.map(work, [(gadgets, count // jobs, lengths, seed * 7919 + j) for j in range(jobs)]):
            for l in lines:
                print(l, flush=True)
                if l.startswith('FAIL'): fails += 1
                if l.startswith('DONE'): tot += int(l.split()[2])
    print(f'TOTAL composites {tot} fails {fails} ({time.time() - t0:.0f} s)')


if __name__ == '__main__':
    main()
