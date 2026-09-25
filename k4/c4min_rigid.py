#!/usr/bin/env python3
"""Owner-rigid gadgets glued in pairs (k4/c4min_hunt.md §4.3).

A profile of a small core is *owner-rigid* if an owner is needed (f* > sigma) and exactly one agent o has a
min-frozen pre-allocation with deficit <= 0 when only o may own (k4/c4min_hunt.c -1o). Two rigid gadgets A, B with
different owners are glued, and C4min is tested on the glued instance:
  merge: one good of A identified with one good of B (every pair of goods; types unchanged), one profile each (-1q);
  link:  a connector agent w = {a, b, p, q} (a of A, b of B, p and q private), every pair (a, b) and every type of w
         (exhaustive mode -E with w as the vectorized agent and every other agent restricted to its gadget type).
With only one owner for the whole instance, a gadget whose junk only its own owner can absorb has to be protected
through slots instead; the question is whether the two demands can exceed the supply.

usage: c4min_rigid.py [--samples=N] [--pairs=P] [--seed=S] [--jobs=J] FILE [FILE ...]   (core lists of n = 3, 4)
       c4min_rigid.py --gadgets=DUMP.jsonl [--pairs=P] ...   the gadgets are the profiles of a climber dump
       (k4/c4min_climb.py --dump) with an owner needed and d* = 0 (the tightest found), not only owner-rigid ones"""
import itertools, json, os, random, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
import c4min_common as cc
import c4min_families as F

INF = 10 ** 6


def owners(sets, m, vals):
    inp = cc.input_one(sets, m, vals) + ' '.join('0' for _ in sets) + '\n'
    w = subprocess.run([cc.hunt_binary(), '-1o'], input=inp, capture_output=True, text=True, check=True).stdout.split()
    f, sigma = int(w[2]), int(w[4])
    return f, sigma, [int(x) for x in w[5:]]


def quick(sets, m, vals):
    inp = cc.input_one(sets, m, vals) + ' '.join('0' for _ in sets) + '\n'
    w = subprocess.run([cc.hunt_binary(), '-1q'], input=inp, capture_output=True, text=True, check=True).stdout.split()
    return int(w[2]), int(w[4])


def find_rigid(args):
    sets, m, doms, seed, N = args
    rng = random.Random(seed)
    out = []
    for _ in range(N):
        vals = [rng.choice(D) for D in doms]
        f, sigma, D = owners(sets, m, vals)
        if f <= sigma: continue
        ok = [o for o, d in enumerate(D) if d <= 0]
        if len(ok) == 1: out.append({'sets': sets, 'm': m, 'vals': [[v[g] for g in S] for S, v in zip(sets, vals)], 'owner': ok[0], 'D': D, 'fstar': f, 'sigma': sigma})
    return out


def glue_test(args):
    A, B = args
    res = {'merge': [0, 0], 'link': [0, 0], 'fails': []}
    mA = A['m']
    valsA = [dict(zip(S, v)) for S, v in zip(A['sets'], A['vals'])]
    valsB = [dict(zip([g + mA for g in S], v)) for S, v in zip(B['sets'], B['vals'])]
    setsB = [[g + mA for g in S] for S in B['sets']]
    for a, b in itertools.product(range(mA), range(mA, mA + B['m'])):
        # merge a and b
        sets = [list(S) for S in A['sets']] + [[a if g == b else g for g in S] for S in setsB]
        vals = valsA + [{(a if g == b else g): x for g, x in v.items()} for v in valsB]
        sets2, m2 = F.normalize(sets)
        lab = {}
        for S in sets:
            for g in S: lab.setdefault(g, len(lab))
        vals2 = [{lab[g]: x for g, x in v.items()} for v in vals]
        if F.check_core(sets2, m2) and all(cc.domains([S], m2) for S in sets2):
            f, holds = quick(sets2, m2, vals2)
            res['merge'][0] += 1
            if not holds: res['merge'][1] += 1; res['fails'].append(('merge', sets2, m2, [[v[g] for g in S] for S, v in zip(sets2, vals2)]))
        # link agent w = {a, b, p, q}
        m3 = mA + B['m'] + 2
        sets3 = [list(S) for S in A['sets']] + setsB + [[a, b, m3 - 2, m3 - 1]]
        if not F.check_core(sets3, m3): continue
        doms = cc.domains(sets3, m3)
        fixed = valsA + valsB
        lines = [f'{len(sets3)} {m3}']
        for S, v in zip(sets3[:-1], fixed):
            lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + ' 1'); lines.append(' '.join(str(v[g]) for g in S))
        S = sets3[-1]
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + f' {len(doms[-1])}')
        for v in doms[-1]: lines.append(' '.join(str(v[g]) for g in S))
        out = subprocess.run([cc.hunt_binary(), '-E', '-x', '3'], input='\n'.join(lines) + '\n0 1\n', capture_output=True, text=True, check=True).stdout
        w = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
        res['link'][0] += int(w[2]); res['link'][1] += int(w[10])
        for l in out.splitlines():
            if l.startswith('FAIL'): res['fails'].append(('link', sets3, m3, l))
    return res


def main():
    files, N, P, seed, jobs, gadgets = [], 300, 40, 1, 4, None
    for a in sys.argv[1:]:
        k, _, v = a.partition('=')
        if k == '--samples': N = int(v)
        elif k == '--pairs': P = int(v)
        elif k == '--seed': seed = int(v)
        elif k == '--jobs': jobs = int(v)
        elif k == '--gadgets': gadgets = v
        else: files.append(a)
    cc.hunt_binary()
    rng = random.Random(seed)
    tasks = []
    for f in files:
        for ci, c in enumerate(cc.load_cores(f)):
            tasks.append((c['sets'], c['m'], cc.domains(c['sets'], c['m']), seed * 100003 + len(tasks), N))
    t0 = time.time()
    rigid = []
    if gadgets:
        from c4min_climb import parse_profile
        lists = {}
        for l in open(gadgets):
            r = json.loads(l)
            if not (r['owner'] and r['dstar'] == 0): continue
            if r['file'] not in lists: lists[r['file']] = cc.load_cores(os.path.join(cc.ROOT, 'results', r['file']))
            c = lists[r['file']][r['core']]
            vals = parse_profile(r['line'], None)
            rigid.append({'sets': c['sets'], 'm': c['m'], 'vals': [[v[g] for g in S] for S, v in zip(c['sets'], vals)], 'source': f"{r['file']}#{r['core']}"})
        print(f'# {len(rigid)} gadgets (owner needed, d* = 0) from {gadgets}', flush=True)
    with ThreadPoolExecutor(jobs) as ex:
        for r in ex.map(find_rigid, tasks): rigid += r
    if tasks: print(f'# {len(tasks)} cores x {N} random profiles: {len(rigid)} owner-rigid profiles ({time.time() - t0:.0f} s)', flush=True)
    pairs = [(rng.choice(rigid), rng.choice(rigid)) for _ in range(P)] if rigid else []
    tot = {'merge': [0, 0], 'link': [0, 0]}
    with ThreadPoolExecutor(jobs) as ex:
        for (A, B), res in zip(pairs, ex.map(glue_test, pairs)):
            for k in ('merge', 'link'): tot[k][0] += res[k][0]; tot[k][1] += res[k][1]
            for fl in res['fails']:
                print('FAIL', json.dumps(fl), '\n  gadgets', json.dumps(A), json.dumps(B), flush=True)
    print(f'# glued pairs {len(pairs)}: merge profiles {tot["merge"][0]} fails {tot["merge"][1]}; '
          f'link profiles {tot["link"][0]} fails {tot["link"][1]} ({time.time() - t0:.0f} s)')


if __name__ == '__main__':
    main()
