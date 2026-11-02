"""Checks of conjecture DE4 (k4/de4.md). EVIDENCE only, except where a mode says it is exhaustive over a finite set.

  python3 k4/de4/check.py suite                      every suite instance with n <= 6, m <= 15 (k4/suite/instances)
  python3 k4/de4/check.py certs FILES PER [SEED]     PER random strict profiles of every core in the certificate files
  python3 k4/de4/check.py exhaustive FILE MAXN4      every strict profile of the cores of FILE with <= MAXN4 4-good agents
  python3 k4/de4/check.py r1ties BATCHES             random R1-cores (any private goods, junk goods) with tied values
  python3 k4/de4/check.py moves                      improving moves from every non-finishable valid state of the suite
  python3 k4/de4/check.py xcheck                     this implementation against de4.c on sampled profiles
  python3 k4/de4/check.py algo [FILES PER]           algorithm DE4 (draft, chains, DE rings, DE finishing) on the
                                                     suite, or on PER random profiles of every core in FILES

For every profile: the valid states, their maxima (largest level sum, then value-Pareto), and for each maximum whether
it is completable (some assignment of the leftover goods is EFX0) and whether DE's single-owner rule finishes it.
"""
import glob
import itertools
import json
import multiprocessing as mp
import os
import random
import subprocess
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import *  # noqa: E402,F401,F403

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SUITE = os.path.join(ROOT, 'k4', 'suite', 'instances')


def judge(I):
    """(number of maxima, maxima not completable, maxima DE's rule does not finish)"""
    mx = maxima(I, all_states(I))
    nc = [Y for Y in mx if completion(I, Y) is None]
    nd = [Y for Y in mx if de_finish(I, Y) is None] if not nc else nc
    return len(mx), nc, nd


def suite_instances(maxn=6, maxm=15):
    for f in sorted(glob.glob(os.path.join(SUITE, '*.json'))):
        d = json.load(open(f))
        if 'sets' not in d or d.get('kind'):
            continue
        if d['n'] > maxn or d['m'] > maxm:
            yield d, None
        else:
            yield d, Inst.from_json(d)


def mode_suite():
    tot = bad = bad_de = 0
    for d, I in suite_instances():
        if I is None:
            print('skipped (too large for this implementation):', d['id'], 'n =', d['n'], 'm =', d['m'])
            continue
        nmax, nc, nd = judge(I)
        tot += 1
        if nc:
            bad += 1
            print('NOT COMPLETABLE MAXIMUM:', d['id'], nc[0])
        if nd:
            bad_de += 1
            print('maximum not finished by DE single-owner rule:', d['id'], nd[0], values(I, nd[0]))
    print(f'suite: {tot} instances; maxima not completable on {bad}; DE single-owner rule fails on {bad_de}')


def _certs_job(args):
    sets, seed, per = args
    rng = random.Random(seed)
    out = []
    for _ in range(per):
        vals = random_profile(sets, rng)
        I = Inst(sets, vals)
        _, nc, nd = judge(I)
        out.append((bool(nc), bool(nd), None if not nc else (sets, vals)))
    return out


def mode_certs(files, per, seed=1):
    cores = []
    for f in files.split(','):
        cores += load_cores(f if os.path.exists(f) else os.path.join(ROOT, 'results', f))
    jobs = [(s, seed * 1000003 + ci, per) for ci, s in enumerate(cores)]
    c = Counter()
    with mp.Pool(os.cpu_count()) as p:
        for res in p.imap_unordered(_certs_job, jobs, chunksize=2):
            for nc, nd, ex in res:
                c['profiles'] += 1
                c['not_completable'] += nc
                c['de_rule_fails'] += nd
                if ex and c['not_completable'] <= 5:
                    print('NOT COMPLETABLE MAXIMUM:', ex, flush=True)
    print(f'certs {files}: {len(cores)} cores, {c["profiles"]} profiles ({per} per core, seed {seed}); '
          f'maxima not completable on {c["not_completable"]}; DE single-owner rule fails on {c["de_rule_fails"]}')


def _exh_job(args):
    sets, chunk, nch = args
    opts = [type_options(S) for S in sets]
    c = Counter()
    first = None
    for idx, vals in enumerate(itertools.product(*opts)):
        if idx % nch != chunk:
            continue
        I = Inst(sets, list(vals))
        _, nc, nd = judge(I)
        c['profiles'] += 1
        c['not_completable'] += bool(nc)
        c['de_rule_fails'] += bool(nd)
        if nc and first is None:
            first = (sets, vals)
    return c, first


def mode_exhaustive(path, maxn4):
    cores = [s for s in load_cores(path if os.path.exists(path) else os.path.join(ROOT, 'results', path))
             if sum(len(S) == 4 for S in s) <= maxn4]
    jobs = [(s, ch, 8) for s in cores for ch in range(8)]
    c = Counter()
    with mp.Pool(os.cpu_count()) as p:
        for cc, first in p.imap_unordered(_exh_job, jobs):
            c.update(cc)
            if first:
                print('NOT COMPLETABLE MAXIMUM:', first, flush=True)
    print(f'exhaustive {path}, cores with <= {maxn4} four-good agents: {len(cores)} cores, {c["profiles"]} strict '
          f'profiles; maxima not completable on {c["not_completable"]}; DE single-owner rule fails on '
          f'{c["de_rule_fails"]}')


def _r1(seed):
    rng = random.Random(seed)
    c = Counter()
    bad = []
    while c['instances'] < 200:
        n = rng.randint(2, 4)
        m = rng.randint(max(4, n + 1), 3 * n + 1)
        sets = [rng.sample(range(m), rng.choice([3, 4, 4])) for _ in range(n)]
        vals = [[rng.randint(1, rng.choice([4, 6, 10, 20])) for _ in S] for S in sets]
        if any(max(V) >= sum(V) - max(V) for V in vals):
            continue                     # not an R1-core (an agent's top is worth at least the rest)
        I = Inst(sets, vals, m)
        c['instances'] += 1
        _, nc, nd = judge(I)
        c['not_completable'] += bool(nc)
        c['de_rule_fails'] += bool(nd)
        if nc:
            bad.append((sets, vals, m))
    return c, bad


def mode_r1ties(batches):
    c = Counter()
    with mp.Pool(os.cpu_count()) as p:
        for cc, bad in p.imap_unordered(_r1, range(batches)):
            c.update(cc)
            for b in bad:
                print('NOT COMPLETABLE MAXIMUM:', b, flush=True)
    print(f'random R1-cores with ties (n = 2..4): {c["instances"]} instances; maxima not completable on '
          f'{c["not_completable"]}; DE single-owner rule fails on {c["de_rule_fails"]}')


def mode_moves():
    """For every valid state of every suite instance (n <= 5, m <= 12) that DE's rule does not finish: is there a
    better valid state (value-Pareto; or level-monotone: no agent loses level, some gains, or equal levels and
    value-Pareto), and which constructive move finds one."""
    c = Counter()
    for d, I in suite_instances(5, 12):
        if I is None:
            continue
        st = all_states(I)
        V = [values(I, Y) for Y in st]
        L = [[level(I, i, Y[i]) for i in range(I.n)] for Y in st]
        for k, Y in enumerate(st):
            if de_finish(I, Y) is not None:
                continue
            c['not_finishable'] += 1
            comp = completion(I, Y) is not None
            c['completable_anyway'] += comp
            ge = lambda a, b: all(x >= y for x, y in zip(a, b))
            if any(ge(V[l], V[k]) and V[l] != V[k] for l in range(len(st))):
                c['pareto_better_exists'] += 1
            elif any(ge(L[l], L[k]) and (L[l] != L[k] or (ge(V[l], V[k]) and V[l] != V[k])) for l in range(len(st))):
                c['only_level_monotone_better'] += 1
                print('only a level-monotone improvement:', d['id'], Y)
            else:
                c['no_better_state'] += 1
                print('no better state:', d['id'], Y, 'completable' if comp else 'NOT completable')
            if chain_move(I, Y) is not None:
                c['move:chain'] += 1
                continue
            # stuck after chains: the leftover goods the blockers' arcs into each free agent need (G1, G2)
            J = leftover(I, Y)
            W = wanted_goods(I, Y)
            for o in range(I.n):
                if set(Y[o]) & W:
                    continue
                best = None
                for x in range(I.n):
                    if x == o:
                        continue
                    own = list(Y[x]) if not set(Y[x]) & W else []
                    for N in upgrades(I, x, list(Y[o]) + J + own, Y[x], must=Y[o]):
                        k = len(set(N) & set(J))
                        if best is None or k < best[0]:
                            best = (k, x, N)
                kind = 'owner holding >= 2 goods' if len(Y[o]) >= 2 else 'owner holding <= 1 good'
                c[f'arcs: {kind}, fewest leftover goods {None if best is None else best[0]}'] += 1
                if best and best[0] == 2:
                    x, N = best[1], best[2]
                    r = I.ranked(x)
                    bigtop = len(r) == 4 and Y[x] == (r[0],) and set(N) == set(r[1:])
                    c['arcs with two leftover goods: big-top holder of its top taking {b,c,d}' if bigtop
                      else 'arcs with two leftover goods: OTHER'] += 1
            if pointer_ring(I, Y, lazy=False) is not None:
                c['move:DE ring (global greedy)'] += 1
            elif pointer_ring(I, Y) is not None:
                c['move:DE ring (lazy, some start)'] += 1
            elif pointer_ring(I, Y, keep_own=True) is not None:
                c['move:ring, blocker keeps part of its holding'] += 1
                print('ring with a blocker keeping part of its holding:', d['id'], Y)
            else:
                c['move:none of these'] += 1
                print('no catalogue move:', d['id'], Y)
    for key in sorted(c):
        print(f'{key}: {c[key]}')


def mode_xcheck():
    here = os.path.dirname(os.path.abspath(__file__))
    exe = os.path.join(here, 'de4')
    subprocess.run(['gcc', '-O2', '-w', '-o', exe, os.path.join(here, 'de4.c')], check=True)
    bad = 0
    for path, idxs, step in [('k4_certs_2.json.gz', range(5), 37), ('k4_certs_3.json.gz', range(0, 51, 5), 4001)]:
        cores = load_cores(os.path.join(ROOT, 'results', path))
        for ci in idxs:
            sets = cores[ci]
            inp = write_input(sets)
            out = subprocess.run([exe, '5', str(step)], input=inp, capture_output=True, text=True).stdout.split('\n')
            out = [l for l in out if l.startswith('profiles')][0]
            ns = nm = prof = ef = 0
            for idx, vals in enumerate(itertools.product(*[type_options(S) for S in sets])):
                if idx % step != 5:
                    continue
                prof += 1
                I = Inst(sets, list(vals))
                st = all_states(I)
                mx = maxima(I, st)
                ns += len(st)
                nm += len(mx)
                ef += any(completion(I, Y) is None for Y in mx)
            py = f'profiles {prof} states {ns} maxima {nm} every_fail {ef}'
            ok = out.startswith(py)
            bad += not ok
            print('agree' if ok else 'DISAGREE', path, 'core', ci, '| C:', out, '| Python:', py, flush=True)
    print('xcheck:', 'all agree' if not bad else f'{bad} disagreements')


def draft(I):
    taken, Y = set(), []
    for i in range(I.n):
        g = next((g for g in I.ranked(i) if g not in taken), None)
        Y.append((g,) if g is not None else ())
        if g is not None:
            taken.add(g)
    return Y


def better(I, Y, Z):
    a, b = levsum(I, Z), levsum(I, Y)
    if a != b:
        return a > b
    vz, vy = values(I, Z), values(I, Y)
    return all(x >= y for x, y in zip(vz, vy)) and vz != vy


def prop6_applies(I, Y):
    """hypotheses (i), (ii) of Proposition 6 of k4/de4.md"""
    J = set(leftover(I, Y))
    for i, A in enumerate(Y):
        if len(A) >= 2 and I.val(i, A) < I.val(i, [g for g in I.sets[i] if g not in A]):
            return False
        r = I.ranked(i)
        if (len(r) == 4 and A == (r[0],) and I.v[i][r[1]] + I.v[i][r[2]] < I.v[i][r[0]]
                and sum(g in J for g in r[1:]) >= 2):
            return False
    return True


def run_algorithm(I, max_steps=500):
    """Algorithm DE4 (k4/de4.md §2): draft; then repeat: finish by DE's single-owner rule if possible; else the chain
    of Lemma 4/4' (first agent in index order); else DE's ring with the global choice of leftover goods. The two
    fallbacks (the ring assigned along the walk from some start; blockers keeping part of their holding) are only
    counted. Returns (outcome, Counter of moves)."""
    Y = draft(I)
    used = Counter()
    for _ in range(max_steps):
        if de_finish(I, Y) is not None:
            return 'finished', used
        if chain_move(I, Y) is None:
            used['ring steps'] += 1
            used['ring steps where Proposition 6 applies'] += prop6_applies(I, Y)
        for name, f in (('chain', lambda: chain_move(I, Y)), ('DE ring', lambda: pointer_ring(I, Y, lazy=False)),
                        ('fallback: lazy ring', lambda: pointer_ring(I, Y)),
                        ('fallback: ring keeping own goods', lambda: pointer_ring(I, Y, keep_own=True))):
            Z = f()
            if Z is not None and better(I, Y, Z):
                used[name] += 1
                Y = Z
                break
        else:
            return 'STUCK', used
    return 'NO TERMINATION', used


def _algo_job(args):
    sets, seed, per = args
    rng = random.Random(seed)
    c = Counter()
    bad = []
    for _ in range(per):
        vals = random_profile(sets, rng)
        out, used = run_algorithm(Inst(sets, vals))
        c[out] += 1
        c.update('move ' + k for k in used.elements())
        if out != 'finished':
            bad.append((sets, vals, out))
    return c, bad


def mode_algo(files=None, per=0):
    c = Counter()
    if files is None:
        for d, I in suite_instances(8, 16):
            if I is None:
                print('skipped:', d['id'])
                continue
            out, used = run_algorithm(I)
            c[out] += 1
            c.update('move ' + k for k in used.elements())
            if out != 'finished':
                print(out, d['id'], dict(used))
            elif used.get('fallback: lazy ring') or used.get('fallback: ring keeping own goods'):
                print('finished with a fallback move:', d['id'], dict(used))
        print('algorithm DE4 on the suite (n <= 8, m <= 16):', dict(sorted(c.items())))
        return
    cores = []
    for f in files.split(','):
        cores += load_cores(f if os.path.exists(f) else os.path.join(ROOT, 'results', f))
    jobs = [(s, 7 * ci + 3, per) for ci, s in enumerate(cores)]
    with mp.Pool(os.cpu_count()) as p:
        for cc, bad in p.imap_unordered(_algo_job, jobs, chunksize=2):
            c.update(cc)
            for b in bad:
                print('NOT FINISHED', b, flush=True)
    print(f'algorithm DE4 on {files}: {len(cores)} cores, {per} random profiles each:', dict(sorted(c.items())))


def write_input(sets):
    m = 1 + max(max(S) for S in sets)
    lines = [f'{len(sets)} {m}'] + [f'{len(S)} ' + ' '.join(map(str, S)) for S in sets]
    for S in sets:
        o = type_options(S)
        lines.append(str(len(o)))
        lines += [' '.join(map(str, v)) for v in o]
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'suite':
        mode_suite()
    elif mode == 'certs':
        mode_certs(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    elif mode == 'exhaustive':
        mode_exhaustive(sys.argv[2], int(sys.argv[3]))
    elif mode == 'r1ties':
        mode_r1ties(int(sys.argv[2]))
    elif mode == 'moves':
        mode_moves()
    elif mode == 'xcheck':
        mode_xcheck()
    elif mode == 'algo':
        mode_algo(*(sys.argv[2], int(sys.argv[3])) if len(sys.argv) > 3 else ())
    else:
        sys.exit(__doc__)
