"""Hard perfect starts of multigraph cores (every good of at most two valuers), and the p <= 2 form of Theorem U
(k4/p3.md section 6, Proposition U2), tested on them. Independent code (k4/p3/p3lib.py, oc1max.py, keep2.py).

For each core of the lists (written by k4/p3/mg_cores.py), --per random strict balanced profiles (p3lib.random_types),
every order: serial-dictatorship picks; kept if they form a maximum matching and every agent holds a pick (a perfect
start); hard if the picks have no one-absorber completion (oc1max.Checker.complete). Every hard start is written to
--out (jsonl.gz, records {'sets', 'vals', 'm', 'order', 'picks', 'D', 'DT'}).
At every hard start with exactly one truly dangerous agent k (D_T = {k}; any number of dangerous agents), test U2:
  some H0, a subset of J inside R_k with v_k(H0) > p_k, crowds no holder other than the head z of the unique canonical
  chain P(k) (crowded: |H0 & R_u| >= 2 and v_u(H0 & R_u) > v_u(B'_u)); then B' after P(k) has a one-absorber completion.
Counts the hard starts, the U2 cases (each completion checked by SAT, models re-checked raw), U2 violations, and the
starts with D_T = {k} where no H0 avoids crowding (and whether one official move repairs them).
    python3 k4/p3/t1_p2.py LIST.json.gz [...] --per=20 --seed=1 --out=FILE.jsonl.gz [--procs=1]
"""
import sys, os, json, gzip, random, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst, sd, random_types
from oc1max import Checker, nu
from keep2 import analyse, chain, state, frozen_at


def u2(I, Y, k, J, p, w):
    P = chain(w, k); z = P[-1]
    pool = [g for g in J if g in I.R[k]]
    for r in range(1, len(pool) + 1):
        for H0 in itertools.combinations(pool, r):
            if I.val(k, H0) <= p[k]: continue
            B = state(I, Y, P, H0)
            holders = [u for u in range(I.n) if u != k and u != z and not frozen_at(I, B, u)]
            if any(len(set(H0) & I.R[u]) >= 2 and I.val(u, set(H0) & I.R[u]) > I.val(u, B[u]) for u in holders): continue
            yield P, H0, B


def work(task):
    m, sets, seed, per, name = task
    rng = random.Random(seed); cnt = collections.Counter(); hard = []; notes = []
    for t in range(per):
        vals = random_types(rng, sets, m); I = Inst(sets, vals, m); N = nu(I); K = Checker(I)
        seen = set()
        for o in itertools.permutations(range(I.n)):
            Y = tuple(sd(I, o))
            if Y in seen: continue
            seen.add(Y)
            if sum(y is not None for y in Y) != N: continue
            cnt['maximum pick vectors'] += 1
            if None in Y: cnt['not perfect (skipped)'] += 1; continue
            if K.complete(tuple(frozenset([y]) for y in Y)) is not None: continue
            J, p, w, F, D, DT, EJ = analyse(I, list(Y))
            cnt['hard perfect starts'] += 1; cnt[f'hard, |D| = {len(D)}, |D_T| = {len(DT)}'] += 1
            hard.append({'name': f'{name}.{t}', 'sets': sets, 'vals': vals, 'm': m, 'order': list(o), 'picks': list(Y),
                         'D': sorted(D), 'DT': sorted(DT)})
            if len(DT) != 1: continue
            k = next(iter(DT)); ok = False
            for P, H0, B in u2(I, list(Y), k, J, p, w):
                cnt['U2 (chain, H0) cases'] += 1
                if K.complete(tuple(B)) is None:
                    cnt['U2 VIOLATION'] += 1; notes.append(('VIOLATION', name, t, sets, vals, Y, P, H0))
                else: ok = True
            cnt['D_T = {k}: U2 applies' if ok else 'D_T = {k}: no H0 avoids crowding'] += 1
            if not ok:
                r = K.check(Y)[0]; cnt['  ... of which one move repairs' if r != 'OC1 fails' else '  ... of which OC1 FAILS'] += 1
                notes.append(('NO-U2', name, t, sets, vals, Y))
        K.close()
    return cnt, hard, notes


if __name__ == '__main__':
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    per, seed, procs = int(opt.get('per', 20)), int(opt.get('seed', 1)), int(opt.get('procs', 1))
    print('$ python3 k4/p3/t1_p2.py ' + ' '.join(sys.argv[1:]), flush=True)
    tasks = []
    for f in files:
        d = json.load(gzip.open(f, 'rt'))
        for c in d['cores']:
            tasks.append((c['m'], c['sets'], seed * 1000003 + len(tasks), per, f'{os.path.basename(f)}#{c["idx"]}'))
    tot = collections.Counter(); t0 = time.time(); out = gzip.open(opt['out'], 'wt') if opt.get('out') else None
    first = {}
    with mp.Pool(procs) as pool:
        for i, (cnt, hard, notes) in enumerate(pool.imap_unordered(work, tasks, chunksize=4)):
            tot.update(cnt)
            for h in hard:
                if out: out.write(json.dumps(h) + '\n')
            for nt in notes:
                if nt[0] not in first or (len(nt[3]), nt[3] and 0) < (len(first[nt[0]][3]), 0): first[nt[0]] = nt
                if nt[0] == 'VIOLATION': print(nt, flush=True)
            if (i + 1) % 100 == 0: print(f'... {i + 1} / {len(tasks)} cores, {time.time() - t0:.0f} s', flush=True)
    if out: out.close()
    for k in sorted(tot): print(f'{k}: {tot[k]}')
    for k, nt in first.items(): print('first', k, json.dumps(nt))
    print(f'time {time.time() - t0:.0f} s')
