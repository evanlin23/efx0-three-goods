"""Hunt for k* = n: cyclic cores generalizing the f = 0 rotation trap dl2-rot-n3m7 (compute/k4-dl2). EVIDENCE only.

  python3 k4/dl2_cycle.py N [--sample=P] [--jobs=J] [--max-cores=C] [--dump=PATH] [--tables=PATH]

dl2-rot-n3m7 (attempts/k4-dl2-rotation.md) is, up to relabelling, the pattern: agents i = 0..n-1 on a cycle, agent i
values {t_i, x_i, t_{i+1}, y_i} with top t_i and second good x_i (t_i is also a good of agent i-1), the trapped P
gives agent i the pair {x_i, t_{i+1}}, and one more good j is junk (m = 2n + 1, so omega >= 1 and f = 0 is
possible). Here the goods are t_0..t_{n-1}, x_0..x_{n-1}, j, and each y_i ranges over j and the x_k, k != i. For every
assignment of the y_i that gives a connected k = 4 core (check4.is_core; every good valued, at most two private goods,
...), up to rotating the cycle, k4/dl2.c evaluates EVERY strict profile in which each agent's top is t_i and its
second good x_i (24 of the 288 strict balanced types; the private-pair condition of check4.core_domains applies), or
--sample=P random ones per core. Prints the k* histogram per core and in total, with dl2_run.py's counters; --dump writes
the D records of every profile with k* >= 3 (and of every 1000th with k* = 1 or 2)."""
import gzip, itertools, json, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import dl2_run as DR


def cores(n):
    t = list(range(n)); x = list(range(n, 2 * n)); j = 2 * n; m = 2 * n + 1
    seen, out = set(), []
    choices = [[j] + [x[k] for k in range(n) if k != i] for i in range(n)]
    for ys in itertools.product(*choices):
        sets = [[t[i], x[i], t[(i + 1) % n], ys[i]] for i in range(n)]
        if not check4.is_core(n, m, sets, True)[0]: continue
        # canonical form under rotating the cycle (relabel i -> i + r)
        def rot(r):
            mp = {}
            for i in range(n):
                mp[t[i]] = t[(i + r) % n]; mp[x[i]] = x[(i + r) % n]
            mp[j] = j
            return tuple(sorted(tuple(mp[g] for g in sets[(i - r) % n]) for i in range(n)))
        key = min(rot(r) for r in range(n))
        if key in seen: continue
        seen.add(key); out.append({'m': m, 'sets': sets, 'ys': list(ys)})
    return out


def run(task):
    k, c, opts, P = task
    sets, m = c['sets'], c['m']
    doms = check4.core_domains(sets, m, False)
    doms = [[d for d in D if d[S[0]] > d[S[1]] > max(d[S[2]], d[S[3]])] for S, D in zip(sets, doms)]
    t0 = time.time()
    b = DR.run_blocks(DR.block(sets, m, doms, k, P), opts)[0]
    for d in b['D']:
        d['vals'] = [[D[p][g] for g in S] for S, D, p in zip(sets, doms, d['prof'])]
        d['core'] = {'id': f'cycle-n{len(sets)}-{k}', 'm': m, 'sets': sets}
    return k, c, b, time.time() - t0


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    n = int(args[0])
    print('# command: python3 k4/dl2_cycle.py ' + ' '.join(sys.argv[1:]), flush=True)
    print(f'# dl2.c sha256 {DR.SHA}', flush=True)
    DR.build()
    cs = cores(n)
    if 'max-cores' in opt: cs = cs[:int(opt['max-cores'])]
    what = f"{opt['sample']} random profiles per core" if 'sample' in opt else 'every profile'
    print(f'# n = {n}: {len(cs)} cyclic cores (up to rotation), {what} with top t_i and second good x_i', flush=True)
    tot = {}
    t0 = time.time()
    with Pool(int(opt.get('jobs', 2))) as pool:
        P = int(opt.get('sample', 0))
        for k, c, b, secs in pool.imap_unordered(run, [(k, c, ['-r1000', '-q1000', '-S1'], P) for k, c in enumerate(cs)]):
            DR.merge(tot, b)
            K = b['K']
            print(f"core {k} ys={c['ys']}: profiles {K['prof']}, omega >= 1 {K['om1']}, k* = 0/1/2/3/>=4/inf: {K['kstar0']}/"
                  f"{K['kstar1']}/{K['kstar2']}/{K['kstar3']}/{K['kstar4']}/{K['kstarinf']}, k* = n: {K['kstarn']} [{secs:.1f} s]", flush=True)
            DR.dump_write(opt.get('dump'), b['D'])
    DR.report(f'cyclic cores n = {n}', tot, time.time() - t0)
    if 'tables' in opt:
        json.dump({'command': 'python3 k4/dl2_cycle.py ' + ' '.join(sys.argv[1:]), 'dl2_c_sha256': DR.SHA,
                   'counters': {k: tot.get(k, 0) for k in DR.KEYS}, 'T': tot.get('T', {}), 'A': tot.get('A', {})},
                  open(opt['tables'], 'w'), indent=0, sort_keys=True)


if __name__ == '__main__':
    main()
