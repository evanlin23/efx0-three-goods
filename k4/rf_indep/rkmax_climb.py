"""Climb toward a counterexample to Conjecture RKMAX at n = 5 (k4/sdc.md section 31 end), starting from the
one-receiver sigma-maximal vectors of the random hunt that need a move (rkmax_rand.py --dump).
Workstream compute/k4-rf-indep.

State: a strict profile of a fixed core.  Its targets are the sigma-maximal maximum-matching SD vectors (all n! orders)
that have exactly one receiver and whose picks do not complete.  Score: the smallest (repairing post-chain states,
completions) over the targets, lexicographically (rf_oc1.c count mode: distinct states after one improving chain that
have a one-absorber completion, and the (absorber, placement) completions over them); lower is harder, and 0 repairing
states is an RKMAX counterexample.  A mutation changes one value (resample in 1..V, a nudge of
+-1..3, or a swap of two of an agent's values), keeps the profile strict, and is accepted when the profile still has a
target and the score does not rise (rarely, by up to 2).  Every sigma-maximal vector, target or not, is tested, so any
OC1 failure is caught; failures are re-checked by the pure-Python search (rf_check.py_oc1, raw EFX0 by enumeration).

    python3 k4/rf_indep/rkmax_climb.py --steps 300 [--procs 4]
"""
import sys, os, gzip, json, itertools, collections, time, argparse, tempfile, subprocess, random, math
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import rf_check as R
from rkmax_check import sigma
from rkmax_rand import strict_vals

G = {}
DUMPS = [('results/k4_rf_indep/rkmax_rand_n5_v20_s1_one_receiver.jsonl.gz', 20),
         ('results/k4_rf_indep/rkmax_rand_n5_v250_s1_one_receiver.jsonl.gz', 250)]


def init_worker(binpath):
    G['p'] = subprocess.Popen([binpath, 'count'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    G['perms'] = {}


def ask(line):
    G['p'].stdin.write(line + '\n'); G['p'].stdin.flush()
    return G['p'].stdout.readline().split()


def evaluate(sets, m, vals):
    """returns (score or None, details); score None: no target.  details['F']: sigma-maximal vectors with no repair"""
    n = len(sets)
    if n not in G['perms']: G['perms'][n] = list(itertools.permutations(range(n)))
    nu = G.setdefault(('nu', json.dumps(sets)), R.nu_kuhn(sets))
    pref = R.prefs(sets, vals)
    vecs = set(R.sd(pref, o) for o in G['perms'][n])
    mm = [Y for Y in vecs if sum(1 for y in Y if y is not None) == nu]
    sig = {Y: sigma(sets, vals, Y) for Y in mm}; best = max(sig.values())
    det = dict(F=[], targets=[], sigma=best)
    score = None
    for Y in sorted((Y for Y in mm if sig[Y] == best), key=str):
        a = ask(R.task_line('c', sets, vals, m, [[y] if y is not None else [] for y in Y]))
        if a[1] == 'P': continue
        nrep, nst, ncomp = int(a[2]), int(a[3]), int(a[4])
        if nrep == 0: det['F'].append(list(Y))
        rec = R.receivers(sets, vals, Y)
        if len(rec) == 1:
            det['targets'].append(dict(picks=list(Y), repairing=nrep, states=nst, completions=ncomp, receiver=rec[0]))
            sc = (nrep, ncomp)
            score = sc if score is None else min(score, sc)
    return score, det


def mutate(rnd, vals, V):
    for _ in range(100):
        new = [list(v) for v in vals]; i = rnd.randrange(len(new)); k = rnd.randrange(len(new[i])); r = rnd.random()
        if r < 0.4: new[i][k] = rnd.randint(1, V)
        elif r < 0.8: new[i][k] = max(1, min(255, new[i][k] + rnd.choice((-3, -2, -1, 1, 2, 3))))
        else:
            k2 = rnd.randrange(len(new[i])); new[i][k], new[i][k2] = new[i][k2], new[i][k]
        v = new[i]; sums = [sum(v[q] for q in range(len(v)) if mask >> q & 1) for mask in range(1 << len(v))]
        if new != vals and len(set(sums)) == len(sums): return new
    return None


def climb(job):
    sid, seed, steps = job
    rnd = random.Random('climb/%d' % sid)
    sets, m, vals, V = seed['sets'], 1 + max(max(s) for s in seed['sets']), seed['vals'], seed['V']
    score, det = evaluate(sets, m, vals)
    out = dict(sid=sid, core=(seed['core_m'], seed['core_idx']), V=V, start_score=score, F=[], accepted=0)
    if score is None: out['note'] = 'seed has no target'; return out
    cur, cur_det, cur_vals = score, det, vals
    best = (score, vals, det)
    for step in range(steps):
        new = mutate(rnd, cur_vals, V)
        if new is None: break
        s, d = evaluate(sets, m, new)
        if d['F']:
            out['F'].append(dict(vals=new, F=d['F'], sigma=d['sigma']))
        if s is None: continue
        if s <= cur or (s[0] <= cur[0] + 1 and rnd.random() < 0.05):
            cur, cur_det, cur_vals = s, d, new; out['accepted'] += 1
            if s < best[0]: best = (s, new, d)
    out.update(best_score=best[0], best_vals=best[1], best_det=best[2], sets=sets)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--steps', type=int, default=300); ap.add_argument('--procs', type=int, default=os.cpu_count() or 4)
    ap.add_argument('--bin', default=None); ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--out', default=None, help='write every seed\'s best profile here (JSONL, gzip)')
    args = ap.parse_args(); t0 = time.time()
    print('$ python3 k4/rf_indep/rkmax_climb.py --steps %d --procs %d' % (args.steps, args.procs))
    binpath = args.bin or os.path.join(tempfile.gettempdir(), 'rf_oc1_bin')
    subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    seeds = []
    for fn, V in DUMPS:
        for line in gzip.open(os.path.join(ROOT, fn), 'rt'):
            r = json.loads(line)
            if r['oc1'].startswith('C'): r['V'] = V; seeds.append(r)
    if args.limit: seeds = seeds[:args.limit]
    print('seeds: %d one-receiver sigma-maximal vectors that need a move' % len(seeds), flush=True)
    res = []
    with Pool(args.procs, initializer=init_worker, initargs=(binpath,)) as pool:
        for r in pool.imap_unordered(climb, [(i, s, args.steps) for i, s in enumerate(seeds)]):
            res.append(r)
            if r['F']: print('F FOUND', json.dumps(r['F'][0]), json.dumps(r.get('sets')), flush=True)
    res.sort(key=lambda r: r['sid'])
    print('climb done %.0f s' % (time.time() - t0), flush=True)
    C = collections.Counter(); start = collections.Counter(); bestc = collections.Counter()
    for r in res:
        if r['start_score'] is None: C['seeds without a target (re-evaluation differs)'] += 1; continue
        start[min(r['start_score'][0], 20)] += 1; bestc[min(r['best_score'][0], 20)] += 1
        C['accepted moves'] += r['accepted']; C['seeds'] += 1
    print('seeds', C['seeds'], 'accepted moves', C['accepted moves'])
    print('start score (repairing post-chain states, capped at 20):', dict(sorted(start.items())))
    print('best score  (repairing post-chain states, capped at 20):', dict(sorted(bestc.items())))
    hard = sorted((r for r in res if r.get('best_score') is not None), key=lambda r: r['best_score'])[:12]
    print('hardest profiles found:')
    for r in hard:
        t = min(r['best_det']['targets'], key=lambda x: (x['repairing'], x['completions']))
        print('  core (m %d, idx %d) V %d: score %s (repairing states, completions; of %d post-chain states), sigma %s, picks %s, receiver %d, sets %s, vals %s'
              % (r['core'][0], r['core'][1], r['V'], tuple(r['best_score']), t['states'], r['best_det']['sigma'], t['picks'],
                 t['receiver'], json.dumps(r['sets']), json.dumps(r['best_vals'])))
    Fs = [(r, f) for r in res for f in r['F']]
    print('OC1 failures at sigma-maximal vectors met during the climb: %d' % len(Fs))
    for r, f in Fs:
        for Y in f['F']:
            m = 1 + max(max(s) for s in r['sets'])
            second = R.py_oc1(r['sets'], f['vals'], m, [[y] if y is not None else [] for y in Y])
            print('  F core %s sets %s vals %s picks %s sigma %s; pure-Python search: %s'
                  % (r['core'], json.dumps(r['sets']), json.dumps(f['vals']), Y, f['sigma'], second))
    if args.out:
        with gzip.open(args.out, 'wt') as f:
            for r in res:
                if r.get('best_score') is None: continue
                f.write(json.dumps(dict(core_m=r['core'][0], core_idx=r['core'][1], V=r['V'], sets=r['sets'],
                                        vals=r['best_vals'], score=r['best_score'], start_score=r['start_score'],
                                        targets=r['best_det']['targets'], sigma=r['best_det']['sigma'])) + '\n')
    print('RESULT climb: %d seeds x %d steps, OC1 failures %d, smallest score %s'
          % (C['seeds'], args.steps, len(Fs), min((tuple(r['best_score']) for r in res if r.get('best_score') is not None), default=None)))
    print('time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
