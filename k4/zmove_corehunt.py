#!/usr/bin/env python3
"""Annealing hunt for a ZMOVE counterexample that also moves between cores (workstream compute/k4-zmove). EVIDENCE
tooling: everything it finds is re-checked by k4/zmove_check.py, and a failure must be confirmed by k4/zmove_indep.py.

As k4/zmove_hunt.py (the same score: k4/zmove_hunt.key_score, higher = closer to a failure), but the state is an
explicit profile (sets, vals, m) and a neighbour is one of:
  - a type change: one or two agents take a random strict balanced type of their goods (k4/check4.strict_balanced_types);
  - a structural change (probability --pcore, default 0.4): one agent replaces one of its goods by another good it does
    not value (an existing good, or a new one with probability 0.15), keeping its value vector; or two agents exchange
    one good each. Goods valued by nobody are dropped and the goods renumbered.
A neighbour is kept if its sets form a k = 4 core (k4/check4.is_core), main's model.Inst.core_violations() is empty,
the values are strict, n stays in [--minn, --maxn] (fixed by the seed), and k4/cover_screen.c finds a key with
def* > 0 (f in --frange). Recording, checkpointing (OUT.state.json) and restarts as k4/zmove_hunt.py.
usage: python3 k4/zmove_corehunt.py OUT.jsonl.gz --seed=JSON | --seedfile=F[:i] [--minutes=M] [--K=16] [--T0=300]
       [--rng=R] [--patience=P] [--pcore=0.4] [--frange=a:b] [--nrep=N] [--maxm=16]"""
import gzip, json, math, os, random, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import zmove_hunt as ZH
import check4
import model as M
from cover_screen_run import binary, parse_hit

TYPES = {k: check4.strict_balanced_types(k, False) for k in (3, 4)}


def compact(sets):
    used = sorted(set(g for S in sets for g in S))
    rl = {g: i for i, g in enumerate(used)}
    return [[rl[g] for g in S] for S in sets], len(used)


def valid(d, maxm):
    if d['m'] > maxm: return False
    ok, _ = check4.is_core(len(d['sets']), d['m'], d['sets'], False)
    if not ok: return False
    I = M.Inst(d['sets'], d['vals'], d['m'])
    return not I.core_violations() and I.strict()


def neighbour(d, rng, pcore):
    sets = [list(S) for S in d['sets']]; vals = [list(v) for v in d['vals']]; m = d['m']; n = len(sets)
    if rng.random() < pcore:
        if rng.random() < 0.7:
            i = rng.randrange(n); j = rng.randrange(len(sets[i]))
            pool = [g for g in range(m) if g not in sets[i]]
            h = m if (rng.random() < 0.15 or not pool) else rng.choice(pool)
            sets[i][j] = h
        else:
            i, k = rng.sample(range(n), 2)
            j, l = rng.randrange(len(sets[i])), rng.randrange(len(sets[k]))
            a, b = sets[i][j], sets[k][l]
            if b in sets[i] or a in sets[k]: return None
            sets[i][j], sets[k][l] = b, a
        sets, m = compact(sets)
    else:
        for _ in range(1 if rng.random() < 0.7 else 2):
            i = rng.randrange(n)
            t = rng.choice(TYPES[len(sets[i])])
            vals[i] = list(t)
    return {'sets': sets, 'vals': vals, 'm': m}


def screen(profs, frange):
    if not profs: return []
    blocks = []
    for d in profs:
        blocks.append('%d %d' % (len(d['sets']), d['m']))
        for S, v in zip(d['sets'], d['vals']):
            blocks.append('%d %s 1' % (len(S), ' '.join(map(str, S)))); blocks.append(' '.join(map(str, v)))
        blocks.append('0 1')
    p = subprocess.run([binary(), '-f', frange], input='\n'.join(blocks) + '\n', capture_output=True, text=True,
                       check=True)
    hit = set()
    for line in p.stdout.splitlines():
        if line.startswith('HIT '):
            h = parse_hit(line, line.split(None, 5)[5].count('['), None)
            hit.add(json.dumps([h['sets'], h['vals']]))
    return [d for d in profs if json.dumps([d['sets'], d['vals']]) in hit]


def evaluate(d):
    rec, _ = ZH.ZC.check_profile(d, ZH.OPT)
    if not rec.get('keys'): return None, rec, None
    s, bk = ZH.score(rec)
    return s, rec, bk


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    out = [a for a in argv if not a.startswith('--')][0]
    seed = ZH.load_seed(opt)
    seed = {'sets': seed['sets'], 'vals': seed['vals'], 'm': seed.get('m') or 1 + max(map(max, seed['sets']))}
    rng = random.Random(int(opt.get('rng', 1)))
    K = int(opt.get('K', 16)); T0 = float(opt.get('T0', 300)); minutes = float(opt.get('minutes', 20))
    patience = int(opt.get('patience', 60)); nmax = int(opt.get('nrep', 2)); pcore = float(opt.get('pcore', 0.4))
    maxm = int(opt.get('maxm', 16)); frange = opt.get('frange', '1:99')
    stf = out + '.state.json'
    stats = {'steps': 0, 'evals': 0, 'screened': 0, 'hits': 0, 'recorded': 0, 'fails': 0, 'restarts': 0, 'elapsed': 0.0,
             'best_margin': None, 'cores': [], 'seen': []}
    s0, _, bk0 = evaluate(seed)
    if s0 is None: s0 = -99999
    cur, cur_s, best = seed, s0, (s0, seed)
    if os.path.exists(stf):
        sv = json.load(open(stf)); stats = sv['stats']; cur = sv['cur']; best = (sv['best_s'], sv['best'])
        rng.seed(sv['rng'] * 1000003 + stats['steps'])
        cur_s = evaluate(cur)[0] or -99999
    print('# command: python3 k4/zmove_corehunt.py ' + ' '.join(argv), flush=True)
    print('# seed: n=%d m=%d start score %s (margin %s)' % (len(seed['sets']), seed['m'], s0,
                                                           bk0[0]['margin'] if bk0 else None), flush=True)
    seen = set(stats['seen']); cores = set(stats['cores'])
    t0 = time.time(); since = 0; budget = minutes * 60 - stats['elapsed']

    def save():
        stats['seen'] = sorted(seen); stats['cores'] = sorted(cores)
        sv = {'stats': dict(stats, elapsed=stats['elapsed'] + time.time() - t0), 'cur': cur, 'best': best[1],
              'best_s': best[0], 'rng': int(opt.get('rng', 1))}
        json.dump(sv, open(stf + '.tmp', 'w')); os.replace(stf + '.tmp', stf)
    fo = gzip.open(out, 'at')
    while time.time() - t0 < budget:
        T = max(1.0, T0 * (1 - (stats['elapsed'] + time.time() - t0) / (minutes * 60)))
        nb = []; keys = set()
        for _ in range(K * 4):
            d = neighbour(cur, rng, pcore)
            if d is None: continue
            k = json.dumps([d['sets'], d['vals']])
            if k in keys or not valid(d, maxm): continue
            keys.add(k); nb.append(d)
            if len(nb) >= K: break
        stats['screened'] += len(nb)
        hits = screen(nb, frange); stats['hits'] += len(hits)
        cands = []
        for d in hits:
            s, rec, bk = evaluate(d); stats['evals'] += 1
            if s is None: continue
            cores.add(json.dumps([d['sets'], d['m']]))
            cands.append((s, d))
            kr, nrep = bk
            if stats['best_margin'] is None or ZH.ZC_m(kr['margin']) > ZH.ZC_m(stats['best_margin']):
                stats['best_margin'] = kr['margin']
            rk = json.dumps([rec['sets'], rec['vals']])
            if ZH.interesting(kr, nrep, nmax) and rk not in seen:
                seen.add(rk); stats['recorded'] += 1
                rec['score'] = s; rec['hard_key'] = kr['key']; rec['nrep'] = nrep
                fo.write(json.dumps(rec, separators=(',', ':')) + '\n'); fo.flush()
                if not kr['pass'] or kr['margin'] == 'inf' or kr['margin'] > 0:
                    tag = 'ZMOVE-FAIL' if not kr['pass'] else 'MARGIN>0 (T4 edge)'
                    if not kr['pass']: stats['fails'] += 1
                    print('FOUND', tag, json.dumps({k: rec[k] for k in ('sets', 'vals', 'm', 'f')}), json.dumps(kr)[:2000],
                          flush=True)
        stats['steps'] += 1
        if cands:
            s, d = max(cands, key=lambda t: t[0]) if rng.random() < 0.5 else rng.choice(cands)
            if s >= cur_s or rng.random() < math.exp((s - cur_s) / T):
                cur, cur_s = d, s
            if s > best[0]: best = (s, d); since = 0
        since += 1
        if since > patience:
            cur, cur_s = best[1], best[0]; since = 0; stats['restarts'] += 1
            if rng.random() < 0.3: cur, cur_s = seed, s0
        if stats['steps'] % 10 == 0: save()
    fo.close()
    save()
    print('# done: steps %d screened %d hits %d evaluated %d (%d cores) recorded %d fails %d restarts %d; best score %s '
          '(best margin seen %s) at %s' % (stats['steps'], stats['screened'], stats['hits'], stats['evals'], len(cores),
                                           stats['recorded'], stats['fails'], stats['restarts'], best[0],
                                           stats['best_margin'], json.dumps(best[1])), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
