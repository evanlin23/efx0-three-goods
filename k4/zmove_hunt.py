#!/usr/bin/env python3
"""Annealing hunt for a counterexample to Theorem ZMOVE, or for the keys closest to one (workstream compute/k4-zmove).
EVIDENCE tooling: everything it finds is re-checked by k4/zmove_check.py, and a failure must be confirmed by
k4/zmove_indep.py before it is believed.

State: a strict profile of a fixed core (the seed's sets and m; each agent's value vector ranges over the core's strict
balanced types, k4/check4.py's core_domains, plus the seed's own vector). A step proposes K neighbours (one or two
agents change type), keeps those that k4/cover_screen.c finds with a key of def* > 0 (f in --frange), and scores each
with k4/zmove_check.check_profile. Per key κ with def* > 0 (margin = min over the Z′-maxima of the least def(P′) over
the (T3⁺) moves with <= 1 helper from P_Q; nrep = the number of such moves to def <= 0 from the maxima):
  s(κ) = 10000·[ZMOVE fails at κ] + 1000·clip(margin, -3, 5) + 200·[no (T4) edge to smaller def*] - min(nrep, 199)
and the profile's score is the maximum over its keys (higher = closer to a failure; margin > 0 means the one-move
clause fails, a failure if there is also no (T4) edge). Metropolis acceptance at a temperature falling linearly;
restarts from the best state after --patience steps without improvement. A profile is appended to OUT (each once) if
its best key fails ZMOVE, has margin > 0, or has margin 0 with nrep <= --nrep (default 2). The
state is checkpointed in OUT.state.json (resumable; one checkpoint per run).

usage: python3 k4/zmove_hunt.py OUT.jsonl.gz --seed='{"sets": ..., "vals": ..., "m": ...}' | --seedfile=F[:i]
       [--minutes=M] [--K=16] [--T0=300] [--rng=R] [--patience=P] [--frange=a:b] [--nrep=N]
F is gzip JSON lines or a JSON list of {sets, vals, m}."""
import gzip, json, math, os, random, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import zmove_check as ZC
from cover_screen_run import binary, parse_hit
from check4 import core_domains

OPT = {'fmin': 1, 'fmax': 99, 'all': False, 'verify_now': False}


def key_score(kr):
    m = kr['margin']
    mm = 5 if m == 'inf' else max(-3, min(5, m))
    nrep = sum(sum(mr['kinds'].values()) for mr in kr['maxima'])
    return 10000 * (not kr['pass']) + 1000 * mm + 200 * (not kr['t4edge']) - min(nrep, 199), nrep


def score(rec):
    best = None; bk = None
    for kr in rec.get('keys', []):
        s, nrep = key_score(kr)
        if best is None or s > best: best, bk = s, (kr, nrep)
    return best, bk


def interesting(kr, nrep, nmax):
    m = kr['margin']
    return (not kr['pass']) or m == 'inf' or m > 0 or (m == 0 and nrep <= nmax)


class Hunt:
    def __init__(self, seed, rng, frange='1:99'):
        self.frange = frange
        self.sets, self.m = seed['sets'], seed['m']
        self.n = len(self.sets)
        doms = core_domains(self.sets, self.m, False)
        self.dom = [[tuple(D[g] for g in S) for D in Ds] for Ds, S in zip(doms, self.sets)]
        for i, v in enumerate(seed['vals']):
            if tuple(v) not in self.dom[i]: self.dom[i].insert(0, tuple(v))
        self.cur = [self.dom[i].index(tuple(v)) for i, v in enumerate(seed['vals'])]
        self.rng = rng
        self.bin = binary()

    def vals(self, st): return [list(self.dom[i][t]) for i, t in enumerate(st)]

    def neighbours(self, st, K):
        out = set()
        for _ in range(K * 3):
            s2 = list(st)
            for _ in range(1 if self.rng.random() < 0.7 else 2):
                i = self.rng.randrange(self.n)
                s2[i] = self.rng.randrange(len(self.dom[i]))
            if s2 != list(st): out.add(tuple(s2))
            if len(out) >= K: break
        return list(out)

    def screen(self, states):
        blocks = []
        for st in states:
            blocks.append('%d %d' % (self.n, self.m))
            for S, v in zip(self.sets, self.vals(st)):
                blocks.append('%d %s 1' % (len(S), ' '.join(map(str, S)))); blocks.append(' '.join(map(str, v)))
            blocks.append('0 1')
        p = subprocess.run([self.bin, '-f', self.frange], input='\n'.join(blocks) + '\n', capture_output=True, text=True,
                           check=True)
        hit = set()
        for line in p.stdout.splitlines():
            if line.startswith('HIT '): hit.add(json.dumps(parse_hit(line, self.n, self.m)['vals']))
        return [st for st in states if json.dumps(self.vals(st)) in hit]

    def evaluate(self, st):
        d = {'sets': self.sets, 'vals': self.vals(st), 'm': self.m}
        rec, _ = ZC.check_profile(d, OPT)
        if not rec.get('keys'): return None, rec, None
        s, bk = score(rec)
        return s, rec, bk


def load_seed(opt):
    if 'seed' in opt: return json.loads(opt['seed'])
    fn, _, idx = opt['seedfile'].partition(':')
    if fn.endswith('.jsonl.gz') or fn.endswith('.jsonl'):
        lines = [json.loads(l) for l in (gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))]
    else:
        lines = json.load(gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))
    return lines[int(idx or 0)]


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    out = [a for a in argv if not a.startswith('--')][0]
    seed = load_seed(opt)
    seed = {'sets': seed['sets'], 'vals': seed['vals'], 'm': seed.get('m') or 1 + max(map(max, seed['sets']))}
    rng = random.Random(int(opt.get('rng', 1)))
    K = int(opt.get('K', 16)); T0 = float(opt.get('T0', 300)); minutes = float(opt.get('minutes', 20))
    patience = int(opt.get('patience', 60)); nmax = int(opt.get('nrep', 2))
    H = Hunt(seed, rng, opt.get('frange', '1:99'))
    stf = out + '.state.json'
    stats = {'steps': 0, 'evals': 0, 'screened': 0, 'hits': 0, 'recorded': 0, 'fails': 0, 'restarts': 0, 'elapsed': 0.0,
             'best_margin': None, 'seen': []}
    cur = tuple(H.cur)
    s0, rec0, bk0 = H.evaluate(cur)
    if s0 is None: s0 = -99999
    best = (s0, cur)
    if os.path.exists(stf):
        sv = json.load(open(stf)); stats = sv['stats']; cur = tuple(sv['cur']); best = (sv['best_s'], tuple(sv['best']))
        rng.seed(sv['rng'] * 1000003 + stats['steps'])
    cur_s = H.evaluate(cur)[0] or -99999
    print('# command: python3 k4/zmove_hunt.py ' + ' '.join(argv), flush=True)
    print('# seed: n=%d m=%d start score %s (margin %s)' % (H.n, H.m, s0, bk0[0]['margin'] if bk0 else None), flush=True)
    seen = set(stats['seen'])
    t0 = time.time(); since = 0; budget = minutes * 60 - stats['elapsed']

    def save():
        stats['seen'] = sorted(seen)
        sv = {'stats': dict(stats, elapsed=stats['elapsed'] + time.time() - t0), 'cur': list(cur), 'best': list(best[1]),
              'best_s': best[0], 'rng': int(opt.get('rng', 1))}
        json.dump(sv, open(stf + '.tmp', 'w')); os.replace(stf + '.tmp', stf)
    fo = gzip.open(out, 'at')
    while time.time() - t0 < budget:
        T = max(1.0, T0 * (1 - (stats['elapsed'] + time.time() - t0) / (minutes * 60)))
        nb = H.neighbours(cur, K); stats['screened'] += len(nb)
        hits = H.screen(nb); stats['hits'] += len(hits)
        cands = []
        for st in hits:
            s, rec, bk = H.evaluate(st); stats['evals'] += 1
            if s is None: continue
            cands.append((s, st))
            kr, nrep = bk
            if stats['best_margin'] is None or ZC_m(kr['margin']) > ZC_m(stats['best_margin']):
                stats['best_margin'] = kr['margin']
            rk = json.dumps(rec['vals'])
            if interesting(kr, nrep, nmax) and rk not in seen:
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
            s, st = max(cands) if rng.random() < 0.5 else rng.choice(cands)
            if s >= cur_s or rng.random() < math.exp((s - cur_s) / T):
                cur, cur_s = st, s
            if s > best[0]: best = (s, st); since = 0
        since += 1
        if since > patience:
            cur, cur_s = best[1], best[0]; since = 0; stats['restarts'] += 1
            if rng.random() < 0.3: cur, cur_s = tuple(H.cur), s0
        if stats['steps'] % 10 == 0: save()
    fo.close()
    save()
    stats['elapsed'] += time.time() - t0
    print('# done: steps %d screened %d hits %d evaluated %d recorded %d fails %d restarts %d; best score %s (best margin '
          'seen %s) at %s' % (stats['steps'], stats['screened'], stats['hits'], stats['evals'], stats['recorded'],
                              stats['fails'], stats['restarts'], best[0], stats['best_margin'], H.vals(best[1])), flush=True)


def ZC_m(m): return 99 if m == 'inf' else m


if __name__ == '__main__':
    main(sys.argv[1:])
