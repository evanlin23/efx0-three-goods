#!/usr/bin/env python3
"""Annealing hunt for keys that COVER / COVER⁺ leave uncovered, or that only the rarest lemma covers (workstream
compute/k4-cover). EVIDENCE tooling: what it finds is checked by k4/cover_check.py, and every uncovered key it
reports must be confirmed by k4/cover_indep.py before it is believed.

State: a strict profile of a fixed core (the seed's sets and m; each agent's value vector ranges over the core's strict
balanced types, k4/check4.py's core_domains, plus the seed's own vector). A step proposes K neighbours (one or two
agents change type), keeps those that k4/cover_screen.c finds with a key of def* > 0 (at any f >= 1), and scores them
with k4/cover_check.check_profile:
  margin(κ)   = the number of (maximum, lemma) pairs covering κ (COVER's lemmas at f = 1, COVER⁺'s at f >= 2);
  rare(κ)     = κ is covered only by B⁺ with threat path 1, or only by C′⁺ instances whose paying good is φ(w) of a
                frozen agent off the move (f >= 2); only by B1′, C′ or exact-only hypotheses (f = 1);
  score       = min over κ of margin(κ) - 2·rare(κ), and -1000 for an uncovered key (lower is better).
Metropolis acceptance at a temperature that falls linearly; restarts from the best state after `--patience` steps
without improvement. Every profile with an uncovered key, and every new rare key, is appended to OUT (gzip JSON lines,
the check_profile record plus 'why'); the run's state is checkpointed in OUT.state.json (resumable).

usage: python3 k4/cover_hunt.py OUT.jsonl.gz --seed='{"sets": ..., "vals": ..., "m": ...}' | --seedfile=F.jsonl.gz[:i]
       [--minutes=M] [--K=16] [--T0=2] [--rng=R] [--patience=P]"""
import gzip, json, math, os, random, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cover_check as CC
from cover_screen_run import binary, parse_hit
from check4 import core_domains

PHIW = 'phi(w) of a frozen w off the move'


def key_eval(rec, kr):
    f = rec['f']
    target = CC.COVER if f == 1 else CC.COVER_PLUS
    margin = sum(len(set(mr['lemmas']) & target) for mr in kr['maxima'])
    cov = set(kr['cover'])
    if f >= 2:
        qk = set(q for mr in kr['maxima'] if "C'+" in mr['lemmas'] for q in mr['detail'].get("C'+ q", []))
        rare = cov == {'B+1'} or (cov == {"C'+"} and qk == {PHIW})
        tag = 'only B+1' if cov == {'B+1'} else ("only C'+ with q = phi(w)" if rare else None)
    else:
        exact_only = all(mr['lemmas'].get(l, 0) == 0 for mr in kr['maxima'] for l in mr['lemmas'] if l in target)
        rare = bool(cov) and (cov <= {"B1'", "C'"} or exact_only)
        tag = ('only ' + '+'.join(sorted(cov)) + (' (exact only)' if exact_only else '')) if rare else None
    return margin, rare, tag


def score(rec):
    best = None; tags = []
    for kr in rec.get('keys', []):
        if 'assert' in kr: tags.append('LEMMA-ASSERT'); return -2000, tags
        margin, rare, tag = key_eval(rec, kr)
        s = -1000 if margin == 0 else margin - 2 * rare
        if margin == 0: tags.append('UNCOVERED')
        if tag: tags.append(tag)
        best = s if best is None else min(best, s)
    return best, tags


class Hunt:
    def __init__(self, seed, rng):
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
        p = subprocess.run([self.bin, '-f', '1:99'], input='\n'.join(blocks) + '\n', capture_output=True, text=True,
                           check=True)
        hit = set()
        for line in p.stdout.splitlines():
            if line.startswith('HIT '): hit.add(json.dumps(parse_hit(line, self.n, self.m)['vals']))
        return [st for st in states if json.dumps(self.vals(st)) in hit]

    def evaluate(self, st):
        d = {'sets': self.sets, 'vals': self.vals(st), 'm': self.m}
        rec = CC.check_profile(d, {'fmin': 1, 'fmax': 99, 'verify': False, 'dlk': False})
        if 'keys' not in rec or not rec['keys']: return None, rec, []
        s, tags = score(rec)
        return s, rec, tags


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    out = [a for a in argv if not a.startswith('--')][0]
    if 'seed' in opt: seed = json.loads(opt['seed'])
    else:
        fn, _, idx = opt['seedfile'].partition(':')
        lines = [json.loads(l) for l in gzip.open(fn, 'rt')]
        seed = lines[int(idx or 0)]
    seed = {'sets': seed['sets'], 'vals': seed['vals'], 'm': seed.get('m') or 1 + max(map(max, seed['sets']))}
    rng = random.Random(int(opt.get('rng', 1)))
    K = int(opt.get('K', 16)); T0 = float(opt.get('T0', 2)); minutes = float(opt.get('minutes', 20))
    patience = int(opt.get('patience', 60))
    H = Hunt(seed, rng)
    stf = out + '.state.json'
    stats = {'steps': 0, 'evals': 0, 'screened': 0, 'hits': 0, 'uncovered': 0, 'rare': 0, 'restarts': 0,
             'elapsed': 0.0, 'seen_rare': []}
    cur = tuple(H.cur)
    if os.path.exists(stf):
        sv = json.load(open(stf)); stats = sv['stats']; cur = tuple(sv['cur']); best = (sv['best_s'], tuple(sv['best']))
        rng.seed(sv['rng'] + stats['steps'])
    s0, rec0, tags0 = H.evaluate(cur)
    if s0 is None: s0 = 999
    if not os.path.exists(stf): best = (s0, cur)
    cur_s = s0
    print('# command: python3 k4/cover_hunt.py ' + ' '.join(argv), flush=True)
    print('# seed: n=%d m=%d start score %s tags %s' % (H.n, H.m, s0, tags0), flush=True)
    seen_rare = set(stats['seen_rare'])
    t0 = time.time(); since = 0; budget = minutes * 60 - stats['elapsed']
    fo = gzip.open(out, 'at')
    while time.time() - t0 < budget:
        T = max(0.05, T0 * (1 - (stats['elapsed'] + time.time() - t0) / (minutes * 60)))
        nb = H.neighbours(cur, K); stats['screened'] += len(nb)
        hits = H.screen(nb); stats['hits'] += len(hits)
        cands = []
        for st in hits:
            s, rec, tags = H.evaluate(st); stats['evals'] += 1
            if s is None: continue
            cands.append((s, st))
            interesting = [t for t in tags if t in ('UNCOVERED', 'LEMMA-ASSERT')]
            rk = json.dumps([rec['vals']])
            if interesting or (tags and rk not in seen_rare):
                if 'UNCOVERED' in tags: stats['uncovered'] += 1
                elif 'LEMMA-ASSERT' not in tags: stats['rare'] += 1; seen_rare.add(rk)
                rec['why'] = tags; rec['score'] = s
                fo.write(json.dumps(rec, separators=(',', ':')) + '\n'); fo.flush()
                if interesting: print('FOUND', tags, json.dumps({k: rec[k] for k in ('sets', 'vals', 'm', 'f')}), flush=True)
        stats['steps'] += 1
        if cands:
            s, st = min(cands) if rng.random() < 0.5 else rng.choice(cands)
            if s <= cur_s or rng.random() < math.exp(-(s - cur_s) / T):
                cur, cur_s = st, s
            if s < best[0]: best = (s, st); since = 0
        since += 1
        if since > patience:
            cur, cur_s = best[1], best[0]; since = 0; stats['restarts'] += 1
            if rng.random() < 0.3: cur, cur_s = tuple(H.cur), s0
        if stats['steps'] % 20 == 0:
            stats['seen_rare'] = sorted(seen_rare)
            sv = {'stats': dict(stats, elapsed=stats['elapsed'] + time.time() - t0), 'cur': list(cur), 'best': list(best[1]),
                  'best_s': best[0], 'rng': int(opt.get('rng', 1))}
            json.dump(sv, open(stf + '.tmp', 'w')); os.replace(stf + '.tmp', stf)
    fo.close()
    stats['elapsed'] += time.time() - t0; stats['seen_rare'] = sorted(seen_rare)
    json.dump({'stats': stats, 'cur': list(cur), 'best': list(best[1]), 'best_s': best[0], 'rng': int(opt.get('rng', 1))},
              open(stf, 'w'))
    print('# done: steps %d screened %d hits %d evaluated %d uncovered %d rare %d restarts %d; best score %s at %s' % (
        stats['steps'], stats['screened'], stats['hits'], stats['evals'], stats['uncovered'], stats['rare'],
        stats['restarts'], best[0], H.vals(best[1])))


if __name__ == '__main__':
    main(sys.argv[1:])
