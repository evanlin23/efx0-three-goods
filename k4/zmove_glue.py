#!/usr/bin/env python3
"""Glued seeds for the ZMOVE hunt (workstream compute/k4-zmove). EVIDENCE tooling.

Two profiles A, B (from the lists given) are glued by identifying --share=s goods of A with s goods of B (s = 1 or 2;
B's other goods are renamed after A's), keeping both value vectors: n = n_A + n_B agents. A glued profile is kept if its
sets form a k = 4 core (k4/check4.is_core), main's model.Inst.core_violations() is empty (strictly balanced, the
private-goods conditions) and the values are strict, n <= --maxn, and k4/cover_screen.c finds a key with def* > 0
(f >= 1). Each kept profile is scored by k4/zmove_hunt.score (higher = closer to a ZMOVE failure) and written to OUT
(gzip JSON lines: id, sets, vals, m, src, score, margin of its hardest key), best first.
usage: python3 k4/zmove_glue.py OUT.jsonl.gz --A=LIST --B=LIST [--share=1] [--pairs=200] [--maxn=6] [--rng=1]
LIST: gzip JSON lines or a JSON list of {sets, vals, m}; k4/zmove_check.py outputs work (their keys are ignored)."""
import gzip, json, os, random, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import check4
import model as M
import zmove_hunt as ZH
from cover_screen_run import binary, parse_hit


def load(fn):
    if fn.endswith('.jsonl.gz') or fn.endswith('.jsonl'):
        L = []
        for l in (gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)):
            try: L.append(json.loads(l))
            except ValueError: break
    else:
        L = json.load(gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))
    return [{'sets': d['sets'], 'vals': d['vals'], 'm': d.get('m') or 1 + max(map(max, d['sets'])),
             'src': d.get('id') or d.get('src')} for d in L if 'sets' in d and 'vals' in d]


def glue(A, B, gA, gB):
    relab, nxt = {}, A['m']
    for g in range(B['m']):
        if g in gB: relab[g] = gA[gB.index(g)]
        else: relab[g] = nxt; nxt += 1
    sets = [list(S) for S in A['sets']] + [[relab[g] for g in S] for S in B['sets']]
    if any(len(set(S)) != len(S) for S in sets): return None
    return {'sets': sets, 'vals': [list(v) for v in A['vals']] + [list(v) for v in B['vals']], 'm': nxt}


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    out = [a for a in argv if not a.startswith('--')][0]
    A = load(opt['A']); B = load(opt['B'])
    s = int(opt.get('share', 1)); pairs = int(opt.get('pairs', 200)); maxn = int(opt.get('maxn', 6))
    rng = random.Random(int(opt.get('rng', 1)))
    cand = []; seen = set(); tries = 0
    while len(cand) < pairs and tries < pairs * 200:
        tries += 1
        a, b = rng.choice(A), rng.choice(B)
        if len(a['sets']) + len(b['sets']) > maxn: continue
        gA = rng.sample(range(a['m']), s); gB = rng.sample(range(b['m']), s)
        d = glue(a, b, gA, gB)
        if d is None: continue
        k = json.dumps([d['sets'], d['vals']])
        if k in seen: continue
        seen.add(k)
        ok, _ = check4.is_core(len(d['sets']), d['m'], d['sets'], False)
        if not ok: continue
        I = M.Inst(d['sets'], d['vals'], d['m'])
        if I.core_violations() or not I.strict(): continue
        d['src'] = 'glue(%s @%s, %s @%s)' % (a['src'], gA, b['src'], gB)
        cand.append(d)
    print('# command: python3 k4/zmove_glue.py ' + ' '.join(argv))
    print('# %d glued cores with core profiles (from %d tries)' % (len(cand), tries), flush=True)
    b = binary(); blocks = []
    for d in cand:
        blocks.append('%d %d' % (len(d['sets']), d['m']))
        for S, v in zip(d['sets'], d['vals']):
            blocks.append('%d %s 1' % (len(S), ' '.join(map(str, S)))); blocks.append(' '.join(map(str, v)))
        blocks.append('0 1')
    p = subprocess.run([b, '-f', '1:99'], input='\n'.join(blocks) + '\n', capture_output=True, text=True, check=True)
    hitv = set()
    for line in p.stdout.splitlines():
        if line.startswith('HIT '):
            agents = line.split(None, 5)[5]
            n = agents.count('[')
            h = parse_hit(line, n, None)
            hitv.add(json.dumps([h['sets'], h['vals']]))
    kept = [d for d in cand if json.dumps([d['sets'], d['vals']]) in hitv]
    print('# %d with a key of def* > 0' % len(kept), flush=True)
    res = []
    for d in kept:
        rec, _ = ZH.ZC.check_profile(d, ZH.OPT)
        if not rec.get('keys'): continue
        sc, bk = ZH.score(rec)
        res.append(dict(d, score=sc, margin=bk[0]['margin'], nrep=bk[1], f=rec['f'], n=rec['n']))
    res.sort(key=lambda r: -r['score'])
    with gzip.open(out, 'wt') as fo:
        for i, r in enumerate(res):
            r['id'] = 'glue-%d' % i
            fo.write(json.dumps(r) + '\n')
    import collections
    print('# scored %d; margins: %s; best: %s' % (len(res), dict(collections.Counter(r['margin'] for r in res)),
                                                [(r['score'], r['margin'], r['nrep'], r['n'], r['f']) for r in res[:10]]))


if __name__ == '__main__':
    main(sys.argv[1:])
