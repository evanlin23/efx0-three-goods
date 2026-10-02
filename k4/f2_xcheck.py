#!/usr/bin/env python3
"""Second implementation for step 1 and 2 of k4/f2.md (workstream proof/k4-f2): the T3-stage states with f >= 2 and
DL_RT4 there, from main's C tool k4/dlrt4.c (compute/k4-rt4; its own 𝒫, deficit and RT4 move kinds, no model.py), compared
state by state with k4/f2_shapes.py's dumps (model.py + k4/dl2_classify.py + k4/dl2_relations.py + k4/f2_lib.py).

For every profile of the inputs (the same deduplicated list as k4/f2_shapes.py, same sources and --chunk slicing), dlrt4.c
-s prints every state (min-frozen P with def(P) > 0) with the flags t1 t2 t3p t3h t4 (some improving move of that
kind). A state with f >= 2 is at the T3 stage iff t1 = t2 = t4 = 0; DL_RT4 fails there iff also t3p = t3h = 0. The
script checks that this set of states equals the set of T3-stage states in the f2_shapes dumps (bases, deficit), and
that the T3 flag agrees with the presence of an improving plain (T3) move there (a repair with W = ∅ in the dumps).
dlrt4.c knows no (T3⁺) move: its T3-stage states without a T3 flag are the DL_RT4 failures.

usage: python3 k4/f2_xcheck.py SOURCE ... --dumps='GLOB[,GLOB...]' [--chunk=K/C] [--exclude-ids=...] (as f2_shapes.py)"""
import collections, glob, gzip, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f2_shapes import collect
from dlrt4_ref import build, block, c_parse


def main(argv):
    srcs = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    print('# command: python3 k4/f2_xcheck.py ' + ' '.join(argv), flush=True)
    mine = {}
    for fn in sorted(f for pat in opt['dumps'].split(',') for f in glob.glob(pat)):
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            key = json.dumps([r['sets'], r['vals']])
            mine.setdefault(key, {})[tuple(tuple(b) for b in r['Bs'])] = (r['def'], any(rp['k'] == 0 for rp in r['reps']))
    items = [(d, l) for d, l in collect(srcs, opt) if len(d['sets']) <= int(opt.get('nmax', 6))]   # as f2_shapes.py
    brt, sha = build(os.path.join(HERE, 'dlrt4.c'))
    print('# dlrt4.c sha256 %s; %d profiles; %d profiles with T3-stage states in the dumps' % (sha, len(items), len(mine)),
          flush=True)
    cnt = collections.Counter()
    CH = 200
    for c0 in range(0, len(items), CH):
        chunk = [d for d, _ in items[c0:c0 + CH]]
        inp = ''.join(block(d, k) for k, d in enumerate(chunk))
        out = subprocess.run([brt, '-s'], input=inp, capture_output=True, text=True, check=True).stdout
        C = c_parse(out, [d['sets'] for d in chunk])
        assert len(C) == len(chunk)
        for d, (_, _, states) in zip(chunk, C):
            cnt['profiles'] += 1
            key = json.dumps([d['sets'], d['vals']])
            cst = {}
            for Bs, s in states.items():
                if s['f'] < 2: continue
                cnt['C: f>=2 def>0 states'] += 1
                if s['t1'] or s['t2'] or s['t4']: continue
                cst[Bs] = (s['d'], bool(s['t3p'] or s['t3h']))
            m = mine.get(key, {})
            cnt['C: T3-stage states'] += len(cst); cnt['f2_shapes: T3-stage states'] += len(m)
            cnt['C: DL_RT4 failures at f >= 2'] += sum(1 for v in cst.values() if not v[1])
            if cst != m:
                cnt['MISMATCH profiles'] += 1
                print('MISMATCH', json.dumps(d), sorted(set(cst.items()) ^ set(m.items()))[:4], flush=True)
            if m: cnt['profiles with T3-stage states'] += 1
    print('# ' + ', '.join('%s %d' % kv for kv in sorted(cnt.items())))


if __name__ == '__main__':
    main(sys.argv[1:])
