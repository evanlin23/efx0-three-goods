"""Sampling test of Conjectures T'_k and T-E (k4/k3_oc1.md §12) on random ranking profiles of a source (e.g. the n = 7
cores, certs7:12), every order's draft.  On each hard perfect draft (exact lb2 fails):
  T'_k   some rotation into a terminal completes with owner none or k (tprime_k.check);
  T-E    rules over the valid Rule E rotations (te_rules.results): some / every / every least-omega / every most-T';
  any    every valid Rule E rotation completes with some owner (exact lb2); also every least-omega' one.
    python3 k4/k3oc1/te_sample.py SOURCE PROFILES_PER_HYPERGRAPH SEED [SHARD NSHARDS]"""
import sys, os, json, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of
from lbtest import upgrade, parts, lb2
from t2k_e import valid_rotations, topo
from te_rules import results
from tprime_k import check
from oc1_fast import drafts
from oc1_k3 import profiles
from oc1_max import sources as hypergraphs

src, P, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
shard, nsh = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (0, 1)
rng = random.Random(seed * 1000 + shard); C = collections.Counter(); t0 = time.time()
print('$ python3 k4/k3oc1/te_sample.py', *sys.argv[1:], flush=True)
for ci, (sets, m) in enumerate(hypergraphs(src, rng)):
    if ci % nsh != shard: continue
    C['hypergraphs'] += 1
    for rk in profiles(sets, P, rng):
        C['profiles'] += 1
        for Y in drafts(rk, len(sets)):
            if any(g is None for g in Y): continue
            C['perfect drafts'] += 1
            if lb2(rk, m, base_of(Y, m)): continue
            nT = len(parts(rk, m, upgrade(rk, m, base_of(Y, m)))[5]); tag = '|T| %d: ' % nT
            C[tag + 'hard perfect'] += 1
            line = json.dumps([list(r) for r in rk]) + ' %d picks %s' % (m, Y)
            r = check(rk, m, Y, C, tag + "T'_k ")
            if r in ('any', 'fail'): print("T'K-" + r, line, flush=True)
            R = results(rk, m, topo(rk, Y), Y)
            if not R:
                C[tag + 'T-E no valid rotation'] += 1; print('NOROT', line, flush=True); continue
            for name, sel in (('some', None), ('every', R), ('every least-omega', [x for x in R if x['om'] == min(y['om'] for y in R)]),
                              ('every most-T', [x for x in R if x['T'] == max(y['T'] for y in R)])):
                ok = any(x['ok'] for x in R) if sel is None else all(x['ok'] for x in sel)
                C[tag + 'T-E (N/E/K) %s %s' % (name, ok)] += 1
                if not ok and name in ('some', 'every least-omega'): print('TE-' + name.replace(' ', '_'), line, flush=True)
            VR = valid_rotations(rk, m, topo(rk, Y), Y); ex = [bool(lb2(rk, m, nb)) for k, p, nb in VR]
            anyok = all(ex)
            C[tag + 'T-E any owner, every rotation %s' % anyok] += 1
            if not anyok: print('TE-any', line, flush=True)
            mo = min(x['om'] for x in R)
            lw = all(e_ for x, e_ in zip(R, ex) if x['om'] == mo)
            C[tag + 'T-E any owner, every least-omega rotation %s' % lw] += 1
            C[tag + 'least omega\' <= 0 %s' % (mo <= 0)] += 1
            if not lw: print('TE-anyleastomega', line, flush=True)
    if C['hypergraphs'] % 20 == 0: print('# progress', C['hypergraphs'], 'hypergraphs', round(time.time() - t0), 's', flush=True)
for k in sorted(C): print(k, C[k])
print('time', round(time.time() - t0), 's')
