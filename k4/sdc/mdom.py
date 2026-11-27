"""Matching domination (k4/sdc.md §28): is EVERY matching (each agent at most one good it values, no good twice)
value-dominated by a complete EFX0 allocation?  A strengthening of value domination of every order's
serial-dictatorship picks (vdom.py), since SD picks form such a matching.  For each instance: every maximal matching
is tested (a matching below a dominated one is dominated); a failing one is printed.

    python3 k4/sdc/mdom.py screen|suite|special|cores:FILES N SEED|logs
logs: every profile (n <= 5, at most four goods per agent) printed in results/k4_sdc/*.log, the hard cases of the
earlier sections (climb results, counterexamples, failures)."""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from nof_var import SPECIAL
from vdom import dominated


def matchings(E):
    """all inclusion-maximal matchings as tuples Y (Y[i] a good of R_i or None)"""
    out = []
    def rec(i, used, Y):
        if i == E.n:
            # maximal: no agent with None can take a free good
            if all(Y[j] is not None or all(g in used for g in E.R[j]) for j in range(E.n)):
                out.append(tuple(Y))
            return
        any_ = False
        for g in E.R[i]:
            if g not in used:
                any_ = True; rec(i + 1, used | {g}, Y + [g])
        rec(i + 1, used, Y + [None])
    rec(0, frozenset(), [])
    return out


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/mdom.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    elif src == 'logs':
        import re, glob
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try: sets, vals = json.loads(mt.group(1))
                    except Exception: continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4: continue
                    key = json.dumps((sets, vals))
                    if key in seen: continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        if len(sets) > 5: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        ms = matchings(E); bad = [Y for Y in ms if not dominated(E, Y)]
        C['maximal matchings'] += len(ms); C['not dominated'] += len(bad); C['instances with one'] += bool(bad)
        if bad and C['shown'] < 4:
            C['shown'] += 1; print('NOT DOMINATED', name, json.dumps((sets, vals)), 'e.g.', bad[0], len(bad), 'of', len(ms), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
