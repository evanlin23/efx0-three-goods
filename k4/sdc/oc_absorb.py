"""OC with a one-absorber completion (k4/sdc.md §29).  The free completion of de_free.py lets any number of agents take
junk.  Here the completion may give at most A agents two or more junk goods (every other agent at most one), with
A = 1 the shape of LB4r's and Draft and Exchange's completions (one owner or finisher).  For every order: the least
number of improving chains (0 or 1, chains of de_free.py) after which such a completion exists.  With OC_A2=a2 the
state after the chain must have a completion with at most a2 absorbers instead (OC_A2=0: the dichotomy of §29).

    python3 k4/sdc/oc_absorb.py screen|suite|special|logs|cores:FILES N SEED [A]"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

DF.CHAIN_ONLY = True


def extends_A(E, base, A):
    cl = list(E.cl); top = E.top
    J = [g for g in range(E.m) if base[g] < 0]
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0: cl.append([E.x[g][base[g]]])
    bigs = []
    for i in range(E.n):
        top += 1; b = top; bigs.append(b)
        for g, h in itertools.combinations(J, 2):
            cl.append([-E.x[g][i], -E.x[h][i], b])
    enc = CardEnc.atmost(lits=bigs, bound=A, top_id=top, encoding=EncType.seqcounter)
    cl.extend(enc.clauses)
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    A2 = int(os.environ.get('OC_A2', '-1'))
    A = int(sys.argv[-1]) if sys.argv[-1].isdigit() and len(sys.argv) in (3, 5) and not (src.startswith('cores:') and len(sys.argv) == 4) else 1
    if A2 < 0: A2 = A
    print('$ python3 k4/sdc/oc_absorb.py', *sys.argv[1:], '(OC_A2=%d)' % A2, flush=True)
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
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); C['instances'] += 1; res = {}
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y not in res:
                base = [-1] * m
                for i, g in enumerate(Y):
                    if g is not None: base[g] = i
                base = tuple(base)
                if extends_A(E, base, A): res[Y] = 0
                elif any(extends_A(E, b2, A2) for b2 in DF.moves(E, base)): res[Y] = 1
                else: res[Y] = None
            C['starts'] += 1; C['start: chains needed %s' % res[Y]] += 1
        bad = [Y for Y, d in res.items() if d is None]
        C['instances with a start not repaired'] += bool(bad)
        if bad and C['shown'] < 4:
            C['shown'] += 1; print('NOT REPAIRED', name, json.dumps((sets, vals)), 'picks', bad[0], flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
