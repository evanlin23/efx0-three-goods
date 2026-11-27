"""Candidate dump rules on (k, p) = (4, 3) instances (k4/p3.md section 3).

State: the picks of a serial-dictatorship order (each agent holds its pick; every pick stays with its agent). The free
goods (not picked) are placed by SAT, restricted by a rule; the question is whether a rule loses completions:
  any      every agent may receive a free good (the exact question: do the picks extend?)
  env      g may go to a valuer of g, or to an agent that envies a valuer of g  (the two-envier rule)
  unenv    g may go to a valuer of g, or to an agent nobody envies
  both     env or unenv
  envonly  g may go only to an envier of a valuer of g (no valuer may keep it)
Envy is in the pick state: i envies j iff v_i(pick_j) > v_i(pick_i) (an agent with no pick envies every holder of one
of its goods). Among the orders whose picks extend, counts the orders each rule loses, and prints the smallest
instances where it does.
    python3 k4/p3/dump_rules.py suite|screen|cores|random [--n=6] [--count=100] [--orders=30] [--seed=1]
"""
import sys, os, random, itertools, json, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *

RULES = ['env', 'unenv', 'both', 'envonly']


def envy_state(I, pk):
    """envies[i] = set of j that i envies, with every agent holding {pick}"""
    E = []
    for i in range(I.n):
        own = I.v[i].get(pk[i], 0) if pk[i] is not None else 0
        E.append({j for j in range(I.n) if j != i and pk[j] is not None and I.v[i].get(pk[j], 0) > own})
    return E


def allowed_sets(I, pk, rule):
    E = envy_state(I, pk)
    envied = set().union(*E) if E else set()
    held = {g for g in pk if g is not None}
    al = {}
    for g in range(I.m):
        if g in held: continue
        val = set(I.V[g])
        envr = {i for i in range(I.n) if E[i] & val}
        unen = set(range(I.n)) - envied
        if rule == 'env': A = val | envr
        elif rule == 'unenv': A = val | unen
        elif rule == 'both': A = val | envr | unen
        elif rule == 'envonly': A = envr
        al[g] = A
    return al


def orders(I, rng, K):
    if I.n <= 4:
        return list(itertools.permutations(range(I.n)))
    return [tuple(rng.sample(range(I.n), I.n)) for _ in range(K)]


def load(src, opt, rng):
    if src == 'suite': return suite_p3()
    if src == 'screen': return screen_p3()
    if src == 'suite4':      # every suite instance with a good of four or more valuers, n <= --maxn
        import p3lib
        return [I for I in p3lib._suite() if I.p() >= 4 and I.n <= int(opt.get('maxn', 8))]
    if src == 'cores':
        L = []                 # --files=4_n4 keeps the lists whose name contains one of the keys; --per=K profiles per core
        for f in core_lists_p3():
            cs = cores_from(f); rng.shuffle(cs)
            if opt.get('files') and not any(k in f for k in opt['files'].split(',')): continue
            for m, sets in cs[:int(opt.get('count', 30))]:
                for _ in range(int(opt.get('per', 1))):
                    L.append(Inst(sets, random_types(rng, sets, m), m, os.path.basename(f)))
        return L
    L = []
    for t in range(int(opt.get('count', 100))):
        rc = random_core43(rng, int(opt.get('n', 6)))
        if rc: L.append(Inst(rc[1], random_types(rng, rc[1], rc[0]), rc[0], f'rand{t}'))
    return L


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1))); K = int(opt.get('orders', 30))
    print('$ python3 k4/p3/dump_rules.py ' + ' '.join(sys.argv[1:]), flush=True)
    L = load(src, opt, rng)
    cnt = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
    for I in L:
        C = Complete(I); seen = set()
        for o in orders(I, rng, K):
            pk = sd(I, o)
            if tuple(pk) in seen: continue
            seen.add(tuple(pk))
            fixed = {g: i for i, g in enumerate(pk) if g is not None}
            cnt['pick vectors'] += 1
            if C.solve(fixed=fixed) is None:
                cnt['no extension'] += 1; continue
            cnt['extends'] += 1
            for r in RULES:
                if C.solve(fixed=fixed, allowed=allowed_sets(I, pk, r)) is None:
                    cnt['lost by ' + r] += 1
                    ex[r].append((I.n, I.m, I.name, o, pk, I.as_json()))
    print(dict(cnt), f'{time.time()-t0:.0f}s', flush=True)
    for r in RULES:
        if ex[r]:
            e = min(ex[r], key=lambda e: (e[0], e[1]))
            print(f'smallest loss of {r}: n={e[0]} m={e[1]} {e[2]} order {e[3]} picks {e[4]}')
            print('   ', json.dumps(e[5]))
