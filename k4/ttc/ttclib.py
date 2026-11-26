"""Housing-market (TTC / YRMH-IGYT) view of the improving chains of k4/sdc.md §29 (workstream proof/k4-ttc, k4/ttc.md).

The induced market of a serial-dictatorship start Y = SD(pi): every agent is an existing tenant holding its base (its
pick, a single good, or nothing: a newcomer); the junk J (unpicked goods) is the pool of vacant goods; an agent's demand
is its additive valuation over subsets of its <= 4 relevant goods.  A *request* of agent a is an improving option:
  take  : S = B_j + H (the base of another agent j still in the market, plus junk H), S inside R_a, v_a(S) > v_a(B_a);
  pool  : S = H (junk only, a gives up its base), v_a(H) > v_a(B_a).
Adding junk to one's own base is not a request: placing junk is the completion's job (oc_absorb.extends_A).

YRMH-IGYT with set demands ("you request my house, I get your turn"; Abdulkadiroglu-Sonmez 1999 for unit demand):
the highest-priority agent p still in the market is the head; it requests its top *take* option.  The owner j of the
requested base gets the turn and requests its top option (take or pool), and so on:
  - a pool request closes a CHAIN: every agent of the request path takes what it requested; the head's base becomes
    junk.  This is exactly an improving chain of de_free.py (x_0 = the pool requester, x_t = the head);
  - a request for the base of an agent already on the path closes a RING (DF's ring, or a chain whose x_0 takes
    B_{x_t} when the loop closes at the head);
  - an agent with no improving request is assigned its base and leaves; its requester requests again;
  - agents that traded leave the market with their new bases (they can be requested no more).
Junk requested by an agent on the path is reserved for it until it requests again.

Modes: 'one' stops after the first trade; 'head' stops after the first trade that includes the current head (rings
closed on the way are kept); 'full' runs the mechanism until the market is empty; 'rep' ('rephead') repeats 'one'
('head') runs, testing the one-absorber completion before each, from the new state with every agent back in the market.
A preference 'H/I' uses H for the head's request and I for every other agent's.

Preferences over requests (pref):
  val    : the most valuable option (the agent's own preference), ties: fewer goods, then index;
  lean   : the fewest junk goods, then the most valuable;
  minimal: only options whose junk part is inclusion-minimal (no junk good can be dropped), then most valuable;
  small  : the fewest goods in S, then the most valuable;
  minval : the least valuable improving option ("just enough"), ties: fewer goods;
  poolval: a pool request if the agent has one (the most valuable), else the least valuable take request;
  poolmin: a pool request if the agent has one (the least valuable), else the least valuable take request.
Priorities (prio), from the order pi of the start:
  pi, rev (reverse of pi), idx (agent index), danger (frozen agents valuing junk first, then pi),
  revdanger (unfrozen agents first in reverse pi, then the rest in reverse pi), wanted (agents nobody wants first,
  in reverse pi).
"""
import sys, os, json, gzip, random, itertools, collections, time, re, glob
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
import _paths  # noqa: E402  (k4/sdc, k4/de4, k3 on the path)
import de_free as DF  # noqa: E402
from sdclib import Enc  # noqa: E402
from sdc_need import instances  # noqa: E402
from sdc_orders import sd  # noqa: E402
from nof_var import SPECIAL  # noqa: E402
from oc_absorb import extends_A  # noqa: E402

DF.CHAIN_ONLY = True
HMAX = 4
BMAX = 4

# the two instances on which the strict dichotomy of k4/sdc.md §29 fails (refute_dich.py; oc_dich.log, r7)
DICH = [('dich3', [[0, 2, 4, 3], [6, 3, 1], [1, 2, 0, 5]], [[5, 10, 1, 12], [10, 12, 11], [11, 8, 6, 1]], 7),
        ('dich-r7', [[0, 2, 5, 7], [1, 7, 8], [3, 4, 5, 6], [3, 4, 8], [6, 7, 8]],
         [[2, 3, 6, 10], [2, 4, 3], [7, 2, 10, 6], [3, 2, 4], [3, 2, 4]], 9)]

CORES = {
    'n3': 'k4_certs_2.json.gz,k4_certs_3.json.gz',
    'n4': 'k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz',
    'n5': 'k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz',
}


def load_items(src, N=0, seed=0):
    """(name, sets, vals, m) for special | dich | k3:5|6|all (k = 3 cores, N profiles) | screen | suite | logs | cores:FILES (N random profiles, seed) |
    core:n3|n4|n5 (shorthand) | big:NMIN-NMAX (N random instances of oc1_bign.gen)"""
    if src == 'special':
        return list(SPECIAL)
    if src == 'dich':
        return list(DICH)
    if src.startswith('core:'):
        src = 'cores:' + CORES[src[5:]]
    if src.startswith('cores:'):
        rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores)
            items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
        return items
    if src.startswith('k3:'):
        # k = 3: the certified k = 3 cores with n = 5, 6 (results/certs_5_6.json.gz), N random strict balanced profiles
        # in all (a > b > c with a < b + c), as in k4/sdc/oc_k3.py
        rng = random.Random(seed); items = []
        cores = json.load(gzip.open(os.path.join(ROOT, 'results', 'certs_5_6.json.gz')))
        want = src[3:]
        cores = [c for c in cores if want == 'all' or len(c['sets']) == int(want)]
        for t in range(N):
            core = cores[t % len(cores)]; sets = core['sets']; vals = []
            for S in sets:
                while True:
                    a, b, c = sorted(rng.sample(range(1, 30), 3), reverse=True)
                    if a < b + c:
                        break
                perm = list(S); rng.shuffle(perm); d = dict(zip(perm, (a, b, c))); vals.append([d[g] for g in S])
            items.append(('k3r%d' % t, sets, vals, core['m']))
        return items
    if src.startswith('tight:'):
        # tight random k = 4 instances: m in [n, n + 3] goods, so that several agents end without a pick (the shape of
        # the OC1-H counterexample of refute_head.py); degrees 3/4, every good relevant to someone
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        lo, hi = map(int, src[6:].split('-')); items = []
        for t in range(N):
            n = lo + t % (hi - lo + 1); rng = random.Random(seed * 100003 + t)
            m = rng.randint(n, n + 3)
            while True:
                sets = [sorted(rng.sample(range(m), rng.choice([3, 4, 4]))) for _ in range(n)]
                if len(set().union(*map(set, sets))) == m:
                    break
            items.append(('t%d' % t, sets, random_profile(sets, rng), m))
        return items
    if src.startswith('big:'):
        import oc1_bign
        lo, hi = map(int, src[4:].split('-'))
        items = []
        for t in range(N):
            n = lo + t % (hi - lo + 1)
            rng = random.Random(seed * 100003 + t)
            sets, vals, m = oc1_bign.gen(n, rng)
            items.append(('b%d' % t, sets, vals, m))
        return items
    if src == 'logs':
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try:
                        sets, vals = json.loads(mt.group(1))
                    except Exception:
                        continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4:
                        continue
                    key = json.dumps((sets, vals))
                    if key in seen:
                        continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
        return items
    return instances(src)


def base_of(E, Y):
    base = [-1] * E.m
    for i, g in enumerate(Y):
        if g is not None:
            base[g] = i
    return tuple(base)


def val(E, i, S):
    return sum(E.v[i].get(g, 0) for g in S)


def bundles(E, base):
    return DF.bundles(E, base)


def orders_of(n, rng, k=None):
    """every order for n <= 5 (or k sampled orders, always with the identity and its reverse)"""
    if k is None and n <= 5:
        return [list(o) for o in itertools.permutations(range(n))]
    k = k or 12
    out = [list(range(n)), list(range(n))[::-1]]
    while len(out) < k:
        o = list(range(n)); rng.shuffle(o); out.append(o)
    return out


def frozen_set(E, base):
    """frozen agents: base a single good that another agent values above its own base"""
    B = bundles(E, base); n = E.n
    fr = set()
    for j in range(n):
        if len(B[j]) != 1:
            continue
        g = B[j][0]
        for i in range(n):
            if i != j and E.v[i].get(g, 0) > val(E, i, B[i]):
                fr.add(j); break
    return fr


def dangerous_set(E, base):
    J = [g for g in range(E.m) if base[g] < 0]
    return set(j for j in frozen_set(E, base) if any(E.v[j].get(g, 0) > 0 for g in J))


def priority(E, base, pi, prio):
    n = E.n
    if prio == 'pi':
        return list(pi)
    if prio == 'rev':
        return list(pi)[::-1]
    if prio == 'idx':
        return list(range(n))
    D = dangerous_set(E, base); F = frozen_set(E, base)
    if prio == 'danger':
        return [i for i in pi if i in D] + [i for i in pi if i not in D]
    if prio == 'revdanger':
        r = list(pi)[::-1]
        return [i for i in r if i not in F] + [i for i in r if i in F]
    if prio == 'wanted':
        r = list(pi)[::-1]
        return [i for i in r if i not in F] + [i for i in r if i in F]
    raise ValueError(prio)


def options(E, base, a, active, reserved, head):
    """improving requests of agent a: list of (S, owner, H); owner None for a pool request"""
    B = bundles(E, base)
    cur = val(E, a, B[a])
    Ja = [g for g in range(E.m) if base[g] < 0 and g not in reserved and E.v[a].get(g, 0) > 0]
    out = []
    Hs = [H for r in range(min(HMAX, len(Ja)) + 1) for H in itertools.combinations(Ja, r)]
    for j in active:
        if j == a or not B[j]:
            continue
        if any(E.v[a].get(g, 0) == 0 for g in B[j]):
            continue
        for H in Hs:
            S = tuple(B[j]) + H
            if len(S) <= BMAX and val(E, a, S) > cur:
                out.append((S, j, H))
    if not head:
        for H in Hs:
            if H and len(H) <= BMAX and val(E, a, H) > cur:
                out.append((H, None, H))
    return out


def rank(E, a, opts, pref, base):
    if not opts:
        return None
    B = bundles(E, base); cur = val(E, a, B[a])
    if pref == 'val':
        key = lambda o: (-val(E, a, o[0]), len(o[0]), o[1] if o[1] is not None else -1, o[2])
    elif pref == 'lean':
        key = lambda o: (len(o[2]), -val(E, a, o[0]), o[1] if o[1] is not None else -1, o[2])
    elif pref == 'small':
        key = lambda o: (len(o[0]), -val(E, a, o[0]), o[1] if o[1] is not None else -1, o[2])
    elif pref == 'minval':
        key = lambda o: (val(E, a, o[0]), len(o[0]), o[1] if o[1] is not None else -1, o[2])
    elif pref == 'poolval':
        key = lambda o: (o[1] is not None, -val(E, a, o[0]) if o[1] is None else val(E, a, o[0]), len(o[0]),
                         o[1] if o[1] is not None else -1, o[2])
    elif pref == 'poolmin':
        key = lambda o: (o[1] is not None, val(E, a, o[0]), len(o[0]), o[1] if o[1] is not None else -1, o[2])
    elif pref == 'minimal':
        def minimal(o):
            S, j, H = o
            base_part = [g for g in S if g not in H]
            return all(val(E, a, base_part + [h for h in H if h != g]) <= cur for g in H)
        opts = [o for o in opts if minimal(o)] or opts
        key = lambda o: (-val(E, a, o[0]), len(o[0]), o[1] if o[1] is not None else -1, o[2])
    else:
        raise ValueError(pref)
    return min(opts, key=key)


def yrmh(E, base, pi, pref, prio, mode, trace=None, max_trades=None):
    """run YRMH-IGYT with set demands from base; returns (final base, number of trades, list of trades)"""
    n = E.n
    hpref, ipref = (pref.split('/') + [pref])[:2] if '/' in pref else (pref, pref)
    base = list(base)
    active = set(range(n))
    order = priority(E, tuple(base), pi, prio)
    trades = []
    path = []      # list of [agent, request or None]
    reserved = set()
    while True:
        if not path:
            heads = [a for a in order if a in active]
            if not heads:
                break
            path = [[heads[0], None]]
        a = path[-1][0]
        if path[-1][1] is not None:
            for g in path[-1][1][2]:
                reserved.discard(g)
            path[-1][1] = None
        opts = options(E, tuple(base), a, active, reserved, head=(len(path) == 1))
        best = rank(E, a, opts, hpref if len(path) == 1 else ipref, tuple(base))
        if best is None:
            # a keeps its base and leaves; its requester requests again
            active.discard(a); path.pop()
            if path and path[-1][1] is not None:
                for g in path[-1][1][2]:
                    reserved.discard(g)
                path[-1][1] = None
            continue
        path[-1][1] = best
        for g in best[2]:
            reserved.add(g)
        S, j, H = best
        on_path = [k for k, (b, _) in enumerate(path) if b == j]
        if j is None or on_path:
            # execute: chain (pool) over the whole path, or ring from position on_path[0]
            start = 0 if j is None else on_path[0]
            cyc = path[start:]
            B = bundles(E, tuple(base))
            nb = list(base)
            if j is None:
                for g in B[path[0][0]]:
                    nb[g] = -1           # the head's base becomes junk
            for agent, req in cyc:
                for g in B[agent]:
                    if nb[g] == agent:
                        nb[g] = -1
            for agent, req in cyc:
                for g in req[0]:
                    nb[g] = agent
            # goods of B_owner taken by the receivers: already reassigned above (owner's goods set to -1 first)
            trades.append(('chain' if j is None else 'ring', [x for x, _ in cyc], [tuple(r[0]) for _, r in cyc]))
            if trace is not None:
                trace.append((trades[-1], tuple(nb)))
            base = nb
            for agent, req in cyc:
                active.discard(agent)
                for g in req[2]:
                    reserved.discard(g)
            path = path[:start]
            if path and path[-1][1] is not None:
                for g in path[-1][1][2]:
                    reserved.discard(g)
                path[-1][1] = None
            if mode == 'one' or (max_trades and len(trades) >= max_trades):
                break
            if mode == 'head' and start == 0:
                break
            continue
        path.append([j, None])
    return tuple(base), trades


def run_mech(E, base, pi, pref, prio, mode, rep_limit=None):
    """'one' / 'full': one run; 'rep': repeat 'one' runs until a one-absorber completion exists or no trade happens"""
    if mode in ('one', 'full', 'head'):
        b, tr = yrmh(E, base, pi, pref, prio, mode)
        return b, len(tr), extends_A(E, b, 1)
    inner = 'head' if mode == 'rephead' else 'one'
    b = base; k = 0
    lim = rep_limit or 4 * E.n
    while True:
        if extends_A(E, b, 1):
            return b, k, True
        if k >= lim:
            return b, k, False
        b2, tr = yrmh(E, b, pi, pref, prio, inner)
        if not tr:
            return b, k, False
        b = b2; k += len(tr)


def dominated(E, base):
    """MD test: some complete EFX0 allocation X gives every agent i at least v_i(B_i) (SAT on sdclib's encoding, the
    bundle-indicator variables y of E restricted to subsets worth at least v_i(B_i))"""
    from pysat.solvers import Cadical153
    B = bundles(E, base)
    cl = list(E.cl)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        u = val(E, i, B[i])
        for S, y in E.y[i].items():
            if E.val(i, S) < u:
                cl.append([-y])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


def extends_owner(E, base, o):
    """one-absorber completion with a prescribed absorber o (o = None: no absorber, every agent at most one junk
    good): every agent other than o receives at most one good of the junk of base"""
    from pysat.solvers import Cadical153
    cl = list(E.cl)
    J = [g for g in range(E.m) if base[g] < 0]
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0:
            cl.append([E.x[g][base[g]]])
    for i in range(E.n):
        if i == o:
            continue
        for g, h in itertools.combinations(J, 2):
            cl.append([-E.x[g][i], -E.x[h][i]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


def iter_chains_path(E, base):
    """the improving chains of de_free.iter_chains (same moves, generated lazily), yielding (state, path) with
    path = (x_0, ..., x_t)"""
    n = E.n; B = bundles(E, base); J = [g for g in range(E.m) if base[g] < 0]
    v = lambda i, S: val(E, i, S)
    H_ = DF.HMAX; BM = DF.BMAX

    def subs(xs):
        for r in range(min(H_, len(xs)) + 1):
            yield from itertools.combinations(xs, r)

    def ext(path, usedH, assign):
        x_t = path[-1]
        pool0 = [g for g in J if g not in usedH and E.v[path[0]].get(g, 0) > 0] + \
                ([g for g in B[x_t] if E.v[path[0]].get(g, 0) > 0] if len(path) > 1 else [])
        for H0 in subs(pool0):
            if not H0:
                continue
            newb0 = (list(B[path[0]]) if len(path) == 1 else []) + list(H0)
            if len(newb0) > BM or v(path[0], newb0) <= v(path[0], B[path[0]]):
                continue
            nb = list(base)
            if len(path) > 1:
                for g in B[x_t]:
                    nb[g] = -1
                for i in range(len(path) - 1, 0, -1):
                    for g in B[path[i - 1]]:
                        nb[g] = path[i]
                    for g in assign[i]:
                        nb[g] = path[i]
            for g in H0:
                nb[g] = path[0]
            yield tuple(nb), tuple(path)
        if len(path) >= n or not B[x_t]:
            return
        for y in range(n):
            if y in path:
                continue
            free = [g for g in J if g not in usedH and E.v[y].get(g, 0) > 0]
            for H in subs(free):
                nby = list(B[x_t]) + list(H)
                if len(nby) > BM or v(y, nby) <= v(y, B[y]):
                    continue
                yield from ext(path + [y], usedH | set(H), {**assign, len(path): H})

    for x in range(n):
        yield from ext([x], frozenset(), {})


def extends_A_pickless(E, base, A):
    """one-absorber completion in which agents with an empty base are not counted: at most A agents with a nonempty
    base receive two or more junk goods; agents without a base receive any number"""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    cl = list(E.cl); top = E.top
    J = [g for g in range(E.m) if base[g] < 0]
    has = set(base[g] for g in range(E.m) if base[g] >= 0)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0:
            cl.append([E.x[g][base[g]]])
    bigs = []
    for i in range(E.n):
        if i not in has:
            continue
        top += 1; b = top; bigs.append(b)
        for g, h in itertools.combinations(J, 2):
            cl.append([-E.x[g][i], -E.x[h][i], b])
    enc = CardEnc.atmost(lits=bigs, bound=A, top_id=top, encoding=EncType.seqcounter) if bigs else None
    if enc:
        cl.extend(enc.clauses)
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok
