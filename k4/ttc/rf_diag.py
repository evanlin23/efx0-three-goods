"""Which receiver-first order (k4/ttc.md §14.9): why the candidate rules of rf_rules.py fail on the n = 5 exports, and
the coordinator's automorphism-amended every-form.

For a failing start Y (a perfect or maximum serial-dictatorship start where OC1 fails) and each receiver u:
  - ROT:  SD(u, o - u) for the first listed order o;
  - YRMH: You-Request-My-House-I-Get-Your-Turn from the first listed order (rf_rules.yrmh);
  - every u-first order: all (n - 1)! orders (u, ...), their distinct outcomes Z, each classified as
        'pickless'  (Z leaves more agents without a pick than Y does: not a maximum matching),
        'image'     (Z is the image of Y under an automorphism of the instance: agent and good permutations preserving
                     every value; the twin swap is one),
        'ok'        (OC1 holds at Z: the picks complete or one official move repairs; raw checker
                     k4/sdc/oc1_mc2_rand.Inst.check), or 'fail'.
    AUT-every: every u-first outcome that is neither pickless nor an image is ok (the coordinator's amended form);
    RF-exists: some u-first outcome is ok and not pickless.
For ROT and YRMH the outcome is classified the same way.  Starts where a rule fails are dumped (DUMP.jsonl).

    python3 k4/ttc/rf_diag.py export FILE.json.gz STRIDE DUMP.jsonl
    python3 k4/ttc/rf_diag.py jsonl FILE.jsonl                  (rows with sets, vals, picks)
    python3 k4/ttc/rf_diag.py rf5                               (ksens's k = 5 twin instance)

Promotion rules (promote_sd), from the first listed order o and from every listed order:
  - YRMH-L: YRMH-IGYT plus 'you take my last house, I get your turn' (an agent whose last available good the head is
    about to take moves to the head first);
  - ROT-L:  the rotation (u, o - u) with the last-house promotion only;
  - YRMH-F, ROT-F (first listed order): the feasibility-guarded forms (feasible_sd), maximum by the pointer lemma.
For the 'every listed o' rules the counts 'ok for every / some receiver' range over all (receiver, listed order) pairs."""
import sys, os, gzip, json, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'sdc')); sys.path.insert(0, HERE)
from oc1_mc2_rand import Inst
from rf_rules import receivers, yrmh


def matching(I, agents, avail):
    """a maximum matching of agents into the available goods (Kuhn's algorithm, agents in the given order)"""
    match = {}

    def aug(a, seen):
        for g in sorted(I.R[a] & avail, key=lambda h: -I.v[a][h]):
            if g not in seen:
                seen.add(g)
                if g not in match or aug(match[g], seen):
                    match[g] = a
                    return True
        return False
    for a in agents:
        aug(a, set())
    return match            # good -> agent


def feasible_sd(I, Y, queue, eject=True):
    """YRMH-F (eject=True) / ROT-F (eject=False): SD along a dynamic queue that keeps the outcome maximum.
    size = |Y| (a maximum matching).  Before the head a takes its best available good g, check that the agents behind
    it can still be matched so that the outcome reaches size; if not, follow the pointer chain of a reference maximum
    matching M of the remaining market (fixed for this step): a -> g -> M-partner c of g -> c's best -> ..., and let
    the first agent on the chain whose best good is feasible pick first ('you request my house in M, I get your
    turn').  The pointer lemma (k4/ttc.md §14.9) says such an agent exists when the state is feasible.  With eject,
    an agent b still waiting whose start pick Y_b is taken moves to the head (YRMH-IGYT).  Returns the SD outcome
    and its realized order; ('stuck', ...) if no agent on the chain is feasible (the state was infeasible)."""
    size = sum(y is not None for y in Y); holder = {Y[i]: i for i in range(I.n) if Y[i] is not None}
    allg = set(range(I.m)); queue = list(queue); taken = set(); picks = [None] * I.n; order = []
    while queue:
        avail = allg - taken; done = sum(p is not None for p in picks)
        M = matching(I, queue, avail); partner = M
        a = queue[0]; chain = []
        while True:
            av = I.R[a] & avail
            if not av:
                break
            g = max(av, key=lambda h: I.v[a][h])
            rest = [c for c in queue if c != a]
            if done + 1 + len(matching(I, rest, avail - {g})) >= size:
                break
            if a in chain:
                return ('stuck',), tuple(order)
            chain.append(a); c = partner.get(g)
            if c is None or c == a:
                return ('stuck',), tuple(order)
            a = c
        queue.remove(a); order.append(a)
        av = I.R[a] & avail
        if not av:
            continue
        g = max(av, key=lambda h: I.v[a][h]); picks[a] = g; taken.add(g)
        b = holder.get(g)
        if eject and b is not None and b != a and b in queue:
            queue.remove(b); queue.insert(0, b)
    return tuple(picks), tuple(order)


def promote_sd(I, Y, queue, eject=True, last=True):
    """SD along a dynamic queue.  last: when the head's best available good g is the last available good of an agent c
    still in the queue, c moves to the head and picks first ('you take my last house, I get your turn').  eject: when
    the head takes Y_b for an agent b still in the queue, b moves to the head (YRMH-IGYT).  The outcome is the SD
    outcome of the realized order, which is returned too."""
    holder = {Y[i]: i for i in range(I.n) if Y[i] is not None}
    queue = list(queue); taken = set(); picks = [None] * I.n; order = []
    while queue:
        a = queue[0]
        av = [g for g in I.R[a] if g not in taken]
        if not av:
            queue.pop(0); order.append(a); continue
        g = max(av, key=lambda h: I.v[a][h])
        if last and len(av) > 1:        # a head with no other option takes g (two agents left with only g: no loop)
            cs = [c for c in queue[1:] if [h for h in I.R[c] if h not in taken] == [g]]
            if cs:
                queue.remove(cs[0]); queue.insert(0, cs[0]); continue
        queue.pop(0); order.append(a); picks[a] = g; taken.add(g)
        b = holder.get(g)
        if eject and b is not None and b != a and b in queue:
            queue.remove(b); queue.insert(0, b)
    return tuple(picks), tuple(order)


def automorphisms(I):
    """agent permutations pi admitting a good permutation tau with v_{pi(i)}(tau(g)) = v_i(g) for all i, g"""
    n = I.n; col = {g: tuple(I.v[i].get(g, 0) for i in range(n)) for g in range(I.m)}
    base = collections.Counter(col.values()); out = []
    for pi in itertools.permutations(range(n)):
        inv = [0] * n
        for i in range(n):
            inv[pi[i]] = i
        cp = {g: tuple(col[g][inv[j]] for j in range(n)) for g in range(I.m)}
        if collections.Counter(cp.values()) == base:
            out.append((pi, cp, col))
    return out


def is_image(auts, Y, Z):
    for pi, cp, col in auts:
        if all((Y[i] is None and Z[pi[i]] is None) or
               (Y[i] is not None and Z[pi[i]] is not None and col[Z[pi[i]]] == cp[Y[i]]) for i in range(len(Y))):
            return True
    return False


def classify(I, Y, Z, size, auts, cache):
    if Z in cache:
        return cache[Z]
    if sum(z is not None for z in Z) < size:
        c = 'pickless'
    elif is_image(auts, Y, Z):
        c = 'image'
    else:
        c = 'ok' if I.check(Z) != 'OC1 fails' else 'fail'
    cache[Z] = c
    return c


def test(sets, vals, Y, orders, recs):
    I = Inst(sets, vals); size = sum(y is not None for y in Y); auts = automorphisms(I); cache = {}
    R = collections.Counter(); rec = {'sets': sets, 'vals': vals, 'picks': list(Y), 'orders': orders, 'per': {}}
    R['starts'] += 1; R['starts with %d receivers' % len(recs)] += 1
    if len(auts) > 1:
        R['starts with a nontrivial automorphism'] += 1
    bad = False; agg = collections.defaultdict(list)
    for u in recs:
        o = orders[0]
        Zr = I.sd([u] + [a for a in o if a != u]); Zy, ordy = yrmh(I, Y, o, u)
        cr = classify(I, Y, Zr, size, auts, cache); cy = classify(I, Y, Zy, size, auts, cache)
        q = [u] + [a for a in o if a != u]
        Zl, ordl = promote_sd(I, Y, q, eject=True, last=True); cl_ = classify(I, Y, Zl, size, auts, cache)
        Zrl, ordrl = promote_sd(I, Y, q, eject=False, last=True); crl = classify(I, Y, Zrl, size, auts, cache)
        agg['YRMH-L'].append(cl_); agg['ROT-L'].append(crl)
        Zf, ordf = feasible_sd(I, Y, q); Zrf, ordrf = feasible_sd(I, Y, q, eject=False)
        cf = 'stuck' if Zf == ('stuck',) else classify(I, Y, Zf, size, auts, cache)
        crf = 'stuck' if Zrf == ('stuck',) else classify(I, Y, Zrf, size, auts, cache)
        agg['YRMH-F'].append(cf); agg['ROT-F'].append(crf)
        if (ordf and ordf[0] != u) or (ordrf and ordrf[0] != u):
            R['  NOTE: a feasibility rule did not put u first (the top good of u is in no maximum matching)'] += 1
        if ordl[0] != u or ordrl[0] != u:
            R['  ERROR: a promotion rule did not put u first'] += 1
        for o2 in orders[1:]:       # every listed order, for the two promotion rules
            q2 = [u] + [a for a in o2 if a != u]
            agg['YRMH-L every listed o'].append(classify(I, Y, promote_sd(I, Y, q2)[0], size, auts, cache))
            agg['ROT-L every listed o'].append(classify(I, Y, promote_sd(I, Y, q2, eject=False)[0], size, auts, cache))
        agg['YRMH-L every listed o'].append(cl_); agg['ROT-L every listed o'].append(crl)
        outs = {}
        for rest in itertools.permutations([a for a in range(I.n) if a != u]):
            Z = I.sd((u,) + rest)
            outs.setdefault(Z, classify(I, Y, Z, size, auts, cache))
        cl = collections.Counter(outs.values())
        aut_every = all(c in ('pickless', 'image', 'ok') for c in outs.values())
        exists = 'ok' in outs.values()
        agg['ROT'].append(cr); agg['YRMH'].append(cy); agg['AUT-every'].append(aut_every); agg['RF-exists'].append(exists)
        R['  u-first outcomes per receiver: %d distinct' % len(outs)] += 1
        for c, k in cl.items():
            R['  u-first outcomes classified %s (total)' % c] += k
        rec['per'][u] = {'ROT': [list(Zr), cr], 'YRMH': [list(Zy), cy, list(ordy)], 'YRMH-L': [list(Zl), cl_, list(ordl)],
                         'ROT-L': [list(Zrl), crl, list(ordrl)], 'YRMH-F': [list(Zf), cf, list(ordf)],
                         'ROT-F': [list(Zrf), crf, list(ordrf)],
                         'u-first': [[list(Z), c] for Z, c in outs.items()]}
        if cr != 'ok' or cy != 'ok' or cl_ != 'ok' or crl != 'ok' or cf != 'ok' or crf != 'ok' or not aut_every:
            bad = True
    for rule in ('ROT', 'YRMH', 'YRMH-L', 'ROT-L', 'YRMH-L every listed o', 'ROT-L every listed o', 'YRMH-F', 'ROT-F'):
        for u_c in agg[rule]:
            R['%s outcome: %s' % (rule, u_c)] += 1
        R['%s: ok for every receiver' % rule] += all(c == 'ok' for c in agg[rule])
        R['%s: ok for some receiver' % rule] += any(c == 'ok' for c in agg[rule])
    R['ROT or YRMH ok, every receiver'] += all(a == 'ok' or b == 'ok' for a, b in zip(agg['ROT'], agg['YRMH']))
    R['ROT, else YRMH when ROT is pickless: ok, every receiver'] += all(
        (b == 'ok') if a == 'pickless' else (a == 'ok') for a, b in zip(agg['ROT'], agg['YRMH']))
    R['AUT-every: every receiver'] += all(agg['AUT-every']); R['AUT-every: some receiver'] += any(agg['AUT-every'])
    R['RF-exists: every receiver'] += all(agg['RF-exists']); R['RF-exists: some receiver'] += any(agg['RF-exists'])
    return R, (rec if bad else None)


def job(a):
    R, rec = test(*a[:5])
    if rec:
        rec['list'], rec['idx'] = a[5], a[6]
    return R, rec


if __name__ == '__main__':
    print('$ python3 k4/ttc/rf_diag.py', *[os.path.basename(x) for x in sys.argv[1:]], flush=True)
    if sys.argv[1] == 'rf5':
        S = [[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]]
        V = [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]]
        I = Inst(S, V); Y = (6, 5, 4, 3)
        orders = [list(o) for o in itertools.permutations(range(4)) if I.sd(o) == Y]; recs = receivers(I, Y)
        print('automorphisms (agent permutations):', [a[0] for a in automorphisms(I)])
        R, rec = test(S, V, Y, orders, recs)
        for k in sorted(R):
            print(k, R[k])
        print(json.dumps(rec['per'] if rec else None))
        sys.exit()
    if sys.argv[1] == 'jsonl':      # rows with sets, vals, picks (orders and receivers recomputed)
        C = collections.Counter()
        for l in open(sys.argv[2]):
            r = json.loads(l); I = Inst(r['sets'], r['vals']); Y = tuple(r['picks'])
            orders = [list(o) for o in itertools.permutations(range(I.n)) if I.sd(o) == Y]
            R, rec = test(r['sets'], r['vals'], Y, orders, receivers(I, Y)); C.update(R)
            print(r.get('list'), r.get('idx'), 'receivers', receivers(I, Y),
                  {u: {k: v[1] for k, v in p.items() if k != 'u-first'} for u, p in rec['per'].items()} if rec else 'all ok')
        for key in sorted(C):
            print(key, C[key])
        sys.exit()
    stride = int(sys.argv[3]); dump = open(sys.argv[4], 'w')
    d = json.load(gzip.open(sys.argv[2])); tasks = []; k = 0
    for h in d['hypergraphs']:
        for st in h['starts']:
            k += 1
            if k % stride:
                continue
            tasks.append((h['sets'], st['vals'], tuple(st['picks']), st['orders'], st['receivers'], h['list'], h['idx']))
    print('starts', len(tasks), flush=True)
    C = collections.Counter(); nd = 0
    with mp.Pool() as pool:
        for R, rec in pool.imap_unordered(job, tasks, chunksize=32):
            C.update(R)
            if rec:
                dump.write(json.dumps(rec) + '\n'); nd += 1
    for key in sorted(C):
        print(key, C[key])
    print('dumped', nd)
