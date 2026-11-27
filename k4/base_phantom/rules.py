"""Which local rule for choosing rounds avoids dead ends?  (The base case cannot repair them: deadends.py.)

For a rule R (a predicate on settlements; a round is R-admissible when all its settlements are, or, for a priority
rule "R>", R-admissible rounds are used when some exist and any admissible round otherwise), the R-graph keeps the
admissible rounds that R allows.  R is *safe* at a start when every state reachable in the R-graph has a lifted
completion or an R-round (no R-dead-end), so the greedy process "take any R-round" always ends in a completion.

Terminal states (BASES): a lifted completion; optionally a base repair of class <= C0/ED/C1/C3 (base.py); with 'R',
also a *final round*: an admissible round of any kind (l-alone phantoms allowed) after which a lifted completion
exists at once.

Settlement features at the state S where it is applied (k, P = (k, x1, .., xt), T):
  E        P is a prefix of the earliest-wanter chain E(k) for some SD order of S
  Efull    P is the whole E(k) for such an order (its end's good unwanted)
  full     the end's good is wanted by no present agent (P cannot be extended canonically)
  best     v_k(T) is the largest over the improving sets inside P's pool
  bestk    v_k(T) is the largest over every canonical chain of k and its pool
  sat      the phantom is satisfied: v_k(R_k - T) <= v_k(T)
  noP1     no "l alone" constraint: every good of R_k - T is worth at most v_k(T) to k
  P1junk   any "l alone" constraint is on a junk good (not on a present agent's base)
  pair / triple   |T|

    [RULES=any,noP1,...] python3 k4/base_phantom/rules.py NAME FILE[,FILE..] [LIMIT|-] [STRIDE]
"""
import sys, os, json, itertools, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bplib import Inst, State, start_state, bits, load_rows, row_key, rounds, lifted_completion, canonical_chains, \
    dangerous, wants, submasks
from base import base_repairs, CLASSES


def sd_orders(I, S):
    tgt = {i: S.B[i].bit_length() - 1 for i in S.alive}
    return [o for o in itertools.permutations(S.alive) if I.sd(o, S.goods) == tgt]


def E_chain(I, S, k, order):
    pos = {a: t for t, a in enumerate(order)}
    P = [k]
    while True:
        g = S.B[P[-1]].bit_length() - 1
        w = [a for a in S.alive if a not in P and wants(I, S.B, a, g)]
        if not w:
            return tuple(P)
        P.append(min(w, key=lambda a: pos[a]))


def features(I, S, orders, k, P, T, bestk_val, S2=None):
    f = {}
    Es = [E_chain(I, S, k, o) for o in orders]
    f['E'] = any(E[:len(P)] == P for E in Es)
    f['Efull'] = any(E == P for E in Es)
    g = S.B[P[-1]].bit_length() - 1
    f['full'] = not any(a not in P and wants(I, S.B, a, g) for a in S.alive)
    pool = (S.junk() | S.B[P[-1]]) & I.R[k]
    best = max(I.V(k, t) for t in submasks(pool, 3))
    tau = I.V(k, T)
    f['best'] = tau == best
    f['bestk'] = tau == bestk_val[k]
    rest = I.R[k] & ~T
    f['sat'] = I.V(k, rest) <= tau
    big = [h for h in bits(rest) if I.val[k][h] > tau]
    f['noP1'] = not big
    # after the round the goods of R_k - T are: k's old pick (now x1's), other agents' bases, junk
    f['P1junk'] = all(not any(S.B[a] >> h & 1 for a in S.alive if a not in P) for h in big)
    # P1ok: every "l alone" good is, after the round, the base of a present agent q content with it alone
    # (v_q(R_q - l) over the present goods is at most v_q(l)), so q could itself be settled with {l}
    f['P1ok'] = True
    if S2 is not None:
        for h in big:
            q = [a for a in S2.alive if S2.B[a] >> h & 1]
            if not q or I.V(q[0], I.R[q[0]] & S2.goods & ~(1 << h)) > I.val[q[0]][h]:
                f['P1ok'] = False
    f['pair'] = len(bits(T)) == 2
    f['triple'] = len(bits(T)) == 3
    return f


RULES = ['any', 'E', 'Efull', 'full', 'best', 'bestk', 'sat', 'noP1', 'P1junk', 'P1ok', 'pair', 'triple',
         'E+best', 'E+bestk', 'Efull+bestk', 'full+bestk', 'E+noP1', 'bestk+noP1', 'E+P1ok']
if os.environ.get('RULES'):
    RULES = os.environ['RULES'].split(',')


def ok_rule(f, rule):
    if rule == 'any':
        return True
    return all(f[x] for x in rule.split('+'))


def graph(I, S0):
    """Explore all admissible rounds; per state: complete?, list of (feature dicts of the settlements, successor)."""
    seen = {}
    stack = [S0]
    while stack:
        S = stack.pop()
        k = S.key()
        if k in seen:
            continue
        comp = lifted_completion(I, S) is not None
        bc = None if comp else base_repairs(I, S)[0]
        edges = []
        if not comp:
            orders = sd_orders(I, S)
            D = dangerous(I, S)
            bestk_val = {}
            for kk in D:
                vals = [I.V(kk, t) for P in canonical_chains(I, S, kk)
                        for t in submasks((S.junk() | S.B[P[-1]]) & I.R[kk], 3)]
                bestk_val[kk] = max(vals) if vals else 0
            for combo, S2 in rounds(I, S):
                fs = [features(I, S, orders, kk, P, T, bestk_val, S2) for kk, P, T in combo]
                edges.append((fs, S2.key()))
                if S2.key() not in seen:
                    stack.append(S2)
        seen[k] = (comp, bc, edges)
    return seen


def evaluate(seen, k0, rule, priority, base=None):
    """(safe, good) of the rule from k0.  With base = 'C0'..'C3', a state with a base repair of that class or a
    smaller one is terminal as well (the greedy process stops there with OC1 under the phantoms)."""
    cls = None if base is None else base.replace('R+', '').replace('R', '') or None
    fin = base is not None and base.startswith('R')

    def term(k):
        comp, bc, edges = seen[k]
        if comp:
            return True
        if cls is not None and bc is not None and CLASSES.index(bc) <= CLASSES.index(cls):
            return True
        # 'R': a final round of any kind (l-alone phantoms allowed) followed by a lifted completion at once
        return fin and any(seen[s2][0] for fs, s2 in edges)
    def allowed(edges):
        a = [s2 for fs, s2 in edges if all(ok_rule(f, rule) for f in fs)]
        if priority and not a:
            a = [s2 for fs, s2 in edges]
        return a
    reach = set()
    stack = [k0]
    dead = False
    while stack:
        k = stack.pop()
        if k in reach:
            continue
        reach.add(k)
        comp, bc, edges = seen[k]
        if term(k):
            continue
        a = allowed(edges)
        if not a:
            dead = True
        stack.extend(a)
    good = {}

    def gd(k):
        if k in good:
            return good[k]
        good[k] = False
        comp, bc, edges = seen[k]
        r = term(k) or any(gd(s) for s in allowed(edges))
        good[k] = r
        return r
    return (not dead), gd(k0)


def job(r):
    I = Inst(r['sets'], r['vals'])
    S = start_state(I, r['picks'])
    seen = graph(I, S)
    C = collections.Counter()
    for rule in RULES:
        for pr in (False, True):
            for base in BASES:
                safe, good = evaluate(seen, S.key(), rule, pr, base)
                C[(rule + ('>' if pr else ''), base, 'safe' if safe else 'UNSAFE', 'good' if good else 'NOT GOOD')] += 1
                if not safe and rule in SHOW and base == 'ED':
                    C[('UNSAFE-EX', rule, json.dumps([r['sets'], r['vals'], r['picks']]))] += 1
    return C


BASES = [None, 'C0', 'ED', 'C1', 'C3', 'R', 'R+C0', 'R+ED']
SHOW = ['noP1', 'P1ok']


if __name__ == '__main__':
    name, fns = sys.argv[1], sys.argv[2].split(',')
    lim = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else None
    stride = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rows = {}
    for fn in fns:
        for r in load_rows(fn):
            rows.setdefault(row_key(r), r)
    rows = list(rows.values())[::stride][:lim]
    print('$ RULES=%s python3 k4/base_phantom/rules.py' % ','.join(RULES), name, ','.join(os.path.relpath(f) for f in fns),
          lim or '-', stride)
    print('distinct starts:', len(rows))
    C = collections.Counter()
    with mp.Pool(4) as pool:
        for c in pool.imap_unordered(job, rows, chunksize=16):
            C.update(c)
    print('  rule           terminal states                               safe  unsafe |   good  not good')
    for rule in RULES:
        for pr in ('', '>'):
            rr = rule + pr
            for base in BASES:
                lab = 'completion' if base is None else (
                    'completion or a base repair <= %s' % base if not base.startswith('R') else
                    'completion, or a final round' + ('' if base == 'R' else ' or a base repair <= %s' % base[2:]))
                print('  %-14s %-44s %6d  %6d | %6d  %6d' % (
                    rr, lab,
                    sum(v for k, v in C.items() if k[0] == rr and k[1] == base and k[2] == 'safe'),
                    sum(v for k, v in C.items() if k[0] == rr and k[1] == base and k[2] == 'UNSAFE'),
                    sum(v for k, v in C.items() if k[0] == rr and k[1] == base and k[3] == 'good'),
                    sum(v for k, v in C.items() if k[0] == rr and k[1] == base and k[3] == 'NOT GOOD')))
    ex = [(k[1], k[2]) for k in C if k[0] == 'UNSAFE-EX']
    for rl in SHOW:
        exs = sorted([e for r_, e in ex if r_ == rl], key=len)[:3]
        print('  unsafe under %s or %s> with base ED, %d cases; smallest:' % (rl, rl, len([1 for r_, e in ex if r_ == rl])))
        for e in exs:
            print('    ', e)
