"""Cycles of the arc graph in the robust order (k4/de4.md §10.2; ledger K4.DE4V3R.C, K4.DE4V3R.D, K4.DE4V3R.T23).
EVIDENCE for the written proofs and conjectures.

The arc graph G of a state Y: an arc o -> x taking T when o is frozen and x wants o's good (T = Y_o), or o is free and
(x, T) is a minimal arc into o (k4/de4.md §7: T a danger set of x inside Y_o + J meeting Y_o, and no danger set of
anyone is a proper subset of T). Its label is T ∩ J. (H) is the condition of §7 (everyone holds a good, nobody is
threatened by J alone, no free self-upgrade and no Lemma 4 move).

  python3 k4/de4/claimd.py refuteC              Conjecture C ("at a maximum with (H), G has no cycle") is false: the
                                                maxima of the screen set whose G has a cycle (GM4-A and others)
  python3 k4/de4/claimd.py c2 SOURCE PER JOBS SEED
        Conjecture C2: at every (V3)-valid state of the largest level sum with (H), G has no cycle on which only arcs
        out of agents holding two or more goods share labels ("F2-clash cycle"); also at the maxima
  python3 k4/de4/claimd.py thm23 SOURCE PER JOBS SEED
        Theorem 23 (replacement) on every cycle of every (V3)-valid (H) state: whenever its hypotheses hold, the
        trade is valid and raises Phi
  python3 k4/de4/claimd.py bswap SOURCE PER JOBS SEED
        Lemma 20' (b-swaps) on every (V3)-valid (H) state: each swap is valid, and its level change
  python3 k4/de4/claimd.py d SOURCE PER JOBS SEED
        Conjecture D on every F2-clash cycle of every (V3)-valid (H) state: Lemma 18, Theorem 23 or a b-swap applies

SOURCE: 'screen' (PER, JOBS ignored), 'rand' (dead.random_r1), 'hyper' (the stuck hypergraphs), 'xhg' (the seven
hypergraphs on which states with no clean pointer cycle were found, k4/de4.md §10.1), or core files under results/."""
import sys, os, json, random, collections, itertools, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import claimt as CT
T = CT.T
S = CT.S
from de4lib import Inst, random_profile, load_cores, wanted_goods, leftover, wanted, apply_takes
from cycle import arcs_into
from dead import random_r1

XHG = [[[0, 1, 4, 5], [0, 2, 5, 6], [1, 2, 4, 6]], [[0, 2, 4, 5], [1, 3, 4, 6], [2, 5, 6], [3, 5, 6]],
       [[0, 1, 2, 5], [1, 3, 4, 5], [2, 3, 4, 5]], [[0, 1, 2, 3], [0, 1, 4, 5], [2, 3, 4, 5]],
       [[0, 2, 4, 5], [1, 3, 4, 5], [2, 3, 5]], [[1, 2, 6, 8], [2, 4, 6], [0, 2, 4, 8]],
       [[0, 2, 5, 6], [1, 4, 5, 6], [2, 3, 4, 6], [3, 4, 5, 6]]]


def H(I, Y, J, W):
    if not all(Y) or any(I.val(x, J) > I.val(x, Y[x]) for x in range(I.n)):
        return False
    return not CT.simple_raise(I, Y, J, W) and not CT.lateral_v3(I, Y, J, W)[1]


def graph(I, Y, J, W):
    arcs = []
    for o in range(I.n):
        if CT.frozen(Y, o, W):
            g = Y[o][0]
            arcs += [(o, w, (g,)) for w in range(I.n) if g in wanted(I, w, Y[w])]
        else:
            arcs += [(o, x, tuple(D)) for _, x, D in arcs_into(I, Y, o, J) if CT.minimal_arc(I, Y, D)]
    return arcs


def cycles(I, arcs, maxlen):
    out = collections.defaultdict(list)
    for a in arcs:
        out[a[0]].append(a)
    res = []

    def rec(start, path):
        for a in out[path[-1][1]]:
            if a[1] == start:
                res.append(path + [a])
            elif a[1] > start and a[1] not in [z[0] for z in path] and len(path) + 1 < maxlen:
                rec(start, path + [a])
    for s in range(I.n):
        for a in out[s]:
            if a[1] > s:
                rec(s, [a])
    return res


def rich(I, Y, x):
    if S.types(I, x, list(Y[x])) != 'U':
        return False
    r = I.ranked(x)
    return len(r) == 4 and set(Y[x]) != {r[0], r[3]} and r[0] not in Y[x]


def single_free(Y, W, o):
    return not CT.frozen(Y, o, W) and len(Y[o]) == 1


def f2_clash_only(I, Y, J, W, cyc):
    """labels of arcs out of free agents holding one good are pairwise disjoint and avoid the other labels"""
    f1 = [g for a in cyc if single_free(Y, W, a[0]) for g in set(a[2]) & J]
    other = set(g for a in cyc if not single_free(Y, W, a[0]) for g in set(a[2]) & J)
    return len(f1) == len(set(f1)) and not (set(f1) & other)


def alternative(I, Y, W, a, succ_take):
    """Theorem 23's same-giver alternative for the arc a = (giver, taker, take), or None"""
    o, x, Tk = a
    r = I.ranked(x)
    t = S.types(I, x, list(Y[x]))
    if rich(I, Y, x) and r[0] in Tk and r[0] in Y[o]:
        return 'keepR', [r[0]] + [g for g in Y[x] if g not in succ_take]
    if CT.frozen(Y, x, W) and t == 'a' and len(r) >= 3 and r[1] in Tk and r[1] in Y[o]:
        return 'down-b', [r[1]]
    if CT.frozen(Y, x, W) and t == 'b' and len(r) == 4 and r[2] in Tk and r[2] in Y[o]:
        return 'down-c', [r[2]]
    return None


def theorem23(I, Y, J, W, p, cyc, C=None, ex=None, tag=''):
    """all replacement choices satisfying Theorem 23's hypotheses; records each outcome. True if one raises Phi."""
    k = len(cyc)
    labs = [set(a[2]) & J for a in cyc]
    shared = [t for t in range(k) if any(labs[t] & labs[u] for u in range(k) if u != t)]
    found = False
    for mask in range(1 << len(shared)):
        rep = [shared[i] for i in range(len(shared)) if mask >> i & 1]
        rest = [t for t in range(k) if t not in rep]
        lr = [g for t in rest for g in labs[t]]
        if len(lr) != len(set(lr)) or any(not (labs[t] & set(lr)) for t in rep):
            continue
        Z = [list(A) for A in Y]
        kinds = {}
        for t in rest:
            Z[cyc[t][1]] = list(cyc[t][2])
        ok = True
        for t in rep:
            st = set(cyc[(t + 1) % k][2]) if (t + 1) % k in rest else set()
            r = alternative(I, Y, W, cyc[t], st)
            if r is None:
                ok = False
                break
            kinds[t] = r[0]
            Z[cyc[t][1]] = r[1]
        if not ok:
            continue
        goods = [g for A in Z for g in A]
        if len(goods) != len(set(goods)):
            continue
        bad = False                                                        # hypothesis (iii)
        for t in rep:
            x = cyc[t][1]
            outside = set(I.sets[x]) - set(Z[x]) - {I.ranked(x)[0]}
            if any(len(Z[i]) == 3 and len(set(Z[i]) & outside) >= 2 for i in range(I.n)):
                bad = True
            if kinds[t] == 'keepR' and len(Z[x]) == 1:
                y = cyc[(t + 1) % k][1]
                ry = I.ranked(y)
                if len(ry) == 4 and tuple(Y[y]) == (ry[1],) and S.types(I, y, list(Z[y])) == 'LP':
                    bad = True
        if bad:
            continue
        comp = set((t + 1) % k for t in rep if kinds[t] != 'keepR' or len(Z[cyc[t][1]]) == 1)
        if not any(T.lev(I, cyc[t][1], Z[cyc[t][1]]) > T.lev(I, cyc[t][1], list(Y[cyc[t][1]]))
                   for t in rest if t not in comp):                          # hypothesis (iv)
            continue
        res = valid(I, Z) and T.phi(I, Z) > p
        found |= res
        if C is not None:
            C['Theorem 23, replaced %s: valid and Phi-raising %s' % (sorted(kinds.values()), res)] += 1
            if not res and len(ex) < 12:
                ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], cyc, kinds))
    return found


def valid(I, Z):
    return CT.valid_nv(I, Z)


def bswaps(I, Y, J, W):
    """Lemma 20' (b-swaps) for each free lower-pair holder u and the holder w != u of b_u"""
    out = []
    for u in range(I.n):
        if S.types(I, u, list(Y[u])) != 'LP':
            continue
        a, b, c, d = I.ranked(u)
        w = next(k for k in range(I.n) if b in Y[k])
        bc = I.v[u][b] + I.v[u][c] > I.v[u][a]
        for _, x, D in arcs_into(I, Y, u, J):
            if x == w and CT.minimal_arc(I, Y, D) and (len(D) == 2 or not set(Y[u]) <= set(D)):
                Nu = [b, c] if (c not in D and bc and not CT.frozen(Y, w, W)) else [b]
                out.append(('i', {w: list(D), u: Nu}))
        if S.types(I, w, list(Y[w])) == 'LP':
            aw, bw, cw, dw = I.ranked(w)
            if bw in Y[u]:
                Nu = [b, c] if (c != bw and bc) else [b]
                Nw = [bw, cw] if (cw != b and I.v[w][bw] + I.v[w][cw] > I.v[w][aw]) else [bw]
                out.append(('ii', {u: Nu, w: Nw}))
        if T.isupper(I, w, list(Y[w])) and len(Y[w]) == 2 and I.ranked(w)[0] in Y[w] and bc:
            out.append(('iii', {u: [b, c], w: [I.ranked(w)[0]]}))
    res = []
    for kind, takes in out:
        Z = [list(A) for A in Y]
        for i, N in takes.items():
            Z[i] = list(N)
        goods = [g for A in Z for g in A]
        if len(goods) == len(set(goods)):
            res.append((kind, Z))
    return res


def run_c2(I, C, ex, tag):
    All, ph, P = CT.states(I)
    top = [Y for Y, p in zip(All, ph) if p == P and T.v3ok(I, Y)]
    V = [CT.vals(I, Y) for Y in top]
    for k, Y in enumerate(top):
        mx = not any(all(a >= b for a, b in zip(V[l], V[k])) and V[l] != V[k] for l in range(len(top)))
        J = set(leftover(I, Y)); W = set(wanted_goods(I, Y))
        if not J or not H(I, Y, J, W):
            continue
        cs = cycles(I, graph(I, Y, J, W), I.n)
        f2 = [c for c in cs if f2_clash_only(I, Y, J, W, c)]
        C['largest level sum, (H): G has a cycle %s; an F2-clash cycle %s' % (bool(cs), bool(f2))] += 1
        if mx:
            C['  of which maxima: G has a cycle %s; an F2-clash cycle %s' % (bool(cs), bool(f2))] += 1
        if f2 and len(ex) < 12:
            ex.append((tag, mx, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y]))


def run_thm23(I, C, ex, tag):
    All, ph, P = CT.states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y)); W = set(wanted_goods(I, Y))
        if not J or not H(I, Y, J, W):
            continue
        for cyc in cycles(I, graph(I, Y, J, W), I.n):
            theorem23(I, Y, J, W, p, cyc, C, ex, tag)


def run_bswap(I, C, ex, tag):
    All, ph, P = CT.states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y)); W = set(wanted_goods(I, Y))
        if not J or not H(I, Y, J, W):
            continue
        for kind, Z in bswaps(I, Y, J, W):
            ok = valid(I, Z)
            C["Lemma 20' (%s): valid %s, level change %+d" % (kind, ok, T.phi(I, Z) - p)] += 1
            if not ok and len(ex) < 12:
                ex.append((tag, kind, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], Z))


def run_d(I, C, ex, tag):
    All, ph, P = CT.states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y)); W = set(wanted_goods(I, Y))
        if not J or not H(I, Y, J, W):
            continue
        bs = None
        for cyc in cycles(I, graph(I, Y, J, W), I.n):
            if not f2_clash_only(I, Y, J, W, cyc):
                continue
            L = [g for a in cyc for g in set(a[2]) & J]
            if len(L) == len(set(L)):
                Z = apply_takes(I, Y, {a[1]: a[2] for a in cyc})
                if Z and valid(I, Z) and (T.phi(I, Z) > p or (T.phi(I, Z) == p and T.v3ok(I, Z) and CT.pareto(I, Z, Y))):
                    C['F2-clash cycle: clean, Lemma 18'] += 1
                    continue
            if theorem23(I, Y, J, W, p, cyc):
                C['F2-clash cycle: Theorem 23'] += 1
                continue
            if bs is None:
                bs = next((kind for kind, Z in bswaps(I, Y, J, W) if valid(I, Z) and T.phi(I, Z) > p), False)
            if bs:
                C["F2-clash cycle: b-swap (%s), Lemma 20'" % bs] += 1
                continue
            C['F2-clash cycle: UNRESOLVED (some valid state with larger Phi: %s)' % any(q > p for q in ph)] += 1
            if len(ex) < 12:
                ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], cyc))


MODES = {'c2': run_c2, 'thm23': run_thm23, 'bswap': run_bswap, 'd': run_d}


def job(args):
    mode, src, per, seed = args
    rng = random.Random(seed)
    C, ex = collections.Counter(), []
    f = MODES[mode]
    if src == 'screen':
        for name, I in S.screen_set():
            f(I, C, ex, name)
        return C, ex
    if src == 'rand':
        cores = None
    elif src == 'xhg':
        cores = XHG
    elif src == 'hyper':
        cores = json.load(open(os.path.join(ROOT, 'results/k4_de4/stuck_hypergraphs.json')))['hypergraphs']
    else:
        cores = []
        for fn in src.split(','):
            cores += load_cores(os.path.join(ROOT, 'results', fn))
    for _ in range(per):
        I = random_r1(rng) if cores is None else Inst(*(lambda s: (s, random_profile(s, rng)))(rng.choice(cores)))
        C['profiles'] += 1
        f(I, C, ex, '')
    return C, ex


def refute_c():
    """maxima of the screen set with (H) whose arc graph has a cycle"""
    n = 0
    for name, I in S.screen_set():
        All, ph, P = CT.states(I)
        top = [Y for Y, p in zip(All, ph) if p == P and T.v3ok(I, Y)]
        V = [CT.vals(I, Y) for Y in top]
        for k, Y in enumerate(top):
            if any(all(a >= b for a, b in zip(V[l], V[k])) and V[l] != V[k] for l in range(len(top))):
                continue
            J = set(leftover(I, Y)); W = set(wanted_goods(I, Y))
            if not J or not H(I, Y, J, W):
                continue
            cs = cycles(I, graph(I, Y, J, W), I.n)
            if cs:
                n += 1
                print(name, 'maximum', [list(A) for A in Y], 'J', sorted(J), 'cycle', cs[0],
                      'F2-clash cycle' if any(f2_clash_only(I, Y, J, W, c) for c in cs) else 'every cycle has an F1 clash')
    print('maxima with (H) whose G has a cycle:', n)
    return n


if __name__ == '__main__':
    mode = sys.argv[1]
    print('$ python3 k4/de4/claimd.py', ' '.join(sys.argv[1:]))
    if mode == 'refuteC':
        sys.exit(0 if refute_c() > 0 else 1)
    src, per, jobs, seed = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    if src == 'screen':
        jobs = 1
    tot, EX = collections.Counter(), []
    with mp.Pool(min(jobs, int(os.environ.get('NP', os.cpu_count())))) as p:
        for C, ex in p.imap_unordered(job, [(mode, src, per, seed + k) for k in range(jobs)]):
            tot.update(C); EX += ex
    for k in sorted(tot):
        print('%9d  %s' % (tot[k], k))
    for e in EX[:12]:
        print('EX', json.dumps(e))
