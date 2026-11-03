"""Probes toward Claim T of k4/de4.md §10 (the robust order; ledger K4.DE4V3R.T). EVIDENCE only.

  python3 k4/de4/claimt.py owner SOURCE PER JOBS SEED   every (V3)-valid state of the largest level sum Phi* that is
        not all-upper and has leftover goods: does a single owner finish it (one free agent takes all of J)? does
        DE's finishing rule (an owner and one-good helpers, de4lib.de_finish)? is it completable (SAT)?
  python3 k4/de4/claimt.py cases SOURCE PER JOBS SEED   every (V3)-valid state (any level sum), not all-upper, with
        leftover goods, where DE's finishing rule fails: which move proves it is not a maximum?
          simple      a valid state with larger Phi from one simple move: a free self-upgrade, Lemma 4 from a frozen
                      agent, or a want cycle;
          lateral     a free self-upgrade that keeps (V3) (value-Pareto, same Phi);
          walk        DE's walk of Theorem 9 closes; its trade is (V3)-valid and value-Pareto-better (and its Phi?);
          residual    none of these: is there a valid state with larger Phi (brute force), a (V3)-valid Pareto-better
                      one with the same Phi, and how many agents does the smallest such Phi-raise change?
  python3 k4/de4/claimt.py pointer SOURCE PER JOBS SEED the total pointer map of k4/de4.md §10.1 on every state of
        `cases` that has no simple move, no (V3)-keeping lateral one and no agent threatened by J alone: agents
        holding one good point as in Lemma 8 (disjoint labels, greedy), agents holding two or more goods to any arc
        whose label avoids those labels, frozen agents to any wanter. Over all choices: is there a cycle with
        pairwise disjoint labels, and does its trade raise Phi (Lemma 18)? If no such cycle exists: the smallest
        Phi-raising states, described agent by agent (old kind -> new goods, each as rank:source)
  python3 k4/de4/claimt.py lp SOURCE PER JOBS SEED      Lemma 20 (b), (c) of k4/de4.md §10.1 on every (V3)-valid state:
        the swaps of a lower-pair holder u with the single holder of b_u, and after a lateral upgrade releasing b_u
  python3 k4/de4/claimt.py loser SOURCE PER JOBS SEED   on the states of `pointer` with no clean raising cycle: does a
        winner/loser rotation (Theorem A' style) along a cycle of a pointer map raise Phi? A take whose label was
        used earlier on the cycle loses: its taker takes an allowed holding inside its take minus J, its own goods
        its successor does not take, and unused leftover goods. Also with "lateral wants": a lower-pair holder may
        take its b from that b's single holder
  python3 k4/de4/claimt.py lateral SOURCE PER JOBS SEED the states of `cases` with no simple or (V3)-keeping move in
        which some agent is threatened by J alone: if these are all free holders x of their b whose c and d are
        leftover (the first form of (L)), each first absorbs e_x, one of c_x, d_x (all choices, distinct), then the
        pointer map of `pointer` is built with these goods counted as used labels (Lemma 17'). Total? A clean
        raising cycle?
  python3 k4/de4/claimt.py arcs SOURCE PER JOBS SEED    partial labelled arcs (k4/de4.md §7) into free agents holding
        two or more goods, at Phi* and at the maxima (Phi*, then (V3)-Pareto), by holder and blocker kind

SOURCE: 'screen' (the screen set of ss_screen.py, PER and JOBS ignored), 'rand' (random R1-cores of dead.random_r1),
'hyper' (random strict profiles of the stuck hypergraphs and R4's hypergraph), or comma-separated core files under
results/. Kinds: a, b, c, d, LP (lower pair), E (empty), UR (robust upper set), Ud ({a, d}, not robust), Ur (other
non-robust upper set); 'fz-' marks a frozen agent."""
import sys, os, json, random, collections, itertools, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import verify_robust as T
S = T.S
from de4lib import Inst, random_profile, load_cores, wanted_goods, leftover, de_finish, subsets, wanted, apply_takes
from cycle import walk, arcs_into, danger_sets
from dead import random_r1

ROBNV = S.Variant('robnv', {'LP': 3, 'UR': 6})          # the robust levels without (V3): for Phi-raising states


def valid_nv(I, Y):
    return S.valid(ROBNV, I, Y)


def kind(I, Y, x, W):
    t = S.types(I, x, Y[x])
    if t == 'U':
        r = I.ranked(x)
        t = 'Ud' if len(r) == 4 and set(Y[x]) == {r[0], r[3]} else 'Ur'
    return ('fz-' if len(Y[x]) == 1 and Y[x][0] in W else '') + t


def single_owner(I, Y, J):
    for o in range(I.n):
        B = list(set(Y[o]) | J)
        if all(I.theta(i, B) <= I.val(i, Y[i]) for i in range(I.n) if i != o):
            return o
    return None


def allupper(I, Y):
    return all(T.isupper(I, i, Y[i]) for i in range(I.n))


def vals(I, Y):
    return tuple(I.val(i, Y[i]) for i in range(I.n))


def pareto(I, Z, Y):
    x, y = vals(I, Z), vals(I, Y)
    return all(p >= q for p, q in zip(x, y)) and x != y


def frozen(Y, x, W):
    return len(Y[x]) == 1 and Y[x][0] in W


def simple_raise(I, Y, J, W):
    """a valid state with larger Phi from a free self-upgrade, Lemma 4 from a frozen agent, or a want cycle"""
    ph = T.phi(I, Y)
    for x in range(I.n):
        if frozen(Y, x, W):
            continue
        pool = [g for g in list(Y[x]) + list(J) if g in I.v[x]]
        for N in subsets(pool):
            if ROBNV.allowed(I, x, list(N)) and I.val(x, N) > I.val(x, Y[x]):
                Z = [list(A) for A in Y]; Z[x] = list(N)
                if valid_nv(I, Z) and T.phi(I, Z) > ph:
                    return 'self-upgrade'
    for x in range(I.n):
        if not frozen(Y, x, W):
            continue
        p = [x]
        while frozen(Y, p[-1], W):
            g = Y[p[-1]][0]
            w = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
            if w in p:
                return 'want cycle'
            p.append(w)
        pool = [g for g in J if g in I.v[x]]
        for N in subsets(pool):
            if ROBNV.allowed(I, x, list(N)) and I.val(x, N) > I.val(x, Y[x]):
                Z = [list(A) for A in Y]; Z[x] = list(N)
                for t in range(1, len(p)):
                    Z[p[t]] = list(Y[p[t - 1]])
                if valid_nv(I, Z) and T.phi(I, Z) > ph:
                    return 'Lemma 4'
    return None


def lateral_v3(I, Y, J, W):
    """free self-upgrades (value up, same Phi): (any keeps (V3), list of kinds)"""
    out = []
    for x in range(I.n):
        if frozen(Y, x, W):
            continue
        pool = [g for g in list(Y[x]) + list(J) if g in I.v[x]]
        for N in subsets(pool):
            if ROBNV.allowed(I, x, list(N)) and I.val(x, N) > I.val(x, Y[x]):
                Z = [list(A) for A in Y]; Z[x] = list(N)
                if valid_nv(I, Z):
                    out.append((T.v3ok(I, Z), kind(I, Y, x, W)))
    return any(k for k, _ in out), sorted(set(t for _, t in out))


def states(I):
    """all (V1)(V2)-valid states, their Phi, and Phi*"""
    All = S.all_states(ROBNV, I)
    return All, [T.phi(I, Z) for Z in All], (max(T.phi(I, Z) for Z in All) if All else None)


def run_owner(I, C, ex, tag):
    All, ph, P = states(I)
    Cm = None
    for Y, p in zip(All, ph):
        if p != P or not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y))
        if not J or allupper(I, Y):
            continue
        so = single_owner(I, Y, J) is not None
        de = de_finish(I, Y) is not None
        if de:
            comp = True
        else:
            Cm = Cm or S.Comp(I)
            comp = Cm.ok(Y)
        C['Phi*, not all-upper, J nonempty: single owner %s, DE rule %s, completable %s' % (so, de, comp)] += 1
        if not so and len(ex) < 12:
            W = set(wanted_goods(I, Y))
            ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y],
                       [kind(I, Y, i, W) for i in range(I.n)], de_finish(I, Y)))


def run_cases(I, C, ex, tag):
    All, ph, P = states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y))
        if not J or allupper(I, Y) or de_finish(I, Y) is not None:
            continue
        C['DE rule fails, not all-upper'] += 1
        W = set(wanted_goods(I, Y))
        r = simple_raise(I, Y, J, W)
        if r:
            C['  simple: %s' % r] += 1
            continue
        keep, kinds = lateral_v3(I, Y, J, W)
        if keep:
            C['  lateral: a free self-upgrade keeping (V3)'] += 1
            continue
        if kinds:
            C['  (only (V3)-breaking free self-upgrades, by %s)' % ','.join(kinds)] += 1
        ws, Zw, _ = walk(I, Y) if all(Y) else ('someone holds nothing', None, None)
        if ws == 'ok' and pareto(I, Zw, Y) and T.v3ok(I, Zw):
            C['  walk closes: (V3)-valid, Pareto-better, Phi raised %s' % (T.phi(I, Zw) > p)] += 1
            continue
        raise_ = [Z for Z, q in zip(All, ph) if q > p]
        par = [Z for Z, q in zip(All, ph) if q == p and T.v3ok(I, Z) and pareto(I, Z, Y)]
        d = min(sum(1 for i in range(I.n) if set(Z[i]) != set(Y[i])) for Z in raise_) if raise_ else None
        C['  residual (walk: %s): Phi-raise %s (smallest changes %s agents), (V3)-Pareto %s' % (ws, bool(raise_), d, bool(par))] += 1
        if len(ex) < 12:
            best = min(raise_, key=lambda Z: sum(1 for i in range(I.n) if set(Z[i]) != set(Y[i]))) if raise_ else None
            ex.append((tag, ws, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y],
                       [kind(I, Y, i, W) for i in range(I.n)], best))


def run_arcs(I, C, ex, tag):
    All, ph, P = states(I)
    top = [Y for Y, p in zip(All, ph) if p == P and T.v3ok(I, Y)]
    V = [vals(I, Y) for Y in top]
    for k, Y in enumerate(top):
        mx = not any(all(a >= b for a, b in zip(V[l], V[k])) and V[l] != V[k] for l in range(len(top)))
        J = set(leftover(I, Y)); W = set(wanted_goods(I, Y))
        if not J:
            continue
        for tg, ok in (('Phi*', True), ('maxima', mx)):
            if not ok:
                continue
            C['%s: states with leftover goods' % tg] += 1
            for x in range(I.n):
                if I.val(x, J) > I.val(x, Y[x]):
                    C['%s: free agent threatened by J alone (lateral), kind %s' % (tg, kind(I, Y, x, W))] += 1
            for u in range(I.n):
                if len(Y[u]) < 2:
                    continue
                for _, x, D in arcs_into(I, Y, u, J):
                    if set(D) & J and not set(Y[u]) <= set(D):
                        C['%s: partial labelled arc into %s from %s' % (tg, kind(I, Y, u, W), kind(I, Y, x, W))] += 1


def pointer_options(I, Y, J, W):
    """the choices of the total pointer map: {agent: [(taker, goods taken)]}, or a reason it is not total"""
    F = [i for i in range(I.n) if not frozen(Y, i, W)]
    opts, used = {}, set()
    for o in F:
        if len(Y[o]) != 1:
            continue
        a = arcs_into(I, Y, o, J, used)
        if not a:
            return 'Lemma 8 fails'
        _, x, D = a[0]
        opts[o] = [(x, tuple(D))]
        used |= set(D) & J
    for u in F:
        if len(Y[u]) >= 2:
            a = arcs_into(I, Y, u, J, used)
            if not a:
                return "Lemma 17 fails"
            opts[u] = [(x, tuple(D)) for _, x, D in a]
    for j in range(I.n):
        if j not in opts:
            g = Y[j][0]
            opts[j] = [(w, (g,)) for w in range(I.n) if g in wanted(I, w, Y[w])]
    return opts


def clean_cycle(I, Y, J, opts, p):
    """over all choices: the best outcome of a cycle with pairwise disjoint labels ('raise', 'v3-pareto', 'neither',
    or None if there is no such cycle)"""
    agents = sorted(opts)
    found = None
    for choice in itertools.product(*[opts[a] for a in agents]):
        sig = dict(zip(agents, choice))
        seen = set()
        for s0 in agents:
            path, o = [], s0
            while o not in path and o not in seen:
                path.append(o); o = sig[o][0]
            seen |= set(path)
            if o not in path:
                continue
            cyc = path[path.index(o):]
            labs = [g for c in cyc for g in sig[c][1] if g in J]
            if len(labs) != len(set(labs)):
                continue
            Z = apply_takes(I, Y, {sig[c][0]: sig[c][1] for c in cyc})
            r = 'invalid'
            if Z and valid_nv(I, Z):
                q = T.phi(I, Z)
                r = 'raise' if q > p else ('v3-pareto' if q == p and T.v3ok(I, Z) and pareto(I, Z, Y) else 'neither')
            if r == 'raise':
                return r
            found = found if found in ('v3-pareto',) else r
    return found


def describe(I, Y, Z, J, W):
    out = []
    for i in range(I.n):
        if set(Z[i]) != set(Y[i]):
            r = I.ranked(i)
            def src(g):
                if g in Y[i]: return 'own'
                if g in J: return 'J'
                return kind(I, Y, next(k for k in range(I.n) if g in Y[k]), W)
            out.append('%s->{%s}' % (kind(I, Y, i, W), ','.join(('abcd'[r.index(g)] if g in r else 'o') + ':' + src(g)
                                                                for g in sorted(Z[i], key=lambda g: r.index(g) if g in r else 9))))
    return ' '.join(sorted(out))


def run_pointer(I, C, ex, tag):
    All, ph, P = states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y))
        if not J or allupper(I, Y) or de_finish(I, Y) is not None:
            continue
        W = set(wanted_goods(I, Y))
        if simple_raise(I, Y, J, W) or lateral_v3(I, Y, J, W)[0]:
            continue
        if any(I.val(x, J) > I.val(x, Y[x]) for x in range(I.n)):
            C['some agent threatened by J alone (not tested here)'] += 1
            continue
        if not all(Y):
            C['someone holds nothing'] += 1
            continue
        opts = pointer_options(I, Y, J, W)
        if isinstance(opts, str):
            C[opts] += 1
            continue
        r = clean_cycle(I, Y, J, opts, p)
        C['pointer map total; best cycle with disjoint labels: %s' % r] += 1
        if r != 'raise':
            raise_ = [Z for Z, q in zip(All, ph) if q > p]
            d = min((sum(1 for i in range(I.n) if set(Z[i]) != set(Y[i])) for Z in raise_), default=None)
            sh = sorted(set(describe(I, Y, Z, J, W) for Z in raise_
                            if sum(1 for i in range(I.n) if set(Z[i]) != set(Y[i])) == d))
            C['  no clean raising cycle: kinds %s | smallest Phi-raise changes %s agents: %s' % (
                ' '.join(sorted(kind(I, Y, i, W) for i in range(I.n))), d, ' / '.join(sh[:4]))] += 1
            if len(ex) < 12:
                ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y],
                           [kind(I, Y, i, W) for i in range(I.n)]))


def minimal_arc(I, Y, D):
    return not any(set(E) < set(D) for i in range(I.n) for E in danger_sets(I, i, Y[i]))


def run_lp(I, C, ex, tag):
    All, ph, P = states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y))
        for u in range(I.n):
            if S.types(I, u, Y[u]) != 'LP':
                continue
            a, b, c, d = I.ranked(u)
            x = next(k for k in range(I.n) if b in Y[k])
            if tuple(Y[x]) == (b,):
                for _, xx, D in arcs_into(I, Y, u, J):
                    if xx != x or not minimal_arc(I, Y, D) or not (len(D) == 2 or not set(Y[u]) <= set(D)):
                        continue
                    if T.lev(I, x, list(D)) <= T.lev(I, x, list(Y[x])):
                        continue
                    Z = [list(A) for A in Y]; Z[x] = list(D); Z[u] = [b]
                    ok = valid_nv(I, Z) and T.phi(I, Z) > p
                    C['Lemma 20(b): x -> D, u -> {b_u} valid and Phi-raising: %s' % ok] += 1
                    if not ok and len(ex) < 12:
                        ex.append(('b', tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], u, x, D))
            if I.v[u][b] + I.v[u][c] > I.v[u][a]:
                for w in range(I.n):
                    if w == u or not T.isupper(I, w, Y[w]) or b not in Y[w]:
                        continue
                    pool = [g for g in list(Y[w]) + list(J) if g in I.v[w]]
                    for N in subsets(pool):
                        if b in N or not ROBNV.allowed(I, w, list(N)) or I.val(w, N) <= I.val(w, Y[w]):
                            continue
                        if T.lev(I, w, list(N)) != T.lev(I, w, list(Y[w])):
                            continue
                        Z = [list(A) for A in Y]; Z[w] = list(N)
                        if not valid_nv(I, Z):
                            continue
                        Z[u] = [b, c]
                        ok = valid_nv(I, Z) and T.phi(I, Z) > p
                        C['Lemma 20(c): w -> N, u -> {b_u, c_u} valid and Phi-raising: %s' % ok] += 1
                        if not ok and len(ex) < 12:
                            ex.append(('c', tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], u, w, N))


def loser_cycle(I, Y, J, cyc, sig, p):
    """winner/loser rotation along cyc (every start); True if some outcome is valid with larger Phi"""
    k = len(cyc)
    for st in range(k):
        order = cyc[st:] + cyc[:st]
        used, plan = set(), []
        for c in order:
            x, Tk = sig[c]
            lab = set(Tk) & J
            lose = bool(lab & used)
            if not lose:
                used |= lab
            plan.append((c, x, Tk, lose))
        Z = [list(A) for A in Y]
        for c, x, Tk, lose in plan:
            if not lose:
                Z[x] = list(Tk)
        taken = set(g for c, x, Tk, lose in plan if not lose for g in Tk)
        losers = [(c, x, Tk) for c, x, Tk, lose in plan if lose]
        opts = []
        for c, x, Tk in losers:
            pool = set(g for g in Tk if g not in J) | set(g for g in Y[x] if g not in taken) | set(g for g in J if g not in taken)
            pool = [g for g in pool if g in I.v[x]]
            opts.append([list(H) for H in subsets(pool) if ROBNV.allowed(I, x, list(H))])
        for choice in itertools.product(*opts):
            Z2 = [list(A) for A in Z]
            for (c, x, Tk), H in zip(losers, choice):
                Z2[x] = H
            goods = [g for A in Z2 for g in A]
            if len(goods) == len(set(goods)) and valid_nv(I, Z2) and T.phi(I, Z2) > p:
                return True
    return False


def run_loser(I, C, ex, tag):
    All, ph, P = states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y))
        if not J or allupper(I, Y) or de_finish(I, Y) is not None:
            continue
        W = set(wanted_goods(I, Y))
        if simple_raise(I, Y, J, W) or lateral_v3(I, Y, J, W)[0]:
            continue
        if any(I.val(x, J) > I.val(x, Y[x]) for x in range(I.n)) or not all(Y):
            continue
        opts = pointer_options(I, Y, J, W)
        if isinstance(opts, str) or clean_cycle(I, Y, J, opts, p) == 'raise':
            continue
        res = {}
        for lateral in (False, True):
            o2 = {a: list(v) for a, v in opts.items()}
            if lateral:      # a lower-pair holder may take its b from that b's single holder
                for u in range(I.n):
                    if S.types(I, u, Y[u]) == 'LP':
                        b = I.ranked(u)[1]
                        x = next(k for k in range(I.n) if b in Y[k])
                        if tuple(Y[x]) == (b,) and (u, (b,)) not in o2[x]:
                            o2[x].append((u, (b,)))
            agents = sorted(o2)
            ok = False
            for choice in itertools.product(*[o2[a] for a in agents]):
                sig = dict(zip(agents, choice))
                seen = set()
                for s0 in agents:
                    path, o = [], s0
                    while o not in path and o not in seen:
                        path.append(o); o = sig[o][0]
                    seen |= set(path)
                    if o in path and loser_cycle(I, Y, J, path[path.index(o):], sig, p):
                        ok = True
                        break
                if ok:
                    break
            res[lateral] = ok
        C['no clean raising cycle (kinds %s): loser rotation raises Phi %s; with lateral wants %s' % (
            ' '.join(sorted(kind(I, Y, i, W) for i in range(I.n))), res[False], res[True])] += 1
        if not res[True] and len(ex) < 12:
            ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y]))


def run_lateral(I, C, ex, tag):
    All, ph, P = states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y):
            continue
        J = set(leftover(I, Y))
        if not J or allupper(I, Y) or de_finish(I, Y) is not None:
            continue
        W = set(wanted_goods(I, Y))
        if simple_raise(I, Y, J, W) or lateral_v3(I, Y, J, W)[0] or not all(Y):
            continue
        thr = [x for x in range(I.n) if I.val(x, J) > I.val(x, Y[x])]
        if not thr:
            continue
        lat = [x for x in thr if len(I.ranked(x)) == 4 and tuple(Y[x]) == (I.ranked(x)[1],)
               and I.ranked(x)[2] in J and I.ranked(x)[3] in J]
        if len(lat) != len(thr):
            C['an agent threatened by J alone is not a holder of b with c, d leftover (second form of (L))'] += 1
            continue
        F = [i for i in range(I.n) if not frozen(Y, i, W)]
        best = None
        for es in itertools.product(*[I.ranked(x)[2:] for x in lat]):
            if len(set(es)) != len(es):
                continue
            E = dict(zip(lat, es))
            used, opts, ok = set(es), {}, True
            for o in F:
                if len(Y[o]) != 1 or o in E:
                    continue
                a = arcs_into(I, Y, o, J, used)
                if not a:
                    ok = False; break
                _, x, D = a[0]
                opts[o] = [(x, tuple(D))]
                used |= set(D) & J
            if not ok:
                best = best or 'Lemma 8 fails'; continue
            for u in F:
                if len(Y[u]) >= 2 or u in E:
                    a = arcs_into(I, Y, u, J, used - ({E[u]} if u in E else set()))
                    if not a:
                        ok = False; break
                    opts[u] = [(x, tuple(D)) for _, x, D in a]
            if not ok:
                best = best or "Lemma 17' fails"; continue
            for j in range(I.n):
                if j not in opts:
                    g = Y[j][0]
                    opts[j] = [(w, (g,)) for w in range(I.n) if g in wanted(I, w, Y[w])]
            r = clean_cycle(I, Y, J, opts, p)
            if r == 'raise':
                best = 'total, a clean cycle raises Phi'; break
            best = 'total, no clean raising cycle (%s)' % r
        C['%d such agents: %s' % (len(lat), best)] += 1
        if best != 'total, a clean cycle raises Phi' and len(ex) < 12:
            ex.append((tag, I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], lat))


MODES = {'lateral': run_lateral, 'owner': run_owner, 'cases': run_cases, 'pointer': run_pointer, 'lp': run_lp, 'loser': run_loser,
         'arcs': run_arcs}


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
    elif src == 'hyper':
        cores = json.load(open(os.path.join(ROOT, 'results/k4_de4/stuck_hypergraphs.json')))['hypergraphs']
        cores += [[[0, 1, 6, 8], [0, 1, 2, 3], [2, 4, 5, 8], [4, 5, 6, 7]]]
    else:
        cores = []
        for fn in src.split(','):
            cores += load_cores(os.path.join(ROOT, 'results', fn))
    for _ in range(per):
        I = random_r1(rng) if cores is None else Inst(*(lambda s: (s, random_profile(s, rng)))(rng.choice(cores)))
        C['profiles'] += 1
        f(I, C, ex, '')
    return C, ex


if __name__ == '__main__':
    mode, src, per, jobs, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    if src == 'screen':
        jobs = 1
    tot, EX = collections.Counter(), []
    with mp.Pool(min(jobs, os.cpu_count())) as p:
        for C, ex in p.imap_unordered(job, [(mode, src, per, seed + k) for k in range(jobs)]):
            tot.update(C); EX += ex
    print('$ python3 k4/de4/claimt.py', ' '.join(sys.argv[1:]))
    for k in sorted(tot):
        print('%9d  %s' % (tot[k], k))
    for e in EX[:12]:
        print('EX', json.dumps(e))
