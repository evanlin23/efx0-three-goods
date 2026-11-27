"""Displacement structure of the dominating EFX0 allocations (k4/ttc.md §7).

Housing-market view: the picks Y are endowments, a complete EFX0 allocation X with v_i(X_i) >= v_i(Y_i) for all i
(MD, k4/sdc.md §28) is an individually rational target.  Agent j is *displaced* in X if Y_j is not in X_j; the
*displacement graph* has an arc j -> i when i holds Y_j in X (i != j).  Every displaced pick has exactly one head, so
the graph has out-degree 1 on displaced agents.  X is *one-path* if the displaced agents can be listed x_0, ..., x_t so
that Y_{x_{i-1}} lies in X_{x_i} for 1 <= i <= t, and the pick of x_t lies anywhere (it becomes junk): exactly the
shape of one improving chain followed by a free completion, with x_0 taking junk (or Y_{x_t}).

For every hard start (picks without a one-absorber completion) this computes, by SAT on sdclib's encoding:
  k*  the fewest displaced agents over the dominating EFX0 allocations;
  whether some, and whether every, dominating allocation with k* displaced agents is one-path (enumerating the
      distinct placements of the displaced picks; the junk placement is projected away);
  the same with "one absorber" added for the one-path ones: the allocation gives two or more goods outside the
      displaced picks and the chain's H-sets to at most one agent (approximated by: at most one agent holds two or more
      goods of J + {Y_{x_t}} that are not part of its received pick).

    python3 k4/ttc/displace.py SRC [N SEED] [nmax=5] [enum=200]"""
import sys, json, random, collections, time, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
import ttclib as T


def base_clauses(E, Y):
    cl = list(E.cl)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
    for i in range(E.n):
        u = E.v[i].get(Y[i], 0) if Y[i] is not None else 0
        for S, y in E.y[i].items():
            if E.val(i, S) < u:
                cl.append([-y])
    return cl


def placement(E, Y, model):
    pos = set(l for l in model if l > 0)
    out = {}
    for j in range(E.n):
        if Y[j] is None:
            continue
        for a in range(E.n):
            if E.x[Y[j]][a] in pos:
                out[j] = a
    return out


def one_path(E, Y, pl):
    disp = [j for j, a in pl.items() if a != j]
    if not disp:
        return True
    D = set(disp)
    # arcs among displaced agents: j -> pl[j] when pl[j] displaced.  Try every end x_t: without x_t's arc (its pick
    # becomes junk and may lie anywhere) the arcs must form one path covering D, from x_0 to x_t
    for xt in disp:
        nxt = {j: pl[j] for j in disp if j != xt and pl[j] in D}
        if len(nxt) != len(D) - 1:
            continue
        starts = [j for j in D if j not in nxt.values()]
        if len(starts) != 1:
            continue
        cur = starts[0]; seenp = {cur}
        while cur in nxt:
            cur = nxt[cur]
            if cur in seenp:
                break
            seenp.add(cur)
        if seenp == D and cur == xt:
            return True
    return False


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a)
    nmax = int(kw.get('nmax', '5')); enum = int(kw.get('enum', '200'))
    print('$ python3 k4/ttc/displace.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); ex = []
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); seen = set()
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0])
            if Y in seen:
                continue
            seen.add(Y); base = T.base_of(E, Y)
            if T.extends_A(E, base, 1):
                continue
            C['distinct hard starts'] += 1
            cl = base_clauses(E, Y)
            disp = []; top = E.top
            for j in range(n):
                if Y[j] is not None:
                    top += 1; d = top; disp.append(d)
                    cl.append([-d, -E.x[Y[j]][j]]); cl.append([d, E.x[Y[j]][j]])
            kstar = None
            for k in range(0, n + 1):
                enc = CardEnc.atmost(lits=disp, bound=k, top_id=top, encoding=EncType.seqcounter)
                S = Cadical153(bootstrap_with=cl + enc.clauses)
                if S.solve():
                    kstar = k
                    pls = []; proj = [E.x[Y[j]][a] for j in range(n) if Y[j] is not None for a in range(n)]
                    while S.solve() and len(pls) < enum:
                        md = S.get_model(); pls.append(placement(E, Y, md))
                        S.add_clause([-l for l in proj if l in set(md)])
                    if len(pls) >= enum and S.solve():
                        C['enumeration capped (not every minimal placement checked)'] += 1
                    S.delete(); break
                S.delete()
            if kstar is None:
                C['NOT DOMINATED (MD fails)'] += 1
                print('MD FAILS', name, json.dumps((sets, vals)), Y, flush=True)
                continue
            C['k* = %d' % kstar] += 1
            op = [one_path(E, Y, pl) for pl in pls]
            C['some minimal one-path'] += any(op)
            C['every minimal one-path'] += all(op)
            if not all(op) and len(ex) < 4:
                bad = [pl for pl, o in zip(pls, op) if not o][0]
                ex.append((name, json.dumps((sets, vals)), 'picks', Y, 'k*', kstar,
                           'non-path placement (pick owner -> holder)', bad))
    for k in sorted(C):
        print(k, C[k])
    for e in ex:
        print('  non-path minimal:', *e)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
