"""Local validity filters on improving chains (k4/ttc.md §6).  For every hard start (picks without a one-absorber
completion) and every improving chain (de_free moves, chains only), compute local properties of the resulting state
B' (J' its junk; "wants": v_i(g) > v_i(B'_i) for g outside B'_i):
  V   valid (Draft and Exchange's validity): every wanted good is the whole base of its holder;
  T   no threat by a base: no base B'_j strictly contains a set T inside R_i with v_i(T) > v_i(B'_i), and no base inside
      R_i is worth more than v_i(B'_i) after removing its least valuable good (the EFX0 condition among the bases);
  N   no frozen agent of B' values its junk above its base: v_x(J' cap R_x) <= v_x(B'_x) for every frozen x
      (Lemma GDT's (G4) without the absorber's pick);
  X0  x_0 is not dangerous after the chain (x_0 frozen in B' and valuing junk counts as dangerous).
For each filter set: how many hard starts have a chain passing it; whether some passing chain repairs; whether every
passing chain repairs.

    python3 k4/ttc/local_rule.py SRC [N SEED] [nmax=5]"""
import sys, json, random, collections, time, itertools
import ttclib as T


def props(E, b2, x0):
    n = E.n; B = T.bundles(E, b2); J = [g for g in range(E.m) if b2[g] < 0]
    v = lambda i, S: T.val(E, i, S)
    hold = [v(i, B[i]) for i in range(n)]
    wanted_goods = set()
    for i in range(n):
        for g in E.R[i]:
            if g not in B[i] and E.v[i][g] > hold[i]:
                wanted_goods.add(g)
    V = all(any(B[j] == [g] for j in range(n)) for g in wanted_goods)
    thr = False
    for i in range(n):
        for j in range(n):
            if i == j or len(B[j]) < 2:
                continue
            Bj = B[j]
            if any(v(i, [h for h in Bj if h != g]) > hold[i] for g in Bj):
                thr = True; break
        if thr:
            break
    Tt = not thr
    frozen = set(j for j in range(n) if len(B[j]) == 1 and B[j][0] in wanted_goods)
    Nn = all(v(x, [g for g in J if E.v[x].get(g, 0) > 0]) <= hold[x] for x in frozen)
    X0 = not (x0 in frozen and any(E.v[x0].get(g, 0) > 0 for g in J))
    return {'V': V, 'T': Tt, 'N': Nn, 'X0': X0}


FILTERS = [(), ('V',), ('T',), ('V', 'T'), ('V', 'X0'), ('V', 'T', 'X0'), ('V', 'N'), ('V', 'T', 'N'), ('N',),
           ('T', 'N')]


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/local_rule.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); ex = collections.defaultdict(list)
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
            ch = []
            for b2, ds in T.DF.moves(E, base, describe=True, all_desc=True).items():
                ok = T.extends_A(E, b2, 1)
                P = [props(E, b2, d[1][0]) for d in ds]
                P = {k: any(p[k] for p in P) for k in P[0]}
                ch.append((P, ok, b2))
            for F in FILTERS:
                key = '+'.join(F) or 'none'
                pas = [(ok, b2) for P, ok, b2 in ch if all(P[k] for k in F)]
                C[key + ': some chain passes'] += bool(pas)
                C[key + ': a passing chain repairs'] += any(ok for ok, _ in pas)
                C[key + ': every passing chain repairs'] += bool(pas) and all(ok for ok, _ in pas)
                C[key + ': passing chains'] += len(pas); C[key + ': passing repairing chains'] += sum(ok for ok, _ in pas)
                if pas and not all(ok for ok, _ in pas) and len(ex[key]) < 2:
                    bad = [b2 for ok, b2 in pas if not ok][0]
                    ex[key].append((name, json.dumps((sets, vals)), 'picks', Y, 'nonrepairing', T.bundles(E, bad)))
    H = C['distinct hard starts']
    print('distinct hard starts', H)
    for F in FILTERS:
        key = '+'.join(F) or 'none'
        print('%-10s passes %4d  a passing chain repairs %4d  every passing chain repairs %4d   (chains %d, repairing %d)'
              % (key, C[key + ': some chain passes'], C[key + ': a passing chain repairs'],
                 C[key + ': every passing chain repairs'], C[key + ': passing chains'],
                 C[key + ': passing repairing chains']))
    for key, l in ex.items():
        for e in l[:1]:
            print('  %s: passing, not repairing:' % key, *e)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
