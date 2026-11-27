"""The pointer structure behind OC1-ED (k4/ttc.md §11).  At serial-dictatorship picks Y (junk J), Lemma GDT of
k4/sdc.md §30 (proved) gives a one-absorber completion with owner o whenever o is unwanted (nobody wants its pick; a
pickless agent counts, with y_o = none) and every frozen agent x satisfies v_x((J + {y_o}) cap R_x) <= v_x(Y_x) ((G4);
(G1)-(G3), (G5) hold automatically at picks with o unwanted).  So at a hard start (no one-absorber completion), every
unwanted o has a nonempty set
    S_o = {x frozen : v_x((J + {y_o}) cap R_x) > v_x(Y_x)}
(checked here as a sanity test of GDT).  Pointers: o -> x in S_o; from x, want paths x = x_0 <- x_1 <- ... (x_{i+1}
wants Y_{x_i}) lead to unwanted agents.  A *fixed point* is o, x in S_o and a want path from x whose last agent
wants... ending at o: x_1, ..., x_{t-1} frozen-and-wanting, and o wants Y_{x_{t-1}} (t >= 1).  It is exactly a chain of
OC1-ED's shape with head o and H_0 inside (J + {y_o}) cap R_x.  Reported per distinct hard start:
  (a) every unwanted o has S_o nonempty (GDT's consequence);
  (b) some fixed point exists;
  (c) some fixed-point chain (some improving H_0 inside (J + {y_o}) cap R_x, the head taking the pick alone or with
      junk) has a one-absorber completion with absorber o or x;  (c-head) with absorber o;
  (d) every fixed point (o, x, path) admits such a repairing choice of H_0, H_t.

    python3 k4/ttc/pointer.py SRC [N SEED] [nmax=5]"""
import sys, json, random, collections, time, itertools
import ttclib as T


def subsets(xs):
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/pointer.py', *argv, flush=True)
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
            J = [g for g in range(m) if base[g] < 0]
            v = lambda i, S: T.val(E, i, S)
            hold = [E.v[i].get(Y[i], 0) if Y[i] is not None else 0 for i in range(n)]
            wants = lambda i, j: Y[j] is not None and i != j and E.v[i].get(Y[j], 0) > hold[i]
            F = set(j for j in range(n) if any(wants(i, j) for i in range(n)))
            U = [o for o in range(n) if o not in F]
            S = {}
            for o in U:
                extra = [Y[o]] if Y[o] is not None else []
                S[o] = [x for x in F if v(x, [g for g in J + extra if E.v[x].get(g, 0) > 0]) > hold[x]]
            C['(a) every unwanted o has S_o nonempty'] += all(S[o] for o in U)
            if not all(S[o] for o in U):
                ex['(a)'].append((name, Y))
            # fixed points: o, x in S_o, want path x = x_0, x_1, ..., x_t = o (x_{i} wants Y_{x_{i-1}})
            fps = []
            def paths(p):
                last = p[-1]
                for j in range(n):
                    if j not in p and wants(j, last):
                        yield p + [j]
                        if j in F:
                            yield from paths(p + [j])
            for o in U:
                for x in S[o]:
                    for p in paths([x]):
                        if p[-1] == o:
                            fps.append((o, x, tuple(p)))
            C['(b) some fixed point'] += bool(fps)
            if not fps:
                ex['(b)'].append((name, json.dumps((sets, vals)), Y)); continue
            any_ok = False; head_ok = False; every_ok = True
            for o, x, p in fps:
                ok_here = False
                pool0 = [g for g in J + ([Y[o]] if Y[o] is not None else []) if E.v[x].get(g, 0) > 0]
                for H0 in subsets(pool0):
                    if not H0 or v(x, H0) <= hold[x]:
                        continue
                    rest_j = [g for g in J if g not in H0 and E.v[o].get(g, 0) > 0]
                    for Ht in subsets(rest_j):
                        nb = list(base)
                        if Y[o] is not None:
                            nb[Y[o]] = -1
                        for i in range(1, len(p)):
                            nb[Y[p[i - 1]]] = p[i]
                        for g in Ht:
                            nb[g] = o
                        for g in H0:
                            nb[g] = x
                        nb = tuple(nb)
                        if T.extends_owner(E, nb, o):
                            ok_here = True; head_ok = True; break
                        if T.extends_owner(E, nb, x):
                            ok_here = True; break
                    if ok_here:
                        break
                any_ok |= ok_here; every_ok &= ok_here
            C['(c) some fixed-point chain repairs (absorber o or x)'] += any_ok
            C['(c-head) ... with absorber o'] += head_ok
            C['(d) every fixed point repairs'] += every_ok
            if not any_ok:
                ex['(c)'].append((name, json.dumps((sets, vals)), Y))
            C['fixed points'] += len(fps)
    for k in sorted(C):
        print(k, C[k])
    for k, l in ex.items():
        for e in l[:2]:
            print('  fails', k, *e)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
