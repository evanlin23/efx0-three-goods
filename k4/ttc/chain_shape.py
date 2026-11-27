"""Shapes of the repairing chains whose head absorbs (k4/ttc.md §11).  For every hard start (picks without a one-absorber
completion) and every improving chain x_0, ..., x_t with t >= 1 (every description, de_free moves) whose result has a
one-absorber completion with absorber x_t (ttclib.extends_owner), record the features
  D0  x_0 is dangerous at the start (frozen and valuing junk);
  F0  x_0 is frozen at the start;
  PJ  x_0 takes junk only (H_0 inside J, not the head's base);
  NJ  no junk for x_1, ..., x_t (H_i empty for i >= 1);
  NJH no junk for x_1, ..., x_{t-1} (the head may take junk);
  UH  the head is unwanted at the start (nobody wants its pick);
  LAST the head is the last agent of the order (for at least one order giving these picks: reported per order);
  M0  H_0 is inclusion-minimal (no junk good can be dropped from x_0's new base);
  T1  t = 1 (a swap: x_1 takes x_0's pick, x_0 takes junk);
and count the hard starts having a head-absorbed repairing chain with each conjunction of features.

    python3 k4/ttc/chain_shape.py SRC [N SEED] [nmax=5]"""
import sys, json, random, collections, time, itertools
import ttclib as T

CONJ = [(), ('D0',), ('F0',), ('PJ',), ('NJH',), ('NJ',), ('UH',), ('M0',), ('T1',),
        ('D0', 'PJ'), ('D0', 'PJ', 'NJH'), ('D0', 'PJ', 'NJ'), ('D0', 'PJ', 'NJ', 'UH'), ('D0', 'PJ', 'NJH', 'UH'),
        ('F0', 'PJ', 'NJ', 'UH'), ('D0', 'PJ', 'NJ', 'UH', 'M0'), ('D0', 'PJ', 'NJH', 'UH', 'M0'),
        ('D0', 'NJH'), ('D0', 'NJH', 'M0'), ('D0', 'NJ'), ('D0', 'NJ', 'M0'), ('D0', 'NJH', 'UH'), ('D0', 'NJH', 'M0', 'UH'),
        ('D0', 'NJH', 'M0', 'T1'), ('D0', 'NJ', 'M0', 'UH')]


def feats(E, base, b2, path, H, D, F, wantedY):
    B = T.bundles(E, base); x0 = path[0]; xt = path[-1]; t = len(path) - 1
    J = set(g for g in range(E.m) if base[g] < 0)
    H0 = set(H.get(0, ()))
    new0 = list(H0)
    m0 = all(T.val(E, x0, [h for h in new0 if h != g]) <= T.val(E, x0, B[x0]) for g in new0)
    return {'D0': x0 in D, 'F0': x0 in F, 'PJ': H0 <= J,
            'NJ': all(not H.get(i) for i in range(1, t + 1)),
            'NJH': all(not H.get(i) for i in range(1, t)),
            'UH': xt not in wantedY, 'M0': m0, 'T1': t == 1}


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/chain_shape.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); ex = collections.defaultdict(list)
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); seen = {}
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0])
            seen.setdefault(Y, []).append(pi[-1])
        for Y, lasts in seen.items():
            base = T.base_of(E, Y)
            if T.extends_A(E, base, 1):
                continue
            C['distinct hard starts'] += 1
            D = T.dangerous_set(E, base); F = T.frozen_set(E, base)
            have = set(); memo = {}; lastok = False
            for b2, ds in T.DF.moves(E, base, describe=True, all_desc=True).items():
                for kind, path, H in ds:
                    if kind != 'chain' or len(path) < 2:
                        continue
                    key = (b2, path[-1])
                    if key not in memo:
                        memo[key] = T.extends_owner(E, b2, path[-1])
                    if not memo[key]:
                        continue
                    f = feats(E, base, b2, path, H, D, F, F)
                    if path[-1] in lasts:
                        lastok = True
                    for cj in CONJ:
                        if all(f[k] for k in cj):
                            have.add(cj)
            C['LAST: a head-absorbed repairing chain headed by the last agent of some order giving these picks'] += lastok
            for cj in CONJ:
                if cj in have:
                    C['+'.join(cj) or 'any'] += 1
                elif len(ex[cj]) < 2:
                    ex[cj].append((name, json.dumps((sets, vals)), 'picks', Y))
    H = C['distinct hard starts']
    print('distinct hard starts', H)
    for cj in CONJ:
        k = '+'.join(cj) or 'any'
        print('  %-18s %d' % (k, C[k]))
    print('  LAST              %d' % C['LAST: a head-absorbed repairing chain headed by the last agent of some order giving these picks'])
    for cj in CONJ:
        if ex[cj] and len(cj) >= 2 and 'PJ' not in cj:
            print('  no head-absorbed repairing chain of shape', '+'.join(cj), ':', *ex[cj][0])
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
