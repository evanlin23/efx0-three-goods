"""Glued gadgets: two cores glued by identifying goods, searched over every strict profile (cegar.py).

Sources: the GM4 family of the DE4 screen set (k4/gm4.md; n = 4, m = 7 or 6: Pareto-maximal partial EFX₀ allocations
that cannot be completed). For a pair (A, B) and s = 1..S, goods of B are identified with goods of A (every choice of
s distinct goods of each, in a random sample), keeping the result a k = 4 core (search4/check.py core test).
Usage: glue.py [--s=1,2] [--pairs=K] [--per=K] [--limit=SEC] [--seed=S] [--fixed] --tag=NAME
  --fixed: agents keep their gadget type (one type each) except those valuing a glued good (every type)."""
import sys, os, json, gzip, time, random, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); K4 = os.path.dirname(HERE); ROOT = os.path.dirname(K4)
sys.path.insert(0, HERE); sys.path.insert(0, K4); sys.path.insert(0, os.path.join(K4, 'sdc'))
import cegar, check, search4 as S4

def gm4():
    import sdc_need
    out, seen = [], set()
    for name, sets, vals, m in sdc_need.instances('screen'):
        if name.startswith('GM4-'):
            out.append((name, sets, vals, m))
    return out

def glue(A, B, idA, idB):
    """A, B: (sets, vals, m). Goods idB[k] of B become goods idA[k] of A; B's other goods are renumbered after A's."""
    sa, va, ma = A; sb, vb, mb = B
    mp, nxt = {}, ma
    for g in range(mb):
        if g in idB: mp[g] = idA[idB.index(g)]
        else: mp[g] = nxt; nxt += 1
    sets = [list(S) for S in sa] + [[mp[g] for g in S] for S in sb]
    vals = [list(v) for v in va] + [list(v) for v in vb]
    return sets, vals, nxt

def main():
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1)))
    S = list(map(int, opt.get('s', '1,2').split(',')))
    G = gm4()
    pairs = [(a, b) for a in range(len(G)) for b in range(a, len(G))]
    rng.shuffle(pairs); pairs = pairs[:int(opt.get('pairs', 10))]
    print('command: python3 k4/hunt/glue.py ' + ' '.join(sys.argv[1:]), flush=True)
    out = []
    for a, b in pairs:
        A, B = G[a], G[b]
        for s in S:
            cands = [(ia, ib) for ia in itertools.combinations(range(A[3]), s) for ib in itertools.permutations(range(B[3]), s)]
            rng.shuffle(cands)
            k = 0
            for ia, ib in cands:
                if k >= int(opt.get('per', 2)): break
                sets, vals, m = glue((A[1], A[2], A[3]), (B[1], B[2], B[3]), list(ia), list(ib))
                n = len(sets)
                if not check.is_core(n, m, sets, sum(len(x) == 4 for x in sets)): continue
                k += 1
                doms = None
                if 'fixed' in opt:
                    C = S4.Core(n, m, sets)
                    glued = set(ia)
                    doms = []
                    for i, (Si, vi) in enumerate(zip(sets, vals)):
                        if glued & set(Si): doms.append(C.dom[i])
                        else:                  # the gadget's own type: the domain member with the same comparisons
                            key = check.types.__wrapped__ if False else None
                            def sig(v):
                                d = len(v); subs = range(1, 1 << d)
                                sm = {T: sum(v[p] for p in range(d) if T >> p & 1) for T in subs}
                                return tuple(sm[X] > sm[Y] for X in subs for Y in subs if X < Y and not X & Y)
                            doms.append([t for t in C.dom[i] if sig(t) == sig(vi)])
                    if any(not d for d in doms): print('  type not strict/balanced: skipped', flush=True); continue
                t0 = time.time()
                H = cegar.Hunt(sets, m, domains=doms, tries=2)
                st = H.run(cap=1, time_limit=float(opt.get('limit', 300)))
                rec = {'name': f'{A[0]}+{B[0]} s={s} {list(ia)}~{list(ib)}', 'n': n, 'm': m, 'sets': sets,
                       'vals': vals, 'fixed': 'fixed' in opt, 'status': st, 'time': round(time.time() - t0, 1), **H.stats()}
                if H.fails: rec['fails'] = [[list(H.dom[i][t]) for i, t in enumerate(p)] for p in H.fails]
                print(f"{rec['name']}: n={n} m={m} beta={sum(map(len, sets)) - n - m + 1} {st} {rec['time']}s {H.stats()}"
                      + (f" FAIL {rec['fails']}" if H.fails else ''), flush=True)
                out.append(rec)
    with open(os.path.join(ROOT, 'results', 'k4_hunt', f"glue_{opt['tag']}.json"), 'w') as f: json.dump(out, f)

if __name__ == '__main__':
    main()
