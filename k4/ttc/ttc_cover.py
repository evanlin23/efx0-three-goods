"""Which TTC runs are needed?  (k4/ttc.md §5.)  For every hard start and every request preference (head/inner over
val, minval, minimal, lean, small) and mode ('one', 'head'), the set of heads p whose YRMH-IGYT run (priority p,
then reverse pi) repairs the start: (A) one-absorber completion, any absorber; (H) one-absorber completion with p
itself the absorber (the pool is the head's, as in Abdulkadiroglu-Sonmez's TTC).  Then a greedy cover: the fewest
(pref, mode) pairs such that every hard start has a repairing head under one of them, for (A) and for (H).

    python3 k4/ttc/ttc_cover.py SRC [N SEED] [nmax=5] [rules=val,minval,minimal,lean,small]"""
import sys, random, collections, json, time
import ttclib as T

BASIC = ['val', 'minval', 'minimal', 'lean', 'small', 'poolval', 'poolmin']
PREFS = [h + '/' + i for h in BASIC for i in BASIC]
MODES = ['one', 'head']


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    global PREFS
    if 'rules' in kw:      # rules=val,minval,...: the basic rules whose head/inner pairs are tried (default: all seven)
        basic = kw['rules'].split(','); PREFS = [h + '/' + i for h in basic for i in basic]
    print('$ python3 k4/ttc/ttc_cover.py', *argv, flush=True)
    t0 = time.time(); rng = random.Random(seed + 7)
    rowsA = []; rowsH = []; names = []
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); seen = set()
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
            if Y in seen or T.extends_A(E, b, 1):
                continue
            seen.add(Y)
            A = set(); H = set(); memo = {}
            for pref in PREFS:
                for mode in MODES:
                    for p in range(n):
                        prio = [p] + [i for i in pi[::-1] if i != p]
                        b2, tr = T.yrmh(E, b, prio, pref, 'pi', mode)
                        if not tr:
                            continue
                        if b2 not in memo:
                            memo[b2] = T.extends_A(E, b2, 1)
                        if memo[b2]:
                            A.add((pref, mode))
                            if T.extends_owner(E, b2, p):
                                H.add((pref, mode))
            rowsA.append(A); rowsH.append(H); names.append((name, Y))
    print('distinct hard starts', len(rowsA))
    for lab, rows in (('A (any absorber)', rowsA), ('H (the head absorbs)', rowsH)):
        cov = sum(1 for r in rows if r)
        print('%s: some TTC run repairs %d of %d' % (lab, cov, len(rows)))
        left = [r for r in rows if r]; chosen = []
        while left:
            cnt = collections.Counter(x for r in left for x in r)
            best = max(sorted(cnt), key=lambda x: cnt[x])
            chosen.append((best, cnt[best])); left = [r for r in left if best not in r]
        print('   greedy cover:', chosen)
        single = collections.Counter(x for r in rows for x in r)
        print('   best single (pref, mode):', sorted(single.items(), key=lambda kv: (-kv[1], kv[0]))[:3])
        for (nm, Y), r in zip(names, rows):
            if not r:
                print('   no TTC run:', nm, Y)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
