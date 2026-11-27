"""Is some TTC request path always repairing?  (k4/ttc.md §5.)  For every hard start: the union over every request
preference (head/inner combinations of val, minval, minimal, lean, small), every head p (priority p, then reverse pi)
and both modes 'one' and 'head' of YRMH-IGYT runs; does some run's result have a one-absorber completion?  Prints the
hard starts on which none does.

    python3 k4/ttc/ttc_union.py SRC [N SEED] [nmax=5] [rules=val,minval,minimal,lean,small]"""
import sys, random, collections, json, time
import ttclib as T

BASIC = ['val', 'minval', 'minimal', 'lean', 'small', 'poolval', 'poolmin']
PREFS = [h + '/' + i for h in BASIC for i in BASIC]


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    global PREFS
    if 'rules' in kw:      # rules=val,minval,...: the basic rules whose head/inner pairs are tried (default: all seven)
        basic = kw['rules'].split(','); PREFS = [h + '/' + i for h in basic for i in basic]
    print('$ python3 k4/ttc/ttc_union.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7)
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); seen = set()
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
            if Y in seen or T.extends_A(E, b, 1):
                continue
            seen.add(Y); C['distinct hard starts'] += 1
            ok = False; states = set()
            for pref in PREFS:
                for p in range(n):
                    prio = [p] + [i for i in pi[::-1] if i != p]
                    for mode in ('one', 'head'):
                        b2, tr = T.yrmh(E, b, prio, pref, 'pi', mode)
                        if tr:
                            states.add(b2)
            ok = any(T.extends_A(E, s, 1) for s in states)
            C['some TTC run repairs'] += ok
            if not ok:
                print('NO TTC RUN REPAIRS', name, json.dumps((sets, vals)), 'picks', Y, 'distinct run results',
                      len(states), flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
