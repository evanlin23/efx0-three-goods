"""Candidate TTC2 (k4/ttc.md §5): from the serial-dictatorship picks of an order pi, if they have no one-absorber
completion, try the 2n YRMH-IGYT runs with set demands (ttclib.yrmh, mode 'head': stop at the first trade through the
head) given by every head p (priority p, then reverse pi) and the two request rules
  minimal/minval : the head requests its most valuable option with an inclusion-minimal junk part; every other agent
                   its least valuable improving option;
  minval/minval  : every agent its least valuable improving option;
and accept the first run whose result has a one-absorber completion (oc_absorb.extends_A).  A start where none does is
a failure of TTC2 (not of OC1).  Also records whether some accepted run lets its head be the absorber (TTC2-H).

    python3 k4/ttc/ttc2.py SRC [N SEED] [nmax=5] [orders=K]   (SRC as in ttclib.load_items; big:6-9 samples orders)"""
import sys, os, random, collections, json, time, multiprocessing as mp
import ttclib as T

RULES = ['minimal/minval', 'minval/minval']


def check(E, pi, b):
    found = False; head_abs = False; who = None
    for pref in RULES:
        for p in [pi[-1]] + [i for i in pi[::-1][1:]]:
            prio = [p] + [i for i in pi[::-1] if i != p]
            b2, tr = T.yrmh(E, b, prio, pref, 'pi', 'head')
            if tr and T.extends_A(E, b2, 1):
                if not found:
                    who = (pref, p, p == pi[-1])
                found = True
                if T.extends_owner(E, b2, p):
                    head_abs = True
                    return True, True, who
    return found, head_abs, who


def job(args):
    name, sets, vals, m, nord, seed = args
    E = T.Enc(sets, vals, m); rng = random.Random(seed)
    C = collections.Counter(); bad = []; done = {}
    for pi in T.orders_of(len(sets), rng, nord):
        Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
        C['starts'] += 1
        key = (Y, tuple(pi))
        if T.extends_A(E, b, 1):
            continue
        C['hard starts'] += 1
        ok, h, who = check(E, pi, b)
        C['TTC2 repairs'] += ok; C['TTC2-H repairs (head absorbs)'] += h
        if ok:
            C['first repairing rule %s' % who[0]] += 1
            C['first repairing head is the last agent of pi'] += who[2]
        else:
            bad.append((pi, Y))
    return name, sets, vals, m, C, bad


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a)
    nmax = int(kw.get('nmax', '5')); nord = int(kw['orders']) if 'orders' in kw else None
    print('$ python3 k4/ttc/ttc2.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); shown = 0
    items = [(nm, s, v, m, nord, seed * 7919 + k) for k, (nm, s, v, m) in enumerate(T.load_items(src, N, seed))
             if len(s) <= nmax]
    with mp.Pool(max(1, (os.cpu_count() or 2) - 1)) as pool:
        for name, sets, vals, m, c, bad in pool.imap_unordered(job, items, chunksize=4):
            C.update(c); C['instances'] += 1
            if bad:
                C['instances with a TTC2 failure'] += 1
                if shown < 8:
                    shown += 1
                    print('TTC2 FAILS', name, json.dumps((sets, vals)), 'm', m, 'order', bad[0][0], 'picks', bad[0][1],
                          flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
