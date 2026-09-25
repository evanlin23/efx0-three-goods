"""k = 4 minimal counterexample: configurations and reductions (k4/MINCEX.md), certified with k4/reduce4.py.

Thread agents: 'P3' (3 goods, one private) and 'PP4' (4 goods, two private). Configurations 'pair' (e and f share a good
g of degree 2 and have distinct other shared goods gl, y) and 'loop' (e and f share g and G; G is valued by an outside
agent). Reductions (all with the unenvied bundle of Lemma M1(b)):
  DEL   delete e, f and the interior goods (no gadget);
  CON-e delete e, g and e's private goods; f' copies f with g renamed gl and f's private goods renamed (pair only);
  CON-f symmetric;
  GAD   (loop) one agent h valuing G at 2 and a new good at 1.
Usage: mincex4.py [pair|loop] KE KF [--jobs=J] [--write=out.json.gz]   (KE, KF in P3, PP4); prints the coverage.
"""
import sys, time, gzip, json, itertools
import numpy as np
import reduce4 as R4


def agent_goods(kind, x, y, tag):
    return (x, y) + ((('p' + tag,) if kind == 'P3' else ('p' + tag, 'q' + tag)))


def config(shape, ke, kf):
    if shape == 'pair':
        S = {'e': agent_goods(ke, 'gl', 'g', 'e'), 'f': agent_goods(kf, 'g', 'y', 'f')}
        D = {'gl', 'y'}
    else:
        S = {'e': agent_goods(ke, 'G', 'g', 'e'), 'f': agent_goods(kf, 'g', 'G', 'f')}
        D = {'G'}
    I = {g for R in S.values() for g in R} - D
    return R4.Config('%s-%s-%s' % (shape, ke, kf), S, I, D)


def signature(vals):
    """Sign vector of v(S) - v(T) over disjoint nonempty S, T (with zeros allowed): the valuation's behavior."""
    n = len(vals)
    sig = []
    for S in range(1, 1 << n):
        for T in range(1, 1 << n):
            if S & T: continue
            a = sum(vals[i] for i in range(n) if S >> i & 1) - sum(vals[i] for i in range(n) if T >> i & 1)
            sig.append((a > 0) - (a < 0))
    return tuple(sig) + tuple(v > 0 for v in vals)


def menu(k, top=6):
    """One valuation per behavior class of k goods, values in 0..top, not all zero."""
    seen = {}
    for vals in itertools.product(range(top + 1), repeat=k):
        if any(vals): seen.setdefault(signature(vals), vals)
    return sorted(seen.values())


def single_config(kind):
    if kind == 'PP4': S = {'e': ('s', 't', 'p', 'q')}
    elif kind == 'P4': S = {'e': ('s', 't', 'u', 'p')}
    else: S = {'e': ('s', 't', 'p')}
    I = {g for g in S['e'] if g.startswith('p') or g == 'q'}
    return R4.Config('single-' + kind, S, I, set(S['e']) - I)


def single_reductions(cfg):
    """Gadget e' on the boundary goods plus (if e has two private goods) one gadget good z': fewer goods."""
    D = sorted(cfg.D)
    goods = D + (["z'"] if len(cfg.I) == 2 else [])
    out = []
    for vals in menu(len(goods)):
        out.append(R4.Reduction(cfg, 'GAD1' + ''.join(map(str, vals)), {"e'": ('fix', dict(zip(goods, vals)))},
                                set(goods) - set(D), source=True))
    return out


def reductions(cfg, shape):
    out = [R4.Reduction(cfg, 'DEL', {}, set(), source=True)]
    if shape == 'pair':
        for a, b, far in (('e', 'f', 'gl'), ('f', 'e', 'y')):
            priv = cfg.priv[b]
            ren = {g: (far if g == 'g' else g + "'" if g in priv else g) for g in cfg.S[b]}
            out.append(R4.Reduction(cfg, 'CON-' + a, {b + "'": ('copy', b, ren)}, {g + "'" for g in priv},
                                    source=True))
    else:
        out.append(R4.Reduction(cfg, 'GAD', {'h': ('fix', {'G': 2, "z'": 1})}, {"z'"}, source=True))
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opts = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    jobs = int(opts.get('jobs', 4))
    if args[0] == 'px':
        shape = 'px'
        cfg = px_config(args[1], 'closed' in args)
        print('configuration %s: agents %s, I = %s, D = %s, %d profiles' % (cfg.name, cfg.S, sorted(cfg.I),
                                                                           sorted(cfg.D), int(np.prod(cfg.shape))))
        _, reds = gadget_cover(cfg, jobs)
    elif args[0] == 'single':
        shape = 'single'
        cfg = single_config(args[1])
        reds = single_reductions(cfg)
    else:
        shape, ke, kf = args
        cfg = config(shape, ke, kf)
        reds = reductions(cfg, shape)
    total = int(np.prod(cfg.shape))
    print('configuration %s: agents %s, I = %s, D = %s, %d profiles' % (cfg.name, cfg.S, sorted(cfg.I), sorted(cfg.D),
                                                                       total), flush=True)
    union = np.zeros(cfg.shape, dtype=bool)
    recs = []
    for red in reds:
        t = time.time()
        ok, kept = R4.run(red, jobs)
        new = int((ok & ~union).sum())
        union |= ok
        if shape == 'single' and not new: continue
        print('  %-6s reduces %6d of %d profiles (%d admissible states, %.1f s)' % (red.name, ok.sum(), total, len(kept),
                                                                                 time.time() - t), flush=True)
        recs.append((red, kept, ok))
    print('  together: %d of %d profiles' % (union.sum(), total), flush=True)
    if 'write' in opts:
        out = []
        for red, kept, ok in recs:
            if ok.any(): out.append(R4.record(red, R4.select(cfg, kept, ok), int(ok.sum())))
        with gzip.open(opts['write'], 'wt') as f: json.dump(out, f)
        print('  wrote %s (%d records)' % (opts['write'], len(out)))
    return union



def px_config(kind, closed=False):
    """Excess agent e (Q3, P4 or Q4) sharing a good g of degree 2 with a P3 agent f; f's other shared good y is also
    valued by e when `closed`."""
    other = {'Q3': ('a', 'b'), 'P4': ('a', 'b', 'pe'), 'Q4': ('a', 'b', 'c')}[kind]
    if closed: other = ('y',) + other[1:]
    S = {'e': ('g',) + other, 'f': ('g', 'y', 'pf')}
    I = {'g', 'pf'} | ({'pe'} if kind == 'P4' else set())
    D = {x for R in S.values() for x in R} - I
    return R4.Config('px-%s%s' % (kind, '-closed' if closed else ''), S, I, D)


def gadget_cover(cfg, jobs=4, write=None, extra=()):
    """Search one-agent gadgets h on D (+ one gadget good z' if |D| < 4), every valuation class of the menu; greedy
    choice of menu items covering the reduced profiles; certificate records for them."""
    D = sorted(cfg.D)
    goods = D + (["z'"] if len(D) < 4 else [])
    Ip = set(goods) - set(D)
    M = R4.menu(len(goods))
    t = time.time()
    ok = R4.gadget_search(cfg, 'h', goods, Ip, M, jobs)
    total = ok.shape[1]
    union = ok.any(0)
    print('  gadget search: %d menu valuations of h on %s; %d of %d profiles reduced (%.1f s)' % (
        len(M), goods, union.sum(), total, time.time() - t), flush=True)
    need, chosen = union.copy(), []
    while need.any():
        k = int((ok & need).sum(1).argmax())
        chosen.append(k); need &= ~ok[k]
    reds = [R4.Reduction(cfg, 'GAD-' + ''.join('%s=%d,' % (g, v) for g, v in zip(goods, M[k])).rstrip(','),
                         {'h': ('fix', {g: int(v) for g, v in zip(goods, M[k])})}, Ip, source=True) for k in chosen]
    for k in chosen: print('    h = %s reduces %d' % (dict(zip(goods, M[k].tolist())), ok[k].sum()))
    return union.reshape(cfg.shape), list(extra) + reds


if __name__ == '__main__':
    main()
