"""Reproduce the failed reductions of attempts/k4-mincex-drop-private.md and attempts/k4-mincex-px-open.md: for a
configuration, a profile and a reduction, print an admissible local state of Y that has no extension (k4/reduce4.py).
Usage: mincex_attempts.py drop-private | px-open"""
import sys, itertools
import numpy as np
import reduce4 as R4, mincex4 as M


def failing_state(red, prof):
    cfg = red.cfg
    for Yb, Ob, src in red.states():
        adm = R4.adm_array(cfg, red.admissible(Yb, Ob, src))
        if adm is None or not adm[prof]: continue
        if not any(all(R4.safe_mask(cfg, s, v)[k] for s, v, k in zip(cfg.agents, R4.views_of(cfg, *X), prof))
                   for X in red.extensions(Yb, Ob, src)):
            return Yb, Ob, src
    return None


def show(cfg, red, prof):
    st = failing_state(red, prof)
    vals = {s: cfg.valuation(s, k) for s, k in zip(cfg.agents, prof)}
    print('  %s under %s: %s' % (red.name, vals, 'no failing state' if st is None else
          'Y = S\': %s | outside: %s | unenvied: %s' % (st[0], st[1], st[2])))


def main():
    what = sys.argv[1]
    if what == 'drop-private':
        for kind in ('P3', 'P4'):
            cfg = M.single_config(kind)
            reds = M.single_reductions(cfg)
            union = np.zeros(cfg.shape, dtype=bool)
            for red in reds: union |= R4.run(red, 1)[0]
            print('%s: %d gadgets (every valuation class of e\' on the boundary goods), %d of %d types reduced' % (
                cfg.name, len(reds), union.sum(), union.size))
        cfg = M.single_config('P3')
        prof = (0,)
        for red in M.single_reductions(cfg)[:3]: show(cfg, red, prof)
    else:
        cfg = M.px_config('Q3')
        union, reds = M.gadget_cover(cfg, jobs=4)
        dl = R4.Reduction(cfg, 'DEL', {}, set(), source=True)
        union |= R4.run(dl, 4)[0]
        for prof in zip(*np.nonzero(~union)):
            print('not reduced:', {s: cfg.valuation(s, k) for s, k in zip(cfg.agents, prof)})
            show(cfg, dl, prof)
            con = R4.Reduction(cfg, 'CON-f (h = e with g renamed y)', {'h': ('fix', {'y': 4, 'a': 3, 'b': 2})}, set(),
                               source=True)
            show(cfg, con, prof)


if __name__ == '__main__':
    main()
