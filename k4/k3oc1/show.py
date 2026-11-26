"""Pretty-print a k = 3 state: each agent's ranking, holding (type A/B/C/E or pair), frozen/free, wanters; junk."""
from de_moves import info, blockers
from k3lib import bundles

def show(rk, m, base, order=None):
    n = len(rk); B, J, rank, U, wants, wanters, free = info(rk, m, base)
    lines = []
    for i in range(n):
        h = B[i]
        if not h: t = 'E'
        elif len(h) == 2: t = 'P'
        else: t = 'ABC'[rk[i].index(h[0])] if h[0] in rk[i] else '?'
        ws = wanters.get(h[0], []) if len(h) == 1 else []
        st = 'free' if i in free else ('pair' if U[i] else 'frozen by %s' % ws)
        lines.append('  %d: %s>%s>%s  holds %s (%s) %s' % (i, rk[i][0], rk[i][1], rk[i][2], h, t, st))
    lines.append('  junk %s%s' % (J, '' if order is None else '  order %s' % (order,)))
    for o in free:
        bl = blockers(rk, base, o, B, J)
        if bl: lines.append('  blockers of %d: %s' % (o, bl))
    return '\n'.join(lines)
