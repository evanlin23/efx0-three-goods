"""Reproduces the failed reductions of attempts/min-cex-*.md (proofs/min_counterexample.md, §8).
For each reduction family, prints how many ranking profiles it reduces and, for the first profile it does not, one
local state of Y (Lemma M1) with no valid extension.
Usage (from the repository root): python attempts/min_cex_failed.py [window|pq|all]"""
import itertools, sys, os, multiprocessing
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
from reduce import Reduction, fmt_state

PERMS = list(itertools.permutations(range(3)))
order = lambda p, goods: tuple(goods[k] for k in p)
sub = lambda t, a, b: tuple(b if g == a else g for g in t)


def window(pr, source=False):
    """Three consecutive P-agents on a thread, x - L - gl - e - gr - R - y; contract e (merge gl, gr into g*)."""
    L, e, R = order(pr[0], ('x', 'gl', 'pL')), order(pr[1], ('gl', 'gr', 'p')), order(pr[2], ('gr', 'y', 'pR'))
    return Reduction({'L': L, 'e': e, 'R': R}, I={'gl', 'gr', 'p', 'pL', 'pR'}, D={'x', 'y'},
                     Sp={'L': sub(L, 'gl', 'g*'), 'R': sub(R, 'gr', 'g*')}, Ip={'g*', 'pL', 'pR'}, source=source)


def pq_con(pr):
    """P-agent e = (gl, g, p) and Q-agent u = (g, y1, y2) sharing the degree-2 good g; contract e (u values gl for g)."""
    e, u = order(pr[0], ('gl', 'g', 'p')), order(pr[1], ('g', 'y1', 'y2'))
    return Reduction({'e': e, 'u': u}, I={'g', 'p'}, D={'gl', 'y1', 'y2'}, Sp={'u': sub(u, 'g', 'gl')}, Ip=set(),
                     source=True)


def pq_del(pr):
    """The same pair; delete e, u, g, p (no gadget)."""
    e, u = order(pr[0], ('gl', 'g', 'p')), order(pr[1], ('g', 'y1', 'y2'))
    return Reduction({'e': e, 'u': u}, I={'g', 'p'}, D={'gl', 'y1', 'y2'}, Sp={}, Ip=set(), source=True)


def run(args):
    fam, pr = args
    red = {'window': window, 'pq_con': pq_con, 'pq_del': pq_del}[fam](pr)
    n, fails = red.check()
    return fam, pr, red.S, (fmt_state(*fails[0]) if fails else None)


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    tasks = []
    if which in ('window', 'all'): tasks += [('window', pr) for pr in itertools.product(PERMS, PERMS, PERMS)]
    if which in ('pq', 'all'): tasks += [(f, pr) for f in ('pq_con', 'pq_del') for pr in itertools.product(PERMS, PERMS)]
    with multiprocessing.Pool() as pool: res = pool.map(run, tasks)
    for fam in ('window', 'pq_con', 'pq_del'):
        rr = [r for r in res if r[0] == fam]
        if not rr: continue
        bad = [r for r in rr if r[3]]
        print('%s: reduces %d of %d profiles' % (fam, len(rr) - len(bad), len(rr)))
        for r in bad: print('   not reduced:', ' '.join('%s=%s' % (a, '>'.join(g)) for a, g in r[2].items()), '| e.g.', r[3])
