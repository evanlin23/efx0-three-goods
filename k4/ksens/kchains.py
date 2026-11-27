"""Least number of improving chains after which a start extends (k4/ksens.md §4), by breadth-first search over
states with ocsat.py: level 0 = the picks, level c = every state c chains reach (each chain as in §29, applied to the
current bases; enumerated by SAT with blocking clauses); the answer is the least c whose level has a state with a
completion ('free', or with at most A absorbers).  The last level is tested with one SAT call per state
(chain='need'), so states of level cmax are never listed.

    python3 k4/ksens/kchains.py '[[sets], [vals]]' ORDER CMAX [A] [cap:N]"""
import sys, json, time
import _paths
import ocsat


def reach(O, base, cap):
    """the states one chain reaches from base, whether or not they have a completion: a fresh solver with the chain
    clauses only (no EFX0 clauses)"""
    from pysat.solvers import Cadical153
    S0 = O.S; top0 = O.top
    O.S = Cadical153()
    for g in range(O.m):                 # allocation variables: exactly one owner, never the pool (no EFX0 clauses)
        O.S.add_clause([O.E.x[g][a] for a in range(O.n)])
        for a in range(O.n):
            for a2 in range(a + 1, O.n): O.S.add_clause([-O.E.x[g][a], -O.E.x[g][a2]])
    act, nb = O.group(base, chain='need')
    keys = sorted(nb); out = []
    while len(out) < cap and O.S.solve(assumptions=[act]):
        mdl = set(l for l in O.S.get_model() if l > 0)
        st = tuple(tuple(sorted(g for (g, i) in keys if i == a and nb[(g, i)] in mdl)) for a in range(O.n))
        out.append([list(b) for b in st])
        O.S.add_clause([-act] + [-nb[k] if nb[k] in mdl else nb[k] for k in keys])
    O.S.delete(); O.S = S0
    return out, len(out) >= cap


def min_chains(sets, vals, m, order, cmax, A=None, cap=200000, log=None):
    n = len(sets); O = ocsat.OC(sets, vals, m)
    Y = ocsat.sd(sets, vals, order, m); level = [ocsat.bases_of(Y, n)]
    if O.holds(level[0], chain='none', A=A): O.close(); return 0, {}
    info = {}
    for c in range(1, cmax + 1):
        if any(O.holds(b, chain='need', A=A) for b in level): O.close(); return c, info
        if log: print('   no state of level', c - 1, 'is repaired by one more chain', flush=True)
        if c == cmax: break
        nxt = {}; capped = False
        for b in level:
            sts, cp = reach(O, b, cap); capped |= cp
            for s in sts: nxt[json.dumps(s)] = s
        info['level %d states' % c] = len(nxt); info['level %d capped' % c] = capped
        if log: print('   level', c, 'states', len(nxt), 'capped' if capped else '', flush=True)
        level = list(nxt.values())
    O.close(); return None, info


if __name__ == '__main__':
    sets, vals = json.loads(sys.argv[1])[:2]; order = tuple(json.loads(sys.argv[2])); cmax = int(sys.argv[3])
    A = None; cap = 200000
    for a in sys.argv[4:]:
        if a.startswith('cap:'): cap = int(a[4:])
        else: A = int(a)
    m = 1 + max(max(s) for s in sets); t0 = time.time()
    c, info = min_chains(sets, vals, m, order, cmax, A, cap, log=True)
    print('least number of chains', c if c is not None else '> %d' % cmax, info, '%.0f s' % (time.time() - t0))
