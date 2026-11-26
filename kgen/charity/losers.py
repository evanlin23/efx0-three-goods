"""How few agents must lose for a complete EFX0 allocation to exist (kgen/charity.md §9)?  For a stranded state X
of the families S(sigma, 3), S'(sigma, 3), S'(sigma, 4) and the CH-F instances: the largest number of agents i with
v_i(Y_i) >= v_i(X_i) over complete EFX0 allocations Y (SAT, chlib.Enc with a cardinality bound over per-agent
indicators), and which agents lose in an optimal Y.

    python3 kgen/charity/losers.py"""
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from chlib import Inst, Enc, efx0, pool_of
from stuck_family import build
import w_counterexample as WC


def fewest_losers(I, X):
    E = Enc(I, charity=False)
    u = [I.val(i, X[i]) for i in range(I.n)]
    pool = [E.x[g][I.n] for g in range(I.m)]
    for keep in range(I.n, -1, -1):
        cl = list(E.cl); top = E.top; ind = []
        for i in range(I.n):
            top += 1; z = top; ind.append(z)
            cl.append([-z] + [y for S, y in E.y[i].items() if I.val(i, S) >= u[i]])
        c = CardEnc.atleast(lits=ind, bound=keep, top_id=top, encoding=EncType.seqcounter)
        cl += c.clauses; top = max(top, c.nv)
        cl += [[-x] for x in pool]                            # complete
        s = Cadical153(bootstrap_with=cl); ok = s.solve(); Y = E.decode(s.get_model()) if ok else None; s.delete()
        if Y is not None:
            assert efx0(I, Y) and not pool_of(I, Y)
            return I.n - keep, [i for i in range(I.n) if I.val(i, Y[i]) < u[i]], Y
    return None, None, None


if __name__ == '__main__':
    print('$ python3 kgen/charity/losers.py', flush=True)
    cases = []
    for s in (2, 3, 4, 5):
        for own in (False, True):
            I, X, P, src, ch = build(s, 3, own=own)
            cases.append(("%s(%d, 3)" % ("S'" if own else 'S', s), I, X, src, ch))
    for s in (2, 3, 4):
        I, X, P, src, ch = build(s, 4, own=True)
        cases.append(("S'(%d, 4)" % s, I, X, src, ch))
    cases.append(('CH-F k4', Inst(9, 14, WC.V4), WC.X4, [6, 7, 8], None))
    cases.append(('CH-F k3', Inst(12, 17, WC.V3), WC.X3, [7, 9, 11], None))
    for name, I, X, src, ch in cases:
        k, L, Y = fewest_losers(I, X)
        role = lambda a: 'source' if a in src else ('champion' if (ch and a in ch.values()) or (ch is None and a < 6)
                                                    else 'relay')
        print('%s: n %d, stranded %d | fewest agents worse off in a complete EFX0 allocation: %d (%s)' % (
            name, I.n, len(pool_of(I, X)), k, ', '.join('%d %s' % (a, role(a)) for a in L)), flush=True)
