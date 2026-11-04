"""Which agents can be processed LAST in a serial-dictatorship order whose picks extend to an EFX0 allocation?
(Last agents are unwanted, the natural owners.)  Also: with the last agent unenvied.

    python3 k4/sdc/sdc_last.py screen"""
import sys, os, json, collections
import _paths
from sdsat import build
from pysat.solvers import Cadical153
from sdc_ps import ps_extra


def last_extra(w, ps):
    def extra(E, p, o, cl):
        if ps:
            ps_extra(w, False)(E, p, o, cl)
        for j in range(E.n):
            if j != w:
                cl.append([o[j][w]] if o[j][w] > 0 else [-(-o[j][w])])   # j before w
    return extra


def solve_last(sets, vals, m, w, ps=False):
    E, p, o, cl = build(sets, vals, m, extra=last_extra(w, ps))
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


if __name__ == '__main__':
    C = collections.Counter()
    print('$ python3 k4/sdc/sdc_last.py', *sys.argv[1:])
    cwd = os.getcwd(); os.chdir(_paths.DE4)
    from ss_screen import screen_set
    S = screen_set(); os.chdir(cwd)
    for name, I in S:
        sets, vals, m = I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m
        last = [w for w in range(I.n) if solve_last(sets, vals, m, w)]
        lastps = [w for w in last if solve_last(sets, vals, m, w, True)]
        C['instances'] += 1; C['agent-instances'] += I.n
        C['agents that can be last'] += len(last); C['... and unenvied'] += len(lastps)
        C['every agent can be last'] += len(last) == I.n
        C['every agent can be last and unenvied'] += len(lastps) == I.n
        if len(last) < I.n and C['shown'] < 3:
            C['shown'] += 1; print('NOT LAST', name, [w for w in range(I.n) if w not in last], json.dumps((sets, vals)))
    print(dict(C))
