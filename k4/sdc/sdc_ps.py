"""SD-C-PS: for every agent w, some serial-dictatorship order's picks extend to an EFX0 allocation in which nobody
envies w (v_j(X_j) >= v_j(X_w) for all j).  Theorem DT has this form (any owner, unenvied).

    python3 k4/sdc/sdc_ps.py screen|suite [r1]"""
import sys, os, json, glob, collections
import _paths
from subsets_util import subsets
from sdsat import build
from sdsat_r1 import r1extra
from pysat.solvers import Cadical153


def ps_extra(w, r1):
    def extra(E, p, o, cl):
        if r1:
            r1extra(E, p, o, cl)
        for j in range(E.n):
            if j == w:
                continue
            for S, y in E.y[j].items():
                vs = E.val(j, S)
                rest = [g for g in E.R[j] if g not in S]
                Ts = [T for T in subsets(rest) if T and sum(E.v[j][g] for g in T) > vs]
                Ts = [T for T in Ts if not any(set(U) < set(T) for U in Ts)]
                for T in Ts:
                    cl.append([-y] + [-E.x[g][w] for g in T])
    return extra


def solve_ps(sets, vals, m, w, r1):
    E, p, o, cl = build(sets, vals, m, extra=ps_extra(w, r1))
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


if __name__ == '__main__':
    src = sys.argv[1]; r1 = len(sys.argv) > 2 and sys.argv[2] == 'r1'; C = collections.Counter()
    print('$ python3 k4/sdc/sdc_ps.py', *sys.argv[1:])
    insts = []
    if src == 'screen':
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from ss_screen import screen_set
        for name, I in screen_set():
            insts.append((name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m))
        os.chdir(cwd)
    else:
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'k4/suite/instances/*.json'))):
            d = json.load(open(f))
            if d.get('vals') and d.get('sets'):
                insts.append((d.get('id'), d['sets'], d['vals'], d.get('m') or 1 + max(max(s) for s in d['sets'])))
    for name, sets, vals, m in insts:
        C['instances'] += 1
        bad = [w for w in range(len(sets)) if not solve_ps(sets, vals, m, w, r1)]
        C['every agent can be unenvied'] += not bad
        C['agent-instances'] += len(sets); C['agent-instances failing'] += len(bad)
        if bad and C['shown'] < 4:
            C['shown'] += 1; print('FAIL', name, 'agents', bad, json.dumps((sets, vals)), flush=True)
    print(dict(C))
