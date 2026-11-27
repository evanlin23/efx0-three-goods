"""Hardest profiles of a certified core: few EFX₀ allocations (EVIDENCE about hardness, not a certificate).

Given a core and its certificate allocations A_1..A_K: with the ordinal outer encoding of cegar.py, the clause
"A_k is not EFX₀" is relaxed by an indicator e_k (C_k OR e_k) and at most c of the e_k may be true, so a model is a
profile under which at most c certificate allocations are EFX₀ (c = 1 is the least possible). For up to P such
profiles, all EFX₀ allocations are counted exactly (inner SAT of search4.Core with blocking clauses, up to a cap).
Usage: hardest.py CERT.json.gz [--name=..|--idx=..|--top=K] [--c=1] [--profiles=P] [--cap=5000]"""
import sys, os, json, gzip, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import cegar
from pysat.card import CardEnc, EncType


def count_efx0(H, prof, cap):
    """Number of EFX₀ allocations under prof (all of them, up to cap), with search4's inner encoding."""
    from pysat.solvers import Solver
    C = H.C
    sol, x, z = C.inner(None, None)
    cnt = 0
    while cnt < cap and sol.solve(assumptions=[z[i][t] for i, t in enumerate(prof)]):
        mod = sol.get_model()
        A = [next(j for j in range(H.n) if mod[x[g][j] - 1] > 0) for g in range(H.m)]
        assert cegar.efx0_raw(H.sets, [H.dom[i][t] for i, t in enumerate(prof)], A, H.n)
        sol.add_clause([-x[g][A[g]] for g in range(H.m)])
        cnt += 1
    sol.delete()
    return cnt


def hardest(sets, m, allocs, c=1, profiles=5, cap=5000, domains=None):
    H = cegar.Hunt(sets, m, domains=domains, use_aut=False)
    es = []
    for A in allocs:
        e = H.vp.id(('e', len(es))); es.append(e)
        H.out.add_clause(H.clause(A) + [e])
    for cl in CardEnc.atmost(es, c, vpool=H.vp, encoding=EncType.seqcounter).clauses: H.out.add_clause(cl)
    res = []
    for _ in range(profiles):
        if not H.out.solve(): break
        mod = H.out.get_model()
        prof = [next(t for t, v in enumerate(zi) if mod[v - 1] > 0) for zi in H.z]
        k = count_efx0(H, prof, cap)
        res.append((k, [list(H.dom[i][t]) for i, t in enumerate(prof)]))
        H.out.add_clause([-H.z[i][t] for i, t in enumerate(prof)])
    return sorted(res)


def main():
    f = [a for a in sys.argv[1:] if not a.startswith('--')][0]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    d = json.load(gzip.open(f, 'rt'))
    cores = d['cores'] if isinstance(d, dict) else d
    for c in cores:
        c['allocs'] = [[int(ch, 36) for ch in A] if isinstance(A, str) else A for A in c['allocs']]
        c.setdefault('m', d.get('m') if isinstance(d, dict) else None)
    if 'name' in opt: cores = [c for c in cores if c.get('name') == opt['name']]
    if 'idx' in opt: cores = [c for c in cores if c.get('idx') == int(opt['idx'])]
    if 'top' in opt: cores = sorted(cores, key=lambda c: -len(c['allocs']))[:int(opt['top'])]
    print('command: python3 k4/hunt/hardest.py ' + ' '.join(sys.argv[1:]), flush=True)
    for c in cores:
        t0 = time.time()
        res = hardest(c['sets'], c['m'], c['allocs'], int(opt.get('c', 1)), int(opt.get('profiles', 5)), int(opt.get('cap', 5000)))
        best = res[0] if res else None
        print(f"{c.get('name', c.get('idx'))} {c['sets']}: {len(c['allocs'])} certificate allocations; fewest EFX₀ "
              f"allocations found {best[0] if best else '-'} at {best[1] if best else '-'}; counts {[k for k, _ in res]} "
              f"[{time.time() - t0:.0f}s]", flush=True)


if __name__ == '__main__':
    main()
