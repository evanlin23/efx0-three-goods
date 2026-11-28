"""Lemmas Ω⁺ and Ψ⁺ (k4/one4.md §2).  Ω⁺: Lemma Ω of k4/c4one.md §6 with (H3) replaced by (H3⁺): either no agent other than x needs
a_x, or x needs, besides a_x, a good g held as its pick by an agent h off the chain, not upgraded, such that no agent
other than x needs g.  The verification of the conclusion is c4omega1.check's own (it rebuilds the run rho', checks it is
a run of Phase 1 with the rotated picks, replays the upgrades, and checks omega' <= omega - 1); only the (H3) test is
replaced, by source substitution.  Ψ⁺: Lemma Ψ (the falling chain) with (Ψ3) (y_k upgrades) and (Ψ4) replaced by
(Ψ3⁺), the same compensation condition (x needs, besides a_x, a good g picked by an agent off the fall chain, not
upgraded, needed by no agent other than x); y_k is not upgraded, and the check verifies omega' <= omega - 1 directly.
Run on the residual cases of k4/one4_residual.py (no proved move applies).
    python3 k4/one4_omega_plus.py FILE [--general]"""
import os, sys, re, json, gzip, types, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, 'c4tools')); sys.path.insert(0, HERE)
import c4omega1 as O

SRC = open(O.__file__).read()
OLD = """    if any(a_x in above(i) for i in range(n) if i not in (x,) and i not in upg and Y[i] != a_x):
        return 'H3 fails: another agent needs a_x'"""
NEW = """    _oth = [i for i in range(n) if i != x and i not in upg and Y[i] != a_x and a_x in above(i)]
    if _oth:
        _h3p = any(g != a_x and any(Y[h] == g and h not in chain and h not in upg for h in range(n))
                   and not any(g in above(i) for i in range(n) if i != x and i not in upg) for g in above(x))
        if not (RELAX or _h3p): return 'H3+ fails'
        TAG[0] = 'H3 fails, H3+ %s' % ('holds' if _h3p else 'fails')
    else: TAG[0] = 'H3 holds'"""
assert OLD in SRC
src = SRC.replace(OLD, NEW).replace("if __name__ == '__main__':", "if False:")
PSI_OLD1 = """    if psi_q and yk != q: return 'Psi3 fails: the last agent of the chain has no envy-free pair'"""
PSI_NEW1 = """    plus = (not cands) and any(g != a_x and any(Y[h] == g and h not in chain and h not in upg and h != x for h in range(n))
                               and not any(g in above(i) for i in range(n) if i != x and i not in upg) for g in above(x))
    if psi_q and yk != q and not plus: return 'Psi3 fails: the last agent of the chain has no envy-free pair'"""
PSI_OLD2 = """    if any(Y[yk] in above(i) for i in range(n) if i not in chain and i != x and i not in upg): return 'Psi4 fails'"""
PSI_NEW2 = """    if not plus and any(Y[yk] in above(i) for i in range(n) if i not in chain and i != x and i not in upg): return 'Psi4 fails'"""
PSI_OLD3 = """    if psi_q:
        w1 = st.omega(); fin = T.upgrades(st, 2); w2 = fin.omega()"""
PSI_NEW3 = """    if plus:
        w1 = st.omega(); w2 = T.upgrades(st, 2).omega()
        if w1 > w - 1 or w2 > w1: return 'PSI+ PROOF STEP 2 FAILS: omega %d -> %d -> %d' % (w, w1, w2)
        return 'Psi+ hypotheses hold; omega drops (fall chain of %d)' % len(chain)
    if psi_q:
        w1 = st.omega(); fin = T.upgrades(st, 2); w2 = fin.omega()"""
for o_, n_ in ((PSI_OLD1, PSI_NEW1), (PSI_OLD2, PSI_NEW2), (PSI_OLD3, PSI_NEW3)):
    assert o_ in src, o_[:60]
    src = src.replace(o_, n_)
M = types.ModuleType('c4omega_plus'); M.__file__ = O.__file__
exec(compile(src, O.__file__, 'exec'), M.__dict__)
M.TAG = ['']; M.RELAX = False

import one4_residual as R


def verdict(l, relax):
    M.RELAX = relax
    n = len(json.loads(re.search(r'sets=(\S+)', l).group(1)))
    best = None
    for x in range(n):
        M.TAG[0] = ''
        v = M.check(l, x)
        if v.startswith('hypotheses hold'): return 'omega drops [%s, x = %d]' % (M.TAG[0], x)
        if v.startswith('PROOF'): best = 'PROOF FAILS [%s]: %s' % (M.TAG[0], v)
    for x in range(n):
        v = M.check_psi(l, x)
        if v.startswith('Psi+ hypotheses hold'): return 'omega drops [Psi+, x = %d]' % x
        if 'PROOF' in v: best = 'PROOF FAILS [Psi+]: %s' % v
    return best or 'no x'


if __name__ == '__main__':
    import c4check_run
    c4check_run.build()
    print('$ python3 k4/one4_omega_plus.py', *sys.argv[1:], flush=True)
    cs = [c for c in json.load(gzip.open(sys.argv[1], 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
    T = collections.Counter(); shown = 0
    from multiprocessing import Pool
    with Pool(4) as pool:
        for res in pool.imap_unordered(R.residual, cs):
            for cls, l in res:
                v1 = verdict(l, False); v2 = verdict(l, True)
                T[(cls, 'Omega+ or Psi+:', v1.split(' [')[0] + (' via Psi+' if 'Psi+' in v1 else ''))] += 1
                T[(cls, 'Omega without (H3) at all:', v2.split(':')[0].split(' [')[0])] += 1
                if v1.startswith('PROOF') and shown < 3: print('PROOF FAILURE', l[:300], v1); shown += 1
    for k in sorted(T, key=str): print(' ', k, T[k])
