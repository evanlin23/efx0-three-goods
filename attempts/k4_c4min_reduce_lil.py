"""Replay of the local-improvement-lemma failures of attempts/k4-c4min-reduce-lil.md (k4/c4min_reduce.md §5.3), by both
implementations: k4/red_lil.py on k4/red_lib.py (Python, from the definitions) and k4/red.c -L (C, run on the one
profile). Potential Phi_r = (r', -t, Lambda), moves M1 M4 M5 (no M2). Catalogues:
  broad            the catalogue as implemented (red.c -L -Lr -L2; red_lil.py RFIRST=1): a modified receiver exchanges one
                   good of its received pair for one pool good (M5: a good of the new pool); in M5 x takes any pair
  narrow           the modification only as in Lemma R(iii) of k4/c4min.md / #50 (red.c -Ln; NARROW=1), x any pair
                   (-Lx; ANYPX=1) or #50's best P_x (no -Lx)
  narrow+recycle   with #50's recycling rule (-Lc; RECYCLE=1)
For each instance it prints, per catalogue, the number of stuck non-completable configurations of the profile (Python
and C must agree) and whether the given configuration is stuck. Ends with "ALL CONFIRMED" if every check holds.
Usage: python3 attempts/k4_c4min_reduce_lil.py   (about a minute)"""
import os, subprocess, sys, tempfile, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4'))
os.environ['RFIRST'] = '1'
os.environ.pop('M2', None)
import red_lil
from red_lib import Prof, Key, fewest_frozen_le1, bits, pc

CATS = {  # name: (NARROW, ANYPX, RECYCLE), red.c flags
    'broad': ((False, False, False), []),
    'narrow, x any pair': ((True, True, False), ['-Ln', '-Lx']),
    'narrow, x best pair': ((True, False, False), ['-Ln']),
    'narrow+recycle, x any pair': ((True, True, True), ['-Ln', '-Lx', '-Lc']),
    'narrow+recycle, x best pair': ((True, False, True), ['-Ln', '-Lc']),
}

INSTANCES = {
    # the narrow catalogue (Lemma R(iii) modification only) is stuck at n = 3; broad and narrow+recycle are not
    'N1': dict(src='results/k4_certs_3.json.gz#43', m=7,
               vals=[{0: 4, 3: 2, 4: 8, 6: 5}, {1: 2, 3: 6, 5: 10, 6: 3}, {2: 1, 4: 6, 5: 8, 6: 4}],
               key=(5, 1), Q={0: [0, 6], 2: [2, 4]}, L=[1, 3],
               stuck={'broad': False, 'narrow, x any pair': True, 'narrow, x best pair': True,
                      'narrow+recycle, x any pair': False, 'narrow+recycle, x best pair': False}),
    # with recycling added, stuck at n = 4 (two 4-good agents, 3-good x); the broad catalogue is not
    'N2': dict(src='results/k4_certs_4_n4_2.json.gz#283', m=9,
               vals=[{0: 3, 2: 7, 6: 5, 7: 6}, {1: 2, 4: 3, 6: 4, 8: 8}, {3: 2, 5: 3, 8: 4}, {5: 2, 7: 3, 8: 4}],
               key=(8, 2), Q={0: [2, 5], 1: [1, 6], 3: [4, 7]}, L=[0, 3],
               stuck={'broad': False, 'narrow+recycle, x any pair': True, 'narrow+recycle, x best pair': True}),
    # not a core (x has three private goods): even the broad catalogue is stuck, while GLOB holds (referee's instance)
    'NC': dict(src='not a core', m=9,
               vals=[{0: 10, 1: 5, 2: 4, 3: 2}, {0: 10, 4: 5, 5: 4, 6: 2}, {0: 10, 6: 2, 7: 5, 8: 4}],
               key=(0, 0), Q={1: [4, 5], 2: [7, 8]}, L=[1, 2, 3, 6],
               stuck={'broad': True}),
}


def c_binary():
    src = os.path.join(HERE, '..', 'k4', 'red.c')
    h = hashlib.sha1(open(src, 'rb').read()).hexdigest()[:12]
    out = os.path.join(tempfile.gettempdir(), 'red_' + h)
    if not os.path.exists(out): subprocess.run(['gcc', '-O2', '-o', out, src], check=True)
    return out


def run_c(inst, flags):
    lines = ['%d %d' % (len(inst['vals']), inst['m'])]
    for v in inst['vals']:
        gs = sorted(v)
        lines.append('%d %s 1' % (len(gs), ' '.join(map(str, gs))))
        lines.append(' '.join(str(v[g]) for g in gs))
    lines.append('0 1')
    out = subprocess.run([c_binary()] + flags, input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True).stdout
    return {k: int(v) for k, v in (l.split() for l in out.splitlines() if not l.startswith('EX'))}


def set_cat(c):
    red_lil.NARROW, red_lil.ANYPX, red_lil.RECYCLE = CATS[c][0]


def improving(P, Ks, K, Q, L):
    p0 = red_lil.phi(P, K, Q, L)
    for K2, Q2, L2 in red_lil.moves(P, Ks, K, Q, L):
        if red_lil.is_config(P, K2, Q2, L2) and red_lil.phi(P, K2, Q2, L2) > p0:
            return K2, Q2, L2
    return None


def completable(K, Q, L):
    return any(K.owner_status(Q, L, o)[2] for o in K.free)


ok = True
def check(name, cond):
    global ok
    print('  %-92s %s' % (name, 'yes' if cond else 'NO'))
    ok &= bool(cond)


for name, inst in INSTANCES.items():
    P = Prof(inst['vals'], inst['m'])
    f, keys = fewest_frozen_le1(P)
    Ks = {x: Key(P, g, x) for g, x in keys}
    print('%s  %s  n=%d m=%d  f=%s  keys (g, x): %s' % (name, inst['src'], P.n, P.m, f, keys))
    g, x = inst['key']; K = Ks[x]
    Q = {y: sum(1 << h for h in S) for y, S in inst['Q'].items()}; L = sum(1 << h for h in inst['L'])
    check('f = 1, omega >= 1, (%d, %d) is a key' % (g, x), f == 1 and P.m - 2 * P.n + 1 >= 1 and K.g == g)
    check('the given pairs and pool form a configuration at the key, not completable',
          red_lil.is_config(P, K, Q, L) and not completable(K, Q, L))
    print('    Phi_r = (r\', -t, Lambda) of the configuration: %s' % (red_lil.phi(P, K, Q, L),))
    for c, want in inst['stuck'].items():
        set_cat(c)
        imp = improving(P, Ks, K, Q, L)
        check('catalogue %-28s: the configuration is %s' % (c, 'stuck' if want else 'not stuck'), (imp is None) == want)
        if imp is not None:
            K2, Q2, L2 = imp
            print('      e.g. to key (%d, %d): pairs %s, pool %s, Phi_r %s' % (K2.g, K2.x, {y: sorted(bits(q)) for y, q in Q2.items()},
                  sorted(bits(L2)), red_lil.phi(P, K2, Q2, L2)))
        # every non-completable configuration of the profile: Python and C count the same stuck ones
        stuck = 0
        for K1 in Ks.values():
            for Q1, L1 in K1.configs():
                if not completable(K1, Q1, L1) and improving(P, Ks, K1, Q1, L1) is None: stuck += 1
        C = run_c(inst, ['-L', '-Lr', '-L2'] + CATS[c][1])
        check('catalogue %-28s: stuck configurations of the profile, Python %d = C %d' % (c, stuck, C.get('FAIL_lil_stuck', 0)),
              stuck == C.get('FAIL_lil_stuck', 0))
    if name == 'NC':
        priv = [h for h in P.vals[x] if h != g and all(h not in P.vals[y] for y in range(P.n) if y != x)]
        check('x = %d has the private goods %s (a k = 4 core allows at most two)' % (x, priv), len(priv) == 3)
        big = all(P.vals[y][Ks[y].g] > sum(sorted((v for h, v in P.vals[y].items() if h != Ks[y].g), reverse=True)[:2]) for y in Ks)
        check('every key is big-top', big)
        t = int(P.v(x, L & K.Ux) > P.vals[x][g])
        po = all(max((P.v(y, (1 << a) | (1 << b)) for a in bits(Q[y] | L) for b in bits(Q[y] | L) if a < b)) <= P.v(y, Q[y]) for y in K.free)
        check('t = 1 and the configuration is pool-optimal', t == 1 and po)
        best = max(red_lil.phi(P, K1, Q1, L1) for K1 in Ks.values() for Q1, L1 in K1.configs())
        maxc = [(K1, Q1, L1) for K1 in Ks.values() for Q1, L1 in K1.configs() if red_lil.phi(P, K1, Q1, L1) == best]
        check('GLOB holds: every maximum of Phi_r over all keys (%s) is completable' % (best,), all(completable(*c) for c in maxc))
        C = run_c(inst, ['-p', 'r,mt,lamR'])
        check('C: pot[r,mt,lamR]_every = 1 and glob_-t,r,lamR_every = 1',
              C.get('pot[r,mt,lamR]_every') == 1 and C.get('glob_-t,r,lamR_every') == 1)
print('ALL CONFIRMED' if ok else 'SOME CHECK FAILED')
