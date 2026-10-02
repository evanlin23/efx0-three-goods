"""DL_RC (ledger K4.DL2.RC), its variant with an unrestricted helper (K4.DL2.RCY) and DL on the key graph with
T3+ / T4 edges (K4.DL2.RCKEY) as predicates for the suite runner (compute/k4-rc-refute).

  python3 k4/suite/run.py --pred=k4/rc_pred.py:rc_c        DL_RC with k4/dlrc.c (through k4/dlrc_run.py)
  python3 k4/suite/run.py --pred=k4/rc_pred.py:rc_indep    DL_RC with k4/rt4_n5_indep.py (repo-free, PR #86 audit)
  python3 k4/suite/run.py --pred=k4/rc_pred.py:rcy_indep   DL_RC with T3+'s helper unrestricted (k4/rcy_indep.py on
                                                           k4/rt4_n5_indep.py's model)
  python3 k4/suite/run.py --pred=k4/rc_pred.py:keyplus_c   DL on the key graph, T3+ / T4 edges, with k4/dlrc.c
k4/rt4_pred.py's rc_x and keyplus_x (k4/rt4_n5_xcheck.py on main's k4/c4x_check.py) are a third implementation where
they apply (n <= 5, m <= 12).

Each returns True if the statement holds at every state (every min-frozen P with def(P) > 0, or every key with
def* > 0), False if it fails somewhere, and None when it says nothing: omega <= 0, f = 0 (Theorem Z), or the instance
is too large (rc_c, keyplus_c: n > 16 or m > 32; the *_indep predicates: n > 5 or m > 13, where rt4_n5_indep.py's
enumeration is too slow). The records rc-n5m13-f1 and rc-n5m12-f2 must give FAILS for rc_c and rc_indep and holds for
keyplus_c; rcy_indep holds at rc-n5m13-f1 and FAILS at rc-n5m12-f2 (results/k4_rc/suite_rc_pred.log)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def _m(d): return d.get('m') or 1 + max(g for S in d['sets'] for g in S)


def _verdict(d, f, nst, nfail, what, unit='states with def > 0'):
    core = '' if d.get('is_core', True) else ' (not a core: the statement does not apply)'
    if f is None: return None, 'omega <= 0'
    if f == 0: return None, f'f = 0 ({nst} states; Theorem Z)'
    if not nst: return True, f'f = {f}, no {unit}'
    return nfail == 0, f'f = {f}, {nst} {unit}, {what} fails at {nfail}{core}'


def _c(d):
    import dlrc_run as DR
    if len(d['sets']) > 16 or _m(d) > 32: return None
    DR.build()
    doms = [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])]
    return DR.run_blocks(DR.block(d['sets'], _m(d), doms, 0, 0), ['-v', '-s', '-r0', '-o0'])[0]


def rc_c(d):
    """DL_RC: at f >= 1 every min-frozen P with def > 0 has a T1, T2, T3+ or T4 move to a min-frozen P' with a smaller deficit (dlrc.c)"""
    b = _c(d)
    if b is None: return None, 'n > 16 or m > 32'
    if not b['V'] or b['V'][0][-4] == -2: return _verdict(d, None, 0, 0, 'DL_RC')
    L, C = b['L'], b['LC']
    if not L['st0'] + L['st1']: return True, 'no state with def > 0'
    if L['st1'] == 0: return None, f"f = 0 ({L['st0']} states; Theorem Z)"
    return _verdict(d, int(b['S'][0][0][0]), C['st1'], C['rcfail'], 'DL_RC')


def keyplus_c(d):
    """DL on the key graph with T3+ / T4 edges: at f >= 1 every key with def* > 0 has a T3+ or T4 edge from one of its states to a key with a smaller def* (dlrc.c)"""
    b = _c(d)
    if b is None: return None, 'n > 16 or m > 32'
    if not b['V'] or b['V'][0][-4] == -2: return _verdict(d, None, 0, 0, 'key-graph DL (T3+/T4)')
    L, C = b['L'], b['LC']
    if not L['st0'] + L['st1']: return True, 'no state with def > 0'
    if L['st1'] == 0: return None, f"f = 0 ({L['st0']} states; Theorem Z)"
    return _verdict(d, int(b['S'][0][0][0]), C['keyspos'], C['keyfailk'], 'key-graph DL (T3+/T4)', 'keys with def* > 0')


def _indep(d):
    if len(d['sets']) > 5 or _m(d) > 13: return None
    import rcy_indep as RY
    return RY.profile(dict(d, m=_m(d)))


def _iv(d, name, what):
    r = _indep(d)
    if r is None: return None, 'n > 5 or m > 13'
    f, nmf, nst, fails, shapes, bad = r
    if f - (2 * len(d['sets']) - _m(d)) <= 0: return _verdict(d, None, 0, 0, what)       # omega = f - sigma
    return _verdict(d, f, nst, fails[name], what)


def rc_indep(d):
    """DL_RC (T1, T2, T3+, T4) at every def > 0 state (f >= 1), with k4/rt4_n5_indep.py's model and move kinds"""
    return _iv(d, 'RC', 'DL_RC')


def rcy_indep(d):
    """DL_RC with T3+'s helper (at most one) unrestricted, at every def > 0 state (f >= 1), with k4/rcy_indep.py"""
    return _iv(d, 'RCY', 'DL_RC with an unrestricted helper')
