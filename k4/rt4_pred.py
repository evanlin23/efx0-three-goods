"""DL_RT4 (ledger K4.DL2.RT4), DL on the key graph (K4.DL13.KEY) and DL_RC (K4.DL2.RC) as predicates for the suite
runner (compute/k4-rt4-n5).

  python3 k4/suite/run.py --pred=k4/rt4_pred.py:rt4_c        DL_RT4 with k4/dlrt4.c (through k4/dlrt4_run.py)
  python3 k4/suite/run.py --pred=k4/rt4_pred.py:rt4_ref      DL_RT4 with k4/dlrt4_ref.py (k4/suite/model.py)
  python3 k4/suite/run.py --pred=k4/rt4_pred.py:rt4_x        DL_RT4 with k4/rt4_n5_xcheck.py (main's k4/c4x_check.py)
  python3 k4/suite/run.py --pred=k4/rt4_pred.py:key_x        DL on the key graph, single T3 / T4 edges (same tool)
  python3 k4/suite/run.py --pred=k4/rt4_pred.py:key_ref      the same with k4/dlrt4_ref.py's T3 / T4 tests (model.py)
  python3 k4/suite/run.py --pred=k4/rt4_pred.py:rc_x         DL_RC, R_C = T1 + T2 + T3+ + T4 (same tool as rt4_x)
  python3 k4/suite/run.py --pred=k4/rt4_pred.py:keyplus_x    DL on the key graph, T3+ / T4 edges (same tool)

Each returns True if the statement holds at every state of the instance (every min-frozen P with def(P) > 0, or every
key with def* > 0), False if it fails somewhere, and None when it says nothing: omega <= 0, or fewest frozen agents
f = 0 (Theorem Z answers the question there), or the instance is too large (rt4_c: n > 16 or m > 32; rt4_ref,
key_ref: n > 6; the *_x predicates: n > 5 or m > 12, where c4x_check's enumeration is too slow). The statements are
about connected cores; the detail says when the instance is not one. The records rt4-n5m9-chain and rt4-n5m10-chain
must give FAILS for rt4_*, key_x, key_ref and holds for rc_x, keyplus_x."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'suite'))


def _m(d): return d.get('m') or 1 + max(g for S in d['sets'] for g in S)


def _verdict(d, f, nst, nfail, what='DL_RT4', unit='states with def > 0'):
    core = '' if d.get('is_core', True) else ' (not a core: the statement does not apply)'
    if f is None: return None, 'omega <= 0'
    if f == 0: return None, f'f = 0 ({nst} states; Theorem Z)'
    if not nst: return True, f'f = {f}, no {unit}'
    return nfail == 0, f'f = {f}, {nst} {unit}, {what} fails at {nfail}{core}'


def rt4_c(d):
    """DL_RT4: at f >= 1 every min-frozen P with def > 0 has a T1, T2, T3 or T4 move to a min-frozen P' with a smaller deficit (dlrt4.c)"""
    import dlrt4_run as DR
    if len(d['sets']) > 16 or _m(d) > 32: return None, 'n > 16 or m > 32'
    DR.build()
    doms = [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])]
    b = DR.run_blocks(DR.block(d['sets'], _m(d), doms, 0, 0), ['-v', '-s', '-r0', '-o0'])[0]
    if not b['V'] or b['V'][0][-4] == -2: return _verdict(d, None, 0, 0)
    L = b['L']
    if not L['st0'] + L['st1']: return True, 'no state with def > 0'     # dlrt4.c gives f only on its state lines
    if L['st1'] == 0: return _verdict(d, 0, L['st0'], L['fail0'])
    return _verdict(d, int(b['S'][0][0][0]), L['st1'], L['fail1'])


def rt4_ref(d):
    """DL_RT4 at every def > 0 state (f >= 1), with k4/dlrt4_ref.py on k4/suite/model.py"""
    import dlrt4_ref as R
    import model as M
    if len(d['sets']) > 6: return None, 'n > 6'
    I = M.Inst(d['sets'], d['vals'], _m(d)); I.preallocs()
    if I.omega <= 0: return _verdict(d, None, 0, 0)
    st = R.ref_states(dict(d, m=_m(d)))
    fails = sum(1 for s in st.values() if not (s['t1'] or s['t2'] or s['t3p'] or s['t3h'] or s['t4']))
    return _verdict(d, I.f, len(st), fails)


def _x(d):
    import rt4_n5_xcheck as XC
    if len(d['sets']) > 5 or _m(d) > 12: return None
    return XC.analyse(dict(d, m=_m(d)))


def _xv(d, field, what, unit):
    r = _x(d)
    if r is None: return None, 'n > 5 or m > 12'
    if 'skip' in r: return _verdict(d, None if r['omega'] <= 0 else r['f'], 0, 0)
    if unit == 'keys with def* > 0': return _verdict(d, r['f'], r['keys_pos'], len(r['kfail'][field]), what, unit)
    return _verdict(d, r['f'], r['states'], len(r['fails']) if field == 'rt4' else r['rc_fail'], what, unit)


def rt4_x(d):
    """DL_RT4 at every def > 0 state (f >= 1), with k4/rt4_n5_xcheck.py on main's k4/c4x_check.py"""
    return _xv(d, 'rt4', 'DL_RT4', 'states with def > 0')


def rc_x(d):
    """DL_RC (R_C = T1 + T2 + T3+ + T4) at every def > 0 state (f >= 1), with k4/rt4_n5_xcheck.py"""
    return _xv(d, 'rc', 'DL_RC', 'states with def > 0')


def key_x(d):
    """DL on the key graph with single T3 / T4 edges (k4/dl13.md §2.3 Remark), with k4/rt4_n5_xcheck.py"""
    return _xv(d, 'T3/T4', 'key-graph DL (T3/T4)', 'keys with def* > 0')


def keyplus_x(d):
    """DL on the key graph with T3+ / T4 edges, with k4/rt4_n5_xcheck.py"""
    return _xv(d, 'T3+/T4', 'key-graph DL (T3+/T4)', 'keys with def* > 0')


def key_ref(d):
    """DL on the key graph with single T3 / T4 edges, with k4/dlrt4_ref.py's T3 and T4 tests on k4/suite/model.py"""
    import dlrt4_ref as R, dl2_relations as DR
    from dl2_classify import PA
    import model as M
    if len(d['sets']) > 6: return None, 'n > 6'
    I = M.Inst(d['sets'], d['vals'], _m(d)); I.preallocs()
    if I.omega <= 0: return _verdict(d, None, 0, 0)
    mp = [Bs for Bs, NA in I.minP]
    P = {Bs: PA(I, Bs) for Bs in mp}
    D = {}
    for Bs in mp:
        x = I.deficit(Bs); D[Bs] = R.CINF if x is None else x
    key = lambda Bs: (P[Bs].NA, tuple(Bs[i] if P[Bs].frozen[i] else None for i in range(I.n)))
    K = {}
    for Bs in mp: K.setdefault(key(Bs), []).append(Bs)
    dstar = {k: min(D[Bs] for Bs in v) for k, v in K.items()}
    pos = [k for k in K if dstar[k] > 0]
    fails = 0
    for k in pos:
        ok = False
        for Bs in K[k]:
            for B2 in mp:
                k2 = key(B2)
                if k2 == k or dstar[k2] >= dstar[k]: continue
                ch = [i for i in range(I.n) if Bs[i] != B2[i]]
                if DR._swap(DR.shape(P[Bs], P[B2]), 1, gives=True) or R.t4_move(P[Bs], P[B2], ch)[0]: ok = True; break
            if ok: break
        fails += not ok
    return _verdict(d, I.f, len(pos), fails, 'key-graph DL (T3/T4)', 'keys with def* > 0')
