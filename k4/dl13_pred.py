"""Conjecture DL13 (k4/dl2.md §3; ledger K4.DL2.T13) as predicates for the suite runner (compute/k4-dl13).

  python3 k4/suite/run.py --pred=k4/dl13_pred.py:dl13_c       k4/dl13.c
  python3 k4/suite/run.py --pred=k4/dl13_pred.py:dl13_model   k4/dl2_relations.py (relation R13) on k4/suite/model.py
  python3 k4/suite/run.py --pred=k4/dl13_pred.py:dl13_x       main's k4/c4x_check.py with k4/dl2_relations_xcheck.rel_B

A predicate returns True if every min-frozen P with def(P) > 0 has an R_13 move (a re-base keeping the needed set,
or a role swap with a needer and at most one helper giving up a good) to a min-frozen P' with a smaller deficit,
False if some P has none, and None when DL13 says nothing (omega <= 0, or fewest frozen agents f = 0, where Theorem Z
answers the question and R_13 is not meant to hold) or the instance is too large (dl13_c: n > 16 or m > 32;
dl13_model: n > 6; dl13_x: n > 4 or m > 10, where c4x_check's enumeration of completions is too slow). DL13 is stated
for connected cores; the detail says when the instance is not one."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'suite'))


def _m(d): return d.get('m') or 1 + max(g for S in d['sets'] for g in S)


def _verdict(d, f, nst, nfail):
    core = '' if d.get('is_core', True) else ' (not a core: DL13 does not apply)'
    if f is None: return None, 'omega <= 0'
    if f == 0: return None, f'f = 0 ({nst} states; Theorem Z)'
    return nfail == 0, f'f = {f}, {nst} states with def > 0, DL13 fails at {nfail}{core}'


def dl13_c(d):
    """DL13: every min-frozen P with def > 0 (f >= 1) has an R_13 move to a min-frozen P' with a smaller deficit"""
    import subprocess, dl13_run as DR
    if len(d['sets']) > 16 or _m(d) > 32: return None, 'n > 16 or m > 32'
    DR.build()
    doms = [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])]
    out = subprocess.run([DR.BIN, '-s', '-r0', '-o0'], input=DR.block(d['sets'], _m(d), doms, 0, 0), capture_output=True,
                         text=True, check=True).stdout
    S = [l.split() for l in out.splitlines() if l.startswith('S ')]
    V = [l.split() for l in out.splitlines() if l.startswith('V ')]
    if not V or V[0][-4] == '-2': return _verdict(d, None, 0, 0)
    n = len(d['sets'])
    f = int(S[0][1]) if S else -1
    fails = sum(1 for w in S if w[2 + n + 3:2 + n + 6] == ['0', '0', '0'])
    if not S: return True, 'no state with def > 0'
    return _verdict(d, f, len(S), fails)


def dl13_model(d):
    """DL13 (R_13 at every def > 0 state, f >= 1), with k4/dl2_relations.py on model.py"""
    import dl2_relations as DRL
    if len(d['sets']) > 6: return None, 'n > 6'
    recs = DRL.profile({'sets': d['sets'], 'vals': d['vals'], 'm': _m(d)})
    import model as M
    I = M.Inst(d['sets'], d['vals'], _m(d)); I.preallocs()
    if I.omega <= 0: return _verdict(d, None, 0, 0)
    if not recs: return True, 'no state with def > 0'
    return _verdict(d, I.f, len(recs), sum(1 for r in recs if not r['holds']['R13']))


def dl13_x(d):
    """DL13 (R_13 at every def > 0 state, f >= 1), with main's k4/c4x_check.py and dl2_relations_xcheck.rel_B"""
    import c4x_check as CX
    from dl2_relations_xcheck import rel_B
    if len(d['sets']) > 4 or _m(d) > 10: return None, 'n > 4 or m > 10'
    sets, vals, m = d['sets'], d['vals'], _m(d)
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    res = CX.analyse(sets, m, vl)
    if not res: return None, 'no valid P'
    mf = max(r[2]['-frozen'] for r in res)
    f = -mf
    if f - (2 * len(sets) - m) <= 0: return _verdict(d, None, 0, 0)
    mp = [(tuple(frozenset(B) for B in r[0]), r[2]['rodef']) for r in res if r[2]['-frozen'] == mf]
    st = [(P, dv) for P, dv in mp if dv > 0]
    fails = sum(1 for P, dv in st if not any(rel_B('R13', sets, vals, P, Q) for Q, d2 in mp if d2 < dv))
    if not st: return True, 'no state with def > 0'
    return _verdict(d, f, len(st), fails)
