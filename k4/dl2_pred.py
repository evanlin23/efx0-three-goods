"""Conjecture DL2 (k4/strategy.md §3; ledger K4.STRAT.DL2) as predicates for the suite runner (compute/k4-dl2).

  python3 k4/suite/run.py --pred=k4/dl2_pred.py:dl2_c        k* from k4/dl2.c
  python3 k4/suite/run.py --pred=k4/dl2_pred.py:dl2_suite    k* from k4/suite/deficit_local.py (model.py's deficit)

A predicate returns True if k* <= 2 (DL2 holds on the instance), False if k* >= 3, None if omega <= 0 (DL2 says
nothing) or the instance is too large (n > 9 for dl2_c, n > 6 for dl2_suite). DL2 is stated for connected cores; the
detail says when the instance is not one."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'suite'))


def _verdict(d, k):
    core = '' if d.get('is_core', True) else ' (not a core: DL2 does not apply)'
    if k is None: return None, 'omega <= 0'
    return k <= 2, f'k* = {k}{core}'


def dl2_c(d):
    """DL2: every min-frozen P with def > 0 has a min-frozen P' with smaller deficit within two base changes (k* <= 2)"""
    import dl2_run as DR
    if len(d['sets']) > 9: return None, 'n > 9'
    DR.build()
    m = d.get('m') or 1 + max(g for S in d['sets'] for g in S)
    doms = [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])]
    b = DR.run_blocks(DR.block(d['sets'], m, doms, 0, 0), ['-v'])[0]
    k = b['V'][0][len(d['sets']) + 1]
    return _verdict(d, None if k == -2 else (float('inf') if k == -1 else k))


def dl2_suite(d):
    """DL2 (k* <= 2), with k4/suite/deficit_local.py"""
    import deficit_local as DL
    if len(d['sets']) > 6: return None, 'n > 6'
    k, det = DL.kstar({'sets': d['sets'], 'vals': d['vals'], 'm': d.get('m')})
    return _verdict(d, k)
