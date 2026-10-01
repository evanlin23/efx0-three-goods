"""Rule RK (k4/rulef.md §4) as predicates of the counterexample suite (k4/suite/run.py --pred=...).

  python3 k4/suite/run.py --pred=k4/rulef_suite.py:rule_rk      LB4r with rule RK's first agent and at most one rotation
                                                               succeeds (k4/rulef.c -A41 -r1, raw EFX0 check)
  python3 k4/suite/run.py --pred=k4/rulef_suite.py:lemma_m      some first agent is in class K0, K1 or C40 (Lemma M)
  python3 k4/suite/run.py --pred=k4/rulef_suite.py:lemma_k0     some first agent is in class K0 (no rotation needed)
Each returns (verdict, detail); detail gives RK's class (K0, K1, C40, open) and the rotations LB4r needed."""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'suite'))
sys.path.insert(0, HERE)
import model as SM
import rulef_run as RR
import adaptive_run as AR

CLASSES = ['K0', 'K1', 'C40', 'open']


def _run(d):
    I = SM.Inst(d['sets'], d['vals'], d.get('m'))
    if I.core_violations(): return None
    if len(d['sets']) > 40 or (d.get('m') or 1 + max(g for S in d['sets'] for g in S)) > 128: return None
    RR.build()
    p = subprocess.run([RR.BIN, '-A41', '-r1', '-T1'], input=AR.encode_profile(d['sets'], d['vals']),
                       capture_output=True, text=True)
    if p.returncode: return ('error', p.stdout[-300:] + p.stderr[-300:])
    rk = next((l for l in p.stdout.split('\n') if l.startswith('RK41')), None)
    single = next((l for l in p.stdout.split('\n') if l.startswith('single ')), '')
    t = rk.split()
    cls = None
    for c in range(4):
        i = t.index('c%d' % c)
        vals = list(map(int, t[i + 1:i + 4]))
        if sum(vals):
            cls = c; rot = vals.index(1)
    viol = int(t[t.index('viol') + 1])
    return cls, rot, viol, single


def rule_rk(d):
    """LB4r with rule RK's first agent (k4/rulef.md §4) and at most one rotation succeeds"""
    r = _run(d)
    if r is None: return None, 'not a k = 4 core, or too large for k4/rulef.c'
    if r[0] == 'error': return None, 'ERROR ' + r[1]
    cls, rot, viol, _ = r
    return rot <= 1 and not viol, 'class %s, rotations %s' % (CLASSES[cls], rot if rot <= 1 else 'fail')


def lemma_m(d):
    """Lemma M: some first agent is in class K0, K1 or C40 (k4/rulef.md §4)"""
    r = _run(d)
    if r is None: return None, 'not a k = 4 core, or too large for k4/rulef.c'
    if r[0] == 'error': return None, 'ERROR ' + r[1]
    return r[0] < 3, 'class %s' % CLASSES[r[0]]


def lemma_k0(d):
    """some first agent is in class K0: Lemma K certifies an owner without rotation (k4/rulef.md §2)"""
    r = _run(d)
    if r is None: return None, 'not a k = 4 core, or too large for k4/rulef.c'
    if r[0] == 'error': return None, 'ERROR ' + r[1]
    return r[0] == 0, 'class %s' % CLASSES[r[0]]
