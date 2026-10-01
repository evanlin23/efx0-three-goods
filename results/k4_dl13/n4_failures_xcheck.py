#!/usr/bin/env python3
"""Cross-check of the DL13 failures that k4/dl13_run.py reports in a dump (compute/k4-dl13, n = 4 slice). EVIDENCE.

  python3 results/k4_dl13/n4_failures_xcheck.py DUMP.jsonl.gz...

Takes every dump record with f >= 1 and branch "none" (dl13.c: no R_13 neighbour), groups them by (core, profile), and
re-runs each profile through the three implementations of k4/dl13_check.py (imported, unchanged): dl13.c -s, the model
(k4/dl2_relations.py on k4/suite/model.py) and, for n <= 4, c4x_check.py + dl2_relations_xcheck.rel_B. For each failing
state of each profile it prints whether each implementation has the state, its def and k, and whether R_13 holds;
then whether R_T (DL_T's relation, "RTr" in both dl2_relations.py and dl2_relations_xcheck.py) holds in the model and in
dl2_relations_xcheck.states_B, and the nearest better min-frozen states of c4x_check.py with, per changed agent, its base
before -> after and whether it is frozen (singleton base inside the needed set NA) before / after, and NA before / after."""
import gzip, json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import dl13_check as DC
import c4x_check as CX
from dl2_relations_xcheck import states_B

b13, sha13 = DC.build(os.path.join(ROOT, 'k4', 'dl13.c'))
print('# command: python3 results/k4_dl13/n4_failures_xcheck.py ' + ' '.join(sys.argv[1:]))
print(f'# dl13.c sha256 {sha13}')
profs = {}
for f in sys.argv[1:]:
    for l in gzip.open(f, 'rt'):
        r = json.loads(l)
        if r['f'] >= 1 and r['br'] == 'none':
            c = r['core']
            key = (c['file'], c['pos'], json.dumps(r['prof']))
            d = profs.setdefault(key, {'sets': c['sets'], 'm': c['m'], 'vals': r['vals'], 'idx': c.get('idx'), 'B': []})
            d['B'].append(tuple(tuple(B) for B in r['B']))


def nearest(d, Bs):
    """c4x_check.py's better min-frozen states at the nearest distance from Bs, with the changed agents described"""
    sets, vals, m = d['sets'], d['vals'], d['m']
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    res = CX.analyse(sets, m, vl)
    mf = max(r[2]['-frozen'] for r in res)
    mp = {tuple(frozenset(B) for B in r[0]): r[2]['rodef'] for r in res if r[2]['-frozen'] == mf}
    P = tuple(frozenset(B) for B in Bs); dv = mp[P]
    val = lambda i, B: sum(vl[i].get(g, 0) for g in B)
    nd = lambda i, B: frozenset(g for g in vl[i] if g not in B and vl[i][g] > val(i, B))
    NA = lambda Q: frozenset().union(*[nd(i, Q[i]) for i in range(len(Q))])
    fz = lambda Q, i: len(Q[i]) == 1 and Q[i] <= NA(Q)
    better = [(sum(a != b for a, b in zip(P, P2)), P2, d2) for P2, d2 in mp.items() if d2 < dv]
    k = min(b[0] for b in better)
    out = []
    for _, P2, d2 in sorted((b for b in better if b[0] == k), key=lambda b: [sorted(B) for B in b[1]]):
        ch = [f"agent {i}: {sorted(P[i])} -> {sorted(P2[i])} (frozen {int(fz(P, i))} -> {int(fz(P2, i))})"
              for i in range(len(P)) if P[i] != P2[i]]
        out.append(f"    nearest better (k {k}, def {d2}): {[sorted(B) for B in P2]}; " + '; '.join(ch)
                   + f"; NA {sorted(NA(P))} -> {sorted(NA(P2))}")
    return out


agree = disagree = rt_fail = 0
for (fn, pos, pr), d in sorted(profs.items()):
    C = DC.c_states(subprocess.run([b13, '-s'], input=DC.block(d, 0), capture_output=True, text=True, check=True).stdout,
                    [d['sets']])[0][2]
    M = DC.model_states(d)
    X = DC.x_states(d) if len(d['sets']) <= 4 else {}
    XB = states_B(d['sets'], d['vals'], d['m']) if len(d['sets']) <= 4 else {}
    MR = {tuple(tuple(B) for B in r['Bs']): r for r in DC.DR.profile(d)}
    print(f"{fn} pos {pos} idx {d['idx']} m {d['m']} sets {d['sets']} prof {pr} vals {d['vals']}: "
          f"def > 0 states: dl13.c {len(C)}, model {len(M)}, xcheck {len(X) if len(d['sets']) <= 4 else '-'}")
    for Bs in d['B']:
        c, m, x = C.get(Bs), M.get(Bs), X.get(Bs)
        cr = None if c is None else bool(c['t1'] or c['t3p'] or c['t3h'])
        line = (f"  B {list(map(list, Bs))}: dl13.c f {c and c['f']} def {c and c['def']} k {c and c['k']} R13 {cr}; "
                f"model f {m and m['f']} def {m and m['def']} k {m and m['k']} R13 {m and m['R13']}; "
                f"xcheck def {x and x['def']} k {x and x['k']} R13 {x and x['R13']}")
        ok = c is not None and m is not None and cr is False and m['R13'] is False and m['f'] >= 1 and \
            (len(d['sets']) > 4 or (x is not None and x['R13'] is False))
        agree += ok; disagree += not ok
        print(line + ('  -> all agree: DL13 fails' if ok else '  -> DISAGREEMENT'))
        rt_m = MR[Bs]['holds']['RTr'] if Bs in MR else None
        rt_x = XB[Bs][2]['RTr'] if Bs in XB else None
        rt_fail += rt_m is False and rt_x is False
        print(f"    R_T (DL_T): model {rt_m}, xcheck {rt_x}")
        if len(d['sets']) <= 4: print('\n'.join(nearest(d, Bs)))
print(f'failing states: {agree} confirmed by every implementation, {disagree} not; profiles {len(profs)}; '
      f'R_T fails (model and xcheck) at {rt_fail} of them')
