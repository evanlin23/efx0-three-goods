#!/usr/bin/env python3
"""Second implementation of the T3-stage and T3⁺ verdicts of k4/f2.md §1–§2 (workstream proof/k4-f2). EVIDENCE tooling.

Built on main's k4/dl134_xcheck.py (compute/k4-dl13): its own enumeration of 𝒫 through main's k4/c4x_check.py (every
base map, (V1), (V2) literally, its own removal-only deficit), and its own move kinds T1, T2, T3 (plain), T4. It does not
import k4/f2_lib.py, and its 𝒫, deficits and move kinds do not use k4/suite/model.py; model.py is loaded transitively
(dl134_xcheck.py imports dl2_relations_xcheck.py, which imports dl2_relations.py) but not used here. The T3⁺ test below is written here from the coordinator's definition:
  NA' = NA; among the changed agents exactly one is frozen in P and free in P' (x) and exactly one free in P and frozen
  in P' (z), with B'_z ⊆ N_z(B_z); the changed agents frozen in both form W; at most one changed agent is free in both,
  and it gives up a good; the multiset of bases {B'_i : i ∈ W ∪ {z}} equals {B_i : i ∈ W ∪ {x}}.
For every profile of the given k4/f2_shapes.py dumps, every min-frozen P with f >= 2 and def(P) > 0 is classified:
T3 stage (no improving T1, T2, T4 move); then 'plain' (an improving T3 move), 'chain' (only T3⁺ moves with W != ∅),
'fail' (none). The set of T3-stage states and the verdicts are compared with the dumps (the dumps' records hold the
T3-stage states of f2_shapes.py with their T3⁺ repairs: 'plain' iff some repair has k = 0).
usage: python3 k4/f2_xcheck2.py DUMP.jsonl.gz ... [--every=E] [--chunk=K/C]"""
import collections, gzip, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dl134_xcheck as X


def t3plus_own(P, Q, IP, IQ):
    """0: not T3⁺; 1: T3⁺ with W empty; 2: T3⁺ with W nonempty"""
    (N1, NA1, fz1), (N2, NA2, fz2) = IP, IQ
    if NA1 != NA2: return 0
    moved = [i for i in range(len(P)) if P[i] != Q[i]]
    out_ = [i for i in moved if fz1[i] and not fz2[i]]
    in_ = [i for i in moved if fz2[i] and not fz1[i]]
    stay = [i for i in moved if fz1[i] and fz2[i]]
    helpers = [i for i in moved if not fz1[i] and not fz2[i]]
    if len(out_) != 1 or len(in_) != 1 or len(helpers) > 1: return 0
    if helpers and not (P[helpers[0]] - Q[helpers[0]]): return 0
    if not Q[in_[0]] <= N1[in_[0]]: return 0
    before = collections.Counter(P[i] for i in stay + out_)
    after = collections.Counter(Q[i] for i in stay + in_)
    if before != after: return 0
    return 2 if stay else 1


def main(argv):
    files = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    print('# command: python3 k4/f2_xcheck2.py ' + ' '.join(argv), flush=True)
    mine = collections.OrderedDict()
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            key = json.dumps([r['sets'], r['vals'], r['m']])
            v = 'fail' if not r['reps'] else ('plain' if any(rp['k'] == 0 for rp in r['reps']) else 'chain')
            mine.setdefault(key, {})[tuple(frozenset(b) for b in r['Bs'])] = (r['def'], v)
    keys = list(mine)[::int(opt.get('every', 1))]
    if 'chunk' in opt:                      # --chunk=K/C: the K-th of C interleaved slices (bounded runs)
        kk, cc = map(int, opt['chunk'].split('/')); keys = keys[kk::cc]
    cnt = collections.Counter()
    for key in keys:
        sets, vals, m = json.loads(key)
        Pr = X.Prof(sets, vals, m)
        info = {P: Pr.info(P) for P, _ in Pr.mp}
        own = {}
        if Pr.f >= 2:
            for P, d in Pr.mp:
                if d <= 0: continue
                better = [(Q, dq) for Q, dq in Pr.mp if dq < d]
                fl = collections.Counter()
                for Q, dq in better:
                    k, _ = Pr.move(P, Q, info[P], info[Q])
                    for kk in ('t1', 't2', 't4', 't3p', 't3h'): fl[kk] += k[kk]
                    t = t3plus_own(P, Q, info[P], info[Q])
                    assert (t == 1) == bool(k['t3p'] or k['t3h']), ('T3+ at W = {} vs dl134_xcheck T3', P, Q)
                    fl['plain'] += t == 1; fl['chain'] += t == 2
                if fl['t1'] or fl['t2'] or fl['t4']: continue
                own[P] = (d, 'plain' if fl['plain'] else ('chain' if fl['chain'] else 'fail'))
        cnt['profiles'] += 1; cnt['T3-stage states (dl134_xcheck)'] += len(own)
        print('profile %d/%d: n=%d m=%d, %d T3-stage states' % (cnt['profiles'], len(keys), len(sets), m, len(own)),
              flush=True)
        for v in own.values(): cnt['verdict ' + v[1]] += 1
        if own != mine[key]:
            cnt['MISMATCH profiles'] += 1
            print('MISMATCH', key, sorted(set(own.items()) ^ set(mine[key].items()), key=str)[:4], flush=True)
    print('# ' + ', '.join('%s %d' % kv for kv in sorted(cnt.items())))


if __name__ == '__main__':
    main(sys.argv[1:])
