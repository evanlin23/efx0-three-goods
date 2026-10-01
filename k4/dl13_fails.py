#!/usr/bin/env python3
"""The DL13 failures found by k4/dl13.c, re-derived and classified with k4/dl2_relations.py on k4/suite/model.py
(compute/k4-dl13; ledger K4.DL2.T13). EVIDENCE tooling.

usage: python3 k4/dl13_fails.py DUMP.jsonl.gz ... [--every=E] [--out=FILE.jsonl.gz]
Reads the "D" records of dl13_run.py / dl13_nbhd.py / dl13_hunt.py dumps with f >= 1 and branch "none" (DL13 fails at
the state; every such state is dumped), and for each distinct profile (every E-th) recomputes every def > 0 state with
dl2_relations.profile (model.py). Checks that the C tool's failing states are exactly model.py's f >= 1 states where
R13 fails (a mismatch is printed), and for each failing state records the moves available among all min-frozen P' with
a smaller deficit (dl2_relations.shape): the nearest distance k, rotations (only free agents change, the needed set
kept; by the number of agents), role swaps with a needer (by the number of helpers and whether every helper gives up
a good of its base), need transfers (an agent with an unchanged base changes its frozen status) and moves that change
the key otherwise (key(U.Z.W.Y.): U agents unfreeze, Z freeze, W stay frozen with another good, Y free agents change;
"chain": the frozen goods move along a chain ending at a free agent). Then tests candidate enlargements of R_13 (every move must also lower the
deficit):
  RTr       R_T of k4/dl2.md: (T1), (T2) rotations of any number of free agents, (T3);
  R13+tr    R_13 plus trades (rotations of two free agents);
  R13+rot3  R_13 plus rotations of at most three free agents;
  R13+h2    (T1) plus role swaps with a needer and at most two helpers, each giving up a good;
  R13+hA    (T1) plus role swaps with a needer and any number of helpers, each giving up a good;
  R134      R_13 plus T4: the changed agents are all frozen in P and P' and NA(P') = NA(P) (frozen agents permute their
            goods), computed from model.py's pre-allocations; RT4 = RTr plus T4; R134s2, RT4s2: T4 by two agents only.
Prints the counts (states, profiles) and, per candidate, how many failing states it repairs."""
import collections, gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dl2_relations as DR
from dl2_classify import PA, M, INF


def t4_moves(it):
    """model.py's T4 at the failing states of a profile: {bases: least |ch| of an improving T4 move (0: none)}, where
    T4 = the changed agents are all frozen in P and in P' and NA(P') = NA(P) (frozen agents permute their goods)"""
    I = M.Inst(it['sets'], it['vals'], it['m']); I.preallocs()
    mp = [Bs for Bs, NA in I.minP]
    D = {}
    for Bs in mp:
        x = I.deficit(Bs); D[Bs] = INF if x is None else x
    PAs = {Bs: PA(I, Bs) for Bs in mp}
    NAof = lambda P: __import__('functools').reduce(lambda a, b: a | b, P.N, 0)
    out = {}
    for Bs in mp:
        key = tuple(tuple(M.bits(B)) for B in Bs)
        if key not in it['fails']: continue
        P = PAs[Bs]; best = 0
        for B2 in mp:
            if D[B2] >= D[Bs]: continue
            P2 = PAs[B2]
            ch = [i for i in range(I.n) if Bs[i] != B2[i]]
            if ch and all(P.frozen[i] and P2.frozen[i] for i in ch) and NAof(P) == NAof(P2):
                best = len(ch) if best == 0 else min(best, len(ch))
        out[key] = best
    return out


def rot(s, kmax=None):
    return (s['U'] == 0 and s['Z'] == 0 and s['W'] == 0 and not s['nt'] and len(s['Y']) == s['k'] and s['k'] >= 2
            and (kmax is None or s['k'] <= kmax))


def swaph(s, hmax=None):
    return DR._swap(s, hmax, gives=True)


CANDS = collections.OrderedDict([
    ('R13', lambda s: DR._one(s, nt_ok=False) or swaph(s, 1)),
    ('RTr', lambda s: DR._one(s, nt_ok=False) or rot(s) or swaph(s, 1)),
    ('R13+tr', lambda s: DR._one(s, nt_ok=False) or rot(s, 2) or swaph(s, 1)),
    ('R13+rot3', lambda s: DR._one(s, nt_ok=False) or rot(s, 3) or swaph(s, 1)),
    ('R13+h2', lambda s: DR._one(s, nt_ok=False) or swaph(s, 2)),
    ('R13+hA', lambda s: DR._one(s, nt_ok=False) or swaph(s, None)),
])


def kind(s):
    if DR._one(s, nt_ok=False): return 'T1'
    if rot(s): return f"rot{s['k']}"
    if DR._swap(s, None): return f"swap+{len(s['Y'])}h" + ('' if s['gives'] else '(keep)')
    if s['nt']: return f"need-transfer(k{s['k']})"
    # frozen goods move between agents (the key changes): U unfrozen, Z newly frozen, W frozen in both, Y free in both
    return f"key(U{s['U']}Z{s['Z']}W{s['W']}Y{len(s['Y'])})" + ('chain' if s['chain'] else '')


def main(argv):
    files = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    print('# command: python3 k4/dl13_fails.py ' + ' '.join(argv), flush=True)
    profs = collections.OrderedDict()
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            if r.get('best') or r.get('br') != 'none' or r.get('f', 0) < 1: continue
            key = json.dumps([r['core']['sets'], r['vals']])
            profs.setdefault(key, {'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m'], 'src': fn,
                                   'core': r['core'], 'prof': r.get('prof'), 'fails': set()})
            profs[key]['fails'].add(tuple(tuple(b) for b in r['B']))
    items = list(profs.values())[::int(opt.get('every', 1))]
    print(f'# {sum(len(p["fails"]) for p in profs.values())} failing states dumped in {len(profs)} profiles; '
          f'recomputing {len(items)} profiles', flush=True)
    fo = gzip.open(opt['out'], 'wt') if 'out' in opt else None
    nst = mism = 0; K = collections.Counter(); kinds = collections.Counter(); nearest = collections.Counter()
    cand = collections.Counter(); sig = collections.Counter(); minsz = None
    for it in items:
        recs = DR.profile({'sets': it['sets'], 'vals': it['vals'], 'm': it['m']})
        t4 = t4_moves(it)
        mf = {tuple(tuple(b) for b in r['Bs']) for r in recs if r['f'] >= 1 and not r['holds']['R13']}
        if mf != it['fails']:
            mism += 1; print('MISMATCH', it['core'].get('pos', it['core'].get('id')), it['prof'], sorted(mf ^ it['fails'])[:3], flush=True)
        for r in recs:
            key = tuple(tuple(b) for b in r['Bs'])
            if key not in mf: continue
            nst += 1; K[r['k']] += 1
            ks = sorted({kind(s) for s in r['shapes']})
            kinds[tuple(ks)] += 1
            nearest[tuple(sorted({kind(s) for s in r['shapes'] if s['k'] == r['k']}))] += 1
            ok = {c: any(p(s) for s in r['shapes']) for c, p in CANDS.items()}
            ok['R134'] = ok['R13'] or bool(t4.get(key)); ok['RT4'] = ok['RTr'] or bool(t4.get(key))
            ok['R134s2'] = ok['R13'] or t4.get(key) == 2; ok['RT4s2'] = ok['RTr'] or t4.get(key) == 2
            for c, v in ok.items(): cand[(c, v)] += 1
            if fo:
                fo.write(json.dumps({'core': it['core'], 'prof': it['prof'], 'vals': it['vals'], 'B': r['Bs'], 'def': r['def'],
                                     'k': r['k'], 'f': r['f'], 'omega': r['omega'], 'kinds': ks, 'cands': ok,
                                     'shapes': r['shapes']}, separators=(',', ':')) + '\n')
    if fo: fo.close()
    print(f'profiles recomputed {len(items)}, failing states {nst}, mismatches with the dump {mism}', flush=True)
    print('nearest distance k of the failing states: ' + str(dict(sorted(K.items(), key=lambda x: (x[0] is None, x[0] or 0)))))
    print('move kinds available (any distance), states:')
    for k, c in kinds.most_common(): print(f'  {list(k)}: {c}')
    print('move kinds at the nearest distance, states:')
    for k, c in nearest.most_common(): print(f'  {list(k)}: {c}')
    print('candidate enlargements of R_13: failing states they repair / do not repair')
    for c in list(CANDS) + ['R134', 'R134s2', 'RT4', 'RT4s2']:
        print(f'  {c:<9} repairs {cand[(c, True)]}, does not repair {cand[(c, False)]}')


if __name__ == '__main__':
    main(sys.argv[1:])
