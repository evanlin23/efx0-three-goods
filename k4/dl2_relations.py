#!/usr/bin/env python3
"""DL_R for structured neighbourhood relations R (workstream proof/k4-dl2-k1; k4/dl2.md §4).

DL_R: every min-frozen P in 𝒫 (k4/c4x.md §1) with def(P) > 0 has a min-frozen R-neighbour P' with def(P') < def(P)
(def = +infinity when no free owner has a safe bundle). By PR #68 (`EFX.C4min.target4_of_defLocal`), DL_R for any
relation R implies TARGET4. This script enumerates, for every such P, every min-frozen P' with a smaller deficit,
describes the move P -> P' by its *shape* (below), and evaluates the relations of RELATIONS on the shapes.

Shape of a move P -> P' (both min-frozen), ch = the agents whose base changes:
  U = changed agents frozen in P, free in P' (unfrozen);  Z = changed agents free in P, frozen in P' (newly frozen);
  W = changed agents frozen in both;  Y = changed agents free in both;  nt = an agent with an unchanged base changes
  its frozen status (a need transfer).
  swap = (|U| = |Z| = 1, W empty, z takes x's good: B'_z = B_x); needer = z needs that good in P.
  For y in Y: 'rel' (B'_y ⊊ B_y, a pure release; 'rel1' if exactly one good is dropped), 'junk' (B'_y ⊆ B_y ∪ J, not a
  release), 'trade' (y takes a good of another changed agent's base).
  xsrc: the unfrozen agent's new base lies in J ('J'), in J ∪ B_z ('JZ'), or elsewhere ('other').
  chain: the frozen goods move along a chain: |U| = |Z| = 1 and every agent of W ∪ Z takes the good of an agent of
  U ∪ W (a rotation of frozen goods ending at a free agent, as in LB+'s rotation).

usage: python3 k4/dl2_relations.py suite | catalog FILE [--every=E] [--max=N] [--jobs=J] [--out=FILE.jsonl.gz]
(--out keeps the states where some relation fails, with the shapes of all their improving moves.)
Prints, per relation, the number of states (and profiles) where it fails, with the first failing examples."""
import collections, gzip, itertools, json, os, sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dl2_classify as DC
from dl2_classify import PA, M, bits, pc, mask, INF


def shape(P, P2):
    n = P.I.n
    ch = [i for i in range(n) if P.Bs[i] != P2.Bs[i]]
    U = [i for i in ch if P.frozen[i] and not P2.frozen[i]]
    Z = [i for i in ch if not P.frozen[i] and P2.frozen[i]]
    W = [i for i in ch if P.frozen[i] and P2.frozen[i]]
    Y = [i for i in ch if not P.frozen[i] and not P2.frozen[i]]
    nt = any(P.frozen[i] != P2.frozen[i] for i in range(n) if i not in ch)
    yk = []
    for y in Y:
        B, B2 = P.Bs[y], P2.Bs[y]
        if not (B2 & ~B) and B2 != B:
            yk.append('rel1' if pc(B & ~B2) == 1 else 'rel')
        elif not (B2 & ~(B | P.J)):
            yk.append('junk')
        else:
            yk.append('trade')
    gives = all(P.Bs[y] & ~P2.Bs[y] for y in Y)          # every agent of Y gives up a good of its base
    swap = needer = False; xsrc = None; chain = False; yz = False
    if len(U) == 1 and len(Z) == 1:
        x, z = U[0], Z[0]
        if not W and P2.Bs[z] == P.Bs[x]:
            swap = True
            needer = bool(P.N[z] & P.Bs[x])
        B2x = P2.Bs[x]
        xsrc = 'J' if not (B2x & ~P.J) else ('JZ' if not (B2x & ~(P.J | P.Bs[z])) else 'other')
        yz = all(not (P2.Bs[y] & ~(P.Bs[y] | P.Bs[z])) for y in Y)   # the agents of Y take only goods of B_z
        # chain: every agent of W ∪ Z holds in P' the (single) good of an agent of U ∪ W
        src = {P.Bs[i]: i for i in U + W}
        chain = all(P2.Bs[i] in src for i in W + Z)
    exch = False
    if len(ch) == 2 and len(Y) == 2:
        a, b = Y
        exch = bool(P2.Bs[a] & P.Bs[b]) or bool(P2.Bs[b] & P.Bs[a])  # a good passes between the two agents
    return {'k': len(ch), 'U': len(U), 'Z': len(Z), 'W': len(W), 'Y': tuple(sorted(yk)), 'nt': nt,
            'swap': swap, 'needer': needer, 'xsrc': xsrc, 'chain': chain, 'gives': gives, 'yz': yz, 'exch': exch}


def _ys(s, allowed, at_most=None):
    return all(k in allowed for k in s['Y']) and (at_most is None or len(s['Y']) <= at_most)


def _one(s, nt_ok=True):           # one agent re-bases
    return s['k'] == 1 and (nt_ok or not s['nt'])


def _trade(s, exch=False):         # two free agents re-base, the needed set unchanged
    return s['k'] == 2 and len(s['Y']) == 2 and not s['nt'] and (s['exch'] or not exch)


def _swap(s, ymax=0, kinds=None, gives=False, yz=False):    # a role swap with a needer, plus agents of Y
    return (s['swap'] and s['needer'] and not s['nt'] and (ymax is None or len(s['Y']) <= ymax)
            and (kinds is None or _ys(s, kinds)) and (s['gives'] or not gives) and (s['yz'] or not yz))


# the relations: name -> (description, predicate on a shape)
RELATIONS = collections.OrderedDict([
    ('R2', ('at most two agents change (DL2, refuted)', lambda s: s['k'] <= 2)),
    ('R3', ('at most three agents change', lambda s: s['k'] <= 3)),
    ('RB', ('one re-base or a plain role swap with a needer', lambda s: _one(s) or _swap(s))),
    ('RB2', ('RB, or a trade (two free agents re-base, needed set unchanged)',
             lambda s: _one(s) or _swap(s) or _trade(s))),
    ('RS1', ('one re-base; or a role swap with a needer plus single-good releases by any number of free agents',
             lambda s: _one(s) or _swap(s, None, ('rel1',)))),
    ('RS1+2', ('RS1, or a trade', lambda s: _one(s) or _trade(s) or _swap(s, None, ('rel1',)))),
    ('RSR+2', ('one re-base; a trade; or a role swap with a needer plus pure releases (any number, any size)',
               lambda s: _one(s) or _trade(s) or _swap(s, None, ('rel1', 'rel')))),
    ('RC', ('one re-base; a trade; or a chain of frozen goods (|U| = |Z| = 1) plus pure releases',
            lambda s: _one(s) or _trade(s) or (s['chain'] and not s['nt'] and _ys(s, ('rel1', 'rel'))))),
    ('RSY', ('one re-base; or a role swap with a needer plus at most one free agent re-basing in any way',
             lambda s: _one(s) or _swap(s, 1))),
    ('RSYa', ('one re-base; or a role swap with a needer plus any number of free agents re-basing in any way',
              lambda s: _one(s) or _swap(s, None))),
    ('RSY+2', ('one re-base; a trade; or a role swap with a needer plus at most one free agent re-basing in any way',
               lambda s: _one(s) or _trade(s) or _swap(s, 1))),
    ('RSYg+2', ('RSY+2, the extra agent giving up at least one good of its base',
                lambda s: _one(s) or _trade(s) or _swap(s, 1, gives=True))),
    ('RSYz+2', ("RSY+2, the extra agent taking goods only from its own base and the needer's old base",
                lambda s: _one(s) or _trade(s) or _swap(s, 1, yz=True))),
    ('RSYgz+2', ('RSY+2 with both restrictions on the extra agent',
                 lambda s: _one(s) or _trade(s) or _swap(s, 1, gives=True, yz=True))),
    ('RSYg', ('RSYg+2 without trades', lambda s: _one(s) or _swap(s, 1, gives=True))),
    ('RT', ('R_T of k4/dl2.md: re-bases that keep the needed set, trades in which a good passes between the two '
            'agents, role swaps with a needer and at most one helper that gives up a good',
            lambda s: _one(s, nt_ok=False) or _trade(s, exch=True) or _swap(s, 1, gives=True))),
    ('RTr', ('R_T with rotations: any number of free agents re-basing with the needed set unchanged, in place of trades '
             '(only in the runs on whole certificate files)',
             lambda s: _one(s, nt_ok=False) or (s['k'] >= 2 and len(s['Y']) == s['k'] and not s['nt'])
             or _swap(s, 1, gives=True))),
])


def profile(d):
    """per def > 0 state: (bases, def, nearest distance, {relation: holds}, the shapes of the improving moves)"""
    I = M.Inst(d['sets'], d['vals'], d.get('m'))
    I.preallocs()
    if I.omega <= 0: return []
    mp = [Bs for Bs, NA in I.minP]
    PAs = {Bs: PA(I, Bs) for Bs in mp}
    D = {}
    for Bs in mp:
        x = I.deficit(Bs); D[Bs] = INF if x is None else x
    out = []
    for Bs in mp:
        if D[Bs] <= 0: continue
        P = PAs[Bs]
        shapes = []; kmin = None
        for B2 in mp:
            if D[B2] >= D[Bs]: continue
            s = shape(P, PAs[B2]); shapes.append(s)
            kmin = s['k'] if kmin is None else min(kmin, s['k'])
        holds = {r: any(pred(s) for s in shapes) for r, (_, pred) in RELATIONS.items()}
        uniq = sorted(set(json.dumps(s, sort_keys=True) for s in shapes))
        out.append({'Bs': [sorted(bits(B)) for B in Bs], 'def': D[Bs], 'k': kmin, 'holds': holds,
                    'f': I.f, 'omega': I.omega, 'shapes': [json.loads(u) for u in uniq]})
    return out


def one(args):
    d, src = args
    return src, d, profile(d)


def items_of(mode, rest, opt):
    items = []
    if mode == 'suite':
        import glob
        for f in sorted(glob.glob(os.path.join(HERE, 'suite', 'instances', '*.json'))):
            d = json.load(open(f))
            if 'kind' in d or len(d['sets']) > int(opt.get('nmax', 6)): continue
            if not d.get('is_core', True): continue         # DL_R is about cores; non-core instances are skipped
            d.setdefault('m', 1 + max(g for S in d['sets'] for g in S))
            items.append(({'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}, d['id']))
    elif mode == 'certs':                                    # every strict profile (or --rand=K per core) of a certs file
        import random
        from check4 import core_domains
        data = json.load(gzip.open(rest[0], 'rt'))
        rng = random.Random(int(opt.get('seed', 1)))
        base = os.path.basename(rest[0]).replace('.json.gz', '')
        for core in data['cores']:
            sets, m = core['sets'], core['m']
            doms = core_domains(sets, m, False)
            if 'rand' in opt:
                profs = [tuple(rng.randrange(len(D)) for D in doms) for _ in range(int(opt['rand']))]
            else:
                profs = itertools.product(*[range(len(D)) for D in doms])
            for ts in profs:
                vals = [[doms[i][ts[i]][g] for g in sets[i]] for i in range(len(sets))]
                items.append(({'sets': sets, 'vals': vals, 'm': m},
                              '%s#%d:%s' % (base, core['idx'], ','.join(map(str, ts)))))
    else:
        recs = json.load(gzip.open(rest[0], 'rt'))['records'][::int(opt.get('every', 1))]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        base = os.path.basename(rest[0]).replace('.json.gz', '')
        for r in recs:
            c = r['core']
            items.append(({'sets': c['sets'], 'vals': r['vals'], 'm': c['m']},
                          '%s:%s#%d:%s' % (base, c['file'], c['idx'], ','.join(map(str, r['prof'])))))
    return items


def main(argv):
    if not argv: print(__doc__); return
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--') and '=' in a)
    jobs = int(opt.get('jobs', 1)); out = opt.get('out')
    items = items_of(mode, rest, opt)
    print('# command: python3 k4/dl2_relations.py ' + ' '.join(argv), flush=True)
    fo = gzip.open(out, 'wt') if out else None
    fail = {r: [] for r in RELATIONS}; failprof = {r: set() for r in RELATIONS}; nfail = collections.Counter()
    nst = 0; nprof = 0; kh = collections.Counter()
    it = map(one, items) if jobs <= 1 else Pool(jobs).imap(one, items, chunksize=4)
    for src, d, recs in it:
        nprof += 1
        for r in recs:
            nst += 1; kh[r['k']] += 1
            for rel, h in r['holds'].items():
                if not h:
                    failprof[rel].add(src); nfail[rel] += 1
                    if len(fail[rel]) < 200: fail[rel].append((len(d['sets']), d['m'], src, d, r))
            if fo and not all(r['holds'].values()):      # only the states where some relation fails
                r2 = dict(r); r2['src'] = src; r2['sets'] = d['sets']; r2['vals'] = d['vals']; r2['m'] = d['m']
                fo.write(json.dumps(r2, separators=(',', ':')) + '\n')
    if fo: fo.close()
    print('profiles %d, def>0 states %d, nearest-distance histogram %s' % (nprof, nst, dict(sorted(kh.items(), key=lambda x: (x[0] is None, x[0] or 0)))))
    for rel, (desc, _) in RELATIONS.items():
        fl = fail[rel]
        print('%-6s fails at %d states of %d profiles  -- %s' % (rel, nfail[rel], len(failprof[rel]), desc))
        for nn, m, src, d, r in sorted(fl, key=lambda t: (t[0], t[1]))[:2]:
            print('       e.g. n=%d m=%d %s sets=%s vals=%s P=%s def=%s k=%s' % (nn, m, src, d['sets'], d['vals'],
                                                                                r['Bs'], r['def'], r['k']))
    sys.stdout.flush()


if __name__ == '__main__':
    main(sys.argv[1:])
