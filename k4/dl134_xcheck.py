#!/usr/bin/env python3
"""Independent membership test for the relation R_134 = T1 + T3 + T4 and its variants (compute/k4-dl13). EVIDENCE tooling.

Built on main's k4/c4x_check.py (its own enumeration of every base map good -> agent or junk, (V1), (V2) literally, and
its own removal-only deficit `rodef`); the move kinds below are written here from the definitions, and the R_13 / R_T
verdicts are cross-checked against k4/dl2_relations_xcheck.rel_B (written separately in proof/k4-dl2-k1). It imports
neither k4/suite/model.py (nor k4/dl2_relations.py, which runs on it) nor the code of compute/k4-dl134.

For a min-frozen P with def(P) > 0 and a min-frozen P' with def(P') < def(P) (tuples of frozensets), with ch the agents
whose base differs, N, N' the needs (goods of R_i outside the base worth more than it), NA, NA' their unions and
"frozen" = a one-good base inside the needed set:
  T1   |ch| = 1 and NA' = NA (k4/dl2.md (T1));
  T2   |ch| >= 2, NA' = NA, no agent of ch frozen in P or in P' (a rotation of free agents, k4/dl2.md (T2));
  T3   a role swap with a needer and at most one helper giving up a good (k4/dl2.md (T3)): NA' = NA, exactly one agent x
       of ch frozen in P and free in P', exactly one z free in P and frozen in P', none frozen in both, at most one
       helper h free in both, B'_z = B_x, B_x inside N_z, and B_h \\ B'_h nonempty (T3p: no helper, T3h: one);
  T4   ch nonempty, every agent of ch frozen in P and in P', NA' = NA: the frozen agents of ch permute their singleton
       bases, every other base unchanged (the coordinator's T4); T4s2 when |ch| = 2.
Relations: R13 = T1 + T3, R134 = R13 + T4, R134s2 = R13 + T4s2, RT = T1 + T2 + T3 (DL_T), RT4 = RT + T4, RT4s2 = RT + T4s2.

usage: python3 k4/dl134_xcheck.py DUMP.jsonl.gz ... [--all] [--every=E] [--out=FILE.jsonl.gz]
  Reads dl13_run.py / dl13_hunt.py / dl13_nbhd.py dump records ("D" records with "core" and "vals"); by default the
  profiles of the records with f >= 1 and branch "none" (DL13 failures), and evaluates every state of those profiles that
  the dumps list as failing (with --all: every def > 0 state with f >= 1 of each profile). Prints per state one line
  "X core prof B def k t1 t2 t3p t3h t4 t4s2 | R13 R134 R134s2 RT RT4 RT4s2 | t4min" (t4min: the least |ch| of an
  improving T4 move, 0 if none) and the totals; --out writes the same per state as JSON lines."""
import collections, gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import c4x_check as CX
from dl2_relations_xcheck import rel_B

KINDS = ('t1', 't2', 't3p', 't3h', 't4', 't4s2')
RELS = collections.OrderedDict([('R13', ('t1', 't3p', 't3h')), ('R134', ('t1', 't3p', 't3h', 't4')),
                                ('R134s2', ('t1', 't3p', 't3h', 't4s2')), ('RT', ('t1', 't2', 't3p', 't3h')),
                                ('RT4', ('t1', 't2', 't3p', 't3h', 't4')), ('RT4s2', ('t1', 't2', 't3p', 't3h', 't4s2'))])


class Prof:
    def __init__(self, sets, vals, m):
        self.sets, self.vals, self.m, self.n = sets, vals, m, len(sets)
        self.vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        res = CX.analyse(sets, m, self.vl)
        mf = max(r[2]['-frozen'] for r in res)
        self.mp = [(tuple(frozenset(B) for B in r[0]), r[2]['rodef']) for r in res if r[2]['-frozen'] == mf]
        self.f = -mf

    def val(self, i, B): return sum(self.vl[i].get(g, 0) for g in B)

    def needs(self, i, B):
        b = self.val(i, B)
        return frozenset(g for g, x in self.vl[i].items() if g not in B and x > b)

    def info(self, P):
        N = [self.needs(i, P[i]) for i in range(self.n)]
        NA = frozenset().union(*N)
        fz = [len(B) == 1 and B <= NA for B in P]
        return N, NA, fz

    def move(self, P, P2, IP, IP2):
        """the kinds of the move P -> P2 (a dict kind -> bool) and |ch|"""
        (N1, NA1, fz1), (N2, NA2, fz2) = IP, IP2
        ch = [i for i in range(self.n) if P[i] != P2[i]]
        k = {x: False for x in KINDS}
        if not ch or NA1 != NA2: return k, len(ch)
        if all(fz1[i] and fz2[i] for i in ch):
            k['t4'] = True; k['t4s2'] = len(ch) == 2
            return k, len(ch)
        if len(ch) == 1: k['t1'] = True; return k, 1
        if not any(fz1[i] or fz2[i] for i in ch): k['t2'] = True; return k, len(ch)
        xs = [i for i in ch if fz1[i] and not fz2[i]]; zs = [i for i in ch if fz2[i] and not fz1[i]]
        ws = [i for i in ch if fz1[i] and fz2[i]]; ys = [i for i in ch if not fz1[i] and not fz2[i]]
        if len(xs) == 1 and len(zs) == 1 and not ws and len(ys) <= 1:
            x, z = xs[0], zs[0]
            if P2[z] == P[x] and P[x] <= N1[z] and all(P[y] - P2[y] for y in ys):
                k['t3h' if ys else 't3p'] = True
        return k, len(ch)

    def state(self, P, dP):
        IP = self.info(P)
        better = [(Q, d) for Q, d in self.mp if d < dP]
        flags = {x: False for x in KINDS}; t4min = 0
        for Q, d in better:
            k, c = self.move(P, Q, IP, self.info(Q))
            for x in KINDS: flags[x] |= k[x]
            if k['t4'] and (t4min == 0 or c < t4min): t4min = c
        holds = {r: any(flags[x] for x in ks) for r, ks in RELS.items()}
        # cross-check of R13 and RT against rel_B (k4/dl2_relations_xcheck.py)
        rb = {r: any(rel_B(r, self.sets, self.vals, P, Q) for Q, _ in better) for r in ('R13', 'RTr')}
        ok = rb['R13'] == holds['R13'] and rb['RTr'] == holds['RT']
        dist = min((sum(1 for a, b in zip(P, Q) if a != b) for Q, _ in better), default=None)
        return flags, holds, t4min, dist, ok


def main(argv):
    files = [a for a in argv if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    print('# command: python3 k4/dl134_xcheck.py ' + ' '.join(argv), flush=True)
    profs = collections.OrderedDict()
    for fn in files:
        for l in gzip.open(fn, 'rt'):
            r = json.loads(l)
            if r.get('best') or 'core' not in r or 'vals' not in r or r.get('f', 0) < 1: continue
            if r.get('br') != 'none' and not ('all' in opt and r.get('br')): continue
            key = json.dumps([r['core']['sets'], r['vals']])
            e = profs.setdefault(key, {'core': r['core'], 'prof': r.get('prof'), 'vals': r['vals'], 'fails': set()})
            if r.get('br') == 'none': e['fails'].add(tuple(tuple(sorted(b)) for b in r['B']))
    items = list(profs.values())[::int(opt.get('every', 1))]
    print(f'# {len(profs)} profiles in the dumps, {sum(len(e["fails"]) for e in profs.values())} DL13-failing states; '
          f'evaluating {len(items)} profiles', flush=True)
    fo = gzip.open(opt['out'], 'wt') if 'out' in opt else None
    tot = collections.Counter(); kinds = collections.Counter(); t4m = collections.Counter(); bad = 0; missing = 0
    for e in items:
        c = e['core']; sets = c['sets']; m = c['m']
        Pr = Prof(sets, e['vals'], m)
        name = '%s#%s' % (c.get('file', c.get('id', '?')), c.get('pos', c.get('key', '?')))
        want = None if 'all' in opt else e['fails']
        found = set()
        for P, dP in Pr.mp:
            if dP <= 0 or Pr.f < 1: continue
            key = tuple(tuple(sorted(B)) for B in P)
            if want is not None and key not in want: continue
            found.add(key)
            flags, holds, t4min, dist, ok = Pr.state(P, dP)
            if not ok: bad += 1
            tot['states'] += 1
            for r, h in holds.items(): tot[r + (' holds' if h else ' fails')] += 1
            kinds['+'.join(x for x in KINDS if flags[x]) or 'none'] += 1
            if flags['t4']: t4m[t4min] += 1
            print('X %s %s %s def %s k %s | %s | %s | t4min %d%s' % (
                name, ','.join(map(str, e['prof'] or [])), [sorted(B) for B in P], dP, dist,
                ' '.join('%s=%d' % (x, flags[x]) for x in KINDS), ' '.join('%s=%d' % (r, h) for r, h in holds.items()),
                t4min, '' if ok else '  MISMATCH with rel_B'), flush=True)
            if fo:
                fo.write(json.dumps({'core': c, 'prof': e['prof'], 'vals': e['vals'], 'B': [sorted(B) for B in P], 'def': dP,
                                     'k': dist, 'f': Pr.f, 'kinds': flags, 'holds': holds, 't4min': t4min,
                                     'relB_agrees': ok}, separators=(',', ':')) + '\n')
        if want is not None and found != want:
            missing += 1; print('MISSING states (in the dump, not failing min-frozen states here):', name, sorted(want - found)[:3])
    if fo: fo.close()
    print('states %d; %s' % (tot['states'], ', '.join('%s holds %d / fails %d' % (r, tot[r + ' holds'], tot[r + ' fails'])
                                                      for r in RELS)))
    print('improving move kinds available (states): ' + ', '.join('%s: %d' % kv for kv in kinds.most_common()))
    print('least |ch| of an improving T4 move (states with one): ' + str(dict(sorted(t4m.items()))))
    print('R13 and RT against rel_B: %d mismatches; profiles whose dumped failing states are not all found: %d' % (bad, missing),
          flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
