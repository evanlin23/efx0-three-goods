"""The repair tables of compute/k4-dl2 from dl2_run.py's --tables files (JSON with the merged T and A counts of
k4/dl2.c). EVIDENCE only.

  python3 k4/dl2_table.py TABLES.json ...

For every P with def(P) > 0 (min-frozen, omega >= 1), dl2.c records:
  - its signature: the classes of the exposures (x, o) w.r.t. its best owners o (free x: Lemma H3's e1, e2, e3, or fO
    for a free exposure of none of those shapes, possible since P need not be Pareto-maximal; frozen x: Lemma H7's G,
    G1, L, or O), "D2" if some frozen agent is exposed w.r.t. two or more free owners (Lemma D(ii)), "allfrozen", and
    "PM" if P is Pareto-maximal (Lemmas H3 and H7 are stated for those; table (1b) restricts to them);
  - the canonical repair: a min-frozen P' at the least distance k with def(P') < def(P) moving the fewest goods, as
    a code per changed agent: T trade (a good moves between it and another changed agent), G grow, S shrink, W swap
    with the pool, with the base sizes before > after; and the roles of the changed agents (F/f frozen or free in P >
    in P', o a best owner of P, x exposed w.r.t. a best owner);
  - every repair type available at the least distance (table A).
Prints: (1) the canonical repairs by k and kind (sizes dropped) against each single class (a P counts once under each
class of its signature); (2) the same by full signature (the 25 most frequent); (3) the roles of the changed agents;
(4) the repair types available at the least distance, by class."""
import json, sys
from collections import defaultdict

CLS = ['e1', 'e2', 'e3', 'fO', 'G', 'G1', 'L', 'O', 'D2', 'allfrozen', 'PM']


def kind(t):
    if t == 'none': return 'none'
    codes = t.split('+')
    return f"k={len(codes)} " + '+'.join(sorted(c[0] for c in codes))


def main():
    T, A = defaultdict(int), defaultdict(int)
    cmds = []
    for fn in sys.argv[1:]:
        d = json.load(open(fn))
        cmds.append(d.get('command'))
        for k, c in d['T'].items(): T[k] += c
        for k, c in d['A'].items(): A[k] += c
    print('# command: python3 k4/dl2_table.py ' + ' '.join(sys.argv[1:]))
    for c in cmds: print('#   from: ' + str(c))
    tot = sum(T.values())
    print(f'P with def > 0: {tot}')
    # (1) kind vs single class
    kinds = defaultdict(int); bycls = defaultdict(lambda: defaultdict(int)); clsn = defaultdict(int)
    for key, c in T.items():
        sig, typ, roles = key.split('|')
        kd = kind(typ); kinds[kd] += c
        for s in sig.split(','):
            bycls[s][kd] += c; clsn[s] += c
    ks = sorted(kinds, key=lambda x: (x.split()[0], -kinds[x]))
    cl = [c for c in CLS if clsn[c]]
    print('\n(1) canonical repair (k agents; kinds T trade, G grow, S shrink, W swap with the pool) by class of the '
          'blocking exposures (a P counts under each class of its signature)\n')
    print('| repair | all | ' + ' | '.join(cl) + ' |')
    print('|---|---|' + '---|' * len(cl))
    for k in ks:
        print(f'| {k} | {kinds[k]} | ' + ' | '.join(str(bycls[c].get(k, '')) for c in cl) + ' |')
    print(f'| **P** | {tot} | ' + ' | '.join(str(clsn[c]) for c in cl) + ' |')
    # (1b) the same restricted to the Pareto-maximal P
    kp = defaultdict(int); bycp = defaultdict(lambda: defaultdict(int)); clp = defaultdict(int); totp = 0
    for key, c in T.items():
        sig, typ, roles = key.split('|')
        ss = sig.split(',')
        if 'PM' not in ss: continue
        kd = kind(typ); kp[kd] += c; totp += c
        for s in ss:
            if s != 'PM': bycp[s][kd] += c; clp[s] += c
    clq = [c for c in CLS if clp[c]]
    print('\n(1b) the same for the Pareto-maximal P only (the setting of Lemmas H3 and H7)\n')
    print('| repair | all PM | ' + ' | '.join(clq) + ' |')
    print('|---|---|' + '---|' * len(clq))
    for k in sorted(kp, key=lambda x: (x.split()[0], -kp[x])):
        print(f'| {k} | {kp[k]} | ' + ' | '.join(str(bycp[c].get(k, '')) for c in clq) + ' |')
    print(f'| **P** | {totp} | ' + ' | '.join(str(clp[c]) for c in clq) + ' |')
    # (2) by full signature
    bysig = defaultdict(lambda: defaultdict(int)); sign = defaultdict(int)
    for key, c in T.items():
        sig, typ, roles = key.split('|')
        bysig[sig][kind(typ)] += c; sign[sig] += c
    top = sorted(sign, key=lambda s: -sign[s])[:25]
    print('\n(2) canonical repair by full signature (the 25 most frequent signatures)\n')
    print('| signature | P | ' + ' | '.join(ks) + ' |')
    print('|---|---|' + '---|' * len(ks))
    for s in top:
        print(f'| {s} | {sign[s]} | ' + ' | '.join(str(bysig[s].get(k, '')) for k in ks) + ' |')
    # (3) roles
    rol = defaultdict(int)
    for key, c in T.items():
        sig, typ, roles = key.split('|')
        if roles == 'none': rol['none'] += c; continue
        rs = roles.split('+')
        tags = []
        for r in rs:
            t = r[0] + '>' + r[2]
            if 'o' in r[3:]: t += ' owner'
            if 'x' in r[3:]: t += ' exposed'
            tags.append(t)
        rol[f'k={len(rs)}: ' + ' + '.join(sorted(tags))] += c
    print('\n(3) the changed agents of the canonical repair (frozen F / free f in P > in P\'; "owner": a best owner of '
          'P; "exposed": exposed w.r.t. a best owner)\n')
    print('| changed agents | P |')
    print('|---|---|')
    for r, c in sorted(rol.items(), key=lambda x: -x[1]):
        print(f'| {r} | {c} |')
    # (4) availability (A): every repair type available at the least distance, counted once per (P, type)
    av = defaultdict(int)
    for key, c in A.items():
        sig, typ = key.split('|')
        for s in sig.split(','): av[(s, typ)] += c
    print('\n(4) repair types available at the least distance, by class (a P counts once per class of its signature '
          'and per available type; the 40 most frequent)\n')
    print('| class | repair type | P |')
    print('|---|---|---|')
    for (s, typ), c in sorted(av.items(), key=lambda x: -x[1])[:40]:
        print(f'| {s} | {typ} | {c} |')

if __name__ == '__main__':
    main()
