"""Which truly dangerous agent's chain to take at the SLOT starts (k4/p3.md section 6; the class {C:D_T} of
k4/p3/fk2_residue.py). For every SLOT start with an SD order on record (the t1_p2.py and collect.py records carry one),
and every k in D_T: does some jump chain starting at d_1 = k repair (some improving H_0; SAT, oc1max.Checker)? Then how
often a fixed rule for k picks a repairing one:
  - first / last: the first / last agent of D_T in the SD order;
  - wanter-best / wanter-worst: the agent of D_T whose pick its wanter values most / least, relative to the wanter's
    own pick (ties: first in the order);
  - deepest / shallowest: the agent of D_T with the longest / shortest need path;
  - fewest-left: the agent of D_T whose canonical chain (with H_0 = its whole pool) leaves the fewest other agents of
    D_T frozen.
    python3 k4/p3/slot_rules.py FILE [FILE ...]      (jsonl[.gz] of hard starts with 'order')
"""
import sys, os, gzip, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker
from keep2 import analyse, chain, frozen_at, state
from fk2 import jump_chains, hypotheses
from fk2_residue import failures


def records(path):
    op = gzip.open if path.endswith('.gz') else open
    for line in op(path, 'rt'):
        d = json.loads(line); r = d.get('inst', d)
        if 'order' in d or 'order' in r: yield r['sets'], r['vals'], r['m'], d['picks'], d.get('order', r.get('order'))


if __name__ == '__main__':
    cnt = collections.Counter()
    print('$ python3 k4/p3/slot_rules.py ' + ' '.join(sys.argv[1:]))
    for path in sys.argv[1:]:
        for sets, vals, m, Y, order in records(path):
            I = Inst(sets, vals, m); K = Checker(I)
            base = tuple(frozenset([y]) for y in Y)
            if K.complete(base) is not None: K.close(); continue
            J, p, w, F, Dg, DT, EJ = analyse(I, list(Y))
            chs = list(jump_chains(I, Y, J, p, w, F))
            if any(hypotheses(I, Y, J, p, *c) for c in chs): K.close(); continue
            fs = set(); good = set()
            for c in chs:
                if K.complete(tuple(c[4])) is None: continue
                good.add(c[0]); fs |= set(failures(I, Y, J, p, DT, EJ, *c).values())
            mins = [f for f in fs if not any(g < f for g in fs)]
            if mins != [frozenset({'C:D_T'})]: K.close(); continue
            cnt['SLOT starts with an order'] += 1
            pos = {a: i for i, a in enumerate(order)}
            DTs = sorted(DT, key=lambda a: pos[a])
            cnt[f'|D_T| = {len(DTs)}'] += 1
            ok = [k for k in DTs if k in good]
            cnt['agents of D_T whose jump chains repair: ' + ('all' if len(ok) == len(DTs) else 'some' if ok else 'none')] += 1
            rel = lambda k: I.v[w[k]][Y[k]] - p[w[k]]
            pool = lambda k: [g for g in J if g in I.R[k]] + ([Y[chain(w, k)[-1]]] if Y[chain(w, k)[-1]] in I.R[k] else [])
            def left(k):
                P = chain(w, k); B = state(I, Y, P, pool(k))
                return sum(1 for d in DT if d != k and frozen_at(I, B, d))
            rules = {'first': DTs[0], 'last': DTs[-1],
                     'wanter-best': max(DTs, key=lambda k: (rel(k), -pos[k])),
                     'wanter-worst': min(DTs, key=lambda k: (rel(k), pos[k])),
                     'deepest': max(DTs, key=lambda k: (len(chain(w, k)), -pos[k])),
                     'shallowest': min(DTs, key=lambda k: (len(chain(w, k)), pos[k])),
                     'fewest-left': min(DTs, key=lambda k: (left(k), pos[k]))}
            for r, k in rules.items(): cnt[f'rule {r}: ' + ('repairs' if k in good else 'fails')] += 1
            K.close()
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
