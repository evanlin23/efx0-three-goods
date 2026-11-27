"""Classify the hard perfect starts with |D| >= 2 collected by collect.py (k4/oc1max_multi.md §1).

Per start:
  * overlap type of the junk sets J_d (d in D): 'disjoint' (pairwise disjoint), 'share1' (some pair shares exactly one
    junk good, none shares two), 'share2+' (some pair shares two or more);
  * whether some dangerous agent's threat needs another agent's pick (the junk J_d alone is not a danger set:
    v_d(J_d) <= p_d, or |J_d| = 1): 'needs-pick';
  * which repairs work (from the recorded repairing moves):
      ED-S*-end   : an ED chain (Hall) with an S* completion owned by x_0 or x_t;
      CAN-k       : a canonical chain from some k in D with an S* completion owned by k;
      CAN-k-min   : the same with H_0 inclusion-minimal among the improving subsets of the pool J + B_{x_t};
      CAN-any     : a canonical chain from some k in D with an S* completion (any owner);
      CAN-OA      : a canonical chain from some k in D with a one-absorber completion (any absorber);
      ANY         : any move with a one-absorber completion.

    python3 k4/oc1max_multi/analyze.py FILE.jsonl [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk


def minimal_H0(I, x0, H0, pool, p):
    """H0 improving for x0 (value > p) and inclusion-minimal among improving subsets of pool"""
    if I.V(x0, H0) <= p: return False
    return all(I.V(x0, [g for g in H0 if g != h]) <= p for h in H0)


def classify(rec):
    I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
    Y = tuple(rec['picks']); base = base_from_picks(Y); J = set(rec['J']); D = rec['D']
    p = [I.V(i, base[i]) for i in range(I.n)]
    Jd = {int(d): set(v) for d, v in rec['Jd'].items()}
    ov = 0
    for a, b in itertools.combinations(D, 2): ov = max(ov, len(Jd[a] & Jd[b]))
    tags = set()
    tags.add('overlap=%d' % ov)
    needs_pick = [d for d in D if not (len(Jd[d]) >= 2 and I.V(d, Jd[d]) > p[d])]
    if needs_pick: tags.add('needs-pick')
    for r in rec['repairs']:
        path = r['path']; kind = r['kind']; ss = set(r['ss']); oa = set(r['oa'])
        tags.add('ANY')
        if r['ed'] and kind == 'chain' and (ss & {path[0], path[-1]}): tags.add('ED-S*-end')
        if r['ed'] and kind == 'add' and path[0] in ss: tags.add('ED-S*-end')
        if r['canon']:
            k = path[0]; xt = path[-1]
            H0 = r['H'].get('0', [])
            pool = [g for g in J | set(base[xt]) if g in I.R[k]]
            mn = minimal_H0(I, k, H0, pool, p[k])
            if oa: tags.add('CAN-OA')
            if ss: tags.add('CAN-any')
            if k in ss:
                tags.add('CAN-k')
                if mn: tags.add('CAN-k-min')
            if xt in ss: tags.add('CAN-end')
            if mn and (ss - {k, xt}): tags.add('CAN-min-other')
    return tags


if __name__ == '__main__':
    T = collections.Counter(); by = collections.defaultdict(collections.Counter); ex = {}
    for fn in sys.argv[1:]:
        for rec in records(fn):
            tags = classify(rec)
            T['starts'] += 1
            ovt = [t for t in tags if t.startswith('overlap')][0]
            key = (len(rec['D']), ovt, 'needs-pick' in tags)
            by[key]['starts'] += 1
            for t in tags:
                if t.startswith('overlap') or t == 'needs-pick': continue
                by[key][t] += 1; T[t] += 1
            for t in ['CAN-k', 'CAN-k-min', 'ED-S*-end', 'CAN-any', 'CAN-OA']:
                if t not in tags:
                    kk = (key, t)
                    if kk not in ex or len(rec['inst']['sets']) < len(ex[kk]['inst']['sets']): ex[kk] = rec
    for k in sorted(T): print(k, T[k])
    print()
    cols = ['starts', 'ANY', 'ED-S*-end', 'CAN-OA', 'CAN-any', 'CAN-k', 'CAN-k-min', 'CAN-end', 'CAN-min-other']
    print('(|D|, overlap, needs-pick)', *cols, sep=' | ')
    for key in sorted(by): print(key, *[by[key][c] for c in cols], sep=' | ')
    print()
    for kk in sorted(ex, key=str):
        r = ex[kk]
        print('smallest without', kk[1], 'in class', kk[0], ':', r['name'], 'n', len(r['inst']['sets']), 'm', r['inst']['m'],
              json.dumps([r['inst']['sets'], r['inst']['vals']]), 'picks', r['picks'])
