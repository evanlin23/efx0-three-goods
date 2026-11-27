"""The n = 5 OC1^max-failing starts where no REC-S repair exists (splice_search.py's 'NO REC-S REPAIR' rows), re-checked
with the multi session's own code (k4/oc1max_multi/recs_witness.witness, reduce_s.study in the E(k) and the general
canonical-chain forms), with the dangerous agents, their earliest-wanter chains and improving pool pairs, and rnd.c's
classes (OC1, OC1', one plain round, RNDOZ, RNDPZ, MD).
    python3 kgen/rounds/recs_gaps.py results/kgen_rounds/splice_search_5pure.log"""
import sys, os, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'oc1max_multi'))
import rndlib, recs_witness, reduce_s
from mmlib import Inst, base_from_picks, junk, dangerous
L = [json.loads(l.split('NO REC-S REPAIR ', 1)[1]) for l in open(sys.argv[1]) if l.startswith('NO REC-S REPAIR')]
print('$ python3 kgen/rounds/recs_gaps.py', sys.argv[1], '| starts without a REC-S repair:', len(L))
for row in L:
    sets, vals, y = row['sets'], row['vals'], tuple(row['picks'])
    I = Inst(sets, vals); n = I.n
    orders = [list(o) for o in itertools.permutations(range(n)) if tuple(I.sd(o)) == y]
    rec = dict(row, orders=orders); b = base_from_picks(y); J = junk(I, b); D = dangerous(I, b); p = [I.V(i, b[i]) for i in range(n)]
    w = recs_witness.witness(rec); stE, badE = reduce_s.study(rec, True); stG, badG = reduce_s.study(rec, False)
    E = {k: [reduce_s.earliest_chain(I, b, k, o) for o in orders] for k in D}
    pools = {k: sorted(set(T for P in E[k] for T in itertools.combinations([g for g in J + list(b[P[-1]]) if g in I.R[k]], 2) if I.V(k, T) > p[k])) for k in D}
    m = I.m; V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv): V[i][g] = x
    res, _ = rndlib.oc1z(V); r = next(r for r in res if tuple(r['picks']) == y)
    print(json.dumps({'list': row['list'], 'idx': row['idx'], 'sets': sets, 'vals': vals, 'picks': list(y), 'orders': orders}))
    print('   recs_witness:', w, '| reduce_s E-form reached:', sorted(stE), '| general form reached:', sorted(stG), '| violations', len(badE) + len(badG))
    print('   junk', J, 'dangerous', D, 'E(k)', {k: sorted(set(E[k])) for k in D}, 'improving pool pairs', pools)
    print('   rnd.c:', {k: r[k] for k in ('EXT1', 'OC1', 'OC1P', 'RND1Z', 'RNDOZ', 'RNDPZ', 'MD')})
