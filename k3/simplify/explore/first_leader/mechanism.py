"""For every rotation case of K3S (index leaders) and every WORKING first leader x, which part of Lemma T's failure
pattern the run from x breaks.  Lemma T: r fails  iff  (every leader exposed) and (every non-last block has exactly
one free agent) and (the last block has no free agent but r) and (the pairs pi_x of the exposed agents are disjoint).

Mechanisms, first that applies:
  r_leader   r is a leader (so r is not exposed; the last block = its leader plus upgraded agents)
  nx_pick    some leader L has b_L or c_L picked by an agent other than r
  nx_up      some leader L has b_L or c_L = c_u of an upgraded agent u
  two_free   some block other than the last has two free agents
  last_free  the last block has a free agent other than r
  share      two exposed agents share a junk good
Also: shape of the run from x (one block / several), whether x's own block is all agents, and which leader is
not exposed (x itself or a later one).
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from fl import run, index_leader, first_then_index, bad_case
from survey import cases


def mechanism(st):
    rank, Y, U = st.rank, st.Y, st.U
    if st.r in st.leaders: return 'r_leader'
    pickers = {Y[i]: i for i in range(st.n) if Y[i] is not None}
    ups = {rank[u][2] for u in U}
    for L in st.leaders:
        for g in rank[L][1:]:
            if g in pickers and pickers[g] != st.r: return 'nx_pick' + ('_first' if L == st.leaders[0] else '_later')
    for L in st.leaders:
        if rank[L][1] in ups or rank[L][2] in ups: return 'nx_up'
    for b in st.blocks[:-1]:
        if len([i for i in b if i in st.freeag]) >= 2: return 'two_free'
    if any(i in st.freeag and i != st.r for i in st.blocks[-1]): return 'last_free'
    if len(st.H) < len(st.E): return 'share'
    return 'other'


def main(argv):
    c = collections.Counter(); per_case = collections.Counter(); ex = {}
    for n, m, rank in cases(argv):
        st = run(n, m, rank, index_leader)
        if st.ok: continue
        c['rotation cases'] += 1
        mechs = set()
        for x in range(n):
            s = run(n, m, rank, first_then_index(x))
            if not s.ok: continue
            mk = mechanism(s); mechs.add(mk)
            c['x works: ' + mk] += 1
            c['x works: %s block(s)' % ('one' if len(s.blocks) == 1 else 'several')] += 1
            ex.setdefault(mk, (rank, m, x))
        per_case[tuple(sorted(mechs))] += 1
        if 'nx_pick_first' in mechs or 'r_leader' in mechs: c['case has x with x itself not exposed or r a leader'] += 1
    print(' '.join(argv))
    for k in sorted(c): print('  %-55s %d' % (k, c[k]))
    for k, v in per_case.most_common(): print('  case mechanisms', k, v)
    for k, v in ex.items(): print('  example', k, v)


if __name__ == '__main__':
    main(sys.argv[1:])
