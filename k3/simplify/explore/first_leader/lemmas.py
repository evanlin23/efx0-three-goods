"""Candidate lemmas that would imply Conjecture FL (or a rotation-free variant), tested on the rotation cases of K3S
(index leaders).  For each, the number of rotation cases where it holds and the smallest case (fewest agents, then
goods) where it fails.  One process.

  A  r (of the failed run) works as first leader
  B  x1 (first agent of the need chain after k*) works as first leader
  C  some agent of the need chain other than k* works as first leader
  D  some first leader x is itself never exposed: in the run from x, b_x or c_x is picked by an agent other than r
     or is an upgrade good c_u  (Lemma T then gives success whatever happens later)
  E  some first leader x gives a run whose absorber r is a leader (then r is never exposed: success)
  F  some first leader works, and it lies in B* minus k*
  G  iterate: index run; while failing, rerun with the failed run's r as the first leader (ends with a success)
  H  some first leader x is ROBUST: every run with first leader x (all later leader choices) succeeds
  J  the rotated pre-allocation P' of Theorem B (K3S's chain) has its picks realized by some draft run
  J2 ... and some run realizing P' succeeds
  K  some first leader x gives NA(run from x) contained in NA(P')   ("at least as good as P'")
  K2 ... and that run succeeds
  L  r or q works as first leader, where q is the agent that holds r's top a_r in the failed run
  L2 q works
  M  (only where A fails) the absorber of the run from r is q
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from fl import run, index_leader, first_then_index, bad_case, all_runs, needs
from survey import cases


def rotated(st):
    k, chain = bad_case(st)
    Y2 = list(st.Y)
    for s in range(1, len(chain)): Y2[chain[s]] = st.Y[chain[s - 1]]
    Y2[k] = st.rank[k][1]; U2 = st.U + [k]
    NA2 = {g for i in range(st.n) for g in needs(st.rank, Y2, U2, i)}
    return k, chain, Y2, U2, NA2


def check(n, m, rank, robust=True):
    st = run(n, m, rank, index_leader)
    if st.ok: return None
    k, chain, Y2, U2, NA2 = rotated(st)
    runs = {x: run(n, m, rank, first_then_index(x)) for x in range(n)}
    W = {x for x in runs if runs[x].ok}
    res = {}
    res['A'] = st.r in W
    res['B'] = len(chain) > 1 and chain[1] in W
    res['C'] = bool(W & set(chain[1:]))
    def own_nx(s, x):
        pick = {s.Y[i]: i for i in range(n) if s.Y[i] is not None}
        ups = {rank[u][2] for u in s.U}
        return any((g in pick and pick[g] != s.r) or g in ups for g in rank[x][1:])
    res['D'] = any(own_nx(runs[x], x) for x in range(n))
    res['E'] = any(runs[x].r in runs[x].leaders for x in range(n))
    res['F'] = bool(W & (set(st.blocks[-1]) - {k}))
    q = next((i for i in range(n) if st.Y[i] == rank[st.r][0]), None)   # holder of r's top in the failed run
    res['L'] = st.r in W or (q is not None and q in W)
    res['L2'] = q is not None and q in W
    if st.r not in W: res['M (when A fails): r of the run from r is q'] = runs[st.r].r == q
    s = st; seen = set(); ok = False
    while True:
        if s.ok: ok = True; break
        if s.r in seen: break
        seen.add(s.r); s = run(n, m, rank, first_then_index(s.r))
    res['G'] = ok
    if robust:
        res['H'] = any(all(t.ok for _, t in all_runs(n, m, rank, prefix=(x,))) for x in range(n))
        real = [t for _, t in all_runs(n, m, rank) if t.Y == Y2]
        res['J'] = bool(real)
        res['J2'] = any(t.ok for t in real)
    res['K'] = any(runs[x].NA <= NA2 for x in range(n))
    res['K2'] = any(runs[x].NA <= NA2 and runs[x].ok for x in range(n))
    return res


def main(argv):
    robust = '--no-robust' not in argv
    argv = [a for a in argv if a != '--no-robust']
    c = collections.Counter(); smallest = {}
    for n, m, rank in cases(argv):
        res = check(n, m, rank, robust)
        if res is None: continue
        c['rotation cases'] += 1
        for key, ok in res.items():
            c[key] += ok
            if not ok and (key not in smallest or (n, m) < smallest[key][:2]): smallest[key] = (n, m, rank)
    print(' '.join(argv), flush=True)
    for key in sorted(c): print('  %-16s %d' % (key, c[key]))
    for key in sorted(smallest): print('  fails', key, smallest[key])


if __name__ == '__main__':
    main(sys.argv[1:])
