"""Deterministic leader rules for K3S without the rotation, built on Lemma T (proofs/k3_simple.md §3.6).

Lemma T: if r fails, every leader is exposed for r and every block other than r's (the last) has exactly one free
agent.  Two facts make parts of this checkable when a block ends, whatever happens later:

  (NX) a leader L is never exposed once b_L or c_L is picked by an agent of a block that is not the last block
       (r lies in the last block: later leaders hold their tops, so they are not upgraded);
  (FF) an agent of a non-last block that is free when its block ends stays free unless it is upgraded, and it can be
       upgraded only if it holds its b and its c is unpicked (needs come only from its own block, by (B2)).

A run is *secured* when (NX) or (FF, two such agents in one non-last block) holds; then r is a valid absorber.

Rules (leader at each insertion step; R = unprocessed agents):
  sec      : if already secured, index.  Else the smallest x in R whose block (simulated) leaves some agent of R
             unprocessed and secures the run.  Else the smallest x whose block takes all of R and whose finished run
             succeeds.  Else index.
  sec_lb   : the same, with LB's lookahead (lead_lb of k3s.py) as the last fallback.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from fl import draft, finish, run, index_leader, r1_key


def sim_block(rank, x, unproc, free, Y, peel_key=None):
    """x leads; then R1 steps (smallest index, or smallest peel_key) until none applies"""
    from fl import State
    unproc, free, Y = list(unproc), set(free), list(Y); blk = []
    tmp = State(); tmp.rank = rank; tmp.free = free
    c = x
    while c is not None:
        Y[c] = next((g for g in rank[c] if g in free), None); free.discard(Y[c]); unproc.remove(c); blk.append(c)
        pe = [j for j in unproc if any(g not in free for g in rank[j])]
        c = (pe[0] if peel_key is None else min(pe, key=lambda j: peel_key(tmp, j))) if pe else None
    return unproc, free, Y, blk


def perm_free(rank, blk, Y, free_after):
    """agents of a finished block that stay free whatever happens later (FF)"""
    na = {g for i in blk for g in (rank[i] if Y[i] is None else rank[i][:rank[i].index(Y[i])])}
    out = []
    for i in blk:
        if Y[i] is not None and Y[i] in na: continue
        if Y[i] is not None and Y[i] == rank[i][1] and rank[i][2] in free_after: continue  # may be upgraded
        out.append(i)
    return out


def secured(rank, blocks, leaders, Y, free_after, nonlast):
    """(NX) or (FF) over the blocks given, which are all known to be non-last"""
    picked = {Y[i] for b in blocks for i in b if Y[i] is not None}
    for L in leaders:
        if rank[L][1] in picked or rank[L][2] in picked: return True
    return any(len(perm_free(rank, b, Y, free_after)) >= 2 for b in blocks)


def make_sec(fallback=index_leader):
    def lead(st, unproc):
        n, m, rank = st.n, st.m, st.rank
        # blocks so far are all non-last (we are about to start another one)
        if secured(rank, st.blocks, st.leaders, st.Y, st.free, True): return unproc[0]
        full = []
        for x in unproc:
            un2, fr2, Y2, blk = sim_block(rank, x, unproc, st.free, st.Y, st.peel_key)
            if un2:
                if secured(rank, st.blocks + [blk], st.leaders + [x], Y2, fr2, True): return x
            else:
                full.append(x)
        for x in full:
            pref = list(st.leaders)
            def ch(s2, u2, pref=pref, x=x):
                t = len(s2.leaders)
                return pref[t] if t < len(pref) else x
            if run(n, m, rank, ch, st.peel_key).ok: return x
        return fallback(st, unproc)
    return lead


def lb_fallback(st, unproc):
    """construction LB's lookahead: the smallest |NA| after the leader's block, minus certain upgrades"""
    rank, n = st.rank, st.n
    best = None
    for x in unproc:
        un2, fr2, Y2, _ = sim_block(rank, x, unproc, st.free, st.Y, st.peel_key)
        done = [k for k in range(n) if k not in un2]
        junk = {g for g in fr2 if not any(g in rank[k] for k in un2)}
        up = set()
        while True:
            NA = {g for k in done if k not in up for g in (rank[k] if Y2[k] is None else rank[k][:rank[k].index(Y2[k])])}
            k = next((k for k in done if k not in up and Y2[k] == rank[k][1] and rank[k][2] in junk
                      and rank[k][1] not in NA), None)
            if k is None: break
            up.add(k); junk.discard(rank[k][2])
        key = (len(NA), x)
        if best is None or key < best: best = key
    return best[1]


def block_size_rule(sign):
    """the leader whose block is smallest (sign = +1) or largest (sign = -1), ties by index"""
    def lead(st, unproc):
        return min(unproc, key=lambda x: (sign * len(sim_block(st.rank, x, unproc, st.free, st.Y, st.peel_key)[3]), x))
    return lead


def iter_r(n, m, rank):
    """deterministic search: the index run; while it fails, rerun with the failed run's r as the FIRST leader"""
    from fl import first_then_index
    st = run(n, m, rank, index_leader); seen = set()
    while not st.ok:
        x = st.r
        if x in seen: return st
        seen.add(x)
        st = run(n, m, rank, first_then_index(x))
    return st


RULES = {'index': index_leader, 'sec': make_sec(), 'sec_lb': make_sec(lb_fallback),
         'small': block_size_rule(+1), 'large': block_size_rule(-1), 'sec_small': make_sec(block_size_rule(+1)),
         'lb': lb_fallback}
# a name ending in '+r1' (e.g. 'lb+r1') runs that leader rule with construction LB's R1 key among peelable agents
RUNNERS = {'iter_r': iter_r}


def test(argv):
    import collections
    from survey import cases
    names = argv[0].split(',')
    c = collections.Counter({'profiles': 0}); ex = {}
    for nm in names: c[nm + ' fails'] = 0      # printed even when zero (older logs omit zero counts)
    for n, m, rank in cases(argv[1:]):
        c['profiles'] += 1
        for nm in names:
            if nm.endswith('+r1'):     # the same leader rule, with construction LB's R1 key among peelable agents
                st = run(n, m, rank, RULES[nm[:-3]], r1_key)
            else:
                st = RUNNERS[nm](n, m, rank) if nm in RUNNERS else run(n, m, rank, RULES[nm])
            if not st.ok:
                c[nm + ' fails'] += 1; ex.setdefault(nm, (rank, m))
    print(' '.join(argv), dict(c), flush=True)
    for k, v in ex.items(): print('  smallest', k, v)


if __name__ == '__main__':
    test(sys.argv[1:])
