"""A fast, trace-keeping re-implementation of K3S steps 1-3 for strict ranking profiles (every agent ranks three
goods a > b > c with a < b + c, values (4, 3, 2)), with an arbitrary leader rule.  Cross-checked against
k3/simplify/k3s.py by `python fl.py check`.

run(n, m, rank, choose) -> State with: order, Y (picks), blocks (lists of agents), leaders, U (upgraded, in order),
r, E (exposed for r), H (HitSet, deduplicated), F (free agents other than r), ok (step 3 succeeds).
choose(state_so_far, unproc) returns the leader for an insertion step; state_so_far has .order, .Y, .free, .blocks.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..'))


class State:
    pass


def draft(n, m, rank, choose, peel_key=None):
    """Step 1.  Peelable = has lost a good (all agents strict).  Among peelable agents: smallest index (K3S), or the
    smallest peel_key(state, j) if given."""
    st = State(); st.n, st.m, st.rank = n, m, rank
    st.free = set(range(m)); st.Y = [None] * n; st.order = []; st.blocks = []; st.leaders = []
    st.peel_key = peel_key
    unproc = list(range(n))
    while unproc:
        pe = [j for j in unproc if any(g not in st.free for g in rank[j])]
        if pe:
            i = pe[0] if peel_key is None else min(pe, key=lambda j: peel_key(st, j))
        else:
            i = choose(st, list(unproc)); st.leaders.append(i); st.blocks.append([])
        st.Y[i] = next((g for g in rank[i] if g in st.free), None)
        st.free.discard(st.Y[i]); st.order.append(i); unproc.remove(i); st.blocks[-1].append(i)
    return st


def r1_key(st, j):
    """construction LB's R1 priority (src/construct.py): rank of the favourite remaining good (3 if none), number of
    goods left, index"""
    left = [g for g in st.rank[j] if g in st.free]
    return (st.rank[j].index(left[0]) if left else 3, len(left), j)


def needs(rank, Y, U, i):
    if i in U: return ()
    if Y[i] is None: return tuple(rank[i])
    return tuple(rank[i][:rank[i].index(Y[i])])


def finish(st):
    """Steps 2-3 of K3S (upgrade loop in index order, absorber r, HitSet test with one slot per free agent)."""
    n, m, rank, Y = st.n, st.m, st.rank, st.Y
    U = []
    def junk():
        used = {g for g in Y if g is not None} | {rank[u][2] for u in U}
        return {g for g in range(m) if g not in used}
    while True:
        J = junk(); NA = {g for i in range(n) for g in needs(rank, Y, U, i)}
        k = next((k for k in range(n) if k not in U and Y[k] == rank[k][1] and rank[k][2] in J
                  and rank[k][1] not in NA), None)
        if k is None: break
        U.append(k)
    J = junk(); NA = {g for i in range(n) for g in needs(rank, Y, U, i)}
    st.U, st.J, st.NA = U, J, NA
    st.freeag = [i for i in range(n) if i not in U and (Y[i] is None or Y[i] not in NA)]
    r = [i for i in st.order if i not in U][-1]; st.r = r
    W = J | ({Y[r]} if Y[r] is not None else set())
    E = [x for x in range(n) if x != r and x not in U and Y[x] == rank[x][0] and rank[x][1] in W and rank[x][2] in W]
    st.E = E
    one = lambda z: rank[z][1] if rank[z][1] in J else rank[z][2]
    H = None
    for x in E:
        for y in E:
            if x != y and H is None:
                for g in (rank[x][1], rank[x][2]):
                    if g in J and g in (rank[y][1], rank[y][2]) and H is None:
                        H = [g] + [one(z) for z in E if z not in (x, y)]
    if H is None: H = [one(z) for z in E]
    st.H = list(dict.fromkeys(H))
    st.F = len([i for i in st.freeag if i != r])
    st.ok = len(st.H) <= st.F
    return st


def run(n, m, rank, choose, peel_key=None):
    return finish(draft(n, m, rank, choose, peel_key))


def index_leader(st, unproc): return unproc[0]


def first_then_index(x):
    def ch(st, unproc):
        if not st.leaders and x in unproc: return x
        return unproc[0]
    return ch


def seq_leader(seq):
    """leaders from the list seq (while the next one is unprocessed), then by index"""
    def ch(st, unproc):
        t = len(st.leaders)
        if t < len(seq) and seq[t] in unproc: return seq[t]
        return unproc[0]
    return ch


class Need(Exception):
    pass


def all_runs(n, m, rank, prefix=(), peel_key=None):
    """every run: yield (leader sequence, State) for every sequence of leader choices extending prefix"""
    def ch(seq):
        def f(st, unproc):
            t = len(st.leaders)
            if t < len(seq):
                assert seq[t] in unproc
                return seq[t]
            raise Need(unproc)
        return f
    stack = [tuple(prefix)]
    while stack:
        seq = stack.pop()
        try:
            st = run(n, m, rank, ch(seq), peel_key)
            yield seq, st
        except Need as e:
            for x in e.args[0]: stack.append(seq + (x,))


def bad_case(st):
    """rotation data of K3S: k = last exposed agent, the scanned need chain"""
    rank, Y, U = st.rank, st.Y, st.U
    k = max(st.E, key=st.order.index); chain = [k]
    for j in st.order[st.order.index(k) + 1:]:
        cur = chain[-1]
        if Y[cur] is not None and Y[cur] in st.NA and j not in U and Y[cur] in needs(rank, Y, U, j):
            chain.append(j)
    return k, chain


def check():
    from k3s import k3s
    from lbx import core_profiles
    from test_k3s import gen_small
    from exp_first_leader import with_first
    cnt = 0; rot = 0
    for src in [core_profiles(4), gen_small(3, 5), gen_small(3, 6)]:
        for n, m, rank in src:
            v = [dict(zip(r, (4, 3, 2))) for r in rank]
            a = k3s(n, m, v, rotate=False) is not None
            b = run(n, m, rank, index_leader).ok
            assert a == b, (rank, m)
            if not a:
                rot += 1
                for x in range(n):
                    a2 = k3s(n, m, v, leader=with_first(x), rotate=False) is not None
                    b2 = run(n, m, rank, first_then_index(x)).ok
                    assert a2 == b2, (rank, m, x)
            cnt += 1
    print('agree on', cnt, 'profiles;', rot, 'rotation cases, every first leader agrees too')


if __name__ == '__main__':
    if sys.argv[1:] == ['check']: check()
