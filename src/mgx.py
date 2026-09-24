"""The multigraph construction for cores, and its extension to goods with three or more valuers
(workstream proof/multigraph-extension; the written proofs are in proofs/multigraph_extension.md).

A core profile is a list trip[i] = (a_i, b_i, c_i) of each agent's three goods, best first. The construction, as in the
proof (section numbers refer to proofs/multigraph_extension.md):
  1. a popular matching Y (section 1): every good that is some agent's top ("f-house") goes to one of the agents whose top
     it is; every other agent i (a "loser") gets s(i), its best good that is nobody's top, or nothing if it has none. Built
     as in the proof of Lemma 1.2: an agent-complete matching of the reduced graph G' (edges i-a_i and i-s(i)), then
     every unmatched f-house is taken over by one of its claimants.
  2. moves (section 3), while one applies: Up (an unenvied agent holding its b whose c is free takes c), U1 (an envied
     agent w holding its top whose b and c are each free or held by one envier k: w takes {b_w, c_w}, k takes a_w), then R1
     (every unenvied agent holding its top takes one free good of its own, if it has one).
  3. the dump (section 4, Lemma 4.2): free goods go to open sinks (unenvied agents whose bundle is not a closed pair).
Every step asserts the invariants I1-I3 of Lemma 3.1 and the facts F1-F4 used by Lemma 4.2, so a run is also a check of the
lemmas; every output is checked against the raw EFX0 definition (efx0_raw, three balanced realizations, no use of L5).

Classes of profiles (section 3):
  MG: every good valued by at most two agents (multigraph cores; a popular matching always exists, Lemma 1.2);
  U:  every good valued by three or more agents is the top of each of its valuers (contains MG);
  T:  no good valued by three or more agents is anyone's top (the moves keep I1-I3; Lemma 4.2's proof does not apply).
Theorems M and X: the construction succeeds on every MG profile and on every U profile that has a popular matching.

Usage: mgx.py n MODE    MODE in {mg, U, T}: every connected core with n agents (all m, enumerated by cores_nauty),
                        every profile of the class; MG = all profiles of multigraph cores. Prints counts per dump case.
       mgx.py n T --search   for T profiles on which Lemma 4.2's case analysis does not apply, also search every
                        assignment of the free goods to unenvied agents (evidence for the conjecture of section 6)."""
import itertools, sys, collections, multiprocessing as mp, time
from cores_nauty import gen_cores_nauty
PERMS = list(itertools.permutations(range(3)))


# ---------------------------------------------------------------- raw EFX0 check (independent of L5)
def efx0_raw(n, m, trip, X):
    """v_i(X_i) >= v_i(X_j - g) for all i != j, g in X_j, under three strictly balanced realizations of each ranking."""
    if len(X) != m or any(not 0 <= o < n for o in X): return False
    bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]
    for vals in ((4, 3, 2), (10, 9, 2), (10, 6, 5)):
        for i, t in enumerate(trip):
            v = dict(zip(t, vals)); own = sum(v.get(g, 0) for g in bundles[i])
            for j, B in enumerate(bundles):
                if j != i and B:
                    w = [v.get(g, 0) for g in B]
                    if sum(w) - min(w) > own: return False
    return True


# ---------------------------------------------------------------- classes
def valuers(n, trip):
    V = collections.defaultdict(list)
    for i, t in enumerate(trip):
        for g in t: V[g].append(i)
    return V

def in_class(n, trip, cls):
    V = valuers(n, trip)
    many = [g for g, vs in V.items() if len(vs) >= 3]
    if cls == 'MG': return not many
    if cls == 'U': return all(trip[i][0] == g for g in many for i in V[g])
    if cls == 'T': return all(trip[i][0] != g for g in many for i in V[g])
    raise ValueError(cls)


# ---------------------------------------------------------------- 1. popular matching
def popular_matching(n, trip):
    """A popular matching as a list Y (Y[i] = good or None), or None if the profile has none (Lemma 1.2's construction)."""
    tops = [t[0] for t in trip]; F = set(tops)
    s = [next((g for g in trip[i] if g not in F), None) for i in range(n)]
    adj = [[tops[i], s[i] if s[i] is not None else ('last', i)] for i in range(n)]
    match = {}                                    # house -> agent

    def augment(i, seen):
        for h in adj[i]:
            if h in seen: continue
            seen.add(h)
            if h not in match or augment(match[h], seen):
                match[h] = i; return True
        return False
    for i in range(n):
        if not augment(i, set()): return None     # Hall's condition fails: no agent-complete matching of G'
    of = {i: h for h, i in match.items()}
    for h in F:                                   # promotion: every f-house matched, to one of its claimants
        if h not in match:
            i = next(i for i in range(n) if tops[i] == h)
            del match[of[i]]; match[h] = i; of[i] = h
    Y = [None] * n
    for h, i in match.items():
        if not (isinstance(h, tuple) and h[0] == 'last'): Y[i] = h
    # it is a popular matching: winners hold their top, losers hold s(i) (or nothing if s(i) is undefined)
    assert all(Y[i] == tops[i] or Y[i] == s[i] for i in range(n)) and all(h in match for h in F)
    return Y


# ---------------------------------------------------------------- 2. states and moves
class State:
    """pick[i]: agent i's single held good (or None) if i is not doubled; Z[i]: the goods of a doubled agent."""
    def __init__(s, n, m, trip, Y):
        s.n, s.m, s.trip = n, m, trip
        s.rank = [{g: r for r, g in enumerate(t)} for t in trip]
        s.pick = list(Y); s.Z = [None] * n

    def holder(s):
        H = {}
        for i in range(s.n):
            for g in (s.Z[i] if s.Z[i] else ([s.pick[i]] if s.pick[i] is not None else [])): H[g] = i
        return H

    def better(s, i):
        """Goods i ranks above its pick (all three if it has none); empty for doubled agents."""
        if s.Z[i]: return ()
        return s.trip[i][:s.rank[i][s.pick[i]]] if s.pick[i] is not None else s.trip[i]

    def enviers(s, H):
        env = collections.defaultdict(set)
        for i in range(s.n):
            for g in s.better(i):
                if g in H: env[H[g]].add(i)
        return env

    def top_holder(s, i): return not s.Z[i] and s.pick[i] == s.trip[i][0]

    def check_invariants(s):
        """I1 (unitary), I2 (doubled goods are nobody's better good), I3 (every envied agent holds its top)."""
        H = s.holder(); env = s.enviers(H)
        for i in range(s.n):
            assert all(g in H for g in s.better(i)), 'I1'
            if s.Z[i]: assert all(g not in s.better(j) for g in s.Z[i] for j in range(s.n)), 'I2'
        for j, e in env.items():
            if e: assert s.top_holder(j), 'I3'

def moves(st, cls):
    """Apply Up and U1 while one applies, then R1. Returns the number of each move."""
    cnt = collections.Counter(); trip = st.trip
    while True:
        st.check_invariants()
        H = st.holder(); env = st.enviers(H); E = {j for j in env if env[j]}
        done = False
        for k in range(st.n):                                            # Up
            a, b, c = trip[k]
            if not st.Z[k] and k not in E and st.pick[k] == b and c not in H:
                st.Z[k] = (b, c); st.pick[k] = None; cnt['Up'] += 1; done = True; break
        if done: continue
        for w in sorted(E):                                              # U1
            a, b, c = trip[w]
            for k in sorted(env[w], key=lambda k: (st.rank[k][a], k)):   # claimants of a_w first
                if all(g not in H or H[g] == k for g in (b, c)):
                    if cls in ('U', 'MG') and len(valuers(st.n, trip)[a]) >= 3:
                        assert trip[k][0] == a                           # class U: the envier is a claimant
                    st.Z[w] = (b, c); st.pick[w] = None; st.pick[k] = a
                    cnt['U1'] += 1; done = True; break
            if done: break
        if not done: break
    H = st.holder(); env = st.enviers(H); E = {j for j in env if env[j]}
    for u in range(st.n):                                                # R1
        if u not in E and st.top_holder(u):
            fr = [g for g in trip[u][1:] if g not in H]
            if fr:
                st.Z[u] = (trip[u][0], fr[0]); st.pick[u] = None; H[fr[0]] = u; cnt['R1'] += 1
    st.check_invariants()
    return cnt


# ---------------------------------------------------------------- 3. the dump (Lemma 4.2)
def terminal_data(st):
    n, m, trip = st.n, st.m, st.trip
    H = st.holder(); env = st.enviers(H); E = {j for j in env if env[j]}
    F = [g for g in range(m) if g not in H]
    nd_tops = [t for t in range(n) if st.top_holder(t)]                  # non-doubled top-holders (E and T_U)
    closed = {H[trip[t][1]] for t in nd_tops if trip[t][1] in H and H.get(trip[t][2]) == H[trip[t][1]]}
    opn = [s_ for s_ in range(n) if s_ not in E and s_ not in closed]
    O = [k for k in range(n) if not st.Z[k] and not st.top_holder(k)]
    W, Hf = {}, {}
    for f in F:
        W[f] = [w for w in E if f in trip[w][1:]]
        Hf[f] = set()
        for w in W[f]:
            p = trip[w][1] if trip[w][2] == f else trip[w][2]
            assert p in H, 'F2: at most one free good per envied agent'
            assert H[p] not in env[w] and H[p] not in E, 'F2: partner held by a sink that does not envy w'
            Hf[f].add(H[p])
    for f in F:   # F1: free goods are valued only by envied agents and doubled agents
        assert all(i in E or st.Z[i] for i in valuers(n, trip)[f]), 'F1'
    return H, env, E, F, O, opn, closed, W, Hf

def dump(st):
    """Lemma 4.2's assignment of the free goods, as X (X[g] = owner) and the case used; None if no case applies."""
    n, m, trip = st.n, st.m, st.trip
    H, env, E, F, O, opn, closed, W, Hf = terminal_data(st)
    X = [H.get(g, -1) for g in range(m)]
    def give(assign, case):
        for f, s_ in assign.items(): X[f] = s_
        return X, case
    if not F: return give({}, 'no free good')
    empty = [s_ for s_ in opn if all(X[g] != s_ for g in range(m))]
    if empty: return give({f: empty[0] for f in F}, '(b) an open agent holds nothing')
    if len(opn) >= 3:
        if any(all(s_ in Hf[f] for s_ in opn) for f in F): return None, None   # impossible when |H_f| <= 2 (F4)
        return give({f: next(s_ for s_ in opn if s_ not in Hf[f]) for f in F}, '(a) three open agents')
    assert set(O) <= set(opn)
    if not O: return give({f: opn[0] for f in F}, '(c) no envier')
    if len(O) == 1:
        k = O[0]; assert all(k not in Hf[f] for f in F)
        return give({f: k for f in F}, '(c) one envier')
    k1, k2 = O                                         # |O| = 2 = |open|
    bad = {k: [f for f in F if k in Hf[f]] for k in O}
    if any(len(bad[k]) > 1 for k in O): return None, None
    both = set(bad[k1]) & set(bad[k2])
    if both:
        f = both.pop()
        return give({g: (k1 if g == f else k2) for g in F}, '(c) two enviers, crossed')
    return give({g: (k2 if g in bad[k1] else k1) for g in F}, '(c) two enviers')

def construct(n, m, trip, cls):
    Y = popular_matching(n, trip)
    if Y is None: return None, 'no popular matching', None
    st = State(n, m, trip, Y)
    cnt = moves(st, cls)
    X, case = dump(st)
    return X, case, (st, cnt)


# ---------------------------------------------------------------- exhaustive runs
def class_profiles(sets, cls):
    """All profiles of the class, as tuples of permutation indices (the class fixes or forbids some tops)."""
    V = collections.defaultdict(list)
    for i, S in enumerate(sets):
        for g in S: V[g].append(i)
    many = {g for g, vs in V.items() if len(vs) >= 3}
    choices = []
    for S in sets:
        ks = list(range(6))
        if cls == 'MG' and many: return []
        if cls == 'U': ks = [k for k in ks if all(S[PERMS[k][0]] == g for g in many if g in S)]
        if cls == 'T': ks = [k for k in ks if S[PERMS[k][0]] not in many]
        choices.append(ks)
    return itertools.product(*choices)

def exhaustive_assignment(st):
    """Evidence only: is there any assignment of the free goods to unenvied agents that is EFX0 (raw check)?"""
    n, m, trip = st.n, st.m, st.trip
    H = st.holder(); env = st.enviers(H); E = {j for j in env if env[j]}
    X0 = [H.get(g, -1) for g in range(m)]; F = [g for g in range(m) if g not in H]
    sinks = [s_ for s_ in range(n) if s_ not in E]
    for choice in itertools.product(sinks, repeat=len(F)):
        X = list(X0)
        for f, s_ in zip(F, choice): X[f] = s_
        if efx0_raw(n, m, trip, X): return True
    return False

def work(task):
    n, m, sets, cls, search = task
    tot = collections.Counter(); ex = []
    for prof in class_profiles(sets, cls):
        trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
        tot['profiles'] += 1
        X, case, info = construct(n, m, trip, cls)
        if case == 'no popular matching': tot[case] += 1; continue
        if X is None:
            tot['Lemma 4.2 case analysis does not apply'] += 1
            if search:
                tot['  ...but some assignment is EFX0' if exhaustive_assignment(info[0]) else '  ...and no assignment is EFX0'] += 1
            if len(ex) < 3: ex.append((sets, trip))
            continue
        if not efx0_raw(n, m, trip, X):
            tot['OUTPUT NOT EFX0'] += 1; ex.append(('not EFX0', sets, trip, X)); continue
        tot['EFX0: ' + case] += 1
        tot['large bundles %d' % sum(1 for j in range(n) if X.count(j) >= 3)] += 1
        for k, v in info[1].items(): tot['moves ' + k] += v
    return tot, ex

def main():
    n, cls = int(sys.argv[1]), sys.argv[2].upper()
    search = '--search' in sys.argv
    t0 = time.time(); tasks = []
    for m in range(3, 2 * n + 1):
        for pi, sets in gen_cores_nauty(n, m):
            tasks.append((n, m, sets, 'MG' if cls == 'MG' else cls, search))
    tot = collections.Counter(); exs = []
    with mp.Pool() as pool:
        for t, ex in pool.imap_unordered(work, tasks, chunksize=2):
            tot.update(t); exs += ex
    print(f"n = {n}, class {cls}: {len(tasks)} connected cores (all m), {time.time() - t0:.0f} s")
    for k in sorted(tot): print(f"  {k}: {tot[k]}")
    for e in exs[:5]: print('  example:', e)
    bad = tot['OUTPUT NOT EFX0'] + (tot['Lemma 4.2 case analysis does not apply'] if cls in ('MG', 'U') else 0)
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
