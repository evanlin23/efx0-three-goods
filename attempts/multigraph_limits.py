"""Where the proof of Theorems M and X (proofs/multigraph_extension.md) stops, with its smallest configurations.
  u1   (attempts/multigraph_u1_mixed_top.md) the move U1 keeps invariant I3 only if, whenever the top a_w of the agent
       giving it up has a third valuer, the agent receiving it ranks it first. Searches every profile with a popular
       matching of every connected core with n <= 4 (all m) for a run of the construction (src/mgx.py) in which U1
       breaks I3, and prints the smallest.
  dump (attempts/multigraph_dump_class_T.md) Lemma 4.2's case analysis uses that every good that is someone's b or c
       has at most two valuers. In class T (no good with three or more valuers is anyone's top) the moves keep I1-I3,
       but facts (i) and (ii) behind its case analysis can fail. Searches every class-T profile with n <= 5 for a
       terminal state where they fail (first at n = 5), then prints the first one and an EFX0 assignment of its free
       goods found by search.
Usage (from the repository root): python attempts/multigraph_limits.py u1 | dump"""
import itertools, os, sys, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'src'))
from cores_nauty import gen_cores_nauty
from mgx import State, popular_matching, efx0_raw, valuers, dump, terminal_data, moves, PERMS

def i3_holds(st):
    H = st.holder(); env = st.enviers(H)
    return all(st.top_holder(j) for j, e in env.items() if e)

def u1_breaks(n, m, trip):
    """Run Up/U1 as in mgx.moves (no asserts); return the U1 step that breaks I3, if any."""
    Y = popular_matching(n, trip)
    if Y is None: return None
    st = State(n, m, trip, Y)
    while True:
        H = st.holder(); env = st.enviers(H); E = {j for j in env if env[j]}
        done = False
        for k in range(n):
            a, b, c = trip[k]
            if not st.Z[k] and k not in E and st.pick[k] == b and c not in H:
                st.Z[k] = (b, c); st.pick[k] = None; done = True; break
        if done: continue
        for w in sorted(E):
            a, b, c = trip[w]
            for k in sorted(env[w], key=lambda k: (st.rank[k][a], k)):
                if all(g not in H or H[g] == k for g in (b, c)):
                    before = (list(st.pick), list(st.Z))
                    st.Z[w] = (b, c); st.pick[w] = None; st.pick[k] = a
                    if not i3_holds(st):
                        return dict(Y=Y, before=before, w=w, k=k, others=sorted(env[w] - {k}))
                    done = True; break
            if done: break
        if not done: return None

def cmd_u1():
    for n in (3, 4):
        for m in range(3, 2 * n + 1):
            found = 0; ex = None
            for pi, sets in gen_cores_nauty(n, m):
                for prof in itertools.product(range(6), repeat=n):
                    trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
                    r = u1_breaks(n, m, trip)
                    if r:
                        found += 1
                        if ex is None: ex = (sets, trip, r)
            print(f'n = {n}, m = {m}: profiles in which U1 breaks I3: {found}')
            if ex:
                sets, trip, r = ex
                a = trip[r['w']][0]
                print(f'  smallest: core {sets}, rankings (a, b, c) {trip}')
                print(f'  popular matching (good held by each agent) {r["Y"]}; state before U1: picks {r["before"][0]}, '
                      f'doubled {r["before"][1]}')
                print(f'  U1 moves agent {r["w"]} to its b and c and gives its top {a} to agent {r["k"]}, which ranks it '
                      f'{"abc"[trip[r["k"]].index(a)]}; agents {r["others"]} still envy the holder of {a}, so agent '
                      f'{r["k"]} is envied without holding its top (I3 fails). Valuers of {a}: {valuers(n, trip)[a]}.')
                return

def fact_fails(n, m, trip):
    """Terminal state of the construction (class T): does fact (i) (|H_f| <= 2) or fact (ii) (an open agent lies in H_f
    for at most one free good) of Lemma 4.2 fail?"""
    Y = popular_matching(n, trip)
    if Y is None: return False
    st = State(n, m, trip, Y); moves(st, 'T')
    H, env, E, F, O, opn, closed, W, Hf = terminal_data(st)
    return any(len(Hf[f]) > 2 for f in F) or any(sum(s in Hf[f] for f in F) > 1 for s in opn)

def cmd_dump():
    from mgx import class_profiles
    for n in (3, 4, 5):
        for m in range(3, 2 * n + 1):
            cnt = 0; first = None
            for pi, sets in gen_cores_nauty(n, m):
                for prof in class_profiles(sets, 'T'):
                    trip = [tuple(S[p] for p in PERMS[k]) for S, k in zip(sets, prof)]
                    if fact_fails(n, m, trip):
                        cnt += 1; first = first or (sets, trip)
            if cnt: print(f'n = {n}, m = {m}: class-T profiles where fact (i) or (ii) fails: {cnt}; first {first}')
    print('(no such profile with n <= 4)')
    sets = [[0, 4, 5], [1, 4, 6], [0, 1, 3], [2, 3, 4], [2, 3, 4]]
    trip = [(0, 4, 5), (1, 4, 6), (0, 1, 3), (2, 4, 3), (2, 3, 4)]
    n, m = 5, 7
    print(f'core {sets}, rankings (a, b, c) {trip}; valuers {dict(sorted(valuers(n, trip).items()))}')
    Y = popular_matching(n, trip); st = State(n, m, trip, Y); cnt = moves(st, 'T')
    print(f'popular matching {Y}; moves {dict(cnt)}; terminal picks {st.pick}, doubled {st.Z}')
    H, env, E, F, O, opn, closed, W, Hf = terminal_data(st)
    print(f'envied {sorted(E)}, enviers O = {O}, open {opn}, closed {sorted(closed)}, free goods {F}')
    for f in F: print(f'  free good {f}: envied valuers W_f = {W[f]}, H_f = {sorted(Hf[f])}')
    X, case = dump(st)
    print('Lemma 4.2 case analysis:', 'does not apply' if X is None else case)
    X0 = [H.get(g, -1) for g in range(m)]
    sinks = [s for s in range(n) if s not in E]
    for choice in itertools.product(sinks, repeat=len(F)):
        Xc = list(X0)
        for f, s in zip(F, choice): Xc[f] = s
        if efx0_raw(n, m, trip, Xc):
            print('an EFX0 assignment of the free goods (owner of goods 0..6):', Xc); break

if __name__ == '__main__':
    {'u1': cmd_u1, 'dump': cmd_dump}[sys.argv[1]]()
