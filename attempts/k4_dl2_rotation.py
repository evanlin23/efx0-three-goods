"""Replay of the f = 0 rotation trap of Conjecture DL2 (attempts/k4-dl2-rotation.md; compute/k4-dl2). Written from
the definitions of k4/c4x.md §1 and k4/strategy.md §3 with plain loops; it shares no code with k4/dl2.c or
k4/suite/model.py. (The first DL2 counterexample, dl2-n3m7 with f = 1, is the proof workstream's:
attempts/k4-dl2-three-agents.md on proof/k4-dl2-k1.)

  python3 attempts/k4_dl2_rotation.py [INSTANCE.json ...]   (default: k4/suite/instances/dl2-rot-n3m7.json)

For each instance ({"sets", "vals", "m"}; agent i values sets[i][k] at vals[i][k], every other good at 0) it checks:
  - the k = 4 core conditions (3 or 4 goods per agent, strictly balanced, at most deg - 2 private goods and p + q < s + t
    for two, every good valued, connected) and strictness (all nonempty subset sums of each agent distinct);
  - 𝒫: bases B_i inside R_i with |B_i| <= 2, pairwise disjoint; needs N_i = {g in R_i \\ B_i : v_i(g) > v_i(B_i)};
    valid iff every needed good is some agent's whole one-good base; f = the fewest frozen agents, omega = f - (2n - m);
  - def(P) for every min-frozen P: |J| - S if <= 0, else the least |C| - S_o(C) over free o and C inside J such that for
    X = B_o + (J \\ C), every x != o and every h in X: v_x(X \\ {h}) <= v_x(B_x) (raw EFX0 toward X); S_o(C) counts the
    slots 2 - |B_j| of the agents j != o that are not frozen once o's needs are taken from X;
  - the P with def > 0, and for each the least number of agents whose base must change to reach a min-frozen P' with
    smaller deficit (k*(P)), with the min-frozen P' within distance 2 listed.
Exit status 0 iff every instance has some P with k*(P) >= 3 (DL2 fails on it)."""
import itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT = [os.path.join(HERE, '..', 'k4', 'suite', 'instances', f) for f in ('dl2-rot-n3m7.json',)]


def check(d):
    sets, vals = d['sets'], d['vals']
    n = len(sets); m = d.get('m') or 1 + max(g for S in sets for g in S)
    v = [{g: x for g, x in zip(S, V)} for S, V in zip(sets, vals)]
    val = lambda i, X: sum(v[i].get(g, 0) for g in X)
    # core conditions and strictness
    ok = True
    for i in range(n):
        S = sets[i]; tot = val(i, S)
        others = set(g for j in range(n) if j != i for g in sets[j])
        priv = [g for g in S if g not in others]
        sums = [sum(c) for k in range(1, len(S) + 1) for c in itertools.combinations([v[i][g] for g in S], k)]
        if not (3 <= len(S) <= 4): ok = False; print(f'  agent {i}: {len(S)} goods')
        if any(2 * v[i][g] >= tot for g in S): ok = False; print(f'  agent {i}: not strictly balanced')
        if len(priv) + 2 > len(S): ok = False; print(f'  agent {i}: too many private goods')
        if len(priv) == 2 and not val(i, priv) < tot - val(i, priv): ok = False; print(f'  agent {i}: p + q >= s + t')
        if len(set(sums)) != len(sums): ok = False; print(f'  agent {i}: not strict')
    if set(g for S in sets for g in S) != set(range(m)): ok = False; print('  a good valued by nobody')
    seen, todo = {0}, [0]
    while todo:
        i = todo.pop()
        for j in range(n):
            if j not in seen and set(sets[i]) & set(sets[j]): seen.add(j); todo.append(j)
    if len(seen) != n: ok = False; print('  not connected')
    print(f'  n = {n}, m = {m}; connected strict k = 4 core: {ok}')

    def needs(i, X): return frozenset(g for g in sets[i] if g not in X and v[i][g] > val(i, X))
    opts = [[frozenset(c) for k in range(3) for c in itertools.combinations(S, k)] for S in sets]
    P = []
    for Bs in itertools.product(*opts):
        if sum(len(B) for B in Bs) != len(frozenset().union(*Bs)): continue          # disjoint
        NA = frozenset().union(*(needs(i, Bs[i]) for i in range(n)))
        singles = frozenset(next(iter(B)) for B in Bs if len(B) == 1)
        if NA <= singles: P.append((Bs, NA))
    f = min(len(NA) for _, NA in P)
    omega = f - (2 * n - m)
    print(f'  |P| = {len(P)}, f = {f}, omega = {omega}')
    mp = [Bs for Bs, NA in P if len(NA) == f]

    def deficit(Bs):
        N = [needs(i, Bs[i]) for i in range(n)]
        NA = frozenset().union(*N)
        J = frozenset(range(m)) - frozenset().union(*Bs)
        frozen = [len(Bs[i]) == 1 and Bs[i] <= NA for i in range(n)]
        S = sum(2 - len(Bs[i]) for i in range(n) if not frozen[i])
        if len(J) <= S: return len(J) - S
        best = None
        for o in range(n):
            if frozen[o]: continue
            for k in range(len(J) + 1):
                for C in itertools.combinations(sorted(J), k):
                    X = Bs[o] | (J - frozenset(C))
                    if any(val(x, X - {h}) > val(x, Bs[x]) for x in range(n) if x != o for h in X): continue
                    NA2 = frozenset().union(*(N[j] for j in range(n) if j != o)) | needs(o, X)
                    slots = sum(2 - len(Bs[j]) for j in range(n) if j != o and not (len(Bs[j]) == 1 and Bs[j] <= NA2))
                    if best is None or k - slots < best: best = k - slots
        return best        # None: no free owner (+inf)

    INF = float('inf')
    df = {Bs: (INF if (x := deficit(Bs)) is None else x) for Bs in mp}
    print(f'  {len(mp)} min-frozen P; least deficit {min(df.values())} (C4min in removal-only form holds iff <= 0)')
    dist = lambda A, B: sum(1 for a, b in zip(A, B) if a != b)
    fails = False
    for Bs in mp:
        if df[Bs] <= 0: continue
        better = [B2 for B2 in mp if df[B2] < df[Bs]]
        k = min((dist(Bs, B2) for B2 in better), default=INF)
        near = [B2 for B2 in mp if B2 != Bs and dist(Bs, B2) <= 2]
        J = sorted(set(range(m)) - set().union(*Bs))
        print(f'  P = {[sorted(B) for B in Bs]}, J = {J}: def(P) = {df[Bs]}, k*(P) = {k}; min-frozen P\' within distance 2: '
              + (', '.join(f'{[sorted(B) for B in B2]} (def {df[B2]})' for B2 in near) if near else 'none'))
        if k >= 3: fails = True
    print(f'  DL2 {"FAILS" if fails else "holds"} on this instance')
    return fails


if __name__ == '__main__':
    files = sys.argv[1:] or DEFAULT
    allfail = True
    for fn in files:
        d = json.load(open(fn))
        print(d.get('id', fn))
        allfail &= check(d)
    sys.exit(0 if allfail else 1)
