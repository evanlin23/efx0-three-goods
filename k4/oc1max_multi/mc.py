"""Lemma M^c (k4/oc1max_multi.md §9): the compensated matching form of the completion, and its check against brute force.

Shape S^c at a state B with owner o: o takes the rest of the junk; every other agent with at most one base good
(holders and frozen single-good agents) takes at most one junk good; agents with two or more base goods take nothing.
At a perfect start (all bases single goods) S^c is exactly the one-absorber shape (Lemma 1).

Model (Lemma M^c).  Hypothesis (G2): no junk good is wanted.  For H inside the junk J and a set F_s of frozen single-good
agents (the frozen slots), put X = B_o + (J - H) and, for each agent i != o,
    tau_i = max( v_i(B_i),
                 max over non-owner multi-good bundles B_q (q != i) of max_h v_i(B_q - h),     [compensated (G1)]
                 max over j in F_s whose good y_j agent i wants of v_i(y_j) ),                  [Lemma 1's (S1)]
and tau_o the same for the owner (without the v_o(B_o) term).  Agent i != o is *needy* if tau_i > v_i(B_i) or X
threatens i at v_i(B_i).  The eligible agents are the holders and F_s.  Graph Gamma^c: h ~ i (i eligible) iff i is not
needy, or i values h, v_i(B_i) + v_i(h) >= tau_i, and X does not threaten i at v_i(B_i) + v_i(h).
Then B has an S^c completion with owner o and d dummy slots iff for some (H, F_s):
    (C1) every needy agent is eligible;  (C2) v_o(X) >= tau_o;
    (C3) Gamma^c has a matching covering the needy agents with at least |H| - d edges.

    python3 k4/oc1max_multi/mc.py FILE [...]      (files of starts: hard2 records or walk_fail rows)
"""
import sys, os, json, gzip, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, frozen, holders, moves, oa_absorbers


def threat_val(I, i, S):
    """max_h v_i(S - h) for |S| >= 2 (the value i must reach not to be threatened by S), else 0"""
    if len(S) < 2: return 0
    vs = [I.v[i].get(g, 0) for g in S]
    return sum(vs) - min(vs)


def g2(I, B):
    J = junk(I, B)
    return all(I.v[i].get(g, 0) <= I.V(i, B[i]) for i in range(I.n) for g in J)


def _match(adj, left, must):
    """is there a matching saturating `left` (goods) and one covering `must` (agents)?  By Mendelsohn-Dulmage both at
    once then exist; return (size of a maximum matching, whether `must` can be covered)"""
    def maxm(goods, agents_ok):
        mt = {}
        def aug(h, seen):
            for a in adj[h]:
                if a in seen or not agents_ok(a): continue
                seen.add(a)
                if a not in mt or aug(mt[a], seen): mt[a] = h; return True
            return False
        return sum(1 for h in goods if aug(h, set())), mt
    nu, _ = maxm(left, lambda a: True)
    # cover `must`: match from the agents' side
    radj = collections.defaultdict(list)
    for h in left:
        for a in adj[h]: radj[a].append(h)
    mt = {}
    def aug2(a, seen):
        for h in radj[a]:
            if h in seen: continue
            seen.add(h)
            if h not in mt or aug2(mt[h], seen): mt[h] = a; return True
        return False
    cover = all(aug2(a, set()) for a in must)
    return nu, cover


def model(I, B, o, d=0):
    """Lemma M^c: does B have an S^c completion with owner o and d dummy slots?"""
    n = I.n; J = junk(I, B); F = set(frozen(I, B))
    N1 = holders(I, B, o)
    F1 = [j for j in range(n) if j != o and len(B[j]) == 1 and j in F]
    Qm = [q for q in range(n) if q != o and len(B[q]) >= 2]
    b = [I.V(i, B[i]) for i in range(n)]
    W = {j: [i for i in range(n) if i != j and I.v[i].get(B[j][0], 0) > b[i]] for j in F1}
    thQ = [max([threat_val(I, i, B[q]) for q in Qm if q != i] + [0]) for i in range(n)]
    for r in range(len(F1) + 1):
        for Fs in itertools.combinations(F1, r):
            tau = list(thQ)
            for j in Fs:
                for i in W[j]: tau[i] = max(tau[i], I.v[i][B[j][0]])
            elig = set(N1) | set(Fs)
            for s in range(len(J) + 1):
                for H in itertools.combinations(J, s):
                    X = list(B[o]) + [g for g in J if g not in H]
                    if I.V(o, X) < tau[o]: continue                                   # (C2)
                    needy = [i for i in range(n) if i != o and (tau[i] > b[i] or I.threat(i, b[i], X))]
                    if any(i not in elig for i in needy): continue                       # (C1)
                    adj = {}
                    for h in H:
                        adj[h] = [i for i in elig if i not in needy or
                                  (h in I.R[i] and b[i] + I.v[i][h] >= tau[i] and not I.threat(i, b[i] + I.v[i][h], X))]
                    nu, cover = _match(adj, list(H), needy)
                    if cover and nu >= len(H) - d: return True                          # (C3)
    return False


def brute(I, B, o, d=0):
    """S^c completion with owner o and d dummy slots, by enumeration and the raw EFX0 definition"""
    n = I.n; J = junk(I, B)
    elig = [i for i in range(n) if i != o and len(B[i]) <= 1]
    for s in range(len(J) + 1):
        for H in itertools.combinations(J, s):
            rest = [g for g in J if g not in H]
            # assign the goods of H to distinct eligible agents or (at most d of them) to dummies
            for k in range(max(0, s - d), min(s, len(elig)) + 1):
                for Hg in itertools.combinations(H, k):
                    for who in itertools.permutations(elig, k):
                        X = [list(x) for x in B]
                        for g, i in zip(Hg, who): X[i].append(g)
                        X[o] += rest
                        if I.efx0(X): return True
    return False


def states(rec):
    I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m']) if 'inst' in rec else Inst(rec['sets'], rec['vals'])
    b = base_from_picks(tuple(rec['picks'])); out = [b]; ms = list(moves(I, b))
    out += ms
    if 'inst' not in rec:   # walk failures: also some two-move states
        for B1 in ms[:: max(1, len(ms) // 6)]: out += list(moves(I, B1))[::5]
    return I, out


def job(rec):
    I, sts = states(rec); C = collections.Counter(); bad = []
    for B in sts:
        if not g2(I, B): C['states without (G2), skipped'] += 1; continue
        C['states'] += 1
        for o in range(I.n):
            for d in (0, 1):
                a = model(I, B, o, d); c = brute(I, B, o, d)
                C['owner tests (d = %d)' % d] += 1; C['  S^c exists (d = %d)' % d] += c
                if a != c: bad.append((I.sets, I.vals, B, o, d, a, c))
        if all(len(x) <= 1 for x in B):
            oa = bool(oa_absorbers(I, B)); sc = any(brute(I, B, o) for o in range(I.n))
            C['single-good states: one-absorber == S^c'] += (oa == sc); C['single-good states'] += 1
    return C, bad


def load(fn):
    f = gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)
    return [json.loads(l) for l in f]


if __name__ == '__main__':
    recs = []
    for fn in sys.argv[1:]: recs += load(fn)
    step = int(os.environ.get('STEP', '1')); recs = recs[::step]
    T = collections.Counter(); bad = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C, b in pool.imap_unordered(job, recs, chunksize=4):
            T.update(C); bad += b
    print('$ python3 k4/oc1max_multi/mc.py', *sys.argv[1:], '(STEP=%d)' % step)
    for k in sorted(T): print(k, T[k])
    print('mismatches between Lemma M^c and brute force:', len(bad), bad[:3])
