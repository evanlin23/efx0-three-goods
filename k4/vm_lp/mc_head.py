"""Does the infeasibility certificate of Lemma M^c (k4/oc1max_multi.md §9) name the head of the repairing chain?
(Timeboxed exploration for the coordinator; k4/vm_lp/rs_dual.md §4, attempts/k4-vm-lp-mc-head.md.)

At a perfect start Y (every agent holds one pick, no multi-good bundle) Lemma M^c with d = 0 says: Y has a one-absorber
EFX0 completion iff for some owner o, set H of junk goods and set F_s of frozen singles (other than o):
  (C1) every needy agent is eligible (eligible = unfrozen agents and F_s, the owner excluded);
  (C2) v_o(X) >= tau_o, where X = {Y_o} + (J - H);
  (C3) Gamma^c(H, F_s) has a matching saturating H and covering every needy agent.
Here b_i = v_i(Y_i); tau_i = max(b_i (i != o), v_i(y_j) for j in F_s whose pick i wants); i != o is needy if
tau_i > b_i or X threatens i at b_i; h ~ i in Gamma^c iff i is eligible and (i is not needy, or i values h,
b_i + v_i(h) >= tau_i and X does not threaten i at b_i + v_i(h)).  (Implemented here from that text; checked against
rklib's brute-force one-absorber search.)

At a start where the picks fail, every (o, H, F_s) violates something.  The agents a violation NAMES:
  (C2) the owner o;  (C1) the needy non-eligible agents;  (C3) the needy agents left uncovered by a maximum matching
  of Gamma^c (they lie in a Hall-deficient set; for a non-saturable H, the agents adjacent to the deficient goods).
For each owner, the closest triples are those with the fewest named agents; the certificate's named set for o is the
union of their named agents.  The repairing chains are rklib's official moves after which the bases have a
one-absorber completion; a chain's HEAD is x_0 (the agent that takes a junk set H_0).  Reported: whether some / every
repairing chain head is named for every owner, for some owner, or not at all; and whether some repairing move changes
a named agent at all.  Starts where a junk good is wanted (no (G2), so not Pareto optimal) are skipped.  EVIDENCE only.
    python3 k4/vm_lp/mc_head.py SOURCE [LIMIT]     (SOURCE: 'export' or a k4/vm data source such as cores:4:3000:301)"""
import sys, os, gzip, json, itertools, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'vm'))
import rklib_copy as R
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def threat(P, i, X, t):
    """X threatens i at value t: |X| >= 2 and max_h v_i(X - h) > t"""
    X = list(X)
    if len(X) < 2: return False
    tot = P.u(i, X)
    return tot - min(P.val[i].get(h, 0) for h in X) > t


def bip_max_matching(adj, left):
    """maximum matching of a bipartite graph given as adj[l] = list of right vertices; returns dict left -> right"""
    match_r = {}
    def aug(l, seen):
        for r in adj.get(l, []):
            if r in seen: continue
            seen.add(r)
            if r not in match_r or aug(match_r[r], seen):
                match_r[r] = l; return True
        return False
    for l in left: aug(l, set())
    return {l: r for r, l in match_r.items()}


def mc_eval(P, Y, o, H, Fs, wants, frozen):
    """the (C1)-(C3) evaluation of one triple: (feasible, named agents)"""
    n = P.n; J = [g for g in range(P.m) if g not in Y]
    X = [Y[o]] + [g for g in J if g not in H]
    b = [P.val[i][Y[i]] for i in range(n)]
    tau = [0] * n
    for i in range(n):
        tau[i] = b[i] if i != o else 0
        for j in Fs:
            if (i, j) in wants: tau[i] = max(tau[i], P.val[i][Y[j]])
    eligible = set(i for i in range(n) if i != o and (i not in frozen or i in Fs))
    needy = set(i for i in range(n) if i != o and (tau[i] > b[i] or threat(P, i, X, b[i])))
    named = set()
    if not P.u(o, X) >= tau[o]: named.add(o)                                   # (C2)
    named |= needy - eligible                                                  # (C1)
    # (C3): goods H to eligible agents; must saturate H and cover the needy
    adj = {}
    for h in H:
        adj[h] = [i for i in eligible if (i not in needy) or (
            h in P.rel[i] and b[i] + P.val[i][h] >= tau[i] and not threat(P, i, X, b[i] + P.val[i][h]))]
    # a matching saturating H and covering needy: needy agents need a good; check with a matching from the agents'
    # side restricted so that needy agents are matched: give priority by matching needy first, then the rest of H
    agents_adj = collections.defaultdict(list)
    for h, L in adj.items():
        for i in L: agents_adj[i].append(h)
    Mn = bip_max_matching(agents_adj, sorted(needy & eligible))                # cover the needy first
    uncovered = (needy & eligible) - set(Mn)
    named |= uncovered
    # then extend to saturate H (Mendelsohn-Dulmage: a needy-covering and an H-saturating matching combine)
    Mh = bip_max_matching(adj, sorted(H))
    if len(Mh) < len(H):
        lost = set(H) - set(Mh)
        for h in lost: named |= set(adj[h]) | ({o} if not adj[h] else set())
    feasible = not named
    return feasible, named


def certificate(P, Y):
    """None if the picks complete (by M^c); else {owner: named set of its closest triples}"""
    n = P.n; J = [g for g in range(P.m) if g not in Y]
    b = [P.val[i][Y[i]] for i in range(n)]
    wants = {(i, j) for i in range(n) for j in range(n) if i != j and P.val[i].get(Y[j], 0) > b[i]}
    frozen = set(j for (_, j) in wants)
    cert = {}
    for o in range(n):
        best = None; names = set()
        F1 = sorted(frozen - {o})
        for r in range(len(J) + 1):
            for H in itertools.combinations(J, r):
                for s in range(len(F1) + 1):
                    for Fs in itertools.combinations(F1, s):
                        ok, named = mc_eval(P, Y, o, set(H), set(Fs), wants, frozen)
                        if ok: return None
                        if best is None or len(named) < best: best = len(named); names = set(named)
                        elif len(named) == best: names |= named
        cert[o] = names
    return cert


def heads(P, Y):
    """heads x_0 of the repairing official chains (and whether additions / rings repair)"""
    B = [frozenset([g]) for g in Y]; hs = set(); kinds = set(); touched = []
    for nb in P.moves(B):
        if P.one_absorber(list(nb)) is None: continue
        ch = [i for i in range(P.n) if nb[i] != B[i]]
        touched.append(set(ch))
        if len(ch) == 1: kinds.add('addition'); hs.add(ch[0]); continue
        x0 = [i for i in ch if not (nb[i] & set(Y)) or (nb[i] - {Y[i]}) - set(Y)]
        # x_0 takes junk (H_0 within J and the last base); other chain agents take the previous base (+ junk)
        jk = [i for i in ch if any(g not in Y for g in nb[i])]
        kinds.add('chain/ring'); hs |= set(jk) if jk else set(ch)
    return hs, kinds, touched


def one(args):
    sets, vals, tag, rs_only = args
    P = R.Prof(sets, vals); nu, Ms = P.max_matchings(); C = collections.Counter(); bad = []
    if nu != P.n: return C, bad
    if rs_only:
        rs = {M: sum(P.ranks(M)) for M in Ms}; best = min(rs.values()); starts = [M for M in Ms if rs[M] == best]
    else:
        starts = Ms
    for Y in starts:
        Jy = [g for g in range(P.m) if g not in Y]
        if any(P.val[i].get(g, 0) > P.val[i][Y[i]] for i in range(P.n) for g in Jy):
            C['skipped: a junk good is wanted (no (G2))'] += 1; continue
        cert = certificate(P, Y); ab = P.one_absorber([[g] for g in Y]) is not None
        if (cert is None) != ab:
            C['MISMATCH with rklib one_absorber'] += 1; bad.append(('mismatch', tag, vals, Y)); continue
        if cert is None: C['picks complete'] += 1; continue
        if P.oc1(Y) != 'M': C['picks fail, OC1 fails too'] += 1; continue
        hs, kinds, touched = heads(P, Y)
        named_all = set.intersection(*cert.values()) if cert else set()
        named_any = set.union(*cert.values()) if cert else set()
        C['picks fail, one move repairs'] += 1
        C[('sizes |named for every owner|, |named for some owner| of n', len(named_all), len(named_any), P.n)] += 1
        C[('some head named for every owner', bool(hs & named_all))] += 1
        C[('some head named for some owner', bool(hs & named_any))] += 1
        C[('every head named for some owner', hs <= named_any)] += 1
        C[('some repairing move changes an agent named for every owner', any(t & named_all for t in touched))] += 1
        C[('some repairing move changes an agent named for some owner', any(t & named_any for t in touched))] += 1
        if not (hs & named_any) and len(bad) < 20: bad.append(('no head named', tag, vals, Y, sorted(hs), {o: sorted(v) for o, v in cert.items()}))
    return C, bad


if __name__ == '__main__':
    src = sys.argv[1]; limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
    print('$ python3 k4/vm_lp/mc_head.py', ' '.join(sys.argv[1:]), flush=True)
    jobs = []
    if src == 'export':
        J = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
        for h in J['hypergraphs']:
            seen = set()
            for st in h['starts']:
                k = json.dumps(st['vals'])
                if k in seen: continue
                seen.add(k); jobs.append((h['sets'], st['vals'], '%s#%d' % (h['list'], h['idx']), True))
    else:
        from vm_test import items_for
        jobs = [(s, v, nm, False) for nm, s, v, m in items_for(src)]
    if limit: jobs = jobs[:limit]
    print('profiles', len(jobs), flush=True)
    T = collections.Counter(); B = []
    with mp.Pool(4) as pool:
        for C, bad in pool.imap_unordered(one, jobs, chunksize=20):
            T.update(C); B += bad
    for k, v in sorted(T.items(), key=str): print(' ', v, k)
    for b in B[:8]: print('  ', b)
