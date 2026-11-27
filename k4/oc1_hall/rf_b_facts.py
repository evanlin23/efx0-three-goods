"""Residue B of Conjecture RF (k4/oc1_hall.md §24.8): which explicit repairs work at the 43,520 B starts of the
certifier's complete n = 4 export, and the facts a written proof would use.

B start: RF picks Y' with one receiver d (= the RF path's end, w = d), two truly dangerous agents k1, k2.

Repairs tested (raw EFX0, ohlib.efx0):
  PICKS-d   one-absorber completion of Y' with owner d; every such completion is listed by shape (who takes a single
            junk good: a D_T agent, u, another agent).
  FULL(k,T) the chain k -> d with d taking everything else: k gets T (a minimal improving set of junk), d gets
            {Y'_k, Y'_d} together with J' minus T, every other agent keeps its pick.  Needs d to want Y'_k.
  FULL(k,S) the same with T = S, the two junk goods k1 and k2 share.

Facts recorded: d wants Y'_u; d wants Y'_k for which k; |J'|; the junk each D_T agent values; whether u values junk.

Lemma RF-B (k4/oc1_hall.md §24.8): its hypotheses (B1)-(B5) are checked one by one at every B start, for each D_T agent
k whose pick d wants and the other D_T agent does not (k<-d; the per-hypothesis counts are for one that meets them all,
if any); its conclusion (the FULL(k, S) allocation) is checked
again with the raw checker's own EFX0 test (k4/sdc/oc1_mc2_rand.Inst.efx0), and the chain is confirmed to be an
official move of Inst.moves at the n = 5 starts and at every 40th n = 4 start (move enumeration is slow).

Also every distinct RF start of the 24 stored n = 5 OC1'^max failures (results/k4_oc1max/oc1prime_cex_n5_partial.jsonl,
all orders giving the failing picks).  D_T agents are labelled by who wants their pick: k<-k' (the other D_T agent),
k<-d.

    python3 k4/oc1_hall/rf_b_facts.py
"""
import sys, os, json, gzip, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, threatened, efx0
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def lemma_rfb(I, Y2, P, d, k, S, C, T_, official=False):
    """hypotheses (B1)-(B5) of Lemma RF-B and its conclusion, at picks Y2 with absorber d, agent k and junk set S"""
    n = I.n; J = P.J; Z = [Y2[k], Y2[d]] + [g for g in J if g not in S]
    wants = lambda i, g: I.v[i].get(g, 0) > P.pv[i]
    h = {}
    h['B1 |S| = 2 and v_k(S) > p_k'] = len(S) == 2 and I.val(k, S) > P.pv[k]
    h['B2 d wants Y\'_k, nobody else does'] = wants(d, Y2[k]) and all(not wants(i, Y2[k]) for i in range(n) if i not in (k, d))
    h['B3 d unfrozen'] = all(not wants(i, Y2[d]) for i in range(n) if i != d)
    h['B4 k values no good of Z but Y\'_k'] = all(g == Y2[k] or g not in I.R[k] for g in Z)
    many = [i for i in range(n) if i not in (k, d) and len([g for g in Z if g in I.R[i]]) >= 2]
    vz = lambda i: sum(I.v[i].get(g, 0) for g in Z) - min(I.v[i].get(g, 0) for g in Z)
    h['B5 every i valuing >= 2 goods of Z: v_i(Z) - min <= p_i'] = all(vz(i) <= P.pv[i] for i in many)
    for key, val in h.items(): C[T_ + 'Lemma RF-B hypothesis %s: %s' % (key, val)] += 1
    C[T_ + 'Lemma RF-B: agents valuing >= 2 goods of Z (besides k, d): %d' % len(many)] += 1
    X = [[y] for y in Y2]; X[k] = list(S); X[d] = list(Z)
    R = RawInst(I.sets, I.vals)
    concl = efx0(I, X) and R.efx0(X)
    C[T_ + 'Lemma RF-B: all hypotheses hold: %s; FULL(k, S) EFX0 (both checkers): %s' % (all(h.values()), concl)] += 1
    if official:
        base = [[y] for y in Y2]; mv = list(base); mv = [list(b) for b in base]; mv[k] = list(S); mv[d] = [Y2[k]]
        key = tuple(tuple(sorted(b)) for b in mv)
        C[T_ + 'Lemma RF-B: chain (k takes S, d takes Y\'_k) is an official move of Inst.moves: %s' % (key in R.moves(base))] += 1
    return all(h.values()), concl


def minimal_improving(I, k, pk, ground):
    imp = [H for r in range(1, len(ground) + 1) for H in itertools.combinations(ground, r) if I.val(k, H) > pk]
    return [H for H in imp if not any(set(K) < set(H) for K in imp)]


def owner_completions(I, Y, J, o):
    """every one-absorber completion of the picks Y with owner o: (dict agent -> single junk good, owner's junk)"""
    others = [i for i in range(I.n) if i != o]; out = []
    for k in range(0, min(len(J), len(others)) + 1):
        for K in itertools.combinations(J, k):
            L = [g for g in J if g not in K]
            for who in itertools.permutations(others, k):
                X = [[y] for y in Y]
                for g, a in zip(K, who): X[a].append(g)
                X[o] += L
                if efx0(I, X): out.append((dict(zip(who, K)), tuple(L)))
    return out


def full(I, Y, J, k, d, T):
    X = [[y] for y in Y]
    X[k] = list(T); X[d] = [Y[k], Y[d]] + [g for g in J if g not in T]
    return efx0(I, X)


def lab(I, P, Y2, k, kk, d):
    """a D_T agent k, labelled by who wants its pick: the other D_T agent kk, and d"""
    return 'k%s%s' % ('<-k\'' if I.v[kk].get(Y2[k], 0) > P.pv[kk] else '', '<-d' if I.v[d].get(Y2[k], 0) > P.pv[d] else '')


def analyse(I, Y, Y2, u, C, ex, tag):
    P0 = Picks(I, Y); P = Picks(I, Y2)
    DT0 = [k for k in P0.D if threatened(I, k, P0.pv[k], P0.J)]
    U2 = [i for i in range(I.n) if i not in P.F and Y2[i] is not None]
    DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
    C[tag + 'RF starts by (|U\'|, |D_T\'|) = (%d, %d)' % (len(U2), len(DT))] += 1
    if len(U2) != 1 or len(DT) != 2: return
    d = U2[0]; C[tag + 'B starts'] += 1; J = P.J; T_ = tag
    k1, k2 = DT; S = tuple(g for g in J if g in I.R[k1] and g in I.R[k2])
    other = {k1: k2, k2: k1}
    C[T_ + 'fact: d wants Y\'_u: %s' % (I.v[d].get(Y2[u], 0) > P.pv[d])] += 1
    C[T_ + 'fact: D_T\' = D_T (the truly dangerous agents of Y): %s' % (sorted(DT) == sorted(DT0))] += 1
    C[T_ + 'fact: u in D_T\': %s' % (u in DT)] += 1
    C[T_ + 'fact: |J\'| = %d, |S| = %d' % (len(J), len(S))] += 1
    C[T_ + 'fact: junk valued by (k1, k2) = %s' % str(sorted((len(P.Jv[k1]), len(P.Jv[k2]))))] += 1
    C[T_ + 'fact: d values %d junk goods' % len(P.Jv[d])] += 1
    C[T_ + 'fact: labels of the D_T pair = %s' % str(sorted(lab(I, P, Y2, k, other[k], d) for k in DT))] += 1
    wk = [k for k in DT if I.v[d].get(Y2[k], 0) > P.pv[d]]
    kd = [k for k in DT if lab(I, P, Y2, k, other[k], d) == 'k<-d']
    C[T_ + 'fact: number of D_T agents labelled k<-d = %d' % len(kd)] += 1
    C['_count ' + T_] += 1
    res = []
    for k in kd:
        C2 = collections.Counter()
        res.append((k, lemma_rfb(I, Y2, P, d, k, S, C2, T_, official=(T_.startswith('n=5') or C['_count ' + T_] % 40 == 0)), C2))
    good = [x for x in res if x[1][0]]
    C[T_ + 'Lemma RF-B: candidates k (labelled k<-d) meeting all of (B1)-(B5): %d of %d' % (len(good), len(kd))] += 1
    C.update(good[0][2] if good else res[0][2])          # the per-hypothesis counts for the chosen k
    for k, (hyp, concl), _ in res:
        C[T_ + 'Lemma RF-B per candidate: hypotheses %s, FULL(k, S) EFX0 %s' % (hyp, concl)] += 1
    C[T_ + 'fact: S improving for (k1, k2): %s' % str([I.val(k, S) > P.pv[k] for k in DT])] += 1
    comp = owner_completions(I, Y2, J, d)
    if comp:
        C[T_ + 'PICKS-d holds'] += 1
        shapes = set(); takers = set()
        for sg, L in comp:
            roles = tuple(sorted(('D_T' if a in DT else ('u' if a == u else 'other')) + (':S' if g in S else ':notS') for a, g in sg.items()))
            shapes.add((roles, len(L)))
            for a, g in sg.items():
                if a in DT and g in S: takers.add(lab(I, P, Y2, a, other[a], d))
        for sh in shapes: C[T_ + '  PICKS-d shape (singles %s; d takes %d junk)' % sh] += 1
        C[T_ + '  PICKS-d: D_T agents that take a good of S in some completion: %s' % sorted(takers)] += 1
        # the simplest shape: one D_T agent takes one good of S, d takes the rest
        one = sorted(set(lab(I, P, Y2, a, other[a], d) for sg, L in comp if len(sg) == 1 for a, g in sg.items() if a in DT and g in S))
        C[T_ + '  PICKS-d: one single (a D_T agent, a good of S), d the rest; which agent: %s' % one] += 1
        for k in DT:
            if full(I, Y2, J, k, d, S): C[T_ + '  PICKS-d holds and FULL(%s, S) is EFX0 too (d wants Y\'_k: %s)' % (lab(I, P, Y2, k, other[k], d), k in wk)] += 1
        return
    C[T_ + 'PICKS-d fails'] += 1
    ok = collections.Counter(); who = set()
    for k in wk:
        for T in minimal_improving(I, k, P.pv[k], [g for g in J if g in I.R[k]]):
            if full(I, Y2, J, k, d, T): ok['FULL(k, T) some minimal T'] += 1; ok['FULL, T = S' if set(T) == set(S) else 'FULL, T != S'] += 1
        if full(I, Y2, J, k, d, S): ok['FULL(k, S)'] += 1; who.add(lab(I, P, Y2, k, other[k], d))
    for r in ('FULL(k, T) some minimal T', 'FULL(k, S)', 'FULL, T = S', 'FULL, T != S'):
        C[T_ + '  PICKS-d fails: %s works: %s' % (r, bool(ok[r]))] += 1
    C[T_ + '  PICKS-d fails: FULL(k, S) works for k = %s' % sorted(who)] += 1
    if not ok['FULL(k, T) some minimal T'] and T_ + 'nofull' not in ex:
        ex[T_ + 'nofull'] = (I.sets, I.vals, Y2, d, DT)


if __name__ == '__main__':
    data = json.load(gzip.open(os.path.join(_paths.ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    C = collections.Counter(); ex = {}
    print('$ python3 k4/oc1_hall/rf_b_facts.py', flush=True)
    for hg in data['hypergraphs']:
        sets = hg['sets']; m = 1 + max(max(s) for s in sets); seen = set()
        for st in hg['starts']:
            vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]
            for o in st['orders']:
                rf = [u] + [x for x in o if x != u]; Y2 = picks(I, rf)
                if (json.dumps(vals), Y2) in seen: continue
                seen.add((json.dumps(vals), Y2))
                analyse(I, Y, Y2, u, C, ex, 'n=4 ')
    # n = 5: every order of the 24 stored OC1'^max failures that gives the failing picks (the receiver is unique there)
    for line in open(os.path.join(_paths.ROOT, 'results', 'k4_oc1max', 'oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line); sets, vals = r['sets'], r['vals']; m = 1 + max(max(s) for s in sets)
        I = Inst(sets, vals, m); Y = tuple(r['picks']); P0 = Picks(I, Y)
        U0 = [i for i in range(I.n) if i not in P0.F and Y[i] is not None]
        C['n=5 failures'] += 1; C['n=5 failures with one receiver: %s' % (len(U0) == 1)] += 1
        u = U0[0]; seen = set()
        for o in itertools.permutations(range(I.n)):
            if picks(I, o) != Y: continue
            C['n=5 failing orders'] += 1
            Y2 = picks(I, [u] + [x for x in o if x != u])
            if Y2 in seen: continue
            seen.add(Y2); analyse(I, Y, Y2, u, C, ex, 'n=5 ')
    for k_ in sorted(C): print(k_, C[k_])
    for k_, v in ex.items(): print('example', k_, json.dumps(v))
