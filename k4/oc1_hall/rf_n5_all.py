"""Conjecture RF at n = 5 on the certifier's complete failure exports: OC1 at EVERY RF start, by class and first step
(k4/oc1_hall.md §24.10).

Input as for rf_n5.py (the exports two_move_starts_n5_partial6 / sel2 of compute/k4-oc1max-cert, or a stored-failure
summary).  For every failing order o and every receiver u, Y' = SD(u, o - u); distinct (profile, Y') pairs once.

If Y' leaves an agent pickless (not a maximum matching, while the cores have nu = n), Conjecture RF as stated on main
(k4/sdc.md: "some order with u first gives a maximum matching; every order with u first that gives one satisfies OC1")
is tested directly: all (n-1)! orders with u first, their distinct maximum-matching pick vectors, raw OC1 at each
(k4/sdc/oc1_mc2_rand.Inst.check).

Otherwise the first repair found, in this order (completions are one-absorber, raw EFX0, ohlib.absorb_brute):
  P    the picks Y' complete;
  K    |D_T'| >= 1: a canonical chain from some k in D_T' (each agent wanting its predecessor's pick) where k takes an
       improving H0 inside S (the junk valued by every agent of D_T', when |D_T'| >= 2) or inside its own junk (when
       |D_T'| = 1), then a completion;
  T    girth's trade: a receiver r and a pick-dangerous p, "p takes {Y'_r, j}, r takes Y'_p" (both improve), then a
       completion;
  RAW  any official move of the raw checker (Inst.moves), then a completion (Inst.one_absorber);
  FAIL none: OC1 fails at Y' (printed).
For DEMOTE-2 starts repaired by the chain "k takes S, d takes Y'_k", it is also recorded whether the state after it has
an S^c completion (Lemma M^c's shape: multi-good holders other than the owner take nothing; by Lemma M^c this is
equivalent to (C1)-(C3) for some (H, F_s), since (G2) holds there, k4/oc1_hall.md §24.10).

    python3 k4/oc1_hall/rf_n5_all.py FILE [FILE ...]
"""
import sys, os, json, gzip, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened, base_of_picks, absorb_brute, bundles_of, efx0
from greedy_rules import apply_chain, canonical_paths
import rf_b_facts as RB
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def sc_exists(I, base):
    """an S^c-shaped completion: owner o takes the rest; every other agent with at most one base good takes at most one
    free good; agents with two or more base goods (other than o) take nothing; raw EFX0"""
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]
    for o in range(I.n):
        others = [i for i in range(I.n) if i != o and len(B[i]) <= 1]
        for k in range(0, min(len(J), len(others)) + 1):
            for K in itertools.combinations(J, k):
                L = [g for g in J if g not in K]
                for who in itertools.permutations(others, k):
                    X = [list(b) for b in B]
                    for g, a in zip(K, who): X[a].append(g)
                    X[o] += L
                    if efx0(I, X): return True
    return False


def improving_subsets(I, k, pk, ground):
    return [H for r in range(1, len(ground) + 1) for H in itertools.combinations(ground, r) if I.val(k, H) > pk]


def classify(I, sets, vals, Y, u, Y2, C, bad, tag):
    P = Picks(I, Y2)
    U2 = [i for i in range(I.n) if i not in P.F]
    DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
    cls = '(%d, %d)' % (len(U2), len(DT))
    C[tag + 'class %s' % cls] += 1
    base = base_of_picks(I, Y2)
    if absorb_brute(I, base, witness=True):
        C[tag + 'class %s: P (picks complete)' % cls] += 1; return
    if DT:
        if len(DT) >= 2:
            S = [g for g in P.J if all(g in I.R[k] for k in DT)]
        found = None
        for k in DT:
            ground = S if len(DT) >= 2 else [g for g in P.J if g in I.R[k]]
            subs = [H for H in improving_subsets(I, k, P.pv[k], [g for g in ground if g in I.R[k]])]
            subs.sort(key=len)
            for path in canonical_paths(I, P, k):
                for H in subs:
                    b2 = apply_chain(I, P, base, path, H)
                    if absorb_brute(I, b2, witness=True):
                        found = (k, path, H); break
                if found: break
            if found: break
        if found:
            k, path, H = found
            d = U2[0] if len(U2) == 1 else None
            kind = 'k -> d' if (len(path) == 2 and path[-1] == d) else ('length %d, head %s' % (len(path) - 1, 'a receiver' if path[-1] in U2 else 'frozen'))
            C[tag + 'class %s: K (chain from k in D_T\', H0 in %s; %s)' % (cls, 'S' if len(DT) >= 2 else 'its junk', kind)] += 1
            if len(U2) == 1 and len(DT) == 2:
                # the chain k -> d with H0 = S, if official: does an S^c completion exist after it?
                for k2 in DT:
                    if I.v[d].get(Y2[k2], 0) > P.pv[d] and I.val(k2, S) > P.pv[k2]:
                        b3 = apply_chain(I, P, base, (k2, d), tuple(S))
                        C[tag + 'DEMOTE-2: after "k takes S, d takes Y\'_k" (official): S^c completion %s' % sc_exists(I, b3)] += 1
                        break
            return
    # girth's trade (T): receiver r, pick-dangerous p (dangerous, not truly), p takes {Y'_r, j}, r takes Y'_p
    pdang = [p for p in P.D if p not in DT]
    for r in U2:
        for p in pdang:
            if not I.v[r].get(Y2[p], 0) > P.pv[r]: continue
            for j in P.Jv[p]:
                if I.v[p].get(Y2[r], 0) + I.v[p][j] <= P.pv[p]: continue
                b2 = list(base); b2[Y2[r]] = p; b2[j] = p; b2[Y2[p]] = r
                if absorb_brute(I, tuple(b2), witness=True):
                    C[tag + 'class %s: T (a receiver trades with a pick-dangerous agent)' % cls] += 1; return
    R = RawInst(sets, vals); res = R.check(Y2)
    C[tag + 'class %s: RAW %s' % (cls, res)] += 1
    if res == 'OC1 fails' and len(bad) < 5:
        bad.append({'sets': sets, 'vals': vals, 'Y': list(Y), 'u': u, "Y'": list(Y2)})


def job(task):
    sets, starts, tag = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); bad = []
    seen = set(); seen_u = set()
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks'])
        P0 = Picks(I, Y); U0 = [i for i in range(I.n) if i not in P0.F and Y[i] is not None]
        orders = st['orders'] if 'orders' in st else [o for o in itertools.permutations(range(I.n)) if picks(I, o) == Y]
        vk = json.dumps(vals)
        for o, u in itertools.product(orders, U0):
            Y2 = picks(I, [u] + [x for x in o if x != u])
            if (vk, Y2) in seen: continue
            seen.add((vk, Y2)); C['RF starts'] += 1
            if None not in Y2:
                classify(I, sets, vals, Y, u, Y2, C, bad, '')
                continue
            C['RF starts with a pickless agent'] += 1
            if (vk, u) in seen_u: continue
            seen_u.add((vk, u))
            # Conjecture RF as on main: some order with u first gives a maximum matching, and every one that does
            # satisfies OC1
            vecs = set(picks(I, (u,) + q) for q in itertools.permutations([x for x in range(I.n) if x != u]))
            mx = [v for v in vecs if None not in v]
            C['pickless rotation: (start, u) pairs'] += 1
            C['pickless rotation: some u-first order gives a maximum matching: %s' % bool(mx)] += 1
            R = RawInst(sets, vals)
            for v in mx:
                res = R.check(v)
                C['pickless rotation: u-first maximum-matching pick vectors: OC1 %s' % res] += 1
                if res == 'OC1 fails' and len(bad) < 5: bad.append({'sets': sets, 'vals': vals, 'Y': list(Y), 'u': u, "u-first max picks": list(v)})
            if not mx and len(bad) < 5: bad.append({'sets': sets, 'vals': vals, 'Y': list(Y), 'u': u, 'no u-first maximum matching': True})
    return tag, C, bad


def tasks_of(path):
    if path.endswith('.jsonl.gz'):
        for line in gzip.open(path):
            r = json.loads(line)
            if r.get('oc1_fails'):
                yield (r['sets'], [{'vals': f['vals'], 'picks': f['picks']} for f in r['oc1_fails']], 'stored')
        return
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        groups = collections.defaultdict(list)          # one profile's starts stay in one task: (profile, Y') once
        for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)
        chunk = []
        for g in groups.values():
            chunk += g
            if len(chunk) >= 2000: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx'])); chunk = []
        if chunk: yield (hg['sets'], chunk, '%s#%d' % (hg['list'], hg['idx']))


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_n5_all.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    T = collections.Counter(); shown = 0
    tasks = [t for p in sys.argv[1:] for t in tasks_of(p)]
    with mp.Pool() as pool:
        for tag, C, bad in pool.imap_unordered(job, tasks):
            T.update(C)
            for b in bad:
                if shown < 20: shown += 1; print('RF VIOLATION OR OPEN CASE:', json.dumps(b), flush=True)
    for k in sorted(T): print(k, T[k])
