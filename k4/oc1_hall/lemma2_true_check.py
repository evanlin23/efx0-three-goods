"""A real test of Lemma 2 (k4/oc1_hall.md §4), both directions, with Theorem DT's moves exercised.
At every state (picks, and every state one improving chain reaches) and every owner o for which (G1), (G2), (G5'),
(H3) hold:
  - enumerate H over subsets of J meeting (H1) only (the demands of the non-holders Q); compute theta(H) (exposed
    holders) and nu(H) (maximum matching of exposed holders to goods of H that make them safe);
  - COUNT := some such H has |H| + theta(H) - nu(H) <= |N_1|;
  - for the least such H: run ohlib.lemma2_build with phi = the nu-matching (the other exposed holders do DT's moves)
    and check the result with the raw EFX0 definition and the S* shape;
  - compare COUNT with the raw S* enumeration ohlib.shaped_completion (owner o).
Counts how often DT's moves were actually used.
STAR=1: Lemma 2* instead: only (G1), (G2) are assumed; exposed holders that are not movable (they want a good of
B_o, or have a danger set inside B_o) must be in the matching; the movable ones may do DT's moves.

    python3 k4/oc1_hall/lemma2_true_check.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import (Inst, picks, base_of_picks, bundles_of, frozen_set, threatened, shaped_completion, efx0,
                   lemma2_build)
from lemma2_check import hypotheses
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True


def max_matching(edges, left):
    """edges: u -> list of goods; maximum matching (augmenting paths)"""
    match = {}   # good -> u
    def aug(u, seen):
        for g in edges[u]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = u; return True
        return False
    for u in left: aug(u, set())
    return {u: g for g, u in match.items()}


STAR = os.environ.get('STAR', '0') == '1'


def hypotheses_star(I, base, o):
    from ohlib import wants_good
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]; F = set(frozen_set(I, base))
    pv = [I.val(i, B[i]) for i in range(I.n)]
    N1 = [j for j in range(I.n) if j != o and len(B[j]) <= 1 and j not in F]
    Q = [j for j in range(I.n) if j != o and j not in N1]
    if any(threatened(I, i, pv[i], B[q]) for q in Q for i in range(I.n) if i != q): return None   # (G1)
    if any(wants_good(I, B, i, g) for g in J for i in range(I.n)): return None                    # (G2)
    return N1, Q


def nonmovable(I, B, o, u, pv):
    from ohlib import wants_good
    if any(wants_good(I, B, u, g) for g in B[o]): return True
    Bo = [g for g in B[o] if g in I.R[u]]
    return len(Bo) >= 2 and I.val(u, Bo) > pv[u]


def count_test(I, base, o, N1, Q):
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]
    pv = [I.val(i, B[i]) for i in range(I.n)]
    best = None
    for r in range(0, len(J) + 1):
        for H in itertools.combinations(J, r):
            Wh = B[o] + [g for g in J if g not in H]
            if any(threatened(I, q, pv[q], Wh) for q in Q): continue              # (H1)
            exposed = [u for u in N1 if threatened(I, u, pv[u], Wh)]
            edges = {u: [g for g in H if g in I.R[u] and not threatened(I, u, pv[u] + I.v[u][g], Wh)] for u in exposed}
            if STAR:
                nm = [u for u in exposed if nonmovable(I, B, o, u, pv)]
                phi = None
                for gs in itertools.permutations(H, len(nm)) if len(nm) <= len(H) else []:
                    if not all(g in edges[u] for u, g in zip(nm, gs)): continue
                    rest = [u for u in exposed if u not in nm]
                    sub = max_matching({u: [g for g in edges[u] if g not in gs] for u in rest}, rest)
                    cand = dict(zip(nm, gs)); cand.update(sub)
                    if phi is None or len(cand) > len(phi): phi = cand
                if phi is None: continue
            else:
                phi = max_matching(edges, exposed)
            if len(H) + len(exposed) - len(phi) <= len(N1):
                return H, phi, exposed
    return None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/lemma2_true_check.py', *sys.argv[1:], '(STAR=%d)' % STAR, flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 4: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y)
            for tag, b in [('picks', base)] + [('after a chain', b2) for b2 in DF.moves(E, base)]:
                for o in range(n):
                    hyp = hypotheses_star(I, b, o) if STAR else hypotheses(I, b, o)
                    if hyp is None: continue
                    N1, Q = hyp
                    C[tag + ': owner tests'] += 1
                    res = count_test(I, b, o, N1, Q)
                    ex = shaped_completion(I, b, o, N1)
                    if bool(res) != ex:
                        C[tag + ': COUNT/RAW MISMATCH'] += 1
                        print('MISMATCH', tag, name, json.dumps((sets, vals)), b, o, bool(res), ex, flush=True)
                    if not res: continue
                    H, phi, exposed = res
                    movers = [u for u in exposed if u not in phi]
                    C[tag + ': count holds'] += 1
                    C[tag + ': count holds, DT moves needed (unmatched exposed holders)'] += bool(movers)
                    X = lemma2_build(I, b, o, list(H), phi, N1)
                    B = bundles_of(I, b); Jset = set(g for g in range(m) if b[g] < 0)
                    ok = X is not None and efx0(I, X) and all(set(bb) <= set(x) for bb, x in zip(B, X))
                    if ok:
                        for j in range(n):
                            extra = [g for g in X[j] if g in Jset]
                            if j != o and (len(extra) > 1 or (extra and j not in N1)): ok = False
                    if not ok:
                        C[tag + ': CONSTRUCTION FAILS'] += 1
                        print('CONSTRUCTION FAILS', tag, name, json.dumps((sets, vals)), b, o, H, phi, X, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
