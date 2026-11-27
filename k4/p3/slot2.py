"""The SLOT residue of Proposition FK2 (k4/p3.md section 6): at the hard starts where every repairing jump chain leaves
a truly dangerous agent frozen and threatened (k4/p3/fk2_residue.py class {C:D_T}), what Lemma 2* (k4/oc1_hall.md
section 6) needs: the least kept-out set H and the holders that take its goods.

Lemma 2* at bases B with owner o, written from its statement (own code): N1 = the single-good holders other than o
that nobody else wants, Q = the other agents other than o, W = B_o + J'. Under (G1) and (G2) (checked here), an S*
completion with owner o exists iff some H inside J' satisfies (H1) (no q in Q is threatened by W - H at v_q(B_q)) and
has a system of distinct representatives in N1, h -> u admissible (u unexposed, i.e. not threatened by W - H at
v_u(B_u); or u values h and is not threatened by W - H at v_u(B_u) + v_u(h)), whose representatives include every
non-movable exposed holder (one that wants a good of B_o, or has |B_o & R_u| >= 2 and v_u(B_o & R_u) > v_u(B_u)).
This is a census of what the repairs use, not a test of Lemma 2* (which is refereed). For each SLOT start it also reports whether some repairing jump chain satisfies Lemma 2* with owner d_1 using only
agents of the chain as representatives. For each SLOT start and each repairing jump chain (owner d_1) it reports the least |H| with Lemma 2*, and for the
goods of that H: whether they belong to a frozen agent's danger, and which holders take them (unexposed or exposed;
an agent of the chain, a root off the chain, or an agent off the chain that was frozen at the picks).
    python3 k4/p3/slot2.py FILE [FILE ...]          (inputs as for k4/p3/fk2.py)
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker
from keep2 import analyse, threatened, frozen_at
from fk2 import starts, jump_chains, crowded, hypotheses, subsets
from fk2_residue import failures


def lemma2star(I, B, o, allowed=None):
    """(G1 and G2 hold, least H with an SDR or None, the SDR {h: u}, exposed, N1); allowed: if given, the agents that
    may represent goods of H"""
    n = I.n; V = I.val
    held = set().union(*B); Jp = [g for g in range(I.m) if g not in held]
    W = list(B[o]) + Jp
    N1 = [u for u in range(n) if u != o and len(B[u]) <= 1 and not frozen_at(I, B, u)]
    Q = [q for q in range(n) if q != o and q not in N1]
    g1 = all(not threatened(I, i, B[q], V(i, B[i])) for q in Q for i in range(n) if i != q)
    g2 = all(V(i, [g]) <= V(i, B[i]) for g in Jp for i in range(n))
    if not (g1 and g2): return False, None, None, None, N1
    for H in subsets(Jp):
        rest = [g for g in W if g not in H]
        if any(threatened(I, q, rest, V(q, B[q])) for q in Q): continue
        exp = {u for u in N1 if threatened(I, u, rest, V(u, B[u]))}
        nonmov = {u for u in exp if any(V(u, [g]) > V(u, B[u]) for g in B[o]) or
                  (len([g for g in B[o] if g in I.R[u]]) >= 2 and V(u, [g for g in B[o] if g in I.R[u]]) > V(u, B[u]))}
        adm = {h: [u for u in N1 if (allowed is None or u in allowed) and
                   (u not in exp or (h in I.R[u] and not threatened(I, u, rest, V(u, B[u]) + V(u, [h]))))]
               for h in H}
        for reps in itertools.product(*[adm[h] for h in H]):
            if len(set(reps)) == len(reps) and nonmov <= set(reps):
                return True, H, dict(zip(H, reps)), exp, N1
    return True, None, None, None, N1


if __name__ == '__main__':
    cnt = collections.Counter(); ex = {}
    print('$ python3 k4/p3/slot2.py ' + ' '.join(sys.argv[1:]))
    for path in sys.argv[1:]:
        for sets, vals, m, Y in starts(path):
            I = Inst(sets, vals, m); K = Checker(I)
            base = tuple(frozenset([y]) for y in Y)
            if K.complete(base) is not None: K.close(); continue
            J, p, w, F, Dg, DT, EJ = analyse(I, list(Y))
            chs = list(jump_chains(I, Y, J, p, w, F))
            if any(hypotheses(I, Y, J, p, *c) for c in chs): K.close(); continue
            fs = {}; rep = []
            for c in chs:
                if K.complete(tuple(c[4])) is None: continue
                rep.append(c)
                for var, f in failures(I, Y, J, p, DT, EJ, *c).items(): fs[f] = 1
            mins = [f for f in fs if not any(g < f for g in fs)]
            if mins != [frozenset({'C:D_T'})]: K.close(); continue
            cnt['SLOT starts'] += 1
            best = None; chain_only = None
            for d1, S, G, H0, B in rep:
                ok2, H2, _, _, _ = lemma2star(I, B, d1, allowed={a for P in S for a in P})
                if ok2 and H2 is not None and (chain_only is None or len(S) < chain_only): chain_only = len(S)
                ok, H, sdr, exp, N1 = lemma2star(I, B, d1)
                cnt['repairing jump chains'] += 1
                if not ok: cnt['   (G1) or (G2) fails'] += 1; continue
                if H is None: cnt['   Lemma 2* fails for owner d_1 (another owner or shape completes)'] += 1; continue
                cnt['   Lemma 2* holds for owner d_1'] += 1
                chain = {a for P in S for a in P}
                kinds = []
                for h, u in sorted(sdr.items()):
                    fz = [q for q in range(I.n) if q != d1 and len(B[q]) == 1 and frozen_at(I, B, q) and h in I.R[q]]
                    kinds.append(('danger of a frozen agent' if fz else 'other') + ' -> ' +
                                 ('exposed' if u in exp else 'unexposed') + ' ' +
                                 ('chain agent' if u in chain else 'off-chain root' if u not in F else 'off-chain, frozen at the picks') +
                                 (' valuing it' if h in I.R[u] else ' not valuing it'))
                key = (len(H), len(S), sorted(kinds))
                if best is None or key < best: best = key
            if best is None: cnt['SLOT start: no repairing jump chain satisfies Lemma 2* with owner d_1'] += 1; K.close(); continue
            cnt[f'least |H| = {best[0]}'] += 1
            cnt['chain agents alone suffice as slot holders: ' + ('yes, least k = %d' % chain_only if chain_only else 'no')] += 1
            for kd in best[2]: cnt['   slot good: ' + kd] += 1
            lab = f'|H| = {best[0]}'
            if lab not in ex or (I.n, I.m) < ex[lab][0]: ex[lab] = ((I.n, I.m), {'sets': sets, 'vals': vals, 'picks': Y})
            K.close()
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
    for k, v in sorted(ex.items()): print('smallest with', k, json.dumps(v[1]))
