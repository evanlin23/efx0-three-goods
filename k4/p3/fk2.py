"""Proposition FK2 (k4/p3.md section 6): forest chains along the jump walk, checked on hard p <= 2 starts.
Independent code (k4/p3/p3lib.py, oc1max.py, keep2.py); shares nothing with k4/oc1cert/ or k4/oc1max_multi/.

At a perfect start Y with strict values in which every good has at most two valuers:
  - w(i): the unique wanter of Y_i (frozen i); a root z (unfrozen) has at most one other valuer c(z), which ranks Y_z
    below its own pick;
  - the *jump walk* from an agent d_1: its need path P(d_1) = (d_1, ..., z_1), then d_2 = c(z_1) and P(d_2) up to z_2,
    then d_3 = c(z_2), ..., as long as the next tree is new; a *jump chain* JC(d_1, k; g_2..g_k; H_0) follows its first
    k segments: every agent of a need path other than its start takes its child's pick, d_{i+1} takes Y_{z_i} plus one
    junk good g_{i+1} (distinct, with v(Y_{z_i}) + v(g_{i+1}) > p_{d_{i+1}}), and d_1 takes an improving
    H_0 inside ((J - G) + {Y_{z_k}}) & R_{d_1}. (k = 1 with d_1 frozen is the canonical chain P(d_1).) It is a forest
    chain (k4/p3/fc2cert.py): junk is added only at the jumps, to the base of a root.
  - FK2, variant A (H = {}): (C_A) no agent frozen after the chain is threatened by W = (J - G) + {Y_{z_k}} at its pick
    value, and no entry d_i at its new base value (automatic unless d_k is a root); (N_A) no single-good holder other than d_1 is crowded by H_0. Variant B (H = {Y_{z_k}} kept out and given to
    z_k, needs Y_{z_k} not in H_0, z_k frozen at the picks or k >= 2 with z_k on a nontrivial path): (C_B) no agent
    frozen after the chain is threatened by J - G at its pick value; (N_B) no single-good holder other than d_1 and
    z_k is crowded by H_0. Either variant claims a one-absorber completion (owner d_1, Lemma 2* of k4/oc1_hall.md).
    It is checked here by SAT (k4/p3/oc1max.Checker.complete, models re-checked by the raw definition): a failure is
    counted as an FK2 VIOLATION.
  - Coverage: at how many hard starts some jump chain satisfies a variant's hypotheses; for the rest, whether some
    jump chain repairs anyway, and the kinds of the other repairing official moves.
    python3 k4/p3/fk2.py FILE [FILE ...]   (jsonl[.gz] of hard starts with 'sets', 'vals', 'picks'; or a CAN2/FC2
                                             certificate .json.gz, whose failure records are used)
"""
import sys, os, gzip, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker
from keep2 import analyse, chain, threatened, frozen_at


def subsets(xs, lo=0):
    return (h for r in range(lo, len(xs) + 1) for h in itertools.combinations(xs, r))


def starts(path):
    op = gzip.open if path.endswith('.gz') else open
    if path.endswith('.json.gz'):
        D = json.load(op(path, 'rt'))
        for rec in D['cores']:
            for f in rec.get('fails', []): yield rec['sets'], f['vals'], rec['m'], f['picks']
    else:
        for line in op(path, 'rt'):
            d = json.loads(line); r = d.get('inst', d); yield r['sets'], r['vals'], r['m'], d['picks']


def jump_walk(I, Y, w, F, d1):
    """the segments of the jump walk from d1: [P(d_1), P(d_2), ...], each a new tree"""
    segs = [chain(w, d1)]; seen = set(segs[0])
    while True:
        z = segs[-1][-1]
        c = [j for j in range(I.n) if j != z and Y[z] in I.R[j]]
        if not c: return segs
        P = chain(w, c[0])
        if set(P) & seen: return segs
        segs.append(P); seen |= set(P)


def jump_chains(I, Y, J, p, w, F):
    """every jump chain: (d1, segments, G, H0, bases)"""
    for d1 in range(I.n):
        segs = jump_walk(I, Y, w, F, d1)
        for k in range(1, len(segs) + 1):
            S = segs[:k]
            if k == 1 and len(S[0]) == 1: continue                    # d1 a root and no jump: not a chain
            zk = S[-1][-1]
            ents = [(S[i][0], Y[S[i - 1][-1]]) for i in range(1, k)]  # (d_{i+1}, Y_{z_i})
            choices = [[g for g in J if g in I.R[d] and I.val(d, (y, g)) > p[d]] for d, y in ents]
            for G in itertools.product(*choices):
                if len(set(G)) != len(G): continue
                pool = [g for g in J if g not in G and g in I.R[d1]] + ([Y[zk]] if Y[zk] in I.R[d1] else [])
                for H0 in subsets(pool, 1):
                    if I.val(d1, H0) <= p[d1]: continue
                    B = [frozenset([y]) for y in Y]
                    for P in S:
                        for i in range(1, len(P)): B[P[i]] = frozenset([Y[P[i - 1]]])
                    for (d, y), g in zip(ents, G): B[d] = frozenset([y, g])
                    B[d1] = frozenset(H0)
                    yield d1, S, G, H0, B


def crowded(I, B, u, H0):
    S = [g for g in H0 if g in I.R[u]]
    return len(S) >= 2 and I.val(u, S) > I.val(u, B[u])


def hypotheses(I, Y, J, p, d1, S, G, H0, B):
    """which FK2 variants apply: 'A', 'B' or neither. threatened() gets the whole set W (or J - G): the owner's bundle
    holds goods the tested agent does not value, and EFX0 lets it remove one of those."""
    zk = S[-1][-1]; n = I.n
    Fr = [q for q in range(n) if q != d1 and len(B[q]) == 1 and frozen_at(I, B, q)]
    holders = [u for u in range(n) if u != d1 and len(B[u]) == 1 and u not in Fr]
    JG = [g for g in J if g not in G]
    multi = [q for q in range(n) if q != d1 and len(B[q]) >= 2]              # the entries d_2, ..., d_k
    out = []
    W = JG + [Y[zk]]
    if all(not threatened(I, q, W, p[q]) for q in Fr) and \
            all(not threatened(I, q, W, I.val(q, B[q])) for q in multi) and \
            not any(crowded(I, B, u, H0) for u in holders):
        out.append('A')
    if Y[zk] not in H0 and len(S[-1]) >= 2 and \
            all(not threatened(I, q, JG, p[q]) for q in Fr) and \
            all(not threatened(I, q, JG, I.val(q, B[q])) for q in multi) and \
            not any(crowded(I, B, u, H0) for u in holders if u != zk):
        out.append('B')
    return out


if __name__ == '__main__':
    cnt = collections.Counter(); ex = {}
    print('$ python3 k4/p3/fk2.py ' + ' '.join(sys.argv[1:]))
    for path in sys.argv[1:]:
        for sets, vals, m, Y in starts(path):
            I = Inst(sets, vals, m); K = Checker(I)
            assert I.p() <= 2 and None not in Y
            base = tuple(frozenset([y]) for y in Y)
            if K.complete(base) is not None: K.close(); cnt['not hard (skipped)'] += 1; continue
            J, p, w, F, Dg, DT, EJ = analyse(I, list(Y))
            cnt['hard starts'] += 1
            applies = set(); jrep = set()
            for d1, S, G, H0, B in jump_chains(I, Y, J, p, w, F):
                k = len(S); cnt[f'jump chains with k = {k}'] += 1
                var = hypotheses(I, Y, J, p, d1, S, G, H0, B)
                ok = K.complete(tuple(B)) is not None
                if ok: jrep.add(k)
                for v in var:
                    cnt[f'FK2 {v} cases (k = {k})'] += 1
                    if not ok:
                        cnt['FK2 VIOLATION'] += 1
                        ex.setdefault('violation', (sets, vals, Y, d1, S, G, H0, v))
                if var: applies.add(k)
            if applies:
                cnt['FK2 applies, least k = %d' % min(applies)] += 1
            else:
                cnt['FK2 does not apply: ' + ('some jump chain repairs (least k = %d)' % min(jrep) if jrep else 'no jump chain repairs')] += 1
                if not jrep:
                    kinds = collections.Counter()
                    for st, tag in K.moves(base).items():
                        if K.complete(st) is not None: kinds[tag[2] + (' of %d' % tag[1] if tag[2] != 'addition' else '')] += 1
                    cnt['   ... repaired by: ' + (', '.join(sorted(kinds)) if kinds else 'NOTHING')] += 1
                    key = (I.n, I.m)
                    if 'nojump' not in ex or key < ex['nojump'][0]:
                        ex['nojump'] = (key, sets, vals, Y, sorted(Dg), sorted(DT), dict(kinds))
            K.close()
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
    for k, v in ex.items(): print(k, json.dumps(v))
