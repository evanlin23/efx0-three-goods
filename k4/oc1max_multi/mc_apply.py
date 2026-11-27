"""Lemma M^c applied to the open leaves SLOT and RING (k4/oc1max_multi.md §9): at every start whose first mechanism
(regimes.mechanism) is CAN-k (SLOT) or ED (RING), take every repairing move (collect.add_repairs) and every owner with
a completion, and record the least certificate of Lemma M^c it has: plain (F_s empty, no requirement from a multi-good
bundle: Lemma M), compensated (G1) (some needy agent's requirement comes from a fixed multi-good bundle), or a frozen slot
(F_s nonempty needed).  Counts over starts (the best certificate kind over the start's repairs).

    python3 k4/oc1max_multi/mc_apply.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, junk, frozen, holders
from regimes import mechanism
from mc import g2, threat_val, _match

KINDS = ['plain (Lemma M)', 'compensated (G1)', 'frozen slot']


def certificate(I, B, o):
    """the least kind of Lemma M^c certificate for an S^c completion of B with owner o (None if none)"""
    n = I.n; J = junk(I, B); F = set(frozen(I, B)); N1 = holders(I, B, o)
    F1 = [j for j in range(n) if j != o and len(B[j]) == 1 and j in F]
    Qm = [q for q in range(n) if q != o and len(B[q]) >= 2]; b = [I.V(i, B[i]) for i in range(n)]
    W = {j: [i for i in range(n) if i != j and I.v[i].get(B[j][0], 0) > b[i]] for j in F1}
    thQ = [max([threat_val(I, i, B[q]) for q in Qm if q != i] + [0]) for i in range(n)]
    best = None
    for r in range(len(F1) + 1):
        for Fs in itertools.combinations(F1, r):
            tau = list(thQ)
            for j in Fs:
                for i in W[j]: tau[i] = max(tau[i], I.v[i][B[j][0]])
            elig = set(N1) | set(Fs)
            for s in range(len(J) + 1):
                for H in itertools.combinations(J, s):
                    X = list(B[o]) + [g for g in J if g not in H]
                    if I.V(o, X) < tau[o]: continue
                    needy = [i for i in range(n) if i != o and (tau[i] > b[i] or I.threat(i, b[i], X))]
                    if any(i not in elig for i in needy): continue
                    adj = {h: [i for i in elig if i not in needy or (h in I.R[i] and b[i] + I.v[i][h] >= tau[i]
                                                                    and not I.threat(i, b[i] + I.v[i][h], X))] for h in H}
                    nu, cover = _match(adj, list(H), needy)
                    if not (cover and nu >= len(H)): continue
                    kind = 2 if Fs else (1 if any(thQ[i] > b[i] for i in needy) or thQ[o] > 0 and False else 0)
                    if best is None or kind < best: best = kind
                    if best == 0: return 0
    return best


if __name__ == '__main__':
    T = collections.Counter()
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            mech, _ = mechanism(I, rec)
            if mech not in ('CAN-k', 'ED'): continue
            leaf = 'SLOT' if mech == 'CAN-k' else 'RING'
            best = None
            for r in rec['repairs']:
                B = tuple(tuple(x) for x in r['base'])
                if not g2(I, B): continue
                for o in r['oa']:
                    c = certificate(I, B, o)
                    if c is not None and (best is None or c < best): best = c
            T[(leaf, 'starts')] += 1
            T[(leaf, 'best Lemma M^c certificate: ' + (KINDS[best] if best is not None else 'none (no S^c repair)'))] += 1
    print('$ python3 k4/oc1max_multi/mc_apply.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
