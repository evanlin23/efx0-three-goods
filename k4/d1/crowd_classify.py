"""Classify failing CROWD-only chains (k4/d1.md §2).  Reads hunt/census JSONL records and, for every chain without
HEAD whose minimal H0 crowds and fails, prints / counts:
  shape   the family M of minimal improving subsets of P_k = Pi & R_k (S1: a singleton exists; 2a: P_k = {b,c},
          M = {bc}; 2b: M = {bcd}; 2c: M = one pair, |P_k| = 3; 2d: two pairs; 2e: three pairs);
  yz      whether Y_{x_t} (the head's pick, released into the pool) lies in P_k, and in H0;
  who     crowded holders: 'head' (x_t) or 'off' (off the chain, unfrozen at the picks);
  why     per crowded holder: Q_u = Pi & R_u, whether a compensation good exists;
  fix     which other minimal H0' on the same chain repairs (with its crowded holders).

    python3 k4/d1/crowd_classify.py FILE.jsonl [...]
"""
import sys, os, json, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from d1lib import Inst, Start, pool, minimal_improving, apply_chain, obstacles, threat


def shape(S, k, Pi):
    I = S.I
    Pk = [g for g in Pi if g in I.R[k]]
    M = minimal_improving(S, k, Pi)
    sizes = sorted(len(H) for H in M)
    if 1 in sizes: return 'S1', Pk, M
    if len(Pk) == 2: return '2a', Pk, M
    if sizes == [3]: return '2b', Pk, M
    return {1: '2c', 2: '2d', 3: '2e'}[len(M)], Pk, M


def main(files):
    C = collections.Counter(); seen = set(); shown = collections.Counter()
    for fn in files:
        for line in open(fn):
            rec = json.loads(line)
            key = json.dumps((rec['sets'], rec['vals'], rec['picks']))
            if key in seen: continue
            seen.add(key)
            I = Inst(rec['sets'], rec['vals'], rec['m']); S = Start(I, tuple(rec['picks'])); k = rec['k']
            rows = rec['rows']
            for r in rows:
                if not r['crowded'] or r['head'] or r['ok']: continue
                path = tuple(r['path']); z = path[-1]; Pi = pool(S, path); H0 = frozenset(r['H0'])
                sh, Pk, M = shape(S, k, Pi)
                yz = S.Y[z]
                tagyz = 'Yz notin Pk' if yz not in Pk else ('Yz in H0' if yz in H0 else 'Yz in Pk-H0')
                B2 = apply_chain(S, path, H0)
                who = []
                for u in r['crowded']:
                    Q = sorted(g for g in Pi if g in I.R[u])
                    comp = [e for e in Q if e not in H0]
                    who.append(('head' if u == z else 'off', len(Q), len(H0 & set(Q)), len(comp)))
                fixes = [q for q in rows if q['path'] == r['path'] and q['ok']]
                fixdesc = sorted(('crowds' if q['crowded'] else 'free') for q in fixes)
                k_ = (sh, tagyz, tuple(sorted(who)), tuple(fixdesc))
                C[k_] += 1
                if shown[k_] < 2:
                    shown[k_] += 1
                    print('EX', k_, json.dumps((rec['sets'], rec['vals'])), 'picks', rec['picks'], 'k', k, 'chain', r['path'],
                          'H0', r['H0'], 'Pk', Pk, 'M', [sorted(h) for h in M], 'fix', [(q['H0'], q['crowded']) for q in fixes])
    print('distinct starts', len(seen))
    for k_, c in sorted(C.items(), key=lambda t: -t[1]): print(c, k_)


if __name__ == '__main__':
    main(sys.argv[1:])
