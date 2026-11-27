#!/usr/bin/env python3
"""Lemma REC-EXISTS (referee): at a maximum-matching SD start with no receiver, a pickless agent exists and no agent values
a junk good, so the picks complete (junk to a pickless agent) and OC1 holds. Hence every OC1-failing MM start has a
receiver. Checked here: do OC1-failing maximum-matching SD starts without any receiver exist? (Conjecture RF's amended statement, "for every
receiver u of a failing start ...", is vacuous at such a start, while RF => OC1^{exists max} and Proposition RF-K need
a receiver.) Random strict connected instances, every agent valuing 3 or 4 goods, all orders; receivers in the
RF sense (a pick holder whose pick no other agent prefers to its own; a pickless agent prefers any good it values).
OC1 by k4/referee/rkmax_ref.oc1 (additions, chains, rings; one-absorber completion). Own code.
    python3 norecv_ref.py N SEED NMIN NMAX"""
import sys, random, itertools, json
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import sd, nu
from rkmax_ref import oc1
from rfmin_ref import rand_strict, recv_gen

def connected(v):
    n = len(v); m = len(v[0]); seen = {0}; st = [0]
    while st:
        i = st.pop()
        for j in range(n):
            if j not in seen and any(v[i][g] > 0 and v[j][g] > 0 for g in range(m)):
                seen.add(j); st.append(j)
    return len(seen) == n

def main(N, seed, nmin, nmax):
    rng = random.Random(seed); c = Counter(); ex = None
    for t in range(N):
        n = rng.randint(nmin, nmax); m = rng.randint(max(4, n - 1), n + 3)
        v = rand_strict(rng, n, m, 3, 4)
        if not connected(v) or not all(any(v[i][g] for i in range(n)) for g in range(m)):
            continue
        c['instances'] += 1
        N0 = nu(v); seen = set()
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(v, list(o)))
            if Y in seen or sum(1 for y in Y if y is not None) != N0:
                continue
            seen.add(Y)
            c['MM starts'] += 1
            if recv_gen(v, list(Y)):
                continue
            c['MM starts with no receiver'] += 1
            J = set(range(m)) - set(y for y in Y if y is not None)
            c['  ... some agent values a junk good' if any(v[i][g] > 0 for i in range(n) for g in J) else
              '  ... no agent values a junk good'] += 1
            c['  ... a pickless agent exists' if None in Y else '  ... NO PICKLESS AGENT'] += 1
            r = oc1(v, list(Y))
            c['  ... OC1 at picks' if r == 0 else ('  ... OC1 after one move' if r == 1 else '  ... OC1 FAILS')] += 1
            if r is None and ex is None:
                ex = dict(v=v, order=list(o), Y=list(Y))
    for k in sorted(c):
        print('  %-40s %d' % (k, c[k]))
    if ex:
        print('  example', json.dumps(ex))

if __name__ == '__main__':
    print('$ python3 k4/referee/norecv_ref.py', *sys.argv[1:], flush=True)
    main(*map(int, sys.argv[1:5]))
