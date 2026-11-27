"""Conjecture K''' (kgen/n3.md §8), two agents, values generic on the relevant goods: if v_b(y_b) > v_b(y_a) and
  (Mb) the junk that b values above y_a is worth at least v_b(y_b) to b, and
  (Ma) the junk that a values above y_b is worth at least v_a(y_a) to a,
then the ratio knife gives an EFX0 allocation of an OC1 shape (with zeros: a-worthless goods first in b's order,
b-worthless last, then Lemma M moves a's worthless goods to b).  If (Mb) fails, LPT_b separates the picks (Lemma 2
(ii)); if (Ma) fails, LPT_a does (Lemma 2 (iii)); so Lemma 2 + K''' settles the two-agent case.  Also re-checks those
two implications on every start.

    python3 kgen/n2_k3.py SEED N MMIN MMAX [zeros]"""
import sys, random, collections, json
from oc2 import efx0, sd
from n2_zeros import knife0, lpt0, shapes4, gen0

if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); zeros = 'zeros' in sys.argv; rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/n2_k3.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi)
        v = gen0(rng, m) if zeros else [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]
            if yb is None or v[b][ya] > v[b][yb]: continue
            J = [g for g in range(m) if g not in (ya, yb)]
            Mb = sum(v[b][g] for g in J if v[b][g] > v[b][ya]) >= v[b][yb]
            Ma = sum(v[a][g] for g in J if v[a][g] > v[a][yb]) >= v[a][ya]
            sep = lambda B: (ya in B[0]) != (yb in B[0])
            if not Mb: C['(Mb) fails'] += 1; C['(Mb) fails => LPT_b separates'] += sep(lpt0(v[b], range(m)))
            if not Ma: C['(Ma) fails'] += 1; C['(Ma) fails => LPT_a separates'] += sep(lpt0(v[a], range(m)))
            if Ma and Mb:
                X = knife0(v, a, b, ya, yb, J); sh = shapes4(v, X, ya, yb, a, b)
                C['K\'\'\' hypothesis'] += 1; C['K\'\'\' knife gives an OC1 shape'] += bool(sh)
                if not sh and C['shown'] < 3: C['shown'] += 1; print('K\'\'\' FAILS', json.dumps(v), 'order', (a, b), flush=True)
    for k in sorted(C):
        if k != 'shown': print(k, C[k])
