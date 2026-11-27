"""Two agents, positive generic values: the ratio knife for shape A1.  b keeps y_b, a keeps y_a; the junk is sorted by
v_b/v_a decreasing; b takes the shortest prefix after which b does not strongly envy a's bundle; a keeps the rest.
Is the result EFX0 (then it is A1)?  Also the mirror knife (a takes junk by v_a/v_b until a is satisfied), and
how often one of the two knives or Lemma 2's cases (kgen/n3.md §8) works.

    python3 kgen/n2_knife.py SEED N MMIN MMAX"""
import sys, random, collections, json
from oc2 import efx0, sd
from n2_rules import shape
from n2_lpt import lpt


def knife(v, taker, other, yt, yo, J):
    """taker keeps yt and takes the shortest prefix of J (by v_taker/v_other decreasing) that leaves it not strongly
    envious of the other's bundle; the other keeps yo and the rest"""
    order = sorted(J, key=lambda g: -v[taker][g] / v[other][g])
    for s in range(len(order) + 1):
        Xt = {yt} | set(order[:s]); Xo = {yo} | set(order[s:])
        vo = [v[taker][g] for g in Xo]
        if len(Xo) < 2 or sum(v[taker][g] for g in Xt) >= sum(vo) - min(vo):
            X = [None, None]; X[taker] = Xt; X[other] = Xo; return X
    return None


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); ex = []
    print('$ python3 kgen/n2_knife.py', *sys.argv[1:], flush=True)
    for t in range(N):
        m = rng.randint(lo, hi); v = [rng.sample(range(1, 10 ** 6), m) for _ in range(2)]
        for a, b in [(0, 1), (1, 0)]:
            y = sd(v, (a, b)); ya, yb = y[a], y[b]; J = [g for g in range(m) if g not in (ya, yb)]
            sep = lambda B: (ya in B[0]) != (yb in B[0])
            lemma2 = v[b][ya] > v[b][yb] or sep(lpt(v[b], range(m))) or sep(lpt(v[a], range(m)))
            kb = knife(v, b, a, yb, ya, J); ka = knife(v, a, b, ya, yb, J)
            okb = kb is not None and efx0(v, kb); oka = ka is not None and efx0(v, ka)
            C['starts'] += 1; C['knife b (b takes by ratio) EFX0'] += okb; C['knife a (a takes by ratio) EFX0'] += oka
            C['either knife'] += okb or oka; C['either knife or Lemma 2'] += okb or oka or lemma2
            if not lemma2: C['open case of Lemma 2'] += 1; C['open case: either knife'] += okb or oka
            if not (okb or oka or lemma2) and len(ex) < 3: ex.append((v, (a, b)))
    for k in sorted(C): print(k, C[k])
    for e in ex: print('uncovered', json.dumps(e))
