"""Random test of the collector theorem (Theorem 5 of proofs/beta2.md) in its general form, beyond beta = 2 cores:
random multigraphs K = (V, E) with pins, |E| + |pins| = |V| + 1, random endpoints (parallel edges allowed) and random
strict rankings of {p_e, x_e, y_e}. Whenever a cover state exists, run beta2.Collector (switches until the collector
is safe), build the allocation of the theorem (plus junk goods Z in the collector's bundle), and check every agent of
E with the raw EFX0 definition (tools/check_certs.safe, three balanced realizations). Evidence for the general
statement only; the proof is in proofs/beta2.md.
Usage: test_collector.py [trials] [seed]"""
import sys, os, random, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from check_certs import safe, REAL
import beta2


def trial(rng):
    nv = rng.randint(1, 9)
    npins = rng.randint(0, min(3, nv))
    ne = nv + 1 - npins
    if ne < 1: return None
    V = list(range(nv)); pins = rng.sample(V, npins)
    E = list(range(ne))
    ends = {e: rng.sample(V, 2) if nv >= 2 else None for e in E}
    if any(x is None for x in ends.values()): return None
    priv = {e: nv + e for e in E}                                   # private goods numbered after V
    rank = {e: tuple(rng.sample([priv[e]] + ends[e], 3)) for e in E}
    C = beta2.Collector(V, E, ends, priv, rank, pins)
    start = next(((w0, c) for w0 in E for c in [C.initial(w0)] if c is not None), None)
    if start is None: return None
    w, head, J, sw = C.solve(start[0], dict(start[1]))
    # agents: E (ids 0..ne-1), then one pin holder per pin; goods: V, privates, two junk goods
    junk = [nv + ne, nv + ne + 1]
    holder = {}
    for e in E:
        if e == w: continue
        holder[head[e]] = e
        holder[priv[e]] = w if e in J else e
    holder[priv[w]] = w
    for g in junk: holder[g] = w
    for k, pv in enumerate(pins): holder[pv] = ne + k
    assert sorted(holder) == list(range(nv + ne + 2)), "not a complete allocation"
    nag = ne + len(pins)
    bundles = [[g for g in holder if holder[g] == j] for j in range(nag)]
    assert sum(len(B) > 2 for B in bundles if B is not bundles[w]) == 0, "a second large bundle"
    for e in E:
        ok = {safe(dict(zip(rank[e], r)), bundles, e) for r in REAL}
        assert len(ok) == 1, "realizations disagree"
        if not ok.pop(): return ('UNSAFE', e, V, pins, ends, rank, bundles)
    return ('ok', sw)


if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    done = unsafe = maxsw = 0
    for _ in range(trials):
        r = trial(rng)
        if r is None: continue
        if r[0] == 'UNSAFE':
            unsafe += 1; print("UNSAFE agent:", r[1:]); break
        done += 1; maxsw = max(maxsw, r[1])
    print(f"collector theorem, random multigraphs: {done} instances with a cover state checked, "
          f"{unsafe} failures, at most {maxsw} switches")
    sys.exit(1 if unsafe else 0)
