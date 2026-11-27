"""Are the matching session's ROUND-RSD chains earliest-wanter prefixes? (k4/oc1max_multi.md §17)

Lemma SD-E(round) (refereed) covers rounds whose chains are prefixes of earliest-wanter chains E(k), subject to (H).
The matching session's ROUND-RSD (k4/matching/round_rsd.py on proof/k4-matching) allows any canonical chains and checks
the SD property directly.  For every witness (rounds of {k, T, P} with the state after each round) this script
replays the rounds and checks, at the state where each round starts:
  - the state, restricted to the present agents and goods, is the SD outcome of some order of the present agents;
  - every chain P of the round is a prefix of E(k) for one such order (the same order for the whole round);
  - (H) for the round (released head picks not wanted by outside agents at the round's start, unless they gain).
Counts per witness file.

    python3 k4/oc1max_multi/round_prefix.py WITNESSES.json.gz INPUT.jsonl[.gz] [...]
"""
import sys, os, json, gzip, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst


def load(fn):
    f = gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)
    return [json.loads(l) for l in f]


def check(row, w):
    I = Inst(row['sets'], row['vals']); n = I.n
    state = [[y] if y is not None else [] for y in row['picks']]; present = set(range(n)); gone = set(); C = collections.Counter()
    for rnd in w['rounds']:
        # orders of the present agents whose SD outcome (goods outside the deleted sets) is the current state
        val = {i: I.V(i, state[i]) for i in present}
        def sd(order):
            taken = set(gone); Y = {}
            for i in order:
                av = [g for g in I.R[i] if g not in taken]
                if av: g = max(av, key=lambda h: (I.v[i][h], -h)); Y[i] = g; taken.add(g)
                else: Y[i] = None
            return Y
        target = {i: (state[i][0] if state[i] else None) for i in present}
        if any(len(state[i]) > 1 for i in present): C['round starts at a non-single-good state'] += 1; return C
        orders = [o for o in itertools.permutations(sorted(present)) if sd(o) == target]
        if not orders: C['round starts at a non-SD state'] += 1; return C
        def E(k, order):
            pos = {a: t for t, a in enumerate(order)}; P = [k]
            while True:
                y = state[P[-1]][0]
                ws = [i for i in present if i != P[-1] and I.v[i].get(y, 0) > val[i]]
                if not ws: return P
                P.append(min(ws, key=lambda i: pos[i]))
        ok_prefix = any(all(s['P'] == E(s['k'], o)[:len(s['P'])] for s in rnd['settled']) for o in orders)
        C['rounds'] += 1; C['rounds of size %d' % len(rnd['settled'])] += 1
        C['round: all chains E-prefixes (one common order)' if ok_prefix else 'round: some chain NOT an E-prefix'] += 1
        new = rnd['state']
        taken = set(g for s in rnd['settled'] for g in s['T'])
        rel = [state[s['P'][-1]][0] for s in rnd['settled'] if state[s['P'][-1]][0] not in taken]
        K = set(s['k'] for s in rnd['settled'])
        H = all(I.v[a].get(y, 0) <= I.V(a, new[a]) for y in rel for a in present - K if I.v[a].get(y, 0) > val[a])
        C['(H) holds' if H else '(H) fails'] += 1
        for s in rnd['settled']: gone |= set(s['T'])
        present -= K; state = [list(x) for x in new]
    return C


if __name__ == '__main__':
    W = json.load(gzip.open(sys.argv[1])); rows = []
    for fn in sys.argv[2:]: rows += load(fn)
    seen = set(); R = []
    for r in rows:                                   # the matching session's distinct-row indexing
        key = json.dumps([r['sets'], r['vals'], list(r['picks'])])
        if key not in seen: seen.add(key); R.append(r)
    T = collections.Counter()
    for w in W['witnesses']:
        T.update(check(R[w['k']], w)); T['witnesses'] += 1
    print('$ python3 k4/oc1max_multi/round_prefix.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
