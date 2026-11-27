"""The RING residue (k4/oc1max_multi.md §7): at the starts whose first repairing mechanism is ED (no canonical chain,
RING-red or RING-OWN repairs), classify every repairing ED chain (collect.add_repairs) with an S* completion: does an
agent off the chain want a good of x_0's new bundle (so that x_0's bundle violates (G1) of Lemma 2*), and does the
S* completion compensate it with a junk good?  Counts over starts.

    python3 k4/oc1max_multi/ring_comp.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, sstar
from regimes import mechanism

if __name__ == '__main__':
    T = collections.Counter(); ex = None
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            mech, DT = mechanism(I, rec)
            if mech != 'ED': continue
            T['ED starts'] += 1; st = set()
            for r in rec['repairs']:
                if not r['ed'] or r['kind'] != 'chain': continue
                path = r['path']; k = path[0]; nb = tuple(tuple(b) for b in r['base'])
                val = [I.V(i, nb[i]) for i in range(I.n)]
                wanters = [w for w in range(I.n) if w not in path and any(I.v[w].get(g, 0) > val[w] for g in nb[k])]
                for o in r['ss']:
                    X = sstar(I, nb, o, witness=True)
                    if X is None: continue
                    comp = [w for w in wanters if len(X[w]) > len(nb[w])]
                    st.add('off-chain wanter of x0 bundle: %s; compensated: %s; owner %s' % (
                        bool(wanters), bool(wanters) and len(comp) == len(wanters), 'x0' if o == k else ('head' if o == path[-1] else 'other')))
            for s in st: T['  ' + s] += 1
            if not any('wanter of x0 bundle: True; compensated: True' in s for s in st):
                T['starts without a compensated-wanter repair'] += 1
                if ex is None or I.n < len(ex['inst']['sets']): ex = rec
    print('$ python3 k4/oc1max_multi/ring_comp.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
    if ex: print('smallest without:', ex['name'], json.dumps([ex['inst']['sets'], ex['inst']['vals']]), 'picks', ex['picks'])
