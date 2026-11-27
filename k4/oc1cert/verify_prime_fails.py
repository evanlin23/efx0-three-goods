"""Verify OC1'^max failures (workstream compute/k4-oc1max-cert) with kgen-rounds' raw brute force (kgen/rounds/
verify_k4zero.py on proof/kgen-rounds: one_chain_prime, completion; chains and additions, no rings) and, for rings,
with the raw checker k4/sdc/oc1_mc2_rand.Inst (its ring moves, brute-force one-absorber completion).  Also confirms that
the picks are an SD outcome of a maximum-matching order and that OC1 fails (Inst.check).

    python3 k4/oc1cert/verify_prime_fails.py FAILS.jsonl DIR      (DIR holds verify_k4zero.py)"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc')); sys.path.insert(0, sys.argv[2])
import verify_k4zero as KR
from oc1_mc2_rand import Inst
C = collections.Counter()
for line in open(sys.argv[1]):
    d = json.loads(line); S, vals, Y = d['sets'], d['vals'], tuple(d['picks'])
    I = Inst(S, vals); m = I.m
    V = [[I.v[i].get(g, 0) for g in range(m)] for i in range(I.n)]
    orders = [o for o in itertools.permutations(range(I.n)) if tuple(KR.sd(V, o)) == Y]
    b0 = [frozenset([g]) if g is not None else frozenset() for g in Y]
    chains_ok = any(KR.completion(V, list(s), 1) is not None for s in KR.one_chain_prime(V, b0))
    # rings (Inst.moves contains them; a ring's states are also OC1' states, rings being unchanged in OC1')
    base = [[g] if g is not None else [] for g in Y]
    rings_ok = any(I.one_absorber([list(b) for b in st]) for st in I.moves(base))
    nu = max(sum(p is not None for p in I.sd(o)) for o in itertools.permutations(range(I.n)))
    res = {'orders': len(orders), 'max matching': sum(y is not None for y in Y) == nu, 'Inst.check': I.check(Y),
           'kgen OC1prime (chains, additions)': chains_ok, 'Inst one move (chains, rings, additions)': rings_ok}
    verdict = 'OC1prime FAILS' if (orders and res['max matching'] and not chains_ok and not rings_ok) else 'not a failure'
    C[verdict] += 1
    print(verdict, json.dumps({'list': d.get('list'), 'idx': d.get('idx'), 'sets': S, 'vals': vals, 'picks': list(Y), **res}), flush=True)
print(dict(C))
