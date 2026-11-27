"""How rare the k = 4 failures of k4/ksens.md §5 are: on each hypergraph of the certifier's 11 counterexamples, random
strict profiles (each agent's values distinct integers in 1..30) and the fraction whose maximum-matching starts include
one that fails OC1 (one chain, one-absorber completion; ocsat).  Evidence for attempts/k4-ksens-k4-searches.md.

    python3 k4/ksens/oc1max_k4_rarity.py T SEED"""
import sys, random
import _paths
import ocsat
from maxmatch import nu
from refute_oc1max_k4 import CEX

if __name__ == '__main__':
    T, seed = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed); n = 4
    print('$ python3 k4/ksens/oc1max_k4_rarity.py', T, seed, flush=True); tot = bad = 0
    for c, (S, _, _) in enumerate(CEX):
        m = 1 + max(max(s) for s in S); v_ = nu(S, [[1] * len(s) for s in S]); b_ = 0
        for t in range(T):
            V = [rng.sample(range(1, 31), len(s)) for s in S]; O = ocsat.OC(S, V, m)
            st = [Y for Y in ocsat.starts(S, V, m) if sum(1 for g in Y if g is not None) == v_]
            if any(not O.holds(ocsat.bases_of(Y, n), chain='any', A=1) for Y in st): b_ += 1
            O.close()
        tot += T; bad += b_
        print('#%d hypergraph %s: %d of %d random profiles fail OC1^max' % (c + 1, S, b_, T), flush=True)
    print('all: %d of %d (%.4f)' % (bad, tot, bad / tot))
