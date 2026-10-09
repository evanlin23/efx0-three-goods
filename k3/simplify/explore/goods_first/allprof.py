"""Every ranking profile WITHOUT fixing agent 0's ranking (so every labelling of the goods), values (4, 3, 2).
test_k3s.gen_small fixes agent 0 = (0, 1, 2); that is exhaustive only for algorithms whose tie-breaks do not depend on
good indices. EP breaks ties by good index, so this file checks all labellings.

  python3 allprof.py "EXPR" N M [N M ...]
"""
import sys, itertools, time
from common import check_rank, explain
import algos

expr = sys.argv[1]; alg = eval(expr, vars(algos)); args = list(map(int, sys.argv[2:]))
print(f"== {alg.__name__}   ({expr})  every labelling", flush=True)
for n, m in zip(args[::2], args[1::2]):
    t = time.time(); tot = bad = 0; first = None
    tri = list(itertools.permutations(range(m), 3))
    for rank in itertools.product(tri, repeat=n):
        tot += 1
        ok, X = check_rank(alg, n, m, list(rank))
        if not ok:
            bad += 1; first = first or (n, m, list(rank), X)
    print(f"  n={n} m={m}: {tot} profiles (all labellings), failures {bad}  [{time.time() - t:.0f}s]", flush=True)
    if first:
        print(f"  first failure: rankings {first[2]}"); [print("    " + l) for l in explain(*first)]
