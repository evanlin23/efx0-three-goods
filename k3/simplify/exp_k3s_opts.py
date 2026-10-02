import sys, os, itertools, collections, random
sys.path.insert(0, os.path.dirname(__file__))
from k3s import k3s, efx0
from lbx import core_profiles
from test_k3s import gen_small
VARS = {'K3S': {}, 'K3ALG slots (cap1=False)': dict(cap1=False), 'single_pass': dict(single_pass=True, strict_absorb=False)}
def check(src, label):
    bad = collections.Counter(); first = {}; tot = 0
    for n, m, rank in src:
        tot += 1; v = [dict(zip(r, (4, 3, 2))) for r in rank]
        for name, o in VARS.items():
            if not efx0(n, m, v, k3s(n, m, v, **o)): bad[name] += 1; first.setdefault(name, (rank, m))
    print(f"{label}: {tot} profiles; failures {dict(bad) or 0}", {k: first[k] for k in first})
check(core_profiles(4), "cores n<=4")
for n, m in [(2, 5), (2, 6), (3, 5), (3, 6), (3, 7), (3, 8)]: check(gen_small(n, m), f"all profiles n={n} m={m}")
rng = random.Random(11)
check(((n, m, [tuple(rng.sample(range(m), 3)) for _ in range(n)]) for n, m in ((rng.randint(2, 8), 0) for _ in range(150000)) for m in [rng.randint(max(3, n), 2 * n + 3)]), "random profiles n<=8")
