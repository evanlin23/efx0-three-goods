"""Self-test of k4/p3/p3lib.py: the SAT model (complete, with a fixed good, and partial with a good left out) against brute
force over all allocations, on random (4, 3) cores with n <= 4. Prints the number of mismatches (0 expected).
    python3 k4/p3/selftest.py   (about a minute)"""
import sys, random, itertools
sys.path.insert(0, 'k4/p3')
from p3lib import *
# self-test: SAT vs brute force on random small (4,3) instances
rng = random.Random(1)
bad = 0; tested = 0
for t in range(150):
    n = rng.choice([2,3,4]); 
    rc = random_core43(rng, n)
    if rc is None: continue
    m, sets = rc
    if m > (8 if n == 4 else 7): continue
    I = Inst(sets, random_types(rng, sets, m), m)
    C = Complete(I); tested += 1
    # brute: number of complete EFX0 allocations; and with good 0 fixed to agent 0
    cnt = 0; cnt0 = 0
    for own in itertools.product(range(n), repeat=m):
        if efx0(I, bundles(I, own)):
            cnt += 1; cnt0 += own[0] == 0
    s = C.solve(); s0 = C.solve(fixed={0: 0})
    if (s is None) != (cnt == 0) or (s0 is None) != (cnt0 == 0): bad += 1; print('MISMATCH', sets)
    if s is not None and not efx0(I, bundles(I, s)): bad += 1; print('BAD MODEL')
    # partial: brute count of partial EFX0 with good 0 unallocated and all others allocated
    pc = 0
    for own in itertools.product(range(n), repeat=m-1):
        if efx0(I, bundles(I, (None,) + own)): pc += 1
    sp = C.solve(allowed={0: {n}}, complete=False, extra=[[-C.x[g][n]] for g in range(1, m)])
    if (sp is None) != (pc == 0): bad += 1; print('PMISMATCH')
print("selftest mismatches", bad, "tested", tested)
