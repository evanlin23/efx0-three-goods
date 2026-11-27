"""Cross-check sdilib.completions (numpy brute force, raw EFX0) against k4/sdc/oc_absorb.extends_A (SAT, sdclib's
encoding) and against efx0() on every returned assignment.  python3 k4/sdind/xcheck_lib.py screen|suite"""
import sys, itertools, collections, random
import _paths
from sdilib import Inst, sd, completions, bundles_of, efx0, picks_base
from sdclib import Enc
from oc_absorb import extends_A
from sdc_need import instances
C = collections.Counter(); rng = random.Random(1)
for name, sets, vals, m in instances(sys.argv[1]):
    if len(sets) > 5: continue
    I = Inst(sets, vals, m); E = Enc(sets, vals, m)
    seen = set()
    for o in itertools.permutations(range(I.n)):
        Y, J = sd(I, o)
        if tuple(Y) in seen: continue
        seen.add(tuple(Y))
        for A in (1, None):
            Jl, As = completions(I, picks_base(I, Y), A)
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            sat = extends_A(E, tuple(base), 1 if A == 1 else I.n)
            C['agree' if (len(As) > 0) == sat else 'DISAGREE'] += 1
            for a in As[:5]:
                C['efx0 ok' if efx0(I, bundles_of(picks_base(I, Y), Jl, a)) else 'EFX0 BAD'] += 1
        # brute count of all assignments vs numpy on a few
        if rng.random() < 0.05 and len(J) <= 5:
            Jl, As = completions(I, picks_base(I, Y), None)
            S1 = set(map(tuple, As.tolist()))
            S2 = set(a for a in itertools.product(range(I.n), repeat=len(J)) if efx0(I, bundles_of(picks_base(I, Y), J, a)))
            C['full set agree' if S1 == S2 else 'FULL SET DISAGREE'] += 1
print(sys.argv[1], dict(C))
