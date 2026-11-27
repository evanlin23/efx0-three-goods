"""OC1'^max (kgen/rounds.md §4.6: one chain whose non-end agents may also take goods of the end's released base) is
REFUTED at n = 5.  Instance: the certifier's n = 5 OC1^max failure 5_pure idx 164 (results/k4_certs_5_pure.json.gz),
the coordinator's integer representative.  Checks, all with the coordinator's own code unless named:
  (1) the profile is a strict connected k = 4 core with MC2 (oc1max_climb.is_core), and the picks (7, 2, 3, 5, 4) are
      the serial-dictatorship picks of the orders listed and form a perfect (so maximum) matching;
  (2) OC1 fails (oc1_mc2_rand.Inst.check) and OC1' fails (oc1prime_verify.prime_states + Inst.one_absorber);
  (3) every two-move repair (plain official moves) is listed, grouped by the shapes of the two moves;
  (4) the EFX0 allocations of the instance (raw enumeration) and those that value-dominate the picks (MD).
Independent cross-checks of (2), run separately (log): kgen/rounds/verify_k4zero.oc1_prime (forward brute force) and
kgen/rounds/rndlib.oc1z (rnd.c) both report OC1' false at this start.
    python3 k4/sdc/oc1prime_n5_cex.py"""
import itertools, json, collections
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
import oc1max_climb as C
import oc1prime_verify as P

SETS = [[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]]
VALS = [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]]
PICKS = (7, 2, 3, 5, 4)

I = Inst(SETS, VALS)
print('instance', json.dumps({'sets': SETS, 'vals': VALS}))
print('(1) strict connected core:', C.is_core(SETS, VALS, False), '| with MC2:', C.is_core(SETS, VALS, True))
ords = [o for o in itertools.permutations(range(5)) if I.sd(o) == PICKS]
print('    orders giving the picks', PICKS, ':', ords, '| nu =', nu(I), '| perfect:', None not in PICKS)
base = [[g] for g in PICKS]
print('(2) OC1:', I.check(PICKS))
st = [nb for nb in P.prime_states(I, base)]
rep = [nb for nb in st if I.one_absorber(nb)]
print("    OC1' move states:", len({tuple(map(tuple, map(sorted, s))) for s in st}), '| with a one-absorber completion:', len(rep))


def shape(b0, b1):
    moved = [i for i in range(I.n) if sorted(b0[i]) != sorted(b1[i])]
    return tuple(moved)


first = {tuple(tuple(sorted(b)) for b in s) for s in I.moves(base)}
two = collections.Counter(); ex = {}
for s1 in first:
    s1 = [list(b) for b in s1]
    for s2 in I.moves(s1):
        s2 = [list(b) for b in s2]
        if I.one_absorber(s2):
            key = (shape(base, s1), shape(s1, s2)); two[key] += 1; ex.setdefault(key, (s1, s2))
print('(3) two-move repairs (state pairs) by (agents changed in move 1, in move 2):')
for k, c in sorted(two.items(), key=lambda kv: -kv[1]): print('   ', k, c, 'e.g.', json.dumps(ex[k]))
J = list(range(I.m))
efx = []
for lab in itertools.product(range(I.n), repeat=I.m):
    B = [[g for g in J if lab[g] == i] for i in range(I.n)]
    if I.efx0(B): efx.append(B)
md = [B for B in efx if all(I.V(i, B[i]) >= I.v[i][PICKS[i]] for i in range(I.n))]
print('(4) EFX0 allocations:', len(efx), '| value-dominating the picks (MD):', len(md))
for B in md: print('    MD', B, [I.V(i, B[i]) for i in range(I.n)])
