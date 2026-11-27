"""Order classes on the core counterexamples (k4/ttc.md §13, attempts/k4-ttc-oc-every-order.md): for each instance,
nu (maximum matching size of agents to relevant goods), the pick counts of the failing orders (OC1 fails: no
one-absorber completion at the picks or after one de_free move), and how the R1-priority outcomes relate to the
maximum-matching outcomes (as sets of pick vectors over all n! orders): equal, one contained in the other, or neither.

    python3 k4/ttc/order_classes.py"""
import json, itertools, collections, os
import ttclib as T, core_climb as CC

R = os.path.join(T.ROOT, 'results', 'k4_ttc')


def instances():
    out = [('n5 two-private core', json.load(open(os.path.join(R, 'oc1_core_candidate.json')))[0]),
           ('MC2 counterexample', json.load(open(os.path.join(R, 'oc1_mc2_counterexample.json')))[0])]
    sets = [[0,2,3,1],[6,4,5,9],[1,2,3,9],[1,6,7,8],[3,6,9],[1,3,6,9]]
    out.append(('Hall B<', {'sets': sets, 'vals': [[6,14,16,12],[4,18,12,28],[28,4,16,21],[16,14,12,6],[28,8,24],[20,30,8,4]], 'm': 10}))
    out.append(('Hall B>', {'sets': sets, 'vals': [[6,14,16,12],[4,18,12,28],[28,4,16,19],[16,14,12,6],[28,8,24],[20,30,8,4]], 'm': 10}))
    seen = set()
    for line in open(os.path.join(R, 'core_climb_mc2_seeded.log')):
        if line.startswith('CORE OC1 FAILS'):
            d = json.loads(line[len('CORE OC1 FAILS '):]); k = json.dumps((d['sets'], d['vals']))
            if k not in seen:
                seen.add(k); out.append(('MC2 climb %d' % len(seen), d))
    return out


if __name__ == '__main__':
    print('$ python3 k4/ttc/order_classes.py')
    tot = collections.Counter()
    for name, d in instances():
        sets, vals, m = d['sets'], d['vals'], d['m']; n = len(sets)
        E = T.Enc(sets, vals, m); nu = CC.nu(sets)
        plain = {}; r1 = set(); fails = collections.Counter(); maxout = set(); r1max = 0
        for pi in itertools.permutations(range(n)):
            Y = tuple(T.sd(E, list(pi))[0]); Yr = tuple(T.sd(E, list(pi), True)[0])
            r1.add(Yr)
            for Z in (Y, Yr):
                if Z not in plain:
                    b = T.base_of(E, Z)
                    plain[Z] = T.extends_A(E, b, 1) or any(T.extends_A(E, x, 1) for x in set(T.DF.moves(E, b)))
            k = sum(1 for y in Y if y is not None)
            if k == nu:
                maxout.add(Y)
            if not plain[Y]:
                fails[k] += 1
        r1_is_max = all(sum(1 for y in Z if y is not None) == nu for Z in r1)
        rel = ('equal' if r1 == maxout else 'R1 ⊂ max' if r1 < maxout else 'max ⊂ R1' if maxout < r1 else
               'neither (R1 outcomes all maximum: %s)' % r1_is_max)
        r1fail = sum(1 for Z in r1 if not plain[Z]); maxfail = sum(1 for Z in maxout if not plain[Z])
        print('%-22s n=%d nu=%d  failing orders by pick count %s  | distinct outcomes: R1 %d, max %d; %s; '
              'failing R1 outcomes %d, failing max outcomes %d' % (name, n, nu, dict(fails), len(r1), len(maxout), rel,
                                                                   r1fail, maxfail))
        tot['instances'] += 1; tot['R1 outcomes all maximum'] += r1_is_max; tot[rel.split(' (')[0]] += 1
        tot['failing R1 outcomes'] += r1fail; tot['failing max outcomes'] += maxfail
    print(dict(tot))
