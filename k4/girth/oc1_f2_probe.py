"""Lemma ORD / (F2) of k4/girth.md section 7: which hypothesis of RF-T's setting forces (F2) "no off-path agent wants
Y_d at Y"?  Random strict balanced order types (k4/girth/sources.domains) on every third pure n = 5 core with m = 8,
40 profiles each, every order sigma whose picks Y are perfect with one receiver u, Y' = SD(u, then sigma - u) perfect,
RF path length >= 2 with d taking a junk good of Y (the stage before DEMOTE-0's conditions): (F2) by the roles at Y'
(|U'|, |D_T'|, whether d is a receiver); and when (F2) fails, which agents are the other receivers of Y' and who
wants the pick of the agent that wants Y_d.  EVIDENCE (the lemma itself is proved in the text).

    python3 k4/girth/oc1_f2_probe.py
"""
import collections
import itertools
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_r2n5 import path_from  # noqa: E402
from sources import cores, domains  # noqa: E402


def main():
    print('$ python3 k4/girth/oc1_f2_probe.py', flush=True)
    C = collections.Counter()
    rng = random.Random(5)
    cs = [c for c in cores(5, pure=True) if c[3] == 8]
    for f, idx, sets, m in cs[::3]:
        doms = domains(sets, m)
        n = len(sets)
        R = [set(s) for s in sets]
        for t in range(40):
            ds = [rng.choice(D) for D in doms]
            vals = [[d[g] for g in sorted(d)] for d in ds]
            v = [dict(d) for d in ds]
            seen = set()
            for o in itertools.permutations(range(n)):
                Y = sd(R, v, o)
                if None in Y:
                    continue
                rl, J = roles(sets, vals, list(Y))
                if rl.count('U') != 1:
                    continue
                u = rl.index('U')
                Y2 = sd(R, v, [u] + [a for a in o if a != u])
                if None in Y2 or (Y, Y2) in seen:
                    continue
                seen.add((Y, Y2))
                path = path_from(Y, Y2, J, u)
                d = path[-1]
                if len(path) < 3 or Y2[d] not in J:
                    continue
                rl2, J2 = roles(sets, vals, list(Y2))
                C['u is the last agent of sigma (must be all)'] += o[-1] == u
                C['configurations'] += 1
                bad = [i for i in range(n) if i not in path and v[i].get(Y[d], 0) > v[i].get(Y[i], 0)]
                F2 = not bad
                tag = "|U'| = %d, |D_T'| = %d, d %s" % (rl2.count('U'), rl2.count('DT'),
                                                        'a receiver' if rl2[d] == 'U' else 'frozen')
                C["(F2) %s: %s" % (F2, tag)] += 1
                C["(F2) %s: |U'| %s" % (F2, '= 1' if rl2.count('U') == 1 else '>= 2')] += 1
                if F2:
                    continue

                def lab(x):
                    return 'u' if x == u else ('x%d' % path.index(x) if x in path else (
                        'a wanter of Y_d' if x in bad else 'another off-path agent'))
                others = tuple(sorted(lab(x) for x in range(n) if rl2[x] == 'U' and x != d))
                C["(F2) fails: the receivers of Y' other than d: %s" % (others,)] += 1
                for i in bad:
                    C["(F2) fails: a wanter of Y_d is unfrozen at Y': %s" % (rl2[i] == 'U')] += 1
                    C["(F2) fails: the agents wanting that wanter's pick at Y: %s" % (tuple(sorted(
                        lab(a) for a in range(n) if a != i and v[a].get(Y[i], 0) > v[a].get(Y[a], 0))),)] += 1
    for k in sorted(C):
        print('   %-100s %6d' % (k, C[k]))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
