"""The faithful LSS algorithm (lss.py) on girth-4 instances (sanity) and on degree-<=4 instances with short cycles;
failures classified by the girth use that breaks (k4/girth.md, sections 1.4 and 2).  EVIDENCE only.

    python3 k4/girth/run_faithful.py [--quick]        log: results/k4_girth_faithful.log
"""
import collections
import random
import sys
import time

from lss import Inst, lss, labels, random_labels, classify, is_efx0, two_cycles, triangles, girth_at_least, \
    random_girth4, flex
from gen import random_linear, random_deg4, with_values, fano, ag23, pg23
from sources import screen, suite, cores, domains

QUICK = '--quick' in sys.argv


def table(name, insts, rng, labs_per_zero=3):
    """per instance: every vertex 0, the default labeling plus random ones; also the flexible sink (section 3)"""
    C = collections.Counter()
    inst_some = inst_flex = 0
    for I in insts:
        some = fl = False
        for z in range(I.n):
            for rep in range(labs_per_zero):
                lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
                r = lss(I, lab=lab)
                c = classify(r)
                C[c or 'EFX0'] += 1
                if not two_cycles(I):
                    assert r.soft_break is None and (r.first_break is None or r.first_break[0] == 'A3L4')
                some |= c is None
                if rep == 0:
                    fl |= bool(flex(I, lab)[1])
        inst_some += some
        inst_flex += fl
    runs = sum(C.values())
    print('%-34s %5d instances, %6d runs: %s' % (name, len(insts), runs,
          ', '.join('%s %d' % (k, C[k]) for k in sorted(C, key=lambda k: (k != 'EFX0', k)))))
    print('%-34s some run EFX0 on %d/%d instances; flexible sink (default labels, some vertex 0) on %d/%d'
          % ('', inst_some, len(insts), inst_flex, len(insts)), flush=True)


def core_profiles(n, per_core, rng):
    out = []
    for f, idx, sets, m in cores(n):
        D = domains(sets, m)
        for _ in range(per_core):
            ds = [rng.choice(d) for d in D]
            out.append(Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m))
    return out


def main():
    t0 = time.time()
    rng = random.Random(2026)
    print('$ python3 k4/girth/run_faithful.py' + (' --quick' if QUICK else ''))
    k = 300 if QUICK else 2000
    g4 = []
    while len(g4) < k:
        I = random_girth4(rng.randint(2, 9), rng.randint(3, 25), rng, maxsize=rng.choice([2, 3, 4, 5]),
                          pzero=rng.choice([0, 0.2]))
        assert girth_at_least(I, 4)
        g4.append(I)
    table('random girth>=4 (any degree)', g4, rng)
    lin = []
    while len(lin) < k:
        n = rng.randint(3, 10)
        e = random_linear(n, rng, sizes=rng.choice([(2, 3), (3,), (2, 3, 4), (3, 4)]), tries=60,
                          private=rng.choice([0, 0.3]))
        if e:
            I = with_values(n, e, rng, mode=rng.choice(['uniform', 'flat', 'geom']))
            if triangles(I):
                lin.append(I)
    table('random linear, deg<=4, triangles', lin, rng)
    for name, (n, ed) in [('Fano + private goods', fano()), ('AG(2,3) (deg 4)', ag23()), ('PG(2,3) (deg 4)', pg23())]:
        L = []
        for _ in range(60 if QUICK else 300):
            e2 = [list(x) for x in ed] + ([[x] for x in range(n) if rng.random() < .5] if n == 7 else [])
            L.append(with_values(n, e2, rng, mode=rng.choice(['uniform', 'flat', 'geom'])))
        table(name, L, rng)
    d4 = []
    while len(d4) < k:
        n = rng.randint(3, 8)
        e = random_deg4(n, rng, tries=40)
        if e:
            I = with_values(n, e, rng, mode=rng.choice(['uniform', 'flat', 'geom']))
            if two_cycles(I):
                d4.append(I)
    table('random deg<=4 with 2-cycles', d4, rng)
    table('screen set (k4/de4/ss_screen.py)', [I for _, I in screen()], rng)
    table('suite (k4/suite/instances)', [I for _, I in suite()], rng)
    table('k=4 cores n=2, all, random profiles', core_profiles(2, 40 if QUICK else 400, rng), rng)
    table('k=4 cores n=3, all, random profiles', core_profiles(3, 10 if QUICK else 60, rng), rng)
    print('time %.0fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
